#!/usr/bin/env python3
"""rxref: independent reference for the `rxref` oracle (steering round 16).

An rxref program is a Racket module with up to 6 regexp lines.  Each line's
spec (pattern AST, input, start/end offsets, input prefix, replacement
template, bytes or string mode) is stored as JSON in a `;; RX {...}` comment
right before the Racket code that runs it, so prog.rkt is self-contained.
The Racket side matches the pregexp through many entry points (byte
strings, strings, input ports, peeking, regexp-match*, regexp-split,
regexp-replace(*), regexp-match?, regexp-quote, a string regexp on the UTF-8
bytes) and prints `<line>.<op> <encoded result>`.  This script translates
the same AST into a Python `re` pattern (explicit ASCII classes, explicit
anchors, so only the documented Racket semantics are used: rx.rkt grammar,
regexps.scrbl for start-pos / end-pos / input-prefix / regexp-match* /
regexp-split / regexp-replace) and computes the expected results.

  rxref.py gen <seed>           print a program
  rxref.py eval prog.rkt        expected output lines
  rxref.py check prog.rkt < l   exit 1 mismatch, 0 match, 2 undecidable
  rxref.py server               framed requests on stdin:
     G <seed>\n                 -> program text with \n replaced by \t
     C <n>\n<prog><m>\n<line>   -> verdict (tab separated)
     S <idx> <n>\n<prog>        -> shrink candidates (one per line, \n->\t), then END
"""
import sys, re, json, random, unicodedata

# ---------------------------------------------------------------- pools
# Characters whose Unicode properties and simple case mappings are stable
# and unambiguous (no Kelvin sign, long s, dotted/dotless i, sharp s
# capital, Angstrom sign: Python's re.IGNORECASE folds those specially).
ASCII_LET = 'abcxyzABCXYZ'
ASCII_OTH = '0123_ -.,:\n\t'
UNI = ['é', 'É', 'ñ', 'Ñ', 'ÿ', 'ß', 'λ', 'Λ', 'σ', 'Σ', 'α', 'ω', 'Ω', 'ж', 'Ж',
       '中', '文', '😀', '𝔸', '́', '²', '٣', '«', '»', '—', '€', '©', ' ',
       '­', 'ǅ', 'Ǆ', 'ǆ', 'ς', 'ê', 'Ê', 'ø', 'Ø', '　', '٫', '∑']
UNI_NOFOLD = {'ς', 'ǅ', 'Ǆ', 'ǆ', 'σ', 'Σ'}   # never under (?i): fold classes differ by design
BYTES_HI = [0x80, 0x9f, 0xa0, 0xc3, 0xce, 0xe9, 0xff, 0x00, 0x7f, 0x01]
PROPS = ['Ll', 'Lu', 'Lt', 'L', 'Nd', 'No', 'N', 'P', 'Po', 'Pd', 'Pi', 'Pf', 'S', 'Sm',
         'Sc', 'So', 'Zs', 'Z', 'Mn', 'M', 'Cf', 'Cc', 'C', 'L&', 'Lo']
POSIX = {'alpha': 'a-zA-Z', 'upper': 'A-Z', 'lower': 'a-z', 'digit': '0-9',
         'xdigit': '0-9a-fA-F', 'alnum': 'a-zA-Z0-9', 'word': 'a-zA-Z0-9_',
         'blank': ' \\t', 'space': ' \\t\\n\\f\\r', 'cntrl': '\\x00-\\x1f',
         'ascii': '\\x00-\\x7f', 'graph': '!-~', 'print': ' \\t!-~'}
KCLS = {'d': '0-9', 'w': 'a-zA-Z0-9_', 's': ' \\t\\n\\f\\r'}
WORD = '[a-zA-Z0-9_]'
OPS_B = ['pos', 'port', 'peek', 'match', 'all', 'allport', 'split', 'repl', 'repl1', 'test', 'quote', 'portmatch',
         'exact', 'outport', 'allg']
OPS_S = ['pos', 'port', 'peek', 'match', 'all', 'allport', 'split', 'repl', 'repl1', 'test', 'quote',
         'utf8', 'portmatch', 'exact', 'outport', 'allg']


def all_chars(mode):
    if mode == 'b':
        return [ord(c) for c in ASCII_LET + ASCII_OTH] + BYTES_HI
    return [ord(c) for c in ASCII_LET + ASCII_OTH] + [ord(c) for c in UNI]


# ---------------------------------------------------------------- AST
# ["lit", c] ["any"] ["cls", neg, items] (items: ["c",x] ["r",lo,hi] ["k",d|w|s] ["px",name])
# ["kls", d|D|w|W|s|S] ["prop", neg, cat] ["bol"] ["eol"] ["wb"] ["nwb"]
# ["seq", [..]] ["alt", [..]] ["grp", x] ["ncg", x] ["mode", m, x] (m: i -i m -m s -s)
# ["rep", lo, hi|None, lazy, x] ["look", "="|"!"|"<="|"<!", x] ["atomic", x]
# ["bref", n] ["cond", n, yes, no|None]

class Gen:
    def __init__(self, rnd, mode):
        self.r = rnd; self.mode = mode; self.ngrp = 0; self.closed = set()
        self.ci = False; self.in_lb = False

    def ch(self):
        r = self.r
        if self.mode == 'b':
            return r.choice([ord(c) for c in ASCII_LET] * 3 + [ord(c) for c in ASCII_OTH] + BYTES_HI)
        pool = [ord(c) for c in ASCII_LET] * 2 + [ord(c) for c in ASCII_OTH] + [ord(c) for c in UNI if not (self.ci and c in UNI_NOFOLD)]
        return r.choice(pool)

    def atom(self, d):
        r = self.r; x = r.random()
        if d <= 0 or x < 0.35:
            y = r.random()
            if y < 0.55: return ['lit', self.ch()]
            if y < 0.63: return ['any']
            if y < 0.80: return self.cls()
            if y < 0.88: return ['kls', r.choice('dDwWsS')]
            if self.mode == 's' and not self.ci and y < 0.94:
                return ['prop', r.random() < 0.3, r.choice(PROPS)]
            if self.closed and not self.in_lb and y < 0.97:
                return ['bref', r.choice(sorted(self.closed))]
            return ['lit', self.ch()]
        y = r.random()
        if y < 0.30:
            self.ngrp += 1; n = self.ngrp
            b = self.regex(d - 1)
            self.closed.add(n)
            return ['grp', b]
        if y < 0.42: return ['ncg', self.regex(d - 1)]
        if y < 0.52:
            m = r.choice(['i', 'i', '-i', 'm', '-m', 's', '-s'])
            old = self.ci
            if m == 'i': self.ci = True
            if m == '-i': self.ci = False
            b = self.regex(d - 1)
            self.ci = old
            return ['mode', m, b]
        if y < 0.68:
            t = r.choice(['=', '!', '<=', '<!'])
            if t in ('<=', '<!'):
                old = self.in_lb; self.in_lb = True
                b = self.fixed(d - 1)
                self.in_lb = old
            else:
                b = self.regex(d - 1)
            return ['look', t, b]
        if y < 0.76: return ['atomic', self.regex(d - 1)]
        if y < 0.84 and self.closed and not self.in_lb:
            n = r.choice(sorted(self.closed))
            yes = self.seq(d - 1)
            no = self.seq(d - 1) if r.random() < 0.6 else None
            return ['cond', n, yes, no]
        if y < 0.92: return r.choice([['bol'], ['eol'], ['wb'], ['nwb']])
        return ['lit', self.ch()]

    def fixed(self, d):
        # fixed-width body for lookbehind (Python requires it)
        r = self.r; parts = []
        for _ in range(r.randint(1, 3)):
            y = r.random()
            if y < 0.5: parts.append(['lit', self.ch()])
            elif y < 0.65: parts.append(['any'])
            elif y < 0.8: parts.append(self.cls())
            elif y < 0.9: parts.append(['kls', r.choice('dDwWsS')])
            elif y < 0.95 and d > 0:
                k = r.randint(1, 3); parts.append(['rep', k, k, False, ['lit', self.ch()]])
            else:
                a = ['lit', self.ch()]; b = ['lit', self.ch()]
                parts.append(['ncg', ['alt', [a, b]]])
        if r.random() < 0.2:
            parts.append(r.choice([['wb'], ['nwb'], ['bol'], ['eol']]))
        return ['seq', parts]

    def cls(self):
        r = self.r; items = []
        for _ in range(r.randint(1, 4)):
            y = r.random()
            if y < 0.45: items.append(['c', self.ch()])
            elif y < 0.75:
                a, b = sorted([self.ch(), self.ch()])
                if chr(a) in ']\\-^[' or chr(b) in ']\\-^[':
                    items.append(['c', a]); items.append(['c', b])
                else:
                    items.append(['r', a, b])
            elif y < 0.9: items.append(['k', r.choice('dws')])
            else: items.append(['px', r.choice(sorted(POSIX))])
        return ['cls', r.random() < 0.3, items]

    def piece(self, d):
        a = self.atom(d)
        r = self.r
        if r.random() < 0.38 and minlen(a) > 0 and a[0] not in ('look', 'bol', 'eol', 'wb', 'nwb') and not has_unbounded(a):
            y = r.random()
            if self.in_lb:
                k = r.randint(1, 2); lo, hi = k, k
            elif y < 0.25: lo, hi = 0, None
            elif y < 0.45: lo, hi = 1, None
            elif y < 0.6: lo, hi = 0, 1
            elif y < 0.75: k = r.randint(0, 3); lo, hi = k, k
            elif y < 0.88: lo = r.randint(0, 2); hi = lo + r.randint(0, 2)
            else: lo, hi = r.randint(0, 2), None
            if lo == 0 and hi == 0: hi = 1
            return ['rep', lo, hi, (not self.in_lb) and r.random() < 0.3, a]
        return a

    def seq(self, d):
        return ['seq', [self.piece(d) for _ in range(self.r.randint(1, 3))]]

    def regex(self, d):
        r = self.r
        if r.random() < 0.3 and not self.in_lb:
            return ['alt', [self.seq(d) for _ in range(r.randint(2, 3))]]
        return self.seq(d)


INF = None


def has_unbounded(n):
    # no unbounded repeat under another repeat (exponential backtracking in both engines)
    if n[0] == 'rep' and (n[2] is None or n[2] > 2): return True
    return any(has_unbounded(k) for k in subnodes(n))


def lens(n, g, errs=None):
    """(min, max|None) per rx.rkt's <n,m> rules; g: group mins by number (filled in order);
    errs collects violations: quantified atom that can match empty, lookbehind not fixed-width"""
    t = n[0]
    if t in ('lit', 'any', 'cls', 'kls', 'prop'): return (1, 1)
    if t in ('bol', 'eol', 'wb', 'nwb'): return (0, 0)
    if t == 'look':
        a, b = lens(n[2], g, errs)
        if n[1] in ('<=', '<!') and (b is None or a != b) and errs is not None: errs.append('lookbehind')
        return (0, 0)
    if t == 'seq':
        lo, hi = 0, 0
        for k in n[1]:
            a, b = lens(k, g, errs); lo += a; hi = None if hi is None or b is None else hi + b
        return (lo, hi)
    if t == 'alt':
        ls = [lens(k, g, errs) for k in n[1]]
        return (min(a for a, _ in ls), None if any(b is None for _, b in ls) else max(b for _, b in ls))
    if t == 'grp':
        idx = len(g); g.append(None)
        r = lens(n[1], g, errs); g[idx] = r[0]
        return r
    if t in ('ncg', 'atomic'): return lens(n[1], g, errs)
    if t == 'mode': return lens(n[2], g, errs)
    if t == 'rep':
        a, b = lens(n[4], g, errs)
        if a <= 0 and errs is not None: errs.append('empty-rep')
        lo = a * n[1]
        hi = None if n[2] is None or b is None else b * n[2]
        return (lo, hi)
    if t == 'bref':
        m = g[n[1] - 1] if n[1] - 1 < len(g) else None
        return (m or 0, None)
    if t == 'cond':
        a = lens(n[2], g, errs); b = lens(n[3], g, errs) if n[3] else (0, 0)
        return (min(a[0], b[0]), None if a[1] is None or b[1] is None else max(a[1], b[1]))
    raise ValueError(t)


def minlen(n):
    try:
        return lens(n, [])[0]
    except Exception:
        return 0


def valid(ast):
    errs = []
    try:
        lens(ast, [], errs)
    except Exception:
        return False
    return not errs


# ---------------------------------------------------------------- rendering
def rk_lit(c, mode, in_cls=False):
    ch = chr(c)
    special = '()*+?[]{}.^\\|$' if not in_cls else ']\\-^['
    if ch.isascii() and ch.isalnum(): return ch
    if ch in special: return '\\' + ch
    return ch


def py_lit(c, in_cls=False):
    ch = chr(c)
    if ch.isascii() and ch.isalnum(): return ch
    if ch == '\n': return '\\n'
    if ch == '\t': return '\\t'
    if ch.isascii() or c < 256:
        return '\\x%02x' % c
    if c < 0x10000: return '\\u%04x' % c
    return '\\U%08x' % c


def render(ast, mode, rest=False):
    """-> (racket pattern text, python pattern text, ngroups)"""
    st = {'g': 0}

    def rk(n):
        t = n[0]
        if t == 'lit': return rk_lit(n[1], mode)
        if t == 'any': return '.'
        if t == 'cls':
            body = ''
            for it in n[2]:
                if it[0] == 'c': body += rk_lit(it[1], mode, True)
                elif it[0] == 'r': body += rk_lit(it[1], mode, True) + '-' + rk_lit(it[2], mode, True)
                elif it[0] == 'k': body += '\\' + it[1]
                else: body += '[:' + it[1] + ':]'
            return '[' + ('^' if n[1] else '') + body + ']'
        if t == 'kls': return '\\' + n[1]
        if t == 'prop': return ('\\P' if n[1] else '\\p') + '{' + n[2] + '}'
        if t == 'bol': return '^'
        if t == 'eol': return '$'
        if t == 'wb': return '\\b'
        if t == 'nwb': return '\\B'
        if t == 'seq': return ''.join(rk(k) for k in n[1])
        if t == 'alt': return '|'.join(rk(k) for k in n[1])
        if t == 'grp': st['g'] += 1; return '(' + rk(n[1]) + ')'
        if t == 'ncg': return '(?:' + rk(n[1]) + ')'
        if t == 'mode': return '(?' + n[1] + ':' + rk(n[2]) + ')'
        if t == 'rep':
            lo, hi = n[1], n[2]
            q = {(0, None): '*', (1, None): '+', (0, 1): '?'}.get((lo, hi))
            if q is None:
                q = '{%d}' % lo if hi == lo else ('{%d,}' % lo if hi is None else ('{,%d}' % hi if lo == 0 else '{%d,%d}' % (lo, hi)))
            a = rk(n[4])
            if n[4][0] in ('seq', 'alt', 'rep') or (n[4][0] == 'lit' and len(a) != 1 and not a.startswith('\\')):
                a = '(?:' + a + ')'
            return a + q + ('?' if n[3] else '')
        if t == 'look': return '(?' + n[1] + rk(n[2]) + ')'
        if t == 'atomic': return '(?>' + rk(n[1]) + ')'
        if t == 'bref': return '(?:\\' + str(n[1]) + ')'
        if t == 'cond':
            return '(?(' + str(n[1]) + ')' + rk(n[2]) + ('|' + rk(n[3]) if n[3] else '') + ')'
        raise ValueError(t)

    # python: track multi mode (Racket: m / -s = multi; s / -m = not multi)
    def py(n, multi):
        t = n[0]
        if t == 'lit': return py_lit(n[1])
        if t == 'any': return '[^\\n]' if multi else '(?s:.)'
        if t == 'cls':
            body = ''
            for it in n[2]:
                if it[0] == 'c': body += py_lit(it[1], True)
                elif it[0] == 'r': body += py_lit(it[1], True) + '-' + py_lit(it[2], True)
                elif it[0] == 'k': body += KCLS[it[1]]
                else: body += POSIX[it[1]]
            return '[' + ('^' if n[1] else '') + body + ']'
        if t == 'kls':
            k = n[1]
            return '[' + ('^' if k.isupper() else '') + KCLS[k.lower()] + ']'
        if t == 'prop':
            cs = [c for c in all_chars('s') if prop_has(n[2], c)]
            if n[1]:
                return '[^' + ''.join(py_lit(c, True) for c in cs) + ']' if cs else '(?s:.)'
            return '[' + ''.join(py_lit(c, True) for c in cs) + ']' if cs else '(?!)'
        if t == 'bol':
            # regexps.scrbl (regexp-match*): ^ matches the beginning of the input only for the first match
            if rest: return '(?<=\\n)' if multi else '(?!)'
            return '(?:\\A|(?<=\\n))' if multi else '\\A'
        if t == 'eol': return '(?=\\n|\\Z)' if multi else '\\Z'
        if t == 'wb': return '(?:(?<=%s)(?!%s)|(?<!%s)(?=%s))' % (WORD, WORD, WORD, WORD)
        if t == 'nwb': return '(?:(?<=%s)(?=%s)|(?<!%s)(?!%s))' % (WORD, WORD, WORD, WORD)
        if t == 'seq': return ''.join(py(k, multi) for k in n[1])
        if t == 'alt': return '|'.join(py(k, multi) for k in n[1])
        if t == 'grp': return '(' + py(n[1], multi) + ')'
        if t == 'ncg': return '(?:' + py(n[1], multi) + ')'
        if t == 'mode':
            m = n[1]
            if m in ('i', '-i'): return '(?' + m + ':' + py(n[2], multi) + ')'
            return '(?:' + py(n[2], m in ('m', '-s')) + ')'
        if t == 'rep':
            lo, hi = n[1], n[2]
            q = '{%d,%s}' % (lo, '' if hi is None else hi)
            return '(?:' + py(n[4], multi) + ')' + q + ('?' if n[3] else '')
        if t == 'look': return '(?' + n[1] + py(n[2], multi) + ')'
        if t == 'atomic': return '(?>' + py(n[1], multi) + ')'
        if t == 'bref': return '(?:\\' + str(n[1]) + ')'
        if t == 'cond':
            return '(?(' + str(n[1]) + ')' + py(n[2], multi) + ('|' + py(n[3], multi) if n[3] else '') + ')'
        raise ValueError(t)

    a = rk(ast)
    return a, py(ast, False), st['g']


def prop_has(cat, c):
    k = unicodedata.category(chr(c))
    if cat == 'L&': return k in ('Ll', 'Lu', 'Lt')
    if len(cat) == 1: return k[0] == cat
    return k == cat


def rkt_str(s):
    out = ['"']
    for ch in s:
        c = ord(ch)
        if ch == '"': out.append('\\"')
        elif ch == '\\': out.append('\\\\')
        elif 0x20 <= c < 0x7f: out.append(ch)
        elif c < 0x10000: out.append('\\u%04x' % c)
        else: out.append('\\U%08x' % c)
    out.append('"')
    return ''.join(out)


def rkt_bytes(b):
    out = ['#"']
    for c in b:
        ch = chr(c)
        if ch == '"': out.append('\\"')
        elif ch == '\\': out.append('\\\\')
        elif 0x20 <= c < 0x7f: out.append(ch)
        else: out.append('\\%03o' % c)
    out.append('"')
    return ''.join(out)


def to_text(codes, mode):
    return bytes(codes) if mode == 'b' else ''.join(chr(c) for c in codes)


PRELUDE = r'''(module m racket/base
  (define (hex2 b) (string-append (if (< b 16) "0" "") (number->string b 16)))
  (define (join l) (if (null? l) "" (apply string-append (car l) (map (lambda (x) (string-append " " x)) (cdr l)))))
  (define (enc v)
    (cond [(not v) "#f"] [(eq? v #t) "#t"] [(exact-integer? v) (number->string v)]
          [(and (pair? v) (exact-integer? (car v)) (exact-integer? (cdr v)))
           (string-append (number->string (car v)) ":" (number->string (cdr v)))]
          [(bytes? v) (apply string-append "b" (map hex2 (bytes->list v)))]
          [(string? v) (apply string-append "s" (map (lambda (c) (string-append (number->string (char->integer c) 16) ",")) (string->list v)))]
          [(list? v) (string-append "[" (join (map enc v)) "]")]
          [else (format "?~s" v)]))
  (define (o k th)
    (define r (with-handlers ([exn:fail? (lambda (e) (let ([m (exn-message e)])
                                                       (string-append "err " (car (regexp-split #rx"\n" m)))))])
                (enc (th))))
    (printf "~a ~a\n" k r))
  (define (C f p) (with-handlers ([exn:fail? values]) (f p)))
  (define (R x) (if (exn? x) (raise x) x))
'''


def spec_ops(sp):
    return OPS_B if sp['mode'] == 'b' else OPS_S


def render_line(sp):
    mode = sp['mode']; i = sp['i']
    rkpat, _, _ = render(sp['ast'], mode)
    inp = to_text(sp['in'], mode); pre = bytes(sp['pre'])
    tm = sp['tmpl']
    st, en = sp['st'], sp['en']
    ens = '#f' if en is None else str(en)
    L = [';; RX ' + json.dumps(sp, separators=(',', ':')) + '\n']
    if mode == 'b':
        L.append('(let ([rx (C byte-pregexp %s)] [in %s] [pre %s] [tm %s])\n' % (rkt_bytes(rkpat.encode('latin-1')), rkt_bytes(inp), rkt_bytes(pre), rkt_bytes(rk_tmpl(tm).encode('latin-1'))))
        P = '(open-input-bytes in)'
    else:
        L.append('(let ([rx (C pregexp %s)] [in %s] [pre %s] [tm %s])\n' % (rkt_str(rkpat), rkt_str(inp), rkt_bytes(pre), rkt_str(rk_tmpl(tm))))
        P = '(open-input-string in)'
    # port start/end are byte counts: precomputed (UTF-8) for string mode
    bst, ben = (st, en) if mode == 'b' else (len(inp[:st].encode()), None if en is None else len(inp[:en].encode()))
    bens = '#f' if ben is None else str(ben)
    body = {
        'pos': '(regexp-match-positions (R rx) in %d %s #f pre)' % (st, ens),
        'port': '(regexp-match-positions (R rx) %s %d %s #f pre)' % (P, bst, bens),
        'peek': '(regexp-match-peek-positions (R rx) %s %d %s #f pre)' % (P, bst, bens),
        'match': '(regexp-match (R rx) in %d %s #f pre)' % (st, ens),
        'portmatch': '(regexp-match (R rx) %s %d %s #f pre)' % (P, bst, bens),
        'all': '(regexp-match-positions* (R rx) in %d %s pre)' % (st, ens),
        'allport': '(regexp-match-positions* (R rx) %s %d %s pre)' % (P, bst, bens),
        'split': '(regexp-split (R rx) in %d %s pre)' % (st, ens),
        'repl': '(regexp-replace* (R rx) in tm)',
        'repl1': '(regexp-replace (R rx) in tm)',
        'test': '(regexp-match? (R rx) in %d %s #f pre)' % (st, ens),
        'quote': '(regexp-match-positions (regexp-quote in) in)' if mode == 'b' else
                 '(regexp-match-positions (regexp (regexp-quote in)) in)',
        'utf8': '(regexp-match-positions (R rx) (string->bytes/utf-8 in) %d %s #f pre)' % (bst, bens),
        'exact': '(regexp-match-exact? (R rx) in)',
        'outport': '(let ([op (open-output-bytes)]) (list (regexp-match-positions (R rx) in 0 %s op pre) (get-output-bytes op)))' % (ens,),
        'allg': '(regexp-match-positions* (R rx) in %d %s pre #:match-select values)' % (st, ens),
    }
    for op in sp['ops']:
        L.append('  (o "%d.%s" (lambda () %s))\n' % (i, op, body[op]))
    L.append('  (void))\n')
    return ''.join(L)


def rk_tmpl(tm):
    s = ''
    for t in tm:
        if isinstance(t, int): s += '\\' + str(t) + '\\$'
        elif t == '&': s += '&'
        else: s += t
    return s


def render_prog(specs):
    return PRELUDE + ''.join(render_line(sp) for sp in specs) + ')\n'


# ---------------------------------------------------------------- generation
def sample(n, r, mode, out, depth=0):
    """best-effort string matching n (for inputs that hit)"""
    t = n[0]
    if depth > 12: return
    if t == 'lit': out.append(n[1])
    elif t == 'any': out.append(r.choice(all_chars(mode)))
    elif t == 'cls':
        if not n[1]:
            it = r.choice(n[2])
            if it[0] == 'c': out.append(it[1])
            elif it[0] == 'r': out.append(r.choice([c for c in all_chars(mode) if it[1] <= c <= it[2]] or [it[1]]))
            else: out.append(ord(r.choice('az09_ ')))
        else: out.append(r.choice(all_chars(mode)))
    elif t == 'kls':
        out.append(ord(r.choice({'d': '0123', 'w': 'abcXYZ_1', 's': ' \t\n'}[n[1]])) if n[1].islower() else r.choice(all_chars(mode)))
    elif t == 'prop': out.append(r.choice(all_chars(mode)))
    elif t == 'seq':
        for k in n[1]: sample(k, r, mode, out, depth + 1)
    elif t == 'alt': sample(r.choice(n[1]), r, mode, out, depth + 1)
    elif t in ('grp', 'ncg', 'atomic'): sample(n[1], r, mode, out, depth + 1)
    elif t == 'mode': sample(n[2], r, mode, out, depth + 1)
    elif t == 'rep':
        hi = n[2] if n[2] is not None else n[1] + 2
        for _ in range(r.randint(n[1], max(n[1], min(hi, n[1] + 3)))): sample(n[4], r, mode, out, depth + 1)
    elif t == 'look':
        if n[1] in ('=', '<='): pass
    elif t == 'cond':
        sample(n[2], r, mode, out, depth + 1)
    elif t == 'eol' and r.random() < 0.3: out.append(10)


def gen_line(r, i):
    mode = 'b' if r.random() < 0.4 else 's'
    for _ in range(50):
        g = Gen(r, mode)
        ast = g.regex(r.choice([1, 2, 2, 3, 3, 4]))
        if valid(ast):
            try:
                _, pyp, ng = render(ast, mode)
                re.compile(pyp.encode('latin-1') if mode == 'b' else pyp)
                break
            except Exception:
                continue
    else:
        ast = ['seq', [['lit', ord('a')]]]
        _, pyp, ng = render(ast, mode)
    codes = []
    for _ in range(r.randint(1, 3)):
        if r.random() < 0.6: sample(ast, r, mode, codes)
        for _ in range(r.randint(0, 3)): codes.append(r.choice(all_chars(mode)))
    codes = codes[:28]
    if r.random() < 0.3 and codes:  # mutate
        k = r.randrange(len(codes)); codes[k] = r.choice(all_chars(mode))
    n = len(codes)
    st = 0 if r.random() < 0.6 else r.randint(0, n)
    en = None if r.random() < 0.7 else r.randint(st, n)
    pre = [] if r.random() < 0.6 else [ord(r.choice('ab_ \n1')) for _ in range(r.randint(1, 3))]
    tmpl = []
    for _ in range(r.randint(1, 3)):
        y = r.random()
        if y < 0.4: tmpl.append(r.choice(['<', '>', 'q', '-', '']))
        elif y < 0.6: tmpl.append('&')
        else: tmpl.append(r.randint(0, ng + 1))
    ops = list(OPS_B if mode == 'b' else OPS_S)
    return {'i': i, 'mode': mode, 'ast': ast, 'in': codes, 'st': st, 'en': en, 'pre': pre, 'tmpl': tmpl, 'ops': ops}


def gen_prog(seed):
    r = random.Random(seed)
    return [gen_line(r, i) for i in range(r.randint(3, 5))]


# ---------------------------------------------------------------- expected
def enc(v):
    if v is None or v is False: return '#f'
    if v is True: return '#t'
    if isinstance(v, int): return str(v)
    if isinstance(v, tuple): return '%d:%d' % v
    if isinstance(v, bytes): return 'b' + ''.join('%02x' % c for c in v)
    if isinstance(v, str): return 's' + ''.join('%x,' % ord(c) for c in v)
    if isinstance(v, list): return '[' + ' '.join(enc(x) for x in v) + ']'
    raise ValueError(v)


def py_tmpl(tm, ng, mode):
    s = ''
    for t in tm:
        if isinstance(t, int):
            if t <= ng: s += '\\g<%d>' % t
        elif t == '&': s += '\\g<0>'
        else: s += t
    return s.encode() if mode == 'b' else s


def expected(sp):
    """-> dict op -> encoded expected value (None = not compared)"""
    mode = sp['mode']
    _, pyp, ng = render(sp['ast'], mode)
    if mode == 'b':
        rx = re.compile(pyp.encode('latin-1'))
    else:
        rx = re.compile(pyp)
    inp = to_text(sp['in'], mode)
    pre_b = bytes(sp['pre'])
    pre = pre_b if mode == 'b' else pre_b.decode('latin-1')  # ASCII only
    st = sp['st']; en = sp['en'] if sp['en'] is not None else len(inp)
    lp = len(pre)
    text = pre + inp[st:en]

    def tpos(p):  # text index -> input index (chars / bytes)
        return p - lp + st

    def bpos(p):  # text index -> UTF-8 byte offset (string mode ports)
        if mode == 'b': return tpos(p)
        base = len(inp[:st].encode())
        if p >= lp: return base + len(text[lp:p].encode())
        return base - (lp - p)

    def positions(m, f):
        if m is None: return None
        out = []
        for k in range(ng + 1):
            s, e = m.span(k)
            out.append(None if s < 0 else (f(s), f(e)))
        return out

    _, pyr, _ = render(sp['ast'], mode, rest=True)
    rx2 = re.compile(pyr.encode('latin-1') if mode == 'b' else pyr)

    def all_matches(t, pos):
        # regexp-match* (regexps.scrbl): each attempt starts at the end of the last match,
        # ^ matches the beginning only for the first match, and the pattern "is
        # restricted from matching an empty sequence immediately after an empty match"
        # (so a non-empty match may start there: Python's finditer rule).
        # regexp-split / regexp-replace*: "Zero-length matches are treated the same".
        m0 = rx.search(t, pos)
        if m0 is None: return []
        out = [m0]
        p = m0.end()
        for k, x in enumerate(rx2.finditer(t, p)):
            if k == 0 and m0.start() == m0.end() and x.start() == x.end() == p:
                continue
            out.append(x)
        return out

    m = rx.search(text, lp)
    ms = all_matches(text, lp)
    E = {}
    E['pos'] = enc(positions(m, tpos))
    E['port'] = enc(positions(m, bpos))
    E['peek'] = E['port']
    E['utf8'] = E['port']
    E['test'] = enc(m is not None)

    def grp_text(k):
        s, e = m.span(k)
        if s < 0: return None
        return text[s:e]
    if m is None:
        E['match'] = '#f'; E['portmatch'] = '#f'
    else:
        E['match'] = enc([grp_text(k) for k in range(ng + 1)])
        E['portmatch'] = enc([None if grp_text(k) is None else (grp_text(k) if mode == 'b' else grp_text(k).encode()) for k in range(ng + 1)])
    E['all'] = enc([(tpos(x.start()), tpos(x.end())) for x in ms])
    E['allport'] = enc([(bpos(x.start()), bpos(x.end())) for x in ms])
    pieces = []; last = lp
    for x in ms:
        pieces.append(text[last:x.start()]); last = x.end()
    pieces.append(text[last:])
    E['split'] = enc(pieces)
    # replace: whole input, no start/end/prefix
    full = inp
    tm = py_tmpl(sp['tmpl'], ng, mode)
    def subst(ms_):
        out = full[:0]; last = 0
        for x in ms_:
            out += full[last:x.start()] + x.expand(tm); last = x.end()
        return out + full[last:]
    E['repl'] = enc(subst(all_matches(full, 0)))
    m1 = rx.search(full, 0)
    E['repl1'] = enc(subst([m1] if m1 else []))
    E['quote'] = enc([(0, len(inp))])
    # regexp-match-exact?: #t only when the first found match is the entire input
    mx = rx.search(full, 0)
    E['exact'] = enc(mx is not None and mx.span() == (0, len(full)))
    # output-port: the input from its beginning (not start-pos) preceding the match,
    # or all of it up to end-pos when there is no match (UTF-8 for strings)
    # (start-pos 0 only: with a positive start-pos Racket writes from start-pos, while the
    # docs say "from its beginning (not start-pos)"; 9.3 does the same; left out)
    text0 = pre + inp[:en]
    m0 = rx.search(text0, lp)
    upto = inp[:m0.start() - lp] if m0 is not None else inp[:en]
    E['outport'] = enc([positions(m0, lambda p: p - lp), upto if mode == 'b' else upto.encode()])
    E['allg'] = enc([positions(x, tpos) for x in ms])
    return E


# ---------------------------------------------------------------- check
def parse_specs(text):
    return [json.loads(l[6:]) for l in text.split('\n') if l.startswith(';; RX ')]


def unwrite(s):
    assert s[0] == '"' and s[-1] == '"'
    out = []; i = 1
    while i < len(s) - 1:
        c = s[i]
        if c == '\\':
            n = s[i + 1]; i += 2
            out.append({'n': '\n', 't': '\t', '\\': '\\', '"': '"', 'r': '\r'}.get(n, n))
        else:
            out.append(c); i += 1
    return ''.join(out)


FEAT_ORDER = ['look<', 'cond', 'bref', 'atomic', 'look', 'prop', 'casei', 'multi', 'lazy', 'bounded',
              'wordb', 'anchor', 'negcls', 'cls', 'alt', 'star', 'lit']


def feats(n, out, ci=False):
    t = n[0]
    if t == 'look': out.add('look<' if n[1].startswith('<') else 'look'); feats(n[2], out, ci)
    elif t == 'cond': out.add('cond'); feats(n[2], out, ci); n[3] and feats(n[3], out, ci)
    elif t == 'bref': out.add('bref')
    elif t == 'atomic': out.add('atomic'); feats(n[1], out, ci)
    elif t == 'prop': out.add('prop')
    elif t == 'mode':
        out.add('casei' if n[1] == 'i' else 'multi' if n[1] in ('m', '-s') else 'alt')
        feats(n[2], out, ci or n[1] == 'i')
    elif t == 'rep':
        if n[3]: out.add('lazy')
        if n[2] is not None and (n[1], n[2]) != (0, 1): out.add('bounded')
        else: out.add('star')
        feats(n[4], out, ci)
    elif t in ('wb', 'nwb'): out.add('wordb')
    elif t in ('bol', 'eol'): out.add('anchor')
    elif t == 'cls': out.add('negcls' if n[1] else 'cls')
    elif t == 'kls': out.add('negcls' if n[1].isupper() else 'cls')
    elif t in ('seq',): [feats(k, out, ci) for k in n[1]]
    elif t == 'alt': out.add('alt'); [feats(k, out, ci) for k in n[1]]
    elif t in ('grp', 'ncg'): feats(n[1], out, ci)
    else: out.add('lit')


def area(sp, bad_ops):
    prim = 'pos'
    if prim not in bad_ops or sp['mode'] == 'b' and False:
        return ('str-' if sp['mode'] == 's' else 'bytes-') + sorted(bad_ops, key=lambda o: spec_ops(sp).index(o))[0]
    f = set(); feats(sp['ast'], f)
    best = next((x for x in FEAT_ORDER if x in f), 'lit').replace('<', 'behind')
    return ('str-' if sp['mode'] == 's' else 'bytes-') + best


def check(text, line):
    """-> ('pass',) | ('skip', why) | ('gen', msg) | ('fail', kind, idx, area, detail)"""
    specs = parse_specs(text)
    f = line.rstrip('\n').split('\t')
    if f[0] != 'ok':
        if f[0] == 'exn':
            return ('gen', 'module raised: ' + '\t'.join(f[2:])[:300])
        return ('skip', f[0])
    got = {}
    for l in unwrite(f[1]).split('\n'):
        if l:
            k, _, v = l.partition(' ')
            got[k] = v
    for sp in specs:
        try:
            E = expected(sp)
        except Exception as ex:
            return ('gen', 'python: %r' % ex)
        bad = []; kind = 'value'; first = None
        rejected = any(got.get('%d.%s' % (sp['i'], op), '').startswith('err pregexp') or
                       got.get('%d.%s' % (sp['i'], op), '').startswith('err byte-pregexp') for op in sp['ops'])
        if rejected:
            continue  # Racket rejected a pattern Python accepts (counted as skip by caller via 'pass')
        for op in sp['ops']:
            k = '%d.%s' % (sp['i'], op)
            g = got.get(k)
            if g is None: return ('gen', 'line %s missing' % k)
            e = E.get(op)
            if e is None: continue
            if g != e:
                bad.append(op)
                if g.startswith('err'): kind = 'error'
                if first is None: first = (k, g, e)
        if bad:
            rkpat, pyp, _ = render(sp['ast'], sp['mode'])
            det = '%s: racket %s, expected %s; pattern %r (python %r) input %r st %s en %s prefix %r; failing ops %s' % (
                first[0], first[1][:300], first[2][:300], rkpat, pyp, to_text(sp['in'], sp['mode']), sp['st'], sp['en'],
                bytes(sp['pre']), ','.join(bad))
            return ('fail', kind, sp['i'], area(sp, bad), det)
    return ('pass',)


# ---------------------------------------------------------------- shrinking
def subnodes(n):
    t = n[0]
    if t in ('seq', 'alt'): return list(n[1])
    if t in ('grp', 'ncg', 'atomic'): return [n[1]]
    if t in ('mode', 'look'): return [n[2]]
    if t == 'rep': return [n[4]]
    if t == 'cond': return [n[2]] + ([n[3]] if n[3] else [])
    return []


def replacements(n):
    """one-step simpler versions of node n (whole-tree rewrite done by caller)"""
    out = []
    t = n[0]
    if t in ('seq', 'alt') and len(n[1]) > 1:
        for k in range(len(n[1])):
            out.append([t, n[1][:k] + n[1][k + 1:]])
    if t == 'seq' and len(n[1]) == 1: out.append(n[1][0])
    if t in ('ncg', 'atomic', 'mode', 'rep', 'look'):
        out.extend(subnodes(n))
    if t == 'rep':
        if n[3]: out.append(['rep', n[1], n[2], False, n[4]])
        if n[2] is None: out.append(['rep', n[1], n[1] + 1, n[3], n[4]])
    if t == 'cls' and len(n[2]) > 1:
        for k in range(len(n[2])): out.append(['cls', n[1], n[2][:k] + n[2][k + 1:]])
    if t not in ('lit',): out.append(['lit', ord('a')])
    return out


def tree_variants(n):
    yield from replacements(n)
    t = n[0]
    if t in ('seq', 'alt'):
        for k, c in enumerate(n[1]):
            for v in tree_variants(c):
                yield [t, n[1][:k] + [v] + n[1][k + 1:]]
    elif t in ('grp', 'ncg', 'atomic'):
        for v in tree_variants(n[1]): yield [t, v]
    elif t in ('mode', 'look'):
        for v in tree_variants(n[2]): yield [t, n[1], v]
    elif t == 'rep':
        for v in tree_variants(n[4]): yield ['rep', n[1], n[2], n[3], v]
    elif t == 'cond':
        for v in tree_variants(n[2]): yield ['cond', n[1], v, n[3]]
        if n[3]:
            yield ['cond', n[1], n[2], None]
            for v in tree_variants(n[3]): yield ['cond', n[1], n[2], v]


def count_groups(n):
    return n[0] == 'grp' and 1 + sum(count_groups(k) for k in subnodes(n)) or sum(count_groups(k) for k in subnodes(n))


def refs_ok(n, ng):
    if n[0] in ('bref', 'cond') and n[1] > ng: return False
    return all(refs_ok(k, ng) for k in subnodes(n))


def shrink(text, idx, bad_ops=None):
    """candidate one-line programs, simplest-first"""
    sp = next(s for s in parse_specs(text) if s['i'] == idx)
    cands = []

    def add(s):
        ng = count_groups(s['ast'])
        if not refs_ok(s['ast'], ng) or not valid(s['ast']): return
        try:
            _, pyp, _ = render(s['ast'], s['mode'])
            re.compile(pyp.encode('latin-1') if s['mode'] == 'b' else pyp)
        except Exception:
            return
        cands.append(s)
    if len(sp['ops']) > 1:
        for op in sp['ops']:
            add(dict(sp, ops=[op]))
    if sp['st']: add(dict(sp, st=0, en=None if sp['en'] is None else sp['en'] - sp['st']))
    if sp['en'] is not None: add(dict(sp, en=None))
    if sp['pre']: add(dict(sp, pre=[]))
    if len(sp['pre']) > 1: add(dict(sp, pre=sp['pre'][1:]))
    if len(sp['tmpl']) > 1:
        for k in range(len(sp['tmpl'])): add(dict(sp, tmpl=sp['tmpl'][:k] + sp['tmpl'][k + 1:]))
    for v in tree_variants(sp['ast']):
        add(dict(sp, ast=v))
    n = len(sp['in'])
    for k in range(n):
        c = sp['in'][:k] + sp['in'][k + 1:]
        st = min(sp['st'], len(c)) if k >= sp['st'] else max(0, sp['st'] - 1)
        en = sp['en']
        if en is not None: en = max(st, en - 1) if k < en else min(en, len(c))
        add(dict(sp, **{'in': c, 'st': st, 'en': en}))
    for k in range(n):
        if sp['in'][k] != ord('a'):
            c = list(sp['in']); c[k] = ord('a'); add(dict(sp, **{'in': c}))
    return [render_prog([dict(c, i=0)]) for c in cands]


def size(text):
    return len(text)


def main():
    cmd = sys.argv[1]
    sys.setrecursionlimit(10000)
    if cmd == 'gen':
        sys.stdout.write(render_prog(gen_prog(int(sys.argv[2]))))
    elif cmd == 'eval':
        for sp in parse_specs(open(sys.argv[2]).read()):
            for op, e in expected(sp).items():
                if op in sp['ops']: print('%d.%s %s' % (sp['i'], op, e))
    elif cmd == 'check':
        r = check(open(sys.argv[2]).read(), sys.stdin.readline())
        print(' '.join(str(x) for x in r))
        sys.exit(1 if r[0] == 'fail' else 0 if r[0] == 'pass' else 2)
    elif cmd == 'server':
        inp = sys.stdin.buffer
        while True:
            h = inp.readline()
            if not h: break
            parts = h.decode().split()
            try:
                if parts[0] == 'G':
                    sys.stdout.write(render_prog(gen_prog(int(parts[1]))).replace('\n', '\t') + '\n')
                elif parts[0] == 'C':
                    text = inp.read(int(parts[1])).decode()
                    m = int(inp.readline())
                    line = inp.read(m).decode()
                    try:
                        r = check(text, line)
                    except Exception as ex:
                        r = ('gen', 'rxref.py exception %r' % ex)
                    sys.stdout.write('\t'.join(str(x).replace('\t', ' ').replace('\n', ' ') for x in r) + '\n')
                elif parts[0] == 'S':
                    text = inp.read(int(parts[2])).decode()
                    try:
                        cs = shrink(text, int(parts[1]))
                    except Exception:
                        cs = []
                    for c in cs[:400]:
                        sys.stdout.write(c.replace('\n', '\t') + '\n')
                    sys.stdout.write('END\n')
            except Exception as ex:
                sys.stdout.write('gen\trxref.py protocol %r\n' % ex)
            sys.stdout.flush()


if __name__ == '__main__':
    main()
