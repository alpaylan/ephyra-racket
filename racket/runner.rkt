#lang racket/base
;; Runs generated module programs and prints one result line per program.
;;   racket runner.rkt server        ; framed programs on stdin: "<nbytes>\n<bytes>"
;;   racket runner.rkt file prog.rkt [variant] ; one program
;; A frame header may carry a variant: "<nbytes> <variant>\n".
;; The program text is a single `(module m racket/base ...)` form; it is
;; eval'd (compiled under whatever mode the process runs in: machine code
;; by default, interpreter under PLT_CS_INTERP=1) in a fresh namespace and
;; instantiated.  Result line (tab-separated, fields `write`n so no raw tabs
;; or newlines):
;;   ok      <output>
;;   exn     <output> <exn struct type> <first line of message>
;;   raise   <output> <written raised value>
;;   timeout <output>
;;   oom
(require racket/fasl racket/port racket/fixnum racket/flonum racket/unsafe/ops racket/list
         racket/string racket/pretty ffi/unsafe/vm racket/place racket/future)

;; Optimizer variants (third oracle, README.md "Variants"): the same module
;; compiled to machine code with one compiler toggle changed.
;;   none     default
;;   unsafe   (#%declare #:unsafe) inserted after the module header
;;   nocp0    Chez cp0 replaced by the identity (run-cp0)
;;   notr     Chez type recovery off (enable-type-recovery #f)
;;   ctx      compile-context-preservation-enabled #t (schemify inline? = #f)
;;   noconst  compile-enforce-module-constants #f
;;   cp0big   larger cp0 inlining budgets and outer-loop unrolling
;;   zo       `compile` (serializable), write + read back, eval
;;   machind  machine-independent compile, write + read back,
;;            compiled-expression-recompile, eval
;;   split    the module split in two (split-module below): provider `a` and
;;            client `m` requiring it, both eval'd in-memory (cross-module
;;            known-binding/inlining info, schemify known.rkt/find-known.rkt)
;;   splitzo  same, each module compiled, written and read back (the inline
;;            info serialized in .zo, as with raco make)
;;   splitmi  same, machine-independent compile + recompile of each module
;;   macro    the items rewritten through hygienic macros (macro-module below)
;;   macrozo  same, compiled, written and read back (serialized scope sets,
;;            binding tables and macro templates)
;;   macrosplit  split first, then rewritten; the macros are defined in `a`
;;            and used by `m` after a zo round trip of `a` (imported macros,
;;            shifted multi-scopes, deserialized syntax)
;;   macrosub  as macrosplit, the client a (module* sub #f ...) submodule
;;            of the provider (macro-sub below)
;;   opaque   literals, variable references, subexpressions and callees
;;            hidden behind a mutable identity `opq-v` (opaque-module below):
;;            no constant folding, no known-value/known-procedure info, no
;;            inlining at those sites; inlined primitives become calls of
;;            the out-of-line library procedures
;;   opaquesplit  opaque, then split (as split), in-memory
;;   ctlnoise the same sites instead wrapped in control forms that are the
;;            identity: a prompt with a fresh tag, an abort to a fresh-tag
;;            prompt whose handler evaluates the expression, dynamic-wind
;;            with void thunks, application of an empty composable
;;            continuation (rumble control.ss: metacontinuation frames,
;;            mark splices, winders)
;;   ctlsplit ctlnoise, then split, each module through a zo round trip
;;   gc       GC stress (gc-module below): sites wrapped in `gc-v` (keep the
;;            value in old objects and eq/weak tables, collect, check the
;;            tables), small collect-trip-bytes, in-place marking, object
;;            counts, a background place (parallel collector), heap check
;;   gczo     gc, compiled, written and read back
;;   gcsplit  gc, then split, each module through a zo round trip
;;   local, localpart, localzo  items moved into an internal-definition body
;;   preempt  green-thread preemption at arbitrary points (preempt-module):
;;            sites wrapped in `pre-v`, which arms the Chez timer a few ticks
;;            ahead, so the engine's timer interrupt swaps the case thread out
;;            (to a helper thread) at a later event check
;;   preemptctl  preempt, some sites wrapped in the ctlnoise forms instead
;;   preemptsplit  preempt, then split, each module through a zo round trip
;;   Chez compiler knobs Racket never sets (steering round 10); every one of
;;   them also turns on $enable-check-prelex-flags (Chez's own check that
;;   prelex referenced/assigned flags are consistent after each front pass;
;;   only run on the compile-to-port path, so half of the programs of each
;;   single-knob variant go through a zo round trip; the Chez mats run
;;   with it, mats/build.zuo `ecpf`, like `spi` and `cl`):
;;   common   commonization-level 1..9 (cpcommonize pass)
;;   noclos   $optimize-closures #f, $lift-closures #f (np-expand-closures)
;;   notrap   generate-interrupt-trap #f (no event-check code in user code)
;;   dbg      debug-level 3, generate-inspector-information #t
;;   noinl    $suppress-primitive-inlining #t (library calls, no cpprim code)
;;   chezmix  a combination of the above (+ notr, cp0big), chosen from the
;;            program text, applied to the module rewritten by opaque, local
;;            or split (or unchanged); chezmixzo: same + zo round trip
;;   future   sites evaluated in futures: (touch (future (lambda () e)))
;;            after the worker started it (future-module); futurezo: + zo;
;;            futuresplit: split + zo; gcfuture: gc knobs + a noise future
(define VARIANTS '("none" "unsafe" "nocp0" "notr" "ctx" "noconst" "cp0big" "zo" "machind"
                   "split" "splitzo" "splitmi" "macro" "macrozo" "macrosplit" "macrosub"
                   "opaque" "opaquesplit" "ctlnoise" "ctlsplit" "gc" "gczo" "gcsplit"
                   "local" "localpart" "localzo" "preempt" "preemptctl" "preemptsplit"
                   "common" "noclos" "notrap" "dbg" "noinl" "chezmix" "chezmixzo"
                   "future" "futurezo" "futuresplit" "gcfuture" "port" "portsplit"
                   "top" "topzo" "topsplit" "rtrip" "rtripzo"))

;; Metamorphic split.  The program is `(module m racket/base <prelude>
;; <items>)`; the prelude ends with `(define-syntax-rule (show e) ...)`.
;; Module `a` = prelude + the items up to and including the last definition,
;; with `(provide (all-defined-out))`; module `m` = the prelude's `require`
;; + `(require 'a)` + the remaining items.  A module cannot `set!` an
;; imported variable, so `(set! x e)` in `m` for an `x` defined in `a`
;; becomes a call of a setter `(define (x:set v) (set! x v))` exported by
;; `a` (`set!` returns void, so does the setter).  Generated names are
;; unique (no shadowing), so the rewrite is purely syntactic.  `a` runs to
;; completion before `m`'s body, exactly as its forms ran first in the one
;; module, so output and results must be identical.
(define (split-module form)
  (define lang (caddr form))         ; racket/base
  (define forms (cdddr form))
  (define (show-def? f) (and (pair? f) (eq? (car f) 'define-syntax-rule)
                             (pair? (cadr f)) (eq? (car (cadr f)) 'show)))
  (define-values (pre items)
    (let loop ([fs forms] [acc '()])
      (cond [(null? fs) (error 'split "no prelude end")]
            [(show-def? (car fs)) (values (reverse (cons (car fs) acc)) (cdr fs))]
            [else (loop (cdr fs) (cons (car fs) acc))])))
  (define (def? f) (and (pair? f) (memq (car f) '(define define-values))))
  ;; split after the last definition: the calls of every defined function
  ;; (the generator's tail) are then all cross-module
  (define k (for/fold ([k 0]) ([f items] [i (in-naturals 1)]) (if (def? f) i k)))
  (define-values (prefix rest) (split-at items k))
  (define (defined-names f)
    (cond [(not (pair? f)) '()]
          [(eq? (car f) 'define) (list (if (pair? (cadr f)) (car (cadr f)) (cadr f)))]
          [(eq? (car f) 'define-values) (cadr f)]
          [else '()]))
  (define a-names (append-map defined-names (append pre prefix)))
  (define mutated (make-hasheq))
  (define (walk e)
    (cond [(and (pair? e) (eq? (car e) 'quote)) e]
          [(and (pair? e) (eq? (car e) 'set!) (pair? (cdr e)) (symbol? (cadr e))
                (memq (cadr e) a-names) (pair? (cddr e)) (null? (cdddr e)))
           (define setter (string->symbol (format "~a:set" (cadr e))))
           (hash-set! mutated (cadr e) setter)
           (list setter (walk (caddr e)))]
          [(pair? e) (cons (walk (car e)) (walk (cdr e)))]
          [else e]))
  (define rest* (map walk rest))
  (define reqs (filter (lambda (f) (and (pair? f) (eq? (car f) 'require))) pre))
  (define setters
    (for/list ([(x s) (in-hash mutated)])
      `(define (,s v) (set! ,x v))))
  (list `(module a ,lang (provide (all-defined-out)) ,@pre ,@prefix ,@setters)
        `(module m ,lang ,@reqs (require 'a) ,@rest*)))

;; ---------------------------------------------------------------------
;; Metamorphic macro rewrite (variants macro, macrozo, macrosplit; steering
;; round 4).  The generated items are rewritten through hygienic macros
;; defined in the module itself (or, for macrosplit, in the provider module
;; `a` and imported by `m`).  Every macro expands to exactly the form it
;; replaces plus bindings the user code cannot see (hygiene: the
;; introduced binders deliberately reuse names of the program's own
;; variables, prelude names like `tap`/`mv`, and `tmp`), and every template
;; keeps the user expression in tail position of the expansion, so
;; continuation marks and tail calls are unchanged.  Constructs: wrappers
;; for if/let/let*/named let/lambda/set!/application/define (module level
;; and internal: definitions produced by macro uses, use-site scopes),
;; macro-defining macros with nested ellipses, recursive macros that wrap
;; an expression in up to 40 lets (large scope sets: the scope-set
;; representation of f1a34e208d), define-syntax in internal-definition
;; contexts, set!-transformers standing for function parameters.  Generated
;; names are unique and never shadow a primitive, so the rewrite is purely
;; syntactic and the result must equal the unrewritten module's.  Choices
;; are a deterministic function of the program text.
(define base-procs
  (let ([ns (make-base-namespace)])
    (parameterize ([current-namespace ns])
      (namespace-require 'racket/fixnum)
      (namespace-require 'racket/flonum))
    (lambda (s)
      (with-handlers ([(lambda (e) #t) (lambda (e) #f)])
        (procedure? (parameterize ([current-namespace ns])
                      (namespace-variable-value s #t (lambda () #f))))))))

(define (macro-rng src)
  (define st (for/fold ([h 7]) ([c (in-string src)])
               (bitwise-and (+ (* h 31) (char->integer c)) #xFFFFFFFF)))
  (lambda (n)                           ; 0 .. n-1
    (set! st (bitwise-and (+ (* st 1103515245) 12345) #x7FFFFFFF))
    (modulo (arithmetic-shift st -8) n)))

;; names: every (define (name ...)) and [name (lambda ...)] in the program
(define (user-fn-names forms)
  (define acc (make-hasheq))
  (let walk ([e forms])
    (when (pair? e)
      (cond [(eq? (car e) 'quote) (void)]
            [else
             (when (and (eq? (car e) 'define) (pair? (cdr e)) (pair? (cadr e)) (symbol? (car (cadr e))))
               (hash-set! acc (car (cadr e)) #t))
             (when (and (symbol? (car e)) (pair? (cdr e)) (pair? (cadr e)) (eq? (car (cadr e)) 'lambda))
               (hash-set! acc (car e) #t))
             (walk (car e)) (walk (cdr e))])))
  acc)

(define (var-names forms)
  (define acc (make-hasheq))
  (let walk ([e forms])
    (cond [(and (pair? e) (eq? (car e) 'quote)) (void)]
          [(pair? e) (walk (car e)) (walk (cdr e))]
          [(and (symbol? e) (regexp-match? #rx"^[a-z]+[0-9]+$" (symbol->string e)))
           (hash-set! acc e #t)]
          [else (void)]))
  (sort (hash-keys acc) symbol<?))

;; Macro definitions; `cn` = collision names for introduced binders.
(define (macro-defs cn)
  (define (n i) (list-ref cn (modulo i (length cn))))
  `((define-syntax-rule (m-def-if name N)
      (define-syntax-rule (name c t e) (let ([N c]) (if N t e))))
    (m-def-if m-if ,(n 0))
    (define-syntax-rule (m-def-app name N)
      (define-syntax name
        (syntax-rules ()
          [(_ f a (... ...)) (let ([N 0]) (f a (... ...)))])))
    (m-def-app m-app ,(n 1))
    (define-syntax (m-app2 stx)
      (syntax-case stx ()
        [(_ f a ...) (with-syntax ([(t ...) (generate-temporaries #'(a ...))])
                       #'(#%app f a ...))]))
    (define-syntax m-let
      (syntax-rules ()
        [(_ ([x e] ...) b ...) (let-values ([(x) e] ...) (let ([,(n 2) 'm-let]) b ...))]))
    (define-syntax m-let*
      (syntax-rules ()
        [(_ () b ...) (let () b ...)]
        [(_ ([x e] r ...) b ...) (let ([x e]) (m-let* (r ...) b ...))]))
    (define-syntax-rule (m-nlet name ([x e] ...) b ...)
      (let ([,(n 3) 'm-nlet]) (let name ([x e] ...) b ...)))
    (define-syntax-rule (m-lambda args b ...)
      (lambda args (define ,(n 4) 'm-lambda) b ...))
    (define-syntax (m-set! stx)
      (syntax-case stx ()
        [(_ x e) (identifier? #'x) #'(let ([,(n 5) e]) (set! x ,(n 5)))]))
    (define-syntax-rule (m-def x e) (begin (define ,(n 6) 'm-def) (define x e)))
    (define-syntax m-define
      (syntax-rules ()
        [(_ (f . args) b ...) (begin (define ,(n 7) 'm-define) (define (f . args) b ...))]))
    (begin-for-syntax (define (m-dec k) (sub1 k)))
    (define-syntax (m-deep stx)
      (syntax-case stx ()
        [(_ k e) (let ([k* (syntax-e #'k)])
                   (if (zero? k*)
                       #'e
                       (with-syntax ([km (m-dec k*)])
                         #'(let ([,(n 8) k]) (m-deep km e)))))]))
    (define-syntax-rule (m-tap e) (let ([tap 'm-tap] [mv 'm-tap] [tmp 'm-tap]) e))
    ;; scope operations on the argument that must cancel out: an introducer
    ;; applied twice (flip), syntax-local-introduce twice, and rebuilding
    ;; the argument with datum->syntax from its own (uniform) context
    (define-syntax (m-flip stx)
      (syntax-case stx ()
        [(_ e) (let ([intro (make-syntax-introducer)])
                 (with-syntax ([e* (intro (intro #'e))])
                   #'(let ([,(n 9) 'm-flip]) e*)))]))
    (define-syntax (m-lintro stx)
      (syntax-case stx ()
        [(_ e) (with-syntax ([e* (syntax-local-introduce (syntax-local-introduce #'e))])
                 #'(let ([,(n 10) 'm-lintro]) e*))]))
    ;; local-expand: the argument fully expanded to core forms inside the
    ;; transformer, then re-expanded as already-expanded syntax; with a
    ;; stop list (#%app) only the head is expanded
    (define-syntax (m-lexp stx)
      (syntax-case stx ()
        [(_ e) (local-expand #'e 'expression '())]))
    (define-syntax (m-lexp-stop stx)
      (syntax-case stx ()
        [(_ e) (with-syntax ([e* (local-expand #'e 'expression (list #'#%app #'if))])
                 #'(let ([,(n 12) 'm-lexp]) e*))]))
    (define-syntax (m-reflect stx)
      (syntax-case stx ()
        [(_ e) (with-syntax ([e* (datum->syntax #'e (syntax->datum #'e) #'e #'e)])
                 #'(let ([,(n 11) 'm-reflect]) e*))]))))

(define (macro-rewrite-items items all-forms rng)
  (define fns (user-fn-names all-forms))
  (define (proc-head? s) (and (symbol? s) (or (hash-ref fns s #f) (base-procs s))))
  (define (pick k) (zero? (rng k)))          ; probability 1/k
  (define (maybe k) (< (rng 10) k))          ; probability k/10
  (define gensym-n 0)
  (define (fresh base) (set! gensym-n (add1 gensym-n))
    (string->symbol (format "~a~~m~a" base gensym-n)))
  ;; ren: symbol -> replacement identifier (set!-transformer macros)
  (define (wrap-arg e ren)
    (define e* (ex e ren))
    (cond [(pick 12) `(m-deep ,(add1 (rng 40)) ,e*)]
          [(pick 15) `(m-tap ,e*)]
          [(pick 25) `(,(case (rng 3) [(0) 'm-flip] [(1) 'm-lintro] [else 'm-reflect]) ,e*)]
          [(pick 20) `(,(if (zero? (rng 2)) 'm-lexp 'm-lexp-stop) ,e*)]
          [else e*]))
  (define (body bs ren) (map (lambda (b) (ex b ren)) bs))
  (define (bindings bs ren)
    (for/list ([b bs]) (list (car b) (ex (cadr b) ren))))
  (define (clauses-ok? bs) (and (list? bs) (andmap (lambda (b) (and (list? b) (= 2 (length b)) (symbol? (car b)))) bs)))
  (define (fn-body args bs ren)
    ;; function body: some parameters become set!-transformer macros
    (define params (let loop ([a args]) (cond [(pair? a) (cons (car a) (loop (cdr a)))]
                                              [(symbol? a) (list a)] [else '()])))
    (define chosen (filter (lambda (p) (maybe 4)) params))
    (define ren* (for/fold ([r ren]) ([p chosen]) (hash-set r p (fresh p))))
    (define defs
      (for/list ([p chosen])
        (define m (hash-ref ren* p))
        `(define-syntax ,m
           (make-set!-transformer
            (lambda (stx)
              (syntax-case stx (set!)
                [(set! id~ v~) #'(set! ,p v~)]
                [(id~ a~ ...) #'(,p a~ ...)]
                [id~ (identifier? #'id~) #',p]))))))
    (append defs (body bs ren*)))
  (define (ex e ren)
    (cond
      [(symbol? e) (hash-ref ren e e)]
      [(not (pair? e)) e]
      [(not (list? e)) e]
      [else
       (define h (car e))
       (define n (length e))
       (case h
         [(quote) e]
         [(if) (if (= n 4)
                   (let ([c (wrap-arg (cadr e) ren)] [t (ex (caddr e) ren)] [f (ex (cadddr e) ren)])
                     (if (maybe 6) `(m-if ,c ,t ,f) `(if ,c ,t ,f)))
                   e)]
         [(begin and or when unless show writeln)
          `(,h ,@(body (cdr e) ren))]
         [(with-continuation-mark)
          `(,h ,@(body (cdr e) ren))]
         [(let)
          (cond
            [(and (>= n 3) (symbol? (cadr e)) (clauses-ok? (caddr e)))
             `(,(if (maybe 5) 'm-nlet 'let) ,(cadr e) ,(bindings (caddr e) ren) ,@(body (cdddr e) ren))]
            [(and (>= n 3) (clauses-ok? (cadr e)))
             `(,(if (maybe 5) 'm-let 'let) ,(bindings (cadr e) ren) ,@(body (cddr e) ren))]
            [else e])]
         [(let* letrec)
          (if (and (>= n 3) (clauses-ok? (cadr e)))
              `(,(if (and (eq? h 'let*) (maybe 5)) 'm-let* h) ,(bindings (cadr e) ren) ,@(body (cddr e) ren))
              e)]
         [(let-values)
          (if (>= n 3)
              `(let-values ,(for/list ([b (cadr e)]) (list (car b) (ex (cadr b) ren))) ,@(body (cddr e) ren))
              e)]
         [(lambda)
          (if (>= n 3)
              `(,(if (maybe 4) 'm-lambda 'lambda) ,(cadr e) ,@(body (cddr e) ren))
              e)]
         [(define)
          (cond [(and (pair? (cadr e)) (>= n 3))
                 `(,(if (maybe 5) 'm-define 'define) ,(cadr e) ,@(fn-body (cdr (cadr e)) (cddr e) ren))]
                [(and (symbol? (cadr e)) (= n 3))
                 `(,(if (maybe 5) 'm-def 'define) ,(cadr e) ,(ex (caddr e) ren))]
                [else e])]
         [(define-values)
          (if (= n 3) `(define-values ,(cadr e) ,(ex (caddr e) ren)) e)]
         [(set!)
          (if (and (= n 3) (symbol? (cadr e)))
              `(,(if (maybe 6) 'm-set! 'set!) ,(hash-ref ren (cadr e) (cadr e)) ,(ex (caddr e) ren))
              e)]
         [(cond)
          `(cond ,@(for/list ([c (cdr e)])
                     (if (list? c)
                         (map (lambda (x) (if (memq x '(else =>)) x (ex x ren))) c)
                         c)))]
         [(case)
          (if (>= n 2)
              `(case ,(ex (cadr e) ren)
                 ,@(for/list ([c (cddr e)])
                     (if (and (list? c) (pair? c)) (cons (car c) (body (cdr c) ren)) c)))
              e)]
         [(with-handlers parameterize)
          (if (and (>= n 3) (list? (cadr e)) (andmap (lambda (c) (and (list? c) (= 2 (length c)))) (cadr e)))
              `(,h ,(for/list ([c (cadr e)]) (list (ex (car c) ren) (ex (cadr c) ren))) ,@(body (cddr e) ren))
              e)]
         [(for/sum for/list for)
          (if (and (>= n 3) (clauses-ok? (cadr e)))
              `(,h ,(bindings (cadr e) ren) ,@(body (cddr e) ren))
              e)]
         [(for/fold)
          (if (and (>= n 4) (clauses-ok? (cadr e)) (clauses-ok? (caddr e)))
              `(,h ,(bindings (cadr e) ren) ,(bindings (caddr e) ren) ,@(body (cdddr e) ren))
              e)]
         [else
          (cond
            [(or (proc-head? h) (hash-ref ren h #f)
                 (and (symbol? h) (regexp-match? #rx"^[a-z]+[0-9]+$" (symbol->string h))))
             (define args (map (lambda (a) (wrap-arg a ren)) (cdr e)))
             (define f (hash-ref ren h h))
             (case (rng 10)
               [(0 1 2) `(m-app ,f ,@args)]
               [(3) `(m-app2 ,f ,@args)]
               [else `(,f ,@args)])]
            [(pair? h)                     ; ((lambda ...) args) etc.
             (map (lambda (a) (ex a ren)) e)]
            [else e])])]))   ; unknown syntactic form: unchanged
  (map (lambda (it) (ex it (hash))) items))

;; `quote-syntax-dummy` placeholder: the identifier case of the
;; set!-transformer expands to the parameter itself.
(define (fix-dummy d)
  (let walk ([e d])
    (cond [(and (pair? e) (eq? (car e) 'quote-syntax-dummy)) (cadr e)]
          [(pair? e) (cons (walk (car e)) (walk (cdr e)))]
          [else e])))

(define (split-prelude forms)
  (define (show-def? f) (and (pair? f) (eq? (car f) 'define-syntax-rule)
                             (pair? (cadr f)) (eq? (car (cadr f)) 'show)))
  (let loop ([fs forms] [acc '()])
    (cond [(null? fs) (error 'macro "no prelude end")]
          [(show-def? (car fs)) (values (reverse (cons (car fs) acc)) (cdr fs))]
          [else (loop (cdr fs) (cons (car fs) acc))])))

(define (macro-cn all src)
  (define vs (var-names all))
  (append (if (null? vs) '(x0) vs) '(tmp tap mv)))

;; single module: (module m racket/base <prelude> <macro defs> <items'>)
(define (macro-module form src)
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng src))
  (define cn (macro-cn (cdddr form) src))
  (define cn* (shuffle-det cn rng))
  `(module m ,lang (require (for-syntax racket/base)) ,@pre ,@(macro-defs cn*)
     ,@(macro-rewrite-items items (cdddr form) rng)))

(define (shuffle-det l rng)
  (let loop ([l l] [acc '()])
    (if (null? l) acc
        (let ([x (list-ref l (rng (length l)))])
          (loop (remq x l) (cons x acc))))))

;; macrosub: as macrosplit, but the client is a `(module* sub #f ...)`
;; submodule of the provider (enclosing module's bindings and macros seen
;; through a shifted module path index: multi-scopes), instantiated after
;; the enclosing module by (dynamic-require '(submod 'm sub) #f).  The
;; enclosing module is `m` so the runner's (dynamic-require ''m #f) runs it.
(define (macro-sub form src)
  (define ms (macro-split form src))
  (define a (car ms))
  (define m (cadr ms))
  ;; a = (module a lang (require (for-syntax racket/base)) (provide ...) <body>)
  ;; m = (module m lang (require (for-syntax racket/base)) <reqs> (require 'a) <items>)
  (define m-items (filter (lambda (f) (not (and (pair? f) (eq? (car f) 'require)))) (cdddr m)))
  `(module m ,(caddr a) ,@(cdddr a)
     (module* sub #f ,@m-items)))

;; split first (setters for set! across modules), then rewrite both; the
;; macros live in `a` and are exported by (all-defined-out) to `m`.
(define (macro-split form src)
  (define ms (split-module form))
  (define a (car ms))
  (define m (cadr ms))
  (define rng (macro-rng src))
  (define cn (shuffle-det (macro-cn (cdddr form) src) rng))
  ;; a = (module a lang (provide (all-defined-out)) <pre> <prefix> <setters>)
  (define-values (a-pre a-items) (split-prelude (cdr (cdddr a))))
  (define a-lang (caddr a))
  (define all (cdddr form))
  (list `(module a ,a-lang (require (for-syntax racket/base)) (provide (all-defined-out))
           ,@a-pre ,@(macro-defs cn) ,@(macro-rewrite-items a-items all rng))
        `(module m ,(caddr m) (require (for-syntax racket/base))
           ,@(macro-rewrite-items (cdddr m) all rng))))

;; ---------------------------------------------------------------------
;; Metamorphic "opaque" rewrite (variants opaque, opaquesplit; steering
;; round 5).  Selected sites are wrapped in `(opq-v e)`, where `opq-v` is a
;; module variable holding the identity and `set!` once, so neither
;; schemify nor Chez cp0/cptypes can see through it: literals stop being
;; constants (no folding), variable references lose their known
;; value/type, an application `(f a ...)` becomes `((opq-v f) a ...)`
;; (no inlining, no known-procedure call; for a primitive the out-of-line
;; library procedure instead of the inline cpprim code), `if` tests stop
;; being foldable.  Only positions whose value is a single value and that
;; are not in tail position are wrapped (application arguments, `if`
;; tests, `let`/`set!`/`define` right-hand sides that are not lambdas), and
;; callees keep their tail position, so continuation marks and tail calls
;; are unchanged; `(opq-v f)` evaluates `f` at the same point as `f` would.
;; `opq-v` matches no generated name.  Densities are a deterministic
;; function of the program text.  The output must equal the original's.
(define opaque-defs
  '((define (opq-id x) x)
    (define opq-v opq-id)
    (set! opq-v opq-id)))

(define ctl-defs
  '((define opq-tag (make-continuation-prompt-tag 'opq))))

;; ctlnoise wrappers; each evaluates `e` exactly once, in a continuation
;; that differs from the original only by frames no generated code can
;; observe (prompts and composable continuations of a tag only these
;; wrappers use; void winders).  Only used at non-tail positions.
(define (ctl-wrap e rng)
  (case (rng 5)
    [(0) `(call-with-continuation-prompt (lambda () ,e) opq-tag)]
    [(1) `(call-with-continuation-prompt (lambda () (abort-current-continuation opq-tag (lambda () ,e)))
                                         opq-tag (lambda (th) (th)))]
    [(2) `(dynamic-wind void (lambda () ,e) void)]
    [(3) `((call-with-continuation-prompt
            (lambda () (call-with-composable-continuation (lambda (k) k) opq-tag)) opq-tag)
           ,e)]
    [else `(call-with-continuation-prompt
            (lambda () (dynamic-wind void (lambda () ,e) void)) opq-tag)]))

(define (opaque-rewrite-items items all-forms rng [ctl? #f])
  (define fns (user-fn-names all-forms))
  (define (user-head? h) (and (symbol? h) (or (hash-ref fns h #f)
                                              (regexp-match? #rx"^[a-z]+[0-9]+$" (symbol->string h)))))
  (define (prim-head? h) (and (symbol? h) (not (user-head? h)) (base-procs h)))
  ;; per-program profile
  (define pre? (memq ctl? '(pre prectl)))
  (define p-lit (vector-ref (if pre? #(1 2 5) #(2 3 5)) (rng 3)))     ; 1/k literals
  (define p-var (vector-ref (if pre? #(1 2 6) #(3 6 20)) (rng 3)))    ; 1/k variable references
  (define p-expr (vector-ref (if pre? #(2 3 12) #(6 12 40)) (rng 3)))  ; 1/k other subexpressions
  ;; preempt: also arm the timer at the start of 1/k function bodies
  (define p-entry (if pre? (vector-ref #(1 2 1000000) (rng 3)) 1000000))
  (define (prologue bs) (if (pick p-entry) (cons '(pre-v (void)) bs) bs))
  (define p-user (vector-ref #(1 2 4) (rng 3)))    ; 1/k user callees
  (define p-prim (vector-ref #(1 2 4 1000000) (rng 4))) ; 1/k primitive callees
  (define (pick k) (zero? (rng k)))
  (define (lambda-form? e) (and (pair? e) (memq (car e) '(lambda case-lambda))))
  (define (literal? e) (or (number? e) (boolean? e) (char? e) (string? e)
                           (and (pair? e) (eq? (car e) 'quote))))
  (define (opq e) (cond [(eq? ctl? 'gc) `(gc-v ,e)]
                        [(eq? ctl? 'rt) `(rt-v ,e)]
                        [(eq? ctl? 'pre) `(pre-v ,e)]
                        [(eq? ctl? 'fut) `(fut-v (lambda () ,e))]
                        [(eq? ctl? 'prectl) (if (pick 3) (ctl-wrap e rng) `(pre-v ,e))]
                        [ctl? (ctl-wrap e rng)]
                        [else `(opq-v ,e)]))
  ;; a single-valued, non-tail position
  (define (arg e)
    (define e* (ex e))
    (cond [(lambda-form? e) e*]
          [(literal? e) (if (pick p-lit) (opq e*) e*)]
          [(symbol? e) (if (pick p-var) (opq e*) e*)]
          [(pick p-expr) (opq e*)]
          [else e*]))
  (define (body bs) (map ex bs))
  (define (bindings bs) (for/list ([b bs]) (list (car b) (arg (cadr b)))))
  (define (clauses-ok? bs) (and (list? bs) (andmap (lambda (b) (and (list? b) (= 2 (length b)) (symbol? (car b)))) bs)))
  (define (ex e)
    (cond
      [(not (pair? e)) e]
      [(not (list? e)) e]
      [else
       (define h (car e))
       (define n (length e))
       (case h
         [(quote) e]
         [(if) (if (= n 4) `(if ,(arg (cadr e)) ,(ex (caddr e)) ,(ex (cadddr e))) e)]
         [(begin and or when unless show writeln with-continuation-mark)
          `(,h ,@(body (cdr e)))]
         [(let)
          (cond
            [(and (>= n 3) (symbol? (cadr e)) (clauses-ok? (caddr e)))
             `(let ,(cadr e) ,(bindings (caddr e)) ,@(body (cdddr e)))]
            [(and (>= n 3) (clauses-ok? (cadr e)))
             `(let ,(bindings (cadr e)) ,@(body (cddr e)))]
            [else e])]
         [(let* letrec)
          (if (and (>= n 3) (clauses-ok? (cadr e)))
              `(,h ,(bindings (cadr e)) ,@(body (cddr e)))
              e)]
         [(let-values)
          (if (>= n 3)
              `(let-values ,(for/list ([b (cadr e)]) (list (car b) (ex (cadr b)))) ,@(body (cddr e)))
              e)]
         [(lambda)
          (if (>= n 3) `(lambda ,(cadr e) ,@(prologue (body (cddr e)))) e)]
         [(define)
          (cond [(and (pair? (cadr e)) (>= n 3)) `(define ,(cadr e) ,@(prologue (body (cddr e))))]
                [(and (symbol? (cadr e)) (= n 3)) `(define ,(cadr e) ,(arg (caddr e)))]
                [else e])]
         [(define-values)
          (if (= n 3) `(define-values ,(cadr e) ,(ex (caddr e))) e)]
         [(set!)
          (if (and (= n 3) (symbol? (cadr e))) `(set! ,(cadr e) ,(arg (caddr e))) e)]
         [(cond)
          `(cond ,@(for/list ([c (cdr e)])
                     (if (and (list? c) (pair? c))
                         (cons (if (eq? (car c) 'else) 'else (arg (car c)))
                               (map (lambda (x) (if (eq? x '=>) x (ex x))) (cdr c)))
                         c)))]
         [(case)
          (if (>= n 2)
              `(case ,(arg (cadr e))
                 ,@(for/list ([c (cddr e)])
                     (if (and (list? c) (pair? c)) (cons (car c) (body (cdr c))) c)))
              e)]
         [(with-handlers parameterize)
          (if (and (>= n 3) (list? (cadr e)) (andmap (lambda (c) (and (list? c) (= 2 (length c)))) (cadr e)))
              `(,h ,(for/list ([c (cadr e)]) (list (ex (car c)) (arg (cadr c)))) ,@(body (cddr e)))
              e)]
         [(for/sum for/list for)
          (if (and (>= n 3) (clauses-ok? (cadr e)))
              `(,h ,(for/list ([b (cadr e)]) (list (car b) (ex (cadr b)))) ,@(body (cddr e)))
              e)]
         [(for/fold)
          (if (and (>= n 4) (clauses-ok? (cadr e)) (clauses-ok? (caddr e)))
              `(,h ,(bindings (cadr e)) ,(for/list ([b (caddr e)]) (list (car b) (ex (cadr b))))
                   ,@(body (cdddr e)))
              e)]
         [else
          (cond
            [(user-head? h)
             `(,(if (pick p-user) (opq h) h) ,@(map arg (cdr e)))]
            [(prim-head? h)
             `(,(if (pick p-prim) (opq h) h) ,@(map arg (cdr e)))]
            [(pair? h) (map ex e)]
            [else e])])]))   ; unknown syntactic form: unchanged
  (map ex items))

(define (opaque-module form src [ctl? #f])
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng (string-append (if ctl? "ctl" "opaque") src)))
  `(module m ,lang ,@pre ,@(if ctl? ctl-defs opaque-defs)
     ,@(opaque-rewrite-items items (cdddr form) rng ctl?)))

;; ---------------------------------------------------------------------
;; Round trips at run time (variants rtrip, rtripzo; steering round 13).
;; The opaque sites are wrapped in `(rt-v e)`, which returns e's value v
;; unchanged after checking documented round trips on it:
;;  - write then read: reference/printer.scrbl, "write mode prints core
;;    datatypes in such a way that using read on the output produces a
;;    value that is equal? to the printed value" (only for trees of numbers,
;;    strings, byte strings, chars, interned symbols, keywords, booleans,
;;    '(), pairs and vectors);
;;  - s-exp->fasl / fasl->s-exp with #:keep-mutable? #t (also boxes and hash
;;    tables): the result must be equal? to v (reference/fasl.scrbl: the
;;    defaults "behave like the composition of write and read");
;;  - number->string / string->number in radix 10 (and 2/8/16 for exact
;;    numbers): eqv? (reference/numbers.scrbl, the printer's number syntax);
;;  - equal-hash-code of v and of each equal? copy are the same
;;    (equality.scrbl: "For any two calls with equal? values, the returned
;;    number is the same"), eqv-hash-code too for numbers; an immutable hash
;;    rebuilt in another insertion order must be equal? with the same code.
;; A violation raises `internal error: round trip ...` (kind internal).
;; Values whose written form is over 20000 chars, and calls after the
;; 3000th per case, are not checked.
(define rt-defs
  '((require (only-in racket/fasl s-exp->fasl fasl->s-exp))
    (define rt-n 0)
    (define (rt-readable? v d)
      (and (< d 200)
           (cond [(or (number? v) (string? v) (bytes? v) (char? v) (keyword? v)
                      (boolean? v) (null? v)) #t]
                 [(symbol? v) (symbol-interned? v)]
                 [(pair? v) (and (rt-readable? (car v) (add1 d)) (rt-readable? (cdr v) (add1 d)))]
                 [(vector? v) (for/and ([x (in-vector v)]) (rt-readable? x (add1 d)))]
                 [else #f])))
    (define (rt-atomic-key? k eq?-table)
      (or (fixnum? k) (char? k) (boolean? k) (null? k) (keyword? k)
          (and (symbol? k) (symbol-interned? k))
          (and (number? k) (not eq?-table))))
    (define (rt-faslable? v d)
      (and (< d 200)
           (cond [(rt-readable? v d) #t]
                 [(box? v) (rt-faslable? (unbox v) (add1 d))]
                 [(pair? v) (and (rt-faslable? (car v) (add1 d)) (rt-faslable? (cdr v) (add1 d)))]
                 [(vector? v) (for/and ([x (in-vector v)]) (rt-faslable? x (add1 d)))]
                 ;; a copy's keys are new objects: in an eq?/eqv?/equal-always?
                 ;; table they must be keys whose identity a copy keeps
                 [(hash? v) (and (not (hash-weak? v)) (not (hash-ephemeron? v))
                                 (for/and ([(k x) (in-hash v)])
                                   (and (rt-faslable? k (add1 d)) (rt-faslable? x (add1 d))
                                        (or (hash-equal? v) (rt-atomic-key? k (hash-eq? v))))))]
                 [else #f])))
    (define (rt-fail what v w)
      (error 'rt-v "internal error: round trip ~a: ~.s -> ~.s" what v w))
    (define (rt-same-hash what v w)
      (unless (= (equal-hash-code v) (equal-hash-code w))
        (rt-fail (format "~a: equal-hash-code differs" what) v w))
      (when (and (number? v) (not (= (eqv-hash-code v) (eqv-hash-code w))))
        (rt-fail (format "~a: eqv-hash-code differs" what) v w)))
    (define (rt-check v)
      (define written (let ([o (open-output-string)]) (write v o) (get-output-string o)))
      (when (< (string-length written) 20000)
        (when (rt-readable? v 0)
          (define w (with-handlers ([exn:fail? (lambda (e) (rt-fail (format "write/read raised ~s" (exn-message e)) v written))])
                      (parameterize ([read-decimal-as-inexact #t] [read-accept-reader #f])
                        (read (open-input-string written)))))
          (unless (equal? v w) (rt-fail "write/read" v w))
          (rt-same-hash "write/read" v w))
        (when (number? v)
          (for ([r (if (exact? v) '(10 2 8 16) '(10))])
            (define s (number->string v r))
            (define w (string->number s r))
            (unless (eqv? v w) (rt-fail (format "number->string/string->number radix ~a" r) v s))))
        (when (rt-faslable? v 0)
          (define w (with-handlers ([exn:fail? (lambda (e) (rt-fail (format "fasl raised ~s" (exn-message e)) v #f))])
                      (fasl->s-exp (s-exp->fasl v #:keep-mutable? #t))))
          (unless (equal? v w) (rt-fail "fasl" v w))
          (rt-same-hash "fasl" v w))
        (when (and (hash? v) (immutable? v) (rt-faslable? v 0))
          (define w (for/fold ([h (hash-copy-clear v)]) ([kv (reverse (hash->list v))])
                      (hash-set h (car kv) (cdr kv))))
          (unless (equal? v w) (rt-fail "hash rebuilt in another order" v w))
          (rt-same-hash "hash rebuilt in another order" v w))))
    (define (rt-v v)
      (set! rt-n (add1 rt-n))
      (when (< rt-n 3000) (rt-check v))
      v)))

(define (rt-module form src)
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng (string-append "rt" src)))
  `(module m ,lang ,@pre ,@rt-defs
     ,@(opaque-rewrite-items items (cdddr form) rng 'rt)))

;; ---------------------------------------------------------------------
;; GC stress (variants gc, gczo, gcsplit; steering round 6).  Garbage
;; collection must not change results (universal: no wrong result; nothing
;; in the program observes memory, weak boxes or finalizers).  The same
;; sites as the opaque rewrite are wrapped in `(gc-v e)`, which evaluates
;; `e`, keeps its value in a large old vector (old->young stores into a
;; large object, card marking) and in a weak box, runs a minor collection
;; (now and then a major one) and returns the value.  Around the case the
;; runner lowers `collect-trip-bytes` (collections at arbitrary allocation
;; points, also inside the expander/schemify/Chez compiler and the fasl
;; reader), sometimes `in-place-minimum-generation` (mark in place instead
;; of copying), sometimes enables object counts (the gc-oce collector),
;; and a background place makes Chez use the parallel collector
;; (gc-par.inc; rumble place.ss thread-preserve-ownership!).  Some cases end
;; with a Chez heap check ($enable-check-heap + a collection); any heap
;; error is reported as an internal error.
(define gc-defs
  '((define gc-keep (make-vector 5000 #f))
    (define gc-n 0)
    ;; every kept cell is a key of an eq?-table and a weak eq?-table (keys
    ;; move when collected: address-hashed tables must be rehashed); a
    ;; cell kept a few calls ago must still be found in both with its
    ;; number, else the collector lost or misplaced it
    (define gc-eq (make-hasheq))
    (define gc-weq (make-weak-hasheq))
    (define (gc-v x)
      (set! gc-n (add1 gc-n))
      (let* ([i (modulo gc-n 5000)]
             [old (vector-ref gc-keep i)]
             [cell (if (zero? (modulo gc-n 5))
                       ;; a captured (never invoked) continuation and marks
                       ;; kept alive across collections
                       (vector gc-n x (call-with-current-continuation (lambda (k) k))
                               (current-continuation-marks))
                       (vector gc-n x (make-weak-box x) (make-ephemeron x gc-n)))])
        (when old (hash-remove! gc-eq old))
        (vector-set! gc-keep i cell)
        (hash-set! gc-eq cell gc-n)
        (hash-set! gc-weq cell gc-n)
        (collect-garbage (if (and (zero? (modulo gc-n 97)) (< gc-n 400)) 'major 'minor))
        (let ([c (vector-ref gc-keep (modulo (- gc-n 3) 5000))])
          (when (and c (not (and (eqv? (hash-ref gc-eq c #f) (vector-ref c 0))
                                 (eqv? (hash-ref gc-weq c #f) (vector-ref c 0)))))
            (error 'gc-v "internal error: kept key lost from an eq table after a collection"))))
      x)))

(define (gc-module form src)
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng (string-append "gc" src)))
  `(module m ,lang ,@pre ,@gc-defs
     ,@(opaque-rewrite-items items (cdddr form) rng 'gc)))

(module gc-worker racket/base
  (require racket/place)
  (provide start)
  (define (start ch)
    (define n 4000)
    (define (mk k) (vector k (exact->inexact k) (list k (number->string k))
                           (make-bytes 3 (modulo k 256)) (box (* k k k k k k))))
    (define (ok? k c)
      (and (vector? c) (= (vector-length c) 5) (eqv? (vector-ref c 0) k)
           (eqv? (vector-ref c 1) (exact->inexact k))
           (equal? (vector-ref c 2) (list k (number->string k)))
           (equal? (vector-ref c 3) (make-bytes 3 (modulo k 256)))
           (eqv? (unbox (vector-ref c 4)) (* k k k k k k))))
    (define v (build-vector n mk))
    (define t (make-hasheq))
    (for ([c (in-vector v)]) (hash-set! t c (vector-ref c 0)))
    (let loop ()
      (define m (sync/timeout 0.002 ch))
      (when (eq? m 'check)
        (place-channel-put
         ch
         (for/and ([c (in-vector v)] [k (in-naturals)])
           (and (ok? k c) (eqv? (hash-ref t c #f) k)))))
      (for ([j 40])
        (define k (random n))
        (define old (vector-ref v k))
        (define c (mk k))
        (hash-remove! t old)
        (vector-set! v k c)
        (hash-set! t c k))
      (loop))))

(define gc-place #f)
(define (start-gc-place!)
  (unless gc-place
    ;; a second Chez thread with preserved ownership, so collections go
    ;; through the parallel collector (its sweeper owns the place's
    ;; objects).  The place keeps a heap of its own (4000 cells, each a
    ;; key of an eq?-table), replaces ~40 random cells every 2 ms (old ->
    ;; young stores, allocation interleaved with the main place's
    ;; collections) and on 'check verifies every cell and its table entry
    ;; (a plain submodule: instantiating it does not run this module's
    ;; command-line dispatch in the place)
    (set! gc-place
          (dynamic-place `(submod (file ,(path->string (variable-reference->module-source
                                                         (#%variable-reference))))
                                  gc-worker)
                         'start))
    (sleep 0.05)))

;; #t when the background place's heap is intact
(define (gc-place-ok?)
  (place-channel-put gc-place 'check)
  (sync/timeout 20 gc-place))

(define chez-trip (vm-eval 'collect-trip-bytes))
(define chez-ipmg (vm-eval 'in-place-minimum-generation))
(define chez-eoc (vm-eval 'enable-object-counts))
(define chez-check-heap (vm-eval '($primitive $enable-check-heap)))
(define chez-heap-errors (vm-eval '($primitive $check-heap-errors)))

(define (gc-variant? v) (member v '("gc" "gczo" "gcsplit" "gcfuture")))

;; returns (values restore-thunk check-heap?)
(define (set-gc-knobs! src)
  (define rng (macro-rng (string-append "gcknobs" src)))
  (start-gc-place!)
  (define trip (chez-trip))
  (define ipmg (chez-ipmg))
  (define eoc (chez-eoc))
  (chez-trip (vector-ref #(65536 262144 1048576 4194304) (rng 4)))
  (case (rng 3)
    [(0) (chez-ipmg 0)]
    [(1) (chez-ipmg 1)]
    [else (void)])
  (when (zero? (rng 4)) (chez-eoc #t))
  (values (lambda () (chez-trip trip) (chez-ipmg ipmg) (chez-eoc eoc))
          (zero? (rng 16))))

(define (heap-check-errors)
  (define before (chez-heap-errors))
  (chez-check-heap #t)
  (collect-garbage 'minor)
  (chez-check-heap #f)
  (- (chez-heap-errors) before))

(define (zo-round-trip c)
  (define o (open-output-bytes))
  (write c o)
  (parameterize ([read-accept-compiled #t])
    (read (open-input-bytes (get-output-bytes o)))))
(define chez-run-cp0 (vm-eval 'run-cp0))
(define chez-type-recovery (vm-eval 'enable-type-recovery))
(define chez-score (vm-eval 'cp0-score-limit))
(define chez-effort (vm-eval 'cp0-effort-limit))
(define chez-unroll (vm-eval 'cp0-outer-unroll-limit))
(define chez-common (vm-eval 'commonization-level))
(define chez-optclos (vm-eval '($primitive $optimize-closures)))
(define chez-liftclos (vm-eval '($primitive $lift-closures)))
(define chez-trap (vm-eval 'generate-interrupt-trap))
(define chez-debug-level (vm-eval 'debug-level))
(define chez-inspinfo (vm-eval 'generate-inspector-information))
(define chez-noinline (vm-eval '($primitive $suppress-primitive-inlining)))
(define chez-check-prelex (vm-eval '($primitive $enable-check-prelex-flags)))
(define chez-knobs2 (list chez-common chez-optclos chez-liftclos chez-trap chez-debug-level
                          chez-inspinfo chez-noinline chez-check-prelex))

;; ---------------------------------------------------------------------
;; Preemption (variants preempt, preemptctl, preemptsplit; steering round 9).
;; Racket threads are Chez engines (rumble engine.ss): when the engine's
;; timer runs out at an event check (procedure entry, loop back-edge), the
;; timer interrupt captures the metacontinuation and the scheduler swaps in
;; another thread; the case thread resumes later where it stopped.  With the
;; default quantum (thread/config.rkt TICKS 100000) that happens a handful of
;; times per case at the same few places.  Here the opaque sites are wrapped
;; in `(pre-v e)`, which evaluates `e`, then lowers the remaining ticks to
;; 1..K (K per program: 2, 8, 32 or 400), so the interrupt fires at an
;; arbitrary later event check, also inside loops with unboxed flonum locals,
;; inside prompts, dynamic-wind, parameterize, marks, handlers and
;; continuation applications.  A helper green thread (created by the runner,
;; its output discarded) is always runnable: it yields with `(sleep 0)` inside
;; its own parameterize + continuation mark and checks that both, a flonum
;; accumulator and a ring of vectors survive the swaps; a failure becomes an
;; `internal error` result line.  Expected: thread switches are not
;; observable by a program that does not share state with other threads
;; (reference/threads.scrbl: threads run concurrently; nothing allows a
;; context switch to change a single thread's results), so the output must
;; equal the default run's.
(define (preempt-defs src)
  (define rng (macro-rng (string-append "preK" src)))
  `((require (only-in ffi/unsafe/vm vm-primitive))
    (define pre-st (vm-primitive 'set-timer))
    (define pre-n 0)
    (define (pre-v x)
      (set! pre-n (add1 pre-n))
      (let ([o (pre-st 0)])
        (pre-st (if (> o 0) (min o (add1 (modulo (* pre-n 7919) ,(vector-ref #(2 8 32 400) (rng 4))))) 0)))
      x)))

(define (preempt-variant? v) (member v '("preempt" "preemptctl" "preemptsplit")))

(define (preempt-module form src [ctl? #f])
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng (string-append "preempt" src)))
  `(module m ,lang ,@pre ,@(preempt-defs src) ,@(if ctl? ctl-defs '())
     ,@(opaque-rewrite-items items (cdddr form) rng (if ctl? 'prectl 'pre))))

(define pre-param (make-parameter 0))
(define pre-swaps 0)   ; helper iterations (RKT_PRE_DEBUG prints them)
;; the helper thread; sets `fail` to a message when a check fails
(define (start-preempt-helper! fail)
  (parameterize ([current-output-port (open-output-nowhere)]
                 [current-error-port (open-output-nowhere)])
    (thread
     (lambda ()
       (with-handlers ([(lambda (e) #t)
                        (lambda (e) (set-box! fail (format "helper raised ~a"
                                                           (if (exn? e) (first-line (exn-message e)) e))))])
         (define ring (make-vector 32 #f))
         (let loop ([i 0] [acc 0.0])
           (define v (vector i (exact->inexact i) (list i (number->string i))))
           (vector-set! ring (modulo i 32) v)
           (parameterize ([pre-param i])
             (with-continuation-mark 'pre-key i
               (begin
                 (sleep 0)
                 (unless (and (eqv? (pre-param) i)
                              (eqv? (continuation-mark-set-first #f 'pre-key) i))
                   (set-box! fail "helper's parameterization or mark changed across a swap"))
                 (void))))
           (unless (fl= acc (fl* (->fl i) 0.25))
             (set-box! fail "helper's flonum accumulator changed across a swap"))
           (when (>= i 32)
             (define old (vector-ref ring (modulo (- i 31) 32)))
             (define k (- i 31))
             (unless (and (eqv? (vector-ref old 0) k) (eqv? (vector-ref old 1) (exact->inexact k))
                          (equal? (vector-ref old 2) (list k (number->string k))))
               (set-box! fail "helper's ring vector changed across a swap")))
           (set! pre-swaps (add1 pre-swaps))
           (unless (unbox fail) (loop (add1 i) (fl+ acc 0.25)))))))))

;; ---------------------------------------------------------------------
;; Futures (variants future, futurezo, futuresplit, gcfuture; steering
;; round 11).  The opaque sites are evaluated as `(fut-v (lambda () e))`:
;; the thunk becomes a future (racket/future), the runner spins a little
;; (K iterations, K per program) until a future worker pthread has started
;; it, then touches it.  So `e` runs on another Chez OS thread (its own
;; thread context, allocation area, unboxed flonum locals, event checks),
;; until it reaches a blocking operation (printing, exceptions, continuation
;; operations, parameterize...), which suspends the future until the touch
;; resumes it in the case thread (thread/future*.rkt, rumble future and
;; engine blocking, collections requested while futures run).  Futures nest
;; when a site is inside another site.  Expected: reference/futures.scrbl,
;; "The touch function forces the evaluation of the thunk inside the given
;; future, returning the values produced by thunk"; the future runs "in
;; parallel ... until it detects an attempt to perform an operation that
;; cannot run safely in parallel" and blocking operations are resumed by
;; touch, so `(touch (future (lambda () e)))` must produce what `e` does
;; (sites are single-valued, non-tail; the thunk body is a fresh frame, as
;; the argument position was).  Only one future runs at a time besides the
;; gcfuture noise future, so there are no races on the program's state.
;; After 3000 futures in one case the wrapper just calls the thunk (time).
;; `gcfuture` (server e): the gc knobs (small collect-trip-bytes, in-place
;; marking, object counts, background place) plus a noise future started
;; with the module that allocates and checks its own lists while the case
;; runs, so collections must rendezvous with running futures.
(define (future-defs src noise?)
  (define rng (macro-rng (string-append "futK" src)))
  `((require (only-in racket/future future touch current-future make-fsemaphore fsemaphore-post
                      fsemaphore-try-wait?))
    (define fut-n 0)
    (define (fut-v th)
      (set! fut-n (add1 fut-n))
      ;; half of the programs never nest futures (a future touched inside
      ;; a running future: see README for the known nested-prompt failure)
      (if (or (> fut-n 3000) ,(if (zero? (rng 2)) '(current-future) #f))
          (th)
          (let* ([s (make-fsemaphore 0)]
                 [f (future (lambda () (fsemaphore-post s) (th)))])
            (let loop ([i 0])
              (unless (or (fsemaphore-try-wait? s) (= i ,(vector-ref #(0 300 3000 30000) (rng 4))))
                (loop (add1 i))))
            (touch f))))
    ,@(if noise?
          '((define fut-stop (box #f))
            (define fut-bad (box #f))
            (define fut-noise
              (future
               (lambda ()
                 (let loop ([i 0] [keep '()])
                   (unless (or (unbox fut-stop) (> i 2000000))
                     (let ([l (list i (exact->inexact i) (vector i i) (* i i i i i))])
                       (when (and (pair? keep)
                                  (let ([o (car keep)])
                                    (not (and (eqv? (cadr o) (exact->inexact (car o)))
                                              (equal? (caddr o) (vector (car o) (car o)))
                                              (eqv? (cadddr o) (* (car o) (car o) (car o) (car o) (car o)))))))
                         (set-box! fut-bad #t))
                       (loop (add1 i) (if (< (length keep) 50) (cons l keep) (list l))))))))))
          '())))

;; the end of a gcfuture module: stop the noise future, report damage
(define future-tail
  '((set-box! fut-stop #t)
    (touch fut-noise)
    (when (unbox fut-bad)
      (error 'fut "internal error: the noise future's lists were damaged"))))

(define (future-variant? v) (member v '("future" "futurezo" "futuresplit" "gcfuture")))

(define (future-module form src [noise? #f])
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng (string-append "future" src)))
  `(module m ,lang ,@pre ,@(future-defs src noise?)
     ,@(opaque-rewrite-items items (cdddr form) rng 'fut)
     ,@(if noise? future-tail '())))

;; ---------------------------------------------------------------------
;; Metamorphic "local" rewrite (variants local, localpart; steering round 8).
;; The generated module-level items (all of them for `local`, a suffix
;; chosen from the program text for `localpart`) are moved into the body of
;; a function, an internal-definition context:
;;   (define (main%) <items'> (void)) (main%)       ; or
;;   (let () <items'> (void))                       ; a module-level expression
;; Module-level definitions (constants for schemify, known procedures,
;; cross-form inlining) become letrec* bindings of one closure body: Chez
;; cpletrec, closure conversion, local set! boxes, schemify's lift and
;; mutated-state analysis, inlining by cp0 instead of schemify.  A module body
;; prints the values of its expression forms with `current-print` and runs
;; each in a prompt for the default tag (reference/syntax.scrbl `module`);
;; an internal body discards them, so each expression item e becomes
;; (call-with-values (lambda () e) local-print%), and half of the programs
;; also wrap it in `call-with-continuation-prompt`.  Definitions keep their
;; order; generated names are unique and only refer to earlier definitions
;; (valid_program), so letrec* semantics equal the module's.  Expected:
;; reference/syntax.scrbl, internal definitions are `letrec-syntaxes+values`
;; with the same left-to-right evaluation; output must be identical.
(define (local-module form src [part? #f])
  (define lang (caddr form))
  (define-values (pre items) (split-prelude (cdddr form)))
  (define rng (macro-rng (string-append (if part? "localpart" "local") src)))
  (define k (if part? (rng (add1 (length items))) 0))
  (define-values (keep moved) (split-at items k))
  (define prompt? (zero? (rng 2)))
  (define (def? f) (and (pair? f) (memq (car f) '(define define-values))))
  (define body
    (for/list ([f moved])
      (cond [(def? f) f]
            [prompt? `(call-with-values
                       (lambda () (call-with-continuation-prompt (lambda () ,f)))
                       local-print%)]
            [else `(call-with-values (lambda () ,f) local-print%)])))
  (define wrapped
    (if (zero? (rng 2))
        `((define (main%) ,@body (void)) (main%))
        `((let () ,@body (void)))))
  `(module m ,lang ,@pre
     (define (local-print% . vs) (for-each (current-print) vs))
     ,@keep ,@wrapped))

;; Metamorphic top-level evaluation (variants top, topzo, topsplit; steering
;; round 13).  The module's body forms are evaluated one by one at the top
;; level of the fresh racket/base namespace instead: every form becomes its
;; own top-level linklet (expander compile/top.rkt, eval/top.rkt), module
;; definitions become namespace (top-level) variables that schemify knows
;; nothing about across forms (no constants, no known procedures, no
;; cross-form inlining; calls through variable references), `require`s and
;; the `show` macro are handled by the top-level expander.  A module body
;; prints its expression forms' values with `current-print` and wraps each in
;; a default-tag prompt (reference/syntax.scrbl `module`); `eval` at the top
;; level does neither, so each expression item e becomes
;;   (call-with-values (lambda () (call-with-continuation-prompt (lambda () e)))
;;                     top-print%)
;; Generated names are unique and only refer to earlier definitions
;; (valid_program), so no forward reference or redefinition exists and
;; the top level's documented differences (reference/eval-model.scrbl, the
;; top level is "hopeless" only for those) do not apply.  For a third of the
;; programs the opaque rewrite is applied first.  topzo: each form compiled,
;; written, read back and evaluated (per form), or for half of the programs
;; the prelude per form and then all generated items as one `(begin ...)`
;; compiled at once (a compiled top-level sequence, its definitions declared
;; but not yet run) and round-tripped.
;; topsplit: the provider module `a` of split-module (zo round trip) is
;; declared, then the client's body (its `(require 'a)` included) runs at
;; the top level: top-level linklets importing a module's known bindings.
(define (top-variant? v) (member v '("top" "topzo" "topsplit")))
(define (top-body-forms mform [src #f])
  ;; (module m lang . body) -> top-level forms
  (define (decl? f) (and (pair? f) (memq (car f) '(define define-values define-syntax-rule
                                                    define-syntax struct require provide))))
  (define (fun-def? f) (and (pair? f) (eq? (car f) 'define) (pair? (cdr f)) (pair? (cadr f))))
  (define fs
    (for/list ([f (cdddr mform)])
      (if (decl? f)
          f
          `(call-with-values
            (lambda () (call-with-continuation-prompt (lambda () ,f)))
            top-print%))))
  ;; for half of the programs (given src), function definitions are
  ;; evaluated a second time, unchanged, at a later position: the top level
  ;; allows redefinition, and a `define` of a lambda has no other effect, so
  ;; callers compiled before (or in the same compiled begin) must see an
  ;; equivalent procedure (no stale known-procedure/inlining assumptions)
  (define rng (and src (macro-rng (string-append "topredef" src))))
  (define fs*
    (if (and rng (zero? (rng 2)))
        (let* ([n (length fs)]
               [v (list->vector (map list fs))])
          (for ([f fs] [i (in-naturals)] #:when (and (fun-def? f) (zero? (rng 2))))
            (define j (+ i (rng (- n i))))
            (vector-set! v j (append (vector-ref v j) (list f))))
          (apply append (vector->list v)))
        fs))
  (cons '(define (top-print% . vs) (for-each (current-print) vs)) fs*))
(define (top-base form src)
  (if (zero? ((macro-rng (string-append "topopq" src)) 3))
      (opaque-module form src)
      form))
(define (run-top variant form src)
  (define rng (macro-rng (string-append "top" variant src)))
  (case variant
    [("top") (for ([f (top-body-forms (top-base form src) src)]) (eval f))]
    [("topzo")
     (define fs (top-body-forms (top-base form src) src))
     (if (zero? (rng 2))
         (for ([f fs]) (eval (zo-round-trip (compile f))))
         ;; `compile` of a top-level begin does not run the `show` macro's
         ;; definition, so the prelude (up to `show`) goes first, per form
         (let-values ([(pre items) (split-prelude fs)])
           (for ([f pre]) (eval (zo-round-trip (compile f))))
           (eval (zo-round-trip (compile `(begin ,@items))))))]
    [("topsplit")
     (define ms (split-module (top-base form src)))
     (eval (zo-round-trip (compile (car ms))))
     (for ([f (top-body-forms (cadr ms) src)])
       (if (zero? (rng 2)) (eval f) (eval (zo-round-trip (compile f)))))]))

;; Metamorphic port variants (steering round 12): every string/bytes port
;; of the program is replaced by a port of another kind with the same
;; content (definitions in `port-alt-forms`, kinds per call from a vector
;; chosen from the program text).  Expected: reference ports.scrbl /
;; custom-ports.scrbl / pipes.scrbl -- a port's content is the bytes it
;; delivers, blocking reads/peeks return the same bytes whatever the chunking,
;; file-position of a non-file input port is the number of bytes read, etc.
(define port-renames
  '((open-input-bytes . pa:open-input-bytes) (open-input-string . pa:open-input-string)
    (open-output-bytes . pa:open-output-bytes) (open-output-string . pa:open-output-string)
    (get-output-bytes . pa:get-output-bytes) (get-output-string . pa:get-output-string)))
(define (port-variant? v) (member v '("port" "portsplit")))
(define (port-module form src)
  (define rng (macro-rng (string-append "port" src)))
  (define-values (pre items) (split-prelude (cdddr form)))
  ;; output positions set: only seekable output kinds (bytes port, file)
  (define seek? (regexp-match? #px"\\(file-position [^ ()]+ " src))
  (define nk 12)
  (define pool (if (zero? (rng 3)) (for/list ([i 3]) (rng nk)) (range nk)))
  (define kinds (for/vector ([i 64]) (list-ref pool (rng (length pool)))))
  (define okinds (for/vector ([i 64]) (rng 4)))
  ;; triage: RKT_PORT_KIND / RKT_PORT_OKIND force one kind for every port
  (define (force v e) (let ([k (getenv e)]) (if k (make-vector 64 (string->number k)) v)))
  (set! kinds (force kinds "RKT_PORT_KIND"))
  (set! okinds (force okinds "RKT_PORT_OKIND"))
  (define (walk e)
    (cond [(symbol? e) (let ([r (assq e port-renames)]) (if r (cdr r) e))]
          [(and (pair? e) (eq? (car e) 'quote)) e]
          [(pair? e) (cons (walk (car e)) (walk (cdr e)))]
          [else e]))
  `(module m ,(caddr form) ,@(drop-right pre 1)
     (define pa:kinds ',kinds)
     (define pa:okinds ',okinds)
     (define pa:seek? ,seek?)
     (define pa:progress? ,(regexp-match? #rx"-evt\\)" src))
     ,@port-alt-forms
     ,(last pre)
     ,@(map walk items)))
(define port-alt-forms
  '(
;; Definitions injected by runner.rkt's `port-module` (variants `port`,
;; `portsplit`) at the end of the prelude.  Every `open-input-bytes`,
;; `open-input-string`, `open-output-bytes`, `open-output-string`,
;; `get-output-bytes`, `get-output-string` of the program is renamed to the
;; `pa:` version below, which builds a port of another kind with the same
;; content (kind per call from `pa:kinds`, a vector literal the runner adds
;; in front of these forms; `pa:okinds` for output ports, `pa:seek?` when the
;; program sets output positions, so only seekable output kinds are used).
;; Read as data by runner.rkt (one form after another).
(require (only-in racket/port input-port-append make-limited-input-port peeking-input-port
                  make-input-port/read-to-peek reencode-input-port port->bytes))
(define pa:n 0)
(define (pa:next v)
  (define k (vector-ref v (modulo pa:n (vector-length v))))
  (set! pa:n (add1 pa:n))
  k)
;; chunk sizes delivered by custom ports, cycling per port
(define (pa:csize i) (vector-ref '#(1 3 100000 2 1 7 4096 5) (modulo i 8)))
(define (pa:valid-utf-8? b) (and (bytes-utf-8-length b #f) #t))
(define pa:tmp-k 0)
(define (pa:tmp-path)
  (set! pa:tmp-k (add1 pa:tmp-k))
  (build-path (find-system-path 'temp-dir)
              (format "rktpa-~a-~a-~a" (current-inexact-milliseconds) (eq-hash-code (box 0)) pa:tmp-k)))
(define (pa:custom-in b peek? start)
  (define pos 0)
  (define n (bytes-length b))
  (define calls start)
  (define (next!) (set! calls (add1 calls)) (pa:csize calls))
  (make-input-port
   'string
   (lambda (dst)
     (if (>= pos n)
         eof
         (let ([m (min (bytes-length dst) (- n pos) (next!))])
           (bytes-copy! dst 0 b pos (+ pos m))
           (set! pos (+ pos m))
           m)))
   (and peek?
        (lambda (dst skip evt)
          (let ([s (+ pos skip)])
            (if (>= s n)
                eof
                (let ([m (min (bytes-length dst) (- n s) (next!))])
                  (bytes-copy! dst 0 b s (+ s m))
                  m)))))
   void))
(define (pa:read-to-peek b start)
  (define pos 0)
  (define n (bytes-length b))
  (define calls start)
  (make-input-port/read-to-peek
   'string
   (lambda (dst)
     (if (>= pos n)
         eof
         (begin
           (set! calls (add1 calls))
           (let ([m (min (bytes-length dst) (- n pos) (pa:csize calls))])
             (bytes-copy! dst 0 b pos (+ pos m))
             (set! pos (+ pos m))
             m))))
   #f
   void))
(define (pa:pieces b k)
  ;; split b into pieces at deterministic cut points (some empty)
  (define n (bytes-length b))
  (let loop ([i 0] [j k] [acc '()])
    (if (>= i n)
        (reverse (cons #"" acc))
        (let ([m (min (- n i) (modulo (* 5 j) 7))])
          (loop (+ i m) (add1 j) (cons (subbytes b i (+ i m)) acc))))))
(define (pa:open-input-bytes b [name 'string])
  ;; bad arguments (the shrinker makes them): the original's error
  (unless (bytes? b) (open-input-bytes b name))
  (define k (pa:next pa:kinds))
  (define b* (bytes->immutable-bytes (bytes-copy b)))
  (define p (pa:open-kind k b* name))
  ;; racket/port's *-evt procedures: "The in must support progress events"
  ;; (port-lib.scrbl); a custom port with a peek procedure but no progress
  ;; events, or input-port-append, does not
  (if (and pa:progress? (not (port-provides-progress-evts? p)))
      (open-input-bytes b* name)
      p))
(define (pa:open-kind k b* name)
  (case k
    [(0) (open-input-bytes b* name)]
    [(1) (pa:custom-in b* #f k)]
    [(2) (pa:custom-in b* #t k)]
    [(3) (pa:read-to-peek b* k)]
    [(4) (let-values ([(i o) (make-pipe #f 'string 'string)])
           (write-bytes b* o)
           (close-output-port o)
           i)]
    ;; (not a limited pipe: a blocking peek beyond the limit waits forever,
    ;; pipes.scrbl: capacity is extended only by bytes actually peeked)
    [(5) (let-values ([(i o) (make-pipe #f 'string 'string)])
           (thread (lambda ()
                     (for ([piece (in-list (pa:pieces b* pa:n))])
                       (write-bytes piece o)
                       (sleep 0))
                     (close-output-port o)))
           i)]
    [(6) (apply input-port-append #t (map open-input-bytes (pa:pieces b* k)))]
    [(7) (peeking-input-port (open-input-bytes b*) 'string)]
    [(8) (make-limited-input-port (open-input-bytes (bytes-append b* #"(tail \"x\n")) (bytes-length b*))]
    [(9) (if (pa:valid-utf-8? b*)
             (reencode-input-port (open-input-bytes b*) "UTF-8" #f #f 'string)
             (pa:custom-in b* #t k))]
    [(10) (let ([f (pa:tmp-path)])
            (call-with-output-file f (lambda (o) (write-bytes b* o)) #:exists 'truncate)
            (begin0 (open-input-file f) (delete-file f)))]
    [else (let-values ([(i o) (make-pipe #f 'string 'string)])
            ;; unlimited pipe filled by a thread, closed at the end
            (thread (lambda ()
                      (for ([piece (in-list (pa:pieces b* (add1 pa:n)))])
                        (write-bytes piece o))
                      (close-output-port o)))
            i)]))
(define (pa:open-input-string s [name 'string])
  (unless (string? s) (open-input-string s name))
  (pa:open-input-bytes (string->bytes/utf-8 s) name))
;; output ports: a struct-free registry from port to its content getter
(define pa:getters (make-weak-hasheq))
(define (pa:open-output-bytes [name 'string])
  (define k (if pa:seek? (vector-ref '#(0 3) (modulo (pa:next pa:okinds) 2)) (pa:next pa:okinds)))
  (case k
    [(0) (open-output-bytes name)]
    [(1) (define inner (open-output-bytes))
         (define calls k)
         (define o
           (make-output-port
            'string always-evt
            (lambda (bs start end non-block? breakable?)
              (if (= start end)
                  0
                  (begin
                    (set! calls (add1 calls))
                    (let ([m (min (- end start) (pa:csize calls))])
                      (write-bytes bs inner start (+ start m))
                      m))))
            void))
         (hash-set! pa:getters o (lambda () (flush-output o) (get-output-bytes inner)))
         o]
    [(2) (define-values (i o) (make-pipe #f 'string 'string))
         (define acc (open-output-bytes))
         (define buf (make-bytes 37))
         (hash-set! pa:getters o
                    (lambda ()
                      (let loop ()
                        (define m (read-bytes-avail!* buf i))
                        (when (and (exact-integer? m) (positive? m))
                          (write-bytes buf acc 0 m)
                          (loop)))
                      (get-output-bytes acc)))
         o]
    [else (define f (pa:tmp-path))
          (define o (open-output-file f #:exists 'truncate))
          (define i (open-input-file f))
          (delete-file f)
          (hash-set! pa:getters o
                     (lambda ()
                       (flush-output o)
                       (file-position i 0)
                       (let ([r (read-bytes 100000000 i)]) (if (eof-object? r) #"" r))))
          o]))
(define (pa:open-output-string [name 'string]) (pa:open-output-bytes name))
(define (pa:get-output-bytes o . more)
  (define g (hash-ref pa:getters o #f))
  (cond [(not g) (apply get-output-bytes o more)]
        [(null? more) (g)]
        [else (let* ([bs (g)]
                     [start (if (>= (length more) 2) (cadr more) 0)]
                     [end (if (>= (length more) 3) (caddr more) (bytes-length bs))])
                (subbytes bs start end))]))
(define (pa:get-output-string o . more)
  (if (hash-ref pa:getters o #f)
      (bytes->string/utf-8 (apply pa:get-output-bytes o more) #\uFFFD)
      (apply get-output-string o more)))
))

(define (variant-source variant src)
  (if (equal? variant "unsafe")
      (string-replace src "(module m racket/base\n" "(module m racket/base\n(#%declare #:unsafe)\n" #:all? #f)
      src))

;; Sets Chez-level knobs (per OS thread, so they apply to the case thread
;; too); returns a thunk that restores them.
(define (set-chez-knobs! variant [src ""])
  (define cp0 (chez-run-cp0))
  (define tr (chez-type-recovery))
  (define sc (chez-score))
  (define ef (chez-effort))
  (define un (chez-unroll))
  (define saved (for/list ([k (in-list chez-knobs2)]) (k)))
  (define (noclos!) (chez-optclos #f) (chez-liftclos #f))
  (define (dbg!) (chez-debug-level 3) (chez-inspinfo #t))
  (define (knob2!) (chez-check-prelex #t))
  (case variant
    [("nocp0") (chez-run-cp0 (lambda (cp0 x) x))]
    [("notr") (chez-type-recovery #f)]
    [("cp0big") (chez-score 120) (chez-effort 5000) (chez-unroll 2)]
    [("common") (knob2!) (chez-common (add1 (modulo (string-length src) 9)))]
    [("noclos") (knob2!) (noclos!)]
    [("notrap") (knob2!) (chez-trap #f)]
    [("dbg") (knob2!) (dbg!)]
    [("noinl") (knob2!) (chez-noinline #t)]
    [("chezmix" "chezmixzo")
     (knob2!)
     (define rng (macro-rng (string-append "chezmix" src)))
     ;; at least one knob: draw until something was set
     (let loop ([n 0])
       (define any? #f)
       (define-syntax-rule (maybe k e ...) (when (< (rng 100) k) (set! any? #t) e ...))
       (maybe 40 (chez-common (add1 (rng 9))))
       (maybe 35 (noclos!))
       (maybe 25 (chez-trap #f))
       (maybe 30 (dbg!))
       (maybe 20 (chez-noinline #t))
       (maybe 20 (chez-type-recovery #f))
       (maybe 20 (chez-score 120) (chez-effort 5000) (chez-unroll 2))
       (unless (or any? (> n 5)) (loop (add1 n))))]
    [else (void)])
  (lambda ()
    (for ([k (in-list chez-knobs2)] [v (in-list saved)]) (k v))
    (chez-run-cp0 cp0) (chez-type-recovery tr) (chez-score sc) (chez-effort ef) (chez-unroll un)))

(define (chezmix-variant? v) (member v '("chezmix" "chezmixzo")))
;; the rewrite chezmix applies (deterministic in the text)
(define (chezmix-forms form src)
  (define rng (macro-rng (string-append "chezmixrw" src)))
  (case (rng 5)
    [(0) (list form)]
    [(1) (list (opaque-module form src))]
    [(2) (list (local-module form src #t))]
    [(3) (split-module form)]
    [else (split-module (opaque-module form src #t))]))

(define TIMEOUT (let ([s (getenv "RKT_CASE_TIMEOUT")]) (if s (string->number s) 10)))
(define MAX-OUT 20000)

(define orig-ns (current-namespace))
(define real-out (current-output-port))

(define (first-line s)
  (let ([m (regexp-match #rx"^[^\n]*" s)]) (car m)))

(define (cap s) (if (> (string-length s) MAX-OUT) (substring s 0 MAX-OUT) s))

(define (fresh-ns)
  (define ns (make-base-namespace))
  (for ([m '(racket/fixnum racket/flonum racket/unsafe/ops racket/list ffi/unsafe/vm racket/future racket/port racket/fasl)])
    (namespace-attach-module orig-ns m ns))
  ns)

;; Returns a list of fields.
(define (run-program src0 [variant "none"])
  (unless (member variant VARIANTS) (error 'runner "unknown variant ~a" variant))
  (define src (variant-source variant src0))
  (define out (open-output-string))
  (define cust (make-custodian))
  (custodian-limit-memory cust (* 2048 1024 1024) cust)
  (define result #f)
  (define restore! (set-chez-knobs! variant src0))
  (define-values (gc-restore! check-heap?)
    (if (gc-variant? variant) (set-gc-knobs! src) (values void #f)))
  (define pre-fail (and (preempt-variant? variant) (box #f)))
  (define th
    (parameterize ([current-custodian cust]
                   [compile-context-preservation-enabled (equal? variant "ctx")]
                   [compile-enforce-module-constants (not (equal? variant "noconst"))])
      (thread
       (lambda ()
         (when pre-fail (start-preempt-helper! pre-fail))
         (set! result
               (parameterize ([current-namespace (fresh-ns)]
                              [current-output-port out]
                              [current-error-port out]
                              [read-accept-reader #f]
                              [read-accept-lang #f])
                 (with-handlers ([exn? (lambda (e)
                                         (list "exn" (get-output-string out)
                                               (symbol->string (vector-ref (struct->vector e) 0))
                                               ;; MASK: fixnum-overflow message wording differs by
                                               ;; mode ("with arguments" vs "computing '(fx* ..)"),
                                               ;; also in 9.3; not specified.  Kind is still compared.
                                               (if (exn:fail:contract:non-fixnum-result? e)
                                                   "<masked nonfx message>"
                                                   (first-line (exn-message e)))))]
                                 [(lambda (v) #t)
                                  (lambda (v) (list "raise" (get-output-string out)
                                                    (format "~s" v)))])
                   (define form (read (open-input-string src)))
                   (case variant
                     [("zo")
                      ;; serializable compile, written and read back as raco make does
                      (eval (zo-round-trip (compile form)))]
                     [("machind")
                      ;; machine-independent compile, round trip, recompile
                      (eval (compiled-expression-recompile
                             (zo-round-trip
                              (parameterize ([current-compile-target-machine #f])
                                (compile form)))))]
                     [("split")
                      (for ([f (split-module form)]) (eval f))]
                     [("splitzo")
                      (for ([f (split-module form)]) (eval (zo-round-trip (compile f))))]
                     [("splitmi")
                      (for ([f (split-module form)])
                        (eval (compiled-expression-recompile
                               (zo-round-trip
                                (parameterize ([current-compile-target-machine #f])
                                  (compile f))))))]
                     [("macro") (eval (macro-module form src))]
                     [("macrozo") (eval (zo-round-trip (compile (macro-module form src))))]
                     [("macrosplit")
                      (for ([f (macro-split form src)]) (eval (zo-round-trip (compile f))))]
                     [("macrosub")
                      (eval (zo-round-trip (compile (macro-sub form src))))]
                     [("opaque") (eval (opaque-module form src))]
                     [("opaquesplit")
                      (for ([f (split-module (opaque-module form src))]) (eval f))]
                     [("ctlnoise") (eval (opaque-module form src #t))]
                     [("ctlsplit")
                      (for ([f (split-module (opaque-module form src #t))])
                        (eval (zo-round-trip (compile f))))]
                     [("gc") (eval (gc-module form src))]
                     [("gczo") (eval (zo-round-trip (compile (gc-module form src))))]
                     [("gcsplit")
                      (for ([f (split-module (gc-module form src))])
                        (eval (zo-round-trip (compile f))))]
                     [("local") (eval (local-module form src))]
                     [("localpart") (eval (local-module form src #t))]
                     [("localzo") (eval (zo-round-trip (compile (local-module form src #t))))]
                     [("preempt") (eval (preempt-module form src))]
                     [("preemptctl") (eval (preempt-module form src #t))]
                     [("preemptsplit")
                      (for ([f (split-module (preempt-module form src))])
                        (eval (zo-round-trip (compile f))))]
                     [("common" "noclos" "notrap" "dbg" "noinl")
                      ;; half of the programs through compile-to-port (the
                      ;; file-compile path, where Chez runs its prelex check)
                      (if (zero? ((macro-rng (string-append "knobzo" src)) 2))
                          (eval (zo-round-trip (compile form)))
                          (eval form))]
                     [("future") (eval (future-module form src))]
                     [("futurezo") (eval (zo-round-trip (compile (future-module form src))))]
                     [("futuresplit")
                      (for ([f (split-module (future-module form src))])
                        (eval (zo-round-trip (compile f))))]
                     [("gcfuture") (eval (future-module form src #t))]
                     [("port") (eval (port-module form src))]
                     [("portsplit")
                      (for ([f (split-module (port-module form src))])
                        (eval (zo-round-trip (compile f))))]
                     [("chezmix") (for ([f (chezmix-forms form src)]) (eval f))]
                     [("chezmixzo")
                      (for ([f (chezmix-forms form src)]) (eval (zo-round-trip (compile f))))]
                     [("top" "topzo" "topsplit") (run-top variant form src)]
                     [("rtrip") (eval (rt-module form src))]
                     [("rtripzo") (eval (zo-round-trip (compile (rt-module form src))))]
                     [else (eval form)])
                   (unless (top-variant? variant) (dynamic-require ''m #f))
                   (when (and (equal? variant "port") (getenv "RKT_PORT_DEBUG"))
                     (eprintf "ports made: ~a\n" (eval 'pa:n (module->namespace ''m))))
                   (when (equal? variant "macrosub")
                     (dynamic-require '(submod 'm sub) #f))
                   (list "ok" (get-output-string out)))))))))
  (define done (sync/timeout TIMEOUT th))
  (define cust-down? (custodian-shut-down? cust))
  (custodian-shutdown-all cust)
  (restore!)
  (gc-restore!)
  (define heap-errs (if check-heap? (heap-check-errors) 0))
  (define place-ok (if (gc-variant? variant) (gc-place-ok?) #t))
  (when (and pre-fail (getenv "RKT_PRE_DEBUG"))
    (eprintf "helper iterations: ~a\n" pre-swaps)
    (set! pre-swaps 0))
  (cond
    [(and pre-fail (unbox pre-fail))
     (list "exn" (get-output-string out) "preempt-helper"
           (format "internal error: ~a" (unbox pre-fail)))]
    [(not place-ok)
     (list "exn" (get-output-string out) "heap-check"
           "internal error: the background place's heap is damaged after the case")]
    [(positive? heap-errs)
     (list "exn" (get-output-string out) "heap-check"
           (format "internal error: ~a Chez heap check errors after the case" heap-errs))]
    [(not done) (list "timeout" (get-output-string out))]
    ;; future variants: the case thread ended without a result although its
    ;; custodian was not shut down (no memory-limit kill): something (an
    ;; abort escaping its prompt) terminated the thread itself
    [(and (not result) (future-variant? variant) (not cust-down?))
     (list "exn" (get-output-string out) "thread-died"
           "internal error: the case thread ended without a result")]
    [(not result) (list "oom")]
    [else result]))

(define (emit fields)
  (define strs
    (for/list ([f fields] [i (in-naturals)])
      (if (zero? i) f (format "~s" (cap f)))))
  (write-string (string-join* strs "\t") real-out)
  (newline real-out)
  (flush-output real-out))

(define (string-join* l sep)
  (apply string-append (add-between l sep)))

(define args (current-command-line-arguments))
(cond
  [(and (= (vector-length args) 1) (equal? (vector-ref args 0) "server"))
   (let loop ()
     (define line (read-line (current-input-port) 'linefeed))
     (unless (eof-object? line)
       (define parts (string-split line))
       (define n (string->number (car parts)))
       (define variant (if (pair? (cdr parts)) (cadr parts) "none"))
       (define bs (read-bytes n (current-input-port)))
       (emit (run-program (bytes->string/utf-8 bs #\?) variant))
       (loop)))]
  [(and (<= 2 (vector-length args) 3) (equal? (vector-ref args 0) "file"))
   (emit (run-program (call-with-input-file (vector-ref args 1) port->string)
                      (if (= (vector-length args) 3) (vector-ref args 2) "none")))]
  [(and (= (vector-length args) 2) (equal? (vector-ref args 0) "splitdump"))
   ;; prints the two modules of the split variants (for triage)
   (for ([f (split-module (read (open-input-string
                                 (call-with-input-file (vector-ref args 1) port->string))))])
     (write f real-out) (newline real-out))]
  [(and (= (vector-length args) 3) (equal? (vector-ref args 0) "macrodump"))
   ;; prints the rewritten module(s) of the macro variants (for triage)
   (let* ([src (call-with-input-file (vector-ref args 1) port->string)]
          [form (read (open-input-string src))])
     (for ([f (case (vector-ref args 2)
                [("macrosplit") (macro-split form src)]
                [("macrosub") (list (macro-sub form src))]
                [("opaque") (list (opaque-module form src))]
                [("opaquesplit") (split-module (opaque-module form src))]
                [("ctlnoise") (list (opaque-module form src #t))]
                [("ctlsplit") (split-module (opaque-module form src #t))]
                [("gc" "gczo") (list (gc-module form src))]
                [("gcsplit") (split-module (gc-module form src))]
                [("local") (list (local-module form src))]
                [("localpart" "localzo") (list (local-module form src #t))]
                [("preempt") (list (preempt-module form src))]
                [("preemptctl") (list (preempt-module form src #t))]
                [("preemptsplit") (split-module (preempt-module form src))]
                [("chezmix" "chezmixzo") (chezmix-forms form src)]
                [("future" "futurezo") (list (future-module form src))]
                [("futuresplit") (split-module (future-module form src))]
                [("gcfuture") (list (future-module form src #t))]
                [("port") (list (port-module form src))]
                [("portsplit") (split-module (port-module form src))]
                [("rtrip" "rtripzo") (list (rt-module form src))]
                [("top" "topzo") (top-body-forms (top-base form src) src)]
                [("topsplit") (let ([ms (split-module (top-base form src))])
                                (cons (car ms) (top-body-forms (cadr ms) src)))]
                [else (list (macro-module form src))])])
       (pretty-write f real-out)))]
  [else (error 'runner "usage: runner.rkt server | file <prog> [variant]")])
