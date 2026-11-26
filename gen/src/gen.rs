//! Typed generator of Racket module programs.
//!
//! Every expression is an `E`: a template with `$0..$9` holes, its children,
//! its type and a feature tag.  Programs are valid by construction (well
//! typed, bounded loops, only earlier definitions referenced); runtime errors
//! (division by zero, fixnum overflow, fl->fx of NaN) can happen and are
//! observable, identically, in every compilation mode.

use ephyra::Source;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ty {
    Int,
    Fl,
    Bool,
    /// Dynamically typed: fixnums, bignums, flonums, booleans, pairs/lists,
    /// null, strings, chars, symbols, vectors, boxes, void.
    Val,
    Stmt,
}

#[derive(Clone, Debug)]
pub struct E {
    pub ty: Ty,
    pub tpl: String,
    pub kids: Vec<E>,
    pub tag: &'static str,
    /// Names this node binds for its children (unique program-wide).
    pub binds: Vec<String>,
    /// Names the template itself references (calls, set! targets, variables).
    pub uses: Vec<String>,
    /// Names a top-level item defines for later items.
    pub defines: Vec<String>,
}

impl E {
    pub fn atom(ty: Ty, s: &str) -> E {
        E { ty, tpl: s.to_string(), kids: vec![], tag: "", binds: vec![], uses: vec![], defines: vec![] }
    }
    pub fn var(ty: Ty, s: &str) -> E {
        let mut e = E::atom(ty, s);
        e.uses.push(s.to_string());
        e
    }
    pub fn node(ty: Ty, tag: &'static str, tpl: &str, kids: Vec<E>) -> E {
        E { ty, tpl: tpl.to_string(), kids, tag, binds: vec![], uses: vec![], defines: vec![] }
    }
    pub fn binding(mut self, names: &[&String]) -> E {
        self.binds.extend(names.iter().map(|s| s.to_string()));
        self
    }
    pub fn using(mut self, names: &[&String]) -> E {
        self.uses.extend(names.iter().map(|s| s.to_string()));
        self
    }
    pub fn defining(mut self, names: &[&String]) -> E {
        self.defines.extend(names.iter().map(|s| s.to_string()));
        self
    }
    /// Free names: used here or below, not bound here or below.
    pub fn free(&self, out: &mut Vec<String>) {
        let mut mine: Vec<String> = self.uses.clone();
        for k in &self.kids {
            k.free(&mut mine);
        }
        mine.retain(|n| !self.binds.contains(n));
        out.extend(mine);
    }
    pub fn render(&self, out: &mut String) {
        let b = self.tpl.as_bytes();
        let mut i = 0;
        while i < b.len() {
            if b[i] == b'$' && i + 1 < b.len() && b[i + 1].is_ascii_digit() {
                let k = (b[i + 1] - b'0') as usize;
                self.kids[k].render(out);
                i += 2;
            } else {
                let start = i;
                while i < b.len() && !(b[i] == b'$' && i + 1 < b.len() && b[i + 1].is_ascii_digit()) {
                    i += 1;
                }
                out.push_str(&self.tpl[start..i]);
            }
        }
    }
    #[allow(dead_code)]
    pub fn size(&self) -> usize {
        1 + self.kids.iter().map(|k| k.size()).sum::<usize>()
    }
    pub fn tags(&self, out: &mut Vec<&'static str>) {
        if !self.tag.is_empty() {
            out.push(self.tag);
        }
        for k in &self.kids {
            k.tags(out);
        }
    }
}

/// Every decision comes from ephyra's `Source`, so ephyra controls seeds,
/// sizes and replay.
pub struct Rng<'a>(pub &'a mut Source);
impl<'a> Rng<'a> {
    pub fn below(&mut self, n: usize) -> usize {
        self.0.index(n)
    }
    pub fn chance(&mut self, p: f64) -> bool {
        self.0.bool_with(p)
    }
    pub fn pick<'b, T>(&mut self, xs: &'b [T]) -> &'b T {
        self.0.pick(xs)
    }
}

const INT_POOL: &[&str] = &[
    "0", "1", "-1", "2", "3", "7", "-8", "100", "255", "-5", "63", "64", "1073741824",
    "-1000003", "1152921504606846975", "-1152921504606846976", "4611686018427387904",
    "576460752303423488", "-4294967296",
];
const FL_POOL: &[&str] = &[
    "0.0", "-0.0", "1.0", "-1.0", "0.5", "-0.5", "1.5", "2.5", "-2.5", "3.0", "0.1", "1e308",
    "-1e308", "+inf.0", "-inf.0", "+nan.0", "4.9406564584124654e-324", "2.2250738585072014e-308",
    "9007199254740992.0", "9007199254740991.0", "1e-10", "123456.789", "-7.25", "4503599627370496.5",
];
const BOOL_POOL: &[&str] = &["#t", "#f"];
// Literals of the dynamic kind. Comparisons on Val use only equal? (eq?/eqv?
// on numbers, chars, strings and quoted literals are unspecified).
const VAL_POOL: &[&str] = &[
    "'()", "'a", "'b", "\"ab\"", "\"\"", "#\\a", "#\\Z", "#\\0", "'(1 2)", "'(a . 2.5)", "(void)",
    "#t", "#f", "0", "-1", "1152921504606846975", "1152921504606846976", "0.0", "-0.0", "+nan.0",
    "2.0", "'#(1 b)", "'(())",
];

#[derive(Clone)]
struct Fun {
    name: String,
    params: Vec<Ty>,
    ret: Ty,
}

pub struct Gen<'a> {
    pub rng: Rng<'a>,
    scope: Vec<(String, Ty, bool)>, // name, type, may set!
    funs: Vec<Fun>,
    next_id: usize,
    loop_depth: usize,
}

impl<'a> Gen<'a> {
    pub fn new(src: &'a mut Source) -> Gen<'a> {
        Gen { rng: Rng(src), scope: vec![], funs: vec![], next_id: 0, loop_depth: 0 }
    }
    fn fresh(&mut self, p: &str) -> String {
        self.next_id += 1;
        format!("{p}{}", self.next_id)
    }
    fn var_of(&mut self, ty: Ty) -> Option<E> {
        let c: Vec<&String> = self.scope.iter().filter(|v| v.1 == ty).map(|v| &v.0).collect();
        if c.is_empty() {
            None
        } else {
            let n = c[self.rng.below(c.len())].clone();
            Some(E::var(ty, &n))
        }
    }
    fn settable(&mut self, ty: Ty) -> Option<String> {
        let c: Vec<&String> = self.scope.iter().filter(|v| v.1 == ty && v.2).map(|v| &v.0).collect();
        if c.is_empty() {
            None
        } else {
            Some(c[self.rng.below(c.len())].clone())
        }
    }
    pub fn leaf(&mut self, ty: Ty) -> E {
        if self.rng.chance(0.6) {
            if let Some(v) = self.var_of(ty) {
                return v;
            }
        }
        let s = match ty {
            Ty::Int => *self.rng.pick(INT_POOL),
            Ty::Fl => *self.rng.pick(FL_POOL),
            Ty::Bool => *self.rng.pick(BOOL_POOL),
            Ty::Val => *self.rng.pick(VAL_POOL),
            Ty::Stmt => "(void)",
        };
        E::atom(ty, s)
    }
    pub fn expr(&mut self, ty: Ty, d: usize) -> E {
        if d == 0 || self.rng.chance(0.15) {
            return self.leaf(ty);
        }
        // Shared control forms (any type) a third of the time.
        if self.rng.chance(0.33) {
            return self.control(ty, d);
        }
        // Library primitives (round 7), mostly through the dynamic kind.
        if ty != Ty::Stmt && ty != Ty::Val && self.rng.chance(0.05) {
            return self.lib_typed(ty, d);
        }
        match ty {
            Ty::Int => self.int_op(d),
            Ty::Fl => self.fl_op(d),
            Ty::Bool => self.bool_op(d),
            Ty::Val => self.val_op(d),
            Ty::Stmt => self.leaf(ty),
        }
    }
    fn bin(&mut self, ty: Ty, tag: &'static str, op: &str, at: Ty, d: usize) -> E {
        let a = self.expr(at, d - 1);
        let b = self.expr(at, d - 1);
        E::node(ty, tag, &format!("({op} $0 $1)"), vec![a, b])
    }
    fn un(&mut self, ty: Ty, tag: &'static str, op: &str, at: Ty, d: usize) -> E {
        let a = self.expr(at, d - 1);
        E::node(ty, tag, &format!("({op} $0)"), vec![a])
    }
    fn small_lit(&mut self, lo: i64, hi: i64) -> E {
        let v = lo + self.rng.below((hi - lo + 1) as usize) as i64;
        E::atom(Ty::Int, &v.to_string())
    }

    fn int_op(&mut self, d: usize) -> E {
        let r = self.rng.below(100);
        match r {
            0..=17 => {
                let op = *self.rng.pick(&[
                    "+", "-", "*", "quotient", "remainder", "modulo", "max", "min", "gcd",
                    "bitwise-and", "bitwise-ior", "bitwise-xor", "+", "-",
                ]);
                self.bin(Ty::Int, "generic-arith", op, Ty::Int, d)
            }
            18..=21 => {
                let op = *self.rng.pick(&["+", "*", "-", "max", "bitwise-and"]);
                let k = vec![self.expr(Ty::Int, d - 1), self.expr(Ty::Int, d - 1), self.expr(Ty::Int, d - 1)];
                E::node(Ty::Int, "generic-arith", &format!("({op} $0 $1 $2)"), k)
            }
            22..=25 => {
                let op = *self.rng.pick(&["-", "abs", "add1", "sub1", "bitwise-not", "integer-length"]);
                self.un(Ty::Int, "generic-arith", op, Ty::Int, d)
            }
            26..=27 => {
                let a = self.expr(Ty::Int, d - 1);
                let k = self.small_lit(-70, 70);
                E::node(Ty::Int, "shift", "(arithmetic-shift $0 $1)", vec![a, k])
            }
            28..=43 => {
                let op = *self.rng.pick(&[
                    "fx+", "fx-", "fx*", "fxquotient", "fxremainder", "fxmodulo", "fxand", "fxior",
                    "fxxor", "fxmin", "fxmax", "fx+/wraparound", "fx-/wraparound", "fx*/wraparound",
                    "fx+", "fx-", "fxmin", "fxmax",
                ]);
                self.bin(Ty::Int, "fixnum", op, Ty::Int, d)
            }
            44..=46 => {
                let op = *self.rng.pick(&["fxnot", "fxabs", "fxpopcount", "fxpopcount32", "fx-"]);
                self.un(Ty::Int, "fixnum", op, Ty::Int, d)
            }
            47..=49 => {
                let op = *self.rng.pick(&["fxlshift", "fxrshift", "fxlshift/wraparound", "fxrshift/logical"]);
                let a = self.expr(Ty::Int, d - 1);
                let k = self.small_lit(0, 64);
                E::node(Ty::Int, "fixnum-shift", &format!("({op} $0 $1)"), vec![a, k])
            }
            50..=55 => {
                let f = self.expr(Ty::Fl, d - 1);
                match self.rng.below(5) {
                    0 => E::node(Ty::Int, "fl->int", "(fl->fx $0)", vec![f]),
                    1 => E::node(Ty::Int, "fl->int", "(fl->exact-integer (flfloor $0))", vec![f]),
                    2 => E::node(Ty::Int, "fl->int", "(inexact->exact (flround $0))", vec![f]),
                    3 => {
                        let s = self.rng.below(60);
                        let e = s + 1 + self.rng.below(64 - s);
                        // NaN bit patterns are not part of Racket's contract: "The datum
                        // -nan.0 refers to the same constant as +nan.0" (reference,
                        // numbers.scrbl:74) and all NaNs are eqv?. Compiled `max`/`min`
                        // become the branchless flmax/flmin (Chez 7c76ed9456), whose NaN
                        // result is all-ones by design, while the interpreter's generic
                        // max returns the canonical +nan.0; flbit-field would expose that
                        // difference. Canonicalise NaN only right before flbit-field.
                        E::node(Ty::Int, "flbit-field", &format!("(flbit-field (let ([fbx $0]) (if (= fbx fbx) fbx +nan.0)) {s} {e})"), vec![f])
                    }
                    _ => E::node(Ty::Int, "fl->int", "(exact-truncate* $0)", vec![f]),
                }
            }
            56..=59 => {
                // struct allocation and access
                let a = self.expr(Ty::Int, d - 1);
                let b = self.expr(Ty::Int, d - 1);
                if self.rng.chance(0.5) {
                    E::node(Ty::Int, "struct", "(pt-a (pt $0 $1))", vec![a, b])
                } else {
                    let c = self.expr(Ty::Int, d - 1);
                    let p = self.fresh("p");
                    E::node(
                        Ty::Int,
                        "struct-mutate",
                        &format!("(let ([{p} (pt $0 $1)]) (set-pt-b! {p} $2) (+ (pt-a {p}) (pt-b {p})))"),
                        vec![a, b, c],
                    )
                }
            }
            60..=63 => {
                let a = self.expr(Ty::Int, d - 1);
                let b = self.expr(Ty::Int, d - 1);
                let i = self.expr(Ty::Int, d - 1);
                match self.rng.below(3) {
                    0 => E::node(Ty::Int, "vector", "(vector-ref (vector $0 $1) (modulo $2 2))", vec![a, b, i]),
                    1 => {
                        let v = self.fresh("vec");
                        E::node(
                            Ty::Int,
                            "vector-mutate",
                            &format!("(let ([{v} (make-vector 3 $0)]) (vector-set! {v} (modulo $2 3) $1) (+ (vector-ref {v} 0) (vector-ref {v} 2)))"),
                            vec![a, b, i],
                        )
                    }
                    _ => E::node(Ty::Int, "list", "(apply + (list $0 $1 $2))", vec![a, b, i]),
                }
            }
            64..=65 => {
                let a = self.expr(Ty::Int, d - 1);
                E::node(Ty::Int, "string", "(string-length (number->string $0))", vec![a])
            }
            66..=67 => {
                let a = self.expr(Ty::Int, d - 1);
                let b = self.expr(Ty::Int, d - 1);
                let c = self.expr(Ty::Int, d - 1);
                E::node(Ty::Int, "hash", "(hash-ref (hash 0 $0 1 $1) (modulo $2 3) -7)", vec![a, b, c])
            }
            68..=71 => {
                // parameterize + continuation marks
                let a = self.expr(Ty::Int, d - 1);
                let b = self.expr(Ty::Int, d - 1);
                E::node(Ty::Int, "parameterize", "(parameterize ([prm $0]) (+ (prm) $1))", vec![a, b])
            }
            72..=75 => {
                let a = self.expr(Ty::Int, d - 1);
                let b = self.expr(Ty::Int, d - 1);
                if self.rng.chance(0.5) {
                    E::node(
                        Ty::Int,
                        "wcm",
                        "(with-continuation-mark 'key $0 (+ $1 (or (continuation-mark-set-first #f 'key) 0)))",
                        vec![a, b],
                    )
                } else {
                    E::node(
                        Ty::Int,
                        "wcm",
                        "(with-continuation-mark 'key $0 (with-continuation-mark 'key $1 (apply + (continuation-mark-set->list (current-continuation-marks) 'key))))",
                        vec![a, b],
                    )
                }
            }
            76..=79 => {
                let n = self.small_lit(0, 6);
                let a = self.expr(Ty::Int, d - 1);
                let i = self.fresh("i");
                let acc = self.fresh("acc");
                self.scope.push((i.clone(), Ty::Int, false));
                self.scope.push((acc.clone(), Ty::Int, false));
                self.loop_depth += 1;
                let body = self.expr(Ty::Int, d - 1);
                self.loop_depth -= 1;
                self.scope.pop();
                self.scope.pop();
                if self.rng.chance(0.5) {
                    E::node(
                        Ty::Int,
                        "for-fold",
                        &format!("(for/fold ([{acc} $1]) ([{i} (in-range $0)]) $2)"),
                        vec![n, a, body],
                    )
                    .binding(&[&i, &acc])
                } else {
                    E::node(Ty::Int, "for-sum", &format!("(for/sum ([{i} (in-range $0)]) (let ([{acc} $1]) $2))"), vec![n, a, body]).binding(&[&i, &acc])
                }
            }
            80..=85 => self.val_to_int(d),
            _ => self.call_or_leaf(Ty::Int, d),
        }
    }

    fn fl_op(&mut self, d: usize) -> E {
        let r = self.rng.below(100);
        match r {
            0..=24 => {
                let op = *self.rng.pick(&["fl+", "fl-", "fl*", "fl/", "flmin", "flmax", "flexpt", "flhypot", "flmin", "flmax"]);
                if (op == "flmin" || op == "flmax" || op == "fl+" || op == "fl*") && self.rng.chance(0.25) {
                    let k = vec![self.expr(Ty::Fl, d - 1), self.expr(Ty::Fl, d - 1), self.expr(Ty::Fl, d - 1)];
                    E::node(Ty::Fl, "flonum", &format!("({op} $0 $1 $2)"), k)
                } else {
                    let tag = if op == "flmin" || op == "flmax" { "flmin-max" } else { "flonum" };
                    self.bin(Ty::Fl, tag, op, Ty::Fl, d)
                }
            }
            25..=39 => {
                let op = *self.rng.pick(&[
                    "flround", "flfloor", "flceiling", "fltruncate", "flabs", "flsqrt", "flsingle",
                    "flround", "flfloor", "flceiling", "fltruncate", "flsin", "flexp", "fllog", "flatan", "fl-",
                ]);
                let tag = match op {
                    "flround" | "flfloor" | "flceiling" | "fltruncate" => "flround",
                    _ => "flonum",
                };
                self.un(Ty::Fl, tag, op, Ty::Fl, d)
            }
            40..=49 => {
                let op = *self.rng.pick(&["+", "-", "*", "/", "min", "max"]);
                self.bin(Ty::Fl, "generic-fl", op, Ty::Fl, d)
            }
            50..=55 => {
                let op = *self.rng.pick(&["abs", "round", "floor", "ceiling", "truncate", "exact->inexact"]);
                self.un(Ty::Fl, "generic-fl", op, Ty::Fl, d)
            }
            56..=63 => {
                let op = *self.rng.pick(&["fx->fl", "->fl", "exact->inexact", "real->double-flonum"]);
                self.un(Ty::Fl, "int->fl", op, Ty::Int, d)
            }
            64..=67 => {
                let a = self.expr(Ty::Fl, d - 1);
                let b = self.expr(Ty::Fl, d - 1);
                let i = self.expr(Ty::Int, d - 1);
                E::node(Ty::Fl, "flvector", "(flvector-ref (flvector $0 $1) (modulo $2 2))", vec![a, b, i])
            }
            68..=69 => {
                let a = self.expr(Ty::Fl, d - 1);
                let b = self.expr(Ty::Fl, d - 1);
                E::node(Ty::Fl, "flonum", "(* $0 (fl+ $1 0.0))", vec![a, b])
            }
            70..=77 => {
                let n = self.small_lit(0, 6);
                let a = self.expr(Ty::Fl, d - 1);
                let i = self.fresh("i");
                let acc = self.fresh("acc");
                self.scope.push((i.clone(), Ty::Int, false));
                self.scope.push((acc.clone(), Ty::Fl, false));
                self.loop_depth += 1;
                let body = self.expr(Ty::Fl, d - 1);
                self.loop_depth -= 1;
                self.scope.pop();
                self.scope.pop();
                let lp = self.fresh("loop");
                E::node(
                    Ty::Fl,
                    "fl-loop",
                    &format!("(let {lp} ([{i} 0] [{acc} $1]) (if (fx< {i} $0) ({lp} (fx+ {i} 1) $2) {acc}))"),
                    vec![n, a, body],
                )
                .binding(&[&i, &acc])
            }
            78..=80 => {
                let v = self.expr(Ty::Val, d - 1);
                let a = self.expr(Ty::Fl, d - 1);
                let t = self.fresh("t");
                match self.rng.below(3) {
                    0 => E::node(Ty::Fl, "type-guard", &format!("(let ([{t} $0]) (if (flonum? {t}) {t} $1))"), vec![v, a]),
                    1 => {
                        let u = self.fresh("u");
                        E::node(Ty::Fl, "type-guard", &format!("(let ([{t} $0] [{u} $1]) (if (real? {t}) (fl+ (real->double-flonum {t}) {u}) {u}))"), vec![v, a])
                    }
                    _ => {
                        let u = self.fresh("u");
                        E::node(Ty::Fl, "type-guard", &format!("(let* ([{t} $0] [{u} $1]) (cond [(flonum? {t}) (fl* {t} {u})] [(fixnum? {t}) (fx->fl {t})] [(pair? {t}) 1.5] [else {u}]))"), vec![v, a])
                    }
                }
            }
            _ => self.call_or_leaf(Ty::Fl, d),
        }
    }

    fn bool_op(&mut self, d: usize) -> E {
        let r = self.rng.below(100);
        match r {
            0..=24 => {
                let op = *self.rng.pick(&["fx<", "fx>", "fx=", "fx<=", "fx>="]);
                if self.rng.chance(0.15) {
                    let k = vec![self.expr(Ty::Int, d - 1), self.expr(Ty::Int, d - 1), self.expr(Ty::Int, d - 1)];
                    E::node(Ty::Bool, "fx-compare", &format!("({op} $0 $1 $2)"), k)
                } else {
                    self.bin(Ty::Bool, "fx-compare", op, Ty::Int, d)
                }
            }
            25..=39 => {
                let op = *self.rng.pick(&["<", ">", "=", "<=", ">=", "eqv?", "equal?"]);
                self.bin(Ty::Bool, "compare", op, Ty::Int, d)
            }
            40..=54 => {
                let op = *self.rng.pick(&["fl<", "fl>", "fl=", "fl<=", "fl>=", "<", "=", "eqv?", "equal?"]);
                self.bin(Ty::Bool, "fl-compare", op, Ty::Fl, d)
            }
            55..=64 => {
                let op = *self.rng.pick(&["zero?", "even?", "odd?", "positive?", "negative?", "fixnum?", "exact-integer?"]);
                self.un(Ty::Bool, "predicate", op, Ty::Int, d)
            }
            65..=69 => {
                let op = *self.rng.pick(&["zero?", "positive?", "negative?", "flonum?", "integer?", "nan?*", "infinite?*"]);
                self.un(Ty::Bool, "fl-predicate", op, Ty::Fl, d)
            }
            70..=89 => {
                match self.rng.below(3) {
                    0 => self.un(Ty::Bool, "logic", "not", Ty::Bool, d),
                    1 => self.bin(Ty::Bool, "logic", "and", Ty::Bool, d),
                    _ => self.bin(Ty::Bool, "logic", "or", Ty::Bool, d),
                }
            }
            90..=95 => {
                let v = self.expr(Ty::Val, d - 1);
                if self.rng.chance(0.25) {
                    let w = self.expr(Ty::Val, d - 1);
                    E::node(Ty::Bool, "equal", "(equal? $0 $1)", vec![v, w])
                } else {
                    let op = *self.rng.pick(&[
                        "pair?", "null?", "list?", "string?", "char?", "symbol?", "fixnum?", "flonum?",
                        "boolean?", "number?", "exact-integer?", "real?", "integer?", "vector?", "box?",
                        "void?", "not", "procedure?", "exact-nonnegative-integer?", "byte?", "rational?",
                    ]);
                    E::node(Ty::Bool, "type-pred", &format!("({op} $0)"), vec![v])
                }
            }
            _ => self.call_or_leaf(Ty::Bool, d),
        }
    }

    fn call_or_leaf(&mut self, ty: Ty, d: usize) -> E {
        let c: Vec<Fun> = self.funs.iter().filter(|f| f.ret == ty).cloned().collect();
        if c.is_empty() {
            return self.leaf(ty);
        }
        let f = c[self.rng.below(c.len())].clone();
        let mut tpl = format!("({}", f.name);
        let mut kids = vec![];
        for (k, p) in f.params.iter().enumerate() {
            tpl.push_str(&format!(" ${k}"));
            kids.push(self.expr(*p, d - 1));
        }
        tpl.push(')');
        E::node(ty, "call", &tpl, kids).using(&[&f.name])
    }

    /// Control forms that work at any type.
    fn control(&mut self, ty: Ty, d: usize) -> E {
        let r = self.rng.below(100);
        match r {
            26..=29 => self.delim(ty, d),
            0..=25 => {
                // if: bias toward compare tests and trivial arms (cmov shapes)
                let cd = if self.rng.chance(0.5) { 1.min(d - 1) } else { d - 1 };
                let c = self.expr(Ty::Bool, cd);
                let (a, b) = if self.rng.chance(0.5) {
                    (self.leaf(ty), self.leaf(ty))
                } else {
                    (self.expr(ty, d - 1), self.expr(ty, d - 1))
                };
                E::node(ty, "if", "(if $0 $1 $2)", vec![c, a, b])
            }
            30..=33 => {
                let c1 = self.expr(Ty::Bool, d - 1);
                let a = self.expr(ty, d - 1);
                let c2 = self.expr(Ty::Bool, d - 1);
                let b = self.leaf(ty);
                let e = self.expr(ty, d - 1);
                E::node(ty, "cond", "(cond [$0 $1] [$2 $3] [else $4])", vec![c1, a, c2, b, e])
            }
            34..=45 => {
                let vt = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Bool, Ty::Int, Ty::Val]);
                let v = self.expr(vt, d - 1);
                let x = self.fresh("x");
                self.scope.push((x.clone(), vt, true));
                let body = self.expr(ty, d - 1);
                self.scope.pop();
                let form = *self.rng.pick(&["let", "let*", "letrec"]);
                E::node(ty, "let", &format!("({form} ([{x} $0]) $1)"), vec![v, body]).binding(&[&x])
            }
            46..=50 => {
                // mutable captured local
                let v = self.expr(Ty::Int, d - 1);
                let x = self.fresh("x");
                let g = self.fresh("g");
                self.scope.push((x.clone(), Ty::Int, true));
                let step = self.expr(Ty::Int, d - 1);
                let body = self.expr(ty, d - 1);
                self.scope.pop();
                E::node(
                    ty,
                    "closure-set",
                    &format!("(let* ([{x} $0] [{g} (lambda () (set! {x} $1) {x})]) ({g}) $2)"),
                    vec![v, step, body],
                )
                .binding(&[&x])
            }
            51..=55 => {
                // set! a settable variable of the same type in scope, else module var
                let mut sty = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Int, Ty::Fl, Ty::Val]);
                if sty == Ty::Val && self.settable(Ty::Val).is_none() {
                    sty = Ty::Int;
                }
                let local = self.settable(sty);
                let target = local.clone().unwrap_or_else(|| if sty == Ty::Int { "mv".into() } else { "mf".into() });
                let v = self.expr(sty, d - 1);
                let body = self.expr(ty, d - 1);
                let e = E::node(ty, "set", &format!("(begin (set! {target} $0) $1)"), vec![v, body]);
                match &local {
                    Some(n) => e.using(&[n]),
                    None => e,
                }
            }
            56..=60 => {
                let a = self.expr(ty, d - 1);
                let k = self.rng.below(10);
                E::node(ty, "tap", &format!("(tap {k} $0)"), vec![a])
            }
            61..=66 => {
                // escape continuation
                let a = self.expr(ty, d - 1);
                let c = self.expr(Ty::Bool, d - 1);
                let b = self.expr(ty, d - 1);
                let k = self.fresh("k");
                let form = *self.rng.pick(&["call/ec", "call/cc", "call-with-escape-continuation"]);
                E::node(ty, "escape", &format!("({form} (lambda ({k}) (if $1 ({k} $0) $2)))"), vec![a, c, b])
            }
            67..=69 => {
                let a = self.expr(ty, d - 1);
                E::node(ty, "dynamic-wind", "(dynamic-wind (lambda () (tap 'in 0)) (lambda () $0) (lambda () (tap 'out 0)))", vec![a])
            }
            70..=74 => {
                let at = *self.rng.pick(&[Ty::Int, Ty::Fl]);
                let a = self.expr(at, d - 1);
                let b = self.expr(Ty::Int, d - 1);
                let (x, y) = (self.fresh("x"), self.fresh("y"));
                self.scope.push((x.clone(), at, false));
                self.scope.push((y.clone(), Ty::Int, false));
                let body = self.expr(ty, d - 1);
                self.scope.pop();
                self.scope.pop();
                if self.rng.chance(0.5) {
                    E::node(ty, "values", &format!("(let-values ([({x} {y}) (values $0 $1)]) $2)"), vec![a, b, body]).binding(&[&x, &y])
                } else {
                    E::node(ty, "values", &format!("(call-with-values (lambda () (values $0 $1)) (lambda ({x} {y}) $2))"), vec![a, b, body]).binding(&[&x, &y])
                }
            }
            75..=79 => {
                let a = self.expr(ty, d - 1);
                let b = self.expr(ty, d - 1);
                E::node(ty, "handlers", "(with-handlers ([exn:fail? (lambda (e) (tap 'caught $1))]) $0)", vec![a, b])
            }
            80..=84 => {
                // local recursive function with bounded recursion
                let f = self.fresh("lf");
                let n = self.fresh("n");
                let x = self.fresh("x");
                let pt = *self.rng.pick(&[Ty::Int, Ty::Fl]);
                self.scope.push((n.clone(), Ty::Int, false));
                self.scope.push((x.clone(), pt, false));
                let base = self.expr(ty, d - 1);
                let step = self.expr(pt, d - 1);
                self.scope.pop();
                self.scope.pop();
                let cnt = self.small_lit(0, 5);
                let arg = self.expr(pt, d - 1);
                let comb = match ty {
                    Ty::Int => "(+ $0 ($F (fx- $N 1) $1))",
                    Ty::Fl => "(fl+ $0 ($F (fx- $N 1) $1))",
                    Ty::Val => "(cons $0 ($F (fx- $N 1) $1))",
                    _ => "(if $0 ($F (fx- $N 1) $1) #f)",
                };
                let rec = comb.replace("$F", &f).replace("$N", &n);
                // kids: 0 base, 1 step, 2 count, 3 arg
                let rec = rec.replace("$1", "$1").replace("$0", "$0");
                E::node(
                    ty,
                    "letrec-loop",
                    &format!("(letrec ([{f} (lambda ({n} {x}) (if (fx<= {n} 0) $0 {rec}))]) ({f} $2 $3))"),
                    vec![base, step, cnt, arg],
                )
                .binding(&[&n, &x])
            }
            85..=89 => {
                let a = self.expr(Ty::Int, d - 1);
                let b = self.expr(ty, d - 1);
                let c = self.expr(ty, d - 1);
                let e = self.leaf(ty);
                E::node(ty, "case", "(case $0 [(0 1) $1] [(2 -1 7) $2] [else $3])", vec![a, b, c, e])
            }
            90..=94 => {
                // immediate lambda application / unused local function
                let at = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Bool, Ty::Val]);
                let a = self.expr(at, d - 1);
                let x = self.fresh("x");
                let u = self.fresh("unused");
                self.scope.push((x.clone(), at, true));
                let body = self.expr(ty, d - 1);
                self.scope.pop();
                if self.rng.chance(0.5) {
                    E::node(ty, "lambda-app", &format!("((lambda ({x}) $1) $0)"), vec![a, body]).binding(&[&x])
                } else {
                    E::node(
                        ty,
                        "unused-fn",
                        &format!("(let ([{x} $0]) (define ({u} q) (set! {x} q) ({u} q)) $1)"),
                        vec![a, body],
                    )
                    .binding(&[&x])
                }
            }
            _ => {
                let a = self.expr(Ty::Int, d - 1);
                let b = self.expr(ty, d - 1);
                E::node(ty, "begin", "(begin $0 $1)", vec![a, b])
            }
        }
    }

    /// `X` combined with `Y` at type `ty` (Y is the hole of a captured continuation).
    fn comb(ty: Ty) -> &'static str {
        match ty {
            Ty::Int => "(fx+/wraparound X Y)",
            Ty::Fl => "(fl+ X Y)",
            Ty::Val => "(cons X Y)",
            _ => "(and X Y)",
        }
    }

    /// A list of marks (Val) seen through prompts with fresh tags.
    fn marks_val(&mut self, d: usize) -> E {
        let tg = self.fresh("tg");
        let v = self.fresh("v");
        let k = self.fresh("k");
        let a = self.expr(Ty::Val, d - 1);
        let b = self.expr(Ty::Val, d - 1);
        let tpl = match self.rng.below(5) {
            0 => format!("(let ([{tg} (make-continuation-prompt-tag)]) (with-continuation-mark 'key $0 (call-with-continuation-prompt (lambda () (with-continuation-mark 'key $1 (continuation-mark-set->list (current-continuation-marks {tg}) 'key))) {tg})))"),
            1 => format!("(let ([{tg} (make-continuation-prompt-tag)]) (with-continuation-mark 'key $0 (call-with-continuation-prompt (lambda () (list (continuation-mark-set-first #f 'key 'none {tg}) (with-continuation-mark 'key $1 (call-with-immediate-continuation-mark 'key (lambda ({v}) {v}) 'none)))) {tg})))"),
            2 => format!("(with-continuation-mark 'key $0 (list (call-with-immediate-continuation-mark 'key (lambda ({v}) {v}) 'none) (with-continuation-mark 'key $1 (continuation-mark-set->list (current-continuation-marks) 'key))))"),
            3 => format!("(let ([{tg} (make-continuation-prompt-tag)]) (call-with-continuation-prompt (lambda () ((let ([{k} (call-with-continuation-prompt (lambda () (with-continuation-mark 'key $0 (car (list (begin ((call-with-composable-continuation (lambda ({k}x) (lambda () (abort-current-continuation {tg} (lambda () {k}x)))) {tg})) (list $1 (continuation-mark-set->list (current-continuation-marks {tg}) 'key))))))) {tg} (lambda ({v}) ({v})))]) (lambda () ({k} void))))) {tg}))"),
            _ => format!("(let ([{tg} (make-continuation-prompt-tag)]) (with-continuation-mark 'key $0 (call-with-continuation-prompt (lambda () (car (list (with-continuation-mark 'key $1 (call-with-continuation-prompt (lambda () (continuation-mark-set->list (current-continuation-marks {tg}) 'key)))))) {tg}))))"),
        };
        E::node(Ty::Val, "marks-tag", &tpl, vec![a, b])
    }

    /// Delimited control: prompts with fresh or default tags, aborts
    /// (through dynamic-wind), composable continuations applied more than
    /// once, full continuations re-entered a bounded number of times,
    /// continuation marks seen through prompts (rumble control.ss).
    fn delim(&mut self, ty: Ty, d: usize) -> E {
        // generic `+` on flonums half the time (fl+ is the unboxed path)
        let c = if ty == Ty::Fl && self.rng.chance(0.5) { "(+ X Y)" } else { Self::comb(ty) };
        let tg = self.fresh("tg");
        let th = self.fresh("th");
        let k = self.fresh("k");
        let kk = self.fresh("kk");
        let r = self.fresh("r");
        let n = self.fresh("n");
        let wind = self.rng.chance(0.3);
        let dw = |e: &str| if wind { format!("(dynamic-wind (lambda () (tap 'in 0)) (lambda () {e}) (lambda () (tap 'out 0)))") } else { e.to_string() };
        match self.rng.below(5) {
            0 => {
                let a = self.expr(ty, d - 1);
                let cnd = self.expr(Ty::Bool, d - 1);
                let b = self.expr(ty, d - 1);
                let e = self.expr(ty, d - 1);
                let inner = dw("(if $1 (abort-current-continuation TAG (lambda () $2)) $3)");
                let body = c.replace("X", "$0").replace("Y", &inner);
                let tpl = if self.rng.chance(0.5) {
                    format!("(let ([{tg} (make-continuation-prompt-tag)]) (call-with-continuation-prompt (lambda () {}) {tg} (lambda ({th}) ({th}))))", body.replace("TAG", &tg))
                } else {
                    format!("(call-with-continuation-prompt (lambda () {}))", body.replace("TAG", "(default-continuation-prompt-tag)"))
                };
                E::node(ty, "prompt", &tpl, vec![a, cnd, b, e])
            }
            1 => {
                let a = self.expr(ty, d - 1);
                let b = self.expr(ty, d - 1);
                let e = self.expr(ty, d - 1);
                let cap = dw(&format!("(call-with-composable-continuation (lambda ({k}) (set! {kk} {k}) $1) {tg})"));
                let mut body = c.replace("X", "$0").replace("Y", &cap);
                if self.rng.chance(0.4) {
                    body = format!("(with-continuation-mark 'key 1 {body})");
                }
                let again = c.replace("X", &r).replace("Y", &format!("({kk} ({kk} $2))"));
                let tpl = format!("(let ([{kk} #f] [{tg} (make-continuation-prompt-tag)]) (let ([{r} (call-with-continuation-prompt (lambda () {body}) {tg})]) {again}))");
                E::node(ty, "composable", &tpl, vec![a, b, e])
            }
            2 => {
                let a = self.expr(ty, d - 1);
                let b = self.expr(ty, d - 1);
                let e = self.expr(ty, d - 1);
                let cap = dw(&format!("(call/cc (lambda ({k}) (set! {kk} {k}) $1))"));
                let body = c.replace("X", "$0").replace("Y", &cap);
                let lim = 2 + self.rng.below(3);
                let tpl = format!("(let ([{n} 0] [{kk} #f]) (let ([{r} {body}]) (set! {n} (fx+ {n} 1)) (if (fx< {n} {lim}) ({kk} $2) {r})))");
                E::node(ty, "reentry", &tpl, vec![a, b, e])
            }
            _ => {
                let m = self.marks_val(d);
                match ty {
                    Ty::Val => m,
                    Ty::Int => E::node(ty, "", "(length $0)", vec![m]),
                    Ty::Fl => E::node(ty, "", "(fx->fl (length $0))", vec![m]),
                    _ => E::node(ty, "", "(pair? $0)", vec![m]),
                }
            }
        }
    }

    fn rand_ty(&mut self) -> Ty {
        *self.rng.pick(&[Ty::Int, Ty::Int, Ty::Fl, Ty::Fl, Ty::Bool, Ty::Int, Ty::Fl, Ty::Val])
    }

    /// Inject a typed expression into the dynamic kind.
    fn inject(&mut self, d: usize) -> E {
        let t = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Bool, Ty::Int, Ty::Fl]);
        let a = self.expr(t, d);
        E::node(Ty::Val, "", "$0", vec![a])
    }

    fn val_to_int(&mut self, d: usize) -> E {
        let v = self.expr(Ty::Val, d - 1);
        let t = self.fresh("t");
        match self.rng.below(6) {
            0 | 1 => {
                let a = self.expr(Ty::Int, d - 1);
                {
                    let u = self.fresh("u");
                    E::node(Ty::Int, "type-guard", &format!("(let ([{t} $0] [{u} $1]) (if (fixnum? {t}) (fx+/wraparound {t} {u}) {u}))"), vec![v, a])
                }
            }
            2 | 3 => {
                let a = self.expr(Ty::Int, d - 1);
                E::node(
                    Ty::Int,
                    "type-dispatch",
                    &format!(
                        "(let ([{t} $0]) (cond [(fixnum? {t}) {t}] [(exact-integer? {t}) (integer-length {t})] [(flonum? {t}) (if (= {t} {t}) (fl->exact-integer (flfloor (flmin 1e18 (flmax -1e18 {t})))) -2)] [(pair? {t}) (+ 10 (if (list? {t}) (length {t}) 100))] [(string? {t}) (string-length {t})] [(char? {t}) (char->integer {t})] [(symbol? {t}) (string-length (symbol->string {t}))] [(null? {t}) 20] [(vector? {t}) (vector-length {t})] [(box? {t}) 30] [(boolean? {t}) (if {t} 41 40)] [else $1]))"
                    ),
                    vec![v, a],
                )
            }
            4 => E::node(Ty::Int, "list-op", &format!("(let ([{t} $0]) (if (list? {t}) (length {t}) -1))"), vec![v]),
            _ => {
                let a = self.expr(Ty::Int, d - 1);
                E::node(Ty::Int, "list-op", &format!("(let loop ([{t} $0] [n 0]) (if (and (pair? {t}) (fx< n 8)) (loop (cdr {t}) (fx+ n 1)) (if (null? {t}) n $1)))"), vec![v, a])
            }
        }
    }

    fn val_op(&mut self, d: usize) -> E {
        if self.rng.chance(0.3) {
            return self.lib_op(d);
        }
        let r = self.rng.below(100);
        match r {
            0..=19 => self.inject(d - 1),
            20..=31 => {
                let a = self.expr(Ty::Val, d - 1);
                let b = self.expr(Ty::Val, d - 1);
                match self.rng.below(4) {
                    0 | 1 => E::node(Ty::Val, "pair", "(cons $0 $1)", vec![a, b]),
                    2 => E::node(Ty::Val, "pair", "(list $0 $1)", vec![a, b]),
                    _ => {
                        let c = self.expr(Ty::Val, d - 1);
                        E::node(Ty::Val, "pair", "(list* $0 $1 $2)", vec![a, b, c])
                    }
                }
            }
            32..=43 => {
                let v = self.expr(Ty::Val, d - 1);
                let t = self.fresh("t");
                match self.rng.below(5) {
                    0 => E::node(Ty::Val, "pair-guard", &format!("(let ([{t} $0]) (if (pair? {t}) (car {t}) {t}))"), vec![v]),
                    1 => E::node(Ty::Val, "pair-guard", &format!("(let ([{t} $0]) (if (pair? {t}) (cdr {t}) '()))"), vec![v]),
                    2 => E::node(Ty::Val, "list-op", &format!("(let ([{t} $0]) (if (list? {t}) (reverse {t}) (list {t})))"), vec![v]),
                    3 => {
                        let w = self.expr(Ty::Val, d - 1);
                        E::node(Ty::Val, "list-op", &format!("(let ([{t} $0]) (if (list? {t}) (append {t} (list $1)) {t}))"), vec![v, w])
                    }
                    _ => {
                        let w = self.expr(Ty::Val, d - 1);
                        E::node(Ty::Val, "list-op", "(member $0 (list 1 'a \"ab\" $1 2.0))", vec![v, w])
                    }
                }
            }
            44..=53 => {
                // mixed-type if / cond arms
                let c = self.expr(Ty::Bool, d - 1);
                let ta = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Bool, Ty::Val]);
                let tb = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Val]);
                let a = if self.rng.chance(0.5) { self.leaf(ta) } else { self.expr(ta, d - 1) };
                let b = if self.rng.chance(0.5) { self.leaf(tb) } else { self.expr(tb, d - 1) };
                E::node(Ty::Val, "if-mixed", "(if $0 $1 $2)", vec![c, a, b])
            }
            54..=63 => {
                let i = self.expr(Ty::Int, d - 1);
                let t = self.fresh("t");
                match self.rng.below(5) {
                    0 => E::node(Ty::Val, "char", &format!("(let ([{t} $0]) (integer->char (+ 48 (modulo {t} 75))))"), vec![i]),
                    1 => E::node(Ty::Val, "string", "(number->string $0)", vec![i]),
                    2 => E::node(Ty::Val, "string", &format!("(let ([{t} (modulo $0 4)]) (substring \"hello\" {t} (+ {t} 1)))"), vec![i]),
                    3 => E::node(Ty::Val, "symbol", &format!("(string->symbol (string-append \"s\" (number->string (modulo $0 3))))"), vec![i]),
                    _ => {
                        let v = self.expr(Ty::Val, d - 1);
                        E::node(Ty::Val, "string", &format!("(let ([{t} $1]) (if (string? {t}) (string-append {t} (number->string $0)) (if (char? {t}) (string {t} #\\x) {t})))"), vec![i, v])
                    }
                }
            }
            64..=71 => {
                let v = self.expr(Ty::Val, d - 1);
                let w = self.expr(Ty::Val, d - 1);
                let b = self.fresh("bx");
                match self.rng.below(3) {
                    0 => E::node(Ty::Val, "box", &format!("(let ([{b} (box $0)]) (set-box! {b} (cons $1 (unbox {b}))) (unbox {b}))"), vec![v, w]),
                    1 => {
                        let i = self.expr(Ty::Int, d - 1);
                        E::node(Ty::Val, "vector-any", &format!("(let ([{b} (vector $0 $1)]) (vector-set! {b} (modulo $2 2) (cons 1 (vector-ref {b} 0))) (vector-ref {b} 1))"), vec![v, w, i])
                    }
                    _ => E::node(Ty::Val, "vector-any", "(vector->list (vector $0 $1))", vec![v, w]),
                }
            }
            72..=79 => {
                let v = self.expr(Ty::Val, d - 1);
                let a = self.expr(Ty::Val, d - 1);
                let b = self.expr(Ty::Val, d - 1);
                let e = self.leaf(Ty::Val);
                E::node(Ty::Val, "case-any", "(case $0 [(a 0) $1] [(#\\a \"ab\" 2.0 ()) $2] [else $3])", vec![v, a, b, e])
            }
            80..=87 => {
                let v = self.expr(Ty::Val, d - 1);
                let t = self.fresh("t");
                E::node(
                    Ty::Val,
                    "type-dispatch",
                    &format!("(let ([{t} $0]) (cond [(fixnum? {t}) (fx->fl {t})] [(flonum? {t}) (if (fl< {t} 0.0) 'neg {t})] [(string? {t}) (string->list {t})] [(char? {t}) (char-upcase {t})] [(pair? {t}) (cdr {t})] [(symbol? {t}) (symbol->string {t})] [else (not {t})]))"),
                    vec![v],
                )
            }
            _ => self.call_or_leaf(Ty::Val, d),
        }
    }

    /// One top-level item.
    pub fn item(&mut self, d: usize) -> E {
        let r = self.rng.below(100);
        match r {
            0..=19 => {
                let t = self.rand_ty();
                let v = self.fresh("v");
                let e = self.expr(t, d);
                self.scope.push((v.clone(), t, true));
                E::node(Ty::Stmt, "", &format!("(define {v} $0)"), vec![e]).defining(&[&v])
            }
            20..=24 => {
                let (a, b) = (self.fresh("v"), self.fresh("v"));
                let ea = self.expr(Ty::Int, d);
                let eb = self.expr(Ty::Fl, d);
                self.scope.push((a.clone(), Ty::Int, false));
                self.scope.push((b.clone(), Ty::Fl, false));
                E::node(Ty::Stmt, "", &format!("(define-values ({a} {b}) (values $0 $1))"), vec![ea, eb]).defining(&[&a, &b])
            }
            25..=49 => {
                let name = self.fresh("f");
                let np = self.rng.below(4);
                let params: Vec<Ty> = (0..np).map(|_| self.rand_ty()).collect();
                let ret = self.rand_ty();
                let mut names = vec![];
                let saved = self.scope.len();
                for t in &params {
                    let p = self.fresh("a");
                    self.scope.push((p.clone(), *t, true));
                    names.push(p);
                }
                let e = if self.rng.chance(0.3) {
                    // internal definition
                    let it = self.rand_ty();
                    let iv = self.fresh("w");
                    let ie = self.expr(it, d - 1);
                    self.scope.push((iv.clone(), it, true));
                    let body = self.expr(ret, d);
                    E::node(ret, "internal-define", &format!("(define {iv} $0) $1"), vec![ie, body]).binding(&[&iv])
                } else if self.rng.chance(0.3) {
                    // small body (one or two operations): under schemify's
                    // inlining size limits, also across modules (split variants)
                    let sd = 1 + self.rng.below(2);
                    self.expr(ret, sd)
                } else {
                    self.expr(ret, d)
                };
                self.scope.truncate(saved);
                self.funs.push(Fun { name: name.clone(), params, ret });
                let pn: Vec<&String> = names.iter().collect();
                E::node(Ty::Stmt, "", &format!("(define ({name} {}) $0)", names.join(" ")), vec![e]).binding(&pn).defining(&[&name])
            }
            50..=54 => {
                let e = self.expr(Ty::Int, d);
                E::node(Ty::Stmt, "", "(set! mv $0)", vec![e])
            }
            55..=59 => {
                let t = self.rand_ty();
                let e = self.expr(t, d);
                E::node(Ty::Stmt, "", "(writeln $0)", vec![e])
            }
            _ => {
                let t = self.rand_ty();
                let e = self.expr(t, d);
                E::node(Ty::Stmt, "", "(show $0)", vec![e])
            }
        }
    }

    pub fn program(&mut self) -> Program {
        let n = 3 + self.rng.below(10);
        let d = 2 + self.rng.below(4);
        let mut items = vec![];
        for _ in 0..n {
            items.push(self.item(d));
        }
        // Make sure functions get called.
        for f in self.funs.clone() {
            if self.rng.chance(0.7) {
                let mut tpl = format!("(show ({}", f.name);
                let mut kids = vec![];
                for (k, p) in f.params.iter().enumerate() {
                    tpl.push_str(&format!(" ${k}"));
                    kids.push(self.expr(*p, 2));
                }
                tpl.push_str("))");
                items.push(E::node(Ty::Stmt, "call", &tpl, kids).using(&[&f.name]));
            }
        }
        Program(items)
    }
}

/// A generated module body: top-level items after the fixed prelude.
#[derive(Clone)]
pub struct Program(pub Vec<E>);

impl std::fmt::Debug for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for it in &self.0 {
            let mut s = String::new();
            it.render(&mut s);
            writeln!(f, "{s}")?;
        }
        Ok(())
    }
}

/// Well scoped: every free name of an item is defined by an earlier item
/// (prelude names such as `mv` are not tracked).  Types are preserved by
/// construction and by every shrink step.
pub fn valid(p: &Program) -> bool {
    let mut defined: Vec<String> = vec![];
    for it in &p.0 {
        if it.ty != Ty::Stmt {
            return false;
        }
        let mut fr = vec![];
        it.free(&mut fr);
        if fr.iter().any(|n| !defined.contains(n)) {
            return false;
        }
        defined.extend(it.defines.iter().cloned());
    }
    true
}

pub const PRELUDE: &str = r#"(module m racket/base
(require racket/fixnum racket/flonum)
(define mv 0)
(define mf 0.0)
(define prm (make-parameter 0))
(struct pt (a b) #:mutable #:transparent)
(define (tap k v) (display k) (display " ") v)
(define (nan?* x) (not (= x x)))
(define (infinite?* x) (and (flonum? x) (or (= x +inf.0) (= x -inf.0))))
(define (exact-truncate* x) (inexact->exact (fltruncate x)))
(define (exn-kind e)
  (cond [(exn:fail:contract:divide-by-zero? e) 'div0]
        [(exn:fail:contract:non-fixnum-result? e) 'nonfx]
        [(exn:fail:contract:arity? e) 'arity]
        [(exn:fail:contract:variable? e) 'variable]
        [(exn:fail:contract? e) 'contract]
        [(exn:fail:out-of-memory? e) 'oom]
        [else 'fail]))
(define-syntax-rule (show e)
  (with-handlers ([exn:fail? (lambda (x) (writeln (list 'exn (exn-kind x) (if (exn:fail:contract:non-fixnum-result? x) "masked" (car (regexp-match #rx"^[^\n]*" (exn-message x)))))))])
    (writeln e)))
"#;

pub fn render_program(items: &[E]) -> String {
    let mut s = String::from(PRELUDE);
    for it in items {
        it.render(&mut s);
        s.push('\n');
    }
    s.push_str("(writeln (list 'final mv mf (prm))))\n");
    s
}

// ---------------------------------------------------------------------------
// ephyra generator

use std::ops::ControlFlow;

pub struct ProgramGen;

fn paths(e: &E, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    out.push(cur.clone());
    for i in 0..e.kids.len() {
        cur.push(i);
        paths(&e.kids[i], cur, out);
        cur.pop();
    }
}
fn get_mut<'b>(e: &'b mut E, path: &[usize]) -> &'b mut E {
    let mut cur = e;
    for &i in path {
        cur = &mut cur.kids[i];
    }
    cur
}
fn simplest(ty: Ty) -> Option<E> {
    match ty {
        Ty::Int => Some(E::atom(Ty::Int, "0")),
        Ty::Fl => Some(E::atom(Ty::Fl, "0.0")),
        Ty::Bool => Some(E::atom(Ty::Bool, "#t")),
        Ty::Val => Some(E::atom(Ty::Val, "'()")),
        Ty::Stmt => None,
    }
}

impl ephyra::Gen for ProgramGen {
    type Value = Program;
    fn generate(&self, g: &mut Source) -> Program {
        Gen::new(g).program()
    }
    /// Candidates, most promising first: drop a top-level item; replace a
    /// node by a child of the same type; replace a node by the simplest
    /// literal of its type.  Only well-scoped candidates are offered.
    fn shrink(&self, p: &Program, visit: &mut dyn FnMut(Program) -> ControlFlow<()>) -> ControlFlow<()> {
        for i in (0..p.0.len()).rev() {
            let mut c = p.clone();
            c.0.remove(i);
            if valid(&c) {
                visit(c)?;
            }
        }
        for it in 0..p.0.len() {
            let mut ps = vec![];
            paths(&p.0[it], &mut vec![], &mut ps);
            for path in &ps {
                let mut c0 = p.clone();
                let node = get_mut(&mut c0.0[it], path).clone();
                if node.ty == Ty::Stmt {
                    continue;
                }
                for k in node.kids.iter().filter(|k| k.ty == node.ty) {
                    let mut c = p.clone();
                    *get_mut(&mut c.0[it], path) = k.clone();
                    if valid(&c) {
                        visit(c)?;
                    }
                }
                if let Some(s) = simplest(node.ty) {
                    if s.tpl != node.tpl {
                        let mut c = p.clone();
                        *get_mut(&mut c.0[it], path) = s;
                        visit(c)?;
                    }
                }
            }
        }
        ControlFlow::Continue(())
    }
}

#[ephyra::generator]
pub fn valid_program(p: &Program) -> bool {
    valid(p)
}

pub fn program_metrics(p: &Program, _size: usize) -> Vec<(&'static str, f64)> {
    let mut tags = vec![];
    for it in &p.0 {
        it.tags(&mut tags);
    }
    let nodes: usize = p.0.iter().map(|e| e.size()).sum();
    let mut text = String::new();
    for it in &p.0 {
        it.render(&mut text);
    }
    vec![
        ("items", p.0.len() as f64),
        ("nodes", nodes as f64),
        ("chars", text.len() as f64),
        ("loops", tags.iter().filter(|t| t.contains("loop") || t.starts_with("for")).count() as f64),
        ("if", tags.iter().filter(|t| **t == "if").count() as f64),
        ("fl", tags.iter().filter(|t| t.starts_with("fl")).count() as f64),
        ("control", tags.iter().filter(|t| ["escape", "wcm", "dynamic-wind", "parameterize", "handlers", "prompt", "composable", "reentry", "marks-tag"].contains(t)).count() as f64),
    ]
}

#[ephyra::generator(valid_program, metrics = program_metrics)]
pub fn programs() -> ProgramGen {
    ProgramGen
}

// ---------------------------------------------------------------------------
// Library primitives (steering round 7): exact rationals, complex numbers,
// number<->string, strings/chars/bytes with Unicode casing, symbols and
// keywords, sorting and list library, mutable/immutable hash tables,
// printing to string ports and reading back, simple regexps.  These run
// the same rumble/Chez library code in machine-code and interpreter mode,
// so the `ref93` oracle (released Racket 9.3 on the same module) is what
// checks them.  Results are values of the dynamic kind (or typed through
// lib_typed).  Only deterministic results: no hash iteration order, no
// eq? on numbers/chars/strings, no hash codes, no procedure printing.

/// Exact rationals, complex numbers, extra integers and inexact edge cases.
const NUM_POOL: &[&str] = &[
    "1/3", "-7/2", "22/7", "1/1024", "-1/3", "3/4", "100000000000000000001/3", "1+2i", "0+1i",
    "-1.5+0.5i", "1.0+0.0i", "3/4-1/2i", "+inf.0+1i", "12345678901234567890", "-98765432109876543210123",
    "(expt 2 64)", "(- (expt 2 62))", "1e21", "1e-7", "123.456", "5e-324", "1.7976931348623157e308",
    "0.30000000000000004", "2/3", "#e1.1", "0", "-0.0", "+nan.0", "-inf.0", "7",
];
/// Strings: ASCII, Latin-1 and classic Unicode with special casing
/// (sharp s, final sigma, dotted I, title-case digraph, ligature,
/// combining accent), digits, separators.
const STR_POOL: &[&str] = &[
    "\"ab\"", "\"\"", "\"Hello World\"", "\"stra\u{df}e\"", "\"\u{3a3}\u{391}\u{3a3}\"", "\"\u{130}stanbul\"",
    "\"\u{1c5}x\"", "\"\u{fb01}ne\"", "\"e\u{301}\"", "\"\u{e9}t\u{e9}\"", "\"\u{3bb}x.x\"", "\"a,b,,c\"",
    "\"0123\"", "\"x\\ty\"", "\"  pad \"", "\"aaab\"", "\"ABC\"", "\"-12.5e3\"", "\"\u{1f600}\"",
];
/// Strings for string->number (valid and invalid notations).
const NUMSTR_POOL: &[&str] = &[
    "\"1/3\"", "\"#e1.5\"", "\"1e400\"", "\"-0\"", "\"#x-ff\"", "\"1.5+2i\"", "\"+inf.0\"", "\"#i1/3\"",
    "\"12345678901234567890\"", "\".5e-3\"", "\"#b101.1\"", "\"1e-400\"", "\"#e1e30\"", "\"1/0\"", "\"+i\"",
    "\"#d1.0e2\"", "\"1_000\"", "\"-nan.0\"", "\"#e1.2e-3\"", "\"1#.#\"", "\"#o777\"", "\"1@2\"", "\"#x1.8p3\"",
    "\"0.1e1\"", "\"-.e1\"", "\"9007199254740993\"", "\"9007199254740993.0\"", "\"#e-0.0\"", "\"2.5e-324\"",
];
const CHAR_POOL: &[&str] = &[
    "#\\a", "#\\Z", "#\\0", "#\\space", "#\\\u{df}", "#\\\u{3c3}", "#\\\u{3a3}", "#\\\u{1c5}", "#\\\u{130}",
    "#\\\u{e9}", "#\\nul", "#\\\u{2163}", "#\\\u{663}", "#\\_", "#\\tab",
];
const BYTES_POOL: &[&str] = &["#\"abc\"", "#\"\"", "#\"\\200\\377a\"", "#\"\\303\\251\"", "#\"\\355\\240\\200\"", "#\"\\360\\237\\230\\200\"", "#\"a\\0b\""];
const RX_POOL: &[&str] = &[
    "#rx\"a+b*\"", "#rx\"(a|b)c\"", "#px\"\\\\d+\"", "#rx\"^[^,]*\"", "#px\"(\\\\w+)\\\\s+(\\\\w+)\"", "#rx\"[aeiou]\"",
    "#rx\"(?i:hello)\"", "#px\"a{2,3}\"", "#rx\"x*\"", "#px\"\\\\bW\"",
];

/// Port contents (steering round 12): line endings, readable data, UTF-8
/// and invalid sequences, data across the 4096-byte port buffer.
const PORT_DATA_POOL: &[&str] = &[
    "#\"line1\\nline2\\r\\nl3\\rlast\"", "#\"(1 2) #(a \\\"b\\\") 3.5 sym ; c\\n#t\"",
    "#\"\\303\\251t\\303\\251\\n\\360\\237\\230\\200\\200x\"", "#\"a\\tb\\tc\\n\\n\"", "#\"\"", "#\"x\"",
    "(bytes-append (make-bytes 4094 97) #\"\\r\\n\\303\\251(x . y) z\")", "(make-bytes 4097 10)",
    "#\"ab(c\\r\\n12 345\\r\"", "#\"#hash((1 . 2)) \\\"s\\\\n\\\" #\\\\x 1/2 -0.0\"", "#\"\\377\\376\\0zz\\n\"",
    "(bytes-append #\"(\" (make-bytes 5000 49) #\")\")",
];
const PORT_RX_POOL: &[&str] = &[
    "#rx\"[0-9]+\"", "#rx#\"\\n\"", "#px\"(?<=a)b\"", "#rx\"$\"", "#rx\"^a*\"", "#px\"\\\\s+\"", "#rx\"(x|\u{e9})\"",
    "#px\"\\\\p{Ll}+\"", "#rx#\"[\\200-\\377]+\"", "#rx\"zz\"", "#px\"(?<!a)[(]\"", "#rx\"a(?=b)\"", "#rx\"\\r\\n|\\r|\\n\"",
    "#rx\"\"", "#px\"[a-z]{2,}\"",
];
const LINE_MODES: &[&str] = &["'linefeed", "'return", "'return-linefeed", "'any", "'any-one"];

impl<'a> Gen<'a> {
    fn lib_lit(&mut self, pool: &[&'static str]) -> E {
        E::atom(Ty::Val, self.rng.pick(pool))
    }
    /// A number of any kind.
    fn lib_num(&mut self, d: usize) -> E {
        if d == 0 {
            return self.lib_lit(NUM_POOL);
        }
        match self.rng.below(10) {
            0 | 1 => { let e = self.expr(Ty::Int, d - 1); E::node(Ty::Val, "", "$0", vec![e]) }
            2 | 3 => { let e = self.expr(Ty::Fl, d - 1); E::node(Ty::Val, "", "$0", vec![e]) }
            4 | 5 | 6 => self.lib_lit(NUM_POOL),
            _ => {
                // lib_numop may give a boolean, list or string: keep numbers
                let e = self.lib_numop(d - 1);
                let t = self.fresh("t");
                E::node(Ty::Val, "", &format!("(let ([{t} $0]) (if (number? {t}) {t} 7))"), vec![e])
            }
        }
    }
    fn lib_int(&mut self, d: usize) -> E {
        if d == 0 || self.rng.chance(0.4) {
            if self.rng.chance(0.5) {
                return E::atom(Ty::Int, self.rng.pick(INT_POOL));
            }
            return self.small_lit(-3, 70);
        }
        self.expr(Ty::Int, d - 1)
    }
    fn lib_str(&mut self, d: usize) -> E {
        if d == 0 || self.rng.chance(0.5) {
            return self.lib_lit(STR_POOL);
        }
        // lib_strop may give any value: non-strings are printed
        let e = self.lib_strop(d - 1);
        let t = self.fresh("t");
        E::node(Ty::Val, "", &format!("(let ([{t} $0]) (if (string? {t}) {t} (format \"~s\" {t})))"), vec![e])
    }
    fn lib_char(&mut self, d: usize) -> E {
        if d == 0 || self.rng.chance(0.6) {
            return self.lib_lit(CHAR_POOL);
        }
        let s = self.lib_str(d - 1);
        let i = self.lib_int(d - 1);
        let t = self.fresh("t");
        E::node(Ty::Val, "lib-char", &format!("(let ([{t} $0]) (if (positive? (string-length {t})) (string-ref {t} (modulo $1 (string-length {t}))) #\\x))"), vec![s, i])
    }
    /// A list of numbers.
    fn lib_numlist(&mut self, d: usize) -> E {
        let n = 1 + self.rng.below(4);
        let kids: Vec<E> = (0..n).map(|_| self.lib_num(d)).collect();
        let tpl = format!("(list {})", (0..n).map(|k| format!("${k}")).collect::<Vec<_>>().join(" "));
        E::node(Ty::Val, "", &tpl, kids)
    }

    fn lib_numop(&mut self, d: usize) -> E {
        let t = self.fresh("t");
        match self.rng.below(30) {
            0 => { let a = self.lib_num(d); let b = self.lib_num(d); let op = *self.rng.pick(&["/", "+", "*", "-", "max", "min"]); E::node(Ty::Val, "lib-num", &format!("({op} $0 $1)"), vec![a, b]) }
            1 => { let a = self.lib_int(d); let b = self.lib_int(d); E::node(Ty::Val, "lib-num", "(/ $0 $1)", vec![a, b]) }
            2 => { let a = self.lib_num(d); E::node(Ty::Val, "lib-num", "(exact->inexact $0)", vec![a]) }
            3 => { let a = self.lib_num(d); E::node(Ty::Val, "lib-num", "(inexact->exact $0)", vec![a]) }
            4 => { let a = self.lib_num(d); let k = self.small_lit(-4, 70); E::node(Ty::Val, "lib-num", "(expt $0 $1)", vec![a, k]) }
            5 => { let a = self.lib_num(d); let b = self.lib_num(d); E::node(Ty::Val, "lib-num", "(expt $0 $1)", vec![a, b]) }
            6 => {
                let a = self.lib_num(d);
                let op = *self.rng.pick(&["sqrt", "exp", "log", "sin", "cos", "atan", "tan", "asin", "acos"]);
                if ["atan", "asin", "acos"].contains(&op) {
                    // complex arguments: 47b09a1d58 changed atanh of complex args after 9.3
                    E::node(Ty::Val, "lib-num", &format!("(let ([{t} $0]) (if (real? {t}) ({op} {t}) 'cx))"), vec![a])
                } else {
                    E::node(Ty::Val, "lib-num", &format!("({op} $0)"), vec![a])
                }
            }
            7 => { let a = self.lib_num(d); let op = *self.rng.pick(&["floor", "ceiling", "round", "truncate", "numerator", "denominator", "abs", "magnitude", "angle", "real-part", "imag-part", "exact-nonnegative-integer?", "integer?", "rational?", "exact?"]); E::node(Ty::Val, "lib-num", &format!("({op} $0)"), vec![a]) }
            8 => { let a = self.lib_int(d); let r = *self.rng.pick(&["2", "8", "16", "10"]); E::node(Ty::Val, "lib-numstr", &format!("(number->string $0 {r})"), vec![a]) }
            9 | 10 => { let a = self.lib_num(d); E::node(Ty::Val, "lib-numstr", "(number->string $0)", vec![a]) }
            11 | 12 => { let s = self.lib_lit(NUMSTR_POOL); if self.rng.chance(0.3) { let r = *self.rng.pick(&["2", "8", "16"]); E::node(Ty::Val, "lib-numstr", &format!("(string->number $0 {r})"), vec![s]) } else { E::node(Ty::Val, "lib-numstr", "(string->number $0)", vec![s]) } }
            13 => { let a = self.lib_num(d); E::node(Ty::Val, "lib-numstr", &format!("(let ([{t} $0]) (equal? {t} (string->number (number->string {t}))))"), vec![a]) }
            14 => { let a = self.lib_num(d); let e = self.lib_lit(&["1/100", "1/10", "0", "0.001", "1/3"]); E::node(Ty::Val, "lib-num", "(rationalize (inexact->exact $0) $1)", vec![a, e]) }
            15 => { let a = self.lib_int(d); let b = self.lib_int(d); let op = *self.rng.pick(&["quotient/remainder", "floor/"]); let op = if op == "floor/" { "quotient/remainder" } else { op }; E::node(Ty::Val, "lib-num", &format!("(call-with-values (lambda () ({op} $0 $1)) list)"), vec![a, b]) }
            16 => { let a = self.lib_int(d); E::node(Ty::Val, "lib-num", "(call-with-values (lambda () (integer-sqrt/remainder (abs $0))) list)", vec![a]) }
            17 => { let a = self.lib_int(d); let s = self.small_lit(0, 70); let e = self.small_lit(0, 130); E::node(Ty::Val, "lib-num", &format!("(let ([{t} $1]) (bitwise-bit-field $0 {t} (max {t} $2)))"), vec![a, s, e]) }
            18 => { let a = self.lib_int(d); let k = self.small_lit(-130, 130); E::node(Ty::Val, "lib-num", "(arithmetic-shift $0 $1)", vec![a, k]) }
            19 => { let a = self.lib_num(d); let b = self.lib_num(d); E::node(Ty::Val, "lib-num", "(make-rectangular $0 $1)", vec![a, b]) }
            20 => { let a = self.lib_num(d); let b = self.lib_num(d); E::node(Ty::Val, "lib-num", "(make-polar $0 $1)", vec![a, b]) }
            21 => { let a = self.lib_num(d); let b = self.lib_num(d); let op = *self.rng.pick(&["=", "<", "<=", ">", ">="]); E::node(Ty::Val, "lib-cmp", &format!("({op} $0 $1)"), vec![a, b]) }
            22 => { let a = self.lib_num(d); let b = self.lib_num(d); let op = *self.rng.pick(&["eqv?", "equal?"]); E::node(Ty::Val, "lib-cmp", &format!("({op} $0 $1)"), vec![a, b]) }
            23 => { let a = self.lib_num(d); let b = self.lib_num(d); E::node(Ty::Val, "lib-num", "(atan $0 $1)", vec![a, b]) }
            24 => { let a = self.lib_num(d); let b = self.lib_num(d); E::node(Ty::Val, "lib-num", "(log $0 $1)", vec![a, b]) }
            25 => { let l = self.lib_numlist(d); let op = *self.rng.pick(&["max", "min", "+", "*", "gcd"]); E::node(Ty::Val, "lib-list", &format!("(apply {op} $0)"), vec![l]) }
            26 => { let a = self.lib_int(d); let k = self.small_lit(1, 80); E::node(Ty::Val, "lib-num", "(exact->inexact (/ (expt 10 $1) (+ 3 (abs $0))))", vec![a, k]) }
            27 => { let a = self.lib_num(d); E::node(Ty::Val, "lib-num", &format!("(let ([{t} $0]) (if (real? {t}) (list (round {t}) (exact->inexact {t}) (inexact->exact (round (* 1.0 {t})))) {t}))"), vec![a]) }
            28 => { let a = self.lib_int(d); let b = self.lib_int(d); let op = *self.rng.pick(&["bitwise-bit-set?", "gcd", "lcm", "modulo", "remainder"]); E::node(Ty::Val, "lib-num", &format!("({op} $0 $1)"), vec![a, b]) }
            _ => { let a = self.lib_num(d); let op = *self.rng.pick(&["exact-integer?", "nan?*", "zero?", "positive?", "even?", "real?", "complex?", "flonum?", "single-flonum?"]); E::node(Ty::Val, "lib-num", &format!("({op} $0)"), vec![a]) }
        }
    }

    fn lib_strop(&mut self, d: usize) -> E {
        let t = self.fresh("t");
        match self.rng.below(22) {
            0 | 1 => { let s = self.lib_str(d); let op = *self.rng.pick(&["string-upcase", "string-downcase", "string-foldcase", "string-titlecase", "string-normalize-nfd", "string-normalize-nfc", "string-normalize-nfkc", "string-normalize-nfkd"]); E::node(Ty::Val, "lib-string", &format!("({op} $0)"), vec![s]) }
            2 => { let a = self.lib_str(d); let b = self.lib_str(d); let op = *self.rng.pick(&["string<?", "string=?", "string-ci=?", "string-ci<?", "string>=?", "string-ci>?"]); E::node(Ty::Val, "lib-string", &format!("({op} $0 $1)"), vec![a, b]) }
            3 => { let a = self.lib_str(d); let b = self.lib_str(d); E::node(Ty::Val, "lib-string", "(string-append $0 $1)", vec![a, b]) }
            4 => { let s = self.lib_str(d); let i = self.lib_int(d); let j = self.lib_int(d); E::node(Ty::Val, "lib-string", &format!("(let* ([{t} $0] [n (string-length {t})] [i (modulo $1 (add1 n))]) (substring {t} i (max i (modulo $2 (add1 n)))))"), vec![s, i, j]) }
            5 => { let s = self.lib_str(d); E::node(Ty::Val, "lib-string", "(string->list $0)", vec![s]) }
            6 => { let a = self.lib_char(d); let b = self.lib_char(d); E::node(Ty::Val, "lib-string", "(list->string (list $0 $1 $0))", vec![a, b]) }
            7 => { let s = self.lib_str(d); E::node(Ty::Val, "lib-bytes", "(string->bytes/utf-8 $0)", vec![s]) }
            8 => { let b = self.lib_lit(BYTES_POOL); let op = *self.rng.pick(&["(bytes->string/utf-8 $0 #\\?)", "(bytes->string/latin-1 $0)", "(bytes->string/utf-8 $0)", "(bytes->list $0)", "(bytes-length $0)", "(bytes-utf-8-length $0 #\\?)", "(bytes->string/locale $0 #\\?)"]); E::node(Ty::Val, "lib-bytes", op, vec![b]) }
            9 => { let s = self.lib_str(d); let op = *self.rng.pick(&["(string->bytes/latin-1 $0 63)", "(string-utf-8-length $0)", "(bytes-append (string->bytes/utf-8 $0) #\"\\0\")", "(string->immutable-string $0)", "(string-copy $0)"]); E::node(Ty::Val, "lib-bytes", op, vec![s]) }
            10 => { let c = self.lib_char(d); let op = *self.rng.pick(&["char-upcase", "char-downcase", "char-foldcase", "char-titlecase", "char->integer", "char-general-category", "char-alphabetic?", "char-numeric?", "char-whitespace?", "char-upper-case?", "char-title-case?", "char-symbolic?", "char-punctuation?", "char-graphic?", "char-blank?", "char-iso-control?", "char-extended-pictographic?"]); E::node(Ty::Val, "lib-char", &format!("({op} $0)"), vec![c]) }
            11 => { let a = self.lib_char(d); let b = self.lib_char(d); let op = *self.rng.pick(&["char<?", "char-ci=?", "char-ci<?", "char=?"]); E::node(Ty::Val, "lib-char", &format!("({op} $0 $1)"), vec![a, b]) }
            12 => { let s = self.lib_str(d); let op = *self.rng.pick(&["string->symbol", "string->uninterned-symbol", "string->keyword", "string->unreadable-symbol"]); let w = if op == "string->keyword" { "(keyword->string ($op $0))" } else { "(symbol->string ($op $0))" }; E::node(Ty::Val, "lib-symbol", &w.replace("$op", op), vec![s]) }
            13 => { let a = self.lib_str(d); let b = self.lib_str(d); let op = *self.rng.pick(&["(symbol<? (string->symbol $0) (string->symbol $1))", "(keyword<? (string->keyword $0) (string->keyword $1))", "(eq? (string->symbol $0) (string->symbol $1))", "(equal? $0 $1)"]); E::node(Ty::Val, "lib-symbol", op, vec![a, b]) }
            14 => { let i = self.lib_int(d); let c = self.lib_char(d); E::node(Ty::Val, "lib-string", "(make-string (modulo $0 5) $1)", vec![i, c]) }
            15 | 16 => { let rx = self.lib_lit(RX_POOL); let s = self.lib_str(d); let op = *self.rng.pick(&["(regexp-match $0 $1)", "(regexp-match-positions $0 $1)", "(regexp-match* $0 $1)", "(regexp-split $0 $1)", "(regexp-replace $0 $1 \"<\\\\0>\")", "(regexp-replace* $0 $1 \"_\")", "(regexp-match? $0 $1)", "(regexp-match-positions* $0 $1)"]); E::node(Ty::Val, "lib-regexp", op, vec![rx, s]) }
            17 => { let v = self.lib_any(d); let op = *self.rng.pick(&["write", "display", "print"]); E::node(Ty::Val, "lib-print", &format!("(let ([o (open-output-string)]) ({op} $0 o) (get-output-string o))"), vec![v]) }
            18 => { let a = self.lib_any(d); let b = self.lib_any(d); let f = *self.rng.pick(&["\"~a|~s\"", "\"~v ~e\"", "\"~s~n~a\"", "\"~.3a/~s\""]); E::node(Ty::Val, "lib-print", &format!("(format {f} $0 $1)"), vec![a, b]) }
            19 => { let v = self.lib_any(d); E::node(Ty::Val, "lib-print", &format!("(let ([{t} $0]) (with-handlers ([exn:fail:read? (lambda (e) 'unreadable)]) (let ([r (read (open-input-string (format \"~s\" {t})))]) (list r (equal? r {t})))))"), vec![v]) }
            20 => { let s = self.lib_str(d); E::node(Ty::Val, "lib-print", &format!("(with-handlers ([exn:fail:read? (lambda (e) 'read-error)]) (let ([p (open-input-string $0)]) (let loop ([n 0] [acc '()]) (let ([{t} (read p)]) (if (or (eof-object? {t}) (fx> n 4)) (reverse acc) (loop (fx+ n 1) (cons {t} acc)))))))"), vec![s]) }
            _ => { let n = self.lib_num(d); E::node(Ty::Val, "lib-string", "(string-length (number->string $0))", vec![n]) }
        }
    }

    /// Lists, sorting, hash tables.
    fn lib_collop(&mut self, d: usize) -> E {
        let h = self.fresh("h");
        match self.rng.below(10) {
            0 | 1 => { let l = self.lib_numlist(d); let op: &str = self.rng.pick(&["(sort (filter real? $0) <)", "(sort (filter real? $0) >=)", "(sort (map number->string $0) string<?)", "(foldl cons '() $0)", "(map (lambda (x) (* x x)) $0)", "(assv 1/3 (map (lambda (x) (cons x x)) $0))", "(member 2.0 $0)", "(memv 0 $0)", "(list-tail $0 1)", "(filter exact? $0)", "(foldr (lambda (x a) (+ x a)) 0 $0)", "(remove 1/3 $0)"]); E::node(Ty::Val, "lib-list", &op, vec![l]) }
            2 => { let a = self.lib_str(d); let b = self.lib_str(d); let c = self.lib_str(d); E::node(Ty::Val, "lib-list", "(sort (list $0 $1 $2) string-ci<?)", vec![a, b, c]) }
            3 | 4 | 5 => {
                let mk = *self.rng.pick(&["make-hash", "make-hasheqv", "make-hash", "make-hashalw", "make-hasheq"]);
                let mk = if mk == "make-hasheq" { "make-hash" } else { mk };
                let k1 = self.lib_any(d); let v1 = self.lib_any(d); let k2 = self.lib_any(d); let k3 = self.lib_any(d);
                E::node(Ty::Val, "lib-hash", &format!("(let ([{h} ({mk})]) (hash-set! {h} $0 $1) (hash-set! {h} $2 'two) (hash-update! {h} $0 (lambda (x) (list x)) 'none) (list (hash-ref {h} $3 'none) (hash-ref {h} $0 #f) (hash-count {h}) (begin (hash-remove! {h} $2) (hash-count {h}))))"), vec![k1, v1, k2, k3])
            }
            6 | 7 => {
                let mk = *self.rng.pick(&["(hash)", "(hasheqv)", "(hashalw)"]);
                let k1 = self.lib_any(d); let k2 = self.lib_any(d); let k3 = self.lib_any(d);
                E::node(Ty::Val, "lib-hash", &format!("(let* ([{h} (hash-set (hash-set {mk} $0 1) $1 2)] [r (hash-remove {h} $2)]) (list (hash-count {h}) (hash-count r) (hash-ref r $0 'none) (equal? {h} (hash-set (hash-set {mk} $1 2) $0 1)) (hash-has-key? r $1)))"), vec![k1, k2, k3])
            }
            8 => { let a = self.lib_any(d); let b = self.lib_any(d); E::node(Ty::Val, "lib-list", "(let ([v (vector $0 $1 $0)]) (vector-fill! v $1) (list (vector->list v) (vector->immutable-vector v) (equal? v (vector $1 $1 $1))))", vec![a, b]) }
            _ => { let a = self.lib_any(d); let b = self.lib_any(d); E::node(Ty::Val, "lib-list", "(list (equal? $0 $1) (equal? (list $0) (list $1)) (eqv? $0 $0))", vec![a, b]) }
        }
    }

    /// Any library value (also plain Val expressions).
    fn lib_any(&mut self, d: usize) -> E {
        if d == 0 {
            let p = *self.rng.pick(&[NUM_POOL, STR_POOL, CHAR_POOL, BYTES_POOL, VAL_POOL]);
            return self.lib_lit(p);
        }
        match self.rng.below(8) {
            0 | 1 => self.lib_num(d),
            2 | 3 => self.lib_str(d),
            4 => self.lib_char(d),
            5 => self.lib_lit(BYTES_POOL),
            6 => self.expr(Ty::Val, d - 1),
            _ => self.lib_collop(d - 1),
        }
    }

    /// A byte count / skip for port operations.
    fn port_n(&mut self, d: usize) -> E {
        match self.rng.below(8) {
            0..=3 => self.small_lit(0, 8),
            4 => E::atom(Ty::Int, self.rng.pick(&["4093", "4094", "4095", "4096", "4097", "5000", "100000"])),
            5 => self.small_lit(9, 40),
            _ => { let e = self.lib_int(d); E::node(Ty::Int, "", "(modulo $0 9)", vec![e]) }
        }
    }
    fn port_data(&mut self, d: usize) -> E {
        match self.rng.below(10) {
            0..=5 => self.lib_lit(PORT_DATA_POOL),
            6 => self.lib_lit(BYTES_POOL),
            7 => { let s = self.lib_str(d); E::node(Ty::Val, "", "(string->bytes/utf-8 $0)", vec![s]) }
            _ => { let a = self.lib_lit(PORT_DATA_POOL); let b = self.lib_lit(PORT_DATA_POOL); E::node(Ty::Val, "", "(bytes-append $0 $1)", vec![a, b]) }
        }
    }
    /// One operation on input port `p` (bound by the enclosing port_in).
    fn port_in_op(&mut self, p: &String, d: usize) -> E {
        let rd = "(with-handlers ([exn:fail:read? (lambda (e) 'read-error)]) ";
        let (tpl, kids): (String, Vec<E>) = match self.rng.below(33) {
            0 => (format!("(read-byte {p})"), vec![]),
            1 => (format!("(peek-byte {p} $0)"), vec![self.port_n(d)]),
            2 => (format!("(read-char {p})"), vec![]),
            3 => (format!("(peek-char {p} $0)"), vec![self.port_n(d)]),
            4 | 5 => (format!("(read-bytes $0 {p})"), vec![self.port_n(d)]),
            6 => (format!("(peek-bytes $0 $1 {p})"), vec![self.port_n(d), self.port_n(d)]),
            7 => (format!("(read-string $0 {p})"), vec![self.port_n(d)]),
            8 => (format!("(peek-string $0 $1 {p})"), vec![self.port_n(d), self.port_n(d)]),
            9 => { let m = *self.rng.pick(LINE_MODES); (format!("(read-line {p} {m})"), vec![]) }
            10 => { let m = *self.rng.pick(LINE_MODES); (format!("(read-bytes-line {p} {m})"), vec![]) }
            11 | 12 => {
                let op = *self.rng.pick(&["regexp-match", "regexp-match-positions", "regexp-try-match", "regexp-match-peek", "regexp-match-peek-positions", "regexp-match?"]);
                (format!("({op} $0 {p})"), vec![self.lib_lit(PORT_RX_POOL)])
            }
            13 => {
                let op = *self.rng.pick(&["regexp-match", "regexp-match-positions", "regexp-match-peek-positions"]);
                (format!("({op} $0 {p} $1)"), vec![self.lib_lit(PORT_RX_POOL), self.port_n(d)])
            }
            14 => (format!("{rd}(read {p}))"), vec![]),
            15 => (format!("{rd}(let ([s (read-syntax 'src {p})]) (if (eof-object? s) s (list (syntax->datum s) (syntax-line s) (syntax-column s) (syntax-position s) (syntax-span s)))))"), vec![]),
            16 | 17 => (format!("(file-position {p})"), vec![]),
            18 => (format!("(call-with-values (lambda () (port-next-location {p})) list)"), vec![]),
            19 => (format!("(let ([bf (make-bytes 6 46)]) (list (read-bytes! bf {p} 1 (min 6 (+ 1 $0))) bf))"), vec![self.port_n(d)]),
            20 => (format!("(let ([bf (make-bytes 6 46)]) (list (peek-bytes! bf $0 {p} 2) bf))"), vec![self.port_n(d)]),
            21 => (format!("(eof-object? (peek-byte {p}))"), vec![]),
            22 => (format!("(let ([r (read-bytes 100000 {p})]) (if (bytes? r) (list (bytes-length r) (subbytes r (max 0 (- (bytes-length r) 9)))) r))"), vec![]),
            23 => (format!("(let ([c (read-char {p})]) (list c (peek-char {p}) (read-char {p})))"), vec![]),
            // avail reads completed by blocking reads: deterministic content
            24 => (format!("(let* ([k (min 5000 $0)] [bf (make-bytes k 46)] [n ({av} bf {p})] [m (if (and (exact-integer? n) (< n k)) (read-bytes! bf {p} n k) 0)]) (if (or (eof-object? n) (and (eqv? n 0) (eof-object? m))) eof (subbytes bf 0 (+ n (if (exact-integer? m) m 0)))))", av = self.rng.pick(&["read-bytes-avail!", "read-bytes-avail!*"])), vec![self.port_n(d)]),
            25 => (format!("(let* ([k (min 5000 $0)] [s $1] [bf (make-bytes k 46)] [n ({av} bf s #f {p})] [m (if (and (exact-integer? n) (< n k)) (peek-bytes! bf (+ s n) {p} n k) 0)]) (if (or (eof-object? n) (and (eqv? n 0) (eof-object? m))) eof (subbytes bf 0 (+ n (if (exact-integer? m) m 0)))))", av = self.rng.pick(&["peek-bytes-avail!", "peek-bytes-avail!*"])), vec![self.port_n(d), self.port_n(d)]),
            // events (racket/port)
            26 => {
                // (racket/port name, template, kids: n = a count, s = a skip, r = a regexp)
                let (f, t, ks): (&str, &str, &str) = *self.rng.pick(&[
                    ("read-bytes-evt", "$0 P", "n"), ("peek-bytes-evt", "$0 $1 #f P", "ns"),
                    ("read-string-evt", "$0 P", "n"), ("read-char-evt", "P", ""), ("read-line-evt", "P 'any", ""),
                    ("read-bytes-line-evt", "P 'linefeed", ""), ("regexp-match-evt", "$0 P", "r"),
                    ("peek-string-evt", "$0 $1 #f P", "ns")]);
                let mut kids = vec![];
                for c in ks.chars() {
                    kids.push(if c == 'r' { self.lib_lit(PORT_RX_POOL) } else { self.port_n(d) });
                }
                (format!("(sync/timeout 5 ((dynamic-require 'racket/port '{f}) {}))", t.replace("P", p)), kids)
            }
            27 => (format!("(eq? (sync/timeout 5 {p}) {p})"), vec![]),
            28 => { let f = *self.rng.pick(&["port->bytes", "port->string", "port->lines", "port->bytes-lines"]); (format!("((dynamic-require 'racket/port '{f}) {p})"), vec![]) }
            29 => (format!("(let ([o (open-output-bytes)]) ((dynamic-require 'racket/port 'copy-port) {p} o) (get-output-bytes o))"), vec![]),
            30 => (format!("(begin (port-count-lines! {p}) 'counting)"), vec![]),
            31 => (format!("(let ([q ((dynamic-require 'racket/port 'make-limited-input-port) {p} $0 #f)]) (list (read-bytes 3 q) (read-char q) (file-position q)))"), vec![self.port_n(d)]),
            _ => (format!("(begin (close-input-port {p}) (port-closed? {p}))"), vec![]),
        };
        E::node(Ty::Val, "port-in", &tpl, kids).using(&[p])
    }
    /// An input port read by a few operations; their results as a list.
    fn port_in(&mut self, d: usize) -> E {
        let p = self.fresh("p");
        let (open, src) = if self.rng.chance(0.75) {
            ("open-input-bytes", self.port_data(d))
        } else {
            ("open-input-string", self.lib_str(d))
        };
        let count = if self.rng.chance(0.4) { format!("(port-count-lines! {p}) ") } else { String::new() };
        let n = 1 + self.rng.below(6);
        let mut kids = vec![src];
        for _ in 0..n {
            let op = self.port_in_op(&p, d);
            kids.push(op);
        }
        let ops = (1..=n).map(|k| format!("${k}")).collect::<Vec<_>>().join(" ");
        E::node(Ty::Val, "port-in", &format!("(let ([{p} ({open} $0)]) {count}(list {ops}))"), kids).binding(&[&p])
    }
    /// One operation on output port `o`; `seek` allows setting the position.
    fn port_out_op(&mut self, o: &String, get: &str, seek: bool, d: usize) -> E {
        let (tpl, kids): (String, Vec<E>) = match self.rng.below(if seek { 16 } else { 14 }) {
            0 | 1 => (format!("(write-bytes $0 {o})"), vec![self.port_data(d)]),
            2 => (format!("(let ([bs $0]) (write-bytes bs {o} (min $1 (bytes-length bs))))"), vec![self.port_data(d), self.port_n(d)]),
            3 | 4 => (format!("(write-string $0 {o})"), vec![self.lib_str(d)]),
            5 => (format!("(write-char $0 {o})"), vec![self.lib_char(d)]),
            6 => (format!("(write-byte (modulo $0 256) {o})"), vec![self.lib_int(d)]),
            7 => { let op = *self.rng.pick(&["display", "write", "print"]); (format!("({op} $0 {o})"), vec![self.lib_any(d)]) }
            8 => (format!("(fprintf {o} \"~a|~s~n\" $0 $1)"), vec![self.lib_any(d), self.lib_any(d)]),
            9 => (format!("(begin (newline {o}) (flush-output {o}) 'nl)"), vec![]),
            10 => (format!("({get} {o})"), vec![]),
            11 => (format!("(file-position {o})"), vec![]),
            12 => (format!("(call-with-values (lambda () (port-next-location {o})) list)"), vec![]),
            13 => (format!("(write-bytes (make-bytes $0 98) {o})"), vec![self.port_n(d)]),
            _ => (format!("(begin (file-position {o} $0) (write-bytes $1 {o}))"), vec![self.port_n(d), self.port_data(d)]),
        };
        E::node(Ty::Val, "port-out", &tpl, kids).using(&[o])
    }
    fn port_out(&mut self, d: usize) -> E {
        let o = self.fresh("o");
        let (open, get) = if self.rng.chance(0.7) { ("open-output-bytes", "get-output-bytes") } else { ("open-output-string", "get-output-string") };
        let seek = open == "open-output-bytes" && self.rng.chance(0.2);
        let count = if self.rng.chance(0.4) { format!("(port-count-lines! {o}) ") } else { String::new() };
        let n = 1 + self.rng.below(6);
        let mut kids = vec![];
        for _ in 0..n {
            let op = self.port_out_op(&o, get, seek, d);
            kids.push(op);
        }
        let ops = (0..n).map(|k| format!("${k}")).collect::<Vec<_>>().join(" ");
        let tail = if self.rng.chance(0.5) { format!(" (file-position {o})") } else { String::new() };
        E::node(Ty::Val, "port-out", &format!("(let ([{o} ({open})]) {count}(list {ops} ({get} {o}){tail}))"), kids).binding(&[&o])
    }

    pub fn lib_op(&mut self, d: usize) -> E {
        let d = d.max(1);
        match self.rng.below(12) {
            0..=3 => self.lib_numop(d - 1),
            4..=7 => self.lib_strop(d - 1),
            10 => self.port_in(d - 1),
            11 => self.port_out(d - 1),
            _ => self.lib_collop(d - 1),
        }
    }

    /// A library result used as an Int, Fl or Bool.
    pub fn lib_typed(&mut self, ty: Ty, d: usize) -> E {
        let v = self.lib_op(d);
        let t = self.fresh("t");
        match ty {
            Ty::Int => E::node(Ty::Int, "lib-typed", &format!("(let ([{t} $0]) (cond [(exact-integer? {t}) {t}] [(and (rational? {t}) (exact? {t})) (numerator {t})] [(string? {t}) (string-length {t})] [(bytes? {t}) (bytes-length {t})] [(char? {t}) (char->integer {t})] [(list? {t}) (length {t})] [(boolean? {t}) (if {t} 1 0)] [else -1]))"), vec![v]),
            Ty::Fl => E::node(Ty::Fl, "lib-typed", &format!("(let ([{t} $0]) (if (real? {t}) (real->double-flonum {t}) (if (number? {t}) (real->double-flonum (real-part {t})) 0.5)))"), vec![v]),
            _ => E::node(Ty::Bool, "lib-typed", &format!("(let ([{t} $0]) (and {t} (not (null? {t})) #t))"), vec![v]),
        }
    }
}
