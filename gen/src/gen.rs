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
        match ty {
            Ty::Int => self.int_op(d),
            Ty::Fl => self.fl_op(d),
            Ty::Bool => self.bool_op(d),
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
                        E::node(Ty::Int, "flbit-field", &format!("(flbit-field $0 {s} {e})"), vec![f])
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
            0..=29 => {
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
                let vt = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Bool, Ty::Int]);
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
                let sty = *self.rng.pick(&[Ty::Int, Ty::Fl]);
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
                E::node(ty, "handlers", "(with-handlers ([exn:fail? (lambda (e) $1)]) $0)", vec![a, b])
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
                let at = *self.rng.pick(&[Ty::Int, Ty::Fl, Ty::Bool]);
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

    fn rand_ty(&mut self) -> Ty {
        *self.rng.pick(&[Ty::Int, Ty::Int, Ty::Fl, Ty::Fl, Ty::Bool])
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
        ("control", tags.iter().filter(|t| ["escape", "wcm", "dynamic-wind", "parameterize", "handlers"].contains(t)).count() as f64),
    ]
}

#[ephyra::generator(valid_program, metrics = program_metrics)]
pub fn programs() -> ProgramGen {
    ProgramGen
}
