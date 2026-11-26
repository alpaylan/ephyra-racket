//! numref programs (steering round 14): lists of typed numeric expressions
//! that racket/numref.py evaluates independently (Python int / Fraction /
//! IEEE double).  Each line is `(o i (lambda () e))`; with `fun` the
//! literal leaves of `e` become parameters of `(define (fnI p...) e)`,
//! called with the literals (machine code with unknown arguments).

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ty { X, I, Q, F, B, S }

#[derive(Clone, Debug)]
pub enum K { Lit, Var, Call, Q, Loop }

#[derive(Clone, Debug)]
pub struct Node { pub k: K, pub text: String, pub kids: Vec<Node>, pub ty: Ty }

#[derive(Clone, Debug)]
pub struct Line { pub e: Node, pub fun: bool, pub pseed: u64, pub chez: bool }

/// Racket name -> Chez Scheme name for lines compiled directly by Chez
/// (`vm-eval`); names not listed are the same in both
pub const CHEZ_MAP: &[(&str, &str)] = &[("fxlshift", "fxsll"), ("fxrshift", "fxsra"), ("fxrshift/logical", "fxsrl"),
    ("fxlshift/wraparound", "fxsll/wraparound"), ("fl->fx", "flonum->fixnum"), ("fx->fl", "fixnum->flonum"),
    ("->fl", "inexact"), ("fl->exact-integer", "exact"), ("arithmetic-shift", "bitwise-arithmetic-shift"),
    ("integer-sqrt", "isqrt")];
const NOT_CHEZ: &[&str] = &["integer->integer-bytes", "integer-bytes->integer", "real->floating-point-bytes",
    "floating-point-bytes->real", "number->string", "string->number"];

pub fn chez_ok(n: &Node) -> bool {
    !(matches!(n.k, K::Call) && NOT_CHEZ.contains(&n.text.as_str())) && n.kids.iter().all(chez_ok)
}

pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 { self.next() % n }
    pub fn p(&mut self, pr: f64) -> bool { (self.next() >> 11) as f64 / (1u64 << 53) as f64 * 1.0 < pr }
    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T { &xs[self.below(xs.len() as u64) as usize] }
}

fn lit(text: String, ty: Ty) -> Node { Node { k: K::Lit, text, kids: vec![], ty } }
fn call(h: &str, ty: Ty, kids: Vec<Node>) -> Node { Node { k: K::Call, text: h.into(), kids, ty } }

const FX_POOL: &[&str] = &["0", "1", "-1", "2", "3", "7", "-7", "10", "255", "256", "65535", "65536",
    "2147483647", "-2147483648", "4294967295", "4294967296", "9007199254740992", "9007199254740993",
    "576460752303423488", "1152921504606846975", "-1152921504606846976", "-1152921504606846975",
    "1000000000", "-3", "5", "63", "64"];
const BIG_POOL: &[&str] = &["1152921504606846976", "-1152921504606846977", "2305843009213693952",
    "4611686018427387904", "9223372036854775807", "9223372036854775808", "-9223372036854775808",
    "18446744073709551615", "18446744073709551616", "-18446744073709551616", "100000000000000000000",
    "340282366920938463463374607431768211457", "-1267650600228229401496703205376",
    "147808829414345923316083210206383297601",
    // 2^1023, 2^1024, 2^1024-2^970 (flonum overflow threshold), 2^1024-2^971
    "89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608",
    "179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216",
    "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497792",
    "179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368",
    "9007199254740993", "-9007199254740995", "18014398509481985", "36028797018963971"];
const Q_POOL: &[&str] = &["1/3", "-1/2", "5/2", "-5/2", "7/2", "1/10", "-7/3", "2/3", "3/4",
    "9007199254740993/2", "1/9007199254740992", "18014398509481987/2",
    "1/340282366920938463463374607431768211456",
    "3/340282366920938463463374607431768211457"];
const FL_POOL: &[&str] = &["0.0", "-0.0", "1.0", "-1.0", "0.5", "-0.5", "1.5", "2.5", "-2.5", "3.5", "0.1",
    "1e300", "-1e300", "1.7976931348623157e308", "5e-324", "-5e-324", "2.2250738585072014e-308",
    "2.225073858507201e-308", "+inf.0", "-inf.0", "+nan.0", "9007199254740992.0", "4503599627370495.5",
    "4503599627370497.0", "0.49999999999999994", "1e22", "1e23", "3.4028234663852886e38",
    "3.4028235677973366e38", "1.401298464324817e-45", "7.006492321624085e-46", "1.1754943508222875e-38",
    "1.0000000596046448", "1.0000001788139343", "-123.456", "6.02e23", "1152921504606846976.0",
    "-1152921504606846976.0", "1152921504606846975.0", "4294967296.5", "2.0", "1e-310"];

fn fl_text(x: f64) -> String {
    if x.is_nan() { return "+nan.0".into(); }
    if x.is_infinite() { return if x > 0.0 { "+inf.0".into() } else { "-inf.0".into() }; }
    let s = format!("{x:?}");
    if s.contains('.') || s.contains('e') { s } else { format!("{s}.0") }
}

fn big_text(r: &mut Rng, bits: u32) -> String {
    // decimal of a random `bits`-bit number, via repeated u64 limbs
    let mut limbs: Vec<u64> = (0..(bits as usize + 63) / 64).map(|_| r.next()).collect();
    let top = bits % 64;
    if top != 0 { let l = limbs.len(); limbs[l - 1] &= (1u64 << top) - 1; }
    let mut digits = Vec::new();
    while limbs.iter().any(|&l| l != 0) {
        let mut rem: u128 = 0;
        for l in limbs.iter_mut().rev() {
            let cur = (rem << 64) | *l as u128;
            *l = (cur / 10) as u64;
            rem = cur % 10;
        }
        digits.push(b'0' + rem as u8);
    }
    if digits.is_empty() { digits.push(b'0'); }
    digits.reverse();
    let s = String::from_utf8(digits).unwrap();
    if r.p(0.4) { format!("-{s}") } else { s }
}

/// decimal string of m * 2^k
fn dec_shl(m: u64, k: u32) -> String {
    let mut d: Vec<u32> = m.to_string().bytes().rev().map(|b| (b - b'0') as u32).collect();
    for _ in 0..k {
        let mut c = 0;
        for x in d.iter_mut() { let v = *x * 2 + c; *x = v % 10; c = v / 10; }
        if c > 0 { d.push(c); }
    }
    d.iter().rev().map(|x| char::from(b'0' + *x as u8)).collect()
}

/// exact values at or next to a binary64 rounding tie: an odd 54-bit (or
/// 25-bit, for flsingle-like ties) mantissa m, maybe +-1, times 2^e for
/// e in the normal, subnormal and overflow ranges
fn tie_text(r: &mut Rng, int: bool) -> String {
    let bits = if r.p(0.8) { 54 } else { 55 };
    let mut m = (1u64 << (bits - 1)) | (r.next() & ((1u64 << (bits - 1)) - 1)) | 1;
    if r.p(0.3) { m = m.wrapping_add(if r.p(0.5) { 1 } else { u64::MAX }); }
    let neg = if r.p(0.4) { "-" } else { "" };
    if int {
        let k = *r.pick(&[0u32, 1, 2, 7, 10, 60, 200, 969, 970, 971]);
        format!("{neg}{}", dec_shl(m, k))
    } else {
        let k = *r.pick(&[1u32, 3, 54, 60, 200, 1022, 1074, 1075, 1076, 1080, 1100, 1127, 1128, 1129]);
        format!("{neg}{m}/{}", dec_shl(1, k))
    }
}

pub struct NumGen { pub r: Rng, qprob: f64, n: usize, scope: Vec<(String, Ty)> }

impl NumGen {
    pub fn new(seed: u64) -> NumGen { NumGen { r: Rng(seed), qprob: 0.0, n: 0, scope: vec![] } }

    fn fx_lit(&mut self) -> String {
        match self.r.below(4) {
            0 => format!("{}", (self.r.next() as i64) >> 3),
            1 => format!("{}", (self.r.below(2001) as i64) - 1000),
            _ => self.r.pick(FX_POOL).to_string(),
        }
    }
    fn leaf(&mut self, ty: Ty) -> Node {
        // loop variables
        if !self.scope.is_empty() && self.r.p(0.35) {
            let cands: Vec<(String, Ty)> = self.scope.iter().filter(|(_, t)| *t == ty || (ty == Ty::I && *t == Ty::X) || (ty == Ty::Q && (*t == Ty::X || *t == Ty::I))).cloned().collect();
            if !cands.is_empty() {
                let (v, _) = self.r.pick(&cands).clone();
                return Node { k: K::Var, text: v, kids: vec![], ty };
            }
        }
        let t = match ty {
            Ty::X => self.fx_lit(),
            Ty::I => match self.r.below(7) {
                6 => tie_text(&mut self.r, true),
                0 | 1 => self.fx_lit(),
                2 => { let b = 61 + self.r.below(1100) as u32; big_text(&mut self.r, b) }
                3 => { let b = 62 + self.r.below(130) as u32; big_text(&mut self.r, b) }
                _ => self.r.pick(BIG_POOL).to_string(),
            },
            Ty::Q => match self.r.below(6) {
                5 => tie_text(&mut self.r, false),
                0 => self.r.pick(Q_POOL).to_string(),
                1 => { let b1 = 1 + self.r.below(200) as u32; let b2 = 2 + self.r.below(1100) as u32;
                       let n = big_text(&mut self.r, b1); let mut d = big_text(&mut self.r, b2);
                       d = d.trim_start_matches('-').to_string(); if d == "0" || d == "1" { d = "3".into(); }
                       // the reader normalizes; gcd is fine
                       format!("{n}/{d}") }
                2 => return self.leaf(Ty::I),
                _ => { let n = self.fx_lit(); format!("{n}/{}", 2 + self.r.below(20)) }
            },
            Ty::F => match self.r.below(5) {
                0 => fl_text(f64::from_bits(self.r.next())),
                1 => fl_text((self.r.below(4001) as f64 - 2000.0) / 8.0),
                _ => self.r.pick(FL_POOL).to_string(),
            },
            Ty::B => if self.r.p(0.5) { "#t".into() } else { "#f".into() },
            Ty::S => return call("number->string", Ty::S, vec![self.gen(Ty::Q, 1), lit(self.r.pick(&["2", "8", "10", "16"]).to_string(), Ty::X)]),
        };
        let t = if t.ends_with("/1") { t.trim_end_matches("/1").to_string() } else { t };
        let n = lit(t, ty);
        if self.r.p(self.qprob) { Node { k: K::Q, text: "q".into(), kids: vec![n], ty } } else { n }
    }
    /// a literal (never a loop variable: expt of a loop accumulator grows without bound)
    fn leaf_lit(&mut self, ty: Ty) -> Node {
        let sc = std::mem::take(&mut self.scope);
        let n = self.leaf(ty);
        self.scope = sc;
        n
    }
    fn small(&mut self, lo: i64, hi: i64) -> Node { lit(format!("{}", lo + self.r.below((hi - lo + 1) as u64) as i64), Ty::X) }

    pub fn gen(&mut self, ty: Ty, d: u32) -> Node {
        if d == 0 || self.r.p(0.22) { return self.leaf(ty); }
        let d1 = d - 1;
        macro_rules! g { ($t:expr) => { self.gen($t, d1) } }
        if self.r.p(0.06) && ty != Ty::B && ty != Ty::S {
            return call("if", ty, vec![g!(Ty::B), g!(ty), g!(ty)]);
        }
        match ty {
            Ty::X => match self.r.below(22) {
                0 => { let h = *self.r.pick(&["fx+", "fx-", "fx*"]); call(h, ty, vec![g!(Ty::X), g!(Ty::X)]) }
                1 | 2 => { let h = *self.r.pick(&["fx+/wraparound", "fx-/wraparound", "fx*/wraparound"]); call(h, ty, vec![g!(Ty::X), g!(Ty::X)]) }
                3 => { let h = *self.r.pick(&["fxquotient", "fxremainder", "fxmodulo"]); call(h, ty, vec![g!(Ty::X), g!(Ty::X)]) }
                4 => { let h = *self.r.pick(&["fxand", "fxior", "fxxor"]); let n = 2 + self.r.below(2); call(h, ty, (0..n).map(|_| self.gen(Ty::X, d1)).collect()) }
                5 => call(*self.r.pick(&["fxnot", "fxabs"]), ty, vec![g!(Ty::X)]),
                6 => { let s = self.small(0, 60); call("fxlshift", ty, vec![g!(Ty::X), s]) }
                7 => { let s = self.small(0, 60); call("fxrshift", ty, vec![g!(Ty::X), s]) }
                8 => { let s = self.small(0, 61); call("fxrshift/logical", ty, vec![g!(Ty::X), s]) }
                9 => { let s = self.small(0, 61); call("fxlshift/wraparound", ty, vec![g!(Ty::X), s]) }
                10 | 11 => { let h = *self.r.pick(&["fxpopcount", "fxpopcount32", "fxpopcount16"]);
                             let a = if self.r.p(0.7) { let m = lit(self.r.pick(&["65535", "4294967295", "1152921504606846975", "255"]).to_string(), Ty::X); call("fxand", ty, vec![g!(Ty::X), m]) } else { g!(Ty::X) };
                             call(h, ty, vec![a]) }
                12 => call(*self.r.pick(&["fxmin", "fxmax"]), ty, vec![g!(Ty::X), g!(Ty::X)]),
                13 | 14 => call("fl->fx", ty, vec![g!(Ty::F)]),
                15 => call(*self.r.pick(&["integer-length", "bitwise-first-bit-set"]), ty, vec![g!(Ty::I)]),
                16 => self.lp(Ty::X, d1),
                _ => self.leaf(ty),
            },
            Ty::I => match self.r.below(22) {
                0 | 1 => { let h = *self.r.pick(&["+", "-", "*"]); call(h, ty, vec![g!(Ty::I), g!(Ty::I)]) }
                2 => { let h = *self.r.pick(&["quotient", "remainder", "modulo"]); call(h, ty, vec![g!(Ty::I), g!(Ty::I)]) }
                3 => call(*self.r.pick(&["gcd", "lcm"]), ty, vec![g!(Ty::I), g!(Ty::I)]),
                4 => call(*self.r.pick(&["abs", "-", "add1", "sub1", "bitwise-not"]), ty, vec![g!(Ty::I)]),
                5 => { let b = self.leaf_lit(Ty::I); let e = self.small(0, 40); call("expt", ty, vec![b, e]) }
                6 => { let s = self.small(-300, 300); call("arithmetic-shift", ty, vec![g!(Ty::I), s]) }
                7 => { let h = *self.r.pick(&["bitwise-and", "bitwise-ior", "bitwise-xor"]); let n = 2 + self.r.below(2); call(h, ty, (0..n).map(|_| self.gen(Ty::I, d1)).collect()) }
                8 => { let s = self.r.below(130) as i64; let e = s + self.r.below(130) as i64;
                       call("bitwise-bit-field", ty, vec![g!(Ty::I), lit(s.to_string(), Ty::X), lit(e.to_string(), Ty::X)]) }
                9 => call("integer-sqrt", ty, vec![call("abs", ty, vec![g!(Ty::I)])]),
                10 => call(*self.r.pick(&["numerator", "denominator"]), ty, vec![g!(Ty::Q)]),
                11 | 12 => call(*self.r.pick(&["floor", "ceiling", "round", "truncate"]), ty, vec![g!(Ty::Q)]),
                13 => call("fl->exact-integer", ty, vec![call(*self.r.pick(&["flround", "fltruncate", "flfloor"]), Ty::F, vec![g!(Ty::F)])]),
                14 => call(*self.r.pick(&["max", "min"]), ty, vec![g!(Ty::I), g!(Ty::I)]),
                15 => { let s = self.small(0, 200); call("bitwise-bit-field", ty, vec![call("flbit-field", ty, vec![g!(Ty::F), lit("0".into(), Ty::X), lit("64".into(), Ty::X)]), lit("0".into(), Ty::X), s]) }
                16 if self.scope.is_empty() => self.lp(Ty::I, d1),
                17 => g!(Ty::X),
                18 | 19 => { let n = *self.r.pick(&["1", "2", "4", "8"]);
                        let b = |r: &mut Rng| lit(if r.p(0.5) { "#t".into() } else { "#f".into() }, Ty::B);
                        let (s1, e1, s2, e2) = (b(&mut self.r), b(&mut self.r), b(&mut self.r), b(&mut self.r));
                        let e2 = if self.r.p(0.7) { e1.clone() } else { e2 };
                        call("integer-bytes->integer", ty, vec![call("integer->integer-bytes", ty, vec![g!(Ty::I), lit(n.into(), Ty::X), s1, e1]), s2, e2]) }
                _ => self.leaf(ty),
            },
            Ty::Q => match self.r.below(12) {
                0..=2 => { let h = *self.r.pick(&["+", "-", "*", "/"]); call(h, ty, vec![g!(Ty::Q), g!(Ty::Q)]) }
                3 | 4 => call("inexact->exact", ty, vec![g!(Ty::F)]),
                5 => call(*self.r.pick(&["abs", "-", "add1"]), ty, vec![g!(Ty::Q)]),
                6 => call(*self.r.pick(&["max", "min"]), ty, vec![g!(Ty::Q), g!(Ty::Q)]),
                7 => { let r = *self.r.pick(&["2", "8", "10", "16"]);
                       call("string->number", ty, vec![call("number->string", Ty::S, vec![g!(Ty::Q), lit(r.into(), Ty::X)]), lit(r.into(), Ty::X)]) }
                8 => { let b = self.leaf_lit(Ty::Q); let e = self.small(-6, 12); call("expt", ty, vec![b, e]) }
                9 => g!(Ty::I),
                10 => { let a = g!(Ty::Q); call("sqrt", ty, vec![call("*", ty, vec![a.clone(), a])]) }
                _ => self.leaf(ty),
            },
            Ty::F => match self.r.below(26) {
                0..=3 => { let h = *self.r.pick(&["fl+", "fl-", "fl*", "fl/"]); let n = 2 + (self.r.p(0.2) as u64); call(h, ty, (0..n).map(|_| self.gen(Ty::F, d1)).collect()) }
                4 => call(*self.r.pick(&["flabs", "flsqrt", "flsingle", "-", "abs"]), ty, vec![g!(Ty::F)]),
                5 | 6 => call(*self.r.pick(&["flround", "flfloor", "flceiling", "fltruncate", "round", "floor", "ceiling", "truncate"]), ty, vec![g!(Ty::F)]),
                7 | 8 => { let h = *self.r.pick(&["flmin", "flmax"]); let n = 2 + (self.r.p(0.3) as u64); call(h, ty, (0..n).map(|_| self.gen(Ty::F, d1)).collect()) }
                9 => { let h = *self.r.pick(&["+", "-", "*", "/"]); call(h, ty, vec![g!(Ty::F), g!(Ty::F)]) }
                10 | 11 => call("exact->inexact", ty, vec![g!(Ty::Q)]),
                12 => call("fx->fl", ty, vec![g!(Ty::X)]),
                13 => call("->fl", ty, vec![g!(Ty::I)]),
                14 => call("flsingle", ty, vec![call(*self.r.pick(&["fl+", "fl-", "fl*", "fl/"]), ty, vec![call("flsingle", ty, vec![g!(Ty::F)]), call("flsingle", ty, vec![g!(Ty::F)])])]),
                15 | 16 => self.lp(Ty::F, d1),
                18 => call("flfma", ty, vec![g!(Ty::F), g!(Ty::F), g!(Ty::F)]),
                19 => call("flnextafter", ty, vec![g!(Ty::F), g!(Ty::F)]),
                17 => { let n = *self.r.pick(&["4", "8", "8"]);
                        let e1 = self.r.p(0.5); let e2 = if self.r.p(0.8) { e1 } else { !e1 };
                        let bl = |x: bool| lit(if x { "#t".into() } else { "#f".into() }, Ty::B);
                        call("floating-point-bytes->real", ty, vec![call("real->floating-point-bytes", ty, vec![g!(Ty::F), lit(n.into(), Ty::X), bl(e1)]), bl(e2)]) }
                _ => self.leaf(ty),
            },
            Ty::B => match self.r.below(12) {
                0..=2 => { let h = *self.r.pick(&["=", "<", ">", "<=", ">="]);
                           let n = 2 + (self.r.p(0.2) as u64);
                           let kids = (0..n).map(|_| { let t = *self.r.pick(&[Ty::I, Ty::Q, Ty::F, Ty::X]); self.gen(t, d1) }).collect();
                           call(h, ty, kids) }
                3 | 4 => call(*self.r.pick(&["fl=", "fl<", "fl>", "fl<=", "fl>="]), ty, vec![g!(Ty::F), g!(Ty::F)]),
                5 => call(*self.r.pick(&["fx=", "fx<", "fx<="]), ty, vec![g!(Ty::X), g!(Ty::X)]),
                6 => call(*self.r.pick(&["even?", "odd?"]), ty, vec![g!(Ty::I)]),
                7 => { let t = *self.r.pick(&[Ty::I, Ty::Q, Ty::F]); call(*self.r.pick(&["zero?", "positive?", "negative?"]), ty, vec![self.gen(t, d1)]) }
                8 => { let k = self.small(0, 200); call("bitwise-bit-set?", ty, vec![g!(Ty::I), k]) }
                9 => { let a = g!(Ty::Q); let r = *self.r.pick(&["2", "8", "16"]);
                       // write/read round trip of an exact number in a radix
                       call("=", ty, vec![call("string->number", Ty::Q, vec![call("number->string", Ty::S, vec![a.clone(), lit(r.into(), Ty::X)]), lit(r.into(), Ty::X)]), a]) }
                10 => { let a = g!(Ty::F); call("=", ty, vec![call("exact->inexact", Ty::F, vec![call("inexact->exact", Ty::Q, vec![a.clone()])]), a]) }
                _ => call("not", ty, vec![g!(Ty::B)]),
            },
            Ty::S => self.leaf(Ty::S),
        }
    }

    /// bounded named-let accumulation loop: unboxed flonum / fixnum locals in machine code
    fn lp(&mut self, ty: Ty, d: u32) -> Node {
        self.n += 1;
        let (lname, iv, acc) = (format!("loop{}", self.n), format!("i{}", self.n), format!("acc{}", self.n));
        let init = self.gen(ty, d.min(1));
        self.scope.push((iv.clone(), Ty::X));
        self.scope.push((acc.clone(), ty));
        let step = self.gen(ty, d.max(1));
        self.scope.pop(); self.scope.pop();
        let k = 1 + self.r.below(6);
        Node { k: K::Loop, text: format!("{lname} {iv} {acc} {k}"), kids: vec![init, step], ty }
    }

    pub fn program(&mut self) -> Vec<Line> {
        let n = 16 + self.r.below(16);
        (0..n).map(|_| {
            self.qprob = *self.r.pick(&[0.0, 0.0, 0.3, 0.7, 1.0]);
            let ty = *self.r.pick(&[Ty::X, Ty::I, Ty::I, Ty::Q, Ty::F, Ty::F, Ty::F, Ty::B, Ty::B, Ty::S]);
            let d = 1 + self.r.below(4) as u32;
            let mut e = self.gen(ty, d);
            for _ in 0..4 { if matches!(e.k, K::Call | K::Loop) { break; } e = self.gen(ty, d); }
            let chez = chez_ok(&e) && self.r.p(0.25);
            Line { e, fun: self.r.p(0.35), pseed: self.r.next(), chez }
        }).collect()
    }
}

fn render(n: &Node, o: &mut String, params: &mut Option<(Vec<String>, Rng, usize)>) { render_c(n, o, params, false) }

fn render_c(n: &Node, o: &mut String, params: &mut Option<(Vec<String>, Rng, usize)>, chez: bool) {
    match n.k {
        K::Lit | K::Q => {
            if let Some((args, r, _)) = params.as_mut() {
                if r.p(0.6) {
                    let mut t = String::new();
                    render(n, &mut t, &mut None);
                    args.push(t);
                    o.push_str(&format!("p{}", args.len() - 1));
                    return;
                }
            }
            if let K::Q = n.k { o.push_str(if chez { "(numref-q " } else { "(q " }); render_c(&n.kids[0], o, params, chez); o.push(')'); }
            else { o.push_str(&n.text); }
        }
        K::Var => o.push_str(&n.text),
        K::Call => {
            o.push('(');
            let h = if chez { CHEZ_MAP.iter().find(|(r, _)| *r == n.text).map(|(_, c)| *c).unwrap_or(&n.text) } else { &n.text };
            o.push_str(h);
            for k in &n.kids { o.push(' '); render_c(k, o, params, chez); }
            o.push(')');
        }
        K::Loop => {
            let f: Vec<&str> = n.text.split(' ').collect();
            o.push_str(&format!("(let {} ([{} 0] [{} ", f[0], f[1], f[2]));
            render_c(&n.kids[0], o, params, chez);
            o.push_str(&format!("]) (if (fx< {} {}) ({} (fx+ {} 1) ", f[1], f[3], f[0], f[1]));
            render_c(&n.kids[1], o, params, chez);
            o.push_str(&format!(") {}))", f[2]));
        }
    }
}

pub const PRELUDE: &str = r##"(module m racket/base
  (require racket/flonum racket/fixnum ffi/unsafe/vm)
  (define q (lambda (x) x))
  (vm-eval '(define numref-q (lambda (x) x)))
  (define flfma (vm-eval '(lambda (a b c) (flfma a b c))))
  (define flnextafter (vm-primitive 'flnextafter))
  (set! q (lambda (x) x))
  (define (ab s)
    (let ([n (string-length s)])
      (if (> n 120) (string-append (substring s 0 50) "~" (number->string n) "~" (substring s (- n 50) n)) s)))
  (define (enc v) (ab (enc1 v)))
  (define (enc1 v)
    (cond [(boolean? v) (if v "#t" "#f")]
          [(flonum? v)
           (cond [(not (= v v)) "nan"] [(= v +inf.0) "+inf"] [(= v -inf.0) "-inf"]
                 [(eqv? v -0.0) "-0"]
                 [else (string-append "f" (number->string (inexact->exact v)))])]
          [(and (rational? v) (exact? v)) (string-append "e" (number->string v))]
          [(string? v) (string-append "s" v)]
          [else (format "?~s" v)]))
  (define (o i th)
    (let ([r (with-handlers ([exn:fail? (lambda (e) "err")]) (enc (th)))])
      (write-string (string-append (number->string i) " " r "\n"))
      (void)))
"##;

pub fn render_line(i: usize, l: &Line) -> String {
    let mut o = String::new();
    if l.fun {
        let mut ps = Some((Vec::new(), Rng(l.pseed), 0usize));
        let mut body = String::new();
        render_c(&l.e, &mut body, &mut ps, l.chez);
        let (args, _, _) = ps.unwrap();
        let pl: Vec<String> = (0..args.len()).map(|k| format!("p{k}")).collect();
        let sp = if args.is_empty() { "" } else { " " };
        if l.chez {
            o.push_str(&format!("  (o {i} (let ([fc (vm-eval '(lambda ({}) {body}))]) (lambda () (fc{sp}{}))))\n", pl.join(" "), args.join(" ")));
        } else {
            o.push_str(&format!("  (define (fn{i} {}) {body})\n", pl.join(" ")));
            o.push_str(&format!("  (o {i} (lambda () (fn{i}{sp}{})))\n", args.join(" ")));
        }
    } else {
        let mut e = String::new();
        render_c(&l.e, &mut e, &mut None, l.chez);
        if l.chez {
            o.push_str(&format!("  (o {i} (vm-eval '(lambda () {e})))\n"));
        } else {
            o.push_str(&format!("  (o {i} (lambda () {e}))\n"));
        }
    }
    o
}

/// lines with their original indices (a shrunk program keeps the index)
pub fn render_numprog(lines: &[(usize, Line)]) -> String {
    let mut s = String::from(PRELUDE);
    for (i, l) in lines { s.push_str(&render_line(*i, l)); }
    s.push_str(")\n");
    s
}

/// one-step simplifications of a line (for shrinking a failing line)
pub fn shrink_candidates(l: &Line) -> Vec<Line> {
    let mut out = Vec::new();
    if l.fun { out.push(Line { fun: false, ..l.clone() }); }
    if l.chez { out.push(Line { chez: false, ..l.clone() }); }
    let mut nodes = Vec::new();
    collect(&l.e, &mut vec![], &mut nodes);
    for (path, rep) in nodes {
        let mut e = l.e.clone();
        let mut cur = &mut e;
        for &k in &path { cur = &mut cur.kids[k]; }
        *cur = rep;
        out.push(Line { e, ..l.clone() });
    }
    out
}

fn collect(n: &Node, path: &mut Vec<usize>, out: &mut Vec<(Vec<usize>, Node)>) {
    match n.k {
        K::Q => out.push((path.clone(), n.kids[0].clone())),
        K::Loop => out.push((path.clone(), n.kids[0].clone())),
        K::Call => for k in &n.kids {
            if k.ty == n.ty || (n.ty == Ty::Q && matches!(k.ty, Ty::I | Ty::X)) || (n.ty == Ty::I && k.ty == Ty::X) {
                if !matches!(k.k, K::Lit) || matches!(n.text.as_str(), "if" | "q") || true {
                    out.push((path.clone(), k.clone()));
                }
            }
        },
        _ => {}
    }
    for (i, k) in n.kids.iter().enumerate() {
        path.push(i);
        collect(k, path, out);
        path.pop();
    }
}
