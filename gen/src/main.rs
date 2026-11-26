//! rktgen: differential search over generated Racket modules.
//!
//!   rktgen run <build-dir> <seed> <seconds> <out-dir>
//!   rktgen sample <seed> [n]        print generated programs
//!
//! Oracles (README.md):
//!   diff  : the same module compiled to machine code (default) and run by
//!           the CS interpreter (PLT_CS_INTERP=1) must give the same result
//!           line (output, error kind, first line of error message).
//!   crash : process death, internal-error messages, or a machine-code-only
//!           timeout (the interpreter finished, so this is a compile hang).

use rktgen::gen;
use rktgen::num;

use ephyra::{Config, Run, TestResult};
use gen::{render_program, Program, ProgramGen, E};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{channel, Receiver, RecvTimeoutError};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

const CASE_TIMEOUT_S: u64 = 10;

#[derive(Clone, Debug, PartialEq)]
enum Res {
    Line(String),
    Died(String),
    Hung,
}

struct Server {
    child: Child,
    stdin: ChildStdin,
    rx: Receiver<String>,
    stderr: Arc<Mutex<String>>,
}

fn spawn_server(racket: &Path, runner: &Path, interp: bool) -> Server {
    spawn_server_jit(racket, runner, interp, false)
}

/// `jitify`: PLT_CS_COMPILE_LIMIT=10, so every module counts as a "large
/// linklet": schemify's jitify mode, only interior functions compiled to
/// machine code, the outer body interpreted (linklet.sls).
fn spawn_server_jit(racket: &Path, runner: &Path, interp: bool, jitify: bool) -> Server {
    let mut cmd = Command::new(racket);
    cmd.arg(runner).arg("server");
    cmd.env("RKT_CASE_TIMEOUT", CASE_TIMEOUT_S.to_string());
    if interp {
        cmd.env("PLT_CS_INTERP", "1");
    } else {
        cmd.env_remove("PLT_CS_INTERP");
    }
    if jitify {
        cmd.env("PLT_CS_COMPILE_LIMIT", "10");
    } else {
        cmd.env_remove("PLT_CS_COMPILE_LIMIT");
    }
    cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = cmd.spawn().expect("spawn racket");
    let stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut stderr_p = child.stderr.take().unwrap();
    let (tx, rx) = channel();
    std::thread::spawn(move || {
        let r = BufReader::new(stdout);
        for line in r.lines() {
            match line {
                Ok(l) => {
                    if tx.send(l).is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
    });
    let stderr = Arc::new(Mutex::new(String::new()));
    let se = stderr.clone();
    std::thread::spawn(move || {
        let mut buf = [0u8; 4096];
        loop {
            match stderr_p.read(&mut buf) {
                Ok(0) | Err(_) => break,
                Ok(n) => {
                    let mut s = se.lock().unwrap();
                    s.push_str(&String::from_utf8_lossy(&buf[..n]));
                    if s.len() > 8000 {
                        let cut = s.len() - 4000;
                        let cut = (cut..s.len()).find(|&i| s.is_char_boundary(i)).unwrap_or(s.len());
                        *s = s[cut..].to_string();
                    }
                }
            }
        }
    });
    Server { child, stdin, rx, stderr }
}

struct Pair {
    racket: PathBuf,
    runner: PathBuf,
    a: Server,
    b: Server,
    /// machine code, compiled under the case's optimizer variant
    c: Server,
    /// machine code in jitify mode (variant `jitify`), started on first use
    d: Option<Server>,
    /// machine code under GC stress (variants gc, gczo, gcsplit: runner.rkt
    /// starts a background place there, so it is kept apart from `c`),
    /// started on first use
    e: Option<Server>,
    /// released Racket 9.3 (variant `ref93`, second reference): racket and
    /// runner compiled by it, copied into the build dir by build.sh; started
    /// on first use
    f: Option<Server>,
    ref93: Option<(PathBuf, PathBuf)>,
    restarts: u64,
}

/// Optimizer variants run on server `c` (runner.rkt VARIANTS); each case
/// gets one, kept fixed while that case is shrunk.  The variant name is the
/// oracle name of its signatures.
/// `jitify` is not a runner.rkt variant: it runs on server `d` (env
/// PLT_CS_COMPILE_LIMIT=10) with variant `none`.
const VARIANTS: &[&str] = &["unsafe", "nocp0", "notr", "ctx", "noconst", "cp0big", "zo", "machind", "jitify",
                            "split", "splitzo", "splitmi", "macro", "macrozo", "macrosplit", "macrosub",
                            "opaque", "opaquesplit", "ctlnoise", "ctlsplit", "gc", "gczo", "gcsplit", "ref93",
                            "local", "localpart", "localzo", "preempt", "preemptctl", "preemptsplit",
                            "common", "noclos", "notrap", "dbg", "noinl", "chezmix", "chezmixzo",
                            "future", "futurezo", "futuresplit", "gcfuture", "port", "portsplit",
                            "top", "topzo", "topsplit", "rtrip", "rtripzo",
                            "chap", "chapzo", "chapsplit"];
/// Draw table: the split variants (module split in two, cross-module
/// inlining; runner.rkt `split-module`) and the macro variants (the module
/// rewritten through hygienic macros, runner.rkt `macro-module`; steering
/// round 4) get a third of the cases each.
const VARIANT_DRAW: &[&str] = &["unsafe", "nocp0", "notr", "ctx", "noconst", "cp0big", "zo", "machind", "jitify",
                                "split", "splitzo", "splitmi", "split", "splitzo", "splitmi",
                                "split", "splitzo", "splitmi",
                                "macro", "macrozo", "macrosplit", "macrosub", "macro", "macrozo", "macrosplit",
                                "macrosub", "macro", "macrozo", "macrosplit", "macrosub",
                                "opaque", "opaque", "opaque", "opaque", "opaque", "opaque", "opaque",
                                "opaque", "opaquesplit", "opaquesplit", "opaquesplit", "opaquesplit",
                                "ctlnoise", "ctlnoise", "ctlsplit", "ctlsplit",
                                "gc", "gc", "gc", "gc", "gc", "gczo", "gczo", "gczo", "gczo",
                                "gcsplit", "gcsplit", "gcsplit", "gcsplit", "gcsplit",
                                "ref93", "ref93", "ref93", "ref93", "ref93", "ref93", "ref93", "ref93",
                                "ref93", "ref93", "ref93", "ref93", "ref93", "ref93",
                                "local", "local", "local", "local", "local", "local", "local", "local",
                                "localpart", "localpart", "localpart", "localpart", "localpart",
                                "localpart", "localpart", "localpart", "localzo", "localzo", "localzo",
                                "localzo",
                                // steering round 9: preemption at arbitrary event checks
                                "preempt", "preempt", "preempt", "preempt", "preempt", "preempt",
                                "preempt", "preempt", "preempt", "preempt", "preempt", "preempt",
                                "preemptctl", "preemptctl", "preemptctl", "preemptctl", "preemptctl",
                                "preemptctl", "preemptctl", "preemptctl",
                                "preemptsplit", "preemptsplit", "preemptsplit", "preemptsplit",
                                "preemptsplit", "preemptsplit", "preemptsplit", "preemptsplit",
                                // steering round 10: Chez compiler knobs Racket never sets
                                "common", "common", "common", "common", "common", "noclos", "noclos",
                                "noclos", "noclos", "noclos", "notrap", "notrap", "notrap", "dbg", "dbg",
                                "dbg", "dbg", "noinl", "noinl", "noinl", "noinl",
                                "chezmix", "chezmix", "chezmix", "chezmix", "chezmix", "chezmix",
                                "chezmix", "chezmix", "chezmixzo", "chezmixzo", "chezmixzo", "chezmixzo",
                                "chezmixzo", "chezmixzo", "chezmixzo", "chezmixzo",
                                // steering round 11: sites evaluated in futures (other OS threads)
                                "future", "future", "future", "future", "future", "future", "future",
                                "future", "future", "future", "futurezo", "futurezo", "futurezo",
                                "futurezo", "futurezo", "futurezo", "futuresplit", "futuresplit",
                                "futuresplit", "futuresplit", "futuresplit", "futuresplit", "futuresplit",
                                "futuresplit", "gcfuture", "gcfuture", "gcfuture",
                                // steering round 12: ports of other kinds with the same content
                                // (only for programs with ports; others fall back to opaque)
                                "port", "port", "port", "port", "port", "port", "port", "port", "port",
                                "port", "port", "port", "portsplit", "portsplit", "portsplit", "portsplit",
                                "portsplit", "portsplit",
                                // steering round 13: forms evaluated one by one at the top level
                                "top", "top", "top", "top", "top", "top", "top", "top", "top", "top",
                                "top", "top", "topzo", "topzo", "topzo", "topzo", "topzo", "topzo",
                                "topzo", "topzo", "topzo", "topzo", "topsplit", "topsplit", "topsplit",
                                "topsplit", "topsplit", "topsplit", "topsplit", "topsplit", "topsplit",
                                "topsplit",
                                // steering round 13: write/read, fasl, number->string and
                                // equal-hash-code round trips checked at the opaque sites
                                "rtrip", "rtrip", "rtrip", "rtrip", "rtrip", "rtrip", "rtrip", "rtrip",
                                "rtripzo", "rtripzo", "rtripzo", "rtripzo", "rtripzo", "rtripzo",
                                // steering round 15: identity chaperones/impersonators at the opaque sites
                                "chap", "chap", "chap", "chap", "chap", "chap", "chap", "chap", "chap",
                                "chap", "chap", "chap", "chap", "chap", "chap", "chap", "chap", "chap",
                                "chap", "chap", "chapzo", "chapzo", "chapzo", "chapzo", "chapzo",
                                "chapzo", "chapzo", "chapzo", "chapzo", "chapzo", "chapzo", "chapzo",
                                "chapsplit", "chapsplit", "chapsplit", "chapsplit", "chapsplit",
                                "chapsplit", "chapsplit", "chapsplit", "chapsplit", "chapsplit",
                                "chapsplit", "chapsplit"];

/// Names bound in trunk's racket/base, racket/fixnum or racket/flonum but not
/// in 9.3: a case using one is not sent to the 9.3 server.
const NEW_SINCE_93: &[&str] = &["flhypot", "fllog1p", "flexpm1", "flcbrt", "flerf", "flgamma", "fllgamma"];

/// `#:unsafe` is only specified when the safe run raises no exn:fail:contract
/// (syntax.scrbl).  Conservative: the safe machine-code run finished `ok`
/// and no exception was raised and caught anywhere (`show` prints `(exn ...`,
/// the generated `with-handlers` handler prints `caught `).
fn unsafe_eligible(a: &Res) -> bool {
    match a {
        Res::Line(l) => kind_of(l) == "ok" && !l.contains("(exn ") && !l.contains("caught "),
        _ => false,
    }
}

impl Pair {
    fn new(racket: PathBuf, runner: PathBuf, ref93: Option<(PathBuf, PathBuf)>) -> Pair {
        let a = spawn_server(&racket, &runner, false);
        let b = spawn_server(&racket, &runner, true);
        let c = spawn_server(&racket, &runner, false);
        Pair { racket, runner, a, b, c, d: None, e: None, f: None, ref93, restarts: 0 }
    }
    /// The 9.3 run for variant `ref93`, sent after a's: None when 9.3 is not
    /// installed or the program uses a name 9.3 lacks.
    fn query93(&mut self, prog: &str, lim: Duration) -> Option<Res> {
        let (r93, run93) = self.ref93.clone()?;
        if NEW_SINCE_93.iter().any(|n| prog.contains(n)) {
            return None;
        }
        if self.f.is_none() {
            self.f = Some(spawn_server(&r93, &run93, false));
        }
        let fv = self.f.as_mut().unwrap();
        let sf = Self::send(fv, prog);
        let rf = Self::recv(fv, sf, lim);
        if !matches!(rf, Res::Line(_)) {
            let _ = fv.child.kill();
            let _ = fv.child.wait();
            self.f = None;
            self.restarts += 1;
        }
        Some(rf)
    }
    fn send(s: &mut Server, prog: &str) -> bool {
        Self::send_v(s, prog, "none")
    }
    fn send_v(s: &mut Server, prog: &str, variant: &str) -> bool {
        let msg = format!("{} {}\n{}", prog.len(), variant, prog);
        s.stdin.write_all(msg.as_bytes()).and_then(|_| s.stdin.flush()).is_ok()
    }
    fn recv(s: &mut Server, sent: bool, limit: Duration) -> Res {
        if !sent {
            return Res::Died(Self::death(s));
        }
        match s.rx.recv_timeout(limit) {
            Ok(l) if !matches!(kind_of(&l), "ok" | "exn" | "raise" | "timeout" | "oom") => {
                // not a result line: something wrote to the server's stdout
                // directly (Racket CS's thread-layer `internal-error` prints
                // "internal-error: ..." and a " at <name>" backtrace with
                // Chez's printf, then exits 1)
                let mut more = vec![l];
                while let Ok(x) = s.rx.recv_timeout(Duration::from_millis(1500)) {
                    if more.len() < 40 { more.push(x); }
                }
                let _ = s.child.kill();
                Res::Died(format!("stray output on stdout: {}; {}", more.join(" | "), Self::death(s)))
            }
            Ok(l) => Res::Line(l),
            Err(RecvTimeoutError::Timeout) => Res::Hung,
            Err(RecvTimeoutError::Disconnected) => Res::Died(Self::death(s)),
        }
    }
    fn death(s: &mut Server) -> String {
        std::thread::sleep(Duration::from_millis(100));
        let st = s.child.try_wait().ok().flatten().map(|x| format!("{x:?}")).unwrap_or("?".into());
        let e = s.stderr.lock().unwrap().clone();
        format!("status {st}; stderr: {}", e.chars().rev().take(1500).collect::<String>().chars().rev().collect::<String>())
    }
    fn query(&mut self, prog: &str, variant: &str) -> (Res, Res, Option<Res>) {
        let lim = Duration::from_secs(CASE_TIMEOUT_S + 30);
        // Send to a and b first so they run in parallel; c (variant) too,
        // except `unsafe`: it runs after a, only when a's run makes it eligible (an
        // ineligible unsafe run is undefined behaviour and could corrupt the
        // server).  b (interpreter) is the slow one anyway.
        let sa = Self::send(&mut self.a, prog);
        let sb = Self::send(&mut self.b, prog);
        if variant == "ref93" {
            let rf = self.query93(prog, lim);
            let ra = Self::recv(&mut self.a, sa, lim);
            let rb = Self::recv(&mut self.b, sb, lim);
            self.restart_ab(&ra, &rb);
            return (ra, rb, rf);
        }
        // safe variants run in parallel with a
        let jit = variant == "jitify";
        if jit && self.d.is_none() {
            self.d = Some(spawn_server_jit(&self.racket, &self.runner, false, true));
        }
        let gcv = variant.starts_with("gc");
        if gcv && self.e.is_none() {
            self.e = Some(spawn_server(&self.racket, &self.runner, false));
        }
        let (cv, wire) = if jit { (self.d.as_mut().unwrap(), "none") }
                         else if gcv { (self.e.as_mut().unwrap(), variant) }
                         else { (&mut self.c, variant) };
        let sc_early = if variant != "unsafe" { Some(Self::send_v(cv, prog, wire)) } else { None };
        let ra = Self::recv(&mut self.a, sa, lim);
        let rc = if variant != "unsafe" || unsafe_eligible(&ra) {
            let cv = if jit { self.d.as_mut().unwrap() } else if gcv { self.e.as_mut().unwrap() } else { &mut self.c };
            let sc = match sc_early { Some(x) => x, None => Self::send_v(cv, prog, wire) };
            let rc = Self::recv(cv, sc, lim);
            if !matches!(rc, Res::Line(_)) {
                let _ = cv.child.kill();
                let _ = cv.child.wait();
                *cv = spawn_server_jit(&self.racket, &self.runner, false, jit);
                self.restarts += 1;
            }
            Some(rc)
        } else {
            None
        };
        let rb = Self::recv(&mut self.b, sb, lim);
        self.restart_ab(&ra, &rb);
        (ra, rb, rc)
    }
    fn restart_ab(&mut self, ra: &Res, rb: &Res) {
        if !matches!(ra, Res::Line(_)) {
            let _ = self.a.child.kill();
            let _ = self.a.child.wait();
            self.a = spawn_server(&self.racket, &self.runner, false);
            self.restarts += 1;
        }
        if !matches!(rb, Res::Line(_)) {
            let _ = self.b.child.kill();
            let _ = self.b.child.wait();
            self.b = spawn_server(&self.racket, &self.runner, true);
            self.restarts += 1;
        }
    }
    fn close(mut self) {
        drop(self.a.stdin);
        drop(self.b.stdin);
        drop(self.c.stdin);
        let mut d = self.d.take().map(|d| { drop(d.stdin); d.child });
        let mut e = self.e.take().map(|e| { drop(e.stdin); e.child });
        let mut f = self.f.take().map(|f| { drop(f.stdin); f.child });
        let mut children = vec![&mut self.a.child, &mut self.b.child, &mut self.c.child];
        if let Some(dc) = d.as_mut() { children.push(dc); }
        if let Some(ec) = e.as_mut() { children.push(ec); }
        if let Some(fc) = f.as_mut() { children.push(fc); }
        for c in children {
            let t = Instant::now();
            loop {
                if let Ok(Some(_)) = c.try_wait() {
                    break;
                }
                if t.elapsed() > Duration::from_secs(20) {
                    let _ = c.kill();
                    let _ = c.wait();
                    break;
                }
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
}

/// Messages that only an internal failure produces (never a documented error).
const INTERNAL: &[&str] = &["internal error", "invalid memory reference", "Exception in ", "attempt to reference unbound", "compile-time"];

fn kind_of(l: &str) -> &str {
    l.split('\t').next().unwrap_or("")
}

#[derive(Debug, Clone, PartialEq)]
enum Verdict {
    Pass,
    Skip(&'static str),
    Fail(&'static str, &'static str), // oracle, kind
}

fn classify(a: &Res, b: &Res) -> Verdict {
    match (a, b) {
        (Res::Died(_), _) | (_, Res::Died(_)) => return Verdict::Fail("crash", "died"),
        _ => {}
    }
    for r in [a, b] {
        if let Res::Line(l) = r {
            if INTERNAL.iter().any(|p| l.contains(p)) {
                return Verdict::Fail("crash", "internal");
            }
        }
    }
    let (la, lb) = match (a, b) {
        (Res::Hung, Res::Hung) => return Verdict::Skip("both_hung"),
        (Res::Hung, Res::Line(l)) if kind_of(l) != "timeout" => return Verdict::Fail("crash", "hang"),
        (Res::Hung, _) | (_, Res::Hung) => return Verdict::Skip("hung"),
        (Res::Line(x), Res::Line(y)) => (x, y),
        _ => unreachable!(),
    };
    let (ka, kb) = (kind_of(la), kind_of(lb));
    if ka == "oom" || kb == "oom" {
        return Verdict::Skip("oom");
    }
    if ka == "timeout" && kb == "timeout" {
        return Verdict::Skip("both_timeout");
    }
    if ka == "timeout" {
        // Machine code timed out where the (~100x slower) interpreter finished.
        return Verdict::Fail("crash", "hang");
    }
    if kb == "timeout" {
        return Verdict::Skip("interp_timeout");
    }
    if la == lb {
        return Verdict::Pass;
    }
    let fa: Vec<&str> = la.split('\t').collect();
    let fb: Vec<&str> = lb.split('\t').collect();
    if ka != kb {
        return Verdict::Fail("diff", "error");
    }
    if ka == "exn" && fa.get(1) == fb.get(1) {
        if fa.get(2) != fb.get(2) {
            return Verdict::Fail("diff", "error");
        }
        return Verdict::Fail("diff", "errmsg");
    }
    Verdict::Fail("diff", "value")
}

/// Variant oracle: machine code (a) vs machine code under an optimizer
/// toggle (c).  Toggles must not change results (compiler.scrbl /
/// eval.scrbl: context preservation only affects stack traces; unsafe only
/// where exn:fail:contract would be raised, excluded by eligibility).
fn classify_variant(a: &Res, c: &Option<Res>, variant: &'static str, prog: &str) -> Verdict {
    let Some(c) = c else { return Verdict::Pass };
    if variant == "ref93" {
        return classify_ref93(a, c, prog);
    }
    let la = match a {
        Res::Line(l) if kind_of(l) != "timeout" && kind_of(l) != "oom" => l,
        _ => return Verdict::Pass,
    };
    let lc = match c {
        Res::Died(_) => return Verdict::Fail(variant, "died"),
        Res::Hung => return Verdict::Fail(variant, "hang"),
        Res::Line(l) => l,
    };
    if INTERNAL.iter().any(|p| lc.contains(p)) && !INTERNAL.iter().any(|p| la.contains(p)) {
        return Verdict::Fail(variant, "internal");
    }
    let kc = kind_of(lc);
    if kc == "oom" {
        return Verdict::Skip("variant_oom");
    }
    if kc == "timeout" {
        return Verdict::Fail(variant, "hang");
    }
    if la == lc {
        return Verdict::Pass;
    }
    let fa: Vec<&str> = la.split('\t').collect();
    let fc: Vec<&str> = lc.split('\t').collect();
    if kind_of(la) != kc {
        return Verdict::Fail(variant, "error");
    }
    if kc == "exn" && fa.get(1) == fc.get(1) {
        if fa.get(2) != fc.get(2) {
            return Verdict::Fail(variant, "error");
        }
        return Verdict::Fail(variant, "errmsg");
    }
    Verdict::Fail(variant, "value")
}

/// Error messages inside the printed output of a result line, `(exn KIND
/// "message")` as written by `show` (in the line's `write`n output field:
/// `(exn KIND \"message\")`), reduced to `(exn KIND)`.
fn strip_msgs(f: &str) -> String {
    let b: Vec<char> = f.chars().collect();
    let mut o = String::new();
    let mut i = 0;
    let pat: Vec<char> = "(exn ".chars().collect();
    while i < b.len() {
        if b[i..].starts_with(&pat) {
            // kind word, then ` \"`
            let mut j = i + pat.len();
            while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == '-') {
                j += 1;
            }
            if j + 2 < b.len() && b[j] == ' ' && b[j + 1] == '\\' && b[j + 2] == '"' {
                // decode written-form escapes (\\ -> \, \" -> ") into the
                // original text; the message ends at an unescaped original quote
                let mut k = j + 3;
                let mut esc = false;
                let mut end = None;
                while k + 1 < b.len() {
                    let ch = if b[k] == '\\' { k += 2; b[k - 1] } else { k += 1; b[k - 1] };
                    if esc { esc = false; continue; }
                    if ch == '\\' { esc = true; continue; }
                    if ch == '"' { end = Some(k); break; }
                }
                if let Some(e) = end {
                    if e < b.len() && b[e] == ')' {
                        o.extend(b[i..j].iter());
                        o.push(')');
                        i = e + 1;
                        continue;
                    }
                }
            }
        }
        o.push(b[i]);
        i += 1;
    }
    o
}

/// ref93 comparison form of a result line: message texts dropped (wording
/// changes between releases are not bugs; the exn struct type and the kind
/// printed by `show` stay), and when the program uses min/max the sign of
/// zero ignored (trunk 05afec9201: flmax returns its second argument for
/// 0.0 and -0.0, documented change).
fn norm93(l: &str, prog: &str) -> String {
    let mut f: Vec<String> = l.split('\t').map(strip_msgs).collect();
    if f.first().map(|s| s.as_str()) == Some("exn") {
        f.truncate(3);
    }
    let mut s = f.join("\t");
    if ["flmax", "flmin", "(max ", "(min "].iter().any(|p| prog.contains(p)) {
        s = s.replace("-0.0", "0.0");
    }
    // The sign of that zero reaches printed infinities through division
    // ((fl/ -1.0 (flmax 0.0 0.0 -0.0)): trunk +inf.0, 9.3 -inf.0), so with
    // flmax the sign of infinity is ignored too.
    if prog.contains("flmax") {
        s = s.replace("-inf.0", "+inf.0");
    }
    s
}

/// Second reference: trunk machine code (a) vs released Racket 9.3 machine
/// code on the same module (c).  Only reached when trunk machine code and
/// trunk interpreter agree (classify_all), so a difference is in code both
/// trunk modes share (rumble/Chez library compiled by the changed compiler,
/// schemify, expander, io) or a documented change since 9.3 (triage against
/// `git log v9.3..`).  9.3 crashes/hangs are 9.3's own problems: skipped.
fn classify_ref93(a: &Res, c: &Res, prog: &str) -> Verdict {
    let la = match a {
        Res::Line(l) if kind_of(l) != "timeout" && kind_of(l) != "oom" => l,
        _ => return Verdict::Pass,
    };
    let lc = match c {
        Res::Line(l) if kind_of(l) != "timeout" && kind_of(l) != "oom" => l,
        _ => return Verdict::Skip("ref93_noresult"),
    };
    if lc.contains("unbound identifier") || lc.contains("exn:fail:syntax") {
        return Verdict::Skip("ref93_unbound");
    }
    if INTERNAL.iter().any(|p| lc.contains(p)) {
        return Verdict::Skip("ref93_internal");
    }
    let (na, nc) = (norm93(la, prog), norm93(lc, prog));
    if na == nc {
        return Verdict::Pass;
    }
    // 9.3 bug fixed in trunk (patch 003 / Chez unboxed flonum box allocated
    // before a continuation capture, also in 9.3): not comparable.
    if prog.contains("call-with-composable-continuation") || prog.contains("call/cc") || prog.contains("call-with-current-continuation") {
        return Verdict::Skip("ref93_continuation");
    }
    // 9.3 bugs repaired in trunk that this generator hits:
    // 8f67966b14 (schemify unused-function handling: a module variable
    // set! next to an unused local function counted as constant), and the
    // schemify mutation-tracking repairs (0cd7dd3cc0, bc1b6eb434): generated
    // programs only set! variables they mutate, so "cannot modify a constant"
    // is never right; 45177e8405 (expt with a most-negative-fixnum exponent).
    if prog.contains("(define (unused") {
        return Verdict::Skip("ref93_known_unused_fn");
    }
    if lc.contains("cannot modify a constant") && !la.contains("cannot modify a constant") {
        return Verdict::Skip("ref93_known_mutation");
    }
    if prog.contains("expt") && prog.contains("-1152921504606846976") {
        return Verdict::Skip("ref93_known_expt");
    }
    if kind_of(la) != kind_of(lc) || (kind_of(la) == "exn" && na.split('\t').nth(2) != nc.split('\t').nth(2)) {
        return Verdict::Fail("ref93", "error");
    }
    Verdict::Fail("ref93", "value")
}

/// Both oracles; machine-vs-interpreter first (its signatures unchanged).
fn classify_all(a: &Res, b: &Res, c: &Option<Res>, variant: &'static str, prog: &str) -> Verdict {
    let v1 = classify(a, b);
    if matches!(v1, Verdict::Fail(..)) {
        return v1;
    }
    if variant == "ref93" && a != b {
        // not comparable (interp timeout etc.): the 9.3 comparison needs
        // both trunk modes to agree
        return v1;
    }
    match classify_variant(a, c, variant, prog) {
        Verdict::Pass => v1,
        v2 @ Verdict::Fail(..) => v2,
        Verdict::Skip(r) => if v1 == Verdict::Pass { Verdict::Skip(r) } else { v1 },
    }
}

const PRIORITY: &[&str] = &[
    "composable", "reentry", "marks-tag", "prompt", "escape", "dynamic-wind", "wcm", "parameterize", "handlers", "closure-set", "unused-fn",
    "letrec-loop", "fl-loop", "for-fold", "for-sum", "values", "struct-mutate", "struct",
    "vector-mutate", "vector", "flvector", "hash", "type-dispatch", "type-guard", "pair-guard",
    "case-any", "box", "vector-any", "list-op", "if-mixed", "char", "symbol", "type-pred", "equal", "pair", 
    "port-in", "port-out", "lib-hash", "lib-regexp", "lib-print", "lib-numstr", "lib-bytes", "lib-symbol", "lib-char", "lib-string", "lib-list", "lib-cmp", "lib-num", "lib-typed",
    "flbit-field", "flround", "flmin-max", "fl->int",
    "int->fl", "fixnum-shift", "fixnum", "shift", "flonum", "generic-fl", "fl-compare", "fx-compare",
    "case", "cond", "if", "set", "lambda-app", "internal-define", "let", "call", "tap", "list",
    "string", "fl-predicate", "predicate", "compare", "generic-arith", "logic", "begin",
];

fn area(items: &[E]) -> String {
    // the feature with the highest priority present in the shrunk program
    let mut tags = vec![];
    for it in items {
        it.tags(&mut tags);
    }
    for p in PRIORITY {
        if tags.contains(p) {
            return p.replace("->", "-to-");
        }
    }
    "toplevel".into()
}

fn json_str(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            '\r' => o.push_str("\\r"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn res_text(r: &Res) -> String {
    match r {
        Res::Line(l) => l.clone(),
        Res::Died(s) => format!("DIED {s}"),
        Res::Hung => "HUNG (no reply)".into(),
    }
}

const REPRO: &str = r#"#!/usr/bin/env bash
# Repro for signature @SIG@ (oracle @ORACLE@, kind @KIND@).
# Runs prog.rkt through runner.rkt twice with the build's racket: compiled to
# machine code (default) and interpreted (PLT_CS_INTERP=1).
# exit 1: failure reproduces; 0: it does not; 2: cannot decide.
B=$(cd "$1" 2>/dev/null && pwd) || exit 2
R="$B/src/racket/bin/racket"
[ -x "$R" ] || exit 2
cd "$(dirname "$0")"
KIND=@KIND@
a=$(env -u PLT_CS_INTERP RKT_CASE_TIMEOUT=20 timeout -k 5 120 "$R" runner.rkt file prog.rkt 2>&1); ca=$?
b=$(PLT_CS_INTERP=1 RKT_CASE_TIMEOUT=120 timeout -k 5 300 "$R" runner.rkt file prog.rkt 2>&1); cb=$?
res() { printf '%s\n' "$1" | grep -E $'^(ok|exn|raise|timeout|oom)\t|^oom$' | tail -1; }
ra=$(res "$a"); rb=$(res "$b")
case $KIND in
  died)
    for c in "$ca:$ra" "$cb:$rb"; do
      code=${c%%:*}; line=${c#*:}
      if [ "$code" != 0 ] && [ "$code" != 124 ] && [ "$code" != 137 ] && [ -z "$line" ]; then exit 1; fi
    done
    exit 0 ;;
  internal)
    if printf '%s\n%s\n' "$a" "$b" | grep -qE 'internal error|invalid memory reference|Exception in |attempt to reference unbound|compile-time'; then exit 1; fi
    [ -n "$ra" ] && [ -n "$rb" ] && exit 0
    exit 2 ;;
  hang)
    [ -z "$rb" ] && exit 2
    case "$rb" in timeout*) exit 2;; esac
    case "$ra" in timeout*) exit 1;; esac
    [ -z "$ra" ] && exit 2
    exit 0 ;;
  *)
    [ -z "$ra" ] || [ -z "$rb" ] && exit 2
    case "$ra$rb" in *timeout*|*oom*) exit 2;; esac
    [ "$ra" != "$rb" ] && exit 1
    exit 0 ;;
esac
"#;

const REPRO_VARIANT: &str = r#"#!/usr/bin/env bash
# Repro for signature @SIG@ (oracle @ORACLE@, kind @KIND@).
# Runs prog.rkt through runner.rkt twice with the build's racket, both
# compiled to machine code: default, and with optimizer variant @ORACLE@
# (runner.rkt VARIANTS; `jitify` = env PLT_CS_COMPILE_LIMIT=10).  For `unsafe` the default run must be eligible (ok,
# no exception raised and caught), else the case is not comparable.
# exit 1: failure reproduces; 0: it does not; 2: cannot decide.
B=$(cd "$1" 2>/dev/null && pwd) || exit 2
R="$B/src/racket/bin/racket"
[ -x "$R" ] || exit 2
cd "$(dirname "$0")"
KIND=@KIND@
VAR=@ORACLE@
a=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=20 timeout -k 5 120 "$R" runner.rkt file prog.rkt none 2>&1); ca=$?
res() { printf '%s
' "$1" | grep -E $'^(ok|exn|raise|timeout|oom)	|^oom$' | tail -1; }
ra=$(res "$a")
[ -z "$ra" ] && exit 2
case "$ra" in timeout*|oom*) exit 2;; esac
if [ "$VAR" = unsafe ]; then
  case "$ra" in ok*) ;; *) exit 0;; esac
  case "$ra" in *"(exn "*|*"caught "*) exit 0;; esac
fi
if [ "$VAR" = jitify ]; then
  c=$(env -u PLT_CS_INTERP PLT_CS_COMPILE_LIMIT=10 RKT_CASE_TIMEOUT=60 timeout -k 5 180 "$R" runner.rkt file prog.rkt none 2>&1); cc=$?
else
  # a process that hit the thread layer's internal-error spins instead of
  # exiting (even on SIGTERM), so died cases get a shorter limit
  T0=180; [ "$KIND" = died ] && T0=45
  c=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=60 timeout -k 5 $T0 "$R" runner.rkt file prog.rkt "$VAR" 2>&1); cc=$?
fi
rc=$(res "$c")
# preempt*/future*: where the timer fires during compilation (or whether a
# future worker picks a future up before the touch) depends on timing, so
# a run that matches is retried twice (the program's own sites are
# deterministic in ticks, the expander/compiler's swaps are not)
# died (e.g. the thread layer's "internal-error: attempting to suspend a
# future in uninterruptible mode", which depends on a future running on a
# worker at that moment): up to 8 more runs until one dies
case "$VAR" in preempt*|future*|gcfuture)
  n=2; T=180; [ "$KIND" = died ] && n=8 && T=45
  for t in $(seq $n); do
    if [ "$KIND" = died ]; then
      [ -n "$rc" ] || break
    else
      [ "$KIND" != hang ] && [ -n "$rc" ] && [ "$ra" = "$rc" ] || break
    fi
    c=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=60 timeout -k 5 $T "$R" runner.rkt file prog.rkt "$VAR" 2>&1); cc=$?
    rc=$(res "$c")
  done ;;
esac
case $KIND in
  died)
    if printf '%s\n' "$c" | grep -q '^internal-error: '; then exit 1; fi
    if [ "$cc" != 0 ] && [ "$cc" != 124 ] && [ "$cc" != 137 ] && [ -z "$rc" ]; then exit 1; fi
    exit 0 ;;
  internal)
    if printf '%s
' "$c" | grep -qE 'internal error|invalid memory reference|Exception in |attempt to reference unbound|compile-time'; then exit 1; fi
    [ -n "$rc" ] && exit 0
    exit 2 ;;
  hang)
    case "$rc" in timeout*) exit 1;; esac
    [ -z "$rc" ] && exit 2
    exit 0 ;;
  *)
    [ -z "$rc" ] && exit 2
    case "$rc" in *oom*|timeout*) exit 2;; esac
    [ "$ra" != "$rc" ] && exit 1
    exit 0 ;;
esac
"#;

const REPRO_REF93: &str = r##"#!/usr/bin/env bash
# Repro for signature @SIG@ (oracle ref93, kind @KIND@).
# Runs prog.rkt through runner.rkt with the build's racket (machine code and
# interpreter, which must agree) and with released Racket 9.3 (the build's
# ref93/ copy, see build.sh); compares trunk machine code with 9.3 after
# dropping error-message texts (and the sign of zero when min/max is used),
# as rktgen's norm93 does.
# exit 1: failure reproduces; 0: it does not; 2: cannot decide.
B=$(cd "$1" 2>/dev/null && pwd) || exit 2
R="$B/src/racket/bin/racket"
R93="$B/ref93/racket/bin/racket"
[ -x "$R" ] && [ -x "$R93" ] || exit 2
cd "$(dirname "$0")"
res() { printf '%s\n' "$1" | grep -E $'^(ok|exn|raise|timeout|oom)\t|^oom$' | tail -1; }
a=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=20 timeout -k 5 120 "$R" runner.rkt file prog.rkt none 2>&1)
b=$(env -u PLT_CS_COMPILE_LIMIT PLT_CS_INTERP=1 RKT_CASE_TIMEOUT=120 timeout -k 5 300 "$R" runner.rkt file prog.rkt none 2>&1)
c=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=60 timeout -k 5 180 "$R93" runner.rkt file prog.rkt none 2>&1)
ra=$(res "$a"); rb=$(res "$b"); rc=$(res "$c")
[ -z "$ra" ] || [ -z "$rb" ] || [ -z "$rc" ] && exit 2
case "$ra$rb$rc" in *timeout*|*oom*) exit 2;; esac
[ "$ra" != "$rb" ] && exit 0
case "$rc" in *"unbound identifier"*|*exn:fail:syntax*) exit 2;; esac
case "$rc" in *"cannot modify a constant"*) case "$ra" in *"cannot modify a constant"*) ;; *) exit 0;; esac;; esac
RA="$ra" RC="$rc" python3 -I -c '
import os, sys
prog = open("prog.rkt", encoding="utf-8").read()
def strip(f):
    o = []; i = 0; n = len(f)
    while i < n:
        if f.startswith("(exn ", i):
            j = i + 5
            while j < n and (f[j].isascii() and (f[j].isalnum() or f[j] == "-")): j += 1
            if j + 2 < n and f[j] == " " and f[j+1] == "\\" and f[j+2] == "\"":
                k = j + 3; esc = False; end = None
                while k + 1 < n:
                    if f[k] == "\\": k += 2; ch = f[k-1]
                    else: k += 1; ch = f[k-1]
                    if esc: esc = False; continue
                    if ch == "\\": esc = True; continue
                    if ch == "\"": end = k; break
                if end is not None and end < n and f[end] == ")":
                    o.append(f[i:j]); o.append(")"); i = end + 1; continue
        o.append(f[i]); i += 1
    return "".join(o)
def norm(l):
    f = [strip(x) for x in l.split("\t")]
    if f[0] == "exn": f = f[:3]
    s = "\t".join(f)
    if any(p in prog for p in ("flmax", "flmin", "(max ", "(min ")): s = s.replace("-0.0", "0.0")
    if "flmax" in prog: s = s.replace("-inf.0", "+inf.0")
    return s
sys.exit(1 if norm(os.environ["RA"]) != norm(os.environ["RC"]) else 0)
'
"##;

struct Search {
    out: PathBuf,
    runner_src: PathBuf,
    per_sig: HashMap<String, usize>,
    shrinks_per_kind: HashMap<String, usize>,
}

impl Search {
    /// Write a finding for the (already shrunk) program; `ra`/`rb` are its results.
    fn record(&mut self, small: &Program, v: &Verdict, seed_label: &str, ra: &Res, rb: &Res, rc: &Option<Res>) {
        let (oracle, kind) = match v {
            Verdict::Fail(o, k) => (*o, *k),
            _ => return,
        };
        let small = &small.0;
        let sig = format!("{oracle}__{kind}__{}", area(&small));
        let cnt = self.per_sig.entry(sig.clone()).or_insert(0);
        if *cnt >= 3 {
            return;
        }
        *cnt += 1;
        let dir = self.out.join("findings").join(&sig).join(cnt.to_string());
        std::fs::create_dir_all(&dir).unwrap();
        let prog = render_program(small);
        std::fs::write(dir.join("prog.rkt"), &prog).unwrap();
        std::fs::copy(&self.runner_src, dir.join("runner.rkt")).unwrap();
        let is_variant = VARIANTS.contains(&oracle);
        let msg = if oracle == "ref93" {
            let c = rc.as_ref().map(res_text).unwrap_or_else(|| "(not run)".into());
            format!("trunk machine-code (= trunk interpreter): {}\nracket 9.3 machine-code: {}", res_text(ra), c)
        } else if is_variant {
            let c = rc.as_ref().map(res_text).unwrap_or_else(|| "(not run)".into());
            format!("machine-code: {}\nmachine-code, variant {oracle}: {}", res_text(ra), c)
        } else {
            format!("machine-code: {}\ninterpreter:  {}", res_text(ra), res_text(rb))
        };
        std::fs::write(dir.join("results.txt"), &msg).unwrap();
        let fj = format!(
            "{{\"signature\": {}, \"oracle\": {}, \"message\": {}, \"seed\": {}}}\n",
            json_str(&sig),
            json_str(oracle),
            json_str(&msg.chars().take(3000).collect::<String>()),
            json_str(seed_label)
        );
        std::fs::write(dir.join("finding.json"), fj).unwrap();
        let rs = (if oracle == "ref93" { REPRO_REF93 } else if is_variant { REPRO_VARIANT } else { REPRO }).replace("@SIG@", &sig).replace("@ORACLE@", oracle).replace("@KIND@", kind);
        let rp = dir.join("repro.sh");
        std::fs::write(&rp, rs).unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&rp, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
}

fn mix(seed: u64, i: u64) -> u64 {
    let mut z = seed.wrapping_mul(0x100000001B3) ^ i.wrapping_mul(0x9E3779B97F4A7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// One failure site per (oracle, kind): ephyra keeps the panic site while
/// shrinking, so a shrink never trades one kind of failure for another.
fn fail_at(v: &Verdict, detail: &str) {
    match v {
        Verdict::Fail("diff", "value") => panic!("diff value: {detail}"),
        Verdict::Fail("diff", "error") => panic!("diff error: {detail}"),
        Verdict::Fail("diff", "errmsg") => panic!("diff errmsg: {detail}"),
        Verdict::Fail("crash", "died") => panic!("crash died: {detail}"),
        Verdict::Fail("crash", "internal") => panic!("crash internal: {detail}"),
        Verdict::Fail("crash", "hang") => panic!("crash hang: {detail}"),
        // variant oracles: the variant is fixed while a case is shrunk, so
        // one site per kind keeps the failure kind.
        Verdict::Fail(_, "value") => panic!("variant value: {detail}"),
        Verdict::Fail(_, "error") => panic!("variant error: {detail}"),
        Verdict::Fail(_, "errmsg") => panic!("variant errmsg: {detail}"),
        Verdict::Fail(_, "died") => panic!("variant died: {detail}"),
        Verdict::Fail(_, "internal") => panic!("variant internal: {detail}"),
        Verdict::Fail(_, "hang") => panic!("variant hang: {detail}"),
        Verdict::Fail(o, k) => panic!("{o} {k}: {detail}"),
        _ => {}
    }
}

/// Last property evaluation, read by the search loop after `run.test`.
struct Last {
    verdict: Verdict,
    a: Res,
    b: Res,
    c: Option<Res>,
}

fn write_stats(out: &Path, cases: u64, failures: u64, extra: &BTreeMap<String, u64>, rate: f64) {
    let mut s = format!("{{\"cases\": {cases}, \"failures\": {failures}, \"cases_per_sec\": {rate:.2}");
    for (k, v) in extra {
        s.push_str(&format!(", {}: {v}", json_str(k)));
    }
    s.push_str("}\n");
    let tmp = out.join("stats.json.tmp");
    std::fs::write(&tmp, s).unwrap();
    std::fs::rename(tmp, out.join("stats.json")).unwrap();
}

// ---------------------------------------------------------------- numref
// Oracle `numref` (steering round 14): numeric expression lists checked
// against racket/numref.py, an independent Python evaluator.  The
// machine-code server `a` runs the module; numref.py says pass / fail.

struct PyRef { child: Child, stdin: ChildStdin, rx: Receiver<String> }

fn spawn_py(script: &Path) -> PyRef {
    let mut child = Command::new("python3").arg("-I").arg(script).arg("server")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn().expect("python3");
    let stdin = child.stdin.take().unwrap();
    let out = child.stdout.take().unwrap();
    let (tx, rx) = channel();
    std::thread::spawn(move || {
        for l in BufReader::new(out).lines() {
            match l { Ok(l) => { if tx.send(l).is_err() { break; } } Err(_) => break }
        }
    });
    PyRef { child, stdin, rx }
}

impl PyRef {
    /// numref.py's verdict fields, or None (python died/hung: restarted)
    fn check(&mut self, script: &Path, prog: &str, line: &str) -> Option<Vec<String>> {
        let msg = format!("{}\n{}{}\n{}", prog.len(), prog, line.len(), line);
        let ok = self.stdin.write_all(msg.as_bytes()).and_then(|_| self.stdin.flush()).is_ok();
        let r = if ok { self.rx.recv_timeout(Duration::from_secs(30)).ok() } else { None };
        match r {
            Some(l) => Some(l.split('\t').map(|x| x.to_string()).collect()),
            None => {
                let _ = self.child.kill();
                let _ = self.child.wait();
                *self = spawn_py(script);
                None
            }
        }
    }
}

const REPRO_NUMREF: &str = r#"#!/usr/bin/env bash
# Repro for signature @SIG@ (oracle numref, kind @KIND@).
# Runs prog.rkt through runner.rkt with the build's racket (machine code, or the
# interpreter for kinds ivalue/ierror) and
# checks every "(o i ...)" line's printed value against numref.py, an
# independent evaluator (Python int / fractions.Fraction / IEEE doubles).
# `python3 -I numref.py eval prog.rkt` prints the expected lines.
# exit 1: failure reproduces; 0: it does not; 2: cannot decide.
B=$(cd "$1" 2>/dev/null && pwd) || exit 2
R="$B/src/racket/bin/racket"
[ -x "$R" ] || exit 2
command -v python3 >/dev/null || exit 2
cd "$(dirname "$0")"
KIND=@KIND@
# kinds ivalue/ierror: the interpreter's (PLT_CS_INTERP=1) output is the wrong one
# kinds uvalue/uerror: machine code under runner.rkt variant unsafe ((#%declare #:unsafe)),
# on lines that raise nothing in safe mode (checked first: else 2)
case $KIND in
  u*) s=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=20 timeout -k 5 120 "$R" runner.rkt file prog.rkt none 2>&1)
      case "$s" in *'err\n'*|*'err"'*) exit 2;; esac
      a=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=20 timeout -k 5 120 "$R" runner.rkt file prog.rkt unsafe 2>&1); ca=$? ;;
  i*) a=$(env -u PLT_CS_COMPILE_LIMIT PLT_CS_INTERP=1 RKT_CASE_TIMEOUT=120 timeout -k 5 300 "$R" runner.rkt file prog.rkt none 2>&1); ca=$? ;;
  *) a=$(env -u PLT_CS_INTERP -u PLT_CS_COMPILE_LIMIT RKT_CASE_TIMEOUT=20 timeout -k 5 120 "$R" runner.rkt file prog.rkt none 2>&1); ca=$? ;;
esac
ra=$(printf '%s\n' "$a" | grep -E $'^(ok|exn|raise|timeout|oom)\t|^oom$' | tail -1)
if [ "${KIND%died}" != "$KIND" ]; then
  if [ "$ca" != 0 ] && [ "$ca" != 124 ] && [ "$ca" != 137 ] && [ -z "$ra" ]; then exit 1; fi
  exit 0
fi
[ -z "$ra" ] && exit 2
printf '%s\n' "$ra" | python3 -I numref.py check prog.rkt >/dev/null
exit $?
"#;

struct NumCtx { py: PyRef, script: PathBuf }

/// mode 0: machine code (server a), 1: interpreter (b), 2: machine code
/// under variant `unsafe` (server c)
fn num_query(pair: &mut Pair, nc: &mut NumCtx, text: &str, mode: u8) -> (Res, Option<Vec<String>>) {
    let lim = Duration::from_secs(CASE_TIMEOUT_S + 30);
    let ok = Res::Line("ok".into());
    let ra = match mode {
        0 => { let s = Pair::send(&mut pair.a, text); let r = Pair::recv(&mut pair.a, s, lim); pair.restart_ab(&r, &ok); r }
        1 => { let s = Pair::send(&mut pair.b, text); let r = Pair::recv(&mut pair.b, s, lim); pair.restart_ab(&ok, &r); r }
        _ => {
            let s = Pair::send_v(&mut pair.c, text, "unsafe");
            let r = Pair::recv(&mut pair.c, s, lim);
            if !matches!(r, Res::Line(_)) {
                let _ = pair.c.child.kill();
                let _ = pair.c.child.wait();
                pair.c = spawn_server(&pair.racket, &pair.runner, false);
                pair.restarts += 1;
            }
            r
        }
    };
    let v = match &ra { Res::Line(l) => nc.py.check(&nc.script, text, l), _ => None };
    (ra, v)
}

/// one numref case; true when a failure was found (and recorded)
fn numref_case(pair: &mut Pair, nc: &mut NumCtx, rseed: u64, search: &mut Search, extra: &mut BTreeMap<String, u64>) -> bool {
    let mut g = num::NumGen::new(rseed);
    let lines: Vec<(usize, num::Line)> = g.program().into_iter().enumerate().collect();
    let text = num::render_numprog(&lines);
    // machine code (a) and interpreter (b) in parallel; each checked against numref.py
    let lim = Duration::from_secs(CASE_TIMEOUT_S + 30);
    let sa = Pair::send(&mut pair.a, &text);
    let sb = Pair::send(&mut pair.b, &text);
    let ra0 = Pair::recv(&mut pair.a, sa, lim);
    let rb0 = Pair::recv(&mut pair.b, sb, lim);
    pair.restart_ab(&ra0, &rb0);
    let va = match &ra0 { Res::Line(l) => nc.py.check(&nc.script, &text, l), _ => None };
    let vb = match &rb0 { Res::Line(l) => nc.py.check(&nc.script, &text, l), _ => None };
    let a_fail = matches!(&va, Some(f) if f[0] == "fail");
    let b_fail = matches!(&vb, Some(f) if f[0] == "fail");
    let mut mode: u8 = if !a_fail && b_fail && matches!(ra0, Res::Line(_)) { 1 } else { 0 };
    let (mut ra, mut v) = if mode == 1 { (rb0, vb) } else { (ra0, va) };
    let mut lines = lines;
    // unsafe re-run (half the passing cases): the lines that raised nothing
    // in safe mode, under (#%declare #:unsafe); syntax.scrbl leaves only
    // evaluations that should have raised exn:fail:contract unspecified
    if mode == 0 && matches!(&v, Some(f) if f[0] == "pass") && mix(rseed, 5) % 2 == 0 {
        let errs: Vec<usize> = v.as_ref().unwrap().get(1).map(|e| e.split(',').filter_map(|x| x.parse().ok()).collect()).unwrap_or_default();
        lines.retain(|(i, _)| !errs.contains(i));
        let t = num::render_numprog(&lines);
        let (rc, vc) = num_query(pair, nc, &t, 2);
        *extra.entry("numref_unsafe".into()).or_insert(0) += 1;
        if matches!(&vc, Some(f) if f[0] == "fail") || matches!(rc, Res::Died(_)) {
            mode = 2; ra = rc; v = vc;
        }
    }
    let text = num::render_numprog(&lines);
    *extra.entry("numref_cases".into()).or_insert(0) += 1;
    match (&ra, &v) {
        (Res::Died(_), _) => {
            // a crash on a numeric program: confirm once, then record whole
            let (rb, _) = num_query(pair, nc, &text, mode);
            if matches!(rb, Res::Died(_)) {
                search.record_num(&text, if mode == 2 { "udied" } else { "died" }, "program", &res_text(&rb), &format!("{rseed}"));
                return true;
            }
            *extra.entry("numref_died_flaky".into()).or_insert(0) += 1;
            false
        }
        (Res::Hung, _) => { *extra.entry("numref_hung".into()).or_insert(0) += 1; false }
        (_, None) => { *extra.entry("numref_py_lost".into()).or_insert(0) += 1; false }
        (Res::Line(_), Some(f)) => match f[0].as_str() {
            "pass" => { *extra.entry("numref_pass".into()).or_insert(0) += 1; false }
            "skip" => { *extra.entry("numref_skip".into()).or_insert(0) += 1; false }
            "gen" => {
                *extra.entry("numref_gen_errors".into()).or_insert(0) += 1;
                if std::env::var("RKTGEN_NUM_DEBUG").is_ok() { eprintln!("numref gen: {:?}\n{text}", f); }
                false
            }
            "fail" => {
                let kind: &'static str = match (mode, f[1] == "error") {
                    (0, true) => "error", (0, false) => "value", (1, true) => "ierror", (1, false) => "ivalue",
                    (_, true) => "uerror", (_, false) => "uvalue" };
                let pk: &str = if f[1] == "error" { "error" } else { "value" };
                let idx: usize = f[2].parse().unwrap_or(0);
                let Some(pos) = lines.iter().position(|(i, _)| *i == idx) else { return false };
                // shrink: the failing line alone, then greedy one-step simplifications
                let mut cur = lines[pos].1.clone();
                let one = num::render_numprog(&[(idx, cur.clone())]);
                let (r1, v1) = num_query(pair, nc, &one, mode);
                let still = |v: &Option<Vec<String>>| matches!(v, Some(f) if f[0] == "fail" && f[1] == pk);
                let shrinkable = still(&v1);
                let (mut best_text, mut best_r, mut best_v) = if shrinkable { (one, r1, v1) } else { (text.clone(), ra.clone(), v.clone()) };
                if shrinkable {
                    let mut steps = 0;
                    'outer: while steps < 120 {
                        for c in num::shrink_candidates(&cur) {
                            steps += 1;
                            if steps >= 120 { break 'outer; }
                            let t = num::render_numprog(&[(idx, c.clone())]);
                            if t.len() >= best_text.len() { continue; }
                            let (rc, vc) = num_query(pair, nc, &t, mode);
                            if still(&vc) {
                                cur = c; best_text = t; best_r = rc; best_v = vc;
                                continue 'outer;
                            }
                        }
                        break;
                    }
                }
                let bv = best_v.unwrap();
                let area = bv.get(3).cloned().unwrap_or_else(|| "num".into());
                let msg = format!("{}\n{}: {}", bv.get(4).cloned().unwrap_or_default(), ["machine-code", "interpreter (PLT_CS_INTERP=1)", "machine-code, (#%declare #:unsafe)"][mode as usize], res_text(&best_r));
                *extra.entry(format!("fail_numref_{kind}")).or_insert(0) += 1;
                search.record_num(&best_text, kind, &area, &msg, &format!("{rseed}"));
                true
            }
            _ => false,
        },
    }
}

impl Search {
    fn record_num(&mut self, prog: &str, kind: &str, area: &str, msg: &str, seed_label: &str) {
        let sig = format!("numref__{kind}__{area}");
        let cnt = self.per_sig.entry(sig.clone()).or_insert(0);
        if *cnt >= 3 { return; }
        *cnt += 1;
        let dir = self.out.join("findings").join(&sig).join(cnt.to_string());
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("prog.rkt"), prog).unwrap();
        std::fs::copy(&self.runner_src, dir.join("runner.rkt")).unwrap();
        std::fs::copy(self.runner_src.with_file_name("numref.py"), dir.join("numref.py")).unwrap();
        std::fs::write(dir.join("results.txt"), msg).unwrap();
        let fj = format!("{{\"signature\": {}, \"oracle\": \"numref\", \"message\": {}, \"seed\": {}}}\n",
                         json_str(&sig), json_str(&msg.chars().take(3000).collect::<String>()), json_str(seed_label));
        std::fs::write(dir.join("finding.json"), fj).unwrap();
        let rp = dir.join("repro.sh");
        std::fs::write(&rp, REPRO_NUMREF.replace("@SIG@", &sig).replace("@KIND@", kind)).unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&rp, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("sample") => {
            let seed: u64 = args[2].parse().unwrap();
            let n: u64 = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(1);
            for i in 0..n {
                let mut src = ephyra::Source::new(mix(seed, i), 10);
                let p = ephyra::Gen::generate(&ProgramGen, &mut src);
                println!(";; case {seed}:{i}\n{}", render_program(&p.0));
            }
        }
        Some("numsample") => {
            let seed: u64 = args[2].parse().unwrap();
            let mut g = num::NumGen::new(seed);
            let lines: Vec<(usize, num::Line)> = g.program().into_iter().enumerate().collect();
            print!("{}", num::render_numprog(&lines));
        }
        Some("norm93") => {
            // rktgen norm93 <prog.rkt>: result lines on stdin -> ref93 comparison form
            let prog = std::fs::read_to_string(&args[2]).unwrap();
            for l in std::io::stdin().lock().lines() {
                println!("{}", norm93(&l.unwrap(), &prog));
            }
        }
        Some("run") => {
            let build = PathBuf::from(&args[2]);
            let seed: u64 = args[3].parse().unwrap();
            let secs: u64 = args[4].parse().unwrap();
            let out = PathBuf::from(&args[5]);
            std::fs::create_dir_all(out.join("findings")).unwrap();
            let racket = build.join("src/racket/bin/racket");
            let runner = build.join("harness/runner.rkt");
            let t0 = Instant::now();
            let deadline = t0 + Duration::from_secs(secs);
            let r93 = build.join("ref93/racket/bin/racket");
            let run93 = build.join("harness93/runner.rkt");
            let ref93 = if r93.exists() && run93.exists() { Some((r93, run93)) } else { None };
            let pair = RefCell::new(Pair::new(racket, runner.clone(), ref93));
            let last: RefCell<Option<Last>> = RefCell::new(None);
            let variant: std::cell::Cell<&'static str> = std::cell::Cell::new(VARIANTS[0]);
            let mut search = Search { out: out.clone(), runner_src: runner, per_sig: HashMap::new(), shrinks_per_kind: HashMap::new() };
            let mut extra: BTreeMap<String, u64> = BTreeMap::new();
            let pyscript = build.join("harness/numref.py");
            let mut numctx = if pyscript.exists() { Some(NumCtx { py: spawn_py(&pyscript), script: pyscript.clone() }) } else { None };
            let (mut cases, mut failures) = (0u64, 0u64);
            let only_variants: Option<Vec<&'static str>> = std::env::var("RKTGEN_VARIANTS").ok().map(|l| {
                l.split(',').filter_map(|x| VARIANTS.iter().copied().find(|v| *v == x)).collect::<Vec<_>>()
            }).filter(|l| !l.is_empty());
            let mut last_write = Instant::now();
            write_stats(&out, 0, 0, &extra, 0.0);
            let property = |p: Program| -> TestResult {
                let var = variant.get();
                let text = render_program(&p.0);
                let (a, b, c) = pair.borrow_mut().query(&text, var);
                let v = classify_all(&a, &b, &c, var, &text);
                let detail = format!("machine={} interp={} variant {var}={}", res_text(&a), res_text(&b),
                                     c.as_ref().map(res_text).unwrap_or_default());
                *last.borrow_mut() = Some(Last { verdict: v.clone(), a, b, c });
                match &v {
                    Verdict::Pass => TestResult::check(true, ""),
                    // timeouts/oom: not comparable (documented in README)
                    Verdict::Skip(r) => TestResult::discard(*r),
                    Verdict::Fail(..) => {
                        fail_at(&v, &detail);
                        unreachable!()
                    }
                }
            };
            // Segments: one ephyra Run each; a Run stops at its first
            // failure, which is shrunk by ephyra and written as a finding.
            let mut segment = 0u64;
            while Instant::now() < deadline {
                let left = deadline.saturating_duration_since(Instant::now());
                let mut cfg = Config::default()
                    .tests(1_000_000_000)
                    .seed(mix(seed, 1_000_000 + segment))
                    .name("racket_machine_vs_interp")
                    .budget(left)
                    .no_regressions();
                cfg.max_discard_ratio = 1e9;
                cfg.shrink.max_steps = 600;
                cfg.shrink.timeout_ms = Some(left.min(Duration::from_secs(90)).as_millis() as u64);
                cfg.locate.enabled = false;
                let seg_seed = cfg.seed.unwrap();
                segment += 1;
                let mut run = Run::new(&cfg, ProgramGen, &property);
                let mut failed: Option<(Program, Verdict, Res, Res, Option<Res>, u64)> = None;
                while run.wants_more() && Instant::now() < deadline {
                    // numref (steering round 14): a fifth of the cases, outside ephyra
                    if let Some(nc) = numctx.as_mut() {
                        if mix(seed, 9_100_000 + cases) % 5 == 0 {
                            let failed = numref_case(&mut pair.borrow_mut(), nc, mix(seed, 9_200_000 + cases), &mut search, &mut extra);
                            cases += 1;
                            if failed { failures += 1; }
                            if last_write.elapsed() > Duration::from_secs(5) {
                                last_write = Instant::now();
                                write_stats(&out, cases, failures, &extra, cases as f64 / t0.elapsed().as_secs_f64());
                            }
                            continue;
                        }
                    }
                    let Some(input) = run.draw() else { continue };
                    let iter = input.iteration();
                    // one variant per drawn case; unchanged while it is shrunk
                    let mut v = VARIANT_DRAW[(mix(seed, 7_000_000 + cases) % VARIANT_DRAW.len() as u64) as usize];
                    // probes: RKTGEN_VARIANTS=a,b,c restricts the draw (unset in the search)
                    if let Some(only) = &only_variants {
                        v = only[(mix(seed, 7_100_000 + cases) % only.len() as u64) as usize];
                    }
                    // port variants only change programs with string/bytes ports
                    if v.starts_with("port") && !render_program(&input.value.0).contains("(open-") {
                        v = "opaque";
                    }
                    variant.set(v);
                    let tested = run.test(&input);
                    cases += 1;
                    let l = last.borrow_mut().take();
                    if let Some(Last { verdict, a, b, c }) = l {
                        let var = variant.get();
                        match &c {
                            Some(_) => *extra.entry(format!("variant_cmp_{var}")).or_insert(0) += 1,
                            None if var == "unsafe" => *extra.entry("unsafe_ineligible".into()).or_insert(0) += 1,
                            None => {}
                        }
                        if let Res::Line(l) = &a {
                            *extra.entry(format!("result_{}", kind_of(l))).or_insert(0) += 1;
                            if l.contains("exn:fail:syntax") || l.contains("exn:fail:read") {
                                // generator bug indicator: should stay 0
                                *extra.entry("gen_syntax_errors".into()).or_insert(0) += 1;
                            }
                            *extra.entry("stmt_errors".into()).or_insert(0) += l.matches("(exn ").count() as u64;
                            *extra.entry("masked_nonfx_msg".into()).or_insert(0) += l.matches("masked").count() as u64;
                        }
                        match &verdict {
                            Verdict::Skip(r) => *extra.entry(format!("skip_{r}")).or_insert(0) += 1,
                            Verdict::Fail(o, k) => {
                                *extra.entry(format!("fail_{o}_{k}")).or_insert(0) += 1;
                            }
                            Verdict::Pass => {}
                        }
                        if tested.failed() {
                            failures += 1;
                            failed = Some((input.value.clone(), verdict, a, b, c, iter));
                            break;
                        }
                    }
                    if last_write.elapsed() > Duration::from_secs(5) {
                        last_write = Instant::now();
                        extra.insert("server_restarts".into(), pair.borrow().restarts);
                        write_stats(&out, cases, failures, &extra, cases as f64 / t0.elapsed().as_secs_f64());
                    }
                }
                if let Some((orig, v, a, b, c, iter)) = failed {
                    let key = match &v {
                        Verdict::Fail(o, k) => format!("{o}__{k}"),
                        _ => String::new(),
                    };
                    let n = search.shrinks_per_kind.entry(key).or_insert(0);
                    *n += 1;
                    // hangs cost a timeout per shrink step; after 40 shrinks of one
                    // kind further failures are only counted.
                    let small = if *n <= 40 && !matches!(v, Verdict::Fail(_, "hang")) {
                        run.shrink().cloned().unwrap_or(orig.clone())
                    } else {
                        run.shrunk_to(orig.clone());
                        orig.clone()
                    };
                    if *n <= 40 {
                        let var = variant.get();
                        let text = render_program(&small.0);
                        let (ra, rb, rc) = pair.borrow_mut().query(&text, var);
                        let (ra, rb, rc) = if classify_all(&ra, &rb, &rc, var, &text) == v { (ra, rb, rc) } else { (a, b, c) };
                        search.record(&small, &v, &format!("{seg_seed}:{iter}"), &ra, &rb, &rc);
                    }
                }
                let _ = run.finish();
                extra.insert("server_restarts".into(), pair.borrow().restarts);
                extra.insert("segments".into(), segment);
                write_stats(&out, cases, failures, &extra, cases as f64 / t0.elapsed().as_secs_f64());
            }
            extra.insert("server_restarts".into(), pair.borrow().restarts);
            write_stats(&out, cases, failures, &extra, cases as f64 / t0.elapsed().as_secs_f64());
            pair.into_inner().close();
        }
        _ => {
            eprintln!("usage: rktgen run <build-dir> <seed> <seconds> <out-dir> | rktgen sample <seed> [n]");
            std::process::exit(2);
        }
    }
}
