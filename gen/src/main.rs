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
    let mut cmd = Command::new(racket);
    cmd.arg(runner).arg("server");
    cmd.env("RKT_CASE_TIMEOUT", CASE_TIMEOUT_S.to_string());
    if interp {
        cmd.env("PLT_CS_INTERP", "1");
    } else {
        cmd.env_remove("PLT_CS_INTERP");
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
    restarts: u64,
}

impl Pair {
    fn new(racket: PathBuf, runner: PathBuf) -> Pair {
        let a = spawn_server(&racket, &runner, false);
        let b = spawn_server(&racket, &runner, true);
        Pair { racket, runner, a, b, restarts: 0 }
    }
    fn send(s: &mut Server, prog: &str) -> bool {
        let msg = format!("{}\n{}", prog.len(), prog);
        s.stdin.write_all(msg.as_bytes()).and_then(|_| s.stdin.flush()).is_ok()
    }
    fn recv(s: &mut Server, sent: bool, limit: Duration) -> Res {
        if !sent {
            return Res::Died(Self::death(s));
        }
        match s.rx.recv_timeout(limit) {
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
    fn query(&mut self, prog: &str) -> (Res, Res) {
        let lim = Duration::from_secs(CASE_TIMEOUT_S + 30);
        // Send to both first so they run in parallel.
        let sa = Self::send(&mut self.a, prog);
        let sb = Self::send(&mut self.b, prog);
        let ra = Self::recv(&mut self.a, sa, lim);
        let rb = Self::recv(&mut self.b, sb, lim);
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
        (ra, rb)
    }
    fn close(mut self) {
        drop(self.a.stdin);
        drop(self.b.stdin);
        for c in [&mut self.a.child, &mut self.b.child] {
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

const PRIORITY: &[&str] = &[
    "escape", "dynamic-wind", "wcm", "parameterize", "handlers", "closure-set", "unused-fn",
    "letrec-loop", "fl-loop", "for-fold", "for-sum", "values", "struct-mutate", "struct",
    "vector-mutate", "vector", "flvector", "hash", "flbit-field", "flround", "flmin-max", "fl->int",
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

struct Search {
    out: PathBuf,
    runner_src: PathBuf,
    per_sig: HashMap<String, usize>,
    shrinks_per_kind: HashMap<String, usize>,
}

impl Search {
    /// Write a finding for the (already shrunk) program; `ra`/`rb` are its results.
    fn record(&mut self, small: &Program, v: &Verdict, seed_label: &str, ra: &Res, rb: &Res) {
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
        let msg = format!("machine-code: {}\ninterpreter:  {}", res_text(ra), res_text(rb));
        std::fs::write(dir.join("results.txt"), &msg).unwrap();
        let fj = format!(
            "{{\"signature\": {}, \"oracle\": {}, \"message\": {}, \"seed\": {}}}\n",
            json_str(&sig),
            json_str(oracle),
            json_str(&msg.chars().take(3000).collect::<String>()),
            json_str(seed_label)
        );
        std::fs::write(dir.join("finding.json"), fj).unwrap();
        let rs = REPRO.replace("@SIG@", &sig).replace("@ORACLE@", oracle).replace("@KIND@", kind);
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
        Verdict::Fail(o, k) => panic!("{o} {k}: {detail}"),
        _ => {}
    }
}

/// Last property evaluation, read by the search loop after `run.test`.
struct Last {
    verdict: Verdict,
    a: Res,
    b: Res,
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
            let pair = RefCell::new(Pair::new(racket, runner.clone()));
            let last: RefCell<Option<Last>> = RefCell::new(None);
            let mut search = Search { out: out.clone(), runner_src: runner, per_sig: HashMap::new(), shrinks_per_kind: HashMap::new() };
            let mut extra: BTreeMap<String, u64> = BTreeMap::new();
            let (mut cases, mut failures) = (0u64, 0u64);
            let mut last_write = Instant::now();
            write_stats(&out, 0, 0, &extra, 0.0);
            let property = |p: Program| -> TestResult {
                let (a, b) = pair.borrow_mut().query(&render_program(&p.0));
                let v = classify(&a, &b);
                let detail = format!("machine={} interp={}", res_text(&a), res_text(&b));
                *last.borrow_mut() = Some(Last { verdict: v.clone(), a, b });
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
                let mut failed: Option<(Program, Verdict, Res, Res, u64)> = None;
                while run.wants_more() && Instant::now() < deadline {
                    let Some(input) = run.draw() else { continue };
                    let iter = input.iteration();
                    let tested = run.test(&input);
                    cases += 1;
                    let l = last.borrow_mut().take();
                    if let Some(Last { verdict, a, b }) = l {
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
                            failed = Some((input.value.clone(), verdict, a, b, iter));
                            break;
                        }
                    }
                    if last_write.elapsed() > Duration::from_secs(5) {
                        last_write = Instant::now();
                        extra.insert("server_restarts".into(), pair.borrow().restarts);
                        write_stats(&out, cases, failures, &extra, cases as f64 / t0.elapsed().as_secs_f64());
                    }
                }
                if let Some((orig, v, a, b, iter)) = failed {
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
                        let (ra, rb) = pair.borrow_mut().query(&render_program(&small.0));
                        let (ra, rb) = if classify(&ra, &rb) == v { (ra, rb) } else { (a, b) };
                        search.record(&small, &v, &format!("{seg_seed}:{iter}"), &ra, &rb);
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
