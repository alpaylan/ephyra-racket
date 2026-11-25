# Racket CS harness: machine code vs interpreter

Layout:

- `build.sh <src> <build> [coverage]`: copies the tree to `<build>/src` (the Racket build writes inside
  its tree; rsync keeps mtimes so rebuilds are incremental), runs `make base CPUS=16 JOBS=16
  PKGS=racket-lib` there, builds the generator with cargo into `<build>/harness-target`, copies
  `racket/runner.rkt` to `<build>/harness/` and compiles it to a `.zo`.
- `run.sh <build> <seed> <seconds> <out>`: runs `<build>/harness-target/release/rktgen run ...`.
- `gen/` (Rust, ephyra): `src/gen.rs` is the program generator (`ProgramGen`, an `ephyra::Gen` with a
  scope-aware shrinker; `#[ephyra::generator(valid_program, metrics = program_metrics)] programs`),
  `src/main.rs` the search loop and oracles. `rktgen sample <seed> [n]` prints programs.
- `racket/runner.rkt`: `racket runner.rkt server` reads framed programs (`<nbytes>\n<text>`) and prints
  one result line each; `racket runner.rkt file prog.rkt` does one (used by `repro.sh`).

## What is generated

One `(module m racket/base ...)` per case: a fixed prelude (`racket/fixnum`, `racket/flonum`, a
mutable struct `pt`, module variables `mv`/`mf`, a parameter `prm`, `tap` which prints a marker to make
evaluation order observable, and `show` which prints a value or the error kind + first message line)
followed by 3-12 top-level items: `define`s of values and of functions with 0-3 typed parameters
(sometimes with an internal define), `define-values`, `set!` of module variables, `show`/`writeln` of
expressions, and calls of every defined function. Expressions are typed (fixnum-range/bignum integers,
flonums, booleans) and well scoped by construction; depth 2-5. Constructs: generic and `fx` arithmetic
(incl. wraparound, shifts, popcount), `fl` arithmetic (flmin/flmax n-ary, flround/floor/ceiling/
truncate, flsingle, flhypot, flbit-field, fl->fx, ...), conversions, comparisons, `if` with trivial arms
(cmov shapes), `cond`, `case`, `let`/`let*`/`letrec`, named-let flonum loops, `for/fold`, `for/sum`,
bounded local recursion via `letrec`, captured mutable locals, `set!`, unused local functions,
`call/ec`/`call/cc` escapes, `dynamic-wind`, `with-continuation-mark` + mark lookup, `parameterize`,
`with-handlers`, `let-values`/`call-with-values`, vectors, flvectors, structs, immutable hashes. Small
literal pools with edge values (0, -1, fixnum bounds, 2^62, -0.0, +-inf.0, +nan.0, subnormals,
2^53 +- 1, x.5 ties) so values collide. Loops are bounded (<= 6 iterations, nested by depth only).

`ephyra check` (`ephyra check --no-instrument` in `gen/`) passed: 10 000
values, all shrink candidates and mutants satisfy `valid_program` (every free name defined earlier).
Median program 103 nodes / 1.2 KB, median 2 loops, 4 ifs, 3 control forms.

## Oracles

1. **diff** (`diff__{value,error,errmsg}__<area>`): two long-lived `racket runner.rkt server`
   processes, one default (schemify + Chez machine code), one with `PLT_CS_INTERP=1` (schemify
   'interp target + the CS interpreter, racket/src/cs/linklet.sls). Each case is `eval`ed in a fresh
   namespace and instantiated; the result line (all printed output, then `ok`, or the uncaught exn's
   struct type + first message line) must be identical. Expected behaviour: compiler.scrbl says a
   module compiled in any mode can be loaded independently of the mode; nothing allows a mode to
   change results (universal: no wrong result). `value` = both ok, different output; `error` = only
   one raised or different exn type; `errmsg` = same exn type, different first line.
2. **crash** (`crash__{died,internal,hang}__<area>`): a server process dies (signal / exit without a
   result), a result mentions `internal error`, `invalid memory reference`, `Exception in `,
   `attempt to reference unbound`, `compile-time`, or the machine-code side times out (10 s) while
   the ~100x slower interpreter finished (a compile hang, cf. issue #5632).

3. **variant** (`<variant>__{value,error,errmsg,died,internal,hang}__<area>`, oracle = variant name):
   a third server, also machine code, compiles the same module with one optimizer toggle changed
   and must print the same result line as the default machine-code server. One variant per drawn
   case (`mix(seed, case)`), kept fixed while that case is shrunk; sent in the frame header
   (`<nbytes> <variant>`), applied by `runner.rkt` around the compile and restored after:
   - `unsafe`: `(#%declare #:unsafe)` after the module header (schemify `unsafe?`, Chez
     optimize-level 3, the unsafe cpprim inlines). syntax.scrbl: behaviour is unspecified only "for
     an evaluation where exn:fail:contract should have been raised", so the case is compared only
     when the default run is `ok` with no exception raised and caught anywhere (`show` prints
     `(exn ...`, the generated `with-handlers` handler now prints `caught ` via `tap`); otherwise it
     is not even sent (UB could corrupt the server). ~50% of cases are eligible.
   - `nocp0`: Chez `(run-cp0 (lambda (cp0 x) x))`; `notr`: `(enable-type-recovery #f)`;
     `cp0big`: `cp0-score-limit` 120, `cp0-effort-limit` 5000, `cp0-outer-unroll-limit` 2.
   - `ctx`: `compile-context-preservation-enabled #t` (schemify `inline?` #f; eval.scrbl: it only
     avoids optimizations that lose stack-trace information).
   - `noconst`: `compile-enforce-module-constants #f` (schemify's known-binding analysis).
   - `zo`: `compile` (serializable linklets), `write`, `read` back with `read-accept-compiled`,
     `eval` — the `raco make` path (serializable schemify, literal lifting, fasl of machine code).
   - `machind`: same with `current-compile-target-machine #f`, then
     `compiled-expression-recompile` (machine-independent form recompiled through schemify).
   A variant-side timeout where the default finished is `hang`. `repro.sh` for these runs
   `runner.rkt file prog.rkt none` and `... <variant>` and compares.

`<area>` is the highest-priority construct tag present in the shrunk program (priority list
`PRIORITY` in main.rs: control forms first, then specific primitives, then generic arithmetic). One
bug can therefore show up under a few areas when the shrinker cannot remove an incidental construct.

Search: ephyra `Run` segments: draw, test; the first failure ends the segment, is shrunk by ephyra
(each oracle kind panics at its own site, so shrinking keeps the kind; 600 steps / 90 s), re-checked,
written as a finding (max 3 per signature, max 40 shrinks per oracle kind per run), then a new segment
starts with a derived seed. `repro.sh` runs `prog.rkt` through its own copy of `runner.rkt` in both
modes against the given build and exits 1/0/2.

## Masked differences (each counted in stats.json)

- `masked_nonfx_msg`: the message of `exn:fail:contract:non-fixnum-result` differs by mode:
  machine code says `fx*: fixnum overflow with arguments 7 and 576...`, the interpreter
  `fx*: fixnum overflow computing '(fx* 7 576...)` (same in Racket 9.3). Wording is unspecified; the
  exception type is still compared. Masked in runner.rkt and in the prelude's `show`.
- `skip_*`: timeouts (`interp_timeout`, `both_timeout`), `oom` (2 GB custodian limit), and Rust-side
  no-reply (`hung`) are not compared; the case is an ephyra discard.
- Not generated at all (unspecified per the docs): `eq?` on numbers/chars/procedures, hash iteration
  order, printing of procedures, `object-name`, time, gensym.

## Stats keys

`cases`, `failures`, `cases_per_sec`, `result_{ok,exn,raise}` (machine-code side), `stmt_errors`
(errors caught by `show`), `gen_syntax_errors` (generator bugs; should be absent/0), `fail_*`,
`skip_*`, `masked_nonfx_msg`, `server_restarts`, `segments`.

## Throughput

~25 cases/s per run.sh alone (one pair of servers; the interpreter side dominates); ~19.7 cases/s each
with 6 run.sh in parallel (on a release build and a coverage build, 240 s each: 28 007 cases,
1 failure). That failure is real and pre-existing (also in 9.3): under `PLT_CS_INTERP=1`,
`(define (f a b c) (define w c) (if (begin (set! w w) #t) 0 0)) (f 0 #t 0.0)` raises
`hash-ref: no value found for key  key: 'w_4` (machine code returns 0).

## Coverage

`build.sh ... coverage` builds the C parts (Chez Scheme kernel `ChezScheme/c`, `rktio`, `start`) with
clang 21 `-fprofile-instr-generate -fcoverage-mapping`, plus `-fcoverage-prefix-map=<build>/src=<tree>`
so the coverage map names the tree's files. `coverage.json` lists the `racket` executable (it
statically links the kernel). Profiles of build-time runs go to `<build>/build-profraw` and are deleted.
Scheme-level code (schemify, expander, the Chez compiler passes where most bugs live) is not visible
to LLVM coverage; trunk has no Scheme-level coverage counters. A 30 s run reached 39% of
functions / 29% of lines of the instrumented C.
