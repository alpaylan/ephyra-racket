# ephyra-racket: property-based differential testing of Racket CS

A harness that generates well-formed Racket modules and checks that Racket CS gives the same
result when the same module is run in ways that must agree: machine code vs. the interpreter
(`PLT_CS_INTERP=1`), optimizer toggles, `.zo` round trips, splitting a module into two (cross-module
inlining), rewriting it through hygienic macros, GC stress, and more. Programs are generated and shrunk
with [Ephyra](https://github.com/datadog-labs/ephyra), a property-based testing library for Rust.

The generator and oracles were written by an automated agent loop driving Ephyra, seeded with the
oracle ideas of [racket-fuzz](https://github.com/samth/racket-fuzz) (no code is shared with it).

## Bugs found

- [racket/racket#5688](https://github.com/racket/racket/issues/5688): schemify: inlined function loses
  `set!` of a `let`-bound copy of its argument
- [racket/racket#5689](https://github.com/racket/racket/issues/5689): schemify: cross-module inlining
  loses `set!` of the inlined function's argument
- [racket/racket#5690](https://github.com/racket/racket/issues/5690): re-entering a continuation
  captured inside `fl+` mutates the flonum returned the first time

## Quick start

Requirements: Rust (`cargo`), a C toolchain, `make`, `rsync`, and network access once (the Racket
build fetches its portable-bytecode boot files). Linux x86_64 is what it has been run on.

```
git clone https://github.com/racket/racket
./build.sh racket build          # minimal Racket CS in build/src, the generator in build/harness-target
./run.sh build 1 600 out         # seed 1, 600 seconds
cat out/stats.json; ls out/findings
```

`build.sh <racket-tree> <build-dir> [coverage]` copies the tree to `<build-dir>/src` (the Racket build
writes inside its tree; rsync keeps mtimes, so rebuilds are incremental), runs
`make base PKGS=racket-lib` there (`CPUS`/`JOBS`, default 16), builds the generator with cargo, and
compiles `racket/runner.rkt` to a `.zo`. With `coverage` it builds the C parts with clang source-based
coverage instead (`LLVM_BIN`, default `/usr/lib/llvm-21/bin`; see Coverage below).

`run.sh <build-dir> <seed> <seconds> <out-dir>` runs one search process. It writes
`<out-dir>/stats.json` (updated periodically) and, for each failure, after shrinking,
`<out-dir>/findings/<signature>/<n>/` with `prog.rkt` (the shrunk module), `finding.json` (signature,
oracle, message, seed), `results.txt` (the two result lines that differ), a copy of `runner.rkt`,
and `repro.sh`: `./repro.sh <build-dir>` re-runs the
case in both configurations and exits 1 if they still differ, 0 if not, 2 if it cannot tell. At most 3
findings are kept per signature. Several `run.sh` processes with different seeds can share one build.

`gen/target/release/rktgen sample <seed> [n]` (after `cargo build --release` in `gen/`) prints generated
programs without running anything.

## Layout

- `gen/` (Rust, Ephyra): `src/gen.rs` is the program generator (`ProgramGen`, an `ephyra::Gen` with a
  scope-aware shrinker; `#[ephyra::generator(valid_program, metrics = program_metrics)] programs`),
  `src/main.rs` the search loop and oracles.
- `racket/runner.rkt`: `racket runner.rkt server` reads framed programs (`<nbytes>\n<text>`) and prints
  one result line each; `racket runner.rkt file prog.rkt [variant]` runs one (used by `repro.sh`);
  `splitdump` and `macrodump` print the rewritten modules of the metamorphic variants.
- `build.sh`, `run.sh`: above.

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

### Delimited control

`Gen::delim` (4% of control choices, taken from `if`): `call-with-continuation-prompt` with fresh
tags (explicit handler) or the default tag (default handler), `abort-current-continuation` to them,
optionally through `dynamic-wind` (printing `in`/`out`); composable continuations captured inside a
prompt (optionally under a mark) and applied twice after the prompt returned; full continuations
(`call/cc`) re-entered 1-3 more times through a `set!`-ed local; marks seen through prompts:
`continuation-mark-set->list`/`-first` with a prompt tag, `call-with-immediate-continuation-mark`,
and the shape of issue #5658 (a composable continuation captured under a mark, aborted out of and
re-applied in a new prompt). Area tags `composable`, `reentry`, `marks-tag`, `prompt` (first in
PRIORITY).

### Dynamic kind (`Val`)

Besides the typed int/flonum/boolean expressions, a dynamically typed kind `Val` mixes fixnums,
bignums, flonums, booleans, pairs/lists, `'()`, strings, chars, symbols, vectors, boxes and void
(`val_op`, `val_to_int` in gen.rs). Constructs: `cons`/`list`/`list*`, `pair?`-guarded `car`/`cdr`,
`reverse`/`append`/`member`/`length` behind `list?`, a bounded cdr-walking loop, mixed-type `if` arms,
`case` on symbols/chars/strings/`()` (equal?), boxes, vectors holding any value, char/string/symbol
conversions, and type dispatch (`cond` over `fixnum?`/`flonum?`/`pair?`/`string?`/... with
type-specific operations in each arm) plus type predicates and `equal?` as booleans. Function
parameters, returns, `let` bindings and `set!` targets can be `Val`, so one function sees arguments of
several types (Chez cptypes type recovery, schemify's known-type info, the `notr` variant). Val is
woven in at ~5-15% of the int/fl/bool choices so old shapes stay reachable. Only `equal?` is used on
Val (eq?/eqv? on strings, chars and quoted literals is unspecified). New area tags (PRIORITY):
`type-dispatch`, `type-guard`, `pair-guard`, `case-any`, `box`, `vector-any`, `list-op`, `if-mixed`,
`char`, `symbol`, `type-pred`, `equal`, `pair`.

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
   - `jitify`: a fourth server (started on first use) with `PLT_CS_COMPILE_LIMIT=10`, so every
     module is a "large linklet": schemify's jitify mode (schemify/jitify.rkt), only interior
     functions compiled, the outer body interpreted — the path real modules over 10 000 terms take.
   - `split`, `splitzo`, `splitmi` (metamorphic, runner.rkt `split-module`): the module is split
     after its last definition into a provider `(module a racket/base (provide (all-defined-out))
     <prelude> <items up to the last define>)` and the client `(module m racket/base <requires>
     (require 'a) <remaining items>)` — mostly the calls of every defined function, so they become
     cross-module calls (schemify's imported known info: known.rkt, find-known.rkt, known-copy.rkt,
     cross-module inlining of small functions, struct `pt` accessors, constants). A client cannot
     `set!` an imported variable, so `(set! x e)` in `m` becomes `(x:set e)` with
     `(define (x:set v) (set! x v))` added to `a` (generated names are unique, so this is syntactic;
     `set!` and the setter both return void). `a`'s body runs to completion before `m`'s, in the
     original order, so output and results must equal the single module's. `split` evals both
     in-memory, `splitzo` compiles each, writes and reads it back (the known/inline info serialized
     in the .zo, the `raco make` path), `splitmi` compiles each machine-independent and recompiles.
     `racket runner.rkt splitdump prog.rkt` prints the two modules. The split variants get ~half of
     the drawn cases (`VARIANT_DRAW` in main.rs). 30% of generated functions get a small body
     (depth 1-2) so they are under the inlining size limits.
   - `macro`, `macrozo`, `macrosplit` (metamorphic, runner.rkt `macro-module`,
     `macro-split`): the generated items are rewritten through hygienic macros defined in the module
     (expander: scope sets, re-represented as sorted lists with a Zobrist hash in f1a34e208d,
     2026-11-16; binding resolution, use-site scopes, serialization of syntax). Each macro expands to
     the form it replaces plus bindings user code cannot see; the introduced binders deliberately reuse
     the program's own variable names, `tap`, `mv` and `tmp`, and every template keeps the user
     expression in tail position (marks, tail calls unchanged). Rewrites (each site with some
     probability, a deterministic function of the program text): `if`→`m-if` (made by a
     macro-defining macro), application→`m-app` (macro-defining macro with `(... ...)`) or `m-app2`
     (syntax-case, `generate-temporaries`), `let`/`let*`/named let/`lambda`/`set!` wrappers,
     module-level and internal `define`→`m-def`/`m-define` (macro uses that produce definitions next
     to a hygienically introduced definition of a colliding name), `m-deep k e` (a recursive macro
     wrapping an argument in k ≤ 40 lets: large scope sets), `m-tap` (rebinding `tap`/`mv`/`tmp`
     around user code), and function parameters replaced by `define-syntax` +
     `make-set!-transformer` macros in the function body (internal-definition context). Only forms
     whose grammar the rewriter knows are rewritten; unknown forms are left alone. Expected: macro
     expansion is semantics-preserving and hygienic (reference/syntax-model.scrbl), so output must
     equal the unrewritten module's. `macro` evals in-memory, `macrozo` compiles + writes + reads
     back, `macrosplit` splits (as `split`), rewrites both modules with the macros defined in `a`
     (exported by `all-defined-out`) and round-trips each through a .zo, so `m` expands against
     deserialized macros; `macrosub` puts the client part into a `(module* sub #f ...)` submodule of
     the provider (enclosing bindings and macros through a shifted module path index), zo round
     trip, then instantiates `(submod 'm sub)`. Also in `wrap-arg`: `m-flip` (a
     `make-syntax-introducer` applied twice), `m-lintro` (`syntax-local-introduce` twice),
     `m-reflect` (`datum->syntax` from the argument's own uniform context), `m-lexp`/`m-lexp-stop`
     (`local-expand` of the argument to core forms, or with a stop list, then re-expanded).
     `racket runner.rkt macrodump prog.rkt <variant>` prints the rewritten
     module(s). They get a third of the drawn cases.
   - `opaque`, `opaquesplit` (metamorphic, runner.rkt `opaque-module`): selected
     sites are wrapped in `(opq-v e)`, `opq-v` a module variable holding the identity that is
     `set!` once, so schemify and Chez cp0/cptypes cannot see through it: literals stop being
     constants, variable references lose known values/types, `(f a ...)` becomes `((opq-v f) a ...)`
     (no inlining or known call; for a primitive the out-of-line library procedure instead of the
     inline cpprim code), `if`/`cond`/`case` tests cannot be folded. Only single-valued, non-tail
     positions are wrapped (arguments, tests, non-lambda right-hand sides) and callees keep tail
     position, so marks and tail calls are unchanged. Densities per program (deterministic in the
     text). `opaquesplit` splits the rewritten module (in-memory).
   - `ctlnoise`, `ctlsplit`: the same sites wrapped in control forms that are the identity — a
     prompt with a tag only the wrappers use, an abort to such a prompt whose handler evaluates the
     expression, `dynamic-wind` with `void` thunks, application of an empty composable continuation
     (rumble control.ss metacontinuation frames, mark splices, winders). `ctlsplit` = split + zo.
     `racket runner.rkt macrodump prog.rkt <variant>` prints the rewritten module(s) for all four.
     The opaque/ctl variants get about a third of the drawn cases.
   - `gc`, `gczo`, `gcsplit` (metamorphic, runner.rkt `gc-module`,
     `set-gc-knobs!`): garbage collection must not change results. They run on a fifth server
     (`e` in main.rs, started on first use) because the runner starts a background place there
     (a second Chez thread with `thread-preserve-ownership!`, rumble place.ss), which makes Chez
     use the parallel collector (`gc-par.inc`, never entered before). The opaque sites are
     wrapped in `(gc-v e)`: the value is kept in a 5000-slot (large-object) vector together with a
     weak box and an ephemeron, or every 5th time a captured, never-invoked full continuation and
     the current marks; the cell is a key of a `make-hasheq` and a `make-weak-hasheq` table; then
     `(collect-garbage 'minor)` (every 97th call, up to 4 times, `'major`); then a cell kept 3
     calls earlier must still be found in both tables with its number, else
     `internal error: kept key lost ...` is raised (address-hashed tables are rehashed when keys
     move; universal: no data loss). Per case (deterministic in the text): `collect-trip-bytes`
     64 KB-4 MB (collections at arbitrary allocation points, also inside the expander, schemify,
     the Chez compiler and the fasl reader), `in-place-minimum-generation` 0/1/default (marking
     in place instead of copying; cf. 6e3d35902a), object counts on for 1/4 (`gc-oce.inc`), and
     for 1/16 a Chez heap check after the case (`$enable-check-heap` + a minor collection; any
     `$check-heap-errors` increase becomes an `exn` line with `internal error: N Chez heap check
     errors`, oracle kind `internal`). `gczo` = compile + zo round trip, `gcsplit` = split + zo
     round trip of each module. `racket runner.rkt macrodump prog.rkt gc` prints the rewrite.
     The place (`gc-worker` submodule, started with `dynamic-place` so the runner's command-line
     dispatch does not run in it) keeps 4000 cells of its own (vector, flonum, list, bytes, box
     of a bignum), each a key of an eq?-table, replaces ~40 random cells every 2 ms, and after
     every gc-variant case is asked to verify all cells and table entries; a failure becomes
     `internal error: the background place's heap is damaged after the case`.
     They get about a quarter of the drawn cases. Cost: ~0.17-0.22 s per case vs 0.06 s default.
     A 25-program probe on the coverage build reached +12 000 C regions (gc.c, gc-par.inc,
     gc-oce.inc) over the cumulative profile.
   - `ref93` (second reference, steering round 7): the same module, variant `none`, on a sixth
     server (`f`, started on first use) running the released **Racket 9.3 CS** (minimal),
     which build.sh copies into `<build>/ref93` (from `$REF93_SRC` or the tarball `$REF93_TGZ` if set, else
     download.racket-lang.org) with the runner compiled by it in `<build>/harness93`. Compared
     only when trunk machine code and the trunk interpreter agree (otherwise the `diff` oracle
     owns the case), so a difference lies in code both trunk modes share — the rumble/Chez
     libraries compiled by the changed Chez compiler (cmov pass 5d5568ec15, branchless
     flmin/flmax, flround instructions, fxbit-count inline), schemify, the expander (scope
     sets), io — or is a documented change since 9.3. Comparison form (`norm93`, mirrored in
     the repro's python): error-message texts dropped (inside `show` output and the final exn
     line; struct type and `show`'s kind stay), and when the program uses min/max the sign of
     zero is ignored (05afec9201 documents flmax's changed -0.0 result). Not compared: 9.3
     crashes/hangs/internal errors (9.3's problems), programs using names 9.3 lacks
     (`NEW_SINCE_93`, e.g. `flhypot`; also any 9.3 unbound-identifier/syntax error), and
     differing programs that capture continuations (9.3 has the unboxed-flonum continuation
     bug fixed by patch 003). Kinds: `ref93__value__*`, `ref93__error__*`. **Triage every
     ref93 finding against `git log v9.3..HEAD`** (regexp repairs, expt with
     most-negative-fixnum, log1+/atanh accuracy, Unicode 18, struct field limit, reader `#s`)
     before calling it a regression; also check whether trunk or 9.3 is the one that is wrong.
     About 1/5 of drawn cases.
     To give this oracle shared library code to check, the generator got **library primitives**
     (gen.rs `lib_op`, ~30% of `Val` expressions and 5% of typed ones via `lib_typed`): exact
     rationals and complex numbers (`/`, `expt`, `sqrt`/`exp`/`log`/trig, `make-polar`,
     `rationalize`, `exact->inexact` of large rationals, `integer-sqrt/remainder`,
     `bitwise-bit-field`, big shifts, exact/inexact comparisons), `number->string` (radix) and
     `string->number` on a pool of tricky notations, round trips; strings with Unicode special
     casing (ß, final sigma, İ, ǅ, ﬁ, combining marks) through up/down/fold/titlecase and the
     four normalizations, string/char comparisons and `char-general-category` etc., UTF-8 and
     Latin-1 bytes conversions with invalid sequences, symbols/keywords, simple regexps
     (match, positions, split, replace), printing to string ports (`write`/`display`/`print`,
     `format` directives) and reading back, `sort`/`foldl`/`assv`/`member` on numeric lists,
     mutable (`make-hash`/`hasheqv`/`hashalw`) and immutable hash tables (count/ref/update/remove,
     `equal?` of hashes; never iteration order). Area tags `lib-num`, `lib-numstr`, `lib-cmp`,
     `lib-string`, `lib-char`, `lib-bytes`, `lib-symbol`, `lib-regexp`, `lib-print`, `lib-list`,
     `lib-hash`, `lib-typed`.
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
1 failure). That failure is real and pre-existing (also in 9.3; racket/racket#5688): under `PLT_CS_INTERP=1`,
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
