# ephyra-racket: property-based differential testing of Racket CS

A harness that generates well-formed Racket modules and checks that Racket CS gives the same
result when the same module is run in ways that must agree: machine code vs. the interpreter
(`PLT_CS_INTERP=1`), optimizer toggles, `.zo` round trips, splitting a module into two (cross-module
inlining), rewriting it through hygienic macros, GC stress, thread preemption, and the released
Racket 9.3 as a second reference. Programs are generated and shrunk
with [Ephyra](https://github.com/datadog-labs/ephyra), a property-based testing library for Rust.

The generator and oracles were written by an automated agent loop driving Ephyra, seeded with the
oracle ideas of [racket-fuzz](https://github.com/samth/racket-fuzz) (no code is shared with it).

## Bugs found

- [racket/racket#5688](https://github.com/racket/racket/issues/5688) (fixed): schemify: inlined
  function loses `set!` of a `let`-bound copy of its argument
- [racket/racket#5689](https://github.com/racket/racket/issues/5689) (fixed): schemify: cross-module
  inlining loses `set!` of the inlined function's argument
- [racket/racket#5690](https://github.com/racket/racket/issues/5690): re-entering a continuation
  captured inside `fl+` mutates the flonum returned the first time
- [racket/racket#5692](https://github.com/racket/racket/issues/5692): compiled `even?`/`odd?` on a
  non-integer flonum reports `fleven?`/`flodd?` instead of `even?`/`odd?`
- [racket/racket#5695](https://github.com/racket/racket/issues/5695): `=` raises "no exact
  representation" for a fixnum above 2^53 and an inexact complex with an infinite or NaN part

## Quick start

Requirements: Rust (`cargo`), a C toolchain, `make`, `rsync`, `curl`, `python3` (the `ref93`
findings' `repro.sh` uses it), and network access at build time: the Racket build fetches its
portable-bytecode boot files, and `build.sh` downloads the Racket 9.3 minimal release for the `ref93`
variant (or set `REF93_SRC` to an installed 9.3 tree, or `REF93_TGZ` to its tarball). Linux x86_64 is
what it has been run on.

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
     zero is ignored (05afec9201 documents flmax's changed -0.0 result), and with flmax also
     the sign of infinity (that zero reaches it through division). Not compared: 9.3
     crashes/hangs/internal errors (9.3's problems), programs using names 9.3 lacks
     (`NEW_SINCE_93`, e.g. `flhypot`; also any 9.3 unbound-identifier/syntax error), and
     differing programs that capture continuations (9.3 has the unboxed-flonum continuation
     bug fixed by patch 003), and known 9.3 bugs repaired in trunk that the generator hits
     (`skip_ref93_known_*`: programs with an unused local function, 8f67966b14; a 9.3-only
     "cannot modify a constant", schemify mutation tracking 0cd7dd3cc0/bc1b6eb434 — generated
     programs never set! a constant; `expt` with -2^60, 45177e8405). Kinds: `ref93__value__*`, `ref93__error__*`. **Triage every
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
   - `local`, `localpart`, `localzo` (metamorphic, steering round 8; runner.rkt `local-module`):
     the generated module-level items (all for `local`; for `localpart`/`localzo` a suffix
     starting at an index chosen from the program text, the rest stays at module level) are
     moved into an internal-definition body, either `(define (main%) <items> (void)) (main%)` or a
     module-level `(let () <items> (void))`. Module-level constants, known procedures and
     variables become letrec* locals of one closure: schemify's letrec/lift/mutated-state
     handling of local bindings, Chez cpletrec, closure conversion, boxes for captured `set!`
     locals, inlining by cp0 instead of schemify's cross-form known info. A module body prints
     its expression forms' values with `current-print` and runs each in a default-tag prompt
     (reference `module`), so expression items become `(call-with-values (lambda () e)
     local-print%)` and, for half the programs, also get a `call-with-continuation-prompt`.
     Generated names are unique and refer only to earlier definitions, so internal-definition
     (`letrec-syntaxes+values`, left to right) semantics give the same output. `localzo` =
     `localpart` + zo round trip. About a fifth of the drawn cases.
     `racket runner.rkt macrodump prog.rkt local` prints the rewrite.
   - `preempt`, `preemptctl`, `preemptsplit` (metamorphic, steering round 9; runner.rkt
     `preempt-module`, `start-preempt-helper!`): green-thread preemption must not change results.
     Racket threads are Chez engines (rumble engine.ss); when the engine timer runs out at an event
     check (procedure entry, loop back-edge) the timer interrupt captures the metacontinuation and
     the scheduler swaps threads — normally once per 100 000 ticks (thread/config.rkt TICKS), so
     almost never inside user code. Here the opaque sites (denser) and the start of half of the
     function bodies are wrapped in `(pre-v e)`, which evaluates `e` and lowers the remaining ticks
     (Chez `set-timer`, via `vm-primitive`) to 1..K, K per program 2/8/32/400, so the interrupt fires
     at an arbitrary later event check: inside loops with unboxed flonum locals, prompts,
     dynamic-wind, parameterize, marks, handlers, composable-continuation applications. A helper
     green thread (output discarded) is always runnable; it yields with `(sleep 0)` inside its own
     parameterize + mark and checks that they, a flonum accumulator and a ring of vectors survive
     swaps (failure: `internal error: helper's ...`, kind `internal`). `preemptctl` wraps a third of
     the sites in the ctlnoise forms instead, `preemptsplit` = split + zo round trip of each module.
     Expected: a thread switch is not observable by a thread that shares no state with others
     (universal: no wrong result). `RKT_PRE_DEBUG=1` makes the runner print the helper's iteration
     count (≈ swaps) to stderr. The repro retries a matching variant run twice (swaps during
     compilation depend on timing). About a fifth of the drawn cases; `macrodump prog.rkt preempt`
     prints the rewrite.
   - `common`, `noclos`, `notrap`, `dbg`, `noinl`, `chezmix`, `chezmixzo` (option toggles, steering
     round 10; runner.rkt `set-chez-knobs!`): Chez compiler parameters Racket never changes, so
     their code paths in the Chez compiler were never exercised. `common`: `commonization-level`
     1-9 (cpcommonize, merging similar lambdas; CSUG: commonization "should not affect the
     behavior of the program"); `noclos`: internal `$optimize-closures #f` + `$lift-closures #f`
     (np-expand-closures instead of np-expand/optimize-closures, no well-known closure lifting);
     `notrap`: `generate-interrupt-trap #f` (no event-check/trap code in user code; loops are
     bounded); `dbg`: `debug-level 3` + `generate-inspector-information #t`; `noinl`: internal
     `$suppress-primitive-inlining #t` (every primitive called out of line instead of the cpprim
     inline code); half of the programs of each go through `compile` + zo round trip (compile-to-port). All of them also turn on `$enable-check-prelex-flags` (the Chez mats run with it, mats/build.zuo `ecpf`; only effective on the compile-to-port path), Chez's own consistency
     check of prelex referenced/assigned flags after each front-end pass (a violation raises
     `Exception in cpcheck-prelex-flags ...`, kind `internal`/`error`). `chezmix` applies a
     combination of the knobs (plus notr / cp0big), chosen from the program text, to the module
     unchanged, opaque-rewritten, localpart-rewritten, split, or ctlnoise+split; `chezmixzo` does
     the same with a zo round trip of each module. `macrodump prog.rkt chezmix` prints the rewrite.
     Not used: `compile-profile 'block` (no counters without source objects), `$loop-unroll-limit`
     (np-profile-unroll-loops is "disabled for now" in cpnanopass.ss). About a fifth of the draws.
   - `future`, `futurezo`, `futuresplit`, `gcfuture` (metamorphic, steering round 11; runner.rkt
     `future-module`): the opaque sites are evaluated as `(fut-v (lambda () e))`, i.e.
     `(touch (future thunk))` after spinning 0/300/3000/30000 iterations (per program) until a
     future worker pthread has started the thunk (an fsemaphore it posts). So `e` runs on another
     Chez OS thread (own thread context and allocation area, unboxed locals, event checks) until a
     blocking operation (printing, exceptions, continuation operations) suspends it and the touch
     resumes it in the case thread (racket/src/thread/future*.rkt, rumble). Sites inside sites nest
     futures (a touch inside a running future) for half of the programs; the other half call the
     thunk directly when already inside a future. After 3000 futures per case `fut-v` just calls the
     thunk. Expected: reference/futures.scrbl, "The touch function forces the evaluation of the
     thunk inside the given future, returning the values produced by thunk"; blocking operations
     are suspended and resumed by `touch`, so the output must equal the plain module's (sites are
     single-valued and non-tail; the thunk body is a fresh frame like the argument position was;
     only one future runs at a time, no races on program state). `futurezo` = + zo round trip,
     `futuresplit` = split + zo round trip of each module, `gcfuture` (server `e`, gc knobs and
     background place as `gc`) adds a noise future started with the module that allocates and
     checks its own lists until the module's last form stops it (`internal error: the noise
     future's lists were damaged`), so collections must rendezvous with a running future. For
     these variants a case thread that ends without a result while its custodian is still alive
     (no memory-limit kill) is reported as `internal error: the case thread ended without a
     result` (otherwise it would look like `oom` and be skipped). The repro retries a matching run
     twice (worker timing). Found in the first probe (also in 9.3): with nested futures, an abort,
     `call/cc`, `call-with-composable-continuation` or `current-continuation-marks` for a prompt
     installed inside the outer future's thunk fails ~50% of runs with "no corresponding prompt in
     the continuation", and an abort to the default tag from the inner future kills the whole
     Racket thread; re-entering a `call/cc` continuation captured in the inner future from the outer
     future's thunk hangs the process (does not even react to SIGTERM) or raises "touch: future
     previously aborted" (all three seen on trunk and 9.3). About 1/7 of the draws. `macrodump prog.rkt future` prints the rewrite.
   - `port`, `portsplit` (metamorphic, steering round 12; runner.rkt `port-module`,
     `port-alt-forms`): every `open-input-bytes`, `open-input-string`, `open-output-bytes`,
     `open-output-string`, `get-output-bytes`, `get-output-string` of the program is renamed to a
     `pa:` version (defined at the end of the prelude) that returns a port of another kind with the
     same content, the kind per call from a vector chosen from the program text (for a third of the
     programs only 3 kinds). Input kinds: the bytes port itself; `make-input-port` without a peek
     procedure (peek emulated by the port layer) and with one, delivering chunks of 1/2/3/5/7/4096/
     all bytes; `make-input-port/read-to-peek`; a pre-filled closed pipe; an unlimited pipe fed piece
     by piece by a thread (with and without `(sleep 0)` between pieces, so reads block on the writer);
     `input-port-append` of pieces (some empty); `peeking-input-port`; `make-limited-input-port` over
     the data plus a tail; `reencode-input-port` UTF-8→UTF-8 (valid UTF-8 only); a temp file
     (opened, then deleted). Output kinds: bytes port, `make-output-port` accepting 1-4096 bytes
     per call into a bytes port, a pipe drained by the getter, a temp file (read back through a
     second port); when the program sets an output position (`(file-position o k)`) only the
     seekable ones (bytes, file). Expected (reference ports.scrbl, custom-ports.scrbl,
     pipes.scrbl, port-buffers.scrbl): blocking reads/peeks return the same bytes whatever the
     chunking; "Calling file-position without a position on a port other than a file-stream port or
     string port returns the number of bytes that have been read from that port"; locations are
     counted from the bytes; get-output-string is "(bytes->string/utf-8 (get-output-bytes out)
     #\uFFFD)". Not used: limited pipes (a blocking peek beyond the limit waits forever; the doc
     only extends capacity by bytes actually peeked — checked on trunk and 9.3), avail/non-blocking
     reads (counts may differ legitimately), `get-output-bytes` with reset (custom ports keep their
     own position). `portsplit` = split + zo round trip. Port names are all `'string`, so messages
     agree. `RKT_PORT_KIND=k` / `RKT_PORT_OKIND=k` force one kind (triage), `RKT_PORT_DEBUG=1`
     prints the number of ports made. Programs without `(open-` run `opaque` instead.
     The generator got port constructs (gen.rs `port_in`, `port_out`, 1/6 of `lib_op`): an input
     port on tricky data (line endings, readable data, UTF-8 and invalid bytes, data across the
     4096-byte buffer) read by 1-6 operations whose results form a list — `read-byte`/`char`,
     `peek-byte`/`char` with skip, `read`/`peek-bytes`/`string` with counts and skips (also around
     4096), `read-line`/`read-bytes-line` in all modes, regexp matching on ports (consuming, peeking,
     try, with start offsets, lookbehind), `read`, `read-syntax` with srclocs, `file-position`,
     `port-next-location` (with `port-count-lines!` for 40%), `read-bytes!`/`peek-bytes!`, the rest;
     and an output port written by 1-6 operations (bytes with ranges, strings, chars, bytes,
     `display`/`write`/`print`, `fprintf`, newline + flush, mid-way gets, positions, locations, big
     writes, position sets followed by a write). Area tags `port-in`, `port-out`.
     First probe (4 x 420 s on a trunk build with fixes for the bugs found so far): the generator's port writes, run inside futures by
     the future variants, crash the process: a future that writes > 4096 bytes to a bytes output
     port (port buffer growth: `make-bytes` -> `guard-large-allocation` -> `current-thread` while
     the port is locked, uninterruptible) prints `internal-error: attempting to suspend a future
     in uninterruptible mode` plus a ` at <name>` backtrace (racket/src/cs/thread.sls
     `internal-error`, thread/future.rkt) with Chez's printf on stdout, and then spins at ~200%
     CPU instead of exiting (ignores SIGTERM). Also in 9.3. Standalone: a loop of
     `(future (lambda () (write-bytes (make-bytes 5000 97) o)))` + `touch`, with the touch
     delayed until a worker has started the future. Those stdout lines used to be read as the
     next result line (findings `<variant>__error__*` with a message like ` at "make-bytes"`);
     now any line that is not a result line makes the server count as dead (`died`, the lines are
     in the message) and the server is killed; the variant repro retries a died future case up to
     8 times with a 45 s limit and accepts an `internal-error:` line as reproduction.
   - `top`, `topzo`, `topsplit` (metamorphic, steering round 13; runner.rkt `run-top`,
     `top-body-forms`): the module's body forms are evaluated one by one at the top level of the
     fresh `racket/base` namespace instead of as a module. Each form is its own top-level linklet
     (expander compile/top.rkt, eval/top.rkt; optimized, machine code), module definitions become
     namespace variables that schemify knows nothing about across forms (no constants, no known
     procedures or struct accessors, no cross-form inlining, every reference through a variable
     instance), `require`, `struct` and the `show` macro go through the top-level expander. A module
     body prints its expression forms' values with `current-print` and runs each in a default-tag
     prompt (reference/syntax.scrbl `module`); top-level `eval` does neither, so each expression
     item becomes `(call-with-values (lambda () (call-with-continuation-prompt (lambda () e)))
     top-print%)`. Generated names are unique and refer only to earlier definitions, so no forward
     reference or redefinition exists (the documented top-level differences, reference
     eval-model.scrbl "top-level is hopeless", are about those). For a third of the programs the
     opaque rewrite is applied first, for a sixth the ctlnoise one. `topzo`: per form `compile` + zo round trip + `eval`, or (half
     of the programs) the prelude per form and then all generated items as one compiled top-level
     `(begin ...)` (one compiled object holding several top-level linklets; `compile` of a begin
     does not run a `define-syntax` of the same begin, hence the prelude first). `topsplit`: the
     provider module `a` of `split-module` (zo round trip) is declared, then the client's body
     including `(require 'a)` runs at the top level, per form plain or zo (top-level linklets
     importing a module's known bindings). `macrodump prog.rkt top` prints the forms. About 1/7 of
     the draws. First probe (300 programs x 3 on trunk): one difference, the known
     unboxed-`fl+` composable-continuation bug (the module side is the wrong one).
     For half of the programs every function definition `(define (f ...) ...)` is also evaluated
     a second time, unchanged, at a later position (the top level allows redefinition, a lambda
     definition has no other effect, so callers compiled earlier — or in the same compiled begin —
     must see an equivalent procedure: no stale known-procedure or inlining assumptions).
   - `rtrip`, `rtripzo` (run-time round trips, steering round 13; runner.rkt `rt-module`,
     `rt-defs`): the opaque sites are wrapped in `(rt-v e)`, which returns e's value unchanged
     after checking documented round trips on it: `write` then `read` gives an `equal?` value
     (printer.scrbl: "write mode prints core datatypes in such a way that using read on the output
     produces a value that is equal? to the printed value"; only trees of numbers, strings, byte
     strings, chars, interned symbols, keywords, booleans, `'()`, pairs, vectors);
     `s-exp->fasl`/`fasl->s-exp` with `#:keep-mutable? #t` (also boxes and hash tables; in
     eq?/eqv?/equal-always? tables only keys whose identity a copy keeps: fixnums, chars, booleans,
     symbols, keywords, and numbers for eqv?) gives an `equal?` value; `number->string` /
     `string->number` (radix 10, and 2/8/16 for exact numbers) gives an `eqv?` number;
     `equal-hash-code` (and `eqv-hash-code` for numbers) of v and of each copy agree
     (equality.scrbl: "For any two calls with equal? values, the returned number is the same");
     an immutable hash rebuilt in reverse insertion order is `equal?` with the same hash code. A
     violation raises `rt-v: internal error: round trip <what>: <v> -> <copy>` (kind `internal`).
     First 3000 sites per case, values written in under 20 000 chars. `rtripzo` = + zo round trip.
     About 1/14 of the draws. Probes: 950 programs x 2 clean after restricting non-equal? table
     keys (a copied mutable-string key is a new object for eqv?, correctly not `equal?`).
   - `chap`, `chapzo`, `chapsplit` (metamorphic, steering round 15; runner.rkt `ch-module`,
     `ch-defs`): the opaque sites are wrapped in `(ch-v e)`, which returns e's value inside an
     identity chaperone or impersonator when it is a vector (`chaperone-vector`/`-vector*`, `#f`
     procs, `impersonate-vector` for mutable ones), box, hash table (with and without clear and
     equal-key procs), `pt` (accessor/mutator subsets, struct-type witness, a chaperoned accessor
     as orig-proc), exn (`exn-message`), prompt tag (handle/abort procs, `callcc-impersonate-proc`
     re-wrapping, `comp-guard-proc` 9.2.0.6) or procedure (`chaperone-procedure`/`*`,
     `impersonate-procedure`/`*`, `#f` wrapper + impersonator property, identity wrappers that also
     add `'mark` key/val triples, keyword-aware wrappers for keyword procedures); a fifth also
     wrap the wrapper again. Applications of user functions and primitives at sites go through
     the wrapper, so loops, known calls and inlined struct accessors / `vector-ref` take the
     impersonator slow paths (rumble impersonator.ss, struct.ss, vector.ss, procedure.ss, hash,
     control.ss). Expected (reference/chaperones.scrbl): with identity interposition every
     operation behaves as on the original; "If wrapper-proc is #f, then applying the resulting
     impersonator is the same as applying proc"; without a result wrapper "proc is called in tail
     position with respect to the call to the impersonator"; `equal?` and printing see through.
     Identity is the one documented difference (a wrapper is not `eq?` to its original), so
     `eq? eqv? memq memv assq assv` in the program are renamed to `ch:` versions comparing the
     originals (weak table wrapper -> original) and, in programs with eq?/eqv?-based tables, the
     key argument of `hash-ref`/`hash-set`/... is unwrapped. Result wrappers (non-tail) only in
     programs that never mention marks, continuations or prompts; impersonators only in programs
     without `equal-always?` tables (impersonators are not `equal-always?` to the original).
     `ch-v` also checks `impersonator-of?`/`chaperone-of?` and the impersonator property
     (`ch-v: internal error: ...`, kind `internal`). `chapzo` = + zo round trip, `chapsplit` =
     split + zo round trip of each module. About 1/8 of the draws. `macrodump prog.rkt chap`
     prints the rewrite. `RKTGEN_VARIANTS=chap,chapzo` (comma list) restricts the draw for probes.
     The generator's `lib_collop` got two templates whose library procedures have impersonator
     paths: `vector-copy!` (also overlapping, same vector), `vector->values`, `list->vector`, and
     `make-hash` from an assoc list, `hash-copy`, `hash-ref-key`, `hash-map/copy`, `hash-clear!`.
     First probes (a trunk build with fixes for the bugs found so far, 4 x 240 s, chap only): ~0.5% failures, all one real bug:
     `vector-fill!` on a chaperoned mutable vector raises "contract violation ... given: <fill
     value>" (rumble/vector.ss checks the fill value instead of the vector; also 9.3). Seen by hand
     while debugging the check (not yet hit by the generator: it only reaches keyword procedures
     through `sort`): `impersonate-procedure` of a keyword procedure with an impersonator property
     answers `chaperone?` #t but `chaperone-of?` #f, and without a property `impersonator?` #f
     (also 9.3).
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

4. **numref** (`numref__{value,error,ivalue,ierror,uvalue,uerror,died,udied}__<op>`, steering round 14):
   an independent second reference for the numeric library both trunk modes share. Every
   oracle above compares Racket with Racket, so a wrong result computed by code that machine
   code and the interpreter both call (Chez's C `number.c` bignum arithmetic, `mathprims.ss`/
   `5_3.ss` rationals and `exact->inexact`, the library procedures `flround`/`flmin`/`flmax`/
   `fxpopcount`/`flsingle`/`flbit-field` compiled with the same new cpprim inlines, the fixnum
   wraparound ops, `integer->integer-bytes`, `number->string`/`string->number` in radix 2/8/16)
   is invisible to them. A fifth of the cases (`mix(seed, 9_100_000 + case) % 5 == 0`, outside
   ephyra) are numref programs from `gen/src/num.rs`: a module with 16-31 lines
   `(o i (lambda () e))`, `e` a typed expression (fixnum / exact integer incl. bignums up to
   ~1100 bits / exact rational / flonum / boolean / string; depth 1-4) over those operations,
   mixed exact-inexact comparisons (numbers.scrbl `=`: "An inexact number is numerically equal to
   an exact number when the exact coercion of the inexact number is the exact number"), bounded
   named-let accumulation loops (unboxed flonum/fixnum locals), `if`, literal pools with edge
   values (fixnum bounds, 2^53+-1, 2^1024-2^970, subnormals, FLT_MAX rounding boundaries) and
   exact values at or next to binary64 rounding ties in the normal, subnormal and overflow
   ranges. Leaves are wrapped in `(q x)` (identity hidden behind `set!`: no constant folding)
   with a per-line probability 0/0.3/0.7/1, and in 35% of the lines the leaves become
   parameters of a module-level `(define (fnI p...) e)` (machine code with unknown arguments).
   A quarter of the lines whose operations all exist in Chez Scheme are compiled by the Chez
   compiler directly, `(o i (vm-eval '(lambda () e')))` (ffi/unsafe/vm; `e'` with Chez names:
   `fxsll`/`fxsra`/`fxsrl`, `flonum->fixnum`, `isqrt`, `bitwise-arithmetic-shift`, ...,
   `numref-q` a Chez top-level identity): no schemify, Chez's own cp0 folding of `mifoldable`
   primitives, and the Chez-only primitives `flfma` (native FMA, 3605290b08) and `flnextafter`
   (c39f716310) inline; Racket lines reach them through prelude bindings. numref.py maps the
   names back (`from_chez`).
   `o` prints `i <enc>` (`#t`/`#f`, `e<exact>`, `f<exact value of the flonum>`, `-0`, `nan`,
   `+inf`, `-inf`, `s<string>`, or `err` when `exn:fail` was raised; strings over 120 chars
   abbreviated to head~length~tail, since runner.rkt caps the output).
   `racket/numref.py` (stdlib only: int, fractions.Fraction, IEEE doubles, ctypes float for
   `flsingle`) parses the same text and evaluates every line by the documented semantics
   (truncating quotient/remainder, floor modulo, round-half-even, IEEE rounding with the sign of
   zero kept, `gcd`/`lcm` of rationals as numbers.scrbl says, fixnum ops raising
   non-fixnum-result outside [-2^60, 2^60), `/wraparound` modulo 2^61, flmin/flmax returning the
   second of 0.0 and -0.0 (05afec9201) and NaN when any argument is NaN). Lines whose result is
   not specified (inexact `sqrt`, the bits of a NaN, NaN bytes read with the other endianness)
   are not compared. Machine code (server a) and the interpreter (server b) both run the module
   and are both checked; for half the passing cases the lines that raised nothing are re-run
   under variant `unsafe` (server c; only evaluations that should raise are unspecified there).
   On a mismatch the failing line alone is re-checked and greedily simplified (replace a node by a
   same-typed child, drop `q`, inline the function), up to 120 steps. Kinds: `value`/`error`
   machine code wrong, `ivalue`/`ierror` interpreter wrong (machine code right), `uvalue`/
   `uerror` unsafe machine code wrong, `died`/`udied` the server died twice on the program.
   `<op>` = the first primitive of the shrunk expression (in preorder), e.g. `fxpopcount`,
   `exact-to-inexact`. Repro: `repro.sh` runs `runner.rkt file prog.rkt` (mode by kind) and
   pipes the result line into `python3 -I numref.py check prog.rkt` (exit 1 mismatch, 0 match, 2
   undecidable); `python3 -I numref.py eval prog.rkt` prints the expected lines,
   `rktgen numsample <seed>` prints a program. Expected behaviour: the documented semantics
   quoted in numref.py; `exact->inexact` is checked as correctly rounded (R6RS `inexact`:
   "the numerically closest inexact number", which Chez implements; Racket only says
   "Coerces") — treat a mismatch there as a watch item until the closest-value claim is
   confirmed. Stats: `numref_cases`, `numref_pass`, `numref_unsafe`, `numref_skip`,
   `numref_gen_errors` (module raised or a line is missing: generator bug, should stay 0),
   `numref_py_lost`, `fail_numref_*`. Before round 14, 2400 programs (~60 000 expressions) passed
   on trunk+patches.

5. **rxref** (`rxref__{value,error,died}__<mode>-<area>`, steering round 16): a second reference for
   the regexp matcher (racket/src/regexp, shared by every mode, so no Racket-vs-Racket oracle sees
   it). An eighth of the cases (`mix(seed, 9_300_000 + case) % 8 == 0`, outside ephyra) are
   programs from `racket/rxref.py gen`: 3-5 lines, each a generated pregexp (literals incl.
   non-ASCII / astral chars and high bytes, `.`, classes with ranges / `\d\w\s` / POSIX classes,
   negated classes, `\D\W\S`, `\p{..}`/`\P{..}` in string mode, `^ $ \b \B`, greedy / lazy /
   bounded quantifiers (only on operands that cannot match empty: rx.rkt rejects others; no
   unbounded repeat under another one), alternation, groups, `(?i:` `(?-i:` `(?m:` `(?s:` ...
   modes, lookahead, fixed-width lookbehind, atomic groups, back references, `(?(N)..|..)`) on
   a byte string (`byte-pregexp`) or a string (`pregexp`), with an input built partly from strings
   the pattern matches, an optional start / end position and input prefix. Each line runs
   `regexp-match-positions`, the same on an input port, `regexp-match-peek-positions`,
   `regexp-match`, `regexp-match` on a port (bytes results), `regexp-match-positions*` on the
   value and on a port, `regexp-split`, `regexp-replace*` / `regexp-replace` with a template of
   literals, `&` and `\N`, `regexp-match?`, `regexp-quote` of the input matching itself, `regexp-match-exact?`, `regexp-match-positions`
   with an output port (start-pos 0: with a positive start-pos Racket writes from start-pos while
   the docs say "from its beginning (not start-pos)", same in 9.3; left out), `#:match-select
   values`, and (string mode) the string regexp on the UTF-8 bytes. rxref.py translates the AST into a
   Python `re` pattern that spells out Racket's documented semantics (rx.rkt grammar:
   `\w`/`\d`/`\s`/POSIX classes are ASCII, `.` matches newline outside multi mode, `$` is the
   end, `(?m:` = `(?-s:` multi mode; `\p{..}` becomes the class of pool characters in that
   category, inputs only use the pool) and computes the expected value of every call from the
   documented rules in regexps.scrbl: `^` and lookbehind see `input-prefix`, not the input before
   `start-pos`; positions independent of `start-pos`; port positions count bytes; in
   `regexp-match*` "each match attempt starts at the end of the last match", `^` only for the
   first match, no empty match immediately after an empty match; `regexp-split` /
   `regexp-replace*`: "Zero-length matches are treated the same as for regexp-match*"; an
   unmatched `\N` in a template is empty. Lines where Racket rejects the pattern are skipped.
   Area: `str-`/`bytes-` plus the first failing call when `regexp-match-positions` itself is
   right (e.g. `str-all`, `bytes-repl`), else the most specific construct of the shrunk pattern
   (`lookbehind`, `cond`, `bref`, `casei`, ...). On a failure rxref.py proposes one-line
   simplifications (single call, no start/prefix, subtree replaced by a child or `a`, input
   characters dropped), kept while kind and area stay the same (<= 200 runs). Once a signature
   has 2 cases (`RXREF_CAP`), later hits are only counted (`rxref_dup`), not shrunk or counted as failures.
   Repro: `repro.sh` runs `runner.rkt file prog.rkt none` and pipes the result into
   `python3 -I rxref.py check prog.rkt` (each line's spec is the JSON in its `;; RX` comment);
   `python3 -I rxref.py eval prog.rkt` prints the expected values, `rktgen rxsample <build>
   <seed>` a program. Stats: `rxref_cases`, `rxref_pass`, `rxref_skip`, `rxref_dup`,
   `rxref_gen_errors` (should stay 0), `rxref_py_lost`, `fail_rxref_*`. `RKTGEN_NO_RXREF=1`
   turns it off.
   Probe on trunk before the merge (120 programs, ~2000 calls): two classes, both also in 9.3:
   `(regexp-match-positions* #px"(?=.)|(?<=é)" "éé")` gives `((0 . 0) (1 . 1))` without
   `(2 . 2)` (after an empty match the next attempt loses the multi-byte lookbehind; also `\B`),
   and `regexp-replace*` handles an empty match differently from `regexp-match*`
   (`(regexp-match-positions* #px"a??" "ab")` = `((0 . 0) (0 . 1) (1 . 1) (2 . 2))`, but
   `(regexp-replace* #px"a??" "ab" "[&]")` = `"[]a[]b[]"`).

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
`skip_*` (incl. `skip_ref93_{noresult,unbound,internal,continuation,known_*}`), `variant_cmp_<v>`
(cases compared under variant v, incl. `variant_cmp_ref93`), `masked_nonfx_msg`,
`server_restarts`, `segments`. `rktgen norm93 prog.rkt < result-lines` prints the ref93
comparison form.

Round 7 check (patched base build, 8 x 700 s + 4 x 500 s): ~28 000 cases, ~4 100 ref93
comparisons, 0 failures; one earlier ref93 finding was a 9.3 bug repaired in trunk (8f67966b14),
now skipped. On the unpatched trunk the old clusters (composable, splitmi set) still appear
within minutes.

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

Round 10 check (a trunk build with fixes for the bugs found so far, 4 x 600 s + 4 x 360 s, ~14 000 cases): 300 sampled programs x 7 knob
variants gave no differences; the search found 6 `*__internal__*` findings (chezmixzo, notrap,
common), all the same Chez crash: with `$enable-check-prelex-flags` on, `compile-to-port` of
`(lambda (t) (real->flonum (+ 5 (length t))))` (also `(inexact (if (fixnum? t) (+ t 1) 1))`)
dies with "invalid memory reference"; it needs cptypes (`enable-type-recovery #f` avoids it).

Round 11 check (same kind of build, 4 x 360 s, 6 669 cases): 4 failures (0.06%), all
future variants, all nested-future continuation failures (futuresplit reentry/composable, futurezo
composable/reentry); 500 sampled programs x 4 future variants gave 2 programs differing (both nested).

Round 12 check (same kind of build, 3 x (4 x 420-480 s), ~27 000 cases, ~950 port /
portsplit comparisons): 582 sampled port programs x {port, portsplit} gave no differences; two
harness false positives found and fixed (bad arguments to `pa:open-input-bytes` from the shrinker;
racket/port `*-evt` on ports without progress events, which port-lib.scrbl excludes). The remaining
failures (~0.02%) are all the future crash described under `port` (future/futurezo/futuresplit
`__died__*`, message `internal-error: attempting to suspend a future in uninterruptible mode`).
Throughput 6.3 cases/s solo vs 7.5 before (port constructs, racket/port loaded per namespace).
