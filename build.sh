#!/usr/bin/env bash
# build.sh <src-dir> <build-dir> [coverage]
# Copies the Racket tree into <build-dir>/src (the Racket build writes inside
# its tree), builds minimal Racket CS in place there (make base, racket-lib
# only), and builds the harness generator into <build-dir>/harness.
# Incremental: rsync keeps mtimes, so an unchanged tree rebuilds in seconds.
set -euo pipefail
SRC=$(cd "$1" && pwd)
mkdir -p "$2"
BUILD=$(cd "$2" && pwd)
MODE=${3:-}
# Parallelism and the LLVM tools for coverage builds; override in the environment.
CPUS=${CPUS:-16}
JOBS=${JOBS:-$CPUS}
HERE=$(cd "$(dirname "$0")" && pwd)

mkdir -p "$BUILD/src"
# No --delete: pb boot files (fetched, racket/src/ChezScheme/boot/pb) and build
# outputs live inside the copy.
rsync -a --exclude=.git "$SRC"/ "$BUILD/src"/

cd "$BUILD/src"
if [ "$MODE" = coverage ]; then
  LLVM_BIN=${LLVM_BIN:-/usr/lib/llvm-21/bin}
  export CC="$LLVM_BIN/clang"
  # The build happens in a copy; map its paths back to the tree we were given
  # so the coverage map names the tree's sources.
  export CFLAGS="-O2 -fprofile-instr-generate -fcoverage-mapping -fcoverage-prefix-map=$BUILD/src=$SRC"
  export LDFLAGS="-fprofile-instr-generate"
  # Instrumented build-time tools write profiles; keep them out of the tree.
  mkdir -p "$BUILD/build-profraw"
  export LLVM_PROFILE_FILE="$BUILD/build-profraw/%m_%p.profraw"
fi
# zuo does not notice changed CFLAGS: start the C build over when they change.
STAMP="$BUILD/cflags.stamp"
if [ "$(cat "$STAMP" 2>/dev/null)" != "${CC:-}|${CFLAGS:-}" ]; then
  [ -e "$STAMP" ] && rm -rf "$BUILD/src/racket/src/build"
fi
make base CPUS=$CPUS JOBS=$JOBS PKGS=racket-lib > "$BUILD/make.log" 2>&1 || {
  tail -40 "$BUILD/make.log"; exit 1; }
echo "${CC:-}|${CFLAGS:-}" > "$STAMP"
RACKET="$BUILD/src/racket/bin/racket"
"$RACKET" -l racket/base -e '(void)' >/dev/null

# Harness generator (Rust).
CARGO_TARGET_DIR="$BUILD/harness-target" cargo build --release --quiet \
  --manifest-path "$HERE/gen/Cargo.toml"
mkdir -p "$BUILD/harness"
cp "$HERE/racket/runner.rkt" "$BUILD/harness/runner.rkt"
# numref oracle's independent reference evaluator (python3 -I, stdlib only)
cp "$HERE/racket/numref.py" "$BUILD/harness/numref.py"
# Compile the runner to machine code so the interpreter server only
# interprets the generated programs, not the runner itself.
( cd "$BUILD/harness" && "$RACKET" -l racket/base -l compiler/cm \
    -e '(managed-compile-zo "runner.rkt")' )

# Second reference (variant ref93): released Racket 9.3 CS (minimal), copied
# into the build dir so repro.sh needs nothing outside it, and the runner
# compiled by it.
REF93_SRC=${REF93_SRC:-}
REF93_TGZ=${REF93_TGZ:-}
REF93_URL=https://download.racket-lang.org/releases/9.3/installers/racket-minimal-9.3-x86_64-linux-cs.tgz
R93="$BUILD/ref93/racket/bin/racket"
if [ ! -x "$R93" ]; then
  rm -rf "$BUILD/ref93"; mkdir -p "$BUILD/ref93"
  if [ -x "$REF93_SRC/racket/bin/racket" ]; then
    rsync -a "$REF93_SRC"/ "$BUILD/ref93"/
  else
    [ -f "$REF93_TGZ" ] || { REF93_TGZ="$BUILD/rm93.tgz"; curl -fsSL -o "$REF93_TGZ" "$REF93_URL"; }
    tar -xzf "$REF93_TGZ" -C "$BUILD/ref93"
  fi
fi
if [ -x "$R93" ]; then
  mkdir -p "$BUILD/harness93"
  cp "$HERE/racket/runner.rkt" "$BUILD/harness93/runner.rkt"
  ( cd "$BUILD/harness93" && "$R93" -l racket/base -l compiler/cm \
      -e '(managed-compile-zo "runner.rkt")' ) || rm -f "$BUILD/harness93/runner.rkt"
else
  echo "warning: no Racket 9.3, variant ref93 disabled" >&2
fi

if [ "$MODE" = coverage ]; then
  rm -rf "$BUILD/build-profraw"
  # The executable statically links the Chez kernel and rktio.
  REAL=$(readlink -f "$RACKET")
  cat > "$BUILD/coverage.json" <<EOF
{"objects": ["$REAL"],
 "profdata": "$LLVM_BIN/llvm-profdata",
 "cov": "$LLVM_BIN/llvm-cov"}
EOF
fi
echo "build ok: $RACKET"
