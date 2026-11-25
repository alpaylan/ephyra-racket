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
HERE=$(cd "$(dirname "$0")" && pwd)

mkdir -p "$BUILD/src"
# No --delete: pb boot files (fetched, racket/src/ChezScheme/boot/pb) and build
# outputs live inside the copy.
rsync -a --exclude=.git "$SRC"/ "$BUILD/src"/

cd "$BUILD/src"
if [ "$MODE" = coverage ]; then
  LLVM_BIN=/usr/lib/llvm-21/bin
  export CC="$LLVM_BIN/clang"
  export CFLAGS="-O2 -fprofile-instr-generate -fcoverage-mapping"
  export LDFLAGS="-fprofile-instr-generate"
  # Instrumented build-time tools write profiles; keep them out of the tree.
  mkdir -p "$BUILD/build-profraw"
  export LLVM_PROFILE_FILE="$BUILD/build-profraw/%m_%p.profraw"
fi
make base CPUS=16 JOBS=16 PKGS=racket-lib > "$BUILD/make.log" 2>&1 || {
  tail -40 "$BUILD/make.log"; exit 1; }
RACKET="$BUILD/src/racket/bin/racket"
"$RACKET" -l racket/base -e '(void)' >/dev/null

# Harness generator (Rust).
CARGO_TARGET_DIR="$BUILD/harness-target" cargo build --release --quiet \
  --manifest-path "$HERE/gen/Cargo.toml"
mkdir -p "$BUILD/harness"
cp "$BUILD/harness-target/release/rktgen" "$BUILD/harness/rktgen"
cp "$HERE/racket/runner.rkt" "$BUILD/harness/runner.rkt"
# Compile the runner to machine code so the interpreter server only
# interprets the generated programs, not the runner itself.
( cd "$BUILD/harness" && "$RACKET" -l racket/base -l compiler/cm \
    -e '(managed-compile-zo "runner.rkt")' )

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
