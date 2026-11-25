#!/usr/bin/env bash
# run.sh <build-dir> <seed> <seconds> <out-dir>
set -euo pipefail
BUILD=$(cd "$1" && pwd)
mkdir -p "$4"
OUT=$(cd "$4" && pwd)
# rktgen is built by build.sh with cargo into $BUILD/harness-target.
exec "$BUILD/harness-target/release/rktgen" run "$BUILD" "$2" "$3" "$OUT"
