#!/usr/bin/env bash
# run.sh <build-dir> <seed> <seconds> <out-dir>
set -euo pipefail
BUILD=$(cd "$1" && pwd)
mkdir -p "$4"
OUT=$(cd "$4" && pwd)
exec "$BUILD/harness/rktgen" run "$BUILD" "$2" "$3" "$OUT"
