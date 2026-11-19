#!/bin/sh
# Download tc39/test262 into third_party/test262 (gitignored) for `lake exe test262`.
# Pin with TEST262_REV=<commit>; default: main.
set -eu
cd "$(dirname "$0")/.."
REV="${TEST262_REV:-main}"
mkdir -p third_party
rm -rf third_party/test262
curl -sSfL --retry 5 --retry-delay 5 --connect-timeout 30 \
  "https://github.com/tc39/test262/archive/${REV}.tar.gz" | tar -xz -C third_party
mv third_party/test262-* third_party/test262
echo "test262 @ ${REV} -> third_party/test262 ($(find third_party/test262/test -name '*.js' | wc -l | tr -d ' ') test files)"
