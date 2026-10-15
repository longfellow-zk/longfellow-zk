#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../../../.."

# Each invocation has at most two stale, independent radius checks.  Building
# The aggregate target directly from a cold state could start all sixteen at once.
for index in 0 1 2 3 4 5 6 7; do
  lake build \
    "examples.Ligero.Longfellow.HahnMaskFS.V7Range${index}" \
    "examples.Ligero.Longfellow.HahnMaskFS.V8Range${index}"
done

lake build LigeroLocalCounts
