#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
CATCHING_UP_OUTPUT=$(mktemp -d)
export CATCHING_UP_OUTPUT
trap 'rm -rf "$CATCHING_UP_OUTPUT"' EXIT HUP INT TERM
sh "$here/reluctant/generate.sh"
sh "$here/generate_dormant.sh"
python3 "$here/generate_plus_restarting.py"
python3 "$here/generate_deferred_simple.py"
for family in reluctant_restarting dormant_restarting dirty_read_restarting plus_restarting deferred_simple; do
  for control in "" inlined_; do
    cp "$CATCHING_UP_OUTPUT/slrtc_${control}${family}.ml" "$here/../generated/"
  done
done
cp "$here/goblint_qsolver_update.ml" "$here/../generated/slrtc_catching_up_update.ml"
cp "$here/slrtc_catching_up_register.ml" "$here/../generated/slrtc_catching_up_register.ml"
