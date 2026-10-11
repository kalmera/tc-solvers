#!/bin/sh
set -eu

directory=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
extraction_directory="$directory"
fragments="$extraction_directory/fragments"
. "$extraction_directory/select_rank_worklist.sh"
generated="${CATCHING_UP_OUTPUT:-$extraction_directory/../generated}"
extracted_control="$extraction_directory/../../../extracted/GoblintControl.ml"
inlined_control="$extraction_directory/goblint_control_inlined.ml"

mkdir -p "$generated"

generate () {
  template=$1
  control=$2
  variant=$3
  output=$4
  reader_wake=${5:-$fragments/reader_wake_immediate.ml.inc}
  dirty_read_commit=${6:-$fragments/simple_dirty_read_commit_base.ml.inc}
  restarting_dirty=${7:-base}
  temporary="$output.tmp"
  if [ "$control" = "$inlined_control" ]; then
    control_kind=inlined
  else
    control_kind=extracted
  fi

  {
    echo '(* GENERATED FILE. DO NOT EDIT.'
    echo "   Variant: $variant"
    echo "   Control: $control_kind"
    echo "   Rank worklist: $rank_worklist_name"
    if grep -q '@@READER_WAKE_QUEUE@@' "$template"; then
      echo "   Reader wake: $(basename "$reader_wake" .ml.inc)"
    fi
    echo "   Adapter: ocaml/adapters/goblint/$(basename "$template")"
    echo '   Regenerate with: make goblint-solvers *)'
    awk -v control="$control" -v control_kind="$control_kind" \
        -v variant="$variant" \
        -v reader_wake="$reader_wake" \
        -v dirty_read_commit="$dirty_read_commit" \
        -v restarting_dirty="$restarting_dirty" \
        -v rank_worklist="$rank_worklist_source" '
      $0 == "(* @@CONTROL@@ *)" {
        print "module Control = struct"
        while ((getline line < control) > 0) {
          if (line ~ /^let (eval_rhs0|solve_one0|solve_loop_fuel0|solve_seeds_with_fuel0) /)
            sub(/0 /, " ", line)
          if (line ~ /^let (eval_rhs|solve_one|solve_all|solve_seeds_with_fuel) /)
            sub(/^let /, "let[@inline always] ", line)
          if (line == "") print ""; else print "  " line
        }
        close(control)
        print "end"
        next
      }
      $0 == "    (* @@RANK_WORKLIST@@ *)" {
        print "    module RankQueue = struct"
        while ((getline line < rank_worklist) > 0) {
          if (line == "") print ""; else print "      " line
        }
        close(rank_worklist)
        print "    end"
        next
      }
      $0 == "    (* @@READER_WAKE_QUEUE@@ *)" {
        while ((getline line < reader_wake) > 0) {
          if (line == "") print ""; else print "    " line
        }
        close(reader_wake)
        next
      }
      $0 == "            (* @@DIRTY_READ_COMMIT@@ *)" {
        while ((getline line < dirty_read_commit) > 0) {
          if (line == "") print ""; else print "            " line
        }
        close(dirty_read_commit)
        next
      }
      $0 ~ /^[ ]+\(\* @@RESTARTING_DIRTY_[A-Z_]+@@ \*\)$/ {
        indent = $0
        sub(/\(\*.*/, "", indent)
        marker = $0
        sub(/^[ ]+\(\* @@RESTARTING_DIRTY_/, "", marker)
        sub(/@@ \*\)$/, "", marker)
        if (restarting_dirty != "base") {
          file = dirty_read_commit
          sub(/simple_dirty_read_commit_[^.]+[.]ml[.]inc$/, "restarting_dirty_" tolower(marker) "_" restarting_dirty ".ml.inc", file)
          while ((getline line < file) > 0) {
            if (line == "") print ""; else print indent line
          }
          close(file)
        }
        next
      }
      {
        gsub(/@@CONTROL_KIND@@/, control_kind)
        gsub(/@@DORMANT_RESTARTING_VARIANT@@/, variant)
        print
      }
    ' "$template"
  } > "$temporary"
  mv "$temporary" "$output"
}

simple="$extraction_directory/goblint_dormant_simple.ml.in"
restarting="$extraction_directory/goblint_dormant_restarting.ml.in"
for source in "$simple" "$restarting" \
  "$extracted_control" "$inlined_control" \
  "$rank_worklist_source" \
  "$fragments/simple_reader_wake_immediate.ml.inc" \
  "$fragments/simple_reader_wake_dirty_read.ml.inc" \
  "$fragments/simple_dirty_read_commit_base.ml.inc" \
  "$fragments/simple_dirty_read_commit_promote.ml.inc" \
  "$fragments/reader_wake_immediate.ml.inc" \
  "$fragments/reader_wake_dirty_read.ml.inc"
do
  if [ ! -f "$source" ]; then
    echo "missing dormant generation input: $source" >&2
    exit 1
  fi
done

for template in "$simple" "$restarting"
do
  if [ "$(grep -c '@@READER_WAKE_QUEUE@@' "$template")" -ne 1 ]; then
    echo "invalid dormant reader-wake marker: $template" >&2
    exit 1
  fi
done

if [ "$(grep -c '^            [(][*] @@DIRTY_READ_COMMIT@@ [*][)]$' "$simple")" -ne 1 ]; then
  echo "invalid dirty-read commit marker: $simple" >&2
  exit 1
fi

for template in "$simple" "$restarting"
do
  if [ "$(grep -c '^[(][*] @@CONTROL@@ [*][)]$' "$template")" -ne 1 ]; then
    echo "invalid dormant control marker: $template" >&2
    exit 1
  fi
  if [ "$(grep -c '^    [(][*] @@RANK_WORKLIST@@ [*][)]$' "$template")" -ne 1 ]; then
    echo "invalid dormant rank-worklist marker: $template" >&2
    exit 1
  fi
done

trap 'rm -f "$generated"/slrtc_dormant_*.ml.tmp \
  "$generated"/slrtc_inlined_dormant_*.ml.tmp \
  "$generated"/slrtc_dirty_read_*.ml.tmp' EXIT HUP INT TERM

generate "$simple" "$extracted_control" DormantSimple \
  "$generated/slrtc_dormant_simple.ml" \
  "$fragments/simple_reader_wake_immediate.ml.inc"
generate "$simple" "$inlined_control" DormantSimple \
  "$generated/slrtc_inlined_dormant_simple.ml" \
  "$fragments/simple_reader_wake_immediate.ml.inc"
generate "$simple" "$inlined_control" DirtyReadSimpleInlined \
  "$generated/slrtc_inlined_dirty_read_simple.ml" \
  "$fragments/simple_reader_wake_dirty_read.ml.inc" \
  "$fragments/simple_dirty_read_commit_promote.ml.inc"
generate "$simple" "$extracted_control" DirtyReadSimple \
  "$generated/slrtc_dirty_read_simple.ml" \
  "$fragments/simple_reader_wake_dirty_read.ml.inc" \
  "$fragments/simple_dirty_read_commit_promote.ml.inc"
generate "$restarting" "$extracted_control" DormantRestarting \
  "$generated/slrtc_dormant_restarting.ml"
generate "$restarting" "$inlined_control" DormantRestarting \
  "$generated/slrtc_inlined_dormant_restarting.ml"
generate "$restarting" "$extracted_control" DirtyReadRestarting \
  "$generated/slrtc_dirty_read_restarting.ml" \
  "$fragments/reader_wake_dirty_read.ml.inc" \
  "$fragments/simple_dirty_read_commit_base.ml.inc" dirty
generate "$restarting" "$inlined_control" DirtyReadRestartingInlined \
  "$generated/slrtc_inlined_dirty_read_restarting.ml" \
  "$fragments/reader_wake_dirty_read.ml.inc" \
  "$fragments/simple_dirty_read_commit_base.ml.inc" dirty
for output in \
  "$generated/slrtc_dormant_simple.ml" \
  "$generated/slrtc_inlined_dormant_simple.ml" \
  "$generated/slrtc_inlined_dirty_read_simple.ml" \
  "$generated/slrtc_dirty_read_simple.ml" \
  "$generated/slrtc_dormant_restarting.ml" \
  "$generated/slrtc_inlined_dormant_restarting.ml" \
  "$generated/slrtc_dirty_read_restarting.ml" \
  "$generated/slrtc_inlined_dirty_read_restarting.ml"
do
  if grep -Eq '@@(CONTROL|RANK_WORKLIST|READER_WAKE|DIRTY_READ_COMMIT|DORMANT_RESTARTING)' "$output"; then
    echo "unexpanded dormant template marker: $output" >&2
    exit 1
  fi
  if ! grep -q 'request_unranked variable' "$output" || \
     ! grep -q 'Control.solve_seeds_with_fuel' "$output"; then
    echo "dormant discovery control is missing: $output" >&2
    exit 1
  fi
done

trap - EXIT HUP INT TERM
