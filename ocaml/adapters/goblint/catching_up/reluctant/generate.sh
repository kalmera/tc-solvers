#!/bin/sh
set -eu

directory=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
extraction_directory="$directory/.."
. "$extraction_directory/select_rank_worklist.sh"
simple_template="$directory/goblint_qsolver_reluctant_simple.ml.in"
restarting_template="$directory/goblint_qsolver_reluctant_restarting.ml.in"
extracted_control="$extraction_directory/../../../extracted/GoblintControl.ml"
inlined_control="$extraction_directory/goblint_control_inlined.ml"
features_restarting="$extraction_directory/goblint_features_restarting.ml"
discovery_order="$extraction_directory/goblint_discovery_order.ml.inc"
trace_support="$extraction_directory/goblint_trace.ml.inc"
output_directory="${CATCHING_UP_OUTPUT:-$extraction_directory/../generated}"

mkdir -p "$output_directory"

generate_solver () {
  source_template=$1
  control=$2
  description=$3
  variant=$4
  configuration=$5
  feature_source=$6
  output=$7
  temporary="$output.tmp"
  adapter="extraction/reluctant/$(basename "$source_template")"
  if [ "$control" = "$inlined_control" ]; then
    control_kind=inlined
  else
    control_kind=extracted
  fi

  {
    echo '(* GENERATED FILE. DO NOT EDIT.'
    echo "   Control: $description"
    echo "   Variant: $variant"
    echo "   Configuration: $configuration"
    echo "   Rank worklist: $rank_worklist_name"
    echo "   Adapter: $adapter"
    echo '   Regenerate with: make second-paper-goblint *)'
    awk -v control="$control" -v control_kind="$control_kind" \
        -v discovery_order="$discovery_order" \
        -v trace_support="$trace_support" \
        -v rank_worklist="$rank_worklist_source" \
        -v variant="$variant" \
        -v feature_source="$feature_source" '
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
      $0 == "    (* @@DISCOVERY_ORDER@@ *)" {
        while ((getline line < discovery_order) > 0) {
          if (line == "    (* @@RANK_WORKLIST@@ *)") {
            print "    module RankQueue = struct"
            while ((getline queue_line < rank_worklist) > 0) {
              if (queue_line == "") print ""; else print "      " queue_line
            }
            close(rank_worklist)
            print "    end"
          } else
            print line
        }
        close(discovery_order)
        next
      }
      $0 == "    (* @@TRACE@@ *)" {
        print "    let trace_supported = true"
        print "    let trace_algorithm = \"" variant "\""
        print "    let trace_control = \"" control_kind "\""
        print ""
        while ((getline line < trace_support) > 0) print line
        close(trace_support)
        next
      }
      skip_feature_interface {
        if ($0 == "end") skip_feature_interface = 0
        next
      }
      $0 == "module type FEATURES = sig" {
        if (variant == "ReluctantRestarting") {
          print "module Features = struct"
          while ((getline line < feature_source) > 0) {
            if (line == "") print ""; else print "  " line
          }
          close(feature_source)
          print "end"
          print ""
          print "module type FEATURES = sig"
          print "  val side_effect_phase_reset : bool"
          print "  val dead_side_elimination : bool"
          print "end"
          print ""
        }
        skip_feature_interface = 1
        next
      }
      $0 == "    (Features : FEATURES)" {
        if (variant == "ReluctantRestarting") print
        next
      }
      $0 == "module SLRTC = Make (Control) (Features)" {
        if (variant == "ReluctantRestarting") print
        else print "module SLRTC = Make (Control)"
        next
      }
      { print }
    ' "$source_template"
  } > "$temporary"
  mv "$temporary" "$output"
}

for source in "$simple_template" "$restarting_template" \
  "$extracted_control" "$inlined_control" \
  "$features_restarting" "$discovery_order" "$trace_support" \
  "$rank_worklist_source"
do
  if [ ! -f "$source" ]; then
    echo "missing reluctant generation input: $source" >&2
    exit 1
  fi
done

if [ "$(grep -c '^    [(][*] @@RANK_WORKLIST@@ [*][)]$' "$discovery_order")" -ne 1 ]; then
  echo "invalid reluctant rank-worklist marker: $discovery_order" >&2
  exit 1
fi

for source_template in "$simple_template" "$restarting_template"
do
  if [ "$(grep -c '^[(][*] @@CONTROL@@ [*][)]$' "$source_template")" -ne 1 ] || \
     [ "$(grep -c '^    [(][*] @@DISCOVERY_ORDER@@ [*][)]$' "$source_template")" -ne 1 ] || \
     [ "$(grep -c '^    [(][*] @@TRACE@@ [*][)]$' "$source_template")" -ne 1 ]; then
    echo "invalid reluctant adapter markers: $source_template" >&2
    exit 1
  fi
done

trap 'rm -f "$output_directory"/slrtc_reluctant_*.ml.tmp \
  "$output_directory"/slrtc_inlined_reluctant_*.ml.tmp' EXIT HUP INT TERM

generate_solver "$simple_template" "$extracted_control" \
  "Rocq extraction/QSolverGoblintControl.v" "ReluctantSimple" \
  "first-discovery Reluctant Simple; aggregate-covered side joins" "" \
  "$output_directory/slrtc_reluctant_simple.ml"
generate_solver "$simple_template" "$inlined_control" \
  "extraction/goblint_control_inlined.ml" "ReluctantSimple" \
  "first-discovery Reluctant Simple; aggregate-covered side joins" "" \
  "$output_directory/slrtc_inlined_reluctant_simple.ml"

generate_solver "$restarting_template" "$extracted_control" \
  "Rocq extraction/QSolverGoblintControl.v" "ReluctantRestarting" \
  "first-discovery Reluctant Restarting; both feature switches enabled" \
  "$features_restarting" "$output_directory/slrtc_reluctant_restarting.ml"
generate_solver "$restarting_template" "$inlined_control" \
  "extraction/goblint_control_inlined.ml" "ReluctantRestarting" \
  "first-discovery Reluctant Restarting; both feature switches enabled" \
  "$features_restarting" "$output_directory/slrtc_inlined_reluctant_restarting.ml"

for output in \
  "$output_directory/slrtc_reluctant_simple.ml" \
  "$output_directory/slrtc_inlined_reluctant_simple.ml" \
  "$output_directory/slrtc_reluctant_restarting.ml" \
  "$output_directory/slrtc_inlined_reluctant_restarting.ml"
do
  if grep -q '@@RANK_WORKLIST@@' "$output"; then
    echo "unexpanded reluctant rank-worklist marker: $output" >&2
    exit 1
  fi
  if ! grep -q 'reluctant_side_update source target' "$output"; then
    echo "reluctant side update is missing: $output" >&2
    exit 1
  fi
  if ! grep -q 'mark_controlled target_info target_rank owner_rank;' "$output" || \
     ! grep -q 'mark_controlled frame.owner_info source_rank target_rank;' "$output"; then
    echo "rank promotion check failed: $output" >&2
    exit 1
  fi
done

for fixed_output in \
  "$output_directory/slrtc_reluctant_simple.ml" \
  "$output_directory/slrtc_inlined_reluctant_simple.ml"
do
  if grep -Eq 'FEATURES|Features[.]' "$fixed_output"; then
    echo "fixed reluctant solver exposes feature configuration: $fixed_output" >&2
    exit 1
  fi
done

trap - EXIT HUP INT TERM
