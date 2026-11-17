#!/bin/sh
set -eu

directory=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
extraction_directory="$directory/../../runtime"
. "$directory/select_rank_worklist.sh"
simple_template="$directory/goblint_slrtc_simple.ml.in"
restarting_template="$directory/goblint_slrtc_restarting.ml.in"
extracted_control="$directory/../../extracted/GoblintControl.ml"
inlined_control="$directory/goblint_control_inlined.ml"
features_restarting="$directory/goblint_features_restarting.ml"
discovery_order="$directory/goblint_discovery_order.ml.inc"
trace_support="$directory/goblint_trace.ml.inc"
update_source="$directory/goblint_slrtc_update.ml"
output_directory="$directory/generated"

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
  adapter="ocaml/adapters/goblint/$(basename "$source_template")"
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
    echo '   Regenerate with: make goblint-solvers *)'
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
          if (line == "")
            print ""
          else
            print "  " line
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
        while ((getline line < trace_support) > 0)
          print line
        close(trace_support)
        next
      }
      skip_feature_interface {
        if ($0 == "end")
          skip_feature_interface = 0
        next
      }
      $0 == "module type FEATURES = sig" {
        if (variant == "Restarting") {
          print "module Features = struct"
          while ((getline line < feature_source) > 0) {
            if (line == "")
              print ""
            else
              print "  " line
          }
          close(feature_source)
          print "end"
          print ""
          print "module type FEATURES = sig"
          print "  val side_effect_phase_reset : bool"
          print "  val dead_side_elimination : bool"
          print "  val recompute_controlled : bool"
          print "end"
        }
        if (variant == "Restarting")
          print ""
        skip_feature_interface = 1
        next
      }
      $0 == "    (Features : FEATURES)" {
        if (variant == "Restarting")
          print
        next
      }
      $0 == "module SLRTC = Make (Control) (Features)" {
        if (variant == "Restarting")
          print
        else
          print "module SLRTC = Make (Control)"
        next
      }
      { print }
    ' "$source_template"
  } > "$temporary"
  mv "$temporary" "$output"
}

for source in "$simple_template" "$restarting_template" \
  "$extracted_control" "$inlined_control" \
  "$features_restarting" "$discovery_order" "$trace_support" "$update_source" \
  "$rank_worklist_source"
do
  if [ ! -f "$source" ]; then
    echo "missing generation input: $source" >&2
    exit 1
  fi
done

for source_template in "$simple_template" "$restarting_template"
do
  if [ "$(grep -c '^[(][*] @@CONTROL@@ [*][)]$' "$source_template")" -ne 1 ]; then
    echo "expected exactly one control marker in $source_template" >&2
    exit 1
  fi
  if [ "$(grep -c '^    [(][*] @@DISCOVERY_ORDER@@ [*][)]$' "$source_template")" -ne 1 ]; then
    echo "expected exactly one discovery-order marker in $source_template" >&2
    exit 1
  fi
  if [ "$(grep -c '^    [(][*] @@TRACE@@ [*][)]$' "$source_template")" -ne 1 ]; then
    echo "expected exactly one trace marker in $source_template" >&2
    exit 1
  fi
done

if [ "$(grep -c '^    [(][*] @@RANK_WORKLIST@@ [*][)]$' "$discovery_order")" -ne 1 ]; then
  echo "expected exactly one rank-worklist marker in $discovery_order" >&2
  exit 1
fi

trap 'rm -f \
  "$output_directory/slrtc_simple.ml.tmp" \
  "$output_directory/slrtc_inlined_simple.ml.tmp" \
  "$output_directory/slrtc_restarting.ml.tmp" \
  "$output_directory/slrtc_inlined_restarting.ml.tmp" \
  "$output_directory/slrtc_update.ml.tmp"' EXIT HUP INT TERM

generate_solver "$simple_template" "$extracted_control" \
  "rocq/extraction/GoblintControl.v" \
  "Simple" \
  "first-discovery instance of the policy-parametric Simple algorithm" \
  "" \
  "$output_directory/slrtc_simple.ml"

generate_solver "$simple_template" "$inlined_control" \
  "ocaml/adapters/goblint/goblint_control_inlined.ml" \
  "Simple" \
  "first-discovery instance of the policy-parametric Simple algorithm" \
  "" \
  "$output_directory/slrtc_inlined_simple.ml"

generate_solver "$restarting_template" "$extracted_control" \
  "rocq/extraction/GoblintControl.v" \
  "Restarting" \
  "first-discovery instance; side-reset and dead-side enabled; controlled-owner recomputation disabled" \
  "$features_restarting" \
  "$output_directory/slrtc_restarting.ml"

generate_solver "$restarting_template" "$inlined_control" \
  "ocaml/adapters/goblint/goblint_control_inlined.ml" \
  "Restarting" \
  "first-discovery instance; side-reset and dead-side enabled; controlled-owner recomputation disabled" \
  "$features_restarting" \
  "$output_directory/slrtc_inlined_restarting.ml"

for output in \
  "$output_directory/slrtc_simple.ml" \
  "$output_directory/slrtc_inlined_simple.ml" \
  "$output_directory/slrtc_restarting.ml" \
  "$output_directory/slrtc_inlined_restarting.ml"
do
  if grep -q '@@RANK_WORKLIST@@' "$output"; then
    echo "unexpanded rank-worklist marker: $output" >&2
    exit 1
  fi
done

for fixed_output in \
  "$output_directory/slrtc_simple.ml" \
  "$output_directory/slrtc_inlined_simple.ml"
do
  if grep -Eq 'FEATURES|Features[.]' "$fixed_output"; then
    echo "fixed solver unexpectedly exposes feature configuration: $fixed_output" >&2
    exit 1
  fi
done

simple_foreign_state='reset_at_close|last_targets|read_dependencies|prepared_targets|deferred_dead|previous_targets|current_targets|min_scope|max_read_rank|outgoing_cells|touched_side|contributions[[:space:]]*:'
for simple_output in \
  "$output_directory/slrtc_simple.ml" \
  "$output_directory/slrtc_inlined_simple.ml"
do
  if grep -Eq "$simple_foreign_state" "$simple_output"; then
    echo "Simple adapter contains state for another variant: $simple_output" >&2
    exit 1
  fi
done

restarting_foreign_state='episode_mode|prepared_targets|deferred_dead|touched_side|max_read_rank|normal_phases'
for restarting_output in \
  "$output_directory/slrtc_restarting.ml" \
  "$output_directory/slrtc_inlined_restarting.ml"
do
  if grep -Eq 'Features[.](variant|normal_phase_reset)' "$restarting_output"; then
    echo "Restarting exposes an unproved feature switch: $restarting_output" >&2
    exit 1
  fi
  if grep -Eq "$restarting_foreign_state" "$restarting_output"; then
    echo "Restarting adapter contains state for another variant: $restarting_output" >&2
    exit 1
  fi
done

for supported_output in \
  "$output_directory/slrtc_simple.ml" \
  "$output_directory/slrtc_inlined_simple.ml" \
  "$output_directory/slrtc_restarting.ml" \
  "$output_directory/slrtc_inlined_restarting.ml"
do
  if ! grep -q 'mark_controlled target_info target_rank owner_rank;' \
      "$supported_output"; then
    echo "correct read promotion is missing: $supported_output" >&2
    exit 1
  fi
  if ! grep -q 'mark_controlled frame.owner_info source_rank target_rank;' \
      "$supported_output"; then
    echo "correct side promotion is missing: $supported_output" >&2
    exit 1
  fi
  if grep -Eq \
      'mark_controlled target_info owner_rank target_rank|mark_controlled frame[.]owner_info target_rank (source_rank|dependency_rank|read_rank)' \
      "$supported_output"; then
    echo "flipped promotion remains in adapter: $supported_output" >&2
    exit 1
  fi
done

{
  echo '(* GENERATED FILE. DO NOT EDIT.'
  echo '   Source: ocaml/adapters/goblint/goblint_slrtc_update.ml'
  echo '   Regenerate with: make goblint-solvers *)'
  sed -n '1,$p' "$update_source"
} > "$output_directory/slrtc_update.ml.tmp"
mv "$output_directory/slrtc_update.ml.tmp" \
  "$output_directory/slrtc_update.ml"

trap - EXIT HUP INT TERM
