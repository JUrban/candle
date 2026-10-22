#!/usr/bin/env bash
set -euo pipefail

# DEVELOPMENT / NON-RELEASE.
#
# Validate the exact textual forest emitted by
# capture_cv_compute_analytic_expr_matan_prep520_all_certificates.ml.  This
# checks the untrusted preparation artifact's shape; it does not replace the
# reflected numerical or analytic checker.

if [[ $# -ne 1 ]]; then
  printf 'usage: %s CAPTURE_LOG\n' "$0" >&2
  exit 2
fi

capture_log=$1
[[ -f "$capture_log" ]]

LC_ALL=C awk '
BEGIN {
  expected_leaves[0] = 401; expected_branch0[0] = 283; expected_branch1[0] = 118;
  expected_leaves[1] = 327; expected_branch0[1] = 321; expected_branch1[1] = 6;
  expected_leaves[2] = 183; expected_branch0[2] = 183; expected_branch1[2] = 0;
  expected_leaves[3] = 398; expected_branch0[3] = 398; expected_branch1[3] = 0;
}

function value(prefix,    i, answer) {
  answer = "";
  for (i = 1; i <= NF; i++) {
    if (index($i,prefix) == 1) {
      answer = $i;
      sub("^" prefix,"",answer);
      return answer;
    }
  }
  return answer;
}

function fail(message) {
  print "prep520 capture validation: " message > "/dev/stderr";
  errors++;
}

/CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_LEAF / {
  component = value("component=");
  leaf_index = value("leaf=");
  branch = value("branch=");
  raw = value("raw=");
  path = value("path=");
  lower = value("lower=");
  upper = value("upper=");

  if (component !~ /^[0-3]$/ || leaf_index !~ /^[0-9]+$/ ||
      branch !~ /^[01]$/ || raw != "false" || path == "" ||
      lower == "" || upper == "") {
    fail("malformed leaf record at line " NR);
    next;
  }

  leaf_key = component SUBSEP path;
  index_key = component SUBSEP leaf_index;
  if (leaf[leaf_key]++)
    fail("duplicate path for component " component ": " path);
  if (leaf_index_seen[index_key]++)
    fail("duplicate leaf index for component " component ": " leaf_index);

  leaf_count[component]++;
  branch_count[component,branch]++;

  lower_count = split(lower,lower_coordinate,",");
  upper_count = split(upper,upper_coordinate,",");
  if (lower_count != 6 || upper_count != 6) {
    fail("non-six-dimensional box at line " NR);
  } else {
    for (coordinate = 1; coordinate <= 6; coordinate++) {
      if (lower_coordinate[coordinate] !~ /^-?[0-9]+(\/[1-9][0-9]*)?$/ ||
          upper_coordinate[coordinate] !~ /^-?[0-9]+(\/[1-9][0-9]*)?$/)
        fail("malformed exact rational at line " NR);
    }
  }

  depth = split(path,path_component,"[.]");
  kraft[component] += 2 ^ (-depth);
  prefix = "";
  for (step = 1; step <= depth; step++) {
    parent_key = component SUBSEP prefix;
    internal[parent_key] = 1;
    token = path_component[step];
    if (token !~ /^[LR][1-6]$/) {
      fail("malformed split token at line " NR ": " token);
      continue;
    }
    side = substr(token,1,1);
    axis = substr(token,2,1);
    child_key = parent_key SUBSEP side;
    if ((child_key in child_axis) && child_axis[child_key] != axis)
      fail("inconsistent split axis below component " component ": " prefix);
    child_axis[child_key] = axis;
    prefix = (prefix == "" ? token : prefix "." token);
  }
}

/CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_COMPONENT_RESULT / {
  component = value("component=");
  if (component !~ /^[0-3]$/) {
    fail("malformed component summary at line " NR);
    next;
  }
  component_summary_count[component]++;
  summary_leaves[component] = value("leaves=");
  summary_branch0[component] = value("branch0=");
  summary_branch1[component] = value("branch1=");
  summary_glue[component] = value("glue=");
  if ($0 !~ /source_id=prep-5202826650 a/)
    fail("wrong source identity in component summary at line " NR);
}

/CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_RESULT / &&
!/CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_COMPONENT_RESULT / {
  final_result_count++;
  final_components = value("components=");
  final_leaves = value("leaves=");
  final_glue = value("glue=");
  final_historical = value("historical_legacy_leaves=");
  final_assumptions = value("assumptions=");
  final_axiom_growth = value("axiom_growth=");
  if ($0 !~ /source_id=prep-5202826650 a/)
    fail("wrong source identity in final result at line " NR);
}

/CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_OK/ {
  ok_count++;
}

END {
  for (key in internal) {
    split(key,key_component,SUBSEP);
    component = key_component[1];
    prefix = key_component[2];
    internal_count[component]++;
    if (leaf[key])
      fail("leaf path is also an internal prefix: component " component ": " prefix);

    left_key = key SUBSEP "L";
    right_key = key SUBSEP "R";
    if (!(left_key in child_axis) || !(right_key in child_axis)) {
      fail("incomplete binary node: component " component ": " prefix);
      continue;
    }
    if (child_axis[left_key] != child_axis[right_key])
      fail("sibling split-axis mismatch: component " component ": " prefix);

    axis = child_axis[left_key];
    left_path = (prefix == "" ? "L" axis : prefix ".L" axis);
    right_path = (prefix == "" ? "R" axis : prefix ".R" axis);
    if (!((component SUBSEP left_path) in leaf) &&
        !((component SUBSEP left_path) in internal))
      fail("missing left child: component " component ": " prefix);
    if (!((component SUBSEP right_path) in leaf) &&
        !((component SUBSEP right_path) in internal))
      fail("missing right child: component " component ": " prefix);
  }

  total_leaves = 0;
  total_internal = 0;
  total_branch0 = 0;
  total_branch1 = 0;
  for (component = 0; component < 4; component++) {
    if (leaf_count[component] != expected_leaves[component])
      fail("unexpected leaf count for component " component);
    if (internal_count[component] != expected_leaves[component] - 1)
      fail("tree is not full for component " component);
    if (branch_count[component,0] != expected_branch0[component] ||
        branch_count[component,1] != expected_branch1[component])
      fail("unexpected branch census for component " component);
    if (kraft[component] < 0.999999999 || kraft[component] > 1.000000001)
      fail("incomplete prefix code for component " component);
    if (component_summary_count[component] != 1 ||
        summary_leaves[component] != expected_leaves[component] ||
        summary_branch0[component] != expected_branch0[component] ||
        summary_branch1[component] != expected_branch1[component] ||
        summary_glue[component] != expected_leaves[component] - 1)
      fail("component summary mismatch for component " component);
    for (leaf_index = 0; leaf_index < expected_leaves[component]; leaf_index++) {
      if (!leaf_index_seen[component SUBSEP leaf_index])
        fail("missing leaf index for component " component ": " leaf_index);
    }

    total_leaves += leaf_count[component];
    total_internal += internal_count[component];
    total_branch0 += branch_count[component,0];
    total_branch1 += branch_count[component,1];
  }

  if (final_result_count != 1 || ok_count != 1 || final_components != 4 ||
      final_leaves != 1309 || final_glue != 1305 || final_historical != 1335 ||
      final_assumptions != 0 || final_axiom_growth != 0)
    fail("final capture marker mismatch");

  printf "CANDLE_CV_MATAN_PREP520_CAPTURE_VALIDATED";
  printf " DEVELOPMENT_NON_RELEASE components=4 leaves=%d internal=%d", total_leaves,total_internal;
  printf " branch0=%d branch1=%d dimensions=6\n", total_branch0,total_branch1;
  if (errors)
    exit 1;
}
' "$capture_log"

printf 'capture_log_sha256=%s\n' "$(sha256sum "$capture_log" | awk '{print $1}')"
