#!/bin/sh
# Checks the comparison benchmarks' workloads and dashboard, and that bindings CI runs this script.
# The benchmark workflows (a PR suite and a main-branch history publishing to GitHub Pages) were not
# migrated with the bindings: they need a dedicated self-hosted runner (see
# bindings/benchmarks/comparison/README.md), so their policy checks went with them.
set -eu

cd "$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"

ci_workflow=.github/workflows/bindings-ci.yml
dashboard_builder=bindings/scripts/build_benchmark_dashboard.py
dashboard_test=bindings/scripts/test_benchmark_dashboard.py
dashboard_html=bindings/benchmarks/comparison/dashboard/index.html
comparison_bench=bindings/benchmarks/comparison/benches/comparison.rs
slow_comparison=bindings/benchmarks/comparison/src/bin/slow_comparison.rs

fail() {
  echo "benchmark CI policy: $*" >&2
  exit 1
}

require_file() {
  [ -f "$1" ] || fail "missing $1"
}

require_text() {
  file=$1
  pattern=$2
  description=$3
  grep -Eq -- "$pattern" "$file" || fail "$file: missing $description"
}

require_literal() {
  file=$1
  literal=$2
  description=$3
  grep -Fq -- "$literal" "$file" || fail "$file: missing $description"
}

reject_text() {
  file=$1
  pattern=$2
  description=$3
  if grep -Eq -- "$pattern" "$file"; then
    fail "$file: contains forbidden $description"
  fi
}

for file in "$ci_workflow" "$dashboard_builder" "$dashboard_test" "$dashboard_html" "$comparison_bench" "$slow_comparison"; do
  require_file "$file"
done

reject_text "$comparison_bench" 'benchmark_group\("public_key"\)' 'public-key derivation timing benchmark'
reject_text "$comparison_bench" 'benchmark_group\("key_creation"\)|secret_key_16_slots' 'obsolete 16-slot Criterion key benchmark'
reject_text "$comparison_bench" '^fn lighthouse_(same_claim|distinct_claim|signature_sets)' 'Lighthouse-only fast aggregate benchmark'
require_text "$comparison_bench" 'benchmark_group\("independent_signatures_verify"\)' 'paired independent-signature verification benchmark'
require_text "$comparison_bench" 'verify_signature_sets' 'batched BLS verification side of the independent-signature workload'
reject_text "$slow_comparison" 'measure_signature_sets_verify|LIGHTHOUSE_SIGNATURE_SETS_WORKLOAD' 'Lighthouse-only supplemental signature-set benchmark'
require_literal "$slow_comparison" 'comparisons.push(measure_key_creation(config.samples)?)' 'explicit key-creation benchmark'
require_literal "$slow_comparison" 'lean_pq::xmss::SecretKey::from_seed' 'leanXMSS key-creation workload'
reject_text "$slow_comparison" 'KEY_CREATION_SLOTS|merge_claims|MultiClaimProof' 'obsolete pre-leanXMSS API'
require_text "$comparison_bench" '"public_key/lean".*lean_public_key\.to_bytes\(\)\.len' 'LeanVM serialized public-key size'
require_text "$comparison_bench" '"public_key/lighthouse".*bls_public_key\.serialize\(\)\.len' 'Lighthouse serialized public-key size'

if ! awk '
  /^  rust:/ { in_rust = 1; next }
  in_rust && /^  [[:alnum:]_-]+:/ { in_rust = 0 }
  in_rust && /sh bindings\/scripts\/check-benchmark-ci\.sh/ { found = 1 }
  END { exit !found }
' "$ci_workflow"; then
  fail "$ci_workflow: Rust job must run sh bindings/scripts/check-benchmark-ci.sh"
fi

python3 "$dashboard_test" >/dev/null

echo "benchmark CI policy checks passed"
