#!/bin/sh
set -eu

pr_workflow=.github/workflows/benchmarks-pr.yml
history_workflow=.github/workflows/benchmarks-history.yml
ci_workflow=.github/workflows/ci.yml
dashboard_builder=scripts/build_benchmark_dashboard.py
dashboard_test=scripts/test_benchmark_dashboard.py
dashboard_html=benchmarks/comparison/dashboard/index.html
comparison_bench=benchmarks/comparison/benches/comparison.rs
slow_comparison=benchmarks/comparison/src/bin/slow_comparison.rs

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

check_full_action_pins() {
  file=$1
  uses_lines=$(grep -E '^[[:space:]]*-?[[:space:]]*uses:' "$file" || true)
  [ -n "$uses_lines" ] || fail "$file: contains no actions"
  unpinned=$(printf '%s\n' "$uses_lines" | grep -Ev '@[0-9a-f]{40}([[:space:]]*(#.*)?)?$' || true)
  [ -z "$unpinned" ] || fail "$file: every uses reference must have a full immutable SHA pin: $unpinned"
}

for file in "$pr_workflow" "$history_workflow" "$dashboard_builder" "$dashboard_test" "$dashboard_html" "$comparison_bench" "$slow_comparison"; do
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

require_text "$pr_workflow" '^  pull_request:$' 'pull_request trigger'
reject_text "$pr_workflow" 'pull_request_target|workflow_run' 'privileged PR trigger'
reject_text "$pr_workflow" 'write-all|:[[:space:]]*write([[:space:]]|$)' 'write permission'
reject_text "$pr_workflow" '(^|[^[:alnum:]_])secrets([^[:alnum:]_]|$)' 'standalone secrets token'
reject_text "$pr_workflow" 'continue-on-error:' 'suppressed action failure'
reject_text "$pr_workflow" 'benchmark-action|BENCHMARK_HISTORY_ENABLED|save-data-file|dev/bench' 'historical comparison machinery'
reject_text "$pr_workflow" '--action-json' 'obsolete action JSON output'
require_text "$pr_workflow" '^permissions:$' 'top-level permissions block'
require_text "$pr_workflow" '^  contents: read$' 'read-only contents permission'
require_text "$pr_workflow" 'types: \[labeled, unlabeled, synchronize, reopened, closed\]' 'opt-in pull request event types'
require_text "$pr_workflow" '^      - scripts/build_benchmark_dashboard\.py$' 'dashboard builder path trigger'
require_text "$pr_workflow" '^      - scripts/test_benchmark_dashboard\.py$' 'dashboard test path trigger'
reject_text "$pr_workflow" 'benchmark-slow' 'obsolete slow-benchmark label routing'
pr_label_guards=$(grep -Fc "contains(github.event.pull_request.labels.*.name, 'run-benchmarks')" "$pr_workflow" || true)
[ "$pr_label_guards" -eq 2 ] || fail "$pr_workflow: both benchmark jobs must require the run-benchmarks label"
pr_closed_guards=$(grep -Fc "github.event.action != 'closed'" "$pr_workflow" || true)
[ "$pr_closed_guards" -eq 2 ] || fail "$pr_workflow: closing a pull request must cancel rather than restart its benchmarks"
require_literal "$pr_workflow" 'timeout-minutes: 30' '30-minute fast timeout'
require_literal "$pr_workflow" 'timeout-minutes: 180' '180-minute slow timeout'
require_literal "$pr_workflow" 'retention-days: 14' '14-day artifact retention'
reject_text "$pr_workflow" '--output-format bencher' 'lossy Bencher-format Criterion output'
require_literal "$pr_workflow" 'rm -rf -- target/criterion' 'stale Criterion result cleanup'
require_literal "$pr_workflow" '--criterion-dir target/criterion' 'structured Criterion estimates input'
require_literal "$pr_workflow" 'python3 scripts/build_benchmark_dashboard.py fast' 'fast dashboard normalization'
require_literal "$pr_workflow" 'python3 scripts/build_benchmark_dashboard.py slow' 'slow dashboard normalization'
require_literal "$pr_workflow" '--output benchmark-artifacts/fast/dashboard.json' 'fast normalized artifact'
require_literal "$pr_workflow" '--output benchmark-artifacts/slow/dashboard.json' 'slow normalized artifact'
require_literal "$pr_workflow" '| tee -a benchmark-artifacts/slow/slow-output.txt' 'peak RSS in slow summary output'
require_literal "$pr_workflow" 'cargo build --release -p lean-pq-comparison --bin slow_comparison' 'untimed slow-runner build'
require_literal "$pr_workflow" '/usr/bin/time -v -o benchmark-artifacts/slow/resource-usage.txt' 'slow-suite peak RSS measurement'
require_literal "$pr_workflow" 'target/release/slow_comparison' 'direct slow-runner execution'
require_literal "$pr_workflow" 'echo "same_sizes=1,8,16,256,512"' 'normal same-claim proof sizes'
require_literal "$pr_workflow" '--same-sizes 1,8,16,256,512' 'normal same-claim proof arguments'
require_literal "$pr_workflow" 'echo "distinct_sizes=1,8,16"' 'normal distinct-claim proof sizes'
reject_text "$pr_workflow" 'key_creation_slots' 'obsolete key-creation slot metadata'
require_literal "$pr_workflow" '--distinct-sizes 1,8,16' 'normal distinct-claim proof arguments'
require_literal "$pr_workflow" '--mixed-claim-counts 8,16' 'mixed-claim proof arguments'
require_literal "$pr_workflow" 'echo "recursive_fan_ins=2,4,8,16"' 'recursive fan-in metadata'
require_literal "$pr_workflow" '--recursive-fan-ins 2,4,8,16' 'recursive fan-in arguments'
require_literal "$pr_workflow" 'cat benchmark-artifacts/fast/criterion-output.txt' 'direct fast summary'
require_text "$pr_workflow" 'sed .*benchmark-artifacts/slow/slow-output\.txt' 'direct slow summary'
pr_benchmark_runners=$(grep -Fc 'runs-on: size-attester7870-x64' "$pr_workflow" || true)
[ "$pr_benchmark_runners" -eq 2 ] || fail "$pr_workflow: both benchmark jobs must use the size-attester7870-x64 runner"
trusted_pr_jobs=$(grep -Fc 'github.event.pull_request.head.repo.full_name == github.repository' "$pr_workflow" || true)
[ "$trusted_pr_jobs" -eq 2 ] || fail "$pr_workflow: benchmark jobs must reject fork pull requests"
reject_text "$pr_workflow" 'runs-on: ubuntu-24\.04' 'GitHub-hosted benchmark runner'
require_literal "$pr_workflow" 'toolchain: 1.97.0' 'pinned Rust toolchain'
require_literal "$pr_workflow" 'runner_image_os=${ImageOS:-unknown}' 'runner image OS metadata'
require_literal "$pr_workflow" 'runner_image_version=${ImageVersion:-unknown}' 'runner image version metadata'
measured_at_entries=$(grep -Fc 'echo "measured_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)"' "$pr_workflow")
[ "$measured_at_entries" -eq 2 ] || fail "$pr_workflow: both suites must record the measurement time"
reject_text "$pr_workflow" 'lighthouse_revision=[0-9a-f]{40}' 'hardcoded Lighthouse revision'
require_literal "$pr_workflow" 'benchmarks/comparison/Cargo.toml' 'Lighthouse revision manifest source'
require_literal "$pr_workflow" "grep -Eq '^[0-9a-f]{40}$'" 'exact Lighthouse revision validation'
require_literal "$pr_workflow" 'de0fac2e4500dabe0009e67214ff5f5447ce83dd' 'pinned checkout action'
require_literal "$pr_workflow" '35d8a35b823d6c20db516f5c35eb0a9640942c17' 'pinned Rust toolchain action'
require_literal "$pr_workflow" '401aff9a7a08acb9d27b64936a90db81024cff97' 'pinned Rust cache action'
require_literal "$pr_workflow" '043fb46d1a93c77aae656e7c1c64a875d1fc6a0a' 'pinned artifact upload action'
check_full_action_pins "$pr_workflow"

require_text "$history_workflow" '^  push:$' 'push trigger'
require_text "$history_workflow" '^      - main$' 'main branch restriction'
reject_text "$history_workflow" '^  schedule:|cron:' 'scheduled benchmark trigger'
require_text "$history_workflow" '^  workflow_dispatch:$' 'manual trigger'
reject_text "$history_workflow" 'pull_request|pull_request_target|workflow_run' 'untrusted publication trigger'
reject_text "$history_workflow" 'benchmark-action|BENCHMARK_HISTORY_ENABLED|max-items-in-chart|benchmark-data-dir-path' 'historical reporting machinery'
reject_text "$history_workflow" '--action-json' 'obsolete action JSON output'
reject_text "$history_workflow" 'deployments: write' 'unneeded deployment permission'
require_text "$history_workflow" '^permissions:$' 'top-level permissions block'
require_text "$history_workflow" '^  contents: read$' 'read-only measurement permission'
require_literal "$history_workflow" 'group: benchmark-dashboard' 'shared publication concurrency group'
require_literal "$history_workflow" 'cancel-in-progress: false' 'non-cancelling publication concurrency'
history_benchmark_runners=$(grep -Fc 'runs-on: size-attester7870-x64' "$history_workflow" || true)
[ "$history_benchmark_runners" -eq 2 ] || fail "$history_workflow: both measurement jobs must use the size-attester7870-x64 runner"
history_publish_runners=$(grep -Fc 'runs-on: ubuntu-24.04' "$history_workflow" || true)
[ "$history_publish_runners" -eq 1 ] || fail "$history_workflow: only dashboard publication should use GitHub-hosted Ubuntu"
require_literal "$history_workflow" "if: github.event_name == 'push' || (github.event_name == 'workflow_dispatch' && (inputs.suite == 'fast' || inputs.suite == 'all'))" 'fast trigger routing'
require_literal "$history_workflow" "if: github.event_name == 'push' || (github.event_name == 'workflow_dispatch' && (inputs.suite == 'slow' || inputs.suite == 'all'))" 'slow trigger routing'
require_literal "$history_workflow" '[[ "$BENCH_SAMPLES" =~ ^[0-9]+$ ]] && (( 10#$BENCH_SAMPLES >= 3 ))' 'slow sample validation'
require_literal "$history_workflow" '--samples "$BENCH_SAMPLES"' 'validated sample argument'
require_literal "$history_workflow" '--same-sizes "$BENCH_SAME_SIZES"' 'validated same-size argument'
require_literal "$history_workflow" '--distinct-sizes "$BENCH_DISTINCT_SIZES"' 'validated distinct-size argument'
require_literal "$history_workflow" '--mixed-claim-counts 8,16' 'mixed-claim proof arguments'
require_literal "$history_workflow" '--recursive-fan-ins "$BENCH_RECURSIVE_FAN_INS"' 'validated recursive fan-in argument'
require_literal "$history_workflow" "default: '2,4,8,16'" 'manual recursive fan-in defaults'
require_literal "$history_workflow" "inputs.recursive_fan_ins || '2,4,8,16'" 'main-push recursive fan-in defaults'
require_literal "$history_workflow" 'echo "recursive_fan_ins=$BENCH_RECURSIVE_FAN_INS"' 'recursive fan-in metadata'
require_literal "$history_workflow" "default: '1,8,16,256,512'" 'manual same-claim default sizes'
require_literal "$history_workflow" "inputs.same_sizes || '1,8,16,256,512'" 'main-push same-claim default sizes'
require_literal "$history_workflow" "inputs.distinct_sizes || '1,8,16'" 'main-push distinct-claim default sizes'
reject_text "$history_workflow" 'key_creation_slots' 'obsolete key-creation slot metadata'
require_literal "$history_workflow" '--warmup-proofs' 'proof warm-up policy'
reject_text "$history_workflow" '--output-format bencher' 'lossy Bencher-format Criterion output'
require_literal "$history_workflow" 'rm -rf -- target/criterion' 'stale Criterion result cleanup'
require_literal "$history_workflow" '--criterion-dir target/criterion' 'structured Criterion estimates input'
require_literal "$history_workflow" '/usr/bin/time -v -o benchmark-artifacts/slow/resource-usage.txt' 'slow peak RSS measurement'
require_literal "$history_workflow" 'python3 scripts/build_benchmark_dashboard.py fast' 'fast dashboard normalization'
require_literal "$history_workflow" 'python3 scripts/build_benchmark_dashboard.py slow' 'slow dashboard normalization'
require_literal "$history_workflow" 'cp benchmarks/comparison/dashboard/index.html benchmark-artifacts/fast/index.html' 'fast dashboard asset'
require_literal "$history_workflow" 'cp benchmarks/comparison/dashboard/index.html benchmark-artifacts/slow/index.html' 'slow dashboard asset'
require_literal "$history_workflow" '| tee -a benchmark-artifacts/slow/slow-output.txt' 'history peak RSS summary output'
history_measured_at=$(grep -Fc 'echo "measured_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)"' "$history_workflow")
[ "$history_measured_at" -eq 2 ] || fail "$history_workflow: both suites must record the measurement time"
require_literal "$history_workflow" 'retention-days: 30' '30-day fast artifact retention'
require_literal "$history_workflow" 'retention-days: 90' '90-day slow artifact retention'
stable_artifact_names=$(grep -Ec 'name: benchmark-dashboard-(fast|slow)-\$\{\{ github\.run_id \}\}$' "$history_workflow" || true)
artifact_overwrites=$(grep -Fc 'overwrite: true' "$history_workflow" || true)
[ "$stable_artifact_names" -eq 4 ] || fail "$history_workflow: uploads and downloads must use stable run names"
[ "$artifact_overwrites" -eq 2 ] || fail "$history_workflow: rerun uploads must replace earlier artifacts"
require_literal "$history_workflow" "if: always() && (needs.fast.result == 'success' || needs.slow.result == 'success')" 'successful-suite publication gate'
require_literal "$history_workflow" 'ref: gh-pages' 'Pages branch checkout'
require_literal "$history_workflow" 'path: site' 'isolated Pages checkout'
require_literal "$history_workflow" 'cp publish/fast/dashboard.json site/data/fast.json' 'latest fast data replacement'
require_literal "$history_workflow" 'cp publish/slow/dashboard.json site/data/slow.json' 'latest slow data replacement'
require_literal "$history_workflow" 'cp publish/fast/index.html site/index.html' 'root fast dashboard asset'
require_literal "$history_workflow" 'cp publish/slow/index.html site/index.html' 'root slow dashboard asset'
require_literal "$history_workflow" 'touch site/.nojekyll' 'Jekyll bypass'
require_literal "$history_workflow" 'rm -r -- site/dev/bench' 'old nested page cleanup'
require_literal "$history_workflow" 'git push origin HEAD:gh-pages' 'Pages branch publication'
require_literal "$history_workflow" 'de0fac2e4500dabe0009e67214ff5f5447ce83dd' 'pinned checkout action'
require_literal "$history_workflow" '3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c' 'pinned artifact download action'
check_full_action_pins "$history_workflow"

measurement_jobs=$(sed '/^  publish:/,$d' "$history_workflow")
if printf '%s\n' "$measurement_jobs" | grep -Eq 'write-all|:[[:space:]]*write([[:space:]]|$)'; then
  fail "$history_workflow: measurement jobs must not have write permissions"
fi

publication_job=$(awk '
  /^  publish:/ { in_publish = 1 }
  in_publish && !/^  publish:/ && /^  [[:alnum:]_-]+:/ { in_publish = 0 }
  in_publish { print }
' "$history_workflow")
[ -n "$publication_job" ] || fail "$history_workflow: missing publication job"
printf '%s\n' "$publication_job" | grep -Eq '^    permissions:$' || fail "$history_workflow: publication job needs explicit permissions"
printf '%s\n' "$publication_job" | grep -Eq '^      contents: write$' || fail "$history_workflow: publication job needs contents write"
if printf '%s\n' "$publication_job" | grep -Eq 'cargo|python|scripts/|target/'; then
  fail "$history_workflow: publication job must not execute measured repository code"
fi
publication_checkouts=$(printf '%s\n' "$publication_job" | grep -Fc 'actions/checkout@de0fac2e4500dabe0009e67214ff5f5447ce83dd')
publication_downloads=$(printf '%s\n' "$publication_job" | grep -Fc 'actions/download-artifact@3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c')
fast_conditions=$(printf '%s\n' "$publication_job" | grep -Fc "if: needs.fast.result == 'success'")
slow_conditions=$(printf '%s\n' "$publication_job" | grep -Fc "if: needs.slow.result == 'success'")
[ "$publication_checkouts" -eq 1 ] || fail "$history_workflow: publication must have one Pages checkout"
[ "$publication_downloads" -eq 2 ] || fail "$history_workflow: publication must download both possible suites"
[ "$fast_conditions" -eq 1 ] || fail "$history_workflow: fast download must depend on fast success"
[ "$slow_conditions" -eq 1 ] || fail "$history_workflow: slow download must depend on slow success"

require_file "$ci_workflow"
if ! awk '
  /^  rust:/ { in_rust = 1; next }
  in_rust && /^  [[:alnum:]_-]+:/ { in_rust = 0 }
  in_rust && /sh scripts\/check-benchmark-ci\.sh/ { found = 1 }
  END { exit !found }
' "$ci_workflow"; then
  fail "$ci_workflow: Rust job must run sh scripts/check-benchmark-ci.sh"
fi

python3 "$dashboard_test" >/dev/null

echo "benchmark CI policy checks passed"
