#!/usr/bin/env python3
"""Temporary hardware attribution driver; diagnostic branch only."""
import fcntl
import glob
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path.cwd()
OUT = ROOT / 'attribution'
OUT.mkdir(exist_ok=True)
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=16G', '-p', 'MemorySwapMax=0']
BASE = os.environ.get('BASE') or '5cfcc744c059bbb134294f2c07c2d442ec7fb8ef'
ENV = dict(os.environ, LEANVM_NUM_THREADS='1', CARGO_BUILD_JOBS='4', CARGO_TERM_COLOR='never')
FOLLOWUP = os.environ.get('ATTRIBUTION_PHASE') == 'followup'

def command(args, name, cwd=ROOT, env=ENV, required=True):
    measured = name.startswith(('components-', 'perf-')) or name == 'stream.jsonl'
    if measured:
        deadline = time.monotonic() + 600
        while os.getloadavg()[0] >= 12:
            if time.monotonic() > deadline:
                raise RuntimeError('load never below 12')
            time.sleep(5)
        before = os.getloadavg()
    with (OUT / name).open('w') as log:
        result = subprocess.run(list(map(str, args)), cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
    if measured:
        after = os.getloadavg()
        accepted = max(before[0], after[0]) <= 20
        with (OUT / 'component-loads.jsonl').open('a') as receipt:
            receipt.write(json.dumps(dict(name=name, load_before=before, load_after=after, accepted=accepted)) + '\n')
        if not accepted:
            raise RuntimeError(f'{name}: overloaded sample discarded')
    if required and result.returncode:
        print((OUT / name).read_text()[-16000:], flush=True)
        raise RuntimeError(f'{name}: exit {result.returncode}')
    return result.returncode

metadata = {'base': BASE, 'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), 'affinity': sorted(os.sched_getaffinity(0)), 'page_size': os.sysconf('SC_PAGE_SIZE'), 'flags': ENV.get('RUSTFLAGS'), 'workers': 1, 'workload': 'leanxmss --n 100 --repeat 1 --cooldown 0 --tracing', 'warmup': 'CLI warm_then_measure discards one full proving pass per invocation', 'files': {}}
for pattern in ['/proc/cpuinfo', '/proc/sys/kernel/perf_event_paranoid', '/sys/kernel/mm/transparent_hugepage/*', '/sys/devices/system/cpu/cpu0/cache/index*/*', '/sys/devices/system/cpu/cpufreq/policy*/*']:
    for name in glob.glob(pattern):
        try:
            metadata['files'][name] = Path(name).read_text()
        except (OSError, UnicodeError):
            pass
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))
for args, name in [(['rustc', '-vV'], 'rustc.txt'), (['rustc', '--print', 'cfg', '-C', 'target-cpu=native'], 'cfg.txt'), (['lscpu'], 'lscpu.txt'), (['uname', '-a'], 'uname.txt')]:
    command(args, name)

baseline = Path('/tmp/arm-attribution-baseline')
if not FOLLOWUP:
    command(['git', 'worktree', 'add', '--detach', baseline, BASE], 'baseline-checkout.log')
binaries = {}
variants = [('trace', ROOT, ''), ('tiled', ROOT, ' --cfg leanvm_round1_neon_tiled'), ('chunk1024', ROOT, ' --cfg leanvm_basis_chunk1024'), ('staged', ROOT, ' --cfg leanvm_basis_staged')] if FOLLOWUP else [('base', baseline, ''), ('trace', ROOT, ''), ('staged', ROOT, ' --cfg leanvm_basis_staged --cfg leanvm_basis_check')]
check_cfg = ' --check-cfg=cfg(leanvm_basis_staged) --check-cfg=cfg(leanvm_basis_check) --check-cfg=cfg(leanvm_round1_neon_tiled) --check-cfg=cfg(leanvm_basis_chunk1024)'
test_exes = {}
for side, cwd, extra in variants:
    target = Path('/tmp/arm-attribution-target-' + side)
    environment = dict(ENV, CARGO_TARGET_DIR=str(target), RUSTFLAGS=ENV.get('RUSTFLAGS', '') + extra + check_cfg)
    command(SCOPE + ['cargo', 'build', '--release', '-p', 'leanvm-cli'], f'build-{side}.log', cwd, environment)
    binaries[side] = target / 'release/leanvm'
    command(['nm', '-C', binaries[side]], f'symbols-{side}.txt', required=False)
    if side != 'base':
        command(['objdump', '-d', '-C', binaries[side]], f'assembly-{side}.txt', required=False)
    if side == 'trace' or (FOLLOWUP and side == 'tiled'):
        command(SCOPE + ['cargo', 'test', '--release', '-p', 'flock', '--lib', '--no-run', '--message-format=json'], f'build-components-{side}.log', env=environment)
        exes = []
        for line in (OUT / f'build-components-{side}.log').read_text().splitlines():
            if line.startswith('{'):
                msg = json.loads(line)
                if msg.get('reason') == 'compiler-artifact' and msg.get('executable') and msg.get('profile', {}).get('test'):
                    exes.append(msg['executable'])
        assert len(exes) == 1, exes
        test_exes[side] = exes[0]

records = []
def save():
    (OUT / 'records.json').write_text(json.dumps(records, indent=2))

def run(side, pair, tracing=True, extra_env=None):
    with open('/tmp/leanvm-bench.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        deadline = time.monotonic() + 600
        while os.getloadavg()[0] >= 12:
            if time.monotonic() > deadline:
                raise RuntimeError('load never below 12')
            time.sleep(5)
        before = os.getloadavg()
        name = f'{pair}-{side}' + ('' if tracing else '-quiet')
        proof = OUT / (name + '.bin')
        env = dict(ENV, ARM_ATTRIBUTION_PROOF=str(proof), **(extra_env or {}))
        args = [binaries[side], 'leanxmss', '--n', '100', '--repeat', '1', '--cooldown', '0']
        if tracing:
            args += ['--tracing']
        start = time.monotonic()
        command(SCOPE + args, name + '.log', env=env)
        after = os.getloadavg()
        record = {'name': name, 'pair': pair, 'side': side, 'tracing': tracing, 'load_before': before, 'load_after': after, 'accepted': max(before[0], after[0]) <= 20, 'wall_s': time.monotonic() - start}
        if proof.exists():
            data = proof.read_bytes()
            record.update(proof_bytes=len(data), proof_sha256=hashlib.sha256(data).hexdigest())
        records.append(record)
        save()
        print(json.dumps(record), flush=True)
        return record['accepted']

# Both binaries use identical workload, worker count, compiler and native flags.
# Every process excludes its internal warmup. Alternating pairs measure added spans.
for pair in range(5):
    for side in (list(binaries) if pair % 2 == 0 else list(reversed(binaries))):
        if not run(side, pair):
            if not run(side, str(pair) + '-retry'):
                raise RuntimeError('repeated overloaded sample')
# No-subscriber controls separate tracing output/collection from code shape effects.
for pair in range(0 if FOLLOWUP else 5):
    for side in (['base', 'trace'] if pair % 2 == 0 else ['trace', 'base']):
        run(side, 'quiet-' + str(pair), tracing=False)

command(SCOPE + ['rustc', '-O', '-C', 'target-cpu=native', 'scripts/arm-attribution-stream.rs', '-o', '/tmp/arm-attribution-stream'], 'build-stream.log')
with open('/tmp/leanvm-bench.lock', 'a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    command(SCOPE + ['/tmp/arm-attribution-stream'], 'stream.jsonl')
# Select the classes dominating actual traced production work, not guessed sizes.
shapes = []
for line in (OUT / '0-trace.log').read_text().splitlines():
    line = re.sub(r'\x1b\[[0-9;]*m', '', line)
    match = re.search(r'Round1 class \[ ([0-9.]+)(ns|µs|ms|s)', line)
    if match:
        fields = dict(re.findall(r'(class|m|k_log|useful_bits|live_blocks): ([0-9]+)', line))
        elapsed = float(match[1]) * {'ns': 1e-9, 'µs': 1e-6, 'ms': 1e-3, 's': 1}[match[2]]
        shapes.append(dict(fields, elapsed_s=elapsed))
shapes.sort(key=lambda item: item['elapsed_s'], reverse=True)
(OUT / 'class-shapes.json').write_text(json.dumps(shapes, indent=2))
capture = OUT / 'round1-inputs'
run('trace', 'capture', extra_env={'ARM_ATTRIBUTION_INPUT_DIR': str(capture)})
# Perf failure is evidence, not a reason to change runner policy.
with open('/tmp/leanvm-bench.lock', 'a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    if shutil.which('perf'):
        args = [binaries['trace'], 'leanxmss', '--n', '100', '--repeat', '1', '--cooldown', '0']
        command(SCOPE + ['perf', 'stat', '-e', 'cycles,instructions,branches,branch-misses,cache-references,cache-misses', '--'] + args, 'perf-stat.txt', required=False)
        status = command(SCOPE + ['perf', 'record', '-F', '499', '-g', '-o', OUT / 'perf.data', '--'] + args, 'perf-record.txt', required=False)
        if not status:
            command(['perf', 'report', '--stdio', '-i', OUT / 'perf.data'], 'perf-report.txt', required=False)
    else:
        (OUT / 'perf-unavailable.txt').write_text('perf executable not installed; no runner policy changes attempted\n')
for shape in shapes[:3]:
    for sample in range(5):
        for side in (list(test_exes) if sample % 2 == 0 else list(reversed(test_exes))):
            env = dict(ENV, ROUND1_INPUT_DIR=str(capture / ('class' + shape['class'])), ROUND1_REPEATS='1', ROUND1_SAMPLE_WINDOWS='256')
            with open('/tmp/leanvm-bench.lock', 'a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                command(SCOPE + [test_exes[side], 'zerocheck::round1::tests::diagnostic_round1_components', '--exact', '--ignored', '--nocapture'], f'components-{side}-class{shape["class"]}-{sample}.log', env=env)

# Last invocation is a genuine production proof and verification, not a component bypass.
run('trace', 'final-proof')
hashes = {r['proof_sha256'] for r in records if 'proof_sha256' in r}
assert len(hashes) == 1, f'diagnostic proof byte mismatch: {hashes}'
print('All diagnostic production proof bytes agree; all invocations proved and verified.', flush=True)
