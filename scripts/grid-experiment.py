#!/usr/bin/env python3
"""Temporary actual-hardware grid experiment, removed before shipping."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path.cwd()
OUT = ROOT / 'grid-evidence'
OUT.mkdir(exist_ok=True)
BASE = os.environ.get('BASE', 'f52bd991c8623894e7b03a2e50bede6c248ea1ad')
PRODUCTION = '4b3b3d1728b95b5acc2a7e9300303d9da4d9a76d'
DIAGNOSTIC = 'ceb165c833f16df100776168f84849fbe5e7ec2c'
HEAD = os.environ['CANDIDATE']
DRIVER = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=16G', '-p', 'MemorySwapMax=0']
ENV = dict(os.environ, CARGO_BUILD_JOBS='4', CARGO_TERM_COLOR='never')
ENV.pop('LEANVM_NUM_THREADS', None)
FLAGS = '-C target-cpu=native --check-cfg=cfg(leanvm_grid_candidate)'
records = []

def run(args, name, cwd=ROOT, env=None):
    with (OUT / name).open('w') as log:
        p = subprocess.run(list(map(str, args)), cwd=cwd, env=env or ENV, stdout=log, stderr=subprocess.STDOUT)
    if p.returncode:
        print((OUT / name).read_text()[-16000:], flush=True)
        raise RuntimeError(f'{name}: exit {p.returncode}')

def measured(args, name, env):
    with open('/tmp/leanvm-bench.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        deadline = time.monotonic() + 900
        while os.getloadavg()[0] >= 12:
            if time.monotonic() > deadline:
                raise RuntimeError('load never below 12')
            time.sleep(5)
        before = os.getloadavg()
        run(SCOPE + args, name, env=env)
        after = os.getloadavg()
        record = dict(name=name, before=before, after=after, accepted=max(before[0], after[0]) <= 20)
        records.append(record)
        (OUT / 'loads.json').write_text(json.dumps(records, indent=2))
        if not record['accepted']:
            raise RuntimeError(f'{name}: overloaded sample discarded')

for command, name in [(['rustc', '-vV'], 'compiler.txt'), (['lscpu'], 'cpu.txt'), (['rustc', '--print', 'cfg', '-C', 'target-cpu=native'], 'cfg.txt')]:
    run(command, name)
if os.uname().machine == 'aarch64':
    cfg = (OUT / 'cfg.txt').read_text()
    assert 'target_feature="aes"' in cfg and 'target_feature="sha3"' in cfg
(OUT / 'metadata.json').write_text(json.dumps(dict(base=BASE, head=HEAD, driver=DRIVER, flags=FLAGS, affinity=sorted(os.sched_getaffinity(0)), phase='final', cases='leaf rate2; first and higher2to1 nodes at rates1,2; captured dense correctness once per worker'), indent=2))
base = Path('/tmp/grid-base')
candidate = Path('/tmp/grid-head')
run(['git', 'worktree', 'add', '--detach', base, BASE], 'checkout-base.log')
run(['git', 'worktree', 'add', '--detach', candidate, HEAD], 'checkout-head.log')
patch = subprocess.check_output(['git', 'diff', PRODUCTION, DIAGNOSTIC, '--', 'crates/pcs/src/whir/sumcheck/first_pass.rs', 'crates/pcs/src/whir/sumcheck/grid_diagnostic.rs', 'bins/leanvm/src/tracked.rs'])
(OUT / 'diagnostic.patch').write_bytes(patch)
for side, cwd in [('base', base), ('head', candidate)]:
    run(['git', 'apply', OUT / 'diagnostic.patch'], f'apply-{side}.log', cwd=cwd)
    fixture = Path('crates/pcs/src/whir/sumcheck/grid_diagnostic.rs')
    shutil.copyfile(ROOT / fixture, cwd / fixture)
# Use the original production input captures, not a newly generated or synthetic workload.
capture = Path(os.getenv('CAPTURE_DIR', '/tmp/grid-capture/basis-inputs'))
if not capture.exists():
    run(['gh', 'run', 'download', '37755153088', '--repo', 'leanEthereum/leanVM', '--name', 'attribution-arm64', '--dir', '/tmp/grid-capture'], 'capture-download.log')
for name, size in [('witness.bin', 81788928), ('weight.bin', 245366784), ('shape.bin', 24)]:
    data = (capture / name).read_bytes()
    assert len(data) == size
    with (OUT / 'capture-hashes.txt').open('a') as receipt:
        receipt.write(f'{name} {len(data)} {hashlib.sha256(data).hexdigest()}\n')
executables = {}
tests = {}
variants = ['base', 'head']
for side in variants:
    cwd = base if side == 'base' else candidate
    target = Path('/tmp/grid-target-' + side)
    extra = '' if side == 'base' else ' --cfg leanvm_grid_candidate'
    env = dict(ENV, CARGO_TARGET_DIR=str(target), RUSTFLAGS=FLAGS + extra)
    run(SCOPE + ['cargo', 'build', '--release', '-p', 'leanvm-cli'], f'build-{side}.log', cwd, env)
    run(SCOPE + ['cargo', 'test', '--release', '-p', 'pcs', '--lib', '--no-run', '--message-format=json'], f'test-build-{side}.log', cwd, env)
    messages = [json.loads(line) for line in (OUT / f'test-build-{side}.log').read_text().splitlines() if line.startswith('{')]
    tests[side] = next(m['executable'] for m in messages if m.get('reason') == 'compiler-artifact' and m.get('executable') and m.get('profile', {}).get('test'))
    executables[side] = target / 'release/leanvm'
    run(SCOPE + [tests[side], 'whir::sumcheck::first_pass::tests', '--test-threads=2'], f'correctness-{side}.log')
    run(['objdump', '-d', '-C', executables[side]], f'assembly-{side}.txt')
    run(['nm', '-C', executables[side]], f'symbols-{side}.txt')
    measured([tests[side], 'grid_diagnostic::captured_basis_components', '--ignored', '--nocapture', '--test-threads=1'], f'components-{side}.log', dict(ENV, ARM_ATTRIBUTION_BASIS_DIR=str(capture), LEANVM_NUM_THREADS='1'))

for workers in ['1', '4', '8', 'default']:
    env = dict(ENV, ARM_ATTRIBUTION_BASIS_DIR=str(capture))
    if workers != 'default':
        env['LEANVM_NUM_THREADS'] = workers
    for pair in range(1):
        for side in (variants if pair % 2 == 0 else list(reversed(variants))):
            name = f'dense-{workers}-{pair}-{side}'
            measured([tests[side], 'grid_diagnostic::captured_dense_pass', '--ignored', '--nocapture', '--test-threads=1'], name + '.log', dict(env, GRID_RESULT=str(OUT / (name + '.bin'))))
        for side in variants[1:]:
            assert (OUT / f'dense-{workers}-{pair}-base.bin').read_bytes() == (OUT / f'dense-{workers}-{pair}-{side}.bin').read_bytes()
    for pair in range(5):
        for side in (variants if pair % 2 == 0 else list(reversed(variants))):
            name = f'tail3-{workers}-{pair}-{side}'
            measured([tests[side], 'grid_diagnostic::captured_dense_pass', '--ignored', '--nocapture', '--test-threads=1'], name + '.log', dict(env, GRID_TAIL3='1', GRID_RESULT=str(OUT / (name + '.bin'))))
        assert (OUT / f'tail3-{workers}-{pair}-base.bin').read_bytes() == (OUT / f'tail3-{workers}-{pair}-head.bin').read_bytes()
    cases = [('leanxmss-100', 2), ('aggregate-leanxmss-100-2to1', 1), ('aggregate-leanxmss-100-2to1', 2)]
    for case, rate in cases:
        for pair in range(5):
            for side in (variants if pair % 2 == 0 else list(reversed(variants))):
                name = f'{case}-rate{rate}-{workers}-{pair}-{side}'
                proofs = OUT / (name + '-proofs')
                measured([executables[side], 'bench', '--only', case, '--log-inv-rate', str(rate), '--repeat', '1', '--cooldown', '0', '--tracing'], name + '.log', dict(env, GRID_PROOFS=str(proofs)))
            a = OUT / f'{case}-rate{rate}-{workers}-{pair}-base-proofs'
            for side in variants[1:]:
                b = OUT / f'{case}-rate{rate}-{workers}-{pair}-{side}-proofs'
                assert sorted(p.name for p in a.iterdir()) == sorted(p.name for p in b.iterdir())
                for proof in a.iterdir():
                    assert proof.read_bytes() == (b / proof.name).read_bytes(), proof
                    with (OUT / 'proof-equality.jsonl').open('a') as receipt:
                        receipt.write(json.dumps(dict(case=case, rate=rate, workers=workers, pair=pair, side=side, file=proof.name, bytes=proof.stat().st_size, sha256=hashlib.sha256(proof.read_bytes()).hexdigest())) + '\n')
print('All captured-grid references, paired grids, production verification and literal paired proof bytes passed.', flush=True)
