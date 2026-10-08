#!/usr/bin/env python3
"""Temporary paired locality experiment; removed before the production PR."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path.cwd()
OUT = ROOT / 'locality-evidence'
OUT.mkdir(exist_ok=True)
BASE = os.environ['BASE']
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=16G', '-p', 'MemorySwapMax=0']
ENV = dict(os.environ, CARGO_BUILD_JOBS='4', CARGO_TERM_COLOR='never')

def command(args, name, cwd=ROOT, env=ENV):
    with (OUT / (name + '.out')).open('w') as out, (OUT / (name + '.err')).open('w') as err:
        result = subprocess.run(list(map(str, args)), cwd=cwd, env=env, stdout=out, stderr=err)
    if result.returncode:
        print((OUT / (name + '.err')).read_text()[-16000:], flush=True)
        raise RuntimeError(f'{name}: {result.returncode}')

metadata = dict(base=BASE, head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), flags=ENV.get('RUSTFLAGS'), affinity=sorted(os.sched_getaffinity(0)), variants=['base', 'head'])
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))
for cmd, name in [(['rustc', '-vV'], 'rustc'), (['lscpu'], 'lscpu'), (['rustc', '--print', 'cfg', '-C', 'target-cpu=native'], 'cfg')]:
    command(cmd, name)

# Identical untimed proof-capture hooks on both snapshots. No prover hooks.
hook = '''
fn capture_locality(bytes: &[u8]) {
    if let Some(path) = std::env::var_os("LOCALITY_PROOF") {
        static INDEX: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let index = INDEX.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        std::fs::write(std::path::PathBuf::from(path).with_extension(format!("{index}.bin")), bytes).unwrap();
    }
}
'''
binaries = {}
for side in metadata['variants']:
    source = Path(f'/tmp/basis-locality-source-{side}')
    command(['git', 'worktree', 'add', '--detach', source, metadata[side]], f'checkout-{side}')
    tracked = source / 'bins/leanvm/src/tracked.rs'
    text = tracked.read_text()
    for marker in ['verified.expect("an honest proof verifies");', 'verified.expect("an honest tree proof verifies");']:
        assert text.count(marker) == 1
        text = text.replace(marker, marker + '\n    capture_locality(&proof.to_bytes());')
    marker = 'let built = tree.tree(LeafShape::of(&proof).expect("an honest announcement"), prover.rate());'
    assert text.count(marker) == 1
    text = text.replace(marker, 'capture_locality(&proof.to_bytes());\n    ' + marker)
    tracked.write_text(text + hook)
    target = Path(f'/tmp/basis-locality-target-{side}')
    env = dict(ENV, CARGO_TARGET_DIR=str(target))
    command(SCOPE + ['cargo', 'build', '--release', '-p', 'leanvm-cli'], f'build-{side}', source, env)
    binaries[side] = target / 'release/leanvm'
    command(['objdump', '-d', '-C', binaries[side]], f'assembly-{side}')
    command(SCOPE + ['cargo', 'test', '--release', '-p', 'pcs', '--lib'], f'pcs-{side}', source, dict(env, LEANVM_NUM_THREADS='4', RUST_TEST_THREADS='2'))

records = []
references = {}
# Missing rates and wider recursion shape; repeat rate one only on x86 to check
# that retaining its original byte-sliced chunk removes the screened regressions.
cases = [('leanxmss-100', 4), ('aggregate-leanxmss-100-4to1', 2)]
if os.uname().machine == 'x86_64':
    cases += [('leanxmss-100', 1), ('aggregate-leanxmss-100-2to1', 1)]
for case, rate in cases:
    for workers in [1, 4, 8, 'default']:
        for pair in range(5):
            order = list(binaries) if pair % 2 == 0 else list(reversed(binaries))
            for side in order:
                name = f'{case}-r{rate}-w{workers}-p{pair}-{side}'
                env = dict(ENV, LOCALITY_PROOF=str(OUT / name))
                env.pop('LEANVM_NUM_THREADS', None)
                if workers != 'default':
                    env['LEANVM_NUM_THREADS'] = str(workers)
                with open('/tmp/leanvm-bench.lock', 'a') as lock:
                    fcntl.flock(lock, fcntl.LOCK_EX)
                    deadline = time.monotonic() + 600
                    while os.getloadavg()[0] >= 12:
                        if time.monotonic() > deadline:
                            raise RuntimeError('load never below 12')
                        time.sleep(5)
                    before = os.getloadavg()
                    command(SCOPE + [binaries[side], 'bench', '--only', case, '--log-inv-rate', str(rate), '--repeat', '1', '--cooldown', '0'], name, env=env)
                    after = os.getloadavg()
                assert max(before[0], after[0]) <= 20, 'overloaded observation discarded'
                proofs = sorted(OUT.glob(name + '.*.bin'))
                assert len(proofs) == (3 if case.startswith('aggregate') else 1)
                hashes = []
                for i, proof in enumerate(proofs):
                    data = proof.read_bytes()
                    key = (case, rate, i)
                    if key in references:
                        assert data == references[key], f'proof mismatch: {name}, {i}'
                    else:
                        references[key] = data
                    hashes.append(dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
                report = json.loads((OUT / (name + '.out')).read_text())
                records.append(dict(case=case, rate=rate, workers=workers, pair=pair, side=side, load_before=before, load_after=after, proofs=hashes, report=report))
                (OUT / 'records.json').write_text(json.dumps(records, indent=2))
                print(name, 'verified, byte-identical', flush=True)
# Untimed existing tracing, including the nested Basis span and allocation columns.
for side, binary in binaries.items():
    command(SCOPE + [binary, 'leanxmss', '--n', '100', '--repeat', '1', '--cooldown', '0', '--tracing'], f'trace-{side}', env=dict(ENV, LEANVM_NUM_THREADS='1'))
