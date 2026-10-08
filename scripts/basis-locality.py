#!/usr/bin/env python3
"""Temporary paired locality experiment; removed before the production PR."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
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

metadata = dict(base=BASE, head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), flags=ENV.get('RUSTFLAGS'), affinity=sorted(os.sched_getaffinity(0)), variants=[256, 512, 1024])
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))
for cmd, name in [(['rustc', '-vV'], 'rustc'), (['lscpu'], 'lscpu'), (['rustc', '--print', 'cfg', '-C', 'target-cpu=native'], 'cfg')]:
    command(cmd, name)

# Identical untimed proof-capture hooks on all three snapshots. No prover hooks.
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
for chunk in metadata['variants']:
    source = Path(f'/tmp/basis-locality-source-{chunk}')
    command(['git', 'worktree', 'add', '--detach', source, BASE if chunk == 256 else metadata['head']], f'checkout-{chunk}')
    path = source / 'crates/pcs/src/whir/sumcheck.rs'
    text = path.read_text()
    text, count = re.subn(r'pub\(crate\) const INITIAL_BASIS_CHUNK: usize = \d+;', f'pub(crate) const INITIAL_BASIS_CHUNK: usize = {chunk};', text)
    assert count == 1
    path.write_text(text)
    tracked = source / 'bins/leanvm/src/tracked.rs'
    text = tracked.read_text()
    for marker in ['verified.expect("an honest proof verifies");', 'verified.expect("an honest tree proof verifies");']:
        assert text.count(marker) == 1
        text = text.replace(marker, marker + '\n    capture_locality(&proof.to_bytes());')
    marker = 'let built = tree.tree(LeafShape::of(&proof).expect("an honest announcement"), prover.rate());'
    assert text.count(marker) == 1
    text = text.replace(marker, 'capture_locality(&proof.to_bytes());\n    ' + marker)
    tracked.write_text(text + hook)
    target = Path(f'/tmp/basis-locality-target-{chunk}')
    env = dict(ENV, CARGO_TARGET_DIR=str(target))
    command(SCOPE + ['cargo', 'build', '--release', '-p', 'leanvm-cli'], f'build-{chunk}', source, env)
    binaries[chunk] = target / 'release/leanvm'
    command(['objdump', '-d', '-C', binaries[chunk]], f'assembly-{chunk}')
    command(SCOPE + ['cargo', 'test', '--release', '-p', 'pcs', '--lib'], f'pcs-{chunk}', source, dict(env, LEANVM_NUM_THREADS='4', RUST_TEST_THREADS='2'))

records = []
references = {}
for case in ['leanxmss-100', 'aggregate-leanxmss-100-2to1']:
    for workers in [1, 4, 8, 'default']:
        for pair in range(5):
            order = list(binaries) if pair % 2 == 0 else list(reversed(binaries))
            for chunk in order:
                name = f'{case}-w{workers}-p{pair}-c{chunk}'
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
                    command(SCOPE + [binaries[chunk], 'bench', '--only', case, '--log-inv-rate', '1', '--repeat', '1', '--cooldown', '0'], name, env=env)
                    after = os.getloadavg()
                assert max(before[0], after[0]) <= 20, 'overloaded observation discarded'
                proofs = sorted(OUT.glob(name + '.*.bin'))
                assert len(proofs) == (3 if case.startswith('aggregate') else 1)
                hashes = []
                for i, proof in enumerate(proofs):
                    data = proof.read_bytes()
                    key = (case, i)
                    if key in references:
                        assert data == references[key], f'proof mismatch: {name}, {i}'
                    else:
                        references[key] = data
                    hashes.append(dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
                report = json.loads((OUT / (name + '.out')).read_text())
                records.append(dict(case=case, workers=workers, pair=pair, chunk=chunk, load_before=before, load_after=after, proofs=hashes, report=report))
                (OUT / 'records.json').write_text(json.dumps(records, indent=2))
                print(name, 'verified, byte-identical', flush=True)
# Untimed existing tracing, including the nested Basis span and allocation columns.
for chunk, binary in binaries.items():
    command(SCOPE + [binary, 'leanxmss', '--n', '100', '--repeat', '1', '--cooldown', '0', '--tracing'], f'trace-{chunk}', env=dict(ENV, LEANVM_NUM_THREADS='1'))
