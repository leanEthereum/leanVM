#!/usr/bin/env python3
"""Write every module `scripts/b1c-vt` generates from `verify_tables`' core IR and the guest's
constants: `LeanVM/Guest/B1/Tables/Vt/*` (the templates `FormsT*`, `SortT`, `SharedT`, the totals,
the selectors, the forms' data) and their completeness twins in `Tables/VtC/`. Run from `lean_vm`
after `guest-core` (`regen-guest.sh`, step `vt`):

    python3 -I scripts/b1c-vt/all.py [--check]

The generators run in a scratch mirror of `Tables/` (the body dumped by `dump.py` there, nothing
left in this directory), in dependency order; `--check` writes nothing and fails naming each stale
module. A module written whole gets a "do not edit" line in its header; four modules are partly
written (the data definitions of `Vt/FormsData`, `Vt/FormsPad`, `Vt/EvalsT` and `VtC/FData`).
The generators read the body at fixed statement positions, so a change to `verify_tables` itself
is a change to them.
"""
import os, re, shutil, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
TABLES = Path('LeanVM/Guest/B1/Tables')
NOTE = '  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).\n'

# (generator and its arguments, the modules it writes whole, the module its stdout is)
JOBS = [
    (['gendiff.py'], ['Vt/FormsDiff'], None),
    (['genbterms.py'], [], None),
    (['genevals.py'], [], None),
    (['genfdata.py'], [], None),
    (['gensel.py'], ['Vt/SelBlocks'], None),
    (['genshared.py'], ['Vt/SharedT'], None),
    (['gensort.py'], ['Vt/SortT'], None),
    (['gentotal.py'], ['Vt/PushPad', 'Vt/PushFw', 'Vt/PullTotal', 'Vt/CountTotal'], None),
    (['genpull.py'], ['Vt/PullSels'], None),
] + [(['mk.py', str(t)], [f'Vt/FormsT{t}'], None) for t in range(5)] + [
    (['-c', 'import mk; mk.gen_t5()'], ['Vt/FormsT5a', 'Vt/FormsT5b', 'Vt/FormsT5'], None),
    (['genair.py'], ['Vt/Air'], None),
    (['gencshared.py'], ['VtC/SShT'], None),
    (['gencsort.py'], ['VtC/SGrpT'], None),
    (['gentwins.py'], [f'VtC/F{b}' for b in
                       ['Forms0', 'Forms1', 'Forms2', 'Forms3', 'Forms4', 'Forms5', 'Forms5a', 'Forms5b', 'Air']], None),
    (['genbtwin.py'], [], 'VtC/BTwin'),
    (['genaux.py'], [], 'VtC/RcReads'),
    (['genbglue.py'], [], 'VtC/BGlueGen'),
    (['genstores.py'], [], 'VtC/Stores'),
]
PARTLY = ['Vt/FormsData', 'Vt/FormsPad', 'Vt/EvalsT', 'VtC/FData']


def noted(text):
    """The module with the "do not edit" line closing its header."""
    if NOTE in text:
        return text
    i = text.index('-/\n')
    return text[:i] + '\n' + NOTE + text[i:]


def main(check):
    whole = [m for _, ms, out in JOBS for m in ms + ([out] if out else [])]
    with tempfile.TemporaryDirectory() as tmp:
        mirror = Path(tmp)
        gen = mirror / 'scripts' / 'b1c-vt'
        shutil.copytree(HERE, gen, ignore=shutil.ignore_patterns('vt_ir.txt', '__pycache__'))
        shutil.copytree(ROOT / TABLES, mirror / TABLES)
        (mirror / 'LeanVM/Guest/Data').symlink_to(ROOT / 'LeanVM/Guest/Data')
        (mirror / 'LeanVM/Guest/Pack').symlink_to(ROOT / 'LeanVM/Guest/Pack')
        shutil.copy(HERE.parent / 'coredata.py', mirror / 'scripts' / 'coredata.py')
        def run(args, out=None):
            r = subprocess.run([sys.executable, '-I', *args], cwd=gen, capture_output=True, text=True)
            if r.returncode:
                sys.exit(f'b1c-vt: {" ".join(args)} failed:\n{r.stderr}')
            if out:
                (mirror / TABLES / f'{out}.lean').write_text(r.stdout)
        run(['dump.py', '../../LeanVM/Guest/Data', 'vt_ir.txt'])
        for args, _, out in JOBS:
            # `-c` runs with this directory on the path, as a run of the script itself would
            run(['-c', f'import sys; sys.path.insert(0, "."); {args[1]}'] if args[0] == '-c' else args, out)
        for m in whole:
            p = mirror / TABLES / f'{m}.lean'
            p.write_text(noted(p.read_text()))
        stale = []
        for m in whole + PARTLY:
            new = (mirror / TABLES / f'{m}.lean').read_text()
            dst = ROOT / TABLES / f'{m}.lean'
            if not dst.exists() or dst.read_text() != new:
                stale.append(m)
                if not check:
                    dst.write_text(new)
        for m in stale:
            print(f'{"stale" if check else "w"} {TABLES / m}.lean')
        print(f'b1c-vt: {len(whole) + len(PARTLY)} modules, {len(stale)} {"stale" if check else "written"}')
        return 1 if check and stale else 0


if __name__ == '__main__':
    args = sys.argv[1:]
    if args not in ([], ['--check']):
        sys.exit('usage: python3 -I scripts/b1c-vt/all.py [--check]')
    sys.exit(main(args == ['--check']))
