"""The hint bridge's per-function checks: the jump cells' (`jumpcells.py`), the computed hints' (`pair.py`), the witness
hints' (`wit.py`) and the allocation hints' (`alloc.py`), each with its link modules and assembly. A hash pack's checks
of the four are one module (`LeanVM/Guest/Bridge/Chk/<pack>.lean`), and so are a link module's
(`Chk/Link*.lean`), so that each pays its imports once; a long function's and a named pack's stay apart. Run after
`progal.py`; `--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/checks.py [--check]
"""
import os, re, sys, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import jumpcells, pair, wit, alloc

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'Chk')
# each check's module of a hash pack `P<n>`, or of a link module `Link<n>`, by its name
KINDS = ((jumpcells, 'JumpCells', 'P_'), (pair, 'PairChk', ''), (wit, 'WitChk', ''), (alloc, 'AllocChk', ''))


def run(check):
    files, existing = {}, set(glob.glob(os.path.join(OUT, '*.lean')))
    for m, _, _ in KINDS:
        fs, ex = m.gen()
        files.update(fs)
        existing |= ex
    groups = {}
    for _, d, pre in KINDS:
        for p in sorted(files):
            name = os.path.basename(p)[:-len('.lean')]
            if os.path.dirname(p) != os.path.join(BR, d):
                continue
            if name.startswith(pre) and re.fullmatch(r'P\d+', name[len(pre):]):
                name = name[len(pre):]
                mod, what = f'LeanVM.Guest.Bridge.Chk.«{name}»', f"The bridge's checks of pack `{name}`'s functions."
            elif re.fullmatch(r'Link\d+', name):
                mod, what = f'LeanVM.Guest.Bridge.Chk.{name}', f"The bridge's checks of the functions of `Checked.{name}`."
            else:
                continue
            groups.setdefault(os.path.join(OUT, name + '.lean'), (mod, what, []))[2].append(p)
    files = data.sequential(genfiles.merge(files, groups, genfiles.header('bridge-cert/checks.py')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: {len(groups)} modules of checks merged')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
