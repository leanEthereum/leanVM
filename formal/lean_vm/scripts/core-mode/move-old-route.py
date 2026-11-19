"""Moves the hand modules the old route named and the core route still reads (`formal/notes/core-mode.md`, the `(b)`
moves), after `drop-mode-route.py` deleted the rest, in one mechanical pass: no module named `EndExecR*`, `Res/` or
`Mode/Cert*` is left.

* `EndExecR.lean` -> `CoreMode/Fam/Res.lean`, `EndExecR<X>.lean` -> `CoreMode/Fam/Res<X>.lean`, `EndExecRef.lean`,
  `EndExecRefOk.lean` -> `CoreMode/Fam/Ref.lean`, `RefOk.lean`;
* `Res/<X>.lean` -> `CoreMode/Fam/<X>.lean` (the residual families' definitions and their lemmas);
* `Mode/Cert<X>.lean` -> `CoreMode/Cert<X>.lean`.

Each file is moved (`git mv`), and every reference to its module name rewritten: the `import`s of every Lean file
(`LeanVM/`, `tests/`, `LeanVM.lean`), the moved files' header comments, and the generators' strings
(`scripts/**/*.py`, which write imports of them). Declarations keep their namespaces (`LeanVM.Guest.Res`,
`LeanVM.Guest.EndExec`): no name a proof cites changes. `--dry-run` lists the moves and writes nothing; `--no-git` moves
with the file system.

usage (from formal/lean_vm): python3 -I scripts/core-mode/move-old-route.py [--dry-run] [--no-git]
"""
import os, re, sys, glob, subprocess

LV = os.getcwd()
G = os.path.join(LV, 'LeanVM', 'Guest')
DRY, NOGIT = '--dry-run' in sys.argv, '--no-git' in sys.argv


def moves():
    """Old module name -> new, for the modules present."""
    out = {}
    for p in sorted(glob.glob(os.path.join(G, 'EndExecR*.lean'))):
        b = os.path.basename(p)[:-5]
        if b in ('EndExecRef', 'EndExecRefOk'):
            new = b[len('EndExec'):]
        else:
            new = 'Res' + b[len('EndExecR'):]
        out['LeanVM.Guest.' + b] = 'LeanVM.Guest.CoreMode.Fam.' + new
    for p in sorted(glob.glob(os.path.join(G, 'Res', '*.lean'))):
        b = os.path.basename(p)[:-5]
        out['LeanVM.Guest.Res.' + b] = 'LeanVM.Guest.CoreMode.Fam.' + b
    for p in sorted(glob.glob(os.path.join(G, 'Mode', 'Cert*.lean'))):
        b = os.path.basename(p)[:-5]
        out['LeanVM.Guest.Mode.' + b] = 'LeanVM.Guest.CoreMode.' + b
    return out


def path(mod):
    return os.path.join(LV, *mod.split('.')) + '.lean'


def main():
    mv = moves()
    clash = [n for n in mv.values() if os.path.exists(path(n))]
    if clash or len(set(mv.values())) != len(mv):
        sys.exit('move-old-route: targets exist or repeat: %s' % clash)
    lines = sum(open(path(o), encoding='utf-8').read().count('\n') for o in mv)
    print('modules moved: %d, %d lines' % (len(mv), lines))
    for o, n in mv.items():
        print('  %s -> %s' % (o, n))
    if DRY:
        return
    for o, n in mv.items():
        os.makedirs(os.path.dirname(path(n)), exist_ok=True)
        if NOGIT:
            os.rename(path(o), path(n))
        else:
            subprocess.run(['git', 'mv', path(o), path(n)], check=True)
    # every reference, longest names first (`EndExecRS` before `EndExecR`), whole names only
    rx = re.compile(r'(?<![\w.«])(%s)(?![\w»])' % '|'.join(re.escape(o) for o in sorted(mv, key=len, reverse=True)))
    files = (glob.glob(os.path.join(LV, 'LeanVM', '**', '*.lean'), recursive=True) +
             glob.glob(os.path.join(LV, 'tests', '**', '*.lean'), recursive=True) + [os.path.join(LV, 'LeanVM.lean')] +
             glob.glob(os.path.join(LV, 'scripts', '**', '*.py'), recursive=True))
    changed = 0
    for f in files:
        if f.endswith('move-old-route.py'):
            continue
        t = open(f, encoding='utf-8').read()
        u = rx.sub(lambda m: mv[m.group(1)], t)
        if u != t:
            open(f, 'w', encoding='utf-8').write(u)
            changed += 1
    print('files rewritten: %d; build LeanVM LeanVMTests, then scripts/regen-guest.sh --check' % changed)


if __name__ == '__main__':
    main()
