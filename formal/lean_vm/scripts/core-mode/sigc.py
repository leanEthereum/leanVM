"""Writes `LeanVM/Guest/CoreMode/Sig/<pack>.lean`: each function's signature (`Fn.«k».csig : Mode.Sig`), what its
callers are told of it: its entry, the frame cells and heap facts it needs at entry and
guarantees at return; and the glue `LeanVM/Guest/CoreMode/GlueE/<pack>.lean`: each function's entry pc
(`Fn.«k».entry`), the only place the core route's data names it.

Every function keeps its signature: its contract, given by hand in its rule file (`fn/<f>.py`'s `CONTRACTS`, written
with `sigseed.py`'s literals), or else as written (`CoreMode/Sig/<pack>.lean`), which the core route's checks hold to
its heap signature (`CoreMode.ownOk`, `fitB`), its frame cells checked against the frame layout (`compiled.fsig`). So a
function's signature, and its callers' certificates, change only when its contract does. A function new to the guest,
one whose frame layout changed, or one named by `--fresh` needs one in its rule file; without one there, the script
stops and names it.

usage (from formal/lean_vm): python3 -I scripts/core-mode/sigc.py [--check] [--fresh NAME,..]"""
import os, re, sys, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import genfiles  # noqa: E402
sys.setrecursionlimit(100000)
import compiled as C  # noqa: E402
import fnrules  # noqa: E402
SEEDS = fnrules.table('CONTRACTS') or {}

ROOT = C.ROOT
OUT = os.path.join(ROOT, 'CoreMode', 'Sig')
GLUE = os.path.join(ROOT, 'CoreMode', 'GlueE')
# `def Fn.«k».csig : Mode.Sig := ⟨Fn.«k».entry, ..⟩` up to the next declaration or the section's end
CSIG = re.compile(r'noncomputable def Fn\.«([^»]+)»\.csig\s*:\s*Mode\.Sig\s*:=\s*⟨Fn\.«[^»]+»\.entry, (.*?)⟩\n(?=noncomputable|\nend)',
                  re.S)


header = genfiles.header('core-mode/sigc.py')


SIG_HEAD = ('/-\n  %s\n\n  What a caller knows of compiled functions: their contracts, the source of their\n'
            '  signatures. `scripts/core-mode/sigc.py` rewrites this file keeping each contract as\n'
            '  written, or a function\'s rule file\'s (`fn/<f>.py` `CONTRACTS`) in its place, and\n'
            '  stops on a function with neither.\n-/\n\nmodule\n\n')


def written():
    """Each function's signature as written, the literal's fields past its entry, by key."""
    out = {}
    for f in glob.glob(os.path.join(OUT, '*.lean')):
        for m in CSIG.finditer(open(f, encoding='utf-8').read()):
            out[m.group(1)] = ' '.join(m.group(2).split())
    return out


def layout_ok(fields, fsig):
    """The written signature's entry cells, self cell and return cells are the frame layout's."""
    parts = C.split_top(fields)
    ent, slf, ret = C.parse(parts[0]), C.parse(parts[1]), C.parse(parts[5])
    return ent == fsig[0] and ret == fsig[2] and slf == (('id', 'none') if fsig[1] is None else ('some', fsig[1]))


def signatures(fresh=()):
    """Each function's signature's fields past its entry, by compiled name, and how many were kept."""
    D = C.code()
    old = written()
    out, kept, need = {}, 0, []
    for n, f in D['fns'].items():
        k = f['ns']
        if k in SEEDS:
            # a contract given by hand (its rule file's)
            out[n] = ' '.join(SEEDS[k].split())
        elif k in old and k not in fresh and layout_ok(old[k], D['fsig'][f['entry']]):
            out[n] = old[k]
            kept += 1
        else:
            need.append(k)
    if need:
        raise SystemExit('sigc: no contract written or in its rule file (fn/<f>.py CONTRACTS) for: ' + ', '.join(sorted(need)))
    return out, kept


def files(lits):
    out = {}
    D = C.code()
    for p, names in sorted(C.packs().items()):
        sec = '\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\n@[expose] public section\n\n'
        body = [SIG_HEAD % ('LeanVM.Guest.CoreMode.Sig.«%s»' % p),
                'public import LeanVM.Guest.Mode.Abs\npublic import LeanVM.Guest.CoreMode.GlueE.«%s»\n' % p, sec]
        glue = [header('LeanVM.Guest.CoreMode.GlueE.«%s»' % p, 'The entry pc of each compiled function of the pack.'),
                'namespace LeanVM.Guest\n\n@[expose] public section\n\n']
        for n in sorted(names, key=lambda n: D['fns'][n]['ns']):
            k = D['fns'][n]['ns']
            body.append('noncomputable def Fn.«%s».csig : Mode.Sig :=\n  ⟨Fn.«%s».entry, %s⟩\n' % (k, k, lits[n]))
            glue.append('abbrev Fn.«%s».entry : Nat := %d\n' % (k, D['fns'][n]['entry']))
        body.append('\nend\n\nend LeanVM.Guest\n'); glue.append('\nend\n\nend LeanVM.Guest\n')
        out[os.path.join(OUT, '%s.lean' % p)] = C.wrap(''.join(body))
        out[os.path.join(GLUE, '%s.lean' % p)] = ''.join(glue)
    return out


def glue_g():
    """`CoreMode/GlueG.lean`: the program's constants the core route's certificates name."""
    return {os.path.join(ROOT, 'CoreMode', 'GlueG.lean'): (
        header('LeanVM.Guest.CoreMode.GlueG', 'The program\'s constants the core route\'s certificates name.') +
        'namespace LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
        '/-- The jump table\'s first cell, `main`\'s frame size. -/\nabbrev jtLo : Nat := %d\n\n'
        '/-- The jump table\'s end. -/\nabbrev jtHi : Nat := %d\n\n'
        '/-- The halting pc, the program\'s last. -/\nabbrev haltPc : Nat := %d\n\n'
        'end\n\nend LeanVM.Guest.CoreMode\n' % (C.code()['jt_lo'], C.code()['jt_hi'], C.code()['halt']))}


def main(argv):
    fresh = set(argv[argv.index('--fresh') + 1].split(',')) if '--fresh' in argv else set()
    lits, kept = signatures(fresh)
    want = files(lits)
    want.update(glue_g())
    check = '--check' in argv
    have = glob.glob(os.path.join(OUT, '*.lean')) + glob.glob(os.path.join(GLUE, '*.lean'))
    stale = genfiles.sync(want, have, check)
    genfiles.fail_if_stale(stale, check)
    print('signatures: %d functions (%d kept as written), %d packs' % (len(lits), kept, len(want) // 2))


if __name__ == '__main__':
    main(sys.argv[1:])
