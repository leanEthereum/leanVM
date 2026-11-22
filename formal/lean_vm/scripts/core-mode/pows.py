"""Each function's own table of the powers of `g` its constants name (`CoreMode/Pows/<pack>.lean`).

For every function, in the pack holding its core, `Fn.«k».pows` holds the pairs `(k, e)`, `K.ofBits k = g^e`, of
`Data.powTree` whose `k` is a constant of its core, as a search tree; `Fn.«k».pows_ok` checks them in
the kernel. The core route's heap checks and route data take this table instead of `Data.powTree`, so
they read no other function's constants and no code pointer. The frame walk's table, with the code
pointers its `SET`s name, is its own (`fpows`, `frame_gen.py`).

usage (from formal/lean_vm): python3 -I scripts/core-mode/pows.py [--check]
"""
import sys, os, re, glob
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compiled as C  # noqa: E402

LV = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
GUEST = os.path.join(LV, 'LeanVM', 'Guest')
OUT = os.path.join(GUEST, 'CoreMode', 'Pows')

SET = re.compile(r'\(\.set \d+ (\d+) 0\)')  # read by `frame_gen.py`
WORD = re.compile(r'\(word (\d+) 0\)')


def global_pows():
    t = open(os.path.join(GUEST, 'Data', 'Pows.lean'), encoding='utf-8').read()
    t = t[:t.index('noncomputable def jtTrie')]
    return {int(k): int(e) for k, e in re.findall(r'\.node (\d+) (\d+)', t)}


def tree(pairs):
    """A balanced search tree by `k`."""
    if not pairs:
        return '.leaf'
    m = len(pairs) // 2
    k, e = pairs[m]
    return f'(.node {k} {e} {tree(pairs[:m])} {tree(pairs[m + 1:])})'


def main(check=False):
    G = global_pows()
    consts, home = {}, {}
    for k, bs in C.BD.core_blocks().items():
        # the function's pack: the one holding its core, as `heap.pack_of`
        home[k] = bs[0][0]
        consts[k] = {int(x) for _, _, text in bs for x in WORD.findall(text)}
    packs = {}
    for k, pack in home.items():
        packs.setdefault(pack, {})[k] = consts[k]
    want = {}
    for pack, fns in sorted(packs.items()):
        out = [genfiles.header('core-mode/pows.py')(f'LeanVM.Guest.CoreMode.Pows.«{pack}»',
                                                    'The powers of `g` each function of the pack names.') +
               f'public import LeanVM.Guest.Pow\n\nset_option linter.all false\nset_option linter.style.nameCheck false\n']
        out.append('\n/-! Each function\'s powers of `g` its constants name (`pows`), checked in the kernel (`pows_ok`). -/\n\n'
                   'namespace LeanVM.Guest\n\n@[expose] public section\n\n')
        for k in sorted(fns):
            pairs = sorted((x, G[x]) for x in fns[k] if x in G)
            out.append(f'noncomputable def Fn.«{k}».pows : Exec.PowTree := {tree(pairs)}\n'
                       f'theorem Fn.«{k}».pows_ok : pows.OkW := Exec.PowTree.okW_of_okWB (by decide +kernel)\n')
        out.append('\nend\n\nend LeanVM.Guest\n')
        want[os.path.join(OUT, pack + '.lean')] = ''.join(out)
    stale = genfiles.sync(want, glob.glob(os.path.join(OUT, '*.lean')), check)
    genfiles.fail_if_stale(stale, check)
    print('pows: %d packs, %d functions' % (len(want), sum(len(f) for f in packs.values())))


if __name__ == '__main__':
    main('--check' in sys.argv)
