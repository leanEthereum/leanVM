"""The frame hints' aligned flags, checked by the kernel (`LeanVM/Guest/Bridge/FrAlChk/*.lean`).

Per pack, each compiled function's `Bridge.frAlChk alW plumb core.body (Data.adviceFn j)` by
`decide +kernel`: every callee a call through a frame hint's site names (every arm of a `dispatch`)
is allocated with the hint's `aligned` flag (`Memory.alW`, the budget's `walJ`). Reads the packs
(`Pack/*/B2CData.lean`), the link modules (`Checked/Link*.lean`, compiled index by name) and the
budget's flags (`Memory/GuestWordsA/Data.lean`, `count/words.py`), after `regen-guest.sh` and
`words.py`. Per link module of `Guest/Checked`, each function's check by index (`Bridge.FrAlJ`,
`Bridge.frAlJ_of`, `Link*.lean`), and the assembly over every function (`All.lean`: `frAlJ_all`).
`--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/fral.py [--check]
"""
import os, sys, glob, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import progal

OUT = os.path.join(data.ROOT, 'Bridge', 'FrAlChk')
HEAD = genfiles.header('bridge-cert/fral.py')


def run(check):
    idx = {}
    for p in sorted(glob.glob(os.path.join(data.ROOT, 'Checked', 'Link*.lean'))):
        for m in re.finditer(r'^kernel_rfl code(\d+) : fnOf \d+ = Fn\.«([^»]+)»\.code$', open(p, encoding='utf-8').read(), re.M):
            idx[m.group(2)] = int(m.group(1))
    # each function's core IR, in some pack's `Core.lean`
    core = {}
    for p in sorted(glob.glob(os.path.join(data.ROOT, 'Pack', '*', 'Core.lean'))):
        for k in re.findall(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', open(p, encoding='utf-8').read(), re.M):
            core[k] = os.path.basename(os.path.dirname(p))
    files, n = {}, 0
    pack_of = {}
    for d in sorted(glob.glob(os.path.join(data.ROOT, 'Pack', '*'))):
        pack = os.path.basename(d)
        b2c = os.path.join(d, 'B2CData.lean')
        if not os.path.exists(b2c):
            continue
        ks = re.findall(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', open(b2c, encoding='utf-8').read(), re.M)
        ks = [k for k in ks if k in idx]
        if not ks:
            continue
        mod = f'LeanVM.Guest.Bridge.FrAlChk.«{pack}»'
        body = ''.join(f'''theorem Fn.«{k}».frAlOk :
    Bridge.frAlChk (fun g ↦ Data.walJ (coreIdx g)) Fn.«{k}».plumb Fn.«{k}».core.body Data.adviceFn{idx[k]} = true := by
  decide +kernel

''' for k in ks)
        n += len(ks)
        for k in ks:
            pack_of[k] = mod
        files[os.path.join(OUT, f'{pack}.lean')] = (
            HEAD(mod=mod, what=f"The kernel's check of the frame hints' aligned flags of pack `{pack}`'s functions.")
            + 'public import LeanVM.Guest.Bridge.FrAl\npublic import LeanVM.Guest.Memory.GuestWordsA.Data\npublic import LeanVM.Guest.Memory.GuestIdx\n'
            + f'public import LeanVM.Guest.Pack.«{pack}».B2CData\n'
            + ''.join(f'public import LeanVM.Guest.Pack.«{c}».Core\n' for c in sorted({core[k] for k in ks}))
            + 'public import Statement.Data.AdviceHints\nimport all Statement.Data.AdviceHints\n' + '''
namespace LeanVM.Guest

set_option linter.all false

public section

''' + body + '''end

end LeanVM.Guest
''')
    lk = progal.links()
    nf = max(lk) + 1
    groups = {}
    for j in sorted(lk):
        groups.setdefault(lk[j][1], []).append(j)
    for lmod, js in sorted(groups.items()):
        imps = {'LeanVM.Guest.Bridge.FrAlLink', 'LeanVM.Guest.Memory.GuestWordsA', f'LeanVM.Guest.Checked.{lmod}',
                f'LeanVM.Guest.Bridge.ProgAl.Tab{lmod[len("Link"):]}'} | {pack_of[lk[j][0]] for j in js}
        body = []
        for j in js:
            k, _, hp = lk[j]
            pe = f'Checked.plumbEq{j}' if hp else f'Bridge.ProgAl.plumbEq{j}'
            body.append(f'theorem fal{j} : Bridge.FrAlJ Memory.alW {j} := '
                        f'Bridge.frAlJ_of Checked.core{j} {pe} Bridge.ProgAl.tab{j} Fn.«{k}».frAlOk\n')
        files[os.path.join(OUT, f'{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.FrAlChk.{lmod}',
                 what=f"The functions of `Checked.{lmod}` pass the frame hints' flags check, by index.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''
namespace LeanVM.Guest.Bridge.FrAlChk

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.FrAlChk
''')
    pred = 'fun j ↦ Bridge.FrAlJ Memory.alW j'
    step = 256
    parts = [(lo, min(lo + step, nf)) for lo in range(1, nf, step)]
    thms = ''.join(f'''theorem frAlJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.FrAlJ Memory.alW j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := {pred}) {la} {lb} fal{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = progal.bisect([lo for lo, _ in parts] + [nf], lambda a, la, lb: f'(frAlJ_{a} j {la} {lb})')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.FrAlChk.All', what="Every compiled function passes the frame hints' flags check.")
        + ''.join(f'public import LeanVM.Guest.Bridge.FrAlChk.{m}\n' for m in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.FrAlChk

open LeanVM.Guest

public section

{thms}/-- **Every compiled function passes the frame hints' flags check** at the budget's flags. -/
theorem frAlJ_all : ∀ j, 1 ≤ j → j < nFns → Bridge.FrAlJ Memory.alW j := fun j h1 (h2 : j < {nf}) ↦
  {top}

end

end LeanVM.Guest.Bridge.FrAlChk
''')
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: the frame hints\' flags of {n} functions in {len(files)} packs')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
