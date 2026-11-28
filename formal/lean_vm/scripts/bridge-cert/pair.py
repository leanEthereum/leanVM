"""The computed hints' data check of every compiled function (`LeanVM/Guest/Bridge/PairChk/*.lean`).

Per module of alignment checks `align.py` writes (`Bridge/Align/*.lean`, `Bridge/AlignCtx/*/Ctx.lean`), each
function's `Bridge.pairChk` over its pack data and its hint-only cells, by `decide +kernel`;
per link module of `Guest/Checked`, each function's advice the advice's by function (`Bridge.AdvJ`, `PairChk/Adv*.lean`,
apart from the data check) and its check over `Bridge.ctxOf` (`Bridge.pairJ_of`, reusing the `Checked` and `ProgAl` link
equations); and the assemblies over every function (`PairChk/AdvAll.lean`, `PairChk/All.lean`). Run after `progal.py`; `--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/pair.py [--check]
"""
import os, re, sys, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import progal

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'PairChk')
HEAD = genfiles.header('bridge-cert/pair.py')


def check_module(ctx_mod):
    """The module of checks for the functions whose context `ctx_mod` holds."""
    if '.Align.«' in ctx_mod:
        return 'LeanVM.Guest.Bridge.PairChk.«' + ctx_mod.split('.Align.«')[1]
    k = ctx_mod.split('.AlignCtx.«')[1].split('»')[0]
    return f'LeanVM.Guest.Bridge.PairChk.«W_{k}»'


def pack_imports(ctx_mod):
    """The pack modules (bundles, core) the context module `ctx_mod` imports."""
    m = ctx_mod[:-len('.Ok')] + '.Ctx' if ctx_mod.endswith('».Ok') else ctx_mod
    path = os.path.join(data.LEAN_VM, *[x.strip('«»') for x in m.split('.')]) + '.lean'
    return sorted(re.findall(r'^public import (LeanVM\.Guest\.Pack\.\S+)$', open(path, encoding='utf-8').read(), re.M))


def run(check):
    ctxs, lk = progal.contexts(), progal.links()
    n = max(lk) + 1
    files = {}
    # the checks over the pack data
    by_mod = {}
    for j, (k, _, _) in sorted(lk.items()):
        by_mod.setdefault(ctxs[k][2], []).append(k)
    for cm, ks in sorted(by_mod.items()):
        mod = check_module(cm)
        body = data.fn_thms((k, 'pairOk', f'Bridge.pairChk {ctxs[k][0]} cert.locs fs core.body = true',
                             'decide +kernel') for k in ks)
        files[os.path.join(OUT, mod.split('PairChk.')[1].strip('«»') + '.lean')] = (
            HEAD(mod=mod, what="The kernel's checks that compiled functions' computed hints pass the data check.")
            + 'public import LeanVM.Guest.Bridge.PairDefs\n' + ''.join(f'public import {m}\n' for m in pack_imports(cm))
            + '\n' + body.rstrip('\n') + '\n')
    # the checks by index
    groups = {}
    for j in sorted(lk):
        groups.setdefault(lk[j][1], []).append(j)
    fss = set()
    for p in glob.glob(os.path.join(data.ROOT, 'Checked', 'Link*.lean')):
        fss |= set(int(x) for x in re.findall(r'^kernel_rfl fsEq(\d+) ', open(p, encoding='utf-8').read(), re.M))
    for lmod, js in sorted(groups.items()):
        tab = f'LeanVM.Guest.Bridge.ProgAl.Tab{lmod[len("Link"):]}'  # the tables' entries, not the alignment checks
        abody = []
        for j in js:
            abody.append(f'''kernel_rfl adv{j} : Data.adviceFns[{j}]? = some Data.adviceFn{j}
kernel_rfl len{j} : Data.adviceFn{j}.2.1 = (fnOf {j}).instructionCount
theorem aj{j} : Bridge.AdvJ {j} := Bridge.advJ_of Bridge.ProgAl.tab{j} adv{j} len{j}
''')
        files[os.path.join(OUT, f'Adv{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.PairChk.Adv{lmod}',
                        what=f"The functions of `Checked.{lmod}` have the advice's entries as their alignment's advice.")
            + f'public import LeanVM.Guest.Bridge.PairLink\npublic import {tab}\n' + '''meta import LeanVM.Guest.KernelLit
import all Statement.Data.Bytecode
import all Statement.Data.AdviceHints

namespace LeanVM.Guest.Bridge.PairChk

open LeanVM.Guest

public section

''' + ''.join(abody) + '''
end

end LeanVM.Guest.Bridge.PairChk
''')
        imps = {f'LeanVM.Guest.Bridge.PairChk.Adv{lmod}', f'LeanVM.Guest.Checked.{lmod}', tab}
        imps |= {check_module(ctxs[lk[j][0]][2]) for j in js}
        body = []
        for j in js:
            k, _, _ = lk[j]
            fe = f'Checked.fsEq{j}'
            if j not in fss:
                body.append(f'kernel_rfl fsEq{j} : B2C.fsN {j} = Fn.«{k}».fs\n')
                fe = f'fsEq{j}'
            body.append(f'theorem pok{j} : Bridge.PairJ {j} := Bridge.pairJ_of Checked.core{j} Checked.cert{j} '
                        f'Bridge.ProgAl.tab{j} {fe} Fn.«{k}».pairOk aj{j}\n')
        files[os.path.join(OUT, f'{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.PairChk.{lmod}',
                        what=f"The functions of `Checked.{lmod}` pass the computed hints' data check over `Bridge.ctxOf`.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''meta import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Bridge.PairChk

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.PairChk
''')
    step = 256
    parts = [(lo, min(lo + step, n)) for lo in range(1, n, step)]
    thms = ''.join(f'''theorem pairJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.PairJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := fun j ↦ Bridge.PairJ j) {la} {lb} pok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(pairJ_{a} j {la} {lb})')
    athms = ''.join(f'''theorem advJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.AdvJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := fun j ↦ Bridge.AdvJ j) {la} {lb} aj{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    atop = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(advJ_{a} j {la} {lb})')
    files[os.path.join(OUT, 'AdvAll.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.PairChk.AdvAll',
                    what="Every compiled function's alignment advice is the advice's entry.")
        + ''.join(f'public import LeanVM.Guest.Bridge.PairChk.Adv{m}\n' for m in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.PairChk

open LeanVM.Guest

public section

{athms}/-- **Every compiled function's alignment advice is the advice's entry.** -/
theorem advJ_all : ∀ j, 1 ≤ j → j < {n} → Bridge.AdvJ j := fun j h1 h2 ↦
  {atop}

end

end LeanVM.Guest.Bridge.PairChk
''')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.PairChk.All',
                    what="Every compiled function's computed hints pass the data check.")
        + ''.join(f'public import LeanVM.Guest.Bridge.PairChk.{m}\n' for m in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.PairChk

open LeanVM.Guest

public section

{thms}/-- **Every compiled function's computed hints pass the data check.** -/
theorem pairJ_all : ∀ j, 1 ≤ j → j < {n} → Bridge.PairJ j := fun j h1 h2 ↦
  {top}

end

end LeanVM.Guest.Bridge.PairChk
''')
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: the computed hints of {len(lk)} functions over {len(groups)} link modules')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
