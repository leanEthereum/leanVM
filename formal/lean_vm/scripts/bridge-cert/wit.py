"""The witness hints' data check of every compiled function (`LeanVM/Guest/Bridge/WitChk/*.lean`).

Per module of alignment checks `align.py` writes, each function's `Bridge.witChk` over its alignment context
(`alignCtx`; one whose cells its windows pack ahead, with those, `alignCtxP`), by `decide +kernel`; per link module
of `Guest/Checked`, each function's `Bridge.WitJ` (`Bridge.witJ_of`, reusing the `Checked` and `ProgAl` link
equations); and the assembly over every function
(`WitChk/All.lean`). Run after `progal.py`; `--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/wit.py [--check]
"""
import os, re, sys, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import progal
import pair

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'WitChk')
HEAD = genfiles.header('bridge-cert/wit.py')


def check_module(ctx_mod):
    """The module of checks for the functions whose context `ctx_mod` holds."""
    return pair.check_module(ctx_mod).replace('.PairChk.', '.WitChk.')


def run(check):
    ctxs, lk = progal.contexts(), progal.links()
    n = max(lk) + 1
    files = {}
    by_mod = {}
    for j, (k, _, _) in sorted(lk.items()):
        by_mod.setdefault(ctxs[k][2], []).append(k)
    for cm, ks in sorted(by_mod.items()):
        mod = check_module(cm)
        okp = os.path.join(data.LEAN_VM, *[x.strip('«»') for x in cm.split('.')]) + '.lean'
        win = cm.endswith('».Ok') and 'theorem alignCtxEq' in open(okp, encoding='utf-8').read()
        prf = 'rw [alignCtxEq]\n  decide +kernel' if win else 'decide +kernel'
        body = data.fn_thms((k, 'witOk', 'Bridge.witChk alignCtx fs core.body = true', prf) for k in ks)
        files[os.path.join(OUT, mod.split('WitChk.')[1].strip('«»') + '.lean')] = (
            HEAD(mod=mod, what="The kernel's checks that compiled functions' witness hints pass the data check.")
            + 'public import LeanVM.Guest.Bridge.WitDefs\n' + f'public import {cm}\n'
            + ''.join(f'public import {m}\n' for m in pair.pack_imports(cm))
            + '\n' + body.rstrip('\n') + '\n')
    groups = {}
    for j in sorted(lk):
        groups.setdefault(lk[j][1], []).append(j)
    fss = set()
    for p in glob.glob(os.path.join(data.ROOT, 'Checked', 'Link*.lean')):
        fss |= set(int(x) for x in re.findall(r'^kernel_rfl fsEq(\d+) ', open(p, encoding='utf-8').read(), re.M))
    for lmod, js in sorted(groups.items()):
        imps = {'LeanVM.Guest.Bridge.WitDefs', f'LeanVM.Guest.Checked.{lmod}', f'LeanVM.Guest.Bridge.ProgAl.Tab{lmod[len("Link"):]}'}  # the tables' entries, not the alignment checks
        imps |= {check_module(ctxs[lk[j][0]][2]) for j in js}
        body = []
        for j in js:
            k, _, hp = lk[j]
            pe = f'Checked.plumbEq{j}' if hp else f'Bridge.ProgAl.plumbEq{j}'
            fe = f'Checked.fsEq{j}'
            if j not in fss:
                body.append(f'kernel_rfl fsEq{j} : B2C.fsN {j} = Fn.«{k}».fs\n')
                fe = f'fsEq{j}'
            body.append(f'theorem wok{j} : Bridge.WitJ {j} := Bridge.witJ_of Checked.code{j} Checked.core{j} '
                        f'Checked.cert{j} {pe} Bridge.ProgAl.tab{j} rfl {fe} Fn.«{k}».witOk\n')
        files[os.path.join(OUT, f'{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.WitChk.{lmod}',
                        what=f"The functions of `Checked.{lmod}` pass the witness hints' data check over their alignment's context.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''meta import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Bridge.WitChk

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.WitChk
''')
    step = 256
    parts = [(lo, min(lo + step, n)) for lo in range(1, n, step)]
    thms = ''.join(f'''theorem witJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.WitJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := fun j ↦ Bridge.WitJ j) {la} {lb} wok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(witJ_{a} j {la} {lb})')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.WitChk.All',
                    what="Every compiled function's witness hints pass the data check.")
        + ''.join(f'public import LeanVM.Guest.Bridge.WitChk.{m}\n' for m in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.WitChk

open LeanVM.Guest

public section

{thms}/-- **Every compiled function's witness hints pass the data check.** -/
theorem witJ_all : ∀ j, 1 ≤ j → j < {n} → Bridge.WitJ j := fun j h1 h2 ↦
  {top}

end

end LeanVM.Guest.Bridge.WitChk
''')
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: the witness hints of {len(lk)} functions over {len(groups)} link modules')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
