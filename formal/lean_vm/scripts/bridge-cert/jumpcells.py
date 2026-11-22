"""The jump cells' data checks (`LeanVM/Guest/Bridge/JumpCells/*.lean`).

Per pack, each function's `Bridge.jcDataD` on its own data, decided by the kernel (`P*.lean`, a long
function in a module of its own, `H*.lean`); per link module of `Guest/Checked` (whose `code`, `core`,
`cert`, `plumbEq` and `fsEq` equations it reuses, and `ProgAl`'s table of hint-only cells), each
function's `Bridge.jcData` (`Link*.lean`); the assembly over every function (`All.lean`). Run after
`progal.py`; `--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/jumpcells.py [--check]
"""
import os, sys, glob, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import progal

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'JumpCells')
HEAD = genfiles.header('bridge-cert/jumpcells.py')
LONG = 20000


def packs():
    """Each function's bundle pack, core pack and code length, by stable name."""
    out = {}
    core = {k: pack for k, bs in data.core_blocks().items() for pack, mod, _ in bs if mod == 'Core'}
    for key, (pk, blk) in data.bundle_blocks().items():
        out[key] = (pk, core.get(key, pk), data.code_of(blk)[2])
    return out


def fs_eqs():
    """The compiled indices whose `fsEq` a `Checked` link module states."""
    out = set()
    for p in sorted(glob.glob(os.path.join(data.ROOT, 'Checked', 'Link*.lean'))):
        out |= set(int(x) for x in re.findall(r'^kernel_rfl fsEq(\d+) ', open(p, encoding='utf-8').read(), re.M))
    return out


def run(check):
    ctxs, lk, pk, fe = progal.contexts(), progal.links(), packs(), fs_eqs()
    n = max(lk) + 1
    files = {}
    groups = {}
    for j, (k, _, _) in sorted(lk.items()):
        b, c, size = pk[k]
        mod = f'H_{k}' if size > LONG else f'P_{b}'
        groups.setdefault(mod, []).append((j, k, b, c))
    for mod, fns in sorted(groups.items()):
        imps = {'LeanVM.Guest.Bridge.JumpCellsDefs', 'LeanVM.Guest.Data.Pows', 'LeanVM.Guest.CheckView'}
        thms = []
        for j, k, b, c in fns:
            imps |= {f'LeanVM.Guest.Pack.«{b}».Bundle', f'LeanVM.Guest.Pack.«{c}».Core', f'LeanVM.Guest.CoreMode.GlueA.«{c}»'}
            # `main` by its index as the glue names it, not as a number
            thms.append((k, 'jcOk', f'Bridge.jcDataD plumb fs (cert.withPows Data.powTree) {ctxs[k][0]} core code.code '
                         f'(Fn.«{k}».idx == 1) = true', 'decide +kernel'))
        files[os.path.join(OUT, f'{mod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.JumpCells.{mod}', what="Functions' data pass the jump cells' check.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '\n' + data.fn_thms(thms))
    links = {}
    for j in sorted(lk):
        links.setdefault(lk[j][1], []).append(j)
    for lmod, js in sorted(links.items()):
        # the alignment tables' entries (`ProgAl/Tab*`), not the alignment checks (`ProgAl/Link*`, the windows)
        imps = {'LeanVM.Guest.Bridge.JumpCellsIdx', f'LeanVM.Guest.Checked.{lmod}',
                f'LeanVM.Guest.Bridge.ProgAl.Tab{lmod[len("Link"):]}'}
        body = []
        for j in js:
            k, _, hp = lk[j]
            b, c, size = pk[k]
            imps.add(f'LeanVM.Guest.Bridge.JumpCells.{"H_" + k if size > LONG else "P_" + b}')
            pe, fq = f'Checked.plumbEq{j}', f'Checked.fsEq{j}'
            if not hp:
                body.append(f'kernel_rfl plumbEq{j} : B2C.plumbOf {j} = Fn.«{k}».plumb\n')
                pe = f'plumbEq{j}'
            if j not in fe:
                body.append(f'kernel_rfl fsEq{j} : B2C.fsN {j} = Fn.«{k}».fs\n')
                fq = f'fsEq{j}'
            body.append(f'theorem jc{j} : Bridge.jcData {j} = true := by have hx : Bridge.extraOf {j} = {ctxs[k][0]} := '
                        f'congrArg Prod.fst ProgAl.tab{j}; rw [Bridge.jcData, Checked.code{j}, Checked.core{j}, '
                        f'Checked.cert{j}, {pe}, {fq}, hx]; exact Fn.«{k}».jcOk\n')
        files[os.path.join(OUT, f'{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.JumpCells.{lmod}',
                        what=f"The functions of `Checked.{lmod}` pass the jump cells' check by index.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''meta import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Bridge.JumpCells

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.JumpCells
''')
    step = 256
    parts = [(lo, min(lo + step, n)) for lo in range(1, n, step)]
    thms = ''.join(f'''theorem jcData_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.jcData j = true := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := fun j ↦ Bridge.jcData j = true) {la} {lb} jc{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(jcData_{a} j {la} {lb})')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.JumpCells.All', what="Every compiled function passes the jump cells' check.")
        + ''.join(f'public import LeanVM.Guest.Bridge.JumpCells.{m}\n' for m in sorted(links)) + f'''
namespace LeanVM.Guest.Bridge.JumpCells

open LeanVM.Guest

public section

{thms}/-- **Every compiled function passes the jump cells' check.** -/
theorem jcData_all : ∀ j, 1 ≤ j → j < {n} → Bridge.jcData j = true := fun j h1 h2 ↦
  {top}

end

end LeanVM.Guest.Bridge.JumpCells
''')
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: the jump cells of {len(lk)} functions over {len(groups)} data modules')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
