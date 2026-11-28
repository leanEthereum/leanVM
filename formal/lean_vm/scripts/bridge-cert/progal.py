"""The deployed guest's alignment by index (`LeanVM/Guest/Bridge/ProgAlData.lean`, `ProgAl/*.lean`).

Reads each function's alignment context off the checks `align.py` writes (`Bridge/Align/*.lean`,
`Bridge/AlignCtx/*/Ctx.lean`): its hint-only cells and its callees with their entries. Writes them as
tables by compiled index (`Bridge.alignExtras`, `Bridge.alignCallees`, the callees by index), and per link
module of `Guest/Checked` (whose `code`, `core`, `cert` and `plumbEq` equations it reuses) each function's
check over `Bridge.ctxOf` (`Bridge.fnAlOk_of`), and the assembly over every function (`ProgAl/All.lean`).
Run after `align.py`; `--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/progal.py [--check]
"""
import os, sys, glob, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'ProgAl')
HEAD = genfiles.header('bridge-cert/progal.py')
CTX = re.compile(r'Bridge\.AlignCtx\.ofData Fn\.«([^»]+)»\.cert\.locs (\[[^\]]*\]) Fn\.«[^»]+»\.code\.entryPc (true|false)\n'
                 r'    Fn\.«[^»]+»\.plumb Data\.powTree Data\.jtTrie (\[[^\]]*\]) CoreMode\.haltPc ')
# the same in `Bridge/Align/*.lean`'s one-line form (`align.ctx_line`)
CTX1 = re.compile(r'def Fn\.«([^»]+)»\.alignCtx : Bridge\.AlignCtx := Bridge\.AlignCtx\.ofData cert\.locs (\[[^\]]*\]) '
                  r'code\.entryPc (true|false) plumb Data\.powTree Data\.jtTrie (\[[^\]]*\]) CoreMode\.haltPc ')


def contexts():
    """Each function's hint-only cells, callees by name and the module proving its check."""
    out = {}
    for p in sorted(glob.glob(os.path.join(BR, 'Align', '*.lean'))):
        mod = f'LeanVM.Guest.Bridge.Align.«{os.path.basename(p)[:-5]}»'
        for m in CTX1.finditer(open(p, encoding='utf-8').read()):
            out[m.group(1)] = (m.group(2), m.group(4), mod)
    for p in sorted(glob.glob(os.path.join(BR, 'AlignCtx', '*', 'Ctx.lean'))):
        k = os.path.basename(os.path.dirname(p))
        for m in CTX.finditer(open(p, encoding='utf-8').read()):
            out[m.group(1)] = (m.group(2), m.group(4), f'LeanVM.Guest.Bridge.AlignCtx.«{k}».Ok')
    return out


def links():
    """Each compiled index's function, link module and whether the module equates its plumbing."""
    out = {}
    for p in sorted(glob.glob(os.path.join(data.ROOT, 'Checked', 'Link*.lean'))):
        t = open(p, encoding='utf-8').read()
        mod = os.path.basename(p)[:-5]
        plumbs = set(int(x) for x in re.findall(r'^kernel_rfl plumbEq(\d+) ', t, re.M))
        for m in re.finditer(r'^kernel_rfl code(\d+) : fnOf \d+ = Fn\.«([^»]+)»\.code$', t, re.M):
            j = int(m.group(1))
            out[j] = (m.group(2), mod, j in plumbs)
    return out


PACK = {}


def names():
    """Each function's compiled name, by stable name (and its pack, `PACK`)."""
    out = {}
    for key, (pack, blk) in data.bundle_blocks().items():
        out[key] = data.code_of(blk)[0]
        PACK[key] = pack
    return out


def trie(m):
    """A `Trie` literal holding `m` (key to term): key `0` at the root, `2k+1` and `2k+2` at key `k` of its
    left and right children."""
    if not m:
        return '.nil'
    v = f'(some {m[0]})' if 0 in m else 'none'
    l = {(k - 1) // 2: x for k, x in m.items() if k and (k - 1) % 2 == 0}
    r = {(k - 1) // 2: x for k, x in m.items() if k and (k - 1) % 2 == 1}
    return f'(.node {v} {trie(l)} {trie(r)})'


def bisect(bs, leaf):
    """`P j` for `bs[0] ≤ j < bs[-1]`, by halves over the bounds `bs`, from `h1 : bs[0] ≤ j` and `h2 : j < bs[-1]`;
    `leaf(a, la, lb)` proves it from `la : bs[a] ≤ j` and `lb : j < bs[a + 1]`."""
    def go(a, b, la, lb):
        if b - a == 1:
            return leaf(a, la, lb)
        m = (a + b + 1) // 2
        v = bs[m]
        return (f'(if hb{v} : j < {v} then {go(a, m, la, f"hb{v}")} else '
                f'{go(m, b, f"(Nat.le_of_not_lt hb{v})", lb)})')
    return go(0, len(bs) - 1, 'h1', 'h2')


def run(check):
    ctxs, lk, nm = contexts(), links(), names()
    n = max(lk) + 1
    idx = {nm[k]: j for j, (k, _, _) in lk.items()}
    extras, callees = ['[]'] * n, [[] for _ in range(n)]
    for j, (k, _, _) in lk.items():
        cells, ents, _ = ctxs[k]
        extras[j] = cells
        callees[j] = [idx[c] for c in re.findall(r'\("([^"]*)", (?:\d+|Fn\.«[^»]+»\.entry)\)', ents)]
    files = {}
    files[os.path.join(BR, 'ProgAlData.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.ProgAlData',
                    what="Each compiled function's hint-only cells, callees and advice, as its alignment check reads them.")
        + '''public import Statement.Data.AdviceHints
public import LeanVM.Guest.ExecCore

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Exec (Trie)

@[expose] public section

/-- Each compiled function's hint-only cells, by index. -/
def alignExtras : Trie (List (Nat × Nat)) :=
  ''' + trie({j: extras[j] for j in range(n) if extras[j] != '[]'}) + '''

/-- Each compiled function's callees its alignment check names, by index, in the order of their names (no code: a
dispatch's lists are long). -/
noncomputable def alignCallees : Trie (List Nat) :=
  ''' + trie({j: '[' + ', '.join(map(str, callees[j])) + ']' for j in range(n) if callees[j]}) + '''

/-- Each compiled function's advice, by index. -/
def alignAdvice : Trie (Nat × Nat × List (Nat × List LeanVM.Prover.Exec.Hint)) :=
  ''' + trie({j: f'Data.adviceFn{j}' for j in range(n)}) + '''

end

end LeanVM.Guest.Bridge
''')
    groups = {}
    for j in sorted(lk):
        groups.setdefault(lk[j][1], []).append(j)
    for mod, js in sorted(groups.items()):
        # the tables' entries (`Tab*`, what the core route's data reads) apart from the alignment checks
        tmod = 'Tab' + mod[len('Link'):]
        imps = {f'LeanVM.Guest.Bridge.ProgAl.{tmod}'} | {ctxs[lk[j][0]][2] for j in js}
        # a long function's pass, checked in windows from the core route's pairing states (`core-mode/pair.py`)
        imps |= {f'LeanVM.Guest.CoreMode.AlignOk.«{lk[j][0]}»' for j in js if '.AlignCtx.«' in ctxs[lk[j][0]][2]}
        body, tbody = [], []
        # the glue naming the callees' entries (`Fn.«k».entry`)
        glue = sorted({PACK[c] for j in js for c in re.findall(r'Fn\.«([^»]+)»\.entry', ctxs[lk[j][0]][1])})
        for j in js:
            k, _, hp = lk[j]
            cells, ents, _ = ctxs[k]
            pe = f'Checked.plumbEq{j}'
            if not hp:
                tbody.append(f'kernel_rfl plumbEq{j} : B2C.plumbOf {j} = Fn.«{k}».plumb\n')
                pe = f'plumbEq{j}'
            tbody.append(f'kernel_rfl tab{j} : (Bridge.extraOf {j}, Bridge.entsOf {j}, Bridge.adviceOf {j}) = '
                         f'({cells}, {ents}, Data.adviceFn{j})\n')
            body.append(f'theorem ok{j} : Bridge.FnAlOk {j} := Bridge.fnAlOk_of Checked.code{j} Checked.core{j} '
                        f'Checked.cert{j} {pe} tab{j} rfl Fn.«{k}».alignOk\n')
        files[os.path.join(OUT, f'{tmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.ProgAl.{tmod}',
                        what=f"The alignment tables' entries of the functions of `Checked.{mod}`.")
            + f'public import LeanVM.Guest.Bridge.ProgAlDefs\npublic import LeanVM.Guest.Checked.{mod}\n'
            + 'import all Statement.Data.Bytecode\nimport all Statement.Data.AdviceHints\n'
            + ''.join(f'public import LeanVM.Guest.CoreMode.GlueE.«{q}»\n' for q in glue)
            + '''meta import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Bridge.ProgAl

open LeanVM.Guest

public section

''' + ''.join(tbody) + '''
end

end LeanVM.Guest.Bridge.ProgAl
''')
        files[os.path.join(OUT, f'{mod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.ProgAl.{mod}',
                        what=f"The functions of `Checked.{mod}` pass their alignment checks over `Bridge.ctxOf`.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''

namespace LeanVM.Guest.Bridge.ProgAl

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.ProgAl
''')
    step = 256
    parts = [(lo, min(lo + step, n)) for lo in range(1, n, step)]
    thms = ''.join(f'''theorem fnAlOk_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.FnAlOk j := fun j h1 h2 ↦
  {bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := fun j ↦ Bridge.FnAlOk j) {la} {lb} ok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(fnAlOk_{a} j {la} {lb})')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.ProgAl.All', what='Every compiled function passes its alignment check.')
        + ''.join(f'public import LeanVM.Guest.Bridge.ProgAl.{mod}\n' for mod in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.ProgAl

open LeanVM.Guest

public section

{thms}/-- **Every compiled function passes its alignment check.** -/
theorem fnAlOk_all : ∀ j, 1 ≤ j → j < {n} → Bridge.FnAlOk j := fun j h1 h2 ↦
  {top}

end

end LeanVM.Guest.Bridge.ProgAl
''')
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: the alignment of {len(lk)} functions over {len(groups)} link modules')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
