import os, sys
# usage: python3 -I gentotal.py  writes Tables/Vt/{PushPad,PushFw,PullTotal,CountTotal}.lean: the three
# sides' totals (`bus_table_total`, G:2496-2555) from verify_tables' second loop over the sides.
# First run: python3 -I dump.py ../../LeanVM/Guest/Data/Core00.lean vt_ir.txt (from this directory).
import re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import IR, parse_atom, VT_LEAN

LO, HI = 2021, 2590          # the totals' loop
PW = [583 + 13 * t for t in range(6)]   # pad_weight[t] (`vtPadV`)
W_BASE = 13                  # fp_w
LEAF_BETA1 = 1975            # beta + 1

def defs(lo, hi):
    d = {}
    for p in range(lo, hi + 1):
        a = parse_atom(IR[p])
        if a is None: continue
        op, args = a
        if op in ('add', 'mul', 'copy'): d.setdefault(args[0], (p, op, args[1:]))
        elif op == 'const': d.setdefault(args[0], (p, 'const', args[1]))
        elif op == 'load': d.setdefault(args[0], (p, 'load', args[1:]))
    return d

D = defs(LO, HI)

def cone(v, leaves, acc, d=None):
    d = D if d is None else d
    if v in leaves or v not in d: return acc
    p, op, args = d[v]
    if p in acc: return acc
    acc.add(p)
    if op in ('add', 'mul', 'copy'):
        for a in args: cone(a, leaves, acc, d)
    return acc

def atom_text(p):
    s = IR[p]
    assert s.startswith('.atom '), s
    return s[len('.atom '):]

def wrap(items, first, indent, width=98):
    out, cur = [], first
    for it in items:
        add = it if cur.endswith('[') or cur.endswith(' ') else ' ' + it
        if len(cur) + len(add) > width:
            out.append(cur); cur = indent + it
        else:
            cur += add
    out.append(cur)
    return '\n'.join(out)

def haves(ps):
    """`have` lines for the atoms at positions ps, and the names of their equations."""
    L, eqs, holds = [], [], []
    for p in sorted(ps):
        L.append(f'  have a{p} := h.atomAt {p} {atom_text(p)} (by decide +kernel)')
        op, args = parse_atom(IR[p])
        if op == 'load':
            assert args[1] == W_BASE, (p, args)
            L.append(f'  have e{p} := tb_loadHolds_unique a{p} (hw {args[2]} (by norm_num))')
            eqs.append(f'e{p}')
        else:
            holds.append(f'a{p}'); eqs.append(f'a{p}')
    for i in range(0, len(holds), 10):
        L.append('  simp only [Atom.Holds] at ' + ' '.join(holds[i:i + 10]))
    return L, eqs

def flat(v, op, stop=frozenset({LEAF_BETA1})):
    """the operands of a chain of `op` from v (inside the region), not past `stop`."""
    if v not in stop and v in D and D[v][1] == op:
        _, _, (a, b) = D[v]
        return flat(a, op, stop) + flat(b, op, stop)
    return [v]

def inner_terms(v):
    """`β1 + Σ w_i·pad_i` (or `1 + …` on the count side, which adds nothing): the padding terms."""
    terms = flat(v, 'add')
    pads = []
    for x in terms:
        if x == LEAF_BETA1: continue
        p, op, args = D[x]
        if op == 'load':
            pads.append((args[1], 1))
        else:
            assert op == 'mul', (x, op)
            a, b = args
            pa, oa, aa = D[a]; pb, ob, ab = D[b]
            assert oa == 'load' and ob == 'const' and ab[1] == 0, (x, IR[pa], IR[pb])
            pads.append((aa[1], ab[0]))
    return pads

def pad_data(total, first_block, count_side):
    """the side's padding sum `Σ_t pw_t·Σ_b eq_b·(…)`: per block (block, table, copy, pads), the
    tables' subtotal cells."""
    data, subs = [], {}
    b = first_block
    for x in flat(total, 'add'):
        _, op, (pw, tsum) = D[x]
        assert op == 'mul' and pw in PW, (x, op)
        t = PW.index(pw)
        subs[t] = tsum
        for y in flat(tsum, 'add'):
            if count_side:
                data.append((b, t, y, [])); b += 1
                continue
            _, op2, (cp, inner) = D[y]
            assert op2 == 'mul'
            data.append((b, t, cp, inner_terms(inner))); b += 1
    return data, subs

def data_lit(data):
    items = [f'({b}, {t}, {c}, [{", ".join(f"({i}, {v})" for i, v in pads)}])' for b, t, c, pads in data]
    items = [x + ',' for x in items[:-1]] + [items[-1] + ']']
    return wrap(items, '  [', '    ')

HDR = '''/-
  LeanVM.Guest.B1.Tables.Vt.%(mod)s

  %(doc)s
-/

module

public import %(imp)s

/-!
%(body_doc)s
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

'''
FTR = '''
end
end LeanVM.Guest.B1.Tables
'''

def write(mod, doc, imp, body_doc, body):
    open(os.path.join(VT_LEAN, f'{mod}.lean'), 'w').write(
        HDR % dict(mod=mod, doc=doc, imp=imp, body_doc=body_doc) + body + FTR)

HYP = '{rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}\n    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))'

def subtotal_lemmas(name, data, subs, beta1, leaves, Wname='W', hyp=HYP):
    """per table: the subtotal cell is `vtPadTable`'s value."""
    out = []
    for t in range(6):
        ps = cone(subs[t], leaves, set())
        L, eqs = haves(ps)
        body = '\n'.join(L)
        s = f'''set_option maxRecDepth 100000 in
theorem {name}{t} {hyp} :
    σ (.n {subs[t]}) = vtPadTable (fun c ↦ σ (.n c)) {Wname} {beta1} {DATA_NAME[name]} {t} := by
{body}
  simp (config := {{ decide := true }}) only [vtPadTable, {DATA_NAME[name]}, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    {'' if beta1 == '1' else 'tb_word_one, '}mul_one, add_zero]
''' + wrap([e + ',' for e in eqs[:-1]] + [eqs[-1] + ']'], '  simp only [', '    ') + ('\n' if beta1 == '1' and sum(1 for x in data if x[1] == t) <= 2 else '\n  ring\n')
        out.append(s)
    return out

DATA_NAME = {'vt_pushPadT': 'vtPushPadData', 'vt_countPadT': 'vtCountPadData'}

def total_lemma(name, statement, target, leaves, extra_rw='', extra=(), d=None, close='  ring\n',
                hyp=HYP):
    ps = cone(target, leaves, set(), d) | set(extra)
    L, eqs = haves(ps)
    return (f'set_option maxRecDepth 100000 in\n/-- **{statement[0]}** -/\ntheorem {name} {hyp} :\n'
            f'    {statement[1]} := by\n' + '\n'.join(L) + '\n' +
            wrap([e + ',' for e in eqs[:-1]] + [eqs[-1] + ']'], '  simp only [', '    ') + '\n' +
            extra_rw + close)

# ---- the push side ----
push_total, pull_total, count_total = 2442, 2488, 2543
def the_add(v):
    _, op, (a, b) = D[v]; assert op == 'add'; return a, b
# bus_table_total[PUSH] = ((acc + padding) + (1 + selector_sum)) + leaf
x, leaf0 = the_add(push_total)
x, one_sel0 = the_add(x)
fw0, pad0 = the_add(x)
_, sel0 = the_add(one_sel0)
push_data, push_subs = pad_data(pad0, 3, False)
x, leaf1 = the_add(pull_total)
x, one_sel1 = the_add(x)
fw1, pad1 = the_add(x)
assert pad1 == pad0
_, sel1 = the_add(one_sel1)
x, leaf2 = the_add(count_total)
pad2, one_sel2 = the_add(x)
_, sel2 = the_add(one_sel2)
count_data, count_subs = pad_data(pad2, 108, True)

def def_pos(v, op=None):
    """the position of the statement writing v (first), anywhere in the body."""
    for p in sorted(IR):
        a = parse_atom(IR[p])
        if a and a[0] in ('add', 'mul', 'copy', 'const') and a[1][0] == v and (op is None or a[0] == op):
            return p
    raise KeyError(v)

SEL0_POS = def_pos(sel0, 'copy'); SEL0_SRC = parse_atom(IR[SEL0_POS])[1][1]
SEL1_POS = def_pos(sel1, 'copy'); SEL1_SRC = parse_atom(IR[SEL1_POS])[1][1]
SEL2_POS = def_pos(sel2, 'copy'); SEL2_SRC = parse_atom(IR[SEL2_POS])[1][1]

if __name__ == '__main__':
    print('push', fw0, pad0, sel0, leaf0, len(push_data))
    print('pull', fw1, sel1, leaf1)
    print('count', pad2, sel2, leaf2, len(count_data))
    leavesP = {LEAF_BETA1} | {c for _, _, c, _ in push_data} | set(PW)
    body = ['''/-- A table's part of a side's padding sum: its blocks' eq weights (by their copies' values)
times `β + 1 + Σ w_i·pad_i` (`β1` the side's `β + 1`). -/
def vtPadTable (eqc W : ℕ → E) (β1 : E) (data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) (t : ℕ) : E :=
  ((data.filter fun x ↦ x.2.1 = t).map fun x ↦
    eqc x.2.2.1 * (β1 + (x.2.2.2.map fun ic ↦ W ic.1 * word ic.2 0).sum)).sum

/-- A side's padding sum: per table, its padding weight times its part. -/
def vtPadSum (eqc pw W : ℕ → E) (β1 : E) (data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) : E :=
  pw 0 * vtPadTable eqc W β1 data 0 + pw 1 * vtPadTable eqc W β1 data 1 +
    pw 2 * vtPadTable eqc W β1 data 2 + pw 3 * vtPadTable eqc W β1 data 3 +
    pw 4 * vtPadTable eqc W β1 data 4 + pw 5 * vtPadTable eqc W β1 data 5

/-- The push side's table blocks: block, table, copy value, padding terms. -/
def vtPushPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
''' + data_lit(push_data) + '\n']
    body += subtotal_lemmas('vt_pushPadT', push_data, push_subs, f'(σ (.n {LEAF_BETA1}))', leavesP)
    subsP = {push_subs[t] for t in range(6)}
    body.append(total_lemma('vt_push_pad', ('The push side\'s padding sum.',
        f'σ (.n {pad0}) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W (σ (.n {LEAF_BETA1}))\n'
        f'      vtPushPadData'), pad0, subsP | set(PW),
        extra_rw='  simp only [vtPadSum, vtPadV]\n' + wrap(
            [f'← vt_pushPadT{t} h hw,' for t in range(5)] + ['← vt_pushPadT5 h hw]'],
            '  rw [', '    ') + '\n', close=''))
    body.append(f'''/-- **The push side's total.** -/
theorem vt_push_total {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) :
    σ (.n {push_total}) = σ (.n {fw0}) + σ (.n {pad0}) + (1 + σ (.n {sel0})) + σ (.n {leaf0}) := by
''' + '\n'.join(f'  have a{p} := h.atomAt {p} {atom_text(p)} (by decide +kernel)'
        for p in sorted(cone(push_total, {fw0, pad0, sel0, leaf0}, set()))) + '\n' +
        '  simp only [Atom.Holds] at ' + ' '.join(f'a{p}' for p in sorted(cone(push_total, {fw0, pad0, sel0, leaf0}, set()))) +
        '\n  rw [' + ', '.join(f'a{p}' for p in sorted(cone(push_total, {fw0, pad0, sel0, leaf0}, set()), reverse=True)) + ', tb_word_one]\n')
    body.append(f'''/-- `push_padding`'s selector sum is the running sum's copy. -/
theorem vt_push_sel {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) : σ (.n {sel0}) = σ (.n {SEL0_SRC}) := by
  have a := h.atomAt {SEL0_POS} {atom_text(SEL0_POS)} (by decide +kernel)
  simpa only [Atom.Holds] using a
''')
    write('PushPad', "`verify_tables`' push side's padding sum and total: the tables' blocks' padding terms, the\n  selector sum and the GKR leaf value.",
          'LeanVM.Guest.B1.Tables.Vt.SelFw',
          "# The push side's padding and total (G:2496-2555)\n\n`vtPushPadData` lists the push side's table blocks with their table, the value of their eq weight's\ncopy (`block_eq_hi[b]`) and their nonzero `COORD_PADDING` terms (slot, value). `vt_push_pad`: the\npadding sum is `Σ_t pad_weight[t]·Σ_b eq_b·(β + 1 + Σ w_i·pad_i)`; `vt_push_total`:\n`bus_table_total[PUSH]` is the framework accumulator, the padding sum, `1 + selector_sum` and the\nGKR push leaf value.",
          '\n'.join(body))

FW_NOTE = "The framework blocks' coordinate values are the first loop's (`coord_vals`): constants, the index\nextensions and the stream words."

def gen_rest():
    # ---- PushFw: the push side's framework accumulator ----
    fwP_leaves = {14, 790, 807, 835, 810, 815, 819, 838, 1293, 1843}
    consts = [def_pos(v, 'const') for v in (791, 792, 793, 808, 811, 836, 839)]
    fwP = total_lemma('vt_push_fw', ("The push side's framework accumulator.",
        f'σ (.n {fw0}) = σ (.n 790) * (σ (.n 14) + (W 0 + W 1 + W 2)) +\n'
        '      σ (.n 807) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 810) + W 2 + W 3 * σ (.n 815) +\n'
        '        W 4 * σ (.n 819))) +\n'
        '      σ (.n 835) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 838) + W 2)) +\n'
        '      σ (.n 1293) * σ (.n 1843)'), fw0, fwP_leaves, extra=consts,
        extra_rw='  simp only [tb_word_one, tb_word_gen, vt_word4]\n')
    write('PushFw', "`verify_tables`' push side's framework blocks: their fingerprints' accumulator and the\n  bytecode share's public term.",
          'LeanVM.Guest.B1.Tables.Vt.PushPad',
          "# The push side's framework blocks (G:2501-2514)\n\n`vt_push_fw`: the accumulator after the state, memory and bytecode blocks is\n`Σ_f eq_f·(β + Σ_i w_i·coord_i)`, the bytecode block's public slots left out, plus\n`public_eq·S`. " + FW_NOTE,
          'theorem vt_word4 : word 4 0 = gen ^ 2 := by\n  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]\n\n' + fwP)
    # ---- PullTotal ----
    fwQ_leaves = {14, 1294, 1299, 1313, 1301, 1305, 1307, 1309, 1315, 1319, 1436, 1843}
    constsQ = [def_pos(v, 'const') for v in (1295, 1296, 1297, 1300, 1314)]
    fwQ = total_lemma('vt_pull_fw', ("The pull side's framework accumulator.",
        f'σ (.n {fw1}) = σ (.n 1294) * (σ (.n 14) + (W 0 + W 1 * vtWFinalPc + W 2)) +\n'
        '      σ (.n 1299) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 1301) + W 2 * σ (.n 1305) +\n'
        '        W 3 * σ (.n 1307) + W 4 * σ (.n 1309))) +\n'
        '      σ (.n 1313) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 1315) + W 2 * σ (.n 1319))) +\n'
        '      σ (.n 1436) * σ (.n 1843)'), fw1, fwQ_leaves, extra=constsQ,
        extra_rw='  simp only [tb_word_one, tb_word_gen, vt_word4]\n')
    # the pull side's running selector sum, over the push side's copies
    D2 = defs(def_pos(sel1, 'copy') - 160, def_pos(sel1, 'copy'))
    copies = [790, 807, 835] + [c for _, _, c, _ in push_data]
    sumQ = total_lemma('vt_pull_sel', ("The pull side's selector sum: the push blocks' copies.",
        f'σ (.n {sel1}) = σ (.n 790) + σ (.n 807) + σ (.n 835) +\n'
        '      (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum'), sel1, set(copies), d=D2,
        extra_rw='  simp only [vtPushPadData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]\n',
        hyp='{rd : Reader} {σ : Val} (h : VtH rd σ)')
    tot = cone(pull_total, {fw1, pad0, sel1, leaf1}, set())
    totQ = (f'''/-- **The pull side's total.** -/
theorem vt_pull_total {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) :
    σ (.n {pull_total}) = σ (.n {fw1}) + σ (.n {pad0}) + (1 + σ (.n {sel1})) + σ (.n {leaf1}) := by
''' + '\n'.join(f'  have a{p} := h.atomAt {p} {atom_text(p)} (by decide +kernel)' for p in sorted(tot)) +
        '\n  simp only [Atom.Holds] at ' + ' '.join(f'a{p}' for p in sorted(tot)) +
        '\n  rw [' + ', '.join(f'a{p}' for p in sorted(tot, reverse=True)) + ', tb_word_one]\n')
    write('PullTotal', "`verify_tables`' pull side total: its framework blocks' fingerprints (with the final memory and\n  bytecode counts), the push side's padding sum, the selector sum and the GKR pull value.",
          'LeanVM.Guest.B1.Tables.Vt.PushFw',
          "# The pull side's total (G:2496-2555)\n\nThe pull side's blocks mirror the push side's: their eq weights are the push blocks' copies, and\ntheir padding sum is the push side's. `vt_pull_total`: `bus_table_total[PULL]`. " + FW_NOTE,
          '/-- `g^(2^19 - 1)`, the final `pc`, as the data writes it. -/\nabbrev vtWFinalPc : E := word 12261764870545049476 0\n\n' + '\n'.join([fwQ, sumQ, totQ]))
    # ---- CountTotal ----
    leavesC = {c for _, _, c, _ in count_data} | set(PW)
    body = ['/-- The count side\'s blocks: block, table, copy value, no padding terms. -/\ndef vtCountPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=\n' + data_lit(count_data) + '\n']
    HC = '{rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E)'
    body += subtotal_lemmas('vt_countPadT', count_data, count_subs, '1', leavesC, hyp=HC)
    subsC = {count_subs[t] for t in range(6)}
    body.append(total_lemma('vt_count_pad', ("The count side's padding sum.",
        f'σ (.n {pad2}) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W 1 vtCountPadData'),
        pad2, subsC | set(PW),
        extra_rw='  simp only [vtPadSum, vtPadV]\n' + wrap(
            [f'← vt_countPadT{t} h W,' for t in range(5)] + ['← vt_countPadT5 h W]'],
            '  rw [', '    ') + '\n', close='', hyp=HC))
    tot = cone(count_total, {pad2, sel2, leaf2}, set())
    body.append(f'''/-- **The count side's total.** -/
theorem vt_count_total {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) :
    σ (.n {count_total}) = σ (.n {pad2}) + (1 + σ (.n {sel2})) + σ (.n {leaf2}) := by
''' + '\n'.join(f'  have a{p} := h.atomAt {p} {atom_text(p)} (by decide +kernel)' for p in sorted(tot)) +
        '\n  simp only [Atom.Holds] at ' + ' '.join(f'a{p}' for p in sorted(tot)) +
        '\n  rw [' + ', '.join(f'a{p}' for p in sorted(tot, reverse=True)) + ', tb_word_one]\n')
    body.append(f'''/-- The count side's selector sum is the running sum's copy. -/
theorem vt_count_sel {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) : σ (.n {sel2}) = σ (.n {SEL2_SRC}) := by
  have a := h.atomAt {SEL2_POS} {atom_text(SEL2_POS)} (by decide +kernel)
  simpa only [Atom.Holds] using a
''')
    write('CountTotal', "`verify_tables`' count side total: the padding sum over its blocks (counts alone, at `β = 0`),\n  the selector sum and the GKR count value.",
          'LeanVM.Guest.B1.Tables.Vt.PullTotal',
          "# The count side's total (G:2496-2555)\n\n`vtCountPadData` lists the count side's blocks with their table and copy. `vt_count_total`:\n`bus_table_total[COUNT]` is the padding sum, `1 + selector_sum` and the GKR count value.",
          '\n'.join(body))

if __name__ == '__main__':
    gen_rest()
