"""verify_sub's words at a child's shape: the static count (`words2`) with each runtime count read off the shape.
Shape: c stream chunks, w pointer width, n tallest table log, p link permutations, tau Keccak table log,
m stack log, r rate (log inverse rate, 1..4), slow (levels taking the zero-challenge sum: 'none', 'all', or a set),
L the memory log, heights (per table log height, or None for the costliest arm)."""
import re, words2 as w
P = {}
for l in open('placeholders.txt'):
    k, _, v = l.partition(' = ')
    v = v.strip()
    try: P[k.replace('_PLACEHOLDER', '')] = eval(v)
    except Exception: pass
P['KECCAK_PACK_LOG'] = 4
NR, NS, MAXL = P['LIG_N_RATES'], P['LIG_N_LOG_SIZES'], P['LIG_MAX_LEVELS']
STRIDE = NS * MAXL
def lig(name, m_idx, lvl, r=None):
    t = P['LIG_' + name]; ml = m_idx * MAXL + lvl
    return t[ml + (r - 1) * STRIDE] if r is not None else t[ml]
def fam(f): return re.sub(r'__L.*', '', f)
def sites(f, family, kinds=('arm', 'frame')):
    out = []
    for i, hs in w.fns[f]['hints']:
        for h in hs:
            if h[0] in kinds:
                callee = h[3][0] if h[0] == 'arm' else h[2]
                if fam(callee) == family: out.append(i)
    return sorted(set(out))
def make(S):
    m_idx = S['m'] - P['LIG_MIN_LOG_SIZE']; r = S['r']
    def os_level(stack, family):
        for f, i in reversed(stack):
            if f.startswith('open_stacked__'): return sites(f, family).index(i)
    def lr_count(stack):
        f, i = stack[-1]
        if fam(f) == 'verify_sub': return S['w']
        return [S['n'], P['LINK_Q_VARS']][sites(f, 'link_rounds').index(i)]
    def skip(f, h, stack):
        if fam(f) != 'level_residual_slow' or h[0] != 'frame' or fam(h[2]) != 'level_residual_sum': return False
        slow = S.get('slow', 'none')
        if slow == 'all': return False
        if slow == 'none': return True
        for g, i in reversed(stack):
            if g.startswith('open_stacked__'): return sites(g, 'level_residual_slow').index(i) not in slow
    S['_skip'] = skip
    def rt(f, kind, off, stack):
        fa = fam(f); caller = stack[-1][0] if stack else None
        if fa == 'hint_stream': return S['c']
        if fa == 'verify_sub' and kind == 'dyn': return P['STREAM_CHUNK'] * S['c']
        if fa == 'squeeze_packed': return (S['p'] // 4 + 2) * 5 if kind == 'dyn' else S['p'] // 4
        if fa == 'link_rounds':
            cnt = lr_count(stack)
            return (cnt // 4 + 2) * 7 if kind == 'dyn' else cnt // 4
        if fa == 'ring_rows': return S['n'] // 8
        if fa == 'rs_eq_run':
            q = (S['tau'] + P['QKECCAK_SLOT_LOG']) // 8
            return (q + 2) * 64 if kind == 'dyn' else q
        if fa == 'check_stack_terminal': return (S['n'] + 1) * 64
        if fa == 'verify_keccak':
            pack = S['tau'] - P['KECCAK_PACK_LOG']
            return pack + P['KECCAK_SEG_LOG'] if kind == 'dyn' else pack
        if fa == 'keccak_layer': return S['tau'] - P['KECCAK_PACK_LOG'] + P['KECCAK_SEG_LOG']
        if fa == 'open_stacked': return P['LIG_POS_TOTAL'][m_idx + (r - 1) * NS]
        if fa == 'level_positions':
            s = lig('SQUEEZES', m_idx, os_level(stack, 'level_positions'), r)
            return (s + 1) * 5 if kind == 'dyn' else s
        if fa == 'level_residual':
            q = lig('QUERIES', m_idx, os_level(stack, 'level_residual'), r)
            b, rr = q // 8, q % 8
            if kind == 'dyn': return 2 * (b + rr + 1)
            return b if off == 6 else rr
        return None
    def pick(f, i, callees, stack, selv):
        if selv is not None: return [selv] if selv < len(callees) else None
        cf = fam(callees[0]); ff = fam(f)
        if ff == 'open_stacked' and len(callees) == NR:
            return [r - 1]
        if cf == 'open_stacked' or cf == 'squeeze_point_from' and ff == 'verify_sub' or cf == 'stack_selectors': return [m_idx]
        if cf in ('state_ends', 'index_side', 'link_terminal', 'chunk_d'): return [S['w'] - P['BYTECODE_LOG']]
        if cf == 'link_row_side': return [P['CHUNK_D'][S['w']] - P['LINK_D_MIN']]
        if cf == 'one_plus_suffixes': return [S['n']]
        if cf in ('table_size', 'table_point') and S.get('heights'):
            t = sites(f, cf).index(i); return [S['heights'][t]]
        if cf == 'squeeze_packed_last': return [S['p'] % 4]
        if cf == 'link_rounds_last':
            return [lr_count(stack) % 4]
        if cf == 'rs_eq_rows' and ff == 'rs_eq_run': return [(S['tau'] + P['QKECCAK_SLOT_LOG']) % 8]
        if cf == 'rs_eq_rows_all': return [S['n'] % 8]
        return None
    return rt, pick
def vs(S, log=None):
    rt, pick = make(S)
    w.UNRES.clear()
    return w.M('verify_sub', {}, rt, pick, (), log, S['_skip'])

def vs_rows(S):
    rt, pick = make(S)
    w.UNRES.clear()
    return w.C('verify_sub', {}, rt, pick, (), S['_skip'])
def vs_cyc(S):
    import cyc
    rt, pick = make(S)
    w.UNRES.clear()
    return cyc.C('verify_sub', {}, rt, pick, (), S['_skip'])
