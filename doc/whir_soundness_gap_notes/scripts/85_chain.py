"""Note 85: the chain of binary full parts Q^(0) = P, Q^(j+1) = Q*(Q^(j)) of a class pattern of the generic tree code
[n, n/2] (T2, one draw of the twiddles in GF(2^64)), with the quantities the list bound of note 85 is written in:
d_j = dim ker Q^(j), B_j = sum of rho_u over the nodes of height j, the check d_j = 2 d_{j+1} - B_j (an instance of (C*)
at every level), delta_u = dim Delta_u, the gains, the fine cost c_j = 2^j d_j - d_0 and the critical scale (the largest
scale N_j = n / 2^j with d_j < N_j * eta, eta = agreement / n - 1/2).
Usage: 85_chain.py file [max]      lines with 'classes per leaf:' (76/83 format) or 'votes:' (83_votes format)
       85_chain.py stair N b f     the one-sided staircase of scale N (top [N, N/2]), blocks of b leaves, f free blocks
Field helpers and the tree code are those of 83_lib.py (83_bin/libgf83.dylib must exist: run 83_run.sh once)."""
import sys, os, random, re, itertools, importlib.util
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lib83", os.path.join(here, "83_lib.py")); L83 = importlib.util.module_from_spec(spec); spec.loader.exec_module(L83)

def class_thetas(C):
    """basis of Lambda(C) as bitmasks over members 1..L (bit l-1), member 0 = the zero row"""
    mem = L83.bits(C); out = []
    for l in mem[1:]:
        th = 1 << (l - 1)
        if mem[0] >= 1: th |= 1 << (mem[0] - 1)
        out.append(th)
    return out
def rows_binary(G, kk, L, spaces):
    """rows theta (x) g_u of a binary pattern; spaces[u] = list of bitmasks over members 1..L"""
    rows = []
    for u, sp in enumerate(spaces):
        for th in sp:
            r = np.zeros(L * kk, dtype=np.uint64)
            for l in range(L):
                if (th >> l) & 1: r[l * kk:(l + 1) * kk] = G[u]
            rows.append(r)
    return rows
def binary_annihilator(V, L):
    """basis (bitmasks) of {theta in F_2^L : sum_l theta_l v_l = 0 for every row v of V}; V has L columns of uint64"""
    cols = []
    for l in range(L):
        x = 0
        for r in range(V.shape[0]): x = (x << 64) | int(V[r, l])
        cols.append(x)
    basis = []   # (reduced value, combination)
    ann = []
    for l in range(L):
        val, comb = cols[l], 1 << l
        for bv, bc in basis:
            if val ^ bv < val: val ^= bv; comb ^= bc
        if val: basis.append((val, comb)); basis.sort(reverse=True)
        else: ann.append(comb)
    return ann
def f2_rank(vs):
    b = []
    for v in vs:
        for x in b:
            if v ^ x < v: v ^= x
        if v: b.append(v); b.sort(reverse=True)
    return len(b)
def chain(cls, n, rnd, verbose=True, target=None):
    v = (n // 2).bit_length() - 1; k = n // 2; t = max(c.bit_length() for c in cls); L = t - 1
    tw = L83.make_tw(v, rnd)
    Gs = [L83.gen(tw[j:], v - j) for j in range(v + 1)]     # generator of the top code at scale n >> j
    spaces = [class_thetas(C) for C in cls]
    w0 = sum(len(s) for s in spaces)
    out = []; prev = None
    for j in range(v + 1):
        nj = n >> j; kj = k >> j; G = Gs[j]
        rows = rows_binary(G, kj, L, spaces)
        ker = L83.kernel(np.array(rows), L * kj) if rows else np.eye(L * kj, dtype=np.uint64)
        d = len(ker); wj = sum(len(s) for s in spaces)
        # Delta_u = span of N g_u over the kernel
        if d: ev = [L83.matmul(ker.reshape(d * L, kj), G.T.copy()) .reshape(d, L, nj)]
        delta = []; Dvec = []
        for u in range(nj):
            Vu = ev[0][:, :, u] if d else np.zeros((0, L), dtype=np.uint64)
            delta.append(L83.rank(Vu) if d else 0); Dvec.append(Vu)
        rec = dict(j=j, N=nj, d=d, w=wj, r=L * kj - d, delta=delta, dimQ=[len(s) for s in spaces], spaces=spaces)
        if prev is not None:
            # rho_u of the nodes one level down, on Delta of their parent (this level)
            rho = []
            for u, sp in enumerate(prev["spaces"]):
                Vp = Dvec[u >> 1]
                if len(sp) == 0 or d == 0: rho.append(0); continue
                T = np.zeros((len(sp), L), dtype=np.uint64)
                for a, th in enumerate(sp):
                    for l in range(L):
                        if (th >> l) & 1: T[a, l] = 1
                rho.append(L83.rank(L83.matmul(T, Vp.T.copy())))
            prev["rho"] = rho; prev["B"] = sum(rho); prev["check"] = (prev["d"] == 2 * d - sum(rho))
        out.append(rec); prev = rec
        if j == v: break
        # next pattern: binary functionals killing both bottom slices of every solution at the pair
        K3 = ker.reshape(d, L, kj) if d else np.zeros((0, L, kj), dtype=np.uint64)
        Gup = Gs[j + 1]; nxt = []
        if d:
            s0 = L83.matmul(np.ascontiguousarray(K3[:, :, 0::2]).reshape(d * L, kj // 2), Gup.T.copy()).reshape(d, L, nj // 2)
            s1 = L83.matmul(np.ascontiguousarray(K3[:, :, 1::2]).reshape(d * L, kj // 2), Gup.T.copy()).reshape(d, L, nj // 2)
        for p in range(nj // 2):
            if d == 0: nxt.append([1 << l for l in range(L)]); continue
            V = np.concatenate([s0[:, :, p], s1[:, :, p]], axis=0)
            nxt.append(binary_annihilator(V, L))
        spaces = nxt
    # distinctness of a generic solution, and agreements
    rows = rows_binary(Gs[0], k, L, [class_thetas(C) for C in cls]); ker0 = L83.kernel(np.array(rows), L * k)
    distinct = None; agree = None
    if len(ker0):
        pt = L83.random_point(ker0, rnd); cw = L83.codewords(Gs[0], k, t, pt); distinct = len(set(map(tuple, cw.tolist())))
        agree = []
        for l in range(t):
            a = 0
            for x in range(n):
                mem = L83.bits(cls[x])
                if l in mem and all(cw[m][x] == cw[l][x] for m in mem): a += 1
            agree.append(a)
    sj = None
    if len(ker0):
        sj = []
        for j in range(v + 1):
            nj = n >> j; kj = k >> j; parts = []
            for u in range(nj):
                d_ = {}
                for l in range(t): d_.setdefault(tuple(cw[l, u << j:(u + 1) << j].tolist()), []).append(l)
                parts.append([sum(1 << l for l in c) for c in d_.values() if len(c) >= 2])
            sp = [[th for C in P for th in class_thetas(C)] for P in parts]
            rws = rows_binary(Gs[j], kj, L, sp)
            sj.append(len(L83.kernel(np.array(rws), L * kj)) if rws else L * kj)
    beta = None
    if len(ker0):
        beta = []   # beta[j][l]: leaves of the agreement set of l at which the class does not coincide on the block of height j
        for j in range(v + 1):
            bl = [0] * t
            for x in range(n):
                mem = L83.bits(cls[x])
                if len(mem) < 2: continue
                u = x >> j; ref = cw[mem[0], u << j:(u + 1) << j]
                if any((cw[m, u << j:(u + 1) << j] != ref).any() for m in mem[1:]):
                    for m in mem: bl[m] += 1
            beta.append(bl)
    return dict(n=n, k=k, t=t, L=L, levels=out, distinct=distinct, agree=agree, w=w0, s=sj, beta=beta)
def report(res, eta_num=None):
    n, k, L, t = res["n"], res["k"], res["L"], res["t"]; lev = res["levels"]; d0 = lev[0]["d"]
    a = min(res["agree"]) if res["agree"] else 0
    print(f"n={n} members={t} kernel d_0={d0} distinct={res['distinct']} agreements min {a} max {max(res['agree']) if res['agree'] else 0} weight w={res['w']} rank={L * k - d0} deficiency={res['w'] - (L * k - d0)} needed (L+1)a-n-Lk+1={(L + 1) * a - n - L * k + 1}")
    thetadim = L - lev[-1]["d"]
    print(f"  dim Theta = {thetadim}")
    if res.get("s"): print("  s_j (kernel of the block-coincidence partition pattern of a generic solution): " + " ".join(f"N={n >> j}:{x}" for j, x in enumerate(res["s"])) + "   2^j s_j - s_0: " + " ".join(str((1 << j) * x - res["s"][0]) for j, x in enumerate(res["s"])))
    crit = None; tot_gain = 0
    if res.get("beta"):
        import math
        for j, bl in enumerate(res["beta"]):
            N = n >> j
            if N < 4 or N > 64: continue
            F = (N // 2 + 1) * math.comb(N, N // 2); e = a - k; tot = sum(e + (1 << j) - b for b in bl)
            print(f"  incoherent leaves at scale N={N}: beta max {max(bl)} mean {sum(bl) / t:.2f}; e+2^j={e + (1 << j)}; sum_l (e+2^j-beta_l)={tot}" + (f" -> Theorem 4.1: members <= {(1 << j) * F * t / tot:.0f} (F({N})={F})" if tot > 0 else " -> no bound at this scale"))
    for rec in lev:
        j = rec["j"]; N = rec["N"]; d = rec["d"]
        line = f"  level {j}: N={N} d_j={d} D_j=d_j/k_j={2 * d / N:.3f} fine cost c_j=2^j d_j-d_0={(1 << j) * d - d0} (n/8={n / 8:g}, (a-k)={a - k})"
        if "rho" in rec:
            rho = rec["rho"]; up = lev[j + 1]
            gain = sum(q - r for q, r in zip(rec["dimQ"], rho)) - 2 * sum(up["dimQ"])
            tot_gain += (1 << j) * gain
            nz = sum(1 for r in rho if r > 0)
            hist = {}
            for u, r in enumerate(rho):
                if r > 0:
                    key = (rec["dimQ"][u], r, up["delta"][u >> 1], up["dimQ"][u >> 1]); hist[key] = hist.get(key, 0) + 1
            line += f" B_j={rec['B']} nodes with rho>0: {nz} (C*) {'ok' if rec['check'] else 'FAIL'} gain G_j={gain}"
            line += " | (dimQ_u,rho_u,delta_p,dimQ_p):count " + " ".join(f"{k_}:{c}" for k_, c in sorted(hist.items()))
        print(line)
        if crit is None and (1 << j) * d - d0 >= (a - k) and j > 0: crit = j - 1
    print(f"  sum_j 2^j G_j = {tot_gain} + k dim Theta = {k * thetadim} -> {tot_gain + k * thetadim} (deficiency {res['w'] - (L * k - d0)})")
    # critical scale: the coarsest scale N_j with c_j = 2^j d_j - d_0 < a - k (wildcards below the excess over the dimension)
    js = [rec["j"] for rec in lev if (1 << rec["j"]) * rec["d"] - d0 < a - k]
    if js: print(f"  critical scale: N = {n >> max(js)} (levels with 2^j d_j - d_0 < a - k: {js})")
    else: print("  no level with 2^j d_j - d_0 < a - k")
def brief(res):
    lev = res["levels"]; n, k, L = res["n"], res["k"], res["L"]; d0 = lev[0]["d"]; a = min(res["agree"]) if res["agree"] else 0
    ok = all(rec.get("check", True) for rec in lev)
    onef = all(sum(1 for r in rec["rho"] if r > 0) <= 2 * lev[rec["j"] + 1]["d"] - rec["d"] for rec in lev if "rho" in rec)
    js = [rec["j"] for rec in lev if (1 << rec["j"]) * rec["d"] - d0 < a - k]
    crit = n >> max(js) if js else 0
    bt = res.get("beta"); extra = ""; m0 = None; b8 = None
    if bt:
        j8 = max(0, len(bt) - 3)              # level of scale 8 (scale 2 is the last level)
        b8 = max(bt[j8]) if n >= 8 else None
        m0 = 0.0
        for i in range(j8):
            m0 = max(m0, max((bt[i + 1][l] - bt[i][l]) / (1 << i) for l in range(res["t"])))
        extra = f" | beta(8) max {b8} (e+b = {a - k + (1 << j8)}) | max nu_l(i)/2^i below scale 8: {m0:g}"
    return f"n={n} members={res['t']} distinct={res['distinct']} min agreement {a} deficiency {res['w'] - (L * k - d0)} d_j (N=n..2): {' '.join(str(rec['d']) for rec in lev)} | (C*) at every level: {'ok' if ok else 'FAIL'} | E_i <= 2 d_(i+1) - d_i: {'ok' if onef else 'FAIL'} | critical scale {crit}" + extra, ok, crit, (tuple(rec["d"] for rec in lev), b8, m0)
def parse_classes(line):
    s = line.split("classes per leaf:")[1].split("sizes:")[0]; out = []
    for tok in s.split():
        if tok == "|": continue
        out.append(0 if tok == "." else sum(1 << int(ch, 36) for ch in tok))
    return out
def expand_votes(line):
    m = re.search(r"top \[(\d+),(\d+)\] b=(\d+) .* M=(\d+) target=(\d+)", line); N, ku, b, M, target = map(int, m.groups())
    blocks = re.findall(r"\[([^\]]*)\]", line.split("votes:")[1]); cls = []
    for blk in blocks:
        for tok in blk.split():
            if tok.startswith("*"): cls += [(1 << M) - 1] * int(tok[1:])
            elif tok == ".": cls.append(0)
            else: cls.append(sum(1 << int(ch, 36) for ch in tok))
    return cls
def staircase(N, b, f, extra=True):
    """one-sided staircase: block 0 = b - 1 zeros and one leaf left, blocks 1..f free (single leaves), members = the N/2-subsets
    of the other N - 1 - f blocks; the free leaves and the leaf left are handed to the members one by one"""
    blocks = list(range(1 + f, N)); mem = list(itertools.combinations(blocks, N // 2)); M = len(mem)
    cls = []
    singles = iter(range(M))
    def nxt():
        l = next(singles, None); return 0 if l is None else 1 << l
    cls += [(1 << M) - 1] * (b - 1) + [nxt() if extra else 0]
    for q in range(1, 1 + f): cls += [nxt() if extra else 0 for _ in range(b)]
    for q in blocks:
        c = sum(1 << l for l, S in enumerate(mem) if q in S); cls += [c] * b
    return cls
def staircase_multi(N, b, m, f):
    """m zero blocks (b - 1 common leaves each), f free blocks, members = the (N/2 - m + 1)-subsets of the other blocks"""
    blocks = list(range(m + f, N)); mem = list(itertools.combinations(blocks, N // 2 - m + 1)); M = len(mem)
    singles = iter(range(M)); cls = []
    def nxt():
        l = next(singles, None); return 0 if l is None else 1 << l
    for q in range(m): cls += [(1 << M) - 1] * (b - 1) + [nxt()]
    for q in range(m, m + f): cls += [nxt() for _ in range(b)]
    for q in blocks:
        c = sum(1 << l for l, S in enumerate(mem) if q in S); cls += [c] * b
    return cls
if __name__ == "__main__":
    rnd = random.Random(20261121)
    if sys.argv[1] == "stair":
        N, b, f = map(int, sys.argv[2:5]); cls = staircase(N, b, f)
        res = chain(cls, N * b, rnd); report(res); print("  " + brief(res)[0])
    elif sys.argv[1] == "stairm":
        N, b, m, f = map(int, sys.argv[2:6]); cls = staircase_multi(N, b, m, f)
        res = chain(cls, N * b, rnd); report(res); print("  " + brief(res)[0])
    else:
        mx = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9; cnt = 0; br = len(sys.argv) > 3 and sys.argv[3] == "brief"; tally = {}
        for line in open(sys.argv[1]):
            if "classes per leaf:" in line: cls = parse_classes(line)
            elif "votes:" in line: cls = expand_votes(line)
            else: continue
            res = chain(cls, len(cls), rnd); cnt += 1
            if br:
                txt, ok, crit, ds = brief(res); key = (res["t"], min(res["agree"]) if res["agree"] else 0, ds, ok, crit); tally[key] = tally.get(key, 0) + 1
                if not ok: print(line.strip()[:200]); print("  " + txt)
            else: print(line.strip()[:160]); report(res)
            if cnt >= mx: break
        if br:
            print(f"{cnt} patterns of {sys.argv[1]}; (members, min agreement, ((d_j for N = n..2), max beta_l(8), max nu_l(i)/2^i below scale 8), (C*) ok at every level, coarsest scale with c_j < e): count")
            for key, c in sorted(tally.items()): print("  ", key, ":", c)
