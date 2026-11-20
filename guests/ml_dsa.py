# ML-DSA (FIPS 204) signature verification: ML-DSA.Verify_internal on N_SIGS claims.
#
# A claim is (pk, mu, sig). The guest hashes pk into tr = H(pk, 64) itself and publishes,
# for each claim, Keccak-256(tr || mu), chained: the public input is d_1 = c_0 and
# d_{s+1} = Keccak-256(d_s || c_s). Whoever checks a claim on (pk, M) computes mu from tr and
# the message, as Verify does, so the guest never reads a message.
#
# Arithmetic mod q lives in the exponent: an integer v is the field element g^v, exact while
# |v| < 2^63, so + is MUL and a product by a constant is a power. A reduction v = r + q t is
# advice, r and t in 12-bit limbs, each range checked and weighted by a table lookup. SHAKE
# runs on the KECCAK permutation, absorbing its own blocks; bytes enter as hinted g-powers,
# each range checked and tied back to its lane through a table of its bits. The widest range
# checks, z's 2 ZB + 1 and UseHint's gamma2, need a memory past them, which every run's own
# size gives.
from snark_lib import *

K = K_PLACEHOLDER
L = L_PLACEHOLDER
TAU = TAU_PLACEHOLDER
OMEGA = OMEGA_PLACEHOLDER
GAMMA2 = GAMMA2_PLACEHOLDER
W1_BITS = W1_BITS_PLACEHOLDER
ZB = ZB_PLACEHOLDER  # gamma1 - beta - 1: a valid z has |z_i| <= ZB
CT_LANES = CT_LANES_PLACEHOLDER  # c~ is lambda / 4 bytes, CT_LANES lanes
N_SIGS = N_SIGS_PLACEHOLDER
# UseHint by table: index k' = r1 + (M_W1 + 1) s + (2 M_W1 + 1) h, for the hint bit h, r0 > 0
# as s, and r1 = HighBits; each array gives one column, from the host.
UH_D = UH_D_PLACEHOLDER  # r1 * 2 gamma2 + s * gamma2
UH_H = UH_H_PLACEHOLDER  # h
UH_W1 = UH_W1_PLACEHOLDER  # UseHint's result

Q = 8380417
M_W1 = (Q - 1) // (2 * GAMMA2)
NKP = 4 * M_W1 + 2
Y_TOWER = 18446744073709551616
PAD_FIRST = 31  # SHAKE's suffix 1111 and pad10*1's first bit
PAD_LAST = 9223372036854775808  # pad10*1's last bit, the top of a lane
PAD128_LAST = PAD_LAST * Y_TOWER  # SHAKE128's last rate lane, lane 20, is cell 10's high limb

PK_LANES = 4 + 40 * K
PK_BLOCKS = (8 * PK_LANES + 136) // 136
NW1 = 4 * K * W1_BITS  # lanes of w1Encode
W1H_BLOCKS = (64 + 8 * NW1 + 136) // 136
CHW = CHW_PLACEHOLDER  # w1 coefficients a packing chunk, 64 / gcd(64, W1_BITS): LPC whole lanes
LPC = W1_BITS * CHW // 64
NCH = 256 // CHW
EXA_STRIDE = 280  # accepted candidates a poly can take: five blocks of 56
EXA_POLY = 3 * EXA_STRIDE  # its three limb arrays
NTT_POLY = 2304  # nine layers of 256

# f = 256^-1 mod q, as f - q = 2^5 - 2^15; K1 q is past f' o + Z for every INTT output o < 2^31
K1 = (32736 * 2147483648 + 64 * 1023 * 8192) // Q + 1
G_QB = GEN ** (Q - ZB)
GQ = GEN ** Q

# Tables in main's frame; a sub-table of 256 holds byte v at v.
OFF_LB = 0  # 8: byte v as lane byte k, v << 8k
OFF_T1 = 2048  # 8: a t1 coefficient's share of byte v, times 2^d, in the exponent
OFF_X256 = 4096  # g^(256 v)
OFF_M127 = 4352  # g^(v & 127)
OFF_TOP = 4608  # v & 127 == 127
OFF_SG = 4864  # 8: g^(256 bit_t(v))
OFF_S12 = 6912  # 2048: g^(4096 v)
OFF_Q0 = 8960  # 4096: g^(q v)
OFF_Q1 = 13056  # 4096: g^(q 2^12 v)
OFF_Q2 = 17152  # 512: g^(q 2^24 v)
OFF_QS = 17664  # 6 quarter-square tables
QS_SIZE = 4606  # s = -255 .. 4350 at s + 255
OFF_UH = OFF_QS + 6 * QS_SIZE  # 7 columns of NKP: D, H, w1, the two straddles' low and high parts
TAB_SIZE = OFF_UH + 7 * NKP

ZETAS = [1, 4808194, 3765607, 3761513, 5178923, 5496691, 5234739, 5178987, 7778734, 3542485, 2682288, 2129892, 3764867, 7375178, 557458, 7159240, 5010068, 4317364, 2663378, 6705802, 4855975, 7946292, 676590, 7044481, 5152541, 1714295, 2453983, 1460718, 7737789, 4795319, 2815639, 2283733, 3602218, 3182878, 2740543, 4793971, 5269599, 2101410, 3704823, 1159875, 394148, 928749, 1095468, 4874037, 2071829, 4361428, 3241972, 2156050, 3415069, 1759347, 7562881, 4805951, 3756790, 6444618, 6663429, 4430364, 5483103, 3192354, 556856, 3870317, 2917338, 1853806, 3345963, 1858416, 3073009, 1277625, 5744944, 3852015, 4183372, 5157610, 5258977, 8106357, 2508980, 2028118, 1937570, 4564692, 2811291, 5396636, 7270901, 4158088, 1528066, 482649, 1148858, 5418153, 7814814, 169688, 2462444, 5046034, 4213992, 4892034, 1987814, 5183169, 1736313, 235407, 5130263, 3258457, 5801164, 1787943, 5989328, 6125690, 3482206, 4197502, 7080401, 6018354, 7062739, 2461387, 3035980, 621164, 3901472, 7153756, 2925816, 3374250, 1356448, 5604662, 2683270, 5601629, 4912752, 2312838, 7727142, 7921254, 348812, 8052569, 1011223, 6026202, 4561790, 6458164, 6143691, 1744507, 1753, 6444997, 5720892, 6924527, 2660408, 6600190, 8321269, 2772600, 1182243, 87208, 636927, 4415111, 4423672, 6084020, 5095502, 4663471, 8352605, 822541, 1009365, 5926272, 6400920, 1596822, 4423473, 4620952, 6695264, 4969849, 2678278, 4611469, 4829411, 635956, 8129971, 5925040, 4234153, 6607829, 2192938, 6653329, 2387513, 4768667, 8111961, 5199961, 3747250, 2296099, 1239911, 4541938, 3195676, 2642980, 1254190, 8368000, 2998219, 141835, 8291116, 2513018, 7025525, 613238, 7070156, 6161950, 7921677, 6458423, 4040196, 4908348, 2039144, 6500539, 7561656, 6201452, 6757063, 2105286, 6006015, 6346610, 586241, 7200804, 527981, 5637006, 6903432, 1994046, 2491325, 6987258, 507927, 7192532, 7655613, 6545891, 5346675, 8041997, 2647994, 3009748, 5767564, 4148469, 749577, 4357667, 3980599, 2569011, 6764887, 1723229, 1665318, 2028038, 1163598, 5011144, 3994671, 8368538, 7009900, 3020393, 3363542, 214880, 545376, 7609976, 3105558, 7277073, 508145, 7826699, 860144, 3430436, 140244, 6866265, 6195333, 3123762, 2358373, 6187330, 5365997, 6663603, 2926054, 7987710, 8077412, 3531229, 4405932, 4606686, 1900052, 7598542, 1054478, 7648983]


def main():
    tab = StackBuf(TAB_SIZE)
    for v in unroll(0, 256):
        for k in unroll(0, 8):
            tab[OFF_LB + 256 * k + v] = const(v * 2 ** (8 * k))
            tab[OFF_SG + 256 * k + v] = GEN ** const(256 * ((v // 2 ** k) % 2))
        # t1 = b0 | (b1 & 3) << 8, (b1 >> 2) | (b2 & 15) << 6, (b2 >> 4) | (b3 & 63) << 4, (b3 >> 6) | b4 << 2
        tab[OFF_T1 + v] = GEN ** const(v * 8192)
        tab[OFF_T1 + 256 + v] = GEN ** const((v % 4) * 256 * 8192)
        tab[OFF_T1 + 512 + v] = GEN ** const((v // 4) * 8192)
        tab[OFF_T1 + 768 + v] = GEN ** const((v % 16) * 64 * 8192)
        tab[OFF_T1 + 1024 + v] = GEN ** const((v // 16) * 8192)
        tab[OFF_T1 + 1280 + v] = GEN ** const((v % 64) * 16 * 8192)
        tab[OFF_T1 + 1536 + v] = GEN ** const((v // 64) * 8192)
        tab[OFF_T1 + 1792 + v] = GEN ** const(v * 4 * 8192)
        tab[OFF_X256 + v] = GEN ** const(256 * v)
        tab[OFF_M127 + v] = GEN ** const(v % 128)
        if const(v % 128 == 127):
            tab[OFF_TOP + v] = 1
        else:
            tab[OFF_TOP + v] = 0
    for v in unroll(0, 2048):
        tab[OFF_S12 + v] = GEN ** const(4096 * v)
    for v in unroll(0, 4096):
        tab[OFF_Q0 + v] = GQ ** v
        tab[OFF_Q1 + v] = GQ ** const(4096 * v)
    for v in unroll(0, 512):
        tab[OFF_Q2 + v] = (GQ ** 16777216) ** v
    for kk in unroll(0, 3):
        for ll in unroll(0, 2):
            for s in unroll(0, 255):
                tab[OFF_QS + QS_SIZE * (2 * kk + ll) + s] = (GEN ** const(2 ** (8 * kk + 12 * ll))) ** const(((255 - s) * (255 - s)) // 4)
            for s in unroll(255, QS_SIZE):
                tab[OFF_QS + QS_SIZE * (2 * kk + ll) + s] = (GEN ** const(2 ** (8 * kk + 12 * ll))) ** const(((s - 255) * (s - 255)) // 4)
    for kp in unroll(0, NKP):
        tab[OFF_UH + kp] = GEN ** UH_D[kp]
        tab[OFF_UH + NKP + kp] = GEN ** UH_H[kp]
        tab[OFF_UH + 2 * NKP + kp] = UH_W1[kp]
        # A 6-bit w1 straddles a lane at bit 60 and at bit 62.
        tab[OFF_UH + 3 * NKP + kp] = const((UH_W1[kp] % 16) * 2 ** 60)
        tab[OFF_UH + 4 * NKP + kp] = const(UH_W1[kp] // 16)
        tab[OFF_UH + 5 * NKP + kp] = const((UH_W1[kp] % 4) * 2 ** 62)
        tab[OFF_UH + 6 * NKP + kp] = const(UH_W1[kp] // 4)
    tp = addr(tab)
    digs = HeapBuf(2 * N_SIGS)
    for s in mul_range(1, GEN ** N_SIGS):
        verify_sig(tp, digs * s * s)
    acc = StackBuf(2)
    acc[0] = digs[1]
    acc[1] = digs[GEN]
    for s in unroll(1, N_SIGS):
        nxt = StackBuf(2)
        keccak(acc, [digs[GEN ** (2 * s)], digs[GEN ** (2 * s + 1)]], nxt)
        acc = nxt
    p = GEN ** 0
    p[1] = acc[0]
    p[GEN] = acc[1]
    return


def verify_sig(tp, dg):
    # pk = rho || t1: rho hinted as lanes, t1 as bytes; both go into the lanes tr hashes.
    ml = HeapBuf(17 * PK_BLOCKS)
    hint_witness(ml[0:4], "rho")
    s1 = HeapBuf(1024 * K)
    for i in unroll(0, K):
        t1_row(tp, ml * GEN ** (4 + 40 * i), s1 * GEN ** (1024 * i))
    pad_lanes(ml, PK_LANES, PK_BLOCKS)
    tr = absorb17(ml, PK_BLOCKS)
    hl = HeapBuf(17 * W1H_BLOCKS)
    hint_witness(hl[0:8], "mu")
    mc = [hl[1] + Y_TOWER * hl[GEN], hl[GEN ** 2] + Y_TOWER * hl[GEN ** 3], hl[GEN ** 4] + Y_TOWER * hl[GEN ** 5], hl[GEN ** 6] + Y_TOWER * hl[GEN ** 7]]
    dig = StackBuf(2)
    keccak(tr[0:2], tr[2:4], dig, tail=mc)
    dg[1] = dig[0]
    dg[GEN] = dig[1]

    a = HeapBuf(EXA_POLY * K * L)
    rc0 = ml[1] + Y_TOWER * ml[GEN]
    rc1 = ml[GEN ** 2] + Y_TOWER * ml[GEN ** 3]
    for i in unroll(0, K):
        for j in unroll(0, L):
            expand_poly(tp, rc0, rc1, const(j + 256 * i + PAD_FIRST * 65536), a * GEN ** (EXA_POLY * (L * i + j)))

    ct = HeapBuf(CT_LANES)
    hint_witness(ct[0:CT_LANES], "ct")
    pp = HeapBuf(TAU)
    sample_in_ball(tp, ct, s1, pp)

    nb = HeapBuf(NTT_POLY * L)
    zh = HeapBuf(512 * L)
    for j in unroll(0, L):
        ntt_fwd(tp, nb * GEN ** (NTT_POLY * j))
        zhat_reduce(tp, nb * GEN ** (NTT_POLY * j + 2048), zh * GEN ** (512 * j))
    wb = HeapBuf(NTT_POLY * K)
    pointwise(tp, tp * GEN ** (OFF_QS + 255), a, zh, wb)
    for i in unroll(0, K):
        intt(tp, wb * GEN ** (NTT_POLY * i))
    zc = HeapBuf(256 * K)
    sparse_ct1(pp, zc)

    hw = HeapBuf(NCH * K)
    for i in unroll(0, K):
        final_row(tp, wb * GEN ** (NTT_POLY * i + 2048), zc * GEN ** (256 * i), hl * GEN ** (8 + 4 * W1_BITS * i), hw * GEN ** (NCH * i))
    weight = hw[1]
    for n in unroll(1, NCH * K):
        weight = weight * hw[GEN ** n]
    assert log(weight) < OMEGA + 1
    pad_lanes(hl, 8 + NW1, W1H_BLOCKS)
    st = absorb17(hl, W1H_BLOCKS)
    for c in unroll(0, CT_LANES // 2):
        st[c] = ct[GEN ** (2 * c)] + Y_TOWER * ct[GEN ** (2 * c + 1)]
    return


# ================================ SHAKE on KECCAK ================================


@inline
def pad_lanes(ln, n: Const, nblocks: Const):
    # pad10*1 after n message lanes, to nblocks blocks of 17 lanes.
    ln[GEN ** n] = PAD_FIRST
    for m in unroll(n + 1, 17 * nblocks - 1):
        ln[GEN ** m] = 0
    ln[GEN ** (17 * nblocks - 1)] = PAD_LAST
    return


@inline
def absorb17(ln, nblocks: Const):
    # SHAKE256's absorption of the 17 nblocks lanes at ln, padded: the state after it,
    # whose first rate lanes are the first output.
    for b in unroll(0, nblocks):
        nx = StackBuf(13)
        for c in unroll(0, 8):
            cell = ln[GEN ** (17 * b + 2 * c)] + Y_TOWER * ln[GEN ** (17 * b + 2 * c + 1)]
            if const(b == 0):
                nx[c] = cell
            else:
                nx[c] = st[c] + cell
        if const(b == 0):
            nx[8] = ln[GEN ** 16]
            for c in unroll(9, 13):
                nx[c] = 0
        else:
            nx[8] = st[8] + ln[GEN ** (17 * b + 16)]
            for c in unroll(9, 13):
                nx[c] = st[c]
        st = StackBuf(13)
        keccak(nx[0:2], nx[2:4], st, tail=nx[4:8], cap=nx)
    return st


@inline
def lane_of(tp, eb, at: Const):
    # The lane whose eight bytes, low first, are hinted at eb[at..at+8] in the exponent.
    for k in unroll(0, 8):
        e = eb[at + k]
        assert log(e) < 256
        if const(k == 0):
            acc = tp[e * GEN ** OFF_LB]
        else:
            acc = acc + tp[e * GEN ** (OFF_LB + 256 * k)]
    return acc


# ===================================== t1 ========================================


def t1_row(tp, ml, s1):
    # Row i of t1: its 40 lanes into ml and its 256 coefficients, times 2^d, into the
    # row's sparse-product table s1: [g^T | g^-T | g^T | g^-T].
    for u in mul_range(1, GEN ** 8):
        t1_unit(tp, ml * u ** 5, s1 * u ** 32)
    return


def t1_unit(tp, ml, s1):
    # Five lanes, 40 bytes, 32 coefficients of ten bits.
    eb = StackBuf(40)
    hint_witness(eb, "t1")
    for w in unroll(0, 5):
        ml[GEN ** w] = lane_of(tp, eb, 8 * w)
    for g in unroll(0, 8):
        b0 = tp * eb[5 * g]
        b1 = tp * eb[5 * g + 1]
        b2 = tp * eb[5 * g + 2]
        b3 = tp * eb[5 * g + 3]
        b4 = tp * eb[5 * g + 4]
        t1_store(s1, 4 * g, b0[GEN ** OFF_T1] * b1[GEN ** (OFF_T1 + 256)])
        t1_store(s1, 4 * g + 1, b1[GEN ** (OFF_T1 + 512)] * b2[GEN ** (OFF_T1 + 768)])
        t1_store(s1, 4 * g + 2, b2[GEN ** (OFF_T1 + 1024)] * b3[GEN ** (OFF_T1 + 1280)])
        t1_store(s1, 4 * g + 3, b3[GEN ** (OFF_T1 + 1536)] * b4[GEN ** (OFF_T1 + 1792)])
    return


@inline
def t1_store(s1, n: Const, gt):
    s1[GEN ** n] = gt
    s1[GEN ** (n + 512)] = gt
    gi = 1 / gt
    s1[GEN ** (n + 256)] = gi
    s1[GEN ** (n + 768)] = gi
    return


# =================================== ExpandA =====================================


def expand_poly(tp, rc0, rc1, lane4, ap):
    # RejNTTPoly(rho || s || r): SHAKE128, five squeezed blocks of 56 three-byte
    # candidates, the accepted ones' limbs (b0, b1, b2 & 127) in the exponent at ap.
    cp = [0, 0, PAD128_LAST, 0, 0]
    st = StackBuf(13)
    keccak([rc0, rc1], [lane4, 0], st, tail=[0, 0, 0, 0], cap=cp)
    cnt = expand_block(tp, st, ap, GEN ** 0)
    for b in unroll(1, 5):
        nx = StackBuf(13)
        keccak(st[0:2], st[2:4], nx, tail=st[4:8], cap=st)
        st = nx
        cnt = expand_block(tp, st, ap, cnt)
    # At least 256 accepted; any past them are never read.
    assert log(cnt / GEN ** 256) < EXA_STRIDE - 255
    return


def expand_block(tp, st: StackBuf(13), ap, cnt):
    # The 21 rate lanes of st, as 168 hinted bytes.
    eb = StackBuf(168)
    hint_witness(eb, "exa")
    for c in unroll(0, 8):
        st[c] = lane_of(tp, eb, 16 * c) + Y_TOWER * lane_of(tp, eb, 16 * c + 8)
    st[8] = lane_of(tp, eb, 128)
    st[9] = lane_of(tp, eb, 136) + Y_TOWER * lane_of(tp, eb, 144)
    st[10] = lane_of(tp, eb, 152) + Y_TOWER * lane_of(tp, eb, 160)
    for c in unroll(0, 56):
        cnt = candidate(tp, eb, ap, cnt, c)
    return cnt


@inline
def candidate(tp, eb, ap, cnt, c: Const):
    # Candidate b0 + 256 b1 + 65536 (b2 & 127) is below q unless b2 & 127 == 127 and
    # b0 + 256 b1 > 0xE000; only then does the prover say which.
    e0 = eb[3 * c]
    e1 = eb[3 * c + 1]
    e2 = eb[3 * c + 2]
    nc = StackBuf(1)
    if tp[e2 * GEN ** OFF_TOP] == 0:
        accept(tp, ap, cnt, e0, e1, e2)
        nc[0] = cnt * GEN
    else:
        y = e0 * tp[e1 * GEN ** OFF_X256]
        rej = hint_witness("exr")
        if rej == 0:
            assert log(y) < 57345
            accept(tp, ap, cnt, e0, e1, e2)
            nc[0] = cnt * GEN
        else:
            assert log(y / GEN ** 57345) < 8191
            nc[0] = cnt
    return nc[0]


@inline
def accept(tp, ap, cnt, e0, e1, e2):
    p = ap * cnt
    p[1] = e0
    p[GEN ** EXA_STRIDE] = e1
    p[GEN ** (2 * EXA_STRIDE)] = tp[e2 * GEN ** OFF_M127]
    return


# ================================= SampleInBall ==================================


@inline
def sib_lane(ct, n: Const):
    if const(n // CT_LANES == 0):
        v = ct[GEN ** n]
    elif const(n == CT_LANES):
        v = PAD_FIRST
    elif const(n == 16):
        v = PAD_LAST
    else:
        v = 0
    return v


def sample_in_ball(tp, ct, s1, pp):
    # c = SampleInBall(c~), as the pointers its sparse product reads: nonzero k at
    # position p with sign bit b is s1 g^(256 - p + 256 b), read at + m for coefficient m.
    nx = StackBuf(13)
    for c in unroll(0, 8):
        nx[c] = sib_lane(ct, 2 * c) + Y_TOWER * sib_lane(ct, 2 * c + 1)
    nx[8] = PAD_LAST
    for c in unroll(9, 13):
        nx[c] = 0
    st = StackBuf(13)
    keccak(nx[0:2], nx[2:4], st, tail=nx[4:8], cap=nx)
    eb = StackBuf(136)
    hint_witness(eb, "sib")
    for c in unroll(0, 8):
        st[c] = lane_of(tp, eb, 16 * c) + Y_TOWER * lane_of(tp, eb, 16 * c + 8)
    st[8] = lane_of(tp, eb, 128)
    # The positions j_k: byte t is taken while k < TAU, accepted if j <= i = 256 - TAU + k.
    jb = HeapBuf(TAU)
    # A cell, so that every step's bound is a runtime one.
    kc0 = StackBuf(1)
    kc0[0] = GEN ** 0
    kc = kc0[0]
    for t in unroll(8, 136):
        nc = StackBuf(1)
        sib_step(eb, jb, kc, nc, t)
        kc = nc[0]
    assert kc == GEN ** TAU
    # Step k sets c_i = c_j, c_j = sign k: the sign sitting at j_k moves to i.
    pos = StackBuf(TAU)
    pos[0] = jb[1]
    for k in unroll(1, TAU):
        jk = jb[GEN ** k]
        nxt = StackBuf(TAU)
        for m in unroll(0, k):
            sib_move(pos, nxt, jk, m, k)
        nxt[k] = jk
        pos = nxt
    for k in unroll(0, TAU):
        sg = tp[eb[k // 8] * GEN ** (OFF_SG + 256 * (k % 8))]
        pp[GEN ** k] = s1 * GEN ** 256 * sg / pos[k]
    return


@inline
def sib_step(eb, jb, kc, nc, t: Const):
    if kc == GEN ** TAU:
        nc[0] = kc
    else:
        e = eb[t]
        f = hint_witness("sibf")
        bound = kc * GEN ** (257 - TAU)
        if f == 0:
            assert log(e) < log(bound)
            jb[kc] = e
            nc[0] = kc * GEN
        else:
            assert log(e / bound) < 256
            nc[0] = kc
    return


@inline
def sib_move(pos, nxt, jk, m: Const, k: Const):
    if pos[m] == jk:
        nxt[m] = GEN ** (256 - TAU + k)
    else:
        nxt[m] = pos[m]
    return


def sparse_ct1(pp, zc):
    # zc row i, coefficient m: g^(-(c t1 2^d)_m), eight coefficients a frame.
    for mm in mul_range(1, GEN ** 32):
        m8 = mm ** 8
        for k in unroll(0, TAU):
            p = pp[GEN ** k] * m8
            nacc = StackBuf(8 * K)
            for i in unroll(0, K):
                for c in unroll(0, 8):
                    if const(k == 0):
                        nacc[8 * i + c] = p[GEN ** (1024 * i + c)]
                    else:
                        nacc[8 * i + c] = acc[8 * i + c] * p[GEN ** (1024 * i + c)]
            acc = nacc
        for i in unroll(0, K):
            for c in unroll(0, 8):
                zc[m8 * GEN ** (256 * i + c)] = acc[8 * i + c]
    return


# ===================================== NTT =======================================


@inline
def reduce_mul(tp, x):
    # g^r for the advice r < 2^23 with x = g^(r + q t), t < 2^33.
    h = StackBuf(5)
    hint_witness(h, "red")
    assert log(h[0]) < 4096
    assert log(h[1]) < 2048
    assert log(h[2]) < 4096
    assert log(h[3]) < 4096
    assert log(h[4]) < 512
    r = h[0] * tp[h[1] * GEN ** OFF_S12]
    assert x == r * tp[h[2] * GEN ** OFF_Q0] * tp[h[3] * GEN ** OFF_Q1] * tp[h[4] * GEN ** OFF_Q2]
    return r


def ntt_fwd(tp, nb):
    # NTT(z) over nine layers of 256: layer 0 the hinted z + ZB, each butterfly's product
    # reduced, its sums not: a layer adds less than 2^23.
    hint_witness(nb[0:256], "z")
    for lay in unroll(0, 8):
        ntt_layer(tp, nb * GEN ** (256 * lay), GEN ** (2 ** (7 - lay)), lay)
    return


def ntt_layer(tp, src, n, lay: Const):
    for jj in mul_range(1, n):
        p = src * jj
        for blk in unroll(0, 2 ** lay):
            a = p[GEN ** (2 ** (8 - lay) * blk)]
            b = p[GEN ** (2 ** (8 - lay) * blk + 2 ** (7 - lay))]
            if const(lay == 0):
                assert log(a) < 2 * ZB + 1
                assert log(b) < 2 * ZB + 1
                a = a * G_QB
                b = b * G_QB
            t = reduce_mul(tp, b ** ZETAS[2 ** lay + blk])
            p[GEN ** (256 + 2 ** (8 - lay) * blk)] = a * t
            p[GEN ** (256 + 2 ** (8 - lay) * blk + 2 ** (7 - lay))] = a * GQ / t
    return


def zhat_reduce(tp, x, zh):
    # NTT(z) reduced below 2^23, as two limbs: the factors of the pointwise products.
    for mm in mul_range(1, GEN ** 256):
        h = StackBuf(3)
        hint_witness(h, "zr")
        assert log(h[0]) < 4096
        assert log(h[1]) < 2048
        assert log(h[2]) < 4096
        assert x[mm] == h[0] * tp[h[1] * GEN ** OFF_S12] * tp[h[2] * GEN ** OFF_Q0]
        zh[mm] = h[0]
        zh[mm * GEN ** 256] = h[1]
    return


def pointwise(tp, tq, a, zh, wb):
    # sum_j A_ij NTT(z_j), each product by quarter squares over the limbs: bytes of A,
    # 12-bit limbs of NTT(z), s = z + e and d = z - e read at s + 255 and d + 255. A
    # pointer must itself be an address, so tq = tp g^(OFF_QS + 255) carries the offset
    # that keeps z - e from reaching below the tables.
    for mm in mul_range(1, GEN ** 256):
        pa = a * mm
        pz = zh * mm
        pw = wb * mm
        zp = StackBuf(2 * L)
        for j in unroll(0, L):
            zp[2 * j] = tq * pz[GEN ** (512 * j)]
            zp[2 * j + 1] = tq * pz[GEN ** (512 * j + 256)]
        for i in unroll(0, K):
            for j in unroll(0, L):
                e = [pa[GEN ** (EXA_POLY * (L * i + j))], pa[GEN ** (EXA_POLY * (L * i + j) + EXA_STRIDE)], pa[GEN ** (EXA_POLY * (L * i + j) + 2 * EXA_STRIDE)]]
                for kk in unroll(0, 3):
                    for ll in unroll(0, 2):
                        sp = zp[2 * j + ll] * e[kk]
                        dp = zp[2 * j + ll] / e[kk]
                        fs = sp[GEN ** (QS_SIZE * (2 * kk + ll))]
                        fd = dp[GEN ** (QS_SIZE * (2 * kk + ll))]
                        if const(j + kk + ll == 0):
                            num = fs
                            den = fd
                        else:
                            num = num * fs
                            den = den * fd
            pw[GEN ** (NTT_POLY * i)] = reduce_mul(tp, num / den)
    return


def intt(tp, nb):
    # NTT^-1 without its final factor 256^-1, which the last step takes: each layer's
    # differences lifted by C q past its inputs (below 2^(23 + lay)), its sums unreduced.
    for lay in unroll(0, 8):
        intt_layer(tp, nb * GEN ** (256 * lay), GEN ** (2 ** lay), lay)
    return


def intt_layer(tp, src, n, lay: Const):
    for jj in mul_range(1, n):
        p = src * jj
        for blk in unroll(0, 2 ** (7 - lay)):
            a = p[GEN ** (2 ** (lay + 1) * blk)]
            b = p[GEN ** (2 ** (lay + 1) * blk + 2 ** lay)]
            p[GEN ** (256 + 2 ** (lay + 1) * blk)] = a * b
            d = a * GQ ** const(2 ** (lay + 1)) / b
            p[GEN ** (256 + 2 ** (lay + 1) * blk + 2 ** lay)] = reduce_mul(tp, d ** (Q - ZETAS[2 ** (8 - lay) - 1 - blk]))
    return


# ================================ UseHint and w1 =================================


def final_row(tp, o, zc, hl, hw):
    # Row i: w' = 256^-1 o - c t1 2^d, Decompose and UseHint by table, w1 packed into
    # the lanes c~' hashes, the hint bits' count into hw, one chunk of lanes a frame.
    for cc in mul_range(1, GEN ** NCH):
        base = cc ** CHW
        po = o * base
        pz = zc * base
        us = StackBuf(CHW)
        for c in unroll(0, CHW):
            us[c] = use_hint(tp, po[GEN ** c], pz[GEN ** c])
        for c in unroll(0, CHW):
            uc = us[c]
            if const(c == 0):
                wt = uc[GEN ** (OFF_UH + NKP)]
            else:
                wt = wt * uc[GEN ** (OFF_UH + NKP)]
        hw[cc] = wt
        pl = hl * cc ** LPC
        for ln in unroll(0, LPC):
            pl[GEN ** ln] = w1_lane(us, ln)
    return


@inline
def use_hint(tp, ov, zv):
    # x = f' o + K1 q + Z + gamma2 - 1 = D(k') + u + q t, u < gamma2; returns k' as a
    # pointer into the UseHint columns.
    h = StackBuf(5)
    hint_witness(h, "fin")
    assert log(h[0]) < NKP
    assert log(h[1]) < GAMMA2
    assert log(h[2]) < 4096
    assert log(h[3]) < 4096
    assert log(h[4]) < 512
    o32 = ov ** 32
    x = o32 / o32 ** 1024 * zv * (GQ ** K1 * GEN ** (GAMMA2 - 1))
    u = tp * h[0]
    assert x == u[GEN ** OFF_UH] * h[1] * tp[h[2] * GEN ** OFF_Q0] * tp[h[3] * GEN ** OFF_Q1] * tp[h[4] * GEN ** OFF_Q2]
    return u


@inline
def w1_lane(us, ln: Const):
    # Lane ln of a chunk: coefficient c's W1_BITS bits at bit W1_BITS c of the chunk, a
    # lane starting inside a coefficient taking its high bits first.
    if const(64 * ln % W1_BITS != 0):
        cs = us[64 * ln // W1_BITS]
        if const(W1_BITS * (64 * ln // W1_BITS) % 64 == 60):
            acc = cs[GEN ** (OFF_UH + 4 * NKP)]
        else:
            acc = cs[GEN ** (OFF_UH + 6 * NKP)]
    for c in unroll(0, CHW):
        if const(W1_BITS * c // 64 == ln):
            uc = us[c]
            if const((W1_BITS * c % 64 + W1_BITS - 1) // 64 == 0):
                part = uc[GEN ** (OFF_UH + 2 * NKP)] * const(2 ** (W1_BITS * c % 64))
            elif const(W1_BITS * c % 64 == 60):
                part = uc[GEN ** (OFF_UH + 3 * NKP)]
            else:
                part = uc[GEN ** (OFF_UH + 5 * NKP)]
            if const(W1_BITS * c == 64 * ln):
                acc = part
            else:
                acc = acc + part
    return acc
