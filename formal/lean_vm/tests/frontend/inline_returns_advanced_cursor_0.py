def main():
    hb = HeapBuf(4)
    hb[1] = 10
    hb[GEN] = 20
    hb[GEN ** 2] = 30
    fs = StackBuf(2)
    fs[0] = 1
    fs[1] = 2
    cur = hb
    fs, a, cur = step(fs, cur)
    fs, b, cur = step(fs, cur)
    v = cur[GEN ** 0]
    p = 1
    p[1] = a + b
    p[GEN] = v
    return

@inline
def step(state, cursor):
    x = cursor[GEN ** 0]
    tg = StackBuf(2)
    tg[0] = x
    tg[1] = 3
    nb = StackBuf(2)
    keccak(state, tg, nb)
    return nb, x, cursor * GEN
