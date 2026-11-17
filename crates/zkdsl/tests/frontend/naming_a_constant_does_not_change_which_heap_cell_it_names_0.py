def main():
    rb = StackBuf(1)
    hint_witness(rb[0:1], "r")
    r = rb[0]
    hb = HeapBuf(16)
    hint_witness(hb[0:4], "vals")
    K = 3 + 1
    x = hb[(r * r) * K]
    p = GEN ** 0
    p[1] = x
    p[GEN] = GEN ** 0
    return
