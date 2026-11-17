def main():
    hb = HeapBuf(8)
    w = GEN ** 3
    for i in mul_range(1, GEN ** 4):
        if i == GEN:
            w = GEN
            hb[i * GEN] = w
        else:
            hb[i * GEN] = w
    p = GEN ** 0
    p[1] = hb[GEN ** 2]
    p[GEN] = hb[GEN ** 3]
    return
