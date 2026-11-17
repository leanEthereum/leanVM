def main():
    c = 5
    hb = HeapBuf(4)
    for i in mul_range(1, 4):
        hb[i] = c
    p = GEN ** 0
    p[1] = hb[GEN]
    p[GEN] = GEN ** 0
    return
