def main():
    hb = HeapBuf(4)
    if const(2 ** 40 == 2 ** 40):
        hb[GEN ** 0] = 5
    else:
        hb[GEN ** 0] = 7
    p = GEN ** 0
    p[1] = hb[GEN ** 0]
    p[GEN] = GEN ** 0
    return
