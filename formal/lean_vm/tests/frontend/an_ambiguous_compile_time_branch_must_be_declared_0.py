def main():
    hb = HeapBuf(4)
    hb[GEN ** 0] = 5
    p = GEN ** 0
    p[1] = hb[GEN ** 0]
    p[GEN] = GEN ** 0
    return
