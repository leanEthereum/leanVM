def main():
    hb = HeapBuf(8)
    hb[GEN * GEN] = GEN ** 5
    p = GEN ** 0
    p[1] = hb[GEN * 2]
    p[GEN] = hb[GEN ** 2]
    return
