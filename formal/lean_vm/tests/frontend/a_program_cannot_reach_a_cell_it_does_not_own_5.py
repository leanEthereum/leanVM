def main():
    hb = HeapBuf(4)
    hint_witness(hb[GEN ** 1:GEN ** 1 + 2], "w")
    p = GEN ** 0
    p[1] = hb[GEN]
    p[GEN] = GEN ** 0
    return
