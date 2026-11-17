def main():
    hb = HeapBuf(2)
    nxt = HeapBuf(2)
    hint_witness(hb[GEN ** 1:GEN ** 1 + 2], "w")
    p = GEN ** 0
    p[1] = GEN ** 0
    p[GEN] = GEN ** 0
    return
