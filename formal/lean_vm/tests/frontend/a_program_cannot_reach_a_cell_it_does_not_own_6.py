def main():
    hb = HeapBuf(8)
    hint_witness(hb[(GEN ** 2) ** 3:(GEN ** 2) ** 3 + 4], "w")
    p = GEN ** 0
    p[1] = GEN ** 0
    p[GEN] = GEN ** 0
    return
