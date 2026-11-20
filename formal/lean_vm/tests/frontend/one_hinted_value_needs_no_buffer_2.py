def main():
    hb = HeapBuf(4)
    for i in mul_range(1, 8):
        w = hint_witness("w")
        hb[i] = w
    p = GEN ** 0
    p[1] = hb[GEN]
    p[GEN] = GEN ** 0
    return
