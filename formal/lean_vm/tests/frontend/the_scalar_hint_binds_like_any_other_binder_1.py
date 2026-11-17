def main():
    sb = StackBuf(2)
    sb[0] = GEN ** 1
    sb[1] = GEN ** 2
    hb = HeapBuf(4)
    for i in mul_range(1, 4):
        if i == i:
            sb = hint_witness("w")
            hb[i] = sb
    p = GEN ** 0
    p[1] = sb[0]
    p[GEN] = GEN ** 0
    return
