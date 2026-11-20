def main():
    hb = HeapBuf(8)
    hb[GEN ** 7] = 5
    out = StackBuf(2)
    keccak(hb[7:9], hb[7:9], out)
    return
