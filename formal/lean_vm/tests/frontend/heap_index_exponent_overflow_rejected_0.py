def main():
    hb = HeapBuf(8)
    hb[GEN ** 340282366920938463463374607431768211455] = 5
    return
