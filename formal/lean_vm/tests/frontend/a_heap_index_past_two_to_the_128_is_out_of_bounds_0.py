def main():
    hb = HeapBuf(8)
    row = hb * GEN ** 340282366920938463463374607431768211455
    row[GEN ** 2] = 5
    return
