def main():
    hb = HeapBuf(8)
    hb[GEN ** 7] = 5
    row = hb * GEN ** 4
    y = row[GEN ** 3]
    assert y == 5
    return
