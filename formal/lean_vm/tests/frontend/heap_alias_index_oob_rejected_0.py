def main():
    hb = HeapBuf(8)
    row = hb * GEN ** 6
    x = row[GEN ** 3]
    assert x == x
    return
