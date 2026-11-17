def main():
    hb = HeapBuf(8)
    x = hb[GEN ** 8]
    assert x == x
    return
