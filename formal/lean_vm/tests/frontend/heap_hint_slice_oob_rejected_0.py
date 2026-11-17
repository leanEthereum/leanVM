def main():
    hb = HeapBuf(8)
    hint_witness(hb[0:9], "w")
    x = hb[GEN ** 0]
    assert x == x
    return
