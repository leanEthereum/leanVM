
def main():
    h = HeapBuf(3)
    hint_witness(h[0:3], "values")
    public = 1
    if public[1] == 0:
        a = h[1] + h[GEN]
    else:
        b = h[1] + h[GEN]
    h[GEN ** 2] = h[1]
    assert h[GEN ** 2] == h[1]
    h[1] = public[GEN]
    return
