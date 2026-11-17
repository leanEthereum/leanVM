
def main():
    public = 1
    out = HeapBuf(2)
    for x in mul_range(GEN ** 65535, public[GEN]):
        if x == GEN ** 65535:
            out[1] = x
        else:
            out[GEN] = x
    assert out[GEN] == public[1]
    return
