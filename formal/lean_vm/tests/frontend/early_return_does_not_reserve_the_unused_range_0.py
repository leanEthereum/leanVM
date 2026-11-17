
def main():
    out = HeapBuf(1)
    for x in mul_range(1, GEN ** 4294967296):
        if x == 1:
            out[1] = 7
            return
    public = 1
    assert public[1] == out[1]
    return
