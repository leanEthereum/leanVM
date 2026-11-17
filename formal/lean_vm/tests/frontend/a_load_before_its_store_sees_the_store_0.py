def main():
    h = HeapBuf(1)
    x = h[1]
    h[1] = GEN ** 3
    public = 1
    assert public[1] == x * GEN
    return
