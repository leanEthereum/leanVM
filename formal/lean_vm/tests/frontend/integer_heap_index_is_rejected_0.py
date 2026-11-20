def main():
    b = HeapBuf(4)
    b[1] = 3
    b[GEN] = 5
    x = 0
    for k in unroll(0, 2):
        p = 1
        p[GEN ** k] = b[k]
    return
