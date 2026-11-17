def main():
    hb = HeapBuf(8)
    hb[1] = 1
    for i in mul_range(1, 16):
        hb[i * GEN] = hb[i]
    return
