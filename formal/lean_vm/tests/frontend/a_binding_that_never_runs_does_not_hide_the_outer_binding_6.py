def main():
    s = StackBuf(2)
    hb = HeapBuf(2)
    for i in mul_range(1, GEN ** 2):
        if const(0 == 1):
            if i == 1:
                s = StackBuf(2)
                keccak([1, 2], [3, 4], s)
        for k in unroll(0, 0):
            hb[i] = s[0]
        hb[i] = 5
    keccak([1, 2], [3, 4], s)
    return
