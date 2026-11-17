def main():
    ctr = 305419896
    out = StackBuf(2)
    keccak([1, 2], [3, ctr], out, len=52)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
