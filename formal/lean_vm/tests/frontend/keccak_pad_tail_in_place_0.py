def main():
    kids = StackBuf(5)
    kids[0] = 4
    kids[1] = 5
    out = StackBuf(2)
    keccak([1, 2], [3, kids[0]], out, tail=kids[1:5], len=80, pad_tail=1)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
