def main():
    flag = StackBuf(1)
    hint_witness(flag, "flag")
    a = [1, 2, 3, 4]
    if flag[0] == 1:
        ignored = StackBuf(2)
        keccak(a[0:2], a[2:4], ignored)
    out = StackBuf(2)
    keccak(a[0:2], a[2:4], out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
