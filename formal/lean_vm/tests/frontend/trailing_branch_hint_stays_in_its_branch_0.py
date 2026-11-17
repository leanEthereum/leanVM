def main():
    flag = StackBuf(1)
    hint_witness(flag, "flag")
    data = StackBuf(1)
    if flag[0] == 1:
        print("anchor", flag[0])
        hint_witness(data, "data")
    p = 1
    p[1] = flag[0]
    p[GEN] = 0
    return
