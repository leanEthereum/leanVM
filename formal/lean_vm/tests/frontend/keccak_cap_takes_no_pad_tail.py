def main():
    s = StackBuf(13)
    keccak([0, 0], [0, 0], s)
    t = StackBuf(4)
    o = StackBuf(13)
    keccak([0, 0], [0, 0], o, tail=t, cap=s, pad_tail=1)
    return
