def main():
    bits = StackBuf(4)
    out = StackBuf(1)
    out[0] = hint_log2_ceil(bits, 4, 0)
    return
