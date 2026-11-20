def main():
    pair = StackBuf(17)
    for k in unroll(0, 17):
        pair[k] = const(k + 1)
    st = StackBuf(13)
    keccak_cells(pair, st, final=0)
    out = StackBuf(2)
    keccak_cells([18, 19], out, state=st)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
