def main():
    pair = StackBuf(17)
    for k in unroll(0, 17):
        pair[k] = const(k + 1)
    chain = HeapBuf(13)
    keccak_cells(pair, chain[0:13], final=0)
    out = StackBuf(2)
    keccak_cells([18, 19], out, state=chain[0:13])
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
