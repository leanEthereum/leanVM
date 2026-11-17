def main():
    run = StackBuf(40)
    for k in unroll(0, 40):
        run[k] = const(k + 1)
    out = StackBuf(2)
    keccak_cells([run[2 * k] for k in unroll(0, 20)], out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
