def main():
    run = StackBuf(20)
    for k in unroll(0, 20):
        run[k] = const(k + 1)
    out = StackBuf(2)
    keccak_cells(run, out)
    hb = HeapBuf(16)
    for k in unroll(0, 16):
        hb[GEN ** k] = const(k + 1)
    heap_out = StackBuf(2)
    keccak_cells(hb[0:16], heap_out)
    assert heap_out[0] == 51840480322923128489450997007565169922
    assert heap_out[1] == 33612726202150371068450760312134188472
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
