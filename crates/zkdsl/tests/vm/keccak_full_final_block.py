def main():
    m = StackBuf(9)
    for k in unroll(0, 9):
        m[k] = const(k + 1)
    one = StackBuf(2)
    keccak_cells(m, one, len=135)
    two = StackBuf(2)
    keccak_cells(m, two, len=136)
    assert two[0] == 130804811289604742947188209148972184226
    assert two[1] == 120867053423954764924108221573135705778
    p = 1
    p[1] = one[0]
    p[GEN] = one[1]
    return
