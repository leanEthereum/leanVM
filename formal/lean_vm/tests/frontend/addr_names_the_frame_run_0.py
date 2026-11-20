def main():
    w = StackBuf(1)
    hint_witness(w, "v")
    out = probe(w[0])
    p = 1
    p[1] = out
    p[GEN] = 1
    return

def probe(v):
    bits = StackBuf(8)
    hint_decompose_bits(bits, v, 8)
    ptr = addr(bits)
    acc = 0
    for i in unroll(0, 8):
        b = bits[i]
        bits[i] = b * b
        acc += b * (2 ** i)
    assert acc == v
    total = 0
    for i in unroll(0, 8):
        total += ptr[GEN ** i] * (2 ** i)
    assert total == v
    for x in mul_range(1, GEN ** 8):
        chk = ptr[x]
        assert chk * chk == chk
    assert addr(bits) == ptr
    return total
