@inline
def scale(a, n: Const):
    if 2 * n == 2:
        t = a * 3
    return t

def main():
    t = 2
    acc = 5
    out = HeapBuf(8)
    for i in mul_range(1, GEN ** 4):
        if i == 1:
            for k in unroll(0, 1):
                if k == 0:
                    t = 9
            out[i] = t
        for k in unroll(0, 2):
            if k == 0:
                acc = i
            else:
                acc = acc * GEN
        out[i * GEN] = acc
        out[i * GEN ** 4] = scale(t, 1)
        for k in unroll(0, 1):
            if 2 * k == 0:
                i = i * GEN
    out[GEN ** 5] = 7
    assert out[1] == 9
    assert out[GEN] == GEN
    assert out[GEN ** 3] == GEN ** 3
    assert out[GEN ** 4] == 6
    assert out[GEN ** 6] == 6
    return
