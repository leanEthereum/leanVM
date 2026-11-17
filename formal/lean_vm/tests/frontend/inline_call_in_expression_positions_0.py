@inline
def wprod(ch, n: Const, idx: Const):
    # eq-tensor weight of compile-time idx over ch[0..n)
    w = GEN ** 0
    for c in unroll(0, n):
        cv = ch[GEN ** c]
        if (idx // (2 ** c)) % 2 == 1:
            w *= cv
        else:
            w *= (1 + cv)
    return w

def main():
    b = HeapBuf(4)
    b[1] = 3
    b[GEN] = 5
    x = wprod(b, 2, 2)
    y = 7 * wprod(b, 2, 1)
    out = HeapBuf(2)
    out[1] = wprod(b, 2, 3)
    p = 1
    p[1] = x
    p[GEN] = y + out[1]
    return
