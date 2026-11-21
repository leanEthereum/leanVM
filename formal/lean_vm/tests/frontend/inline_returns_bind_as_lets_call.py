@inline
def step(cursor, acc):
    x = cursor[GEN ** 0]
    y = acc * x
    return y, x, cursor * GEN

@inline
def word(a, b, j: Const):
    w = a
    if const(j == 1):
        w = b
    return w

def main():
    public = 1
    seed = public[1]
    b = HeapBuf(2)
    for i in unroll(0, 2):
        b[GEN ** i] = seed * GEN ** i
    cur = b
    acc = seed
    for i in unroll(0, 2):
        acc, x, cur = step(cur, acc)
    out = HeapBuf(3)
    out[1] = acc
    out[GEN] = x
    out[GEN ** 2] = word(acc, x, 1)
    return
