
def make_heap(x):
    h = HeapBuf(2)
    h[1] = x
    h[GEN] = x * x
    return h

def run(stop):
    saved = HeapBuf(GEN ** 12)
    heaps = HeapBuf(GEN ** 12)
    nested = HeapBuf(GEN ** 36)
    sums = HeapBuf(GEN ** 13)
    sums[GEN ** 2] = 0
    for x in mul_range(GEN ** 2, stop):
        pair = [x, x * x]
        saved[x] = addr(pair)
        heaps[x] = make_heap(x)
        for y in mul_range(1, GEN ** 3):
            local = [x, y]
            nested[x ** 3 * y] = addr(local)
        sums[x * GEN] = sums[x] + x
    for x in mul_range(GEN ** 2, stop):
        p = saved[x]
        h = heaps[x]
        assert p[1] == x
        assert p[GEN] == x * x
        assert h[1] == x
        assert h[GEN] == x * x
        for y in mul_range(1, GEN ** 3):
            q = nested[x ** 3 * y]
            assert q[1] == x
            assert q[GEN] == y
    return sums[stop]

def main():
    public = 1
    result = run(public[GEN])
    assert result == public[1]
    return
