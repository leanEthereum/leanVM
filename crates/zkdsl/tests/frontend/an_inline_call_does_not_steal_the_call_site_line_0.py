
@inline
def idf(x):
    y = x * x
    return y


def main():
    hb = HeapBuf(4)
    hb[GEN] = GEN ** 3
    a = hb[GEN]
    assert idf(a) == GEN
    return
