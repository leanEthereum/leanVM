@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + 18446744073709551616 * b

def main():
    a = 5
    b = 7
    packed = pack64x2(a, b)
    p = 1
    p[1] = packed
    p[GEN] = packed
    return
