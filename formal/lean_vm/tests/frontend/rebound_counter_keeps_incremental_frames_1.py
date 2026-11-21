
def bump(x):
    if x == 1:
        return GEN ** 5
    if x == GEN ** 6:
        return 1
    return x

def main():
    public = 1
    seen = HeapBuf(7)
    for x in mul_range(1, public[GEN]):
        seen[x] = x
        x = bump(x)
    assert seen[GEN ** 6] == GEN ** 6
    assert seen[GEN] == GEN
    return
