@inline
def scale(x, k):
    return x * k

@inline
def prod(a, b):
    return a * b

def main():
    public = 1
    w = public[1]
    s = StackBuf(1)
    y = w * 6
    s[0] = w * w
    out = HeapBuf(2)
    out[1] = y
    out[GEN] = s[0]
    return
