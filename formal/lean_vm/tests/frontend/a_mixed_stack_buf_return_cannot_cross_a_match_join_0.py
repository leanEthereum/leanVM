@inline
def f(k: Const):
    s = StackBuf(2)
    s[0] = GEN ** 7
    s[1] = GEN ** 9
    return GEN ** k, s

def main():
    x = GEN
    a, b = match(log(x), range(0, 2), lambda i: f(i))
    assert a == a
    assert b == GEN ** 7
    return
