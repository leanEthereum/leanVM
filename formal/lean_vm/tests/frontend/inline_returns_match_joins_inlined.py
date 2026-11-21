C = [GEN ** 2]

@inline
def five():
    return 5

@inline
def scale(x, k):
    return x * k + 0

@inline
def prod(a, b):
    return a * b

@inline
def first(s: StackBuf(1)):
    return s[0]

@inline
def sq(x):
    x = x * x
    return x

@inline
def rd(b, i):
    return b[i]

@inline
def pick(a, b, k: Const):
    r = five()
    if const(k == 1):
        r = b
    if const(k == 2):
        r = prod(a, b)
    return r

@inline
def pair(a, b, k: Const):
    return pick(a, b, k), a

@inline
def run(s: StackBuf(1), t: StackBuf(1), k: Const):
    if const(k == 0):
        t = s
    return t

def main():
    p = GEN ** 0
    x = hint_witness("w")
    a = hint_witness("w")
    b = hint_witness("w")
    assert log(x) < 3
    u, v = match(log(x), range(0, 3), lambda i: pair(a, b, i))
    r = match(log(x), range(0, 3), lambda i: pick(a, b, i))
    s = [a]
    t = [b]
    q = match(log(x), range(0, 3), lambda i: run(s, t, i))
    p[1] = u * v
    p[GEN] = r * q
    return
