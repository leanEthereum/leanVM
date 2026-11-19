C = [GEN ** 2]

def five():
    return 5

def scale(x, k):
    return x * k + 0

def prod(a, b):
    return a * b

def first(s: StackBuf(1)):
    return s[0]

def sq(x):
    x = x * x
    return x

def rd(b, i):
    return b[i]

def pick(a, b, k: Const):
    r = five()
    if const(k == 1):
        r = b
    if const(k == 2):
        r = prod(a, b)
    return r

def pair(a, b, k: Const):
    return pick(a, b, k), a

def run(s: StackBuf(1), t: StackBuf(1), k: Const):
    if const(k == 0):
        t = s
    return t

def main():
    p = GEN ** 0
    w = hint_witness("w")
    k = 7 - 2
    p[1] = scale(w, 3 + 5) * k
    p[GEN] = scale(w, 3 * 3)
    return
