@inline
def f(s: StackBuf(2)):
    return s[0]

def main():
    t = StackBuf(3)
    t[0] = 1
    r = f(t)
    return
