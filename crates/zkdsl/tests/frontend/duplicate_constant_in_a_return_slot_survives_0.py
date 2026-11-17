def tag(x):
    # `marker` is the same constant the flag below returns, and it is computed
    # first, so the flag's `SET` is a textual duplicate of it.
    marker = 7
    return x * marker, 7

def main():
    v, flag = tag(GEN ** 3)
    p = 1
    p[1] = v
    p[GEN] = flag
    return
