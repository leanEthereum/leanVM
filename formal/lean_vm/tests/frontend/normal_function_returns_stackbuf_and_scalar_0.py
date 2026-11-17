def main():
    out, x = make(9)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = x
    return

def make(v):
    out = [v, 6]
    return out, v + 1
