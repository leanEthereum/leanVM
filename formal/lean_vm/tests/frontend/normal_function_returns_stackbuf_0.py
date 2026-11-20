def main():
    out = forward(5)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = out[2]
    return

def forward(v):
    out = make(v)
    return out

def make(v):
    out = StackBuf(3)
    out[0] = v
    out[1] = v + 3
    out[2] = 11
    return out
