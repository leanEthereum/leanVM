def main():
    rb = StackBuf(1)
    hint_witness(rb[0:1], "x,y#z]w")
    p = GEN ** 0
    p[1] = rb[0]
    p[GEN] = GEN ** 0
    return
