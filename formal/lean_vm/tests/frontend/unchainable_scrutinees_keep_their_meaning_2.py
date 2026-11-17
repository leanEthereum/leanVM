@inline
def step(k: Const):
    return GEN ** ((k + 1) % 4)

def main():
    x = GEN ** 0
    for p in unroll(0, 3):
        x = match(log(x), range(0, 4), lambda k: step(k))
    q = 1
    q[1] = x
    q[GEN] = 0
    return
