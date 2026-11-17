@inline
def pick():
    m = hint_witness("m")
    return m

def main():
    r = pick()
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
