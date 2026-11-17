def add_both(a, b):
    return a + b

def main():
    k = GEN ** 5
    # Both arguments are the same expression, and the sum is computed here too,
    # so every operand the call needs has a duplicate in this frame.
    local = k + k
    s = add_both(k, k)
    p = 1
    p[1] = s + local
    return
