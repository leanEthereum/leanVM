# Error: dead code after `return` must be rejected at compile time.
def main():
    x = 1
    return
    assert x == 0
    return
