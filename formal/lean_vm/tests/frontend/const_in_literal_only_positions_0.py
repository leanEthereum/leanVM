LEN = 3
BOUND = 8

def main():
    x = GEN ** LEN
    assert log x < BOUND
    return
