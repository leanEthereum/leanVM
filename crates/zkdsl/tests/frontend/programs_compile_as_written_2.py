def main():
    r = match(log(GEN), range(0, 2), lambda j: const(36893488147419103233))
    assert r == 36893488147419103233
    return
