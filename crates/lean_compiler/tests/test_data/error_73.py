# Error: a lambda binder that shadows a name visible in an enclosing scope
# changes compiled semantics after inlining + match_range substitution
# (see compiler-lambda-inline-capture.md), so it must be rejected.
def main():
    x = 7
    selector = 1
    res = choose(x, x, selector)
    print(res)
    return

@inline
def choose(n, m, selector):
    return match_range(selector, range(0, 3), lambda n: n + m)
