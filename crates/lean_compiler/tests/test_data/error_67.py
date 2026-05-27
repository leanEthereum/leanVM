# Error: a `Const` function parameter cannot be reassigned as a scalar target.
def main():
    overwrite(7)
    return

def overwrite(n: Const):
    n = 1
    return
