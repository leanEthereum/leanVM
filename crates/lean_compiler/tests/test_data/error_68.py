# Error: a `Const` function parameter cannot be used as an array write base.
def main():
    poke(7)
    return

def poke(arr: Const):
    arr[0] = 1
    return
