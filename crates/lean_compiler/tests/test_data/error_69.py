# Error: a `Const` function parameter cannot be used as an array read base.
def main():
    peek(7)
    return

def peek(arr: Const):
    x = arr[0]
    return
