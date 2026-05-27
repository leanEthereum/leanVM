# Error: duplicate parameter name in a function signature.
def main():
    pick(1, 2)
    return


def pick(value, value):
    return value + 100
