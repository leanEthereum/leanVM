# expect: compile-error only the whole right-hand side of an assignment
# A match used directly as a return expression: only an assignment binds a match's targets, so the parser must refuse
# it with an error, not panic or bind nothing.
from snark_lib import *

T = [3, 5]


def f(y):
    return match(log(y), range(0, 2), lambda k: T[k])


def main():
    r = f(GEN)
    return
