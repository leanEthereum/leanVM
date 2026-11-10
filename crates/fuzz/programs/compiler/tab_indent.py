# expect: ok
# A tab-indented body: the parser must not mis-nest blocks silently.
from snark_lib import *

def main():
	x = GEN
	return
