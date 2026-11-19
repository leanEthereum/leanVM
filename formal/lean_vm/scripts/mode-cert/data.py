"""The guest's compiled functions, hints, powers of `g` and jump table: `scripts/core-mode/compiled.py`'s reader."""
import os, sys, importlib.util
_m = sys.modules.get('compiled')
if _m is None:
    _spec = importlib.util.spec_from_file_location('compiled', os.path.join(
        os.path.dirname(os.path.abspath(__file__)), '..', 'core-mode', 'compiled.py'))
    _m = importlib.util.module_from_spec(_spec)
    sys.modules['compiled'] = _m
    _spec.loader.exec_module(_m)
load, HERE, LEAN_VM, ROOT, STATEMENT = _m.load, _m.HERE, _m.LEAN_VM, _m.ROOT, _m.STATEMENT
