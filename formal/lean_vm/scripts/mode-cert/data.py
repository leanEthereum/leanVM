"""The compiled code's reader, `scripts/core-mode/compiled.py`, under the name the mode walk's scripts import."""
import importlib.util, os

_spec = importlib.util.spec_from_file_location(
    'compiled', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'core-mode', 'compiled.py'))
_m = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_m)
load, HERE, LEAN_VM, ROOT, STATEMENT = _m.load, _m.HERE, _m.LEAN_VM, _m.ROOT, _m.STATEMENT
