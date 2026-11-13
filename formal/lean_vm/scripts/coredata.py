"""The core IR as `guest-core` writes it, read back for the scripts.

`LeanVM/Guest/Data/Core.lean` lists the functions in the compiler's order (`coreFunctions`, each
`Fn.«key».core`), and function `key`'s definitions sit, in its namespace `LeanVM.Guest.Fn.«key»`, in
its pack `LeanVM/Guest/Pack/P<k>/Core.lean` (`packs.pack_of`), or, for a long function, in its own
`LeanVM/Guest/Pack/<key>/Core*.lean` (`guest-core`'s `packCount`, `ownSize`); an old snapshot may
hold them in `LeanVM/Guest/Fn/<key>/Core*.lean`.
`legacy_texts(data)` gives each function's text in the form the packed `Data/Core{k}.lean` held
before (function `j` as `core{j}`, its definitions in `namespace core{j}`), which the readers parse;
a data directory still in that form (an old snapshot) is read as it is.
"""
import re
from pathlib import Path


def keys(data):
    """The functions' stable names, in the compiler's order, from the glue `Core.lean` in `data`."""
    t = (Path(data) / 'Core.lean').read_text(encoding='utf-8')
    i = t.find('def coreFunctions')
    if i < 0:
        return None
    return re.findall(r'Fn\.«([^»]+)»\.core', t[i:t.index(' []', i)])


_PACKED = {}


def packed(data):
    """The packed functions' texts, by stable name: each one's namespace in its pack, and the pack's
    module."""
    top = Path(data).parent / 'Pack'
    if top not in _PACKED:
        out = {}
        for p in sorted(top.glob('P[0-9]*/Core.lean')):
            mod = f'LeanVM.Guest.Pack.{p.parent.name}.Core'
            for m in re.finditer(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»\n(.*?)^end LeanVM\.Guest\.Fn\.«\1»$',
                                 p.read_text(encoding='utf-8'), re.M | re.S):
                out[m.group(1)] = (m.group(2), mod)
        _PACKED[top] = out
    return _PACKED[top]


def fn_module(data, key):
    """The module holding function `key`'s definition."""
    return packed(data)[key][1] if key in packed(data) else f'LeanVM.Guest.Pack.{key}.Core'


def fn_text(data, key):
    """Function `key`'s text: its namespace in its pack, or its own files, the continuations first."""
    if key in packed(data):
        return packed(data)[key][0]
    for top in ('Pack', 'Fn'):
        d = Path(data).parent / top / key
        files = sorted(d.glob('Core*.lean'), key=lambda p: (p.stem == 'Core', int(p.stem[4:] or 0)))
        if files:
            return ''.join(p.read_text(encoding='utf-8') for p in files)
    return ''


def legacy(text, j):
    """A function's text with its definitions named as function `j`'s."""
    text = re.sub(r'^namespace core$', f'namespace core{j}', text, flags=re.M)
    text = re.sub(r'^end core$', f'end core{j}', text, flags=re.M)
    text = re.sub(r'^noncomputable def core : Core\.Fn where$', f'noncomputable def core{j} : Core.Fn where', text,
                  flags=re.M)
    return re.sub(r'^  body := core\.body$', f'  body := core{j}.body', text, flags=re.M)


def legacy_texts(data):
    """Each function's text as the packed `Data/Core{k}.lean` held it, in the compiler's order (an old
    snapshot: its files' texts)."""
    ks = keys(data)
    if ks is None or not ks:
        return [p.read_text(encoding='utf-8') for p in sorted(Path(data).glob('Core[0-9]*.lean'))]
    return [legacy(fn_text(data, k), j) for j, k in enumerate(ks)]
