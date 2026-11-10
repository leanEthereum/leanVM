# usage: python3 -I genstores.py > ../../LeanVM/Guest/B1/Tables/VtC/Stores.lean
# Writes vtSL, the stores (loads into older values) of verify_tables' evaluation list, in order.
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vtflat
top, flat, ctr, cend = vtflat.load()
assert cend == 5990, cend
st = []
for (k, s), c in zip(flat, ctr):
    m = re.match(r'\.atom \(\.load \(\.n (\d+)\) \(\.n (\d+)\) (\d+)\)$', s)
    if m and int(m.group(1)) < c: st.append(m.groups())
items = ',\n'.join(f'  .load (.n {d}) (.n {p}) {o}' for d, p, o in st)
print(f'''/-
  LeanVM.Guest.B1.Tables.VtC.Stores

  The stores of `verify_tables`' evaluation list (generated: scripts/b1c-vt/genstores.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Flat

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The {len(st)} stores of `vtEvL`, in order. -/
def vtSL : List Atom := [
{items}]

set_option maxRecDepth 100000 in
/-- The counter `storesOf` carries stays unevaluated over long runs without loads: the kernel's
recursion goes deep (as `CoreNames`' checks). -/
theorem vt_stores : storesOf 20 vtEvL = vtSL := by decide +kernel

end
end LeanVM.Guest.B1.Tables''')
