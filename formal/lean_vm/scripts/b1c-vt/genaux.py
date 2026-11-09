# usage: python3 -I genaux.py > ../../LeanVM/Guest/B1/Tables/VtC/RcReads.lean
# Writes vtAuxMask: the bit mask of the indices verify_tables' range checks read the memory into.
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vtflat
top, flat, ctr, cend = vtflat.load()
aux = []
for k, s in flat:
    m = re.match(r'\.atom \(\.rangeCheck \(\.n (\d+)\) \(\.n (\d+)\) \(\.n (\d+)\) \(\.n (\d+)\) \(\.n (\d+)\)\)$', s)
    if m: aux += [int(m.group(3)), int(m.group(4))]
mask = sum(1 << i for i in set(aux))
print(f'''/-
  LeanVM.Guest.B1.Tables.VtC.RcReads

  The indices `verify_tables`' range checks read the memory into, as a bit mask (generated:
  scripts/b1c-vt/genaux.py), and the kernel's checks that nothing else uses them.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Agree
public import LeanVM.Guest.B1.Tables.VtC.Flat

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Core

@[expose] public section

/-- The {len(set(aux))} indices the range checks of `vtEvL` read the memory into, as bits. -/
def vtAuxMask : ℕ := {mask}

/-- Index `i` is a range check's read. -/
def vtAux (i : ℕ) : Bool := vtAuxMask.testBit i

theorem vt_aux : ∀ i ∈ auxIdx vtEvL, vtAux i = true :=
  List.all_eq_true.mp (show (auxIdx vtEvL).all vtAux = true by decide +kernel)

theorem vt_dead : vtEvL.all (deadS vtAux) = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables''')
