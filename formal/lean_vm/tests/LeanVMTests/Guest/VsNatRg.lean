import LeanVM.Guest.B1.VsC.VsNatRg

/-!
# The ring grind at the honest context, pinned

On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.ring_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.ring_cells

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.hlow_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.hlow_nat

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.nonce_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.nonce_reads
