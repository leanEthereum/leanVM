/-
  LeanVM.Guest.Backend.Sound.Obl.GuestB1

  The guest's obligations with B1's theorems for the facts the analysis takes from outside.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Guest
public import LeanVM.Guest.B1.VerifySub.KnownAll
public import LeanVM.Guest.B1.Bits.Tables

/-!
# The bridge to B1

The facts `guest_obligations_of` takes beyond what remains are B1's theorems, stated over the core
program and a valuation, with no certificate:

* `expPost_B1`: `exponent_tables`' relation is the exponent table (B1-a's
  `exponent_tables_holds`);
* `vsFacts_B1`: `verify_sub`'s first `333` statements bound `dims_g[g^0]` below `g^34`
  (`VerifySub.vsDimsKnown0_holds`), its first `1545` the eight words of `kappa_base` below
  `kbBound` (`VerifySub.vsKnown_holds`, over the exponent table at its argument `4`).

`guest_obligations` is then `guest_obligations_of` with the exponent table `B1.ExpTables` as the
guest's relation `0`: every function's obligations from `RestObl` alone.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`exponent_tables` returns the exponent table** (B1-a). -/
theorem expPost_B1 : ExpPost B1.ExpTables := by
  intro rd a r h
  have := (B1.exponent_tables_holds rd a r).mp h
  match a, r, this with
  | [], [q], h => exact h.1

theorem vs_body : (coreProgram.getD vsIdx default).body = Fn.body fn% «verify_sub» := rfl

/-- **`verify_sub`'s facts** (B1-d). -/
theorem vsFacts_B1 : VsFacts B1.ExpTables := by
  intro κ L h1 h2 σ hex p hp hl
  rw [vs_body] at hl
  simp only [vsFacts, List.mem_cons, List.mem_map, List.mem_range] at hp
  rcases hp with rfl | ⟨c, hc, rfl⟩
  · exact B1.VerifySub.vsDimsKnown0_holds L h1 h2 σ hl
  · exact B1.VerifySub.vsKnown_holds L h1 h2 σ hex hl c hc

variable {κ : ℕ} {W : World κ} {X : Reader → String → List E → Prop}

/-- **The guest's obligations**, from what remains: every function of a compiled program whose
core is the guest's and whose precondition is `guestU B1.ExpTables X` has its obligations, on a
memory of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, given the obligations of the `92` functions
the analysis does not discharge (`RestObl`). -/
theorem guest_obligations (hW : W.Compiled) (hcore : W.p.map (·.core) = coreProgram)
    (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) (hU : W.U = guestU B1.ExpTables X W.L.read)
    (hrest : RestObl B1.ExpTables X) : ∀ tf ∈ W.p, W.Obligations tf :=
  guest_obligations_of hW hcore hκ hU expPost_B1 vsFacts_B1 hrest

end
end LeanVM.Guest.Backend.Obl

/-- info: 'LeanVM.Guest.Backend.Obl.guest_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Obl.guest_obligations
