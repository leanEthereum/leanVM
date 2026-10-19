/-
  LeanVM.Guest.B1.Whir.CapAt

  `verify_merkle_cap` placed: pure, so complete in the uniform form from its relation.
-/

module

public import LeanVM.Guest.B1.Whir.Cap
public import LeanVM.Guest.B1.Uniform

/-!
# `verify_merkle_cap`, placed (TRIAGE #29, #30)

`verify_merkle_cap__L{D}` and its loop helper allocate nothing and call only each other
(`vmc_pure`), so its completeness on every memory holding the caller's words lifts to the
uniform form (`completeAt_of_rel_pure`): `VmcCompleteAt`, at its five depths.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

theorem vmc_pure_two {f g : String} {fn gn : Fn} (hf : coreProgram.find? f = some fn)
    (hg : coreProgram.find? g = some gn) (hb1 : Stmt.pureList [f, g] fn.body = true)
    (hb2 : Stmt.pureList [f, g] gn.body = true) : coreProgram.PureIn [f, g] := by
  intro h hh hn hfn
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hh
  rcases hh with rfl | rfl
  · rw [hf, Option.some.injEq] at hfn; subst hfn; exact hb1
  · rw [hg, Option.some.injEq] at hfn; subst hfn; exact hb2

/-- **`verify_merkle_cap` of depth `D`, placed**: on every layout `Lin` of the caller's words on
which it means `rets`, it returns them and no buffer. -/
def VmcCompleteAt (fs : String → ℕ) (cert : String → V → ℕ) (k D : ℕ) (name : String) : Prop :=
  ∀ (Lin : Main.Layout) (cap flags : E) (rets : List E),
    (∀ rd, MemL rd Lin → MeaningVerifyMerkleCap D rd [cap, flags] rets) →
      CompleteAt fs cert k name Lin [cap, flags] (Returns rets)

theorem vmc_completeAt {fs : String → ℕ} {cert : String → V → ℕ} {k D : ℕ} {name loop : String}
    (hS : coreProgram.PureIn [name, loop])
    (hiff : ∀ rd args rets, coreProgram.Rel rd name args rets ↔ MeaningVerifyMerkleCap D rd args rets) :
    VmcCompleteAt fs cert k D name := fun _ _ _ _ h =>
  completeAt_of_rel_pure hS (by simp) (fun rd hL => (hiff rd _ _).mpr (h rd hL)) k

set_option maxRecDepth 100000 in
theorem vmc_completeAt_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 4 "verify_merkle_cap__L4" :=
  vmc_completeAt (loop := "__loop454")
    (vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L4") (f := Data.core674) (j := 674)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop454") (f := Data.core1006) (j := 1006)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)) verify_merkle_cap_L4_iff

set_option maxRecDepth 100000 in
theorem vmc_completeAt_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 5 "verify_merkle_cap__L5" :=
  vmc_completeAt (loop := "__loop433")
    (vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L5") (f := Data.core586) (j := 586)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop433") (f := Data.core978) (j := 978)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)) verify_merkle_cap_L5_iff

set_option maxRecDepth 100000 in
theorem vmc_completeAt_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 6 "verify_merkle_cap__L6" :=
  vmc_completeAt (loop := "__loop431")
    (vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L6") (f := Data.core583) (j := 583)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop431") (f := Data.core975) (j := 975)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)) verify_merkle_cap_L6_iff

set_option maxRecDepth 100000 in
theorem vmc_completeAt_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 7 "verify_merkle_cap__L7" :=
  vmc_completeAt (loop := "__loop456")
    (vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L7") (f := Data.core683) (j := 683)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop456") (f := Data.core1008) (j := 1008)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)) verify_merkle_cap_L7_iff

set_option maxRecDepth 100000 in
theorem vmc_completeAt_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 8 "verify_merkle_cap__L8" :=
  vmc_completeAt (loop := "__loop429")
    (vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L8") (f := Data.core579) (j := 579)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop429") (f := Data.core972) (j := 972)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)) verify_merkle_cap_L8_iff

end
end LeanVM.Guest.B1
