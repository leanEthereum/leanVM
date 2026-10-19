/-
  LeanVM.Guest.B1.Whir.CapAt

  `verify_merkle_cap` placed: pure, so complete in the uniform form from its relation.
-/

module

public import LeanVM.Guest.B1.Whir.Cap
public import LeanVM.Guest.B1.Uniform
public import LeanVM.Guest.Memory.Size

/-!
# `verify_merkle_cap`, placed (TRIAGE #29, #30)

`verify_merkle_cap__L{D}` and its loop helper allocate nothing and call only each other
(`vmc_pure`), so its completeness on every memory holding the caller's words lifts to the
uniform form (`completeAt_of_rel_pure`): `VmcCompleteAt`, at its five depths; by a bounded tree
(`VmcCompleteAtB`) given its trees' size.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL)

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
      CompleteAtD fs cert k name Lin [cap, flags] (Returns rets)

/-- `VmcCompleteAt` by trees of at most `B` words. -/
def VmcCompleteAtB (fs : String → ℕ) (cert : String → V → ℕ) (k D : ℕ) (name : String) (B : ℕ) : Prop :=
  ∀ (Lin : Main.Layout) (cap flags : E) (rets : List E),
    (∀ rd, MemL rd Lin → MeaningVerifyMerkleCap D rd [cap, flags] rets) →
      CompleteAtB fs cert k name Lin [cap, flags] (Returns rets) B

theorem vmc_completeAtB {fs : String → ℕ} {cert : String → V → ℕ} {k D : ℕ} {name loop : String}
    (hS : coreProgram.PureIn [name, loop])
    (hiff : ∀ rd args rets, coreProgram.Rel rd name args rets ↔ MeaningVerifyMerkleCap D rd args rets) {B : ℕ}
    (hB : TotalLe coreProgram fs name fun _ => B) : VmcCompleteAtB fs cert k D name B := fun _ _ _ _ h =>
  completeAt_of_rel_pureBat hS (by simp) (fun rd hL => (hiff rd _ _).mpr (h rd hL)) k
    fun rd t hn hv hb => hB rd t _ _ hn hv hb

theorem vmc_completeAt {fs : String → ℕ} {cert : String → V → ℕ} {k D : ℕ} {name loop : String}
    (hS : coreProgram.PureIn [name, loop])
    (hiff : ∀ rd args rets, coreProgram.Rel rd name args rets ↔ MeaningVerifyMerkleCap D rd args rets) :
    VmcCompleteAt fs cert k D name := fun _ _ _ _ h =>
  completeAt_of_rel_pureD hS (by simp) (fun rd hL => (hiff rd _ _).mpr (h rd hL)) k

set_option maxRecDepth 100000 in
theorem vmc_pure_L4 : coreProgram.PureIn ["verify_merkle_cap__L4", "__loop454"] :=
  vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L4") (f := Data.core674) (j := 674)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop454") (f := Data.core1006) (j := 1006)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)

theorem vmc_completeAt_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 4 "verify_merkle_cap__L4" :=
  vmc_completeAt vmc_pure_L4 verify_merkle_cap_L4_iff

theorem vmc_completeAtB_L4 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLe coreProgram fs "verify_merkle_cap__L4" fun _ => B) :
    VmcCompleteAtB fs cert k 4 "verify_merkle_cap__L4" B :=
  vmc_completeAtB vmc_pure_L4 verify_merkle_cap_L4_iff hB

set_option maxRecDepth 100000 in
theorem vmc_pure_L5 : coreProgram.PureIn ["verify_merkle_cap__L5", "__loop433"] :=
  vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L5") (f := Data.core586) (j := 586)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop433") (f := Data.core978) (j := 978)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)

theorem vmc_completeAt_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 5 "verify_merkle_cap__L5" :=
  vmc_completeAt vmc_pure_L5 verify_merkle_cap_L5_iff

theorem vmc_completeAtB_L5 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLe coreProgram fs "verify_merkle_cap__L5" fun _ => B) :
    VmcCompleteAtB fs cert k 5 "verify_merkle_cap__L5" B :=
  vmc_completeAtB vmc_pure_L5 verify_merkle_cap_L5_iff hB

set_option maxRecDepth 100000 in
theorem vmc_pure_L6 : coreProgram.PureIn ["verify_merkle_cap__L6", "__loop431"] :=
  vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L6") (f := Data.core583) (j := 583)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop431") (f := Data.core975) (j := 975)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)

theorem vmc_completeAt_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 6 "verify_merkle_cap__L6" :=
  vmc_completeAt vmc_pure_L6 verify_merkle_cap_L6_iff

theorem vmc_completeAtB_L6 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLe coreProgram fs "verify_merkle_cap__L6" fun _ => B) :
    VmcCompleteAtB fs cert k 6 "verify_merkle_cap__L6" B :=
  vmc_completeAtB vmc_pure_L6 verify_merkle_cap_L6_iff hB

set_option maxRecDepth 100000 in
theorem vmc_pure_L7 : coreProgram.PureIn ["verify_merkle_cap__L7", "__loop456"] :=
  vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L7") (f := Data.core683) (j := 683)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop456") (f := Data.core1008) (j := 1008)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)

theorem vmc_completeAt_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 7 "verify_merkle_cap__L7" :=
  vmc_completeAt vmc_pure_L7 verify_merkle_cap_L7_iff

theorem vmc_completeAtB_L7 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLe coreProgram fs "verify_merkle_cap__L7" fun _ => B) :
    VmcCompleteAtB fs cert k 7 "verify_merkle_cap__L7" B :=
  vmc_completeAtB vmc_pure_L7 verify_merkle_cap_L7_iff hB

set_option maxRecDepth 100000 in
theorem vmc_pure_L8 : coreProgram.PureIn ["verify_merkle_cap__L8", "__loop429"] :=
  vmc_pure_two (Program.find?_of_indexOf? (n := "verify_merkle_cap__L8") (f := Data.core579) (j := 579)
      (by decide +kernel) rfl) (Program.find?_of_indexOf? (n := "__loop429") (f := Data.core972) (j := 972)
      (by decide +kernel) rfl) (by decide +kernel) (by decide +kernel)

theorem vmc_completeAt_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) :
    VmcCompleteAt fs cert k 8 "verify_merkle_cap__L8" :=
  vmc_completeAt vmc_pure_L8 verify_merkle_cap_L8_iff

theorem vmc_completeAtB_L8 (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLe coreProgram fs "verify_merkle_cap__L8" fun _ => B) :
    VmcCompleteAtB fs cert k 8 "verify_merkle_cap__L8" B :=
  vmc_completeAtB vmc_pure_L8 verify_merkle_cap_L8_iff hB

end
end LeanVM.Guest.B1
