/-
  LeanVM.Guest.Lift.OsCallees

  `open_stacked`'s callees complete in the uniform placed form, on the regions they load:
  `CompleteRelRegD`, from each callee's `Rel`-level meaning and a kernel check of its body.
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Opening.Fold
public import LeanVM.Guest.B1.Opening.OodPointHi
public import LeanVM.Guest.B1.Opening.FinalMessage
public import LeanVM.Guest.B1.Opening.RowWeights
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Eq.FoldFinal
public import LeanVM.Guest.B1.Bits.AssertCanonical
public import LeanVM.Guest.B1.Bits.Grind

/-!
# `open_stacked`'s callees, placed on their regions

**The form.** `CompleteRelRegD fs cert k f Pre Reg`: for arguments whose loaded words lie in the
caller's words (`Reg args (RegionL Lin)`), and a precondition `Pre` on every memory defined below
`2^k` holding them, `f` is complete placed (`CompleteAtD`) returning `rets`. `RegPtrs spec`: for
each `(j, n) ∈ spec`, the `n` words from argument `j`'s pointer lie in the region.

**The lift** (`completeRelRegD_of_iff`): a function whose body is a leaf (atoms, branches, arms;
nothing placed) loading only `param j` at offsets below `n`, `(j, n) ∈ spec` (`specLoad`), its
parameters `.n 0, .n 1, …` at the spec's indices (`LeafSpecOk`, a kernel check), and whose
relation is its meaning `Pre`, is `CompleteRelRegD … Pre (RegPtrs spec)`: its loads lie in the
caller's words, so `Lift.completeAtD_of_relIn` places it.

**The callees** (`OsCalleesRegD`, `osCalleesRegD_holds`): `opening_fold`, `assert_canonical`,
`grind_check__L17`, `opening_ood_point__L{n}`, `opening_final_message__L{n}`,
`opening_row_weights__L4_L0`/`__L6_L1`, `verify_merkle_cap__L{D}`, `fold_final_msg__L{n}`, with
their meanings (B1's `*_holds`) and the specs B1-b gave. `decode_query_windows`, which writes its own
frame run, is not pure and has its own form (`QwDecodeAtD`, `B1/Bits/QueryWindowsAt.lean`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.Lift (anyAtom)

@[expose] public section

/-- **Complete placed, on the regions the arguments' pointers load.** -/
def CompleteRelRegD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (Reg : List E → (ℕ → Prop) → Prop) : Prop :=
  ∀ args rets Lin, Reg args (RegionL Lin) → (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtD fs cert k f Lin args (Returns rets)

/-- The callee's loads: from argument `j`'s pointer, offsets below `n`, for each `(j, n) ∈ spec`. -/
def RegPtrs (spec : List (ℕ × ℕ)) (args : List E) (R : ℕ → Prop) : Prop :=
  ∀ p ∈ spec, ∀ t < p.2, ∃ i, (args.getD p.1 0).limb 0 * addressOfIndex t = addressOfIndex i ∧ R i

/-- A load of parameter `.n j` at an offset below `n`, `(j, n) ∈ spec`; no other load. -/
def specLoad (spec : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p off => spec.any fun q => decide (p = .n q.1) && decide (off < q.2)
  | _ => true

/-- **The kernel's check of a callee**: found, its parameters `.n j` at the spec's indices, its body
a leaf loading as the spec says. -/
def LeafSpecOk (f : String) (spec : List (ℕ × ℕ)) : Prop :=
  ∃ fn, coreProgram.find? f = some fn ∧ (∀ q ∈ spec, fn.params[q.1]? = some (.n q.1)) ∧
    Lift.Stmt.leafOkList (specLoad spec) fn.body = true

theorem loads_spec {spec : List (ℕ × ℕ)} {σ : Val} {es : List Ev}
    (h : ∀ e ∈ es, Lift.EvLeafOk (specLoad spec) e) :
    ∀ A ∈ loadAddrs σ es, ∃ q ∈ spec, ∃ off < q.2, A = (σ (.n q.1)).limb 0 * addressOfIndex
        off := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      simp only [Lift.EvLeafOk, specLoad, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨q, hq, rfl, hoff⟩ := hok
      exact ⟨q, hq, off, hoff, hea.symm⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A leaf callee whose relation is its meaning, placed on its regions.** -/
theorem completeRelRegD_of_iff {f : String} {spec : List (ℕ × ℕ)}
    {Pre : Reader → List E → List E → Prop} (hok : LeafSpecOk f spec)
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ Pre rd args rets) (k : ℕ) :
    CompleteRelRegD fs cert k f Pre (RegPtrs spec) := by
  obtain ⟨fn, hf, hpar, hleaf⟩ := hok
  intro args rets Lin hreg hpre
  refine Lift.completeAtD_of_relIn (Lift.pureIn_of_leafOk hf hleaf) (List.mem_singleton_self _)
    fun rd hl hL => Lift.relIn_of_leaf hf hleaf (fun σ es vs hp hw A hA => ?_)
      ((hiff rd args rets).mpr (hpre rd hl hL))
  have hall := Lift.walk_leafOk (σ := σ) fn.body hleaf
  rw [hw] at hall
  obtain ⟨q, hq, off, hoff, rfl⟩ := loads_spec hall A hA
  have hσ : σ (.n q.1) = args.getD q.1 0 := by
    have h1 := hpar q hq
    have h2 : (fn.params.map σ)[q.1]? = args[q.1]? := by rw [hp]
    rw [List.getElem?_map, h1] at h2
    simp only [Option.map_some] at h2
    rw [List.getD_eq_getElem?_getD, ← h2]
    rfl
  rw [hσ]
  exact hreg q hq off hoff

/-! ## The callees -/

/-- `opening_fold`'s loads: the two words at the cursor (argument 7). -/
def foldSpec : List (ℕ × ℕ) := [(7, 2)]

/-- `opening_ood_point__L{n}`'s: the `n` coordinates at `point` (argument 13). -/
def oodSpec (n : ℕ) : List (ℕ × ℕ) := [(13, n)]

/-- `opening_final_message__L{n}`'s: `n + 1` words at the cursor (7), `n` at `out` (8). -/
def finalMsgSpec (n : ℕ) : List (ℕ × ℕ) := [(7, n + 1), (8, n)]

/-- `opening_row_weights__L{f}_L{r}`'s: `f` words at `point` (0), the two factors at `out` (1). -/
def rowWeightsSpec (f : ℕ) : List (ℕ × ℕ) := [(0, f), (1, 2 ^ rwLo f + 2 ^ (f - rwLo f))]

/-- `verify_merkle_cap__L{D}`'s: the cap's `2^(D+2)` cells (0), the `2^D` flags (1). -/
def merkleCapSpec (D : ℕ) : List (ℕ × ℕ) := [(0, 2 ^ (D + 2)), (1, 2 ^ D)]

/-- `fold_final_msg__L{n}`'s: the `2^n` message words (0), the `n` coordinates (1). -/
def foldFinalSpec (n : ℕ) : List (ℕ × ℕ) := [(0, 2 ^ n), (1, n)]

/-- **`open_stacked`'s pure callees, placed on their regions.** -/
structure OsCalleesRegD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop where
  fold : CompleteRelRegD fs cert k "opening_fold" MeaningOpeningFold (RegPtrs foldSpec)
  canonical : CompleteRelRegD fs cert k "assert_canonical"
    (fun _ args rets => MeaningAssertCanonical args rets) (RegPtrs [])
  grind : CompleteRelRegD fs cert k "grind_check__L17"
    (fun _ args rets => MeaningGrindCheck 17 args rets) (RegPtrs [])
  ood : ∀ p ∈ oodPointNamesAll, CompleteRelRegD fs cert k p.1 (MeaningOpeningOodPoint p.2)
    (RegPtrs (oodSpec p.2))
  finalMsg : ∀ p ∈ finalMessageNames, CompleteRelRegD fs cert k p.1
    (MeaningOpeningFinalMessage p.2) (RegPtrs (finalMsgSpec p.2))
  rowWeights4 : CompleteRelRegD fs cert k "opening_row_weights__L4_L0" (MeaningOpeningRowWeights 4 0)
    (RegPtrs (rowWeightsSpec 4))
  rowWeights6 : CompleteRelRegD fs cert k "opening_row_weights__L6_L1" (MeaningOpeningRowWeights 6 1)
    (RegPtrs (rowWeightsSpec 6))
  merkleCap : ∀ p ∈ merkleCapNames, CompleteRelRegD fs cert k p.1 (MeaningVerifyMerkleCap p.2)
    (RegPtrs (merkleCapSpec p.2))
  foldFinal : ∀ p ∈ foldFinalMsgNames, CompleteRelRegD fs cert k p.1 (MeaningFoldFinalMsg p.2)
    (RegPtrs (foldFinalSpec p.2))

/-! ### The kernel's checks -/

/-- `LeafSpecOk`, decided. -/
noncomputable def leafSpecB (f : String) (spec : List (ℕ × ℕ)) : Bool :=
  match coreProgram.find? f with
  | some fn => (spec.all fun q => decide (fn.params[q.1]? = some (.n q.1))) &&
      Lift.Stmt.leafOkList (specLoad spec) fn.body
  | none => false

theorem leafSpecOk_of {f : String} {spec : List (ℕ × ℕ)} (h : leafSpecB f spec = true) :
    LeafSpecOk f spec := by
  unfold leafSpecB at h
  split at h
  · rename_i fn hf
    rw [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨fn, hf, fun q hq => of_decide_eq_true (h.1 q hq), h.2⟩
  · cases h

theorem leafSpecOk_all {names : List (String × ℕ)} {spec : ℕ → List (ℕ × ℕ)}
    (h : (names.all fun p => leafSpecB p.1 (spec p.2)) = true) :
    ∀ p ∈ names, LeafSpecOk p.1 (spec p.2) := fun p hp =>
  leafSpecOk_of (List.all_eq_true.mp h p hp)

set_option maxRecDepth 100000 in
theorem fold_leafSpec : leafSpecB "opening_fold" foldSpec = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem canonical_leafSpec : leafSpecB "assert_canonical" [] = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem grind_leafSpec : leafSpecB "grind_check__L17" [] = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ood_leafSpec : (oodPointNamesAll.all fun p => leafSpecB p.1 (oodSpec p.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem finalMsg_leafSpec :
    (finalMessageNames.all fun p => leafSpecB p.1 (finalMsgSpec p.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rowWeights4_leafSpec : leafSpecB "opening_row_weights__L4_L0" (rowWeightsSpec 4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rowWeights6_leafSpec : leafSpecB "opening_row_weights__L6_L1" (rowWeightsSpec 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem merkleCap_leafSpec :
    (merkleCapNames.all fun p => leafSpecB p.1 (merkleCapSpec p.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem foldFinal_leafSpec :
    (foldFinalMsgNames.all fun p => leafSpecB p.1 (foldFinalSpec p.2)) = true := by
  decide +kernel

/-- **`open_stacked`'s pure callees are complete, placed on their regions**, at every frame size and
certificate. -/
theorem osCalleesRegD_holds (k : ℕ) : OsCalleesRegD fs cert k where
  fold := completeRelRegD_of_iff (leafSpecOk_of fold_leafSpec) (opening_fold_holds) k
  canonical := completeRelRegD_of_iff (leafSpecOk_of canonical_leafSpec) assert_canonical_holds k
  grind := completeRelRegD_of_iff (leafSpecOk_of grind_leafSpec) grind_check_holds k
  ood p hp := completeRelRegD_of_iff (leafSpecOk_all ood_leafSpec p hp)
    (opening_ood_point_all_holds p hp) k
  finalMsg p hp := completeRelRegD_of_iff (leafSpecOk_all finalMsg_leafSpec p hp)
    (opening_final_message_holds p hp) k
  rowWeights4 := completeRelRegD_of_iff (leafSpecOk_of rowWeights4_leafSpec)
    opening_row_weights_holds.2 k
  rowWeights6 := completeRelRegD_of_iff (leafSpecOk_of rowWeights6_leafSpec)
    opening_row_weights_holds.1 k
  merkleCap p hp := completeRelRegD_of_iff (leafSpecOk_all merkleCap_leafSpec p hp)
    (verify_merkle_cap_holds p hp) k
  foldFinal p hp := completeRelRegD_of_iff (leafSpecOk_all foldFinal_leafSpec p hp)
    (fold_final_msg_holds p hp) k

end
end LeanVM.Guest.B1
