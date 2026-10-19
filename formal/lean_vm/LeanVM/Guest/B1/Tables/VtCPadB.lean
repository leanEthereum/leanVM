/-
  LeanVM.Guest.B1.Tables.VtCPadB

  A dispatched `padding_weight` arm complete by a bounded tree: its frame.
-/

module

public import LeanVM.Guest.B1.Tables.VtCPad
public import LeanVM.Guest.B1.Tables.VtCSize
public import LeanVM.Guest.B1.Tables.VtCStraightB

/-!
# `padding_weight`, placed, bounded

A function whose body is straight-line with no `HeapBuf` and no callee (`vtcLeafOk`, by kernel
evaluation) has trees of its frame alone (`vtc_leaf_total_of_ok`); the 29 `padding_weight` arms
are such (`pw_leafOk`), so `pw_completeAtD` holds by a tree of `fs` of the arm (`pw_completeAtB`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A leaf's shape: found, its body straight-line then a `ret`, no `HeapBuf`, no callee. -/
noncomputable def vtcLeafOk (g : String) : Bool :=
  match coreProgram.find? g with
  | some fn => match fn.body.getLast? with
    | some (.ret _) => fn.body.dropLast.all Main.Stmt.straight &&
        (fn.body.dropLast.filterMap Main.Stmt.allocSz).isEmpty &&
        (fn.body.dropLast.filterMap Main.Stmt.callS).isEmpty
    | _ => false
  | none => false

/-- **A leaf's valid trees are its frame.** -/
theorem vtc_leaf_total_of_ok {fs : String → ℕ} {g : String} (hok : vtcLeafOk g = true) {rd : Reader}
    {t : Tree} {args rets : List E} (hn : t.name = g) (hv : t.Valid coreProgram rd args rets)
    (hbo : t.BufsOk coreProgram) : t.total fs = fs g := by
  unfold vtcLeafOk at hok
  split at hok
  · next fn hf =>
    split at hok
    · next vs hl =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
      obtain ⟨⟨hst, hna⟩, hnc⟩ := hok
      have hb : fn.body = fn.body.dropLast ++ [.ret vs] := by
        rw [← List.dropLast_append_getLast?  _ hl]
        simp
      exact vtc_leaf_total hf hb hst hna hnc hn hv hbo
    · exact absurd hok (by simp)
  · exact absurd hok (by simp)

set_option maxRecDepth 100000 in
theorem pw_leafOk : ∀ j < 29, vtcLeafOk (pwNames.getD j "") = true := by decide +kernel

theorem pw_ok (j : ℕ) (hj : j < pwNames.length) : vtcLeafOk (pwNames[j]'hj) = true := by
  have := pw_leafOk j (by simpa [pwNames] using hj)
  rwa [List.getD_eq_getElem _ _ hj] at this

/-- **A dispatched `padding_weight` arm is complete, placed, by a tree of its frame**:
`pw_completeAtD` in `CompleteAtB` form. -/
theorem pw_completeAtB {fs : String → ℕ} {cert : String → V → ℕ} (j : ℕ) (hj : j < pwNames.length)
    {k : ℕ} {Lin : Main.Layout} {zeta : E} {zs : List E} {n : ℕ} (hn : n ≤ 2 ^ j) (hzl : j ≤ zs.length)
    (hz : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd zeta zs) :
    CompleteAtB fs cert k (pwNames[j]'hj) Lin [eOfNat n, zeta]
      (Returns [paddingWeight (zs.take j) n, pwLead j n, pwRest j n]) (fs (pwNames[j]'hj)) := by
  have hok := pw_ok j hj
  refine vtc_completeAt_of_rel_lowB pure_pw (List.getElem_mem hj) k (fun rd hlow hL rd' hag =>
    pw_dispatch_complete j hj ⟨n, zs.take j, hn, rfl, by simp only [List.length_take]; omega,
      fun i hi => by
        simp only [List.length_take] at hi
        rw [List.getElem_take]
        exact loadHolds_agree hag (hz rd hlow hL i (by omega)) (addr_in_region hz hlow hL (by omega)),
      rfl⟩) fun _ _ t _ htn hv hbo => (vtc_leaf_total_of_ok hok htn hv hbo).le

/-- `pw_completeAtB` within weights: the arm's frame. -/
theorem pw_completeAtW {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ} (j : ℕ)
    (hj : j < pwNames.length) {k : ℕ} {Lin : Main.Layout} {zeta : E} {zs : List E} {n : ℕ} (hn : n ≤ 2 ^ j)
    (hzl : j ≤ zs.length) (hz : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd zeta zs) :
    Main.CompleteAtW fs cert w k (pwNames[j]'hj) Lin [eOfNat n, zeta]
      (Returns [paddingWeight (zs.take j) n, pwLead j n, pwRest j n]) (fs (pwNames[j]'hj))
      fun θ => w θ (pwNames[j]'hj) :=
  Main.CompleteAtB.toW_total (pw_completeAtB j hj hn hzl hz) fun _ _ _ _ htn hv hbo =>
    (vtc_leaf_total_of_ok (pw_ok j hj) htn hv hbo).le

end
end LeanVM.Guest.B1.VerifySub
