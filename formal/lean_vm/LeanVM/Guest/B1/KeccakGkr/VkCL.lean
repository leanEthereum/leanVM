/-
  LeanVM.Guest.B1.KeccakGkr.VkCL

  `verify_keccak`'s honest valuation on a memory holding its layout: the head and the first
  claim's record.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCK

/-!
# The head and the first record, on the layout

`D.val rd B …`: `verify_keccak`'s honest valuation (`vkσ`) at its arguments `D.args …`, the oracle
`D.w B curE`. `D.Mem rd …`: the memory holds the buffers, the caller's words and the layers'
buffers. `head_first`: there, the head and the first claim's record hold, and the values the rest
reads are the honest ones.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public noncomputable section

namespace VkData

variable (D : VkData)

/-- `verify_keccak`'s arguments. -/
def args (curE chiE olE zvE slE : ℕ) : List E :=
  D.f ++ [ptr curE, gen ^ D.τ, ptr chiE, ptr olE, ptr zvE, ptr slE]

/-- **The honest valuation.** -/
def val (rd : Reader) (B curE chiE olE zvE slE : ℕ) : Val :=
  vkσ rd (D.w B curE) (D.args curE chiE olE zvE slE)

/-- The memory holds the buffers, the caller's words and the layers' buffers. -/
structure Mem (rd : Reader) (B curE chiE olE zvE slE : ℕ) (ls : ℕ → ℕ) : Prop where
  own : MemL rd (bufL B D.sizes (D.own B ls))
  lin : MemL rd (D.lin curE chiE olE zvE slE)
  lay : ∀ s < 12, MemL rd (layerBufs (D.layer s) (firstOf s) (ptr (curE + D.lcur s)) (ls s))

variable {D}

theorem op_getD (h : D.Ok) {i : ℕ} (hi : i < D.τ) : D.op.getD i 0 = D.chis.getD i 0 := by
  rw [op_eq, List.take_append_drop, List.getD_append _ _ _ _ (by rw [inst_length h]; exact hi),
    inst_getD h hi]

theorem c0_point_seg (h : D.Ok) : D.c0.point.getD (D.τ - 4) 0 = D.seg.getD 0 0 := by
  have hl := inst_length h
  simp only [c0, vkFirst]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp [hl]

theorem c0_mu_eq (h : D.Ok) : D.c0.mu = eqKernel (D.chis.take 4) := by
  have := h.1
  simp only [c0, vkFirst, inst, List.take_take, show min 4 D.τ = 4 by omega]

theorem claims_cw0 {B : ℕ} {ls : ℕ → ℕ} (h : D.Ok) {j : ℕ} (hj : j < 22) :
    (D.claims B ls).getD j 0 = (D.cw0 B).getD j 0 := by
  rw [claims, List.getD_append _ _ _ _ (by simp [cw0, c0_mu h]; omega)]

theorem alloc_goodP {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {pre : List Stmt}
    (hg : ∀ s ∈ pre, pinB s = false → GoodS rd S w σ s) :
    ∀ x ∈ pre.filterMap Main.Stmt.allocSz, σ x.1 = w x.1.idx := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  have h := hg s hs
  cases s with
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | alloc d n =>
        simp only [Main.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx
        exact h rfl
      | allocDyn d sz =>
        simp only [Main.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx
        exact h rfl
      | _ => simp [Main.Stmt.allocSz] at hsx
    | _ => simp [Main.Stmt.allocSz] at hsx
  | _ => simp [Main.Stmt.allocSz] at hsx

theorem vk_ker2 : noStoreVia [.n 5, .n 7] vkSt = true ∧
    (vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT).all (fun s ↦ !pinB s) = true := by
  decide +kernel

variable {rd : Reader} {B curE chiE olE zvE slE : ℕ} {ls : ℕ → ℕ}

theorem args_length (h : D.Ok) : (D.args curE chiE olE zvE slE).length = 11 := by
  simp [args, h.2.2.2.2.1]

/-- The facts every section starts from: the values by index, the equations, the arguments. -/
theorem val_good (h : D.Ok) :
    (∀ v, D.val rd B curE chiE olE zvE slE v = D.val rd B curE chiE olE zvE slE (.n v.idx)) ∧
    (∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w B curE) (D.val rd B curE chiE olE zvE slE) s) ∧
    (∀ i < 11, D.val rd B curE chiE olE zvE slE (.n i) = (D.args curE chiE olE zvE slE).getD i 0) :=
  ⟨fun v ↦ vkσ_idx v, fun _ hs hp ↦ vk_good (args_length h) hs hp,
    fun _ hi ↦ vk_param (args_length h) hi⟩

/-- Every statement after the head satisfies its equations. -/
theorem val_good' (h : D.Ok) {s : Stmt}
    (hs : s ∈ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT) :
    GoodS rd vkSt (D.w B curE) (D.val rd B curE chiE olE zvE slE) s :=
  (val_good h).2.1 s (by
    rw [vkT]; simp only [List.append_assoc, List.mem_append] at hs ⊢; exact Or.inr hs)
    (by have := List.all_eq_true.mp vk_ker2.2 s hs; simpa using this)

theorem val_alloc (h : D.Ok) :
    ∀ x ∈ vkAllocs, D.val rd B curE chiE olE zvE slE x.1 = D.w B curE x.1.idx := by
  have := alloc_goodP (pre := vkPre) (fun s hs hp ↦ (val_good (rd := rd) (B := B) (curE := curE)
    (chiE := chiE) (olE := olE) (zvE := zvE) (slE := slE) h).2.1 s
    (by rw [vkT_pre]; exact List.mem_append_left _ hs) hp)
  rwa [vkPre_kernel.2.2.1] at this

end VkData

end
end LeanVM.Guest.B1.VerifySub
