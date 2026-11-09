/-
  LeanVM.Guest.B1.VerifySub.C.Lam

  `verify_sub`'s batching (G:3472-3485), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Ctab
public import LeanVM.Guest.B1.VerifySub.Lam

/-!
# The batching, honestly

`vsLamT_complete`: `λ`'s squeeze, and for the `142` batched claims their value read where it is
pooled (`vsClaimAt`: `claim_pool` or `col_eval_words`, holding `vals`), the target accumulated
with the powers `λ^(i+1)`; then `λ^143` times the outputs' claim.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier Finset

@[expose] public section

theorem vsLamT_noNe : vsLamT.all noNeB = true := by decide +kernel

theorem vsLam_notS : ∀ i < 142, Atom.load (.n (1112 + 4 * i)) (.n (vsClaimAt (vsKept i)).1)
    (vsClaimAt (vsKept i)).2 ∉ vsSL := by
  decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsLamT_good (hl : args.length = 6) :
    ∀ s ∈ vsLamT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 1007) (blk := vsLamT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsLamT_noNe s hs)] at h

theorem vsLamStep_mem {i : ℕ} (hi : i < 142) {s : Stmt} (hs : s ∈ vsLamStep i) : s ∈ vsLamT := by
  rw [vsLamT]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hs⟩))

/-- The batched claims, honestly. -/
theorem vsLam_loop (hl : args.length = 6) {vals : ℕ → E}
    (hpool : ∀ i < 142, LoadHolds rd (vsσ rd w args (.n (vsClaimAt (vsKept i)).1))
      (vsClaimAt (vsKept i)).2 (vals i))
    {C : CallRel} {kret : List E → Prop} :
    ∀ n ≤ 142, ∀ {nx : Prop}, nx →
      vsσ rd w args (.n (vsPw n)) = vsσ rd w args (.n 1111) ^ (n + 1) ∧
      vsσ rd w args (.n (vsTg n)) = vsσ rd w args (.n 1091) +
        ∑ i ∈ range n, vsσ rd w args (.n 1111) ^ (i + 1) * vals i ∧
      Stmt.HoldsList C rd (vsσ rd w args) ((List.range n).flatMap vsLamStep) nx kret := by
  have hG := vsLamT_good (rd := rd) (w := w) hl
  generalize hσ : vsσ rd w args = σ at *
  intro n
  induction n with
  | zero =>
    intro _ nx h
    refine ⟨by simp [vsPw], by simp [vsTg], h⟩
  | succ n ih =>
    intro hn nx hnx
    have hn' : n < 142 := by omega
    have g := fun s (h : s ∈ vsLamStep n) ↦ hG s (vsLamStep_mem hn' h)
    have r := good_read (w := w) (g (vsLd (1112 + 4 * n) (vsClaimAt (vsKept n)).1
      (vsClaimAt (vsKept n)).2) (by simp [vsLamStep])) (vsLam_notS n hn') (hpool n hn')
    have m1 : Good rd vsSL w σ (.mul (.n (1113 + 4 * n)) (.n (vsPw n)) (.n (1112 + 4 * n))) :=
      g (vsMul _ _ _) (by simp [vsLamStep])
    have a1 : Good rd vsSL w σ (.add (.n (1114 + 4 * n)) (.n (vsTg n)) (.n (1113 + 4 * n))) :=
      g (vsAdd _ _ _) (by simp [vsLamStep])
    have m2 : Good rd vsSL w σ (.mul (.n (1115 + 4 * n)) (.n (vsPw n)) (.n 1111)) :=
      g (vsMul _ _ _) (by simp [vsLamStep])
    have hpw : vsPw n < 1113 + 4 * n := by unfold vsPw; split <;> omega
    simp only [Good] at m1 a1 m2
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show vsPw n < 1113 + 4 * n from hpw,
      show 1112 + 4 * n < 1113 + 4 * n by omega⟩)] at m1
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show vsPw n < 1115 + 4 * n by omega,
      show 1111 < 1115 + 4 * n by omega⟩)] at m2
    obtain ⟨ep, et, -⟩ := ih (by omega) (nx := True) trivial
    have hstep : Stmt.HoldsList C rd σ (vsLamStep n) nx kret := by
      simp only [vsLamStep, Stmt.HoldsList, Stmt.Holds, vsLd, vsMul, vsAdd]
      exact ⟨r.2, m1, a1, m2, hnx⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [vsPw_succ, m2, ep]; ring
    · rw [vsTg_succ, a1, et, m1, ep, r.1, Finset.sum_range_succ]; ring
    · rw [List.range_succ, List.flatMap_append, holdsList_append]
      exact (ih (by omega) (nx := Stmt.HoldsList C rd σ ((List.range 1).flatMap
        (fun i ↦ vsLamStep (n + i))) nx kret) (by simpa using hstep)).2.2 |> fun h ↦ by
          simpa using h

set_option maxRecDepth 100000 in
/-- **The batching, honestly.** -/
theorem vsLamT_complete (hl : args.length = 6)
    (hz : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0)
    (hcap : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (754 + i)))) {vals : ℕ → E}
    (hpool : ∀ i < 142, LoadHolds rd (vsσ rd w args (.n (vsClaimAt (vsKept i)).1))
      (vsClaimAt (vsKept i)).2 (vals i))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 1679) = vsσ rd w args (.n 1111) ^ 143 ∧
      vsσ rd w args (.n 1681) = vsσ rd w args (.n 1091) +
        ∑ i ∈ range 142, vsσ rd w args (.n 1111) ^ (i + 1) * vals i +
          vsσ rd w args (.n 1111) ^ 143 * vsσ rd w args (.n 657) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsLamT next kret := by
  have hG := vsLamT_good (rd := rd) (w := w) hl
  have g1 : Good rd vsSL w (vsσ rd w args) (.mul (.n 1680) (.n 1679) (.n 657)) :=
    hG (vsMul 1680 1679 657) (by rw [vsLamT]; simp)
  have g2 : Good rd vsSL w (vsσ rd w args) (.add (.n 1681) (.n 1678) (.n 1680)) :=
    hG (vsAdd 1681 1678 1680) (by rw [vsLamT]; simp)
  simp only [Good] at g1 g2
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show 1679 < 1680 by norm_num,
    show 657 < 1680 by norm_num⟩)] at g1
  obtain ⟨ep, et, -⟩ := vsLam_loop (C := C) (kret := kret) hl hpool 142 le_rfl (nx := True)
    trivial
  rw [show vsPw 142 = 1679 from rfl] at ep
  rw [show vsTg 142 = 1678 from rfl] at et
  refine ⟨ep, by rw [g2, g1, et, ep], ?_⟩
  rw [vsLamT, holdsList_append, holdsList_append]
  refine vsSqzT_complete hl (capb := 754) (o := 1092)
    (fun s hs ↦ vs_mem_slice (n := 1007) (blk := vsLamT) (by decide +kernel)
      (by rw [vsLamT]; exact List.mem_append_left _ (List.mem_append_left _ hs))) hz hcap ?_
  refine (vsLam_loop hl hpool 142 le_rfl ?_).2.2
  simp only [vsMul, vsAdd]
  exact ⟨g1, g2, hn⟩

end
end LeanVM.Guest.B1.VerifySub
