/-
  LeanVM.Guest.B1.KeccakGkr.FoldT

  `fold_shifts`' statements (`foldT`, G:2626-2652) compute `foldF`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkT
public import LeanVM.Guest.B1.KeccakGkr.FoldMath

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The pairs `q' = 2p + b` level `t` folds, in the guest's order. -/
def foldFilt (t : ℕ) : List ℕ :=
  (List.range (2 ^ (t + 1))).filter fun q' ↦
    t + 1 < 6 || shiftUsed.contains (q' / 2 + 2 ^ t * (q' % 2))

theorem foldLevelT_mem {src : ℕ → ℕ} {b : ℕ} {a : V} {t : ℕ} {q' : ℕ} (hq : q' ∈ foldFilt t)
    {k : ℕ} (hk : k < 2 ^ (6 - t) / 2) :
    let n := 2 ^ (6 - t)
    let x0 := foldVal src b t (q' / 2 * n + (2 * k + (n - 1) * (q' % 2)) % n)
    let x1 := foldVal src b t (q' / 2 * n + (2 * k + 1 + (n - 1) * (q' % 2)) % n)
    let d := b + 195 * t + 3 + 3 * ((foldFilt t).idxOf q' * (n / 2) + k)
    Stmt.atom (.mul (.n d) (.n (b + 195 * t + 2)) (.n x0)) ∈ foldLevelT src b a t ∧
      Stmt.atom (.mul (.n (d + 1)) (.n (b + 195 * t)) (.n x1)) ∈ foldLevelT src b a t ∧
      Stmt.atom (.add (.n (d + 2)) (.n d) (.n (d + 1))) ∈ foldLevelT src b a t := by
  intro n x0 x1 d
  have hz : (q', (foldFilt t).idxOf q') ∈ (foldFilt t).zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hq),
      List.getElem_idxOf]
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [foldLevelT, List.mem_append, List.mem_cons, List.mem_flatMap]
    right
    refine ⟨(q', (foldFilt t).idxOf q'), hz, k, List.mem_range.2 hk, ?_⟩
    simp [d, x0, x1, n]

theorem foldLevelT_atoms (src : ℕ → ℕ) (b : ℕ) (a : V) (t : ℕ) :
    AllAtoms (foldLevelT src b a t) := by
  intro s hs
  simp only [foldLevelT, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl) | ⟨_, _, k, _, hs⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rcases hs with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- **A level of `fold_shifts`**: from level `t`'s cells, `foldF` of level `t + 1`. -/
theorem foldLevelT_holds {src : ℕ → ℕ} {b : ℕ} {a : V} {t : ℕ} (ht : t < 6) {A : List E}
    {S : ℕ → E} (hAl : A.length = 6)
    (hall : ∀ a', Stmt.atom a' ∈ foldLevelT src b a t → a'.Holds rd σ)
    (hA : ∀ v, LoadHolds rd (σ a) t v → v = A.getD t 0)
    (hprev : ∀ p < 2 ^ t, ∀ k < 2 ^ (6 - t),
      σ (.n (foldVal src b t (p * 2 ^ (6 - t) + k))) = foldF A S t p k) :
    ∀ q' ∈ foldFilt t, ∀ k < 2 ^ (5 - t),
      σ (.n (foldVal src b (t + 1) ((q' / 2 + 2 ^ t * (q' % 2)) * 2 ^ (5 - t) + k))) =
        foldF A S (t + 1) (q' / 2 + 2 ^ t * (q' % 2)) k := by
  intro q' hq k hk
  have hq2 : q' < 2 ^ (t + 1) := List.mem_range.1 (List.mem_filter.1 hq).1
  have hn2 : 2 ^ (6 - t) / 2 = 2 ^ (5 - t) := by interval_cases t <;> rfl
  obtain ⟨m1, m2, m3⟩ := foldLevelT_mem (src := src) (b := b) (a := a) hq (k := k) (by rwa [hn2])
  have a1 := hall _ m1
  have a2 := hall _ m2
  have a3 := hall _ m3
  have lB := hall (.load (.n (b + 195 * t)) a t) (by simp [foldLevelT])
  have c1 := hall (.const (.n (b + 195 * t + 1)) (word 1 0)) (by simp [foldLevelT])
  have e2 := hall (.add (.n (b + 195 * t + 2)) (.n (b + 195 * t + 1)) (.n (b + 195 * t)))
    (by simp [foldLevelT])
  simp only [Atom.Holds] at a1 a2 a3 lB c1 e2
  have hp : q' / 2 < 2 ^ t := by rw [pow_succ] at hq2; omega
  have hb : q' % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hpos : foldVal.foldPos' t (q' / 2 + 2 ^ t * (q' % 2)) = (foldFilt t).idxOf q' := by
    unfold foldVal.foldPos' foldFilt
    congr 1
    interval_cases t <;> omega
  have hv : foldVal src b (t + 1) ((q' / 2 + 2 ^ t * (q' % 2)) * 2 ^ (5 - t) + k) =
      b + 195 * t + 3 + 3 * ((foldFilt t).idxOf q' * (2 ^ (6 - t) / 2) + k) + 2 := by
    have hm0 : 0 < 2 ^ (5 - t) := by positivity
    have hd : ((q' / 2 + 2 ^ t * (q' % 2)) * 2 ^ (5 - t) + k) / 2 ^ (5 - t) =
        q' / 2 + 2 ^ t * (q' % 2) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm0, Nat.div_eq_of_lt hk, zero_add]
    have hm : ((q' / 2 + 2 ^ t * (q' % 2)) * 2 ^ (5 - t) + k) % 2 ^ (5 - t) = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    simp only [foldVal, hn2, hd, hm, hpos]
  rw [hv, a3, a2, a1, e2, c1, word_one, hA _ lB]
  have hx0 := hprev (q' / 2) hp ((2 * k + (2 ^ (6 - t) - 1) * (q' % 2)) % 2 ^ (6 - t))
    (Nat.mod_lt _ (by positivity))
  have hx1 := hprev (q' / 2) hp ((2 * k + 1 + (2 ^ (6 - t) - 1) * (q' % 2)) % 2 ^ (6 - t))
    (Nat.mod_lt _ (by positivity))
  rw [hx0, hx1, foldF_succ A hAl S ht hp hb hk]

/-- **`fold_shifts`** (G:2638-2652): the used shifts `Σ_z V[z]·eq(a, z + r)`. -/
theorem foldT_holds {src : ℕ → ℕ} {b : ℕ} {a : V} {A : List E} {S : ℕ → E} (hAl : A.length = 6)
    (hA : ∀ t < 6, ∀ v, LoadHolds rd (σ a) t v → v = A.getD t 0)
    (hsrc : ∀ j < 64, σ (.n (src j)) = S j) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (foldT src b a) next kret) :
    (∀ r ∈ shiftUsed, σ (.n (foldVal src b 6 r)) = ∑ z ∈ range 64, S z * eqAt A ((z + r) % 64)) ∧
      next := by
  rw [foldT, holdsList_range_flatten _ _ (fun t ↦ by
    unfold foldLevelT
    rw [noRetList_append]
    simp only [Stmt.noRetList, Stmt.noRet, Bool.true_and]
    induction ((List.range (2 ^ (t + 1))).filter _).zipIdx with
    | nil => rfl
    | cons x xs ih =>
      rw [List.flatMap_cons, noRetList_append, ih, Bool.and_true]
      induction (List.range (2 ^ (6 - t) / 2)) with
      | nil => rfl
      | cons y ys ih' => rw [List.flatMap_cons, noRetList_append, ih']; rfl)] at h
  obtain ⟨hlv, hn⟩ := h
  have hall : ∀ t < 6, ∀ a', Stmt.atom a' ∈ foldLevelT src b a t → a'.Holds rd σ := fun t ht ↦
    ((holdsList_atoms (foldLevelT_atoms src b a t) True kret).1 (hlv t ht)).1
  have lev : ∀ t ≤ 5, ∀ p < 2 ^ t, ∀ k < 2 ^ (6 - t),
      σ (.n (foldVal src b t (p * 2 ^ (6 - t) + k))) = foldF A S t p k := by
    intro t
    induction t with
    | zero =>
      intro _ p hp k hk
      obtain rfl : p = 0 := by simpa using hp
      simp only [foldVal, zero_mul, zero_add]
      rw [hsrc k (by simpa using hk), foldF_zero A S (by simpa using hk)]
    | succ t ih =>
      intro ht p hp k hk
      have hstep := foldLevelT_holds (src := src) (b := b) (a := a) (t := t) (by omega) hAl
        (hall t (by omega)) (hA t (by omega)) (ih (by omega))
      have hq : (p % 2 ^ t * 2 + p / 2 ^ t) ∈ foldFilt t := by
        simp only [foldFilt, List.mem_filter, List.mem_range]
        refine ⟨?_, by simp [show t + 1 < 6 by omega]⟩
        rw [pow_succ] at hp ⊢
        have := Nat.mod_lt p (show 0 < 2 ^ t by positivity)
        have : p / 2 ^ t < 2 := Nat.div_lt_of_lt_mul hp
        omega
      have e := hstep _ hq k (by rwa [show 6 - (t + 1) = 5 - t by omega] at hk)
      have hpq : (p % 2 ^ t * 2 + p / 2 ^ t) / 2 + 2 ^ t * ((p % 2 ^ t * 2 + p / 2 ^ t) % 2) = p := by
        rw [pow_succ] at hp
        have : p / 2 ^ t < 2 := Nat.div_lt_of_lt_mul hp
        have h1 : (p % 2 ^ t * 2 + p / 2 ^ t) / 2 = p % 2 ^ t :=
          (fun X Y (hY : Y < 2) ↦ by omega : ∀ X Y : ℕ, Y < 2 → (X * 2 + Y) / 2 = X) _ _ this
        have h2 : (p % 2 ^ t * 2 + p / 2 ^ t) % 2 = p / 2 ^ t :=
          (fun X Y (hY : Y < 2) ↦ by omega : ∀ X Y : ℕ, Y < 2 → (X * 2 + Y) % 2 = Y) _ _ this
        rw [h1, h2, Nat.add_comm, Nat.div_add_mod]
      rw [hpq, show 5 - t = 6 - (t + 1) by omega] at e
      exact e
  refine ⟨fun r hr ↦ ?_, hn⟩
  have hr64 : r < 64 := (show ∀ r ∈ shiftUsed, r < 64 by decide) r hr
  have hstep := foldLevelT_holds (src := src) (b := b) (a := a) (t := 5) (by omega) hAl
    (hall 5 (by omega)) (hA 5 (by omega)) (lev 5 le_rfl)
  have hq : (r % 32 * 2 + r / 32) ∈ foldFilt 5 := by
    simp only [foldFilt, List.mem_filter, List.mem_range]
    refine ⟨by omega, ?_⟩
    simp only [show ¬ (5 + 1 < 6) by omega, decide_false, Bool.false_or]
    rw [show (r % 32 * 2 + r / 32) / 2 + 2 ^ 5 * ((r % 32 * 2 + r / 32) % 2) = r by omega]
    simpa using hr
  have e := hstep _ hq 0 (by norm_num)
  rw [show (r % 32 * 2 + r / 32) / 2 + 2 ^ 5 * ((r % 32 * 2 + r / 32) % 2) = r by omega] at e
  simp only [show (5 : ℕ) - 5 = 0 from rfl, pow_zero, mul_one, add_zero] at e
  rw [e, foldF_six A hAl S hr64]

end
end LeanVM.Guest.B1.VerifySub
