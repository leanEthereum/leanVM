/-
  LeanVM.Guest.B1.Sig.WotsGroupComplete

  An arm of a WOTS+C group completes on the group's arms region.
-/

module

public import LeanVM.Guest.B1.Sig.WotsGroup

/-!
# A group's arm, complete

`groupArm_complete`: arm `k < 4^n` of a group from base `b` completes on `b + 6 ..< armB (4^n)`,
its valuation the arm evaluated and its tips canonical, from canonical starts; the arm is in
single-assignment form.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **An arm of a group completes.** -/
theorem groupArm_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {b k : Nat}
    (hk : k < 4 ^ n) (hB : B ≤ b + 6) (hpi : NBv B prodIn) (hei : NBv B encIn)
    (hpw : NBv B (W.power (digitSum k n))) (σ : Val) (hg : good σ)
    (hs : ∀ t < n, StartCanon σ (slotsT W fold b t) (dig k t)
      (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k))) :
    Completes C rd (b + 6) (armB W first n fold prodIn encIn b (4 ^ n))
      (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
        (armB W first n fold prodIn encIn b k)).1 σ
      (fun σ' => σ' = fwd (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
          (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1 σ ∧
        (∀ t < n, IsCanonical128 (σ' (.n (slotsT W fold b t 2)))) ∧
        SSA (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
          (armB W first n fold prodIn encIn b k)).1) := by
  have hend : armB W first n fold prodIn encIn b (k + 1) ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
    armB_mono W first n fold prodIn encIn b (by omega)
  have hgs : b + 6 ≤ groupStart fold b := by rw [groupStart_eq]; split <;> omega
  have hgsf : fold = true → b + 7 ≤ groupStart fold b := by intro hf; rw [groupStart_eq, hf]; simp
  have hpoB : B ≤ groupStart fold b + chainStride W * n := by omega
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.zero_add] at hend
    have h1 := armB_one W first n fold prodIn encIn b
    rw [armB_zero] at hs ⊢
    simp only [↓reduceIte] at hs ⊢
    obtain ⟨l1, l2, l3⟩ := arm0_lay W fold (n := n) hB
    have hR : ∀ x, WalksR (slotsT W fold b) (W.size + 1) 0 n (if fold then b + 6 + 1 else b + 6) x →
        x ≠ .n (groupStart fold b + chainStride W * n) ∧
        x ≠ .n (groupStart fold b + chainStride W * n + 1) ∧ (fold = true → x ≠ .n (b + 6)) ∧
        (0 ≠ 0 → x ≠ .n (walksT W (slotsT W fold b) first 0 W.size n 0 (if fold then b + 6 + 1 else b + 6)).2) := by
      intro x hx
      obtain ⟨j, rfl, h1, h2⟩ := l3 x hx
      refine ⟨fun e => ?_, fun e => ?_, fun hf e => ?_, fun h => absurd rfl h⟩ <;>
        simp only [V.mk.injEq, true_and] at e
      · omega
      · omega
      · have := hgsf hf; omega
    have hssa := armT_ssa (first := first) (prodIn := prodIn) (encIn := encIn) hW l1 l2 hpi hei hpw
      (show groupStart fold b + chainStride W * n ≠ groupStart fold b + chainStride W * n + 1 by omega)
      hpoB (by omega)
      (fun hf => ⟨by have := hgsf hf; omega, by have := hgsf hf; omega⟩)
      hR (fun h => absurd rfl h)
    obtain ⟨kc, ktip⟩ := armT_canon (first := first) (prodIn := prodIn) (encIn := encIn) hW hc l1 l2
      (by omega) hR hssa.1 σ hg (by simpa using hs)
    obtain ⟨σ', he, hp, hh⟩ := fwd_completes (C := C) (rd := rd) (lo := b + 6)
      (hi := armB W first n fold prodIn encIn b (4 ^ n)) hssa.1 (fun x hx => by
        rcases hssa.2 x hx with h | rfl | rfl | ⟨-, rfl⟩ | ⟨h, -⟩
        · obtain ⟨j, rfl, h1', h2'⟩ := l3 x h
          exact ⟨j, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨b + 6, le_rfl, by omega, rfl⟩
        · exact absurd rfl h) σ kc
    refine ⟨σ', he, ⟨hp, fun t ht => ?_, hssa.1⟩, hh⟩
    rw [hp]
    exact ktip t ht
  · have ha := armB_pos W first n fold prodIn encIn b hk0
    have hnext := armB_next_pos W first n fold prodIn encIn b k hk0
    have h1 : armB W first n fold prodIn encIn b 1 ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
      armB_mono W first n fold prodIn encIn b (Nat.one_le_two_pow.trans (Nat.pow_le_pow_left (by norm_num) n))
    have h1' := armB_one W first n fold prodIn encIn b
    simp only [hk0, ↓reduceIte] at hs ⊢
    obtain ⟨l1, l2, l3⟩ := armPos_lay W fold (n := n) (k := k) (a := armB W first n fold prodIn encIn b k) hB ha
    have hws2 := walksT_snd W (slotsT W fold b) first k W.size n 0
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
    have hb0 : armB W first n fold prodIn encIn b k ≤
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) := by
      split <;> omega
    have hb0f : fold = true → armB W first n fold prodIn encIn b k + 1 ≤
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) := by
      intro hf; simp [hf]
    have hwb := walkBase_le W.size k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
      (Nat.zero_le n)
    simp only [walkBase] at hwb
    have hR : ∀ x, WalksR (slotsT W fold b) W.size k n
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) x →
        x ≠ .n (groupStart fold b + chainStride W * n) ∧
        x ≠ .n (groupStart fold b + chainStride W * n + 1) ∧
        (fold = true → x ≠ .n (armB W first n fold prodIn encIn b k)) ∧
        (k ≠ 0 → x ≠ .n (walksT W (slotsT W fold b) first k W.size n 0
          (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)).2) := by
      intro x hx
      obtain ⟨j, rfl, h⟩ := l3 x hx
      refine ⟨fun e => ?_, fun e => ?_, fun hf e => ?_, fun _ e => ?_⟩ <;>
        simp only [V.mk.injEq, true_and] at e <;> rcases h with h | h
      all_goals first | omega | (have := hb0f hf; omega)
    have hssa := armT_ssa (first := first) (prodIn := prodIn) (encIn := encIn)
      (po := groupStart fold b + chainStride W * n) (eo := groupStart fold b + chainStride W * n + 1)
      (k := k) (b := armB W first n fold prodIn encIn b k) hW (by simpa [hk0] using l1)
      (by simpa [hk0] using l2) hpi hei hpw (by omega) hpoB (by omega) (fun hf => ⟨by omega, by omega⟩)
      (by simpa [hk0] using hR)
      (fun _ => ⟨by rw [hws2]; rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
        by rw [hws2]; omega, by rw [hws2]; omega, fun hf => by rw [hws2]; have := hb0f hf; omega⟩)
    obtain ⟨kc, ktip⟩ := armT_canon (first := first) (prodIn := prodIn) (encIn := encIn) hW hc
      (by simpa [hk0] using l1) (by simpa [hk0] using l2) (by omega) (by simpa [hk0] using hR) hssa.1 σ hg
      (by simpa [hk0] using hs)
    obtain ⟨σ', he, hp, hh⟩ := fwd_completes (C := C) (rd := rd) (lo := b + 6)
      (hi := armB W first n fold prodIn encIn b (4 ^ n)) hssa.1 (fun x hx => by
        rcases hssa.2 x hx with h | rfl | rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩
        · obtain ⟨j, rfl, h⟩ := l3 x (by simpa [hk0] using h)
          rcases h with h | h
          · exact ⟨j, by omega, by omega, rfl⟩
          · exact ⟨j, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by rw [hws2]; omega, by rw [hws2]; omega, rfl⟩) σ kc
    refine ⟨σ', he, ⟨hp, fun t ht => ?_, hssa.1⟩, hh⟩
    rw [hp]
    exact ktip t ht

/-- **A group's values are numbered below its end**, its digit word at `d`, its arms from `b`. -/
theorem groupD_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {fold : Bool}
    {prodIn encIn : V} {d : Nat} {pre : List Stmt} {b : Nat} (hB : B ≤ b + 6) (hdb : d ≤ b)
    (hpre : NumBelow (b + 6) (Stmt.valsList pre)) (hpi : NBv (b + 6) prodIn) (hei : NBv (b + 6) encIn)
    (hpw : ∀ k < 4 ^ n, NBv (b + 6) (W.power (digitSum k n))) :
    NumBelow (groupD W first n fold prodIn encIn d pre b).2
      (Stmt.valsList (groupD W first n fold prodIn encIn d pre b).1) := by
  have hW' := StepShape.mono hW hB
  have hend : (groupD W first n fold prodIn encIn d pre b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupD, groupArmsT]; rw [armsT_snd]; rfl
  have hge : b + 6 ≤ armB W first n fold prodIn encIn b (4 ^ n) := by
    rw [← armB_zero W first n fold prodIn encIn b]
    exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)
  have hgs : b + 6 ≤ groupStart fold b := by rw [groupStart_eq]; split <;> omega
  have h1 := armB_one W first n fold prodIn encIn b
  have h1e : armB W first n fold prodIn encIn b 1 ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
    armB_mono W first n fold prodIn encIn b (Nat.one_le_two_pow.trans (Nat.pow_le_pow_left (by norm_num) n))
  rw [hend]
  have harm : ∀ k < 4 ^ n, NumBelow (armB W first n fold prodIn encIn b (4 ^ n))
      (Stmt.valsList (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
        (armB W first n fold prodIn encIn b k)).1) := by
    intro k hk
    have hk1 : armB W first n fold prodIn encIn b (k + 1) ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
      armB_mono W first n fold prodIn encIn b (by omega)
    have hlt := armB_lt W first n fold prodIn encIn b k
    have hbase : b + 6 ≤ armB W first n fold prodIn encIn b k := by
      rw [← armB_zero W first n fold prodIn encIn b]
      exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)
    have hP1 : ∀ x, NBv (b + 6) x → ∃ j < armB W first n fold prodIn encIn b (4 ^ n), x = .n j := by
      rintro x ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨l1, l2, l3⟩ := arm0_lay W fold (n := n) (le_refl (b + 6))
      rw [armB_zero]
      have hws : (if fold then b + 6 + 1 else b + 6) + walkSum W.size 0 0 n ≤
          groupStart fold b + chainStride W * n := by
        rw [walkSum_zero_digits, chainStride_eq, groupStart_eq]
        have : n * (1 + 3 * W.size) ≤ (1 + 3 * (W.size + 1)) * n := by
          rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
        split <;> omega
      refine armT_vals hW' (by simpa using l1) (by simpa using l2) hP1 (fun x hx => ?_) ⟨?_, ?_, ?_,
        hP1 _ hpi, hP1 _ hei, hP1 _ (hpw _ hk), ?_⟩
      · obtain ⟨j, rfl, h1', h2'⟩ := l3 x (by simpa using hx)
        exact ⟨j, by omega, rfl⟩
      · exact ⟨_, by omega, rfl⟩
      · exact ⟨_, by omega, rfl⟩
      · exact ⟨_, by omega, rfl⟩
      · rw [walksT_snd, walkBase_eq]
        exact ⟨_, by omega, rfl⟩
    · have ha := armB_pos W first n fold prodIn encIn b hk0
      have hnext := armB_next_pos W first n fold prodIn encIn b k hk0
      obtain ⟨l1, l2, l3⟩ := armPos_lay W fold (n := n) (k := k) (a := armB W first n fold prodIn encIn b k)
        (le_refl (b + 6)) ha
      have hwb := walkBase_le W.size k
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
        (Nat.zero_le n)
      simp only [walkBase] at hwb
      refine armT_vals hW' (by simpa [hk0] using l1) (by simpa [hk0] using l2) hP1 (fun x hx => ?_)
        ⟨?_, ?_, ?_, hP1 _ hpi, hP1 _ hei, hP1 _ (hpw _ hk), ?_⟩
      · obtain ⟨j, rfl, h⟩ := l3 x (by simpa [hk0] using hx)
        rcases h with h | h
        · exact ⟨j, by rw [groupStart_eq] at h1 h; omega, rfl⟩
        · exact ⟨j, by omega, rfl⟩
      · exact ⟨_, by omega, rfl⟩
      · exact ⟨_, by omega, rfl⟩
      · exact ⟨_, by omega, rfl⟩
      · rw [walksT_snd]
        exact ⟨_, by omega, rfl⟩
  have hpre' := hpre.mono hge
  simp only [groupD, List.cons_append, List.append_assoc, valsList_cons, valsList_append]
  intro x hx
  simp only [hintW, rangeS, cst, Stmt.vals, Atom.vals, Hint.vals, Dest.vals, valsList_cons, valsList_nil,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | (rfl | rfl | rfl | rfl | rfl | rfl) | hx | rfl | rfl | hx
  all_goals try exact ⟨_, by omega, rfl⟩
  · exact hpre' x hx
  refine numBelow_valsArms _ (fun a ha => ?_) x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  simp only [groupArmsT] at hk ⊢
  rw [armsT_getElem]
  rw [armsT_length] at hk
  simp only [Nat.zero_add]
  exact harm k hk

/-- **A group's values are numbered below its end.** -/
theorem groupT_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {fold : Bool}
    {prodIn encIn : V} {b : Nat} (hB : B ≤ b) (hpi : NBv b prodIn) (hei : NBv b encIn)
    (hpw : ∀ j, NBv b (W.power j)) :
    NumBelow (groupT W first n fold prodIn encIn b).2 (Stmt.valsList (groupT W first n fold prodIn encIn b).1) :=
  groupD_numBelow (pre := []) hW (by omega) le_rfl (.nil _) (NBv.mono' hpi (by omega)) (NBv.mono' hei (by omega))
    (fun _ _ => NBv.mono' (hpw _) (by omega))

end
end LeanVM.Guest.B1.Sig
