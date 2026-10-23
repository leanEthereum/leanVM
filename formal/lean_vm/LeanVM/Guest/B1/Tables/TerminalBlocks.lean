/-
  LeanVM.Guest.B1.Tables.TerminalBlocks

  `check_opening_terminal`'s segments read as equations: the slot products, each claim's block,
  the ring-switch sum.
-/

module

public import LeanVM.Guest.B1.Tables.TerminalSpec

/-!
# `check_opening_terminal`'s blocks

* `qFacs_holds`: a slot's eight factors multiply `1 + bit + point[t]` over its bits.
* `claim_pi`, `claim_lo`, `claim_q`: claim `j`'s block adds `λ_j · low · selector` to the running
  sum, `low` read from the claim's chain at its length (`pi_eq` for the public input), the length
  checked against the column's log.
* `rs_sum`: the ring switch's `Σ c_k · row_k`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## The slot products -/

theorem qFac_holds (t : ℕ) (bit : Bool) (prev : Option ℕ) (c : ℕ)
    (h : Stmt.HoldsList C rd σ (qFac t bit prev c).1 True kret) :
    ∃ y, LoadHolds rd (σ (.n 13)) t y ∧
      σ (.n (qFac t bit prev c).2.1) = (prev.elim 1 fun q => σ (.n q)) * (1 + bitE bit + y) := by
  cases bit <;> cases prev <;>
    simp only [qFac, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.cons_append, List.nil_append,
      and_true, Bool.false_eq_true, ↓reduceIte, word_one, bitE, Option.elim, one_mul] at h ⊢
  · obtain ⟨c0, l1, a2⟩ := h
    exact ⟨_, l1, by rw [a2, c0, add_zero]⟩
  · obtain ⟨c0, l1, a2, m⟩ := h
    exact ⟨_, l1, by rw [m, a2, c0, add_zero]⟩
  · exact ⟨_, h, by rw [e_add_self, zero_add]⟩
  · obtain ⟨l, m⟩ := h
    exact ⟨_, l, by rw [m, e_add_self, zero_add]⟩

theorem qFac_noRet (t : ℕ) (bit : Bool) (prev : Option ℕ) (c : ℕ) :
    Stmt.noRetList (qFac t bit prev c).1 = true := by
  cases bit <;> cases prev <;> rfl

theorem noRetList_app (a b : List Stmt) :
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b) := by
  induction a with
  | nil => simp [Stmt.noRetList]
  | cons s a ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

theorem qFacs_noRet (slot : ℕ) : ∀ (n : ℕ) (prev : Option ℕ) (c : ℕ),
    Stmt.noRetList (qFacs slot n prev c).1 = true
  | 0, _, _ => rfl
  | n + 1, prev, c => by
    simp only [qFacs]
    rw [noRetList_app, qFac_noRet, qFacs_noRet slot n]
    rfl

/-- **A slot's equality** (G:2048-2050): the factors from `8 - n` multiply the product so far. -/
theorem qFacs_holds (slot : ℕ) : ∀ (n : ℕ) (prev : Option ℕ) (c : ℕ), n ≤ 8 →
    (n < 8 → prev.isSome) →
    Stmt.HoldsList C rd σ (qFacs slot n prev c).1 True kret →
    ∃ ys : ℕ → E, (∀ t, 8 - n ≤ t → t < 8 → LoadHolds rd (σ (.n 13)) t (ys t)) ∧
      σ (.n (qFacs slot n prev c).2.1) = (prev.elim 1 fun q => σ (.n q)) *
        ∏ t ∈ Finset.Ico (8 - n) 8, (1 + bitE (slot.testBit t) + ys t)
  | 0, prev, c, _, hp, _ => by
    obtain ⟨q, rfl⟩ := Option.isSome_iff_exists.mp (hp (by omega))
    exact ⟨fun _ => 0, fun t h1 h2 => absurd h2 (by omega), by simp [qFacs]⟩
  | n + 1, prev, c, hn, _, h => by
    simp only [qFacs] at h ⊢
    rw [holdsList_append, holdsList_noRet _ (qFac_noRet _ _ _ _)] at h
    obtain ⟨y, ly, hv⟩ := qFac_holds _ _ _ _ h.1
    obtain ⟨ys, hys, hs⟩ := qFacs_holds slot n _ _ (by omega) (fun _ => rfl) h.2
    refine ⟨fun t => if t = 8 - (n + 1) then y else ys t, fun t h1 h2 => ?_, ?_⟩
    · dsimp only
      by_cases ht : t = 8 - (n + 1)
      · rw [ite_pos' ht, ht]; exact ly
      · rw [ite_neg' ht]; exact hys t (by omega) h2
    · have hn' : n ≤ 7 := by omega
      have hI : Finset.Ico (8 - (n + 1)) 8 = insert (8 - (n + 1)) (Finset.Ico (8 - n) 8) := by
        refine Finset.ext fun t => ?_
        simp only [Finset.mem_Ico, Finset.mem_insert]
        constructor
        · intro h; omega
        · intro h; omega
      rw [hs, Option.elim, hv, hI, Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]
      dsimp only
      rw [ite_pos' rfl, mul_assoc]
      congr 2
      exact Finset.prod_congr rfl fun t ht => by
        rw [ite_neg' (by simp only [Finset.mem_Ico] at ht; omega)]

/-! ## The claims -/

/-- A public-input claim's block (G:2041-2043, 2053-2056). -/
theorem claim_pi {j : ℕ} (hk : claimKind j = 3) (h : Stmt.HoldsList C rd σ (claimBlk j) True kret) :
    LoadHolds rd (σ (.n 10)) (claimCol j) (σ (.n 5)) ∧
      ∃ lam, LoadHolds rd (σ (.n 8)) j lam ∧
        σ (.n (claimV.getD j 0 + 4)) =
          σ (.n (claimAcc j)) + lam * σ (.n 35) * σ (.n (selV (claimCol j))) := by
  simp only [claimBlk, hk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨lc, ae, ll, m2, m3, a4⟩ := h
  rw [← e_add_eq_zero_iff.mp ae] at lc
  exact ⟨lc, _, ll, by rw [a4, m3, m2]⟩

/-- A claim's block on the bus point or the table point (G:2044-2047, 2053-2056). -/
theorem claim_lo {j : ℕ} (hk : claimKind j = 0 ∨ claimKind j = 1)
    (h : Stmt.HoldsList C rd σ (claimBlk j) True kret) :
    ∃ cp low lam, LoadHolds rd (σ (.n 7)) j cp ∧
      LoadHolds rd (σ (.n (if claimKind j = 0 then 17 else 19)) * cp) 0 low ∧
      LoadHolds rd (σ (.n 10)) (claimCol j) cp ∧ LoadHolds rd (σ (.n 8)) j lam ∧
      σ (.n (claimV.getD j 0 + 7)) =
        σ (.n (claimAcc j)) + lam * low * σ (.n (selV (claimCol j))) := by
  have h3 : claimKind j ≠ 3 := by omega
  have h2 : claimKind j ≠ 2 := by omega
  simp only [claimBlk, h3, h2, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    and_true] at h
  obtain ⟨lc, m1, ll, lk, ae, lm, m5, m6, a7⟩ := h
  rw [m1] at ll
  rw [← e_add_eq_zero_iff.mp ae] at lk
  exact ⟨_, _, _, lc, ll, lk, lm, by rw [a7, m6, m5]⟩

/-- A limb's claim block (G:2048-2056). -/
theorem claim_q {j : ℕ} (hk : claimKind j = 2) (h : Stmt.HoldsList C rd σ (claimBlk j) True kret) :
    ∃ (cp low lam : E) (ys : ℕ → E), LoadHolds rd (σ (.n 7)) j cp ∧
      (∀ t < 8, LoadHolds rd (σ (.n 13)) t (ys t)) ∧
      LoadHolds rd (σ (.n 21) * cp) 0 low ∧ LoadHolds rd (σ (.n 10)) 5 (cp * gen ^ 8) ∧
      LoadHolds rd (σ (.n 8)) j lam ∧
      σ (.n ((qFacs (claimSlot j) 8 none (claimV.getD j 0 + 1)).2.2 + 9)) =
        σ (.n (claimAcc j)) + lam * ((∏ t ∈ Finset.range 8,
          (1 + bitE ((claimSlot j).testBit t) + ys t)) * low) * σ (.n (selV 5)) := by
  simp only [claimBlk, hk, ↓reduceIte] at h
  obtain ⟨lc, h⟩ := h
  simp only [List.append_eq] at h
  rw [holdsList_append, holdsList_noRet _ (qFacs_noRet _ _ _ _)] at h
  obtain ⟨hq, h⟩ := h
  obtain ⟨ys, hys, hprod⟩ :=
    qFacs_holds (claimSlot j) 8 none _ le_rfl (fun h => absurd h (by omega)) hq
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_g8] at h
  obtain ⟨mu, lu, m2, c3, m4, l5, ae, l6, m7, m8, a9⟩ := h
  rw [mu] at lu
  rw [← e_add_eq_zero_iff.mp ae, m4, c3] at l5
  refine ⟨_, _, _, ys, lc, fun t ht => hys t (by omega) ht, lu, l5, l6, ?_⟩
  rw [a9, m8, m7, m2, hprod]
  simp [Option.elim]

/-! ## The ring switch -/

/-- `Σ c_k · row_k` (G:2063-2065). -/
theorem rs_sum (h : ∀ k < 64, Stmt.HoldsList C rd σ (rsBlk k) True kret) {c r : ℕ → E}
    (hc : ∀ k < 64, LoadHolds rd (σ (.n 12)) k (c k))
    (hr : ∀ k < 64, LoadHolds rd (σ (.n 1825)) k (r k)) :
    σ (.n 2080) = ∑ k ∈ Finset.range 64, c k * r k := by
  have key : ∀ k < 64, σ (.n (if k = 0 then 1828 else 1828 + 4 * k)) =
      ∑ i ∈ Finset.range (k + 1), c i * r i := by
    intro k hk
    induction k with
    | zero =>
      have h0 := h 0 (by omega)
      simp only [rsBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
      obtain ⟨l1, l2, m⟩ := h0
      rw [ite_pos' rfl, m, loadHolds_unique l1 (hc 0 (by omega)),
        loadHolds_unique l2 (hr 0 (by omega)), Finset.sum_range_one]
    | succ k ih =>
      have ih' := ih (by omega)
      have h1 := h (k + 1) hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp only [rsBlk, Nat.reduceAdd, Nat.reduceMul, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true, Nat.one_ne_zero] at h1 ih'
        obtain ⟨l1, l2, m, a⟩ := h1
        show σ (.n 1832) = _
        rw [a, m, loadHolds_unique l1 (hc 1 hk), loadHolds_unique l2 (hr 1 hk),
          Finset.sum_range_succ, ih']
      · have n1 : k + 1 ≠ 1 := by omega
        have n0 : k ≠ 0 := by omega
        simp only [rsBlk, Nat.add_one_ne_zero, n1, n0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds, and_true] at h1 ih'
        obtain ⟨l1, l2, m, a⟩ := h1
        rw [show 1824 + 4 * (k + 1) = 1828 + 4 * k by omega] at a
        rw [ite_neg' (Nat.add_one_ne_zero k), a, m, loadHolds_unique l1 (hc (k + 1) hk),
          loadHolds_unique l2 (hr (k + 1) hk), Finset.sum_range_succ, ih']
  have := key 63 (by omega)
  simpa using this

end

end
end LeanVM.Guest.B1
