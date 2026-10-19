/-
  LeanVM.Guest.B1.Tables.TerminalCClaims

  `check_opening_terminal`'s claims, complete: the slot products and the 112 claim blocks.
-/

module

public import LeanVM.Guest.B1.Tables.TerminalComplete

/-!
# The claims, complete

`qFacs_complete`: a slot's eight factors over the point's words. `c_claim_lo`, `c_claim_q`,
`c_claim_pi`: claim `j`'s block, its length checked against its column's log.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

/-- `NumBelow` of a literal block, each value by `omega`. -/
macro "nb_tac" : tactic =>
  `(tactic| (simp only [Stmt.valsList, Stmt.vals, Atom.vals, List.cons_append, List.nil_append,
      List.append_nil]; repeat' (first | exact NumBelow.nil _ | refine NumBelow.cons ⟨_, by omega, rfl⟩ ?_)))

section
variable {C : CallRel} {rd : Reader}

theorem upds_lt {σ : Val} {l : List (ℕ × E)} {lo : ℕ} (hl : ∀ p ∈ l, lo ≤ p.1) {j : ℕ} (hj : j < lo) :
    upds σ l (.n j) = σ (.n j) :=
  upds_of_not_mem σ l fun p hp => by
    have := hl p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega

/-- **One factor of a slot's equality**, complete. -/
theorem qFac_complete (t : ℕ) (bit : Bool) (prev : Option ℕ) (c : ℕ) (hc13 : 13 < c)
    (hprev : ∀ q, prev = some q → q < c) {a13 Y : E} (hY : LoadHolds rd a13 t Y) (σ : Val)
    (h13 : σ (.n 13) = a13) :
    Completes C rd c (qFac t bit prev c).2.2 (qFac t bit prev c).1 σ (fun _ => True) ∧
      NumBelow (qFac t bit prev c).2.2 (Stmt.valsList (qFac t bit prev c).1) ∧
      c < (qFac t bit prev c).2.2 ∧ (qFac t bit prev c).2.1 < (qFac t bit prev c).2.2 := by
  cases bit
  · cases prev with
    | none =>
      simp only [qFac, Bool.false_eq_true, ↓reduceIte]
      refine ⟨completes_upds [(c, word 1 0 0), (c + 1, Y), (c + 2, word 1 0 0 + Y)] (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro p (rfl | rfl | rfl) <;> dsimp only <;> omega)
        (fun next kret hn => ?_) trivial, ?_, by omega, by omega⟩
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
        rw [upds_lt (lo := c) (by simp) hc13, h13]
        fl_ev
        exact ⟨trivial, hY, trivial, hn⟩
      · nb_tac
    | some q =>
      simp only [qFac, Bool.false_eq_true, ↓reduceIte]
      have hq := hprev q rfl
      refine ⟨completes_upds [(c, word 1 0 0), (c + 1, Y), (c + 2, word 1 0 0 + Y),
        (c + 3, σ (.n q) * (word 1 0 0 + Y))] (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro p (rfl | rfl | rfl | rfl) <;> dsimp only <;> omega) (fun next kret hn => ?_) trivial, ?_,
        by omega, by omega⟩
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.cons_append, List.nil_append]
        rw [upds_lt (lo := c) (by simp) hc13, upds_lt (lo := c) (by simp) hq, h13]
        fl_ev
        exact ⟨trivial, hY, trivial, trivial, hn⟩
      · nb_tac
  · cases prev with
    | none =>
      simp only [qFac, ↓reduceIte]
      refine ⟨completes_upds [(c, Y)] (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro p rfl; dsimp only; omega) (fun next kret hn => ?_) trivial, ?_, by omega,
        by omega⟩
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
        rw [upds_lt (lo := c) (by simp) hc13, h13]
        fl_ev
        exact ⟨hY, hn⟩
      · nb_tac
    | some q =>
      simp only [qFac, ↓reduceIte]
      have hq := hprev q rfl
      refine ⟨completes_upds [(c, Y), (c + 1, σ (.n q) * Y)] (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro p (rfl | rfl) <;> dsimp only <;> omega) (fun next kret hn => ?_)
        trivial, ?_, by omega, by omega⟩
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.cons_append, List.nil_append]
        rw [upds_lt (lo := c) (by simp) hc13, upds_lt (lo := c) (by simp) hq, h13]
        fl_ev
        exact ⟨hY, trivial, hn⟩
      · nb_tac
  
/-- **A slot's eight factors**, complete over the point's words. -/
theorem qFacs_complete (slot : ℕ) {a13 : E} {Y : ℕ → E} (hY : ∀ t < 8, LoadHolds rd a13 t (Y t)) :
    ∀ (n : ℕ) (prev : Option ℕ) (c : ℕ), n ≤ 8 → 13 < c → (∀ q, prev = some q → q < c) →
      ∀ σ : Val, σ (.n 13) = a13 →
      Completes C rd c (qFacs slot n prev c).2.2 (qFacs slot n prev c).1 σ (fun _ => True) ∧
        NumBelow (qFacs slot n prev c).2.2 (Stmt.valsList (qFacs slot n prev c).1) ∧
        c ≤ (qFacs slot n prev c).2.2 ∧ (0 < n → (qFacs slot n prev c).2.1 < (qFacs slot n prev c).2.2)
  | 0, _, c, _, _, _, σ, _ => ⟨completes_nil _ _ σ trivial, NumBelow.nil _, le_rfl, fun h => absurd h (by omega)⟩
  | n + 1, prev, c, hn, hc, hp, σ, h13 => by
    simp only [qFacs]
    obtain ⟨r1, r2, r3, r4⟩ := qFac_complete (C := C) (8 - (n + 1)) ((slot).testBit (8 - (n + 1)))
      prev c hc hp (hY _ (by omega)) σ h13
    set r := qFac (8 - (n + 1)) ((slot).testBit (8 - (n + 1))) prev c
    obtain ⟨-, -, s3, -⟩ := qFacs_complete slot hY n (some r.2.1) r.2.2 (by omega) (by omega)
      (fun q hq => by cases hq; exact r4) σ h13
    refine ⟨Completes.append (m := r.2.2) (by omega) s3 r2 r1 fun σ' he _ => ?_, ?_, by omega,
      fun _ => ?_⟩
    · exact (qFacs_complete slot hY n (some r.2.1) r.2.2 (by omega) (by omega)
        (fun q hq => by cases hq; exact r4) σ' (by rw [he.apply (Or.inl (by omega)), h13])).1
    · rw [valsList_append]
      obtain ⟨-, s2, -, -⟩ := qFacs_complete slot hY n (some r.2.1) r.2.2 (by omega) (by omega)
        (fun q hq => by cases hq; exact r4) σ h13
      exact (r2.mono s3).append s2
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp only [qFacs, Option.getD_some]; omega
      · exact (qFacs_complete slot hY n (some r.2.1) r.2.2 (by omega) (by omega)
          (fun q hq => by cases hq; exact r4) σ h13).2.2.2 hpos

theorem claim_idx : ∀ j < 112, 312 ≤ claimV.getD j 0 ∧ claimAcc j < claimV.getD j 0 ∧
    selV (claimCol j) < claimV.getD j 0 ∧ selV 5 < claimV.getD j 0 ∧
    claimV.getD (j + 1) 0 = claimAcc (j + 1) + 1 := by
  decide +kernel

/-- **A claim on the bus point or the table point**, complete: its point's length `m` the
column's log. -/
theorem c_claim_lo {j : ℕ} (hj : j < 112) (hk : claimKind j = 0 ∨ claimKind j = 1) (σ : Val)
    {a7 a8 a10 ch low lam : E} {m : ℕ} (h7 : σ (.n 7) = a7) (h8 : σ (.n 8) = a8)
    (h10 : σ (.n 10) = a10) (hch : σ (.n (if claimKind j = 0 then 17 else 19)) = ch)
    (lcp : LoadHolds rd a7 j (gen ^ m)) (llow : LoadHolds rd ch m low)
    (lk : LoadHolds rd a10 (claimCol j) (gen ^ m)) (llam : LoadHolds rd a8 j lam) :
    Completes C rd (claimV.getD j 0) (claimV.getD (j + 1) 0) (claimBlk j) σ (fun _ => True) := by
  obtain ⟨i1, i2, i3, -, i5⟩ := claim_idx j hj
  have h3 : claimKind j ≠ 3 := by omega
  have h2 : claimKind j ≠ 2 := by omega
  have hch' : (if claimKind j = 0 then 17 else 19) < claimV.getD j 0 := by split <;> omega
  rw [i5, (claimAcc_succ j hj).2.1 hk]
  simp only [claimBlk, h3, h2, ↓reduceIte]
  generalize claimV.getD j 0 = v at i1 i2 i3 hch' ⊢
  refine completes_upds [(v, gen ^ m), (v + 1, ch * gen ^ m), (v + 2, low), (v + 3, gen ^ m),
    (v + 4, lam), (v + 5, lam * low), (v + 6, lam * low * σ (.n (selV (claimCol j)))),
    (v + 7, σ (.n (claimAcc j)) + lam * low * σ (.n (selV (claimCol j))))]
    (by simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> omega)
    (fun next kret hn => ?_) trivial
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  rw [upds_lt (lo := v) (by simp) (show 7 < v by omega), upds_lt (lo := v) (by simp) (show 8 < v by omega),
    upds_lt (lo := v) (by simp) (show 10 < v by omega), upds_lt (lo := v) (by simp) hch',
    upds_lt (lo := v) (by simp) i3, upds_lt (lo := v) (by simp) i2, h7, h8, h10, hch]
  fl_ev
  exact ⟨lcp, trivial, lh_back llow (by omega), lk, e_add_self _, llam, trivial, trivial, trivial, hn⟩

/-- **A public-input claim**, complete: its column's log the memory's (`g^n = σ 5`). -/
theorem c_claim_pi {j : ℕ} (hj : j < 112) (hk : claimKind j = 3) (σ : Val) {a5 a8 a10 lam : E}
    (h5 : σ (.n 5) = a5) (h8 : σ (.n 8) = a8) (h10 : σ (.n 10) = a10)
    (lk : LoadHolds rd a10 (claimCol j) a5) (llam : LoadHolds rd a8 j lam) :
    Completes C rd (claimV.getD j 0) (claimV.getD (j + 1) 0) (claimBlk j) σ (fun _ => True) := by
  obtain ⟨i1, i2, i3, -, i5⟩ := claim_idx j hj
  rw [i5, (claimAcc_succ j hj).1 hk]
  simp only [claimBlk, hk, ↓reduceIte]
  generalize claimV.getD j 0 = v at i1 i2 i3 ⊢
  refine completes_upds [(v, a5), (v + 1, lam), (v + 2, lam * σ (.n 35)),
    (v + 3, lam * σ (.n 35) * σ (.n (selV (claimCol j)))),
    (v + 4, σ (.n (claimAcc j)) + lam * σ (.n 35) * σ (.n (selV (claimCol j))))]
    (by simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> omega)
    (fun next kret hn => ?_) trivial
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  rw [upds_lt (lo := v) (by simp) (show 5 < v by omega), upds_lt (lo := v) (by simp) (show 8 < v by omega),
    upds_lt (lo := v) (by simp) (show 10 < v by omega), upds_lt (lo := v) (by simp) (show 35 < v by omega),
    upds_lt (lo := v) (by simp) i3, upds_lt (lo := v) (by simp) i2, h5, h8, h10]
  fl_ev
  exact ⟨lk, e_add_self _, llam, trivial, trivial, trivial, hn⟩

/-- **A limb's claim**, complete: its point's length `m`, `q_flock`'s log `m + 8`. -/
theorem c_claim_q {j : ℕ} (hj : j < 112) (hk : claimKind j = 2) (σ : Val)
    {a7 a8 a10 a13 q low lam : E} {m : ℕ} {Y : ℕ → E} (h7 : σ (.n 7) = a7) (h8 : σ (.n 8) = a8)
    (h10 : σ (.n 10) = a10) (h13 : σ (.n 13) = a13) (h21 : σ (.n 21) = q)
    (hY : ∀ t < 8, LoadHolds rd a13 t (Y t))
    (lcp : LoadHolds rd a7 j (gen ^ m)) (llow : LoadHolds rd q m low)
    (lk : LoadHolds rd a10 5 (gen ^ (m + 8))) (llam : LoadHolds rd a8 j lam) :
    Completes C rd (claimV.getD j 0) (claimV.getD (j + 1) 0) (claimBlk j) σ (fun _ => True) := by
  obtain ⟨i1, i2, -, i4, i5⟩ := claim_idx j hj
  rw [i5, (claimAcc_succ j hj).2.2 hk]
  simp only [claimBlk, hk, ↓reduceIte]
  rw [List.cons_append]
  generalize claimV.getD j 0 = v at i1 i2 i4 ⊢
  obtain ⟨-, qb, qle, qlt⟩ := qFacs_complete (C := C) (claimSlot j) hY 8 none (v + 1) le_rfl
    (by omega) (fun _ h => by cases h) σ h13
  have qlt' := qlt (by omega)
  generalize hQ : qFacs (claimSlot j) 8 none (v + 1) = Q at qb qle qlt' ⊢
  refine Completes.atom_cons (gen ^ m) (by omega) (NumBelow.cons ⟨v, by omega, rfl⟩
    (NumBelow.cons ⟨7, by omega, rfl⟩ (NumBelow.nil _))) ?_ ?_
  · show LoadHolds rd (Function.update σ (.n v) (gen ^ m) (.n 7)) j
      (Function.update σ (.n v) (gen ^ m) (.n v))
    rw [upd_ne (by omega), upd_eq, h7]; exact lcp
  set σ1 := Function.update σ (.n v) (gen ^ m)
  have k1 : ∀ i < v, σ1 (.n i) = σ (.n i) := fun i hi => upd_ne (by omega)
  have hv1 : σ1 (.n v) = gen ^ m := by simp [σ1]
  have hQc := qFacs_complete (C := C) (claimSlot j) hY 8 none (v + 1) le_rfl (by omega)
    (fun _ h => by cases h) σ1 (by rw [k1 13 (by omega), h13])
  rw [hQ] at hQc
  refine Completes.append (m := Q.2.2) (by omega) (by omega) qb hQc.1 fun σ2 e2 _ => ?_
  have k2 : ∀ i < v + 1, σ2 (.n i) = σ1 (.n i) := fun i hi => e2.apply (Or.inl hi)
  refine completes_upds [(Q.2.2, q * gen ^ m), (Q.2.2 + 1, low), (Q.2.2 + 2, σ2 (.n Q.2.1) * low),
    (Q.2.2 + 3, word 256 0 0), (Q.2.2 + 4, gen ^ m * word 256 0 0), (Q.2.2 + 5, gen ^ (m + 8)),
    (Q.2.2 + 6, lam), (Q.2.2 + 7, lam * (σ2 (.n Q.2.1) * low)),
    (Q.2.2 + 8, lam * (σ2 (.n Q.2.1) * low) * σ (.n (selV 5))),
    (Q.2.2 + 9, σ (.n (claimAcc j)) + lam * (σ2 (.n Q.2.1) * low) * σ (.n (selV 5)))]
    (by simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> omega)
    (fun next kret hn => ?_) trivial
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  rw [upds_lt (lo := Q.2.2) (by simp) (show 21 < Q.2.2 by omega),
    upds_lt (lo := Q.2.2) (by simp) (show v < Q.2.2 by omega),
    upds_lt (lo := Q.2.2) (by simp) qlt',
    upds_lt (lo := Q.2.2) (by simp) (show 10 < Q.2.2 by omega),
    upds_lt (lo := Q.2.2) (by simp) (show 8 < Q.2.2 by omega),
    upds_lt (lo := Q.2.2) (by simp) (show selV 5 < Q.2.2 by omega),
    upds_lt (lo := Q.2.2) (by simp) (show claimAcc j < Q.2.2 by omega),
    k2 21 (by omega), k2 v (by omega), k2 10 (by omega), k2 8 (by omega), k2 (selV 5) (by omega),
    k2 (claimAcc j) (by omega), k1 21 (by omega), k1 10 (by omega), k1 8 (by omega),
    k1 (selV 5) (by omega), k1 (claimAcc j) (by omega), hv1, h21, h10, h8]
  fl_ev
  refine ⟨trivial, lh_back llow (by omega), trivial, trivial, trivial, lk, ?_, llam, trivial,
    trivial, trivial, hn⟩
  rw [word_g8, ← pow_add]; exact e_add_self _

end

end
end LeanVM.Guest.B1
