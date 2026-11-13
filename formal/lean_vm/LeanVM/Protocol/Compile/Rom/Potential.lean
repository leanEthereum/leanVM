/-
  LeanVM.Protocol.Compile.Rom.Potential

  The potential of the random-oracle theorem: a function of the oracles' log that bounds the
  probability that the compiled verifier will accept from a doomed history, and the
  supermartingale property of its terms: one fresh permutation answer does not raise an existing
  term in expectation.
-/

module

public import LeanVM.Protocol.Compile.Rom.Decode

/-!
# The potential

Fix a program `P`, a doom certificate `C : Cert P` and the family of seedings `σ`. The potential
of a log `ℓ` is

  `Φ ℓ = 1` if `ℓ` fails (`Fail`), and otherwise `min 1 (∑ term over the records of ℓ)`,

the records being the decoder's (`decode`), one per permutation entry. A record's term is, when
the history at which it starts is doomed, the escape probability of the group of challenges it
starts, *conditioned on the challenges already drawn*:

* `gv ℓ d h p` follows the squeezes the log already answers from the state `d` with no scalar
  waiting (`sqIn`), at history `h` and node `p`, and the openings (answered from the history's
  words), to the first squeeze the log does not answer, where it is `esc C.D` of the history and
  node there; at a prover move or verdict it is `esc` there (`0` or `1`).
* `gv1 ℓ u h p` is the same with the first squeeze answered by `u`.
* A record `st h p pw` of the state `u` has term `[D h] · [pow] · gv ℓ u h p` after the seed, where
  `[pow] = 1`, and `[D h] · [pow] · gv1 ℓ u h p` after a nonce, where `[pow]` is whether the proof
  of work passed on `u`'s third lane: the proof of work's permutation also draws the group's first
  challenge, `u`'s first two lanes.
* A record `sq h p` of the squeeze `u` has term `[D h] · gv1 ℓ u h p`.

A hash entry changes no term (`term_append_inl`). Every term is a supermartingale at a fresh
permutation answer, on the answers whose capacity no permutation input of the log carries
(`Fresh`, `term_step_old`): `gv` is one because `esc` at a `sample` node is the average over the
challenge of `esc` after it, and the challenge of a uniform state is uniform (`gv_step`). The new
record's average and the failure terms are in `LeanVM.Protocol.Compile.Rom.Step`.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## Freshness -/

/-- The input of a squeeze from the state `d` with no scalar waiting. -/
def sqIn (d : KeccakState) : KeccakState := duplexOf (capOf d) []

/-- The freshness of a permutation answer: no permutation input of the log carries its
capacity. -/
def Fresh (ℓ : Log) (u : KeccakState) : Prop := ∀ y ∈ fIns ℓ, capOf y ≠ capOf u

/-- A fresh state has no squeeze in the log. -/
theorem lookF_sqIn_of_fresh {ℓ : Log} {u : KeccakState} (hu : Fresh ℓ u) : lookF ℓ (sqIn u) = none := by
  rw [lookF, lookR_eq_none_iff]
  intro hm
  exact hu _ hm (by simp [sqIn])

theorem fIns_append_inr (ℓ : Log) (s u : KeccakState) : fIns (ℓ ++ [.inr (s, u)]) = fIns ℓ ++ [s] := by
  simp [fIns]

theorem fIns_append_inl (ℓ : Log) (p : Bytes × Digest) : fIns (ℓ ++ [.inl p]) = fIns ℓ := by
  simp [fIns]

theorem fresh_of_not_badF {ℓ : Log} {s u : KeccakState} (h : ¬ BadF ℓ s u) :
    Fresh (ℓ ++ [.inr (s, u)]) u := by
  intro y hy hc
  rw [fIns_append_inr, List.mem_append, List.mem_singleton] at hy
  refine h (Or.inr (Or.inl ⟨y, ?_, hc⟩))
  rcases hy with hy | rfl
  · exact List.mem_cons_of_mem _ hy
  · exact List.mem_cons_self

/-! ## Escape probabilities -/

section Esc

variable (D : List Ev → Prop)

theorem esc_sample (h : List Ev) (k : E → VerifierProgram Bool) :
    esc D h (.sample k) =
      (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, esc D (h ++ [Ev.sample c]) (k c) := by
  simp [esc]

theorem esc_query (h : List Ev) (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram Bool) :
    esc D h (.query i ps k) = match answer h i ps with
      | some rows => esc D (h ++ [Ev.query rows]) (k rows)
      | none => 0 := by
  simp only [esc]
  rfl

theorem esc_le_one : ∀ (h : List Ev) (p : VerifierProgram Bool), esc D h p ≤ 1
  | h, .sample k => by
    rw [esc_sample]
    calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, esc D (h ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ _c : E, 1 := by
          gcongr with c; exact esc_le_one _ (k c)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)
  | h, .query i ps k => by
    rw [esc_query]
    split
    · exact esc_le_one _ _
    · exact zero_le_one
  | h, .ret true => by simp only [esc]; split <;> simp
  | h, .ret false => by simp [esc]
  | h, .fail => by simp [esc]
  | h, .read _ => by simp only [esc]; split <;> simp
  | h, .grind _ _ => by simp only [esc]; split <;> simp
  | h, .commit _ _ _ => by simp only [esc]; split <;> simp

/-- At a doomed boundary, the escape probability is at most the certificate's bound. -/
theorem esc_le_eps {P : VerifierProgram Bool} (C : Cert P) {h : List Ev} {p : VerifierProgram Bool}
    (hr : P.Reachable h) (hb : Boundary h) (ha : P.after h = some p) (hD : C.D h) :
    esc C.D h p ≤ C.ε h := by
  cases p with
  | sample k => exact C.group hr hb ha (Or.inl ⟨k, rfl⟩) hD
  | query i ps k => exact C.group hr hb ha (Or.inr ⟨i, ps, k, rfl⟩) hD
  | ret a => cases a <;> simp [esc, hD]
  | fail => simp [esc]
  | read _ => simp [esc, hD]
  | grind _ _ => simp [esc, hD]
  | commit _ _ _ => simp [esc, hD]

/-- The average of a constant times an indicator. -/
theorem avg_ind_mul_const_le (F : KeccakState → Prop) (c : ℝ≥0∞) :
    (∑ u, ind (F u) * c) / Fintype.card KeccakState ≤ c :=
  avg_le_of_le fun _ ↦ (mul_le_mul_left (ind_le_one _) c).trans (one_mul c).le

/-- **The challenge of a fresh squeeze is uniform**: the average over a state `u` of the escape
probability after the challenge `challengeOf u` is the escape probability before it. -/
theorem avg_esc_sample (h : List Ev) (k : E → VerifierProgram Bool) :
    (∑ u : KeccakState, esc D (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u))) /
        Fintype.card KeccakState = esc D h (.sample k) := by
  rw [sum_challengeOf_div fun c ↦ esc D (h ++ [Ev.sample c]) (k c), esc_sample,
    div_eq_mul_inv, mul_comm]

end Esc

/-! ## Group values -/

section Gv

variable (D : List Ev → Prop)

/-- The escape probability of a group conditioned on the squeezes the log answers: follow them
from the state `d` with no scalar waiting, at history `h` and node `p`, then `esc`. -/
noncomputable def gv (ℓ : Log) : KeccakState → List Ev → VerifierProgram Bool → ℝ≥0∞
  | d, h, .sample k => match lookF ℓ (sqIn d) with
    | some u => gv ℓ u (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u))
    | none => esc D h (.sample k)
  | d, h, .query i ps k => match answer h i ps with
    | some rows => gv ℓ d (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | _, h, .ret a => esc D h (.ret a)
  | _, h, .fail => esc D h .fail
  | _, h, .read k => esc D h (.read k)
  | _, h, .grind b k => esc D h (.grind b k)
  | _, h, .commit ht w k => esc D h (.commit ht w k)

/-- From a fresh state, the group value is the escape probability. -/
theorem gv_fresh {ℓ : Log} {d : KeccakState} (hd : Fresh ℓ d) :
    ∀ (h : List Ev) (p : VerifierProgram Bool), gv D ℓ d h p = esc D h p
  | h, .sample k => by simp only [gv, lookF_sqIn_of_fresh hd]
  | h, .query i ps k => by
    simp only [gv, esc_query]
    split
    · exact gv_fresh hd _ _
    · rfl
  | _, .ret _ => rfl
  | _, .fail => rfl
  | _, .read _ => rfl
  | _, .grind _ _ => rfl
  | _, .commit _ _ _ => rfl

/-- A hash entry leaves group values unchanged. -/
theorem gv_append_inl (ℓ : Log) (e : Bytes × Digest) :
    ∀ (d : KeccakState) (h : List Ev) (p : VerifierProgram Bool), gv D (ℓ ++ [.inl e]) d h p = gv D
        ℓ d h p
  | d, h, .sample k => by
    simp only [gv, lookF_append_inl]
    split
    · exact gv_append_inl ℓ e _ _ _
    · rfl
  | d, h, .query i ps k => by
    simp only [gv]
    split
    · exact gv_append_inl ℓ e _ _ _
    · rfl
  | _, _, .ret _ => rfl
  | _, _, .fail => rfl
  | _, _, .read _ => rfl
  | _, _, .grind _ _ => rfl
  | _, _, .commit _ _ _ => rfl

/-- **Group values are supermartingales.** For a fresh permutation input `t`, the average over
the answer `u` of the group value after the entry `(t, u)`, on the answers that are fresh, is at
most the group value before it. -/
theorem gv_step {ℓ : Log} {t : KeccakState} (ht : lookF ℓ t = none) :
    ∀ (d : KeccakState) (h : List Ev) (p : VerifierProgram Bool),
      (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * gv D (ℓ ++ [.inr (t, u)]) d h p) /
          Fintype.card KeccakState ≤ gv D ℓ d h p
  | d, h, .sample k => by
    rcases hl : lookF ℓ (sqIn d) with _ | v
    · by_cases hx : sqIn d = t
      · -- the squeeze from the deepest state: a martingale step
        have hval : ∀ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) *
            gv D (ℓ ++ [.inr (t, u)]) d h (.sample k) ≤
              esc D (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u)) := by
          intro u
          simp only [gv]
          rw [hx, lookF_append_inr_self ht]
          dsimp only
          by_cases hf : Fresh (ℓ ++ [.inr (t, u)]) u
          · rw [ind_of hf, one_mul, gv_fresh D hf]
          · rw [ind_of_not hf, zero_mul]; exact bot_le
        rw [show gv D ℓ d h (.sample k) = esc D h (.sample k) by simp only [gv, hl]]
        calc (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) *
                gv D (ℓ ++ [.inr (t, u)]) d h (.sample k)) / Fintype.card KeccakState
            ≤ (∑ u, esc D (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u)))
              / Fintype.card KeccakState := by gcongr with u; exact hval u
          _ = esc D h (.sample k) := avg_esc_sample D h k
      · have : ∀ u, gv D (ℓ ++ [.inr (t, u)]) d h (.sample k) = esc D h (.sample k) := by
          intro u; simp only [gv, lookF_append_inr_of_ne hx, hl]
        simp only [this, gv, hl]
        exact avg_ind_mul_const_le _ _
    · have : ∀ u, gv D (ℓ ++ [.inr (t, u)]) d h (.sample k) =
          gv D (ℓ ++ [.inr (t, u)]) v (h ++ [Ev.sample (challengeOf v)]) (k (challengeOf v)) := by
        intro u; simp only [gv, lookF_append_of_some hl]
      simp only [this, gv, hl]
      exact gv_step ht v _ _
  | d, h, .query i ps k => by
    simp only [gv]
    split
    · exact gv_step ht d _ _
    · simp only [mul_zero, Finset.sum_const_zero, ENNReal.zero_div, le_refl]
  | d, h, .ret a => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .fail => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .read k => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .grind b k => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .commit ht' w k => by simp only [gv]; exact avg_ind_mul_const_le _ _

/-- The group value with its first squeeze answered by `u`: follow the openings to the squeeze,
take `u`'s challenge, then `gv`. -/
noncomputable def gv1 (ℓ : Log) (u : KeccakState) : List Ev → VerifierProgram Bool → ℝ≥0∞
  | h, .sample k => gv D ℓ u (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u))
  | h, .query i ps k => match answer h i ps with
    | some rows => gv1 ℓ u (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | h, .ret a => esc D h (.ret a)
  | h, .fail => esc D h .fail
  | h, .read k => esc D h (.read k)
  | h, .grind b k => esc D h (.grind b k)
  | h, .commit ht w k => esc D h (.commit ht w k)

theorem gv1_append_inl (ℓ : Log) (e : Bytes × Digest) (u : KeccakState) :
    ∀ (h : List Ev) (p : VerifierProgram Bool), gv1 D (ℓ ++ [.inl e]) u h p = gv1 D ℓ u h p
  | h, .sample k => gv_append_inl D ℓ e _ _ _
  | h, .query i ps k => by
    simp only [gv1]
    split
    · exact gv1_append_inl ℓ e u _ _
    · rfl
  | _, .ret _ => rfl
  | _, .fail => rfl
  | _, .read _ => rfl
  | _, .grind _ _ => rfl
  | _, .commit _ _ _ => rfl

/-- `gv1` is a supermartingale, as `gv` is. -/
theorem gv1_step {ℓ : Log} {t : KeccakState} (ht : lookF ℓ t = none) (u : KeccakState) :
    ∀ (h : List Ev) (p : VerifierProgram Bool),
      (∑ v, ind (Fresh (ℓ ++ [.inr (t, v)]) v) * gv1 D (ℓ ++ [.inr (t, v)]) u h p) /
          Fintype.card KeccakState ≤ gv1 D ℓ u h p
  | h, .sample k => gv_step D ht _ _ _
  | h, .query i ps k => by
    simp only [gv1]
    split
    · exact gv1_step ht u _ _
    · simp only [mul_zero, Finset.sum_const_zero, ENNReal.zero_div, le_refl]
  | h, .ret a => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .fail => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .read k => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .grind b k => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .commit ht' w k => by simp only [gv1]; exact avg_ind_mul_const_le _ _

/-- **The first squeeze of a group, fresh, averages to the escape probability.** -/
theorem gv1_new {ℓ : Log} {t : KeccakState} :
    ∀ (h : List Ev) (p : VerifierProgram Bool),
      (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * gv1 D (ℓ ++ [.inr (t, u)]) u h p) /
          Fintype.card KeccakState ≤ esc D h p
  | h, .sample k => by
    calc (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * gv1 D (ℓ ++ [.inr (t, u)]) u h (.sample k)) /
            Fintype.card KeccakState
        ≤ (∑ u, esc D (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u))) /
            Fintype.card KeccakState := by
          gcongr with u
          simp only [gv1]
          by_cases hf : Fresh (ℓ ++ [.inr (t, u)]) u
          · rw [ind_of hf, one_mul, gv_fresh D hf]
          · rw [ind_of_not hf, zero_mul]; exact bot_le
      _ = esc D h (.sample k) := avg_esc_sample D h k
  | h, .query i ps k => by
    simp only [gv1, esc_query]
    split
    · exact gv1_new _ _
    · simp only [mul_zero, Finset.sum_const_zero, ENNReal.zero_div, le_refl]
  | h, .ret a => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .fail => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .read k => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .grind b k => by simp only [gv1]; exact avg_ind_mul_const_le _ _
  | h, .commit ht' w k => by simp only [gv1]; exact avg_ind_mul_const_le _ _

/-- The escape probability of a group whose first challenge is `c`: follow the openings to the
first squeeze, take the challenge `c`, then `esc`. -/
noncomputable def escAt (c : E) : List Ev → VerifierProgram Bool → ℝ≥0∞
  | h, .sample k => esc D (h ++ [Ev.sample c]) (k c)
  | h, .query i ps k => match answer h i ps with
    | some rows => escAt c (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | h, .ret a => esc D h (.ret a)
  | h, .fail => esc D h .fail
  | h, .read k => esc D h (.read k)
  | h, .grind b k => esc D h (.grind b k)
  | h, .commit ht w k => esc D h (.commit ht w k)

/-- From a fresh state, `gv1` is the escape probability after the state's challenge. -/
theorem gv1_fresh {ℓ : Log} {u : KeccakState} (hu : Fresh ℓ u) :
    ∀ (h : List Ev) (p : VerifierProgram Bool), gv1 D ℓ u h p = escAt D (challengeOf u) h p
  | h, .sample k => gv_fresh D hu _ _
  | h, .query i ps k => by
    simp only [gv1, escAt]
    split
    · exact gv1_fresh hu _ _
    · rfl
  | _, .ret _ => rfl
  | _, .fail => rfl
  | _, .read _ => rfl
  | _, .grind _ _ => rfl
  | _, .commit _ _ _ => rfl

/-- Averaging the first challenge gives the escape probability. -/
theorem avg_escAt : ∀ (h : List Ev) (p : VerifierProgram Bool),
    (∑ c : E, escAt D c h p) / Fintype.card E = esc D h p
  | h, .sample k => by
    simp only [escAt, esc_sample]
    rw [div_eq_mul_inv, mul_comm]
  | h, .query i ps k => by
    simp only [escAt, esc_query]
    split
    · exact avg_escAt _ _
    · simp
  | h, .ret a => by
    simp only [escAt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  | h, .fail => by
    simp only [escAt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  | h, .read k => by
    simp only [escAt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  | h, .grind b k => by
    simp only [escAt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  | h, .commit ht w k => by
    simp only [escAt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)

end Gv

/-! ## Terms and the potential -/

section Terms

variable (D : List Ev → Prop)

/-- The proof-of-work factor of a state record: `1` after the seed, whether the proof of work
of `b` bits passed on the permutation's third lane after a nonce. -/
noncomputable def powF : Option (ℕ × E) → KeccakState → ℝ≥0∞
  | none, _ => 1
  | some (b, _), u => ind (powOk b (Keccak.lane u 2) = true)

/-- The group value of a state record: after the seed the group's first squeeze is a later
permutation (`gv`); after a proof of work it is the state's own challenge (`gv1`). -/
noncomputable def stGv (ℓ : Log) : Option (ℕ × E) → KeccakState → List Ev →
    VerifierProgram Bool → ℝ≥0∞
  | none, u, h, p => gv D ℓ u h p
  | some _, u, h, p => gv1 D ℓ u h p

/-- The term of a record. -/
noncomputable def term (ℓ : Log) : Shape × KeccakState → ℝ≥0∞
  | (.none, _) => 0
  | (.st h p pw, u) => ind (D h) * (powF pw u * stGv D ℓ pw u h p)
  | (.sq h p, u) => ind (D h) * gv1 D ℓ u h p

theorem term_append_inl (ℓ : Log) (e : Bytes × Digest) (κ : Shape × KeccakState) :
    term D (ℓ ++ [.inl e]) κ = term D ℓ κ := by
  obtain ⟨s, u⟩ := κ
  cases s with
  | none => rfl
  | st h p pw => cases pw <;> simp only [term, stGv, gv_append_inl, gv1_append_inl]
  | sq h p => simp only [term, gv1_append_inl]

variable {X : Type} (σ : Seeds X) (P : VerifierProgram Bool)

/-- The sum of the terms of the records of a log. -/
noncomputable def termSum (ℓ : Log) : ℝ≥0∞ := ((decode σ P ℓ).kinds.map (term D ℓ)).sum

open Classical in
/-- **The potential**: `1` on a failed log, otherwise the sum of the terms, capped at `1`. -/
noncomputable def pot (ℓ : Log) : ℝ≥0∞ := if Fail σ ℓ then 1 else min 1 (termSum D σ P ℓ)

theorem pot_nil : pot D σ P [] = 0 := by
  have h0 : termSum D σ P [] = 0 := by
    simp only [termSum, decode_nil, Dec.init, List.map_nil, List.sum_nil]
  simp only [pot, not_fail_nil, ↓reduceIte, h0, min_eq_right (zero_le_one' ℝ≥0∞)]

theorem pot_le_one (ℓ : Log) : pot D σ P ℓ ≤ 1 := by
  unfold pot; split
  · exact le_rfl
  · exact min_le_left _ _

theorem termSum_append_inl (ℓ : Log) (e : Bytes × Digest) :
    termSum D σ P (ℓ ++ [.inl e]) = termSum D σ P ℓ := by
  simp only [termSum, decode_append_inl]
  congr 1
  exact List.map_congr_left fun κ _ ↦ term_append_inl D ℓ e κ

end Terms

/-! ## The supermartingale property of old records -/

/-- **Old records are supermartingales** at a fresh permutation answer. -/
theorem term_step_old (D : List Ev → Prop) {ℓ : Log} {t : KeccakState} (ht : lookF ℓ t = none)
    (κ : Shape × KeccakState) :
    (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * term D (ℓ ++ [.inr (t, u)]) κ) /
        Fintype.card KeccakState ≤ term D ℓ κ := by
  obtain ⟨s, d⟩ := κ
  -- pull a constant factor out of the average
  have hpull : ∀ (a : ℝ≥0∞) (f : KeccakState → ℝ≥0∞),
      (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * (a * f u)) / Fintype.card KeccakState =
        a * ((∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * f u) / Fintype.card KeccakState) := by
    intro a f
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ ↦ by ring
  cases s with
  | none => simp [term]
  | st h p pw =>
    simp only [term]
    rw [hpull, hpull]
    gcongr
    cases pw
    · exact gv_step D ht d h p
    · exact gv1_step D ht d h p
  | sq h p =>
    simp only [term]
    rw [hpull]
    gcongr
    exact gv1_step D ht d h p

end
end LeanVM.Protocol.Compile.Rom
