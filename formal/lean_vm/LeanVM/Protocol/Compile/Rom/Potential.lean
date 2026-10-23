/-
  LeanVM.Protocol.Compile.Rom.Potential

  The potential of the random-oracle theorem: a function of the oracle's log that bounds the
  probability that the compiled verifier will accept from a doomed history, and its step
  inequality: one fresh answer raises it, in expectation, by at most the largest escape
  probability plus the probability of failure.
-/

module

public import LeanVM.Protocol.Compile.Rom.Decode

/-!
# The potential and the step inequality

Fix a program `P`, a doom certificate `C : Cert P` and the seeding `σ`. The potential of a log
`ℓ` is

  `Φ ℓ = 1` if `ℓ` fails (`Fail`), and otherwise `min 1 (∑ term over the records of ℓ)`,

the records being the decoder's (`decode`), one per entry. A record's term is, when the history
at which it starts is doomed, the escape probability of the group of challenges it starts,
*conditioned on the challenges already drawn*:

* `gv ℓ d h p` follows the squeezes the log already answers from the chain state `d` at history
  `h` and node `p`, and the openings (answered from the history's words), to the first squeeze
  the log does not answer, where it is `esc C.D` of the history and node there; at a prover
  move or verdict it is `esc` there (`0` or `1`).
* A record `bnd h p` of the chain state `d` has term `[D h] · gv ℓ d h p`.
* A record `grd h p b cv n` of the state `d` after the nonce `n` has term
  `[D h] · ρ · gv ℓ d h p`, with `ρ = 2^-min(b,64)` while the proof of work of `(cv, n)` is not in
  the log and `[powOk]` of its answer once it is (`rho`).
* A record `pow h p b cv n` of the proof of work `v` has term
  `[D h] · [powOk b n v] · gv` at the state after the nonce if the log has it, and `esc D h p`
  otherwise.

## The step inequality

`step_ineq` (`LeanVM.Protocol.Compile.Rom.Step`): for a log `ℓ` and an input `t` it does not
answer,

  `(∑ u, Φ (ℓ ++ [(t, u)])) / |Digest| ≤ Φ ℓ + εmax + (4 + k)(|ℓ| + 1) / |Digest|`,

where `εmax` bounds `2^-min(grindBits h, 64) · C.ε h` for every `h`. The last term is the
probability that the new entry fails (`sum_badEntry_le`). If it does not, write `F u` for "no
input of the new log has `u` in its first 32 bytes". Then:

* every old record's term is a supermartingale (`term_step_old`): `gv` is one because `esc` at a
  `sample` node is the average over the challenge of `esc` after it, and the challenge of a
  uniform digest is uniform (`gv_step`); a fresh proof of work turns `ρ = 2^-min(b,64)` into
  `[powOk]`, whose average is at most that (`sum_powOk_div_le`);
* the new record's term averages to at most `εmax` (`term_step_new`): it starts at the
  certificate's escape bound of its group, discounted by the proof of work.

Neither part assumes anything of the log: the decoding is a function of the log, and only
`F u` is used.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## Lookups after one more entry -/

theorem look_append_single (ℓ : Log) (t : Bytes) (u : Digest) (x : Bytes) :
    look (ℓ ++ [(t, u)]) x = (look ℓ x).or (if x = t then some u else none) := by
  induction ℓ with
  | nil =>
    simp only [List.nil_append, look, logLookup_cons, logLookup_nil, Option.none_or]
    by_cases h : x = t
    · simp [h]
    · simp [h, Ne.symm h]
  | cons e ℓ ih =>
    simp only [look] at ih ⊢
    simp only [List.cons_append, logLookup_cons]
    split
    · rfl
    · exact ih

theorem look_append_single_of_some {ℓ : Log} {x : Bytes} {v : Digest} (h : look ℓ x = some v)
    (t : Bytes) (u : Digest) : look (ℓ ++ [(t, u)]) x = some v := by
  rw [look_append_single, h, Option.some_or]

theorem look_append_single_of_ne {ℓ : Log} {x t : Bytes} (h : x ≠ t) (u : Digest) :
    look (ℓ ++ [(t, u)]) x = look ℓ x := by
  rw [look_append_single, ite_eq_right_iff.mpr (fun e ↦ absurd e h), Option.or_none]

theorem look_append_single_self {ℓ : Log} {t : Bytes} (h : look ℓ t = none) (u : Digest) :
    look (ℓ ++ [(t, u)]) t = some u := by
  rw [look_append_single, h, Option.none_or]; simp

/-- The freshness of an answer: no input of the log starts with it. -/
def Fresh (ℓ : Log) (u : Digest) : Prop := ∀ x ∈ ℓ.map Prod.fst, chunk0 x ≠ digestBytes u

/-- A fresh digest has no chain step in the log. -/
theorem look_chain_of_fresh {ℓ : Log} {u : Digest} (hu : Fresh ℓ u) (blk : Bytes) :
    look ℓ (digestBytes u ++ blk) = none := by
  rw [look, logLookup_eq_none_iff]
  intro hm
  exact hu _ hm (chunk0_append u blk)

theorem fresh_of_not_bad {X : Type} {σ : Seeds X} {ℓ : Log} {t : Bytes} {u : Digest}
    (h : ¬ BadEntry σ ℓ t u) : Fresh (ℓ ++ [(t, u)]) u := by
  intro x hx hc
  refine h (Or.inr ⟨x, ?_, Or.inl hc⟩)
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact List.mem_cons_of_mem _ hx
  · exact List.mem_cons_self

/-! ## Escape probabilities -/

section Esc

variable (D : List Ev → Prop)

theorem esc_sample (h : List Ev) (k : E → Prog Bool) :
    esc D h (.sample k) =
      (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, esc D (h ++ [Ev.sample c]) (k c) := by
  simp [esc]

theorem esc_query (h : List Ev) (i : ℕ) (ps : List ℕ) (k : List (List K) → Prog Bool) :
    esc D h (.query i ps k) = match answer h i ps with
      | some rows => esc D (h ++ [Ev.query rows]) (k rows)
      | none => 0 := by
  simp only [esc]
  rfl

theorem esc_le_one : ∀ (h : List Ev) (p : Prog Bool), esc D h p ≤ 1
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
theorem esc_le_eps {P : Prog Bool} (C : Cert P) {h : List Ev} {p : Prog Bool}
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

end Esc

/-! ## Group values -/

section Gv

variable (D : List Ev → Prop)

/-- The escape probability of a group conditioned on the squeezes the log answers: follow them
from the chain state `d` at history `h` and node `p`, then `esc`. -/
noncomputable def gv (ℓ : Log) : Digest → List Ev → Prog Bool → ℝ≥0∞
  | d, h, .sample k => match look ℓ (digestBytes d ++ blockOf 0 2) with
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

/-- From a fresh digest, the group value is the escape probability. -/
theorem gv_fresh {ℓ : Log} {d : Digest} (hd : Fresh ℓ d) :
    ∀ (h : List Ev) (p : Prog Bool), gv D ℓ d h p = esc D h p
  | h, .sample k => by simp only [gv, look_chain_of_fresh hd]
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

theorem gv_le_one (ℓ : Log) : ∀ (d : Digest) (h : List Ev) (p : Prog Bool), gv D ℓ d h p ≤ 1
  | d, h, .sample k => by
    simp only [gv]
    split
    · exact gv_le_one ℓ _ _ _
    · exact esc_le_one D _ _
  | d, h, .query i ps k => by
    simp only [gv]
    split
    · exact gv_le_one ℓ _ _ _
    · exact zero_le_one
  | _, _, .ret _ => esc_le_one D _ _
  | _, _, .fail => esc_le_one D _ _
  | _, _, .read _ => esc_le_one D _ _
  | _, _, .grind _ _ => esc_le_one D _ _
  | _, _, .commit _ _ _ => esc_le_one D _ _

/-- An entry that is not a squeeze leaves group values unchanged. -/
theorem gv_append_of_not_squeeze {ℓ : Log} {t : Bytes} (ht : ∀ c, t ≠ digestBytes c ++ blockOf 0 2)
    (u : Digest) : ∀ (d : Digest) (h : List Ev) (p : Prog Bool),
      gv D (ℓ ++ [(t, u)]) d h p = gv D ℓ d h p
  | d, h, .sample k => by
    simp only [gv, look_append_single_of_ne (Ne.symm (ht d))]
    split
    · exact gv_append_of_not_squeeze ht u _ _ _
    · rfl
  | d, h, .query i ps k => by
    simp only [gv]
    split
    · exact gv_append_of_not_squeeze ht u _ _ _
    · rfl
  | _, _, .ret _ => rfl
  | _, _, .fail => rfl
  | _, _, .read _ => rfl
  | _, _, .grind _ _ => rfl
  | _, _, .commit _ _ _ => rfl

/-- The average of a constant times an indicator. -/
theorem avg_ind_mul_const_le (F : Digest → Prop) (c : ℝ≥0∞) :
    (∑ u, ind (F u) * c) / Fintype.card Digest ≤ c := by
  refine ENNReal.div_le_of_le_mul ?_
  have h1 : ∑ u, ind (F u) * c ≤ ∑ _u : Digest, c := by
    refine Finset.sum_le_sum fun u _ ↦ ?_
    calc ind (F u) * c ≤ 1 * c := mul_le_mul_left (ind_le_one _) c
      _ = c := one_mul c
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **Group values are supermartingales.** For a fresh input `t`, the average over the answer
`u` of the group value after the entry `(t, u)`, on the answers that are fresh, is at most the
group value before it. -/
theorem gv_step {ℓ : Log} {t : Bytes} (ht : look ℓ t = none) :
    ∀ (d : Digest) (h : List Ev) (p : Prog Bool),
      (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) * gv D (ℓ ++ [(t, u)]) d h p) / Fintype.card Digest ≤
        gv D ℓ d h p
  | d, h, .sample k => by
    rcases hl : look ℓ (digestBytes d ++ blockOf 0 2) with _ | v
    · by_cases hx : digestBytes d ++ blockOf 0 2 = t
      · -- the squeeze from the deepest state: a martingale step
        have hval : ∀ u, ind (Fresh (ℓ ++ [(t, u)]) u) * gv D (ℓ ++ [(t, u)]) d h (.sample k) ≤
            esc D (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u)) := by
          intro u
          simp only [gv]
          rw [hx, look_append_single_self ht]
          dsimp only
          by_cases hf : Fresh (ℓ ++ [(t, u)]) u
          · rw [ind_of hf, one_mul, gv_fresh D hf]
          · rw [ind_of_not hf, zero_mul]; exact bot_le
        rw [show gv D ℓ d h (.sample k) = esc D h (.sample k) by simp only [gv, hl]]
        calc (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) * gv D (ℓ ++ [(t, u)]) d h (.sample k))
              / Fintype.card Digest
            ≤ (∑ u, esc D (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u)))
              / Fintype.card Digest := by gcongr with u; exact hval u
          _ = (∑ c, esc D (h ++ [Ev.sample c]) (k c)) / Fintype.card E :=
              sum_challengeOf_div fun c ↦ esc D (h ++ [Ev.sample c]) (k c)
          _ = esc D h (.sample k) := by rw [esc_sample, div_eq_mul_inv, mul_comm]
      · have : ∀ u, gv D (ℓ ++ [(t, u)]) d h (.sample k) = esc D h (.sample k) := by
          intro u; simp only [gv, look_append_single_of_ne hx, hl]
        simp only [this, gv, hl]
        exact avg_ind_mul_const_le _ _
    · have : ∀ u, gv D (ℓ ++ [(t, u)]) d h (.sample k) =
          gv D (ℓ ++ [(t, u)]) v (h ++ [Ev.sample (challengeOf v)]) (k (challengeOf v)) := by
        intro u; simp only [gv, look_append_single_of_some hl]
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

end Gv

/-! ## Terms and the potential -/

section Terms

variable (D : List Ev → Prop)

/-- The proof-of-work factor of the nonce `n` at the grind state `cv`: `2^-min(b, 64)` until the
proof of work is in the log, then whether it passed. -/
noncomputable def rho (ℓ : Log) (b : ℕ) (cv : Digest) (n : E) : ℝ≥0∞ :=
  match powIn ℓ cv n with
  | some v => ind (powOk b n v = true)
  | none => 2⁻¹ ^ min b 64

/-- The group value from the state after a nonce, if the log has it, and the escape
probability at the group's start otherwise. -/
noncomputable def gvOpt (ℓ : Log) : Option Digest → List Ev → Prog Bool → ℝ≥0∞
  | some d, h, p => gv D ℓ d h p
  | none, h, p => esc D h p

/-- The term of a record. -/
noncomputable def term (ℓ : Log) : Shape × Digest → ℝ≥0∞
  | (.none, _) => 0
  | (.bnd h p, d) => ind (D h) * gv D ℓ d h p
  | (.grd h p b cv n, d) => ind (D h) * (rho ℓ b cv n * gv D ℓ d h p)
  | (.pow h p b cv n, v) =>
    ind (D h) * (ind (powOk b n v = true) * gvOpt D ℓ (look ℓ (digestBytes cv ++ blockOf n 4)) h p)

variable {X : Type} (σ : Seeds X) (P : Prog Bool)

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

end Terms

/-! ## The supermartingale property of old records -/

section Old

variable (D : List Ev → Prop)

theorem powOk_avg (b : ℕ) (n : E) :
    (∑ u : Digest, ind (powOk b n u = true)) / Fintype.card Digest ≤ 2⁻¹ ^ min b 64 := by
  refine le_of_eq_of_le ?_ (sum_powOk_div_le b n)
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  unfold ind
  split_ifs <;> simp_all

/-- The tags `3` and `4` and the squeeze block differ. -/
theorem chain_ne_of_tag {c c' : Digest} {x x' : E} {a a' : ℕ} (ha : a < 256) (ha' : a' < 256)
    (hne : a ≠ a') : digestBytes c ++ blockOf x a ≠ digestBytes c' ++ blockOf x' a' := by
  intro h
  have := (chainInput_inj h).2.2
  have h1 := congrArg UInt8.toNat this
  simp only [Nat.toUInt8, UInt8.toNat_ofNat'] at h1
  omega

theorem not_squeeze_of_tag {c : Digest} {x : E} {a : ℕ} (ha : a < 256) (hne : a ≠ 2) :
    ∀ c', digestBytes c ++ blockOf x a ≠ digestBytes c' ++ blockOf 0 2 := fun _ ↦
  chain_ne_of_tag ha (by norm_num) hne

/-- How the proof-of-work factor moves at one fresh entry: either it stays (on fresh answers),
or the entry is the proof of work and the factor becomes its result. -/
theorem rho_step {ℓ : Log} {t : Bytes} (ht : look ℓ t = none) (b : ℕ) (cv : Digest) (n : E) :
    (∀ u, Fresh (ℓ ++ [(t, u)]) u → rho (ℓ ++ [(t, u)]) b cv n = rho ℓ b cv n) ∨
      (rho ℓ b cv n = 2⁻¹ ^ min b 64 ∧ (∃ base, t = digestBytes base ++ blockOf n 4) ∧
        ∀ u, rho (ℓ ++ [(t, u)]) b cv n = ind (powOk b n u = true)) := by
  rcases hb : look ℓ (digestBytes cv ++ blockOf 0 3) with _ | base
  · left
    intro u hu
    simp only [rho, powIn, hb, Option.bind_none]
    by_cases hx : digestBytes cv ++ blockOf 0 3 = t
    · rw [hx, look_append_single_self ht, Option.bind_some, look_chain_of_fresh hu]
    · rw [look_append_single_of_ne hx, hb, Option.bind_none]
  · rcases hp : look ℓ (digestBytes base ++ blockOf n 4) with _ | v
    · by_cases hx : digestBytes base ++ blockOf n 4 = t
      · right
        refine ⟨by simp [rho, powIn, hb, hp], ⟨base, hx.symm⟩, fun u ↦ ?_⟩
        simp only [rho, powIn, look_append_single_of_some hb, Option.bind_some, hx,
          look_append_single_self ht]
      · left
        intro u _
        simp only [rho, powIn, look_append_single_of_some hb, Option.bind_some, hb,
          look_append_single_of_ne hx, hp]
    · left
      intro u _
      simp only [rho, powIn, look_append_single_of_some hb, Option.bind_some, hb,
        look_append_single_of_some hp, hp]

/-- **Old records are supermartingales.** -/
theorem term_step_old {ℓ : Log} {t : Bytes} (ht : look ℓ t = none) (κ : Shape × Digest) :
    (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) * term D (ℓ ++ [(t, u)]) κ) / Fintype.card Digest ≤
      term D ℓ κ := by
  obtain ⟨s, d⟩ := κ
  have hc : (Fintype.card Digest : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card Digest : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- pull a constant factor out of the average
  have hpull : ∀ (a : ℝ≥0∞) (f : Digest → ℝ≥0∞),
      (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) * (a * f u)) / Fintype.card Digest =
        a * ((∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) * f u) / Fintype.card Digest) := by
    intro a f
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ ↦ by ring
  cases s with
  | none => simp [term]
  | bnd h p =>
    simp only [term]
    rw [hpull]
    gcongr
    exact gv_step D ht d h p
  | grd h p b cv n =>
    simp only [term]
    rw [hpull]
    gcongr
    rcases rho_step ht b cv n with hst | ⟨hr, ⟨base, htb⟩, hr'⟩
    · calc (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
              (rho (ℓ ++ [(t, u)]) b cv n * gv D (ℓ ++ [(t, u)]) d h p)) / Fintype.card Digest
          = (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
              (rho ℓ b cv n * gv D (ℓ ++ [(t, u)]) d h p)) / Fintype.card Digest := by
            congr 1
            refine Finset.sum_congr rfl fun u _ ↦ ?_
            by_cases hf : Fresh (ℓ ++ [(t, u)]) u
            · rw [hst u hf]
            · simp [ind_of_not hf]
        _ = rho ℓ b cv n * ((∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
              gv D (ℓ ++ [(t, u)]) d h p) / Fintype.card Digest) := hpull _ _
        _ ≤ rho ℓ b cv n * gv D ℓ d h p := by gcongr; exact gv_step D ht d h p
    · have hgv : ∀ u, gv D (ℓ ++ [(t, u)]) d h p = gv D ℓ d h p := fun u ↦
        gv_append_of_not_squeeze D (htb ▸ not_squeeze_of_tag (by norm_num) (by norm_num)) u d h p
      calc (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
              (rho (ℓ ++ [(t, u)]) b cv n * gv D (ℓ ++ [(t, u)]) d h p)) / Fintype.card Digest
          ≤ (∑ u, ind (powOk b n u = true) * gv D ℓ d h p) / Fintype.card Digest := by
            refine ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _
            rw [hr' u, hgv u]
            calc ind (Fresh (ℓ ++ [(t, u)]) u) * (ind (powOk b n u = true) * gv D ℓ d h p)
                ≤ 1 * (ind (powOk b n u = true) * gv D ℓ d h p) := by
                  gcongr; exact ind_le_one _
              _ = _ := one_mul _
        _ = ((∑ u, ind (powOk b n u = true)) / Fintype.card Digest) * gv D ℓ d h p := by
            rw [← Finset.sum_mul, ENNReal.mul_div_right_comm]
        _ ≤ 2⁻¹ ^ min b 64 * gv D ℓ d h p := by gcongr; exact powOk_avg b n
        _ = rho ℓ b cv n * gv D ℓ d h p := by rw [hr]
  | pow h p b cv n =>
    simp only [term]
    rw [hpull, hpull]
    gcongr
    rcases hl : look ℓ (digestBytes cv ++ blockOf n 4) with _ | e
    · by_cases hx : digestBytes cv ++ blockOf n 4 = t
      · have : ∀ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
            gvOpt D (ℓ ++ [(t, u)]) (look (ℓ ++ [(t, u)]) (digestBytes cv ++ blockOf n 4)) h p ≤
              esc D h p := by
          intro u
          rw [hx, look_append_single_self ht]
          simp only [gvOpt]
          by_cases hf : Fresh (ℓ ++ [(t, u)]) u
          · rw [ind_of hf, one_mul, gv_fresh D hf]
          · rw [ind_of_not hf, zero_mul]; exact bot_le
        simp only [gvOpt]
        calc _ ≤ (∑ _u : Digest, esc D h p) / Fintype.card Digest := by
              gcongr with u; exact this u
          _ ≤ esc D h p := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              exact ENNReal.div_le_of_le_mul' le_rfl
      · simp only [look_append_single_of_ne hx, hl, gvOpt]
        exact avg_ind_mul_const_le _ _
    · simp only [look_append_single_of_some hl, gvOpt]
      exact gv_step D ht e h p

end Old

end
end LeanVM.Protocol.Compile.Rom
