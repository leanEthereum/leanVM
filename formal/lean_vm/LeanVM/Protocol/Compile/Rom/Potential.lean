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
  node there; at a prover move or verdict it is `esc` there (`0` or `1`). A packed draw follows
  its chunks (`chunks`), each squeeze's first cells, and at the first chunk the log does not
  answer averages the rest (`restAvg`).
* `gvF ℓ L u h p` is the same with the first draw's challenges taken from the cells `L` of the
  state `u`: `gv1 ℓ u` with a squeeze's eight cells (`cells8`), `gvG ℓ u` with a grind's seven
  (`groundCells`).
* A record `st h p pw` of the state `u` has term `[D h] · [pow] · gv ℓ u h p` after the seed, where
  `[pow] = 1`, and `[D h] · [pow] · gv1 ℓ u h p` after a nonce, where `[pow]` is whether the proof
  of work passed on `u`'s third lane: the proof of work's permutation also draws the group's first
  challenge, `u`'s first two lanes.
* A record `sq h p` of the squeeze `u` has term `[D h] · gv1 ℓ u h p`.

A hash entry changes no term (`term_append_inl`). Every term is a supermartingale at a fresh
permutation answer, on the answers whose capacity no permutation input of the log carries
(`Fresh`, `term_step_old`): `gv` is one because `esc` at a `sample` node is the average over the
challenge of `esc` after it, and the challenge of a uniform state is uniform (`gv_step`); at a
packed draw `esc` is the average over `E^n`, and the cells of a uniform state are uniform and
independent (`sum_cells8_div`, `avgPk_drawVal`, `chunks_step`). The new
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

/-- At a doomed boundary, the escape probability is at most the certificate's bound. -/
theorem esc_le_eps {P : VerifierProgram Bool} {G : List Ev → Prop} (C : CertG P G) {h : List Ev} {p : VerifierProgram Bool}
    (hr : P.Reachable h) (hb : Boundary h) (ha : P.after h = some p) (hD : C.D h) :
    esc C.D h p ≤ C.ε h := by
  cases p with
  | sample k => exact C.group hr hb ha (Or.inl ⟨k, rfl⟩) hD
  | query i ps k => exact C.group hr hb ha (Or.inr (Or.inl ⟨i, ps, k, rfl⟩)) hD
  | samplePacked n k => exact C.group hr hb ha (Or.inr (Or.inr ⟨n, k, rfl⟩)) hD
  | ret a => cases a <;> simp [esc, hD]
  | fail => simp [esc]
  | read _ => simp [esc, hD]
  | readPacked _ _ => simp [esc, hD]
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

/-! ## Packed draws -/

section Draws

/-- The escape of a packed draw of `n` challenges past the challenges `cs`, the rest averaged:
`E0` of the whole draw. -/
noncomputable def restAvg (E0 : List E → ℝ≥0∞) (n : ℕ) (cs : List E) : ℝ≥0∞ :=
  avgPk (n - cs.length) fun r ↦ E0 (cs ++ r)

/-- A draw's value once its challenges `cs` are known: `fin` if it is complete, `cont` if not. -/
noncomputable def drawVal (fin cont : List E → ℝ≥0∞) (n : ℕ) (cs : List E) : ℝ≥0∞ :=
  if n ≤ cs.length then fin cs else cont cs

theorem restAvg_of_le {E0 : List E → ℝ≥0∞} {n : ℕ} {cs : List E} (h : n ≤ cs.length) :
    restAvg E0 n cs = E0 cs := by
  simp [restAvg, Nat.sub_eq_zero_of_le h, avgPk_zero]

/-- **The rest of a draw, one more chunk of up to `M` challenges drawn uniformly**: averaging the
draw's value over the chunk is the rest's average. -/
theorem avgPk_drawVal (E0 : List E → ℝ≥0∞) (n M : ℕ) (cs : List E) :
    avgPk M (fun L ↦ drawVal E0 (restAvg E0 n) n (cs ++ L.take (n - cs.length))) =
      restAvg E0 n cs := by
  set m := n - cs.length with hm
  by_cases hmM : m ≤ M
  · have hv : ∀ L : List E, L.length = M →
        drawVal E0 (restAvg E0 n) n (cs ++ L.take m) = E0 (cs ++ L.take m) := by
      intro L hL
      unfold drawVal
      have hc : n ≤ (cs ++ L.take m).length := by simp; omega
      simp only [hc, ↓reduceIte]
    rw [avgPk_congr hv, show M = m + (M - m) by omega, avgPk_append]
    refine avgPk_congr fun a ha ↦ ?_
    rw [← avgPk_const (M - m) (E0 (cs ++ a))]
    refine avgPk_congr fun b _ ↦ ?_
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · have hv : ∀ L : List E, L.length = M →
        drawVal E0 (restAvg E0 n) n (cs ++ L.take m) =
          avgPk (m - M) fun r ↦ E0 (cs ++ (L ++ r)) := by
      intro L hL
      unfold drawVal restAvg
      rw [List.take_of_length_le (by omega)]
      have hc : ¬ n ≤ cs.length + L.length := by omega
      simp only [List.length_append, List.append_assoc]
      rw [show n - (cs.length + L.length) = m - M by omega]
      simp only [hc, ↓reduceIte]
    rw [avgPk_congr hv, restAvg, ← hm, show m = M + (m - M) by omega, avgPk_append]
    simp only [show M + (m - M) - M = m - M by omega]

end Draws

/-! ## Group values -/

section Gv

variable (D : List Ev → Prop)

/-- The chunks of a packed draw of `n` challenges the log answers, from the state `d` with no
scalar waiting, `cs` drawn: each chunk is a squeeze (`sqIn`) and its first cells; `fin` at the
complete draw, after its last chunk's state, `rest` at the first chunk the log does not
answer. -/
noncomputable def chunks (ℓ : Log) (fin : List E → KeccakState → ℝ≥0∞) (rest : List E → ℝ≥0∞)
    (n : ℕ) (d : KeccakState) (cs : List E) : ℝ≥0∞ :=
  match lookF ℓ (sqIn d) with
  | some u =>
    if _hn : n ≤ (cs ++ (cells8 u).take (n - cs.length)).length then
      fin (cs ++ (cells8 u).take (n - cs.length)) u
    else chunks ℓ fin rest n u (cs ++ (cells8 u).take (n - cs.length))
  | none => rest cs
termination_by n - cs.length
decreasing_by
  simp only [List.length_append, List.length_take, length_cells8] at *
  omega

theorem chunks_some {ℓ : Log} {fin : List E → KeccakState → ℝ≥0∞} {rest : List E → ℝ≥0∞}
    {n : ℕ} {d u : KeccakState} (cs : List E) (hl : lookF ℓ (sqIn d) = some u) :
    chunks ℓ fin rest n d cs =
      drawVal (fun cs' ↦ fin cs' u) (chunks ℓ fin rest n u) n
        (cs ++ (cells8 u).take (n - cs.length)) := by
  rw [chunks, hl]
  simp only [drawVal]
  split <;> rfl

theorem chunks_none {ℓ : Log} {fin : List E → KeccakState → ℝ≥0∞} {rest : List E → ℝ≥0∞}
    {n : ℕ} {d : KeccakState} (cs : List E) (hl : lookF ℓ (sqIn d) = none) :
    chunks ℓ fin rest n d cs = rest cs := by
  rw [chunks, hl]

theorem chunks_fresh {ℓ : Log} {fin : List E → KeccakState → ℝ≥0∞} {rest : List E → ℝ≥0∞}
    {n : ℕ} {d : KeccakState} (cs : List E) (hd : Fresh ℓ d) :
    chunks ℓ fin rest n d cs = rest cs :=
  chunks_none cs (lookF_sqIn_of_fresh hd)

/-- The escape probability of a group conditioned on the squeezes the log answers: follow them
from the state `d` with no scalar waiting, at history `h` and node `p`, then `esc`. A packed draw
follows its chunks (`chunks`). -/
noncomputable def gv (ℓ : Log) : KeccakState → List Ev → VerifierProgram Bool → ℝ≥0∞
  | d, h, .sample k => match lookF ℓ (sqIn d) with
    | some u => gv ℓ u (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u))
    | none => esc D h (.sample k)
  | d, h, .samplePacked n k =>
    chunks ℓ (fun cs u ↦ gv ℓ u (h ++ [Ev.samplePacked cs]) (k cs))
      (restAvg (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)) n) n d []
  | d, h, .query i ps k => match answer h i ps with
    | some rows => gv ℓ d (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | _, h, .ret a => esc D h (.ret a)
  | _, h, .fail => esc D h .fail
  | _, h, .read k => esc D h (.read k)
  | _, h, .readPacked n k => esc D h (.readPacked n k)
  | _, h, .grind b k => esc D h (.grind b k)
  | _, h, .commit ht w k => esc D h (.commit ht w k)

theorem esc_samplePacked (h : List Ev) (n : ℕ) (k : List E → VerifierProgram Bool) :
    esc D h (.samplePacked n k) =
      restAvg (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)) n [] := by
  simp [esc, restAvg]

/-- From a fresh state, the group value is the escape probability. -/
theorem gv_fresh {ℓ : Log} {d : KeccakState} (hd : Fresh ℓ d) :
    ∀ (h : List Ev) (p : VerifierProgram Bool), gv D ℓ d h p = esc D h p
  | h, .sample k => by simp only [gv, lookF_sqIn_of_fresh hd]
  | h, .samplePacked n k => by
    rw [gv, chunks_fresh _ hd, esc_samplePacked]
  | h, .query i ps k => by
    simp only [gv, esc_query]
    split
    · exact gv_fresh hd _ _
    · rfl
  | _, .ret _ => rfl
  | _, .fail => rfl
  | _, .read _ => rfl
  | _, .readPacked _ _ => rfl
  | _, .grind _ _ => rfl
  | _, .commit _ _ _ => rfl

/-- Chunks depend on the log only through permutation entries. -/
theorem chunks_append_inl (ℓ : Log) (e : Bytes × Digest) {fin fin' : List E → KeccakState → ℝ≥0∞}
    (hfin : ∀ cs u, fin' cs u = fin cs u) (rest : List E → ℝ≥0∞) (n : ℕ) (d : KeccakState)
    (cs : List E) : chunks (ℓ ++ [.inl e]) fin' rest n d cs = chunks ℓ fin rest n d cs := by
  rcases hl : lookF ℓ (sqIn d) with _ | u
  · rw [chunks_none _ (by rw [lookF_append_inl]; exact hl), chunks_none _ hl]
  · rw [chunks_some _ (by rw [lookF_append_inl]; exact hl), chunks_some _ hl]
    unfold drawVal
    split
    · exact hfin _ _
    · exact chunks_append_inl ℓ e hfin rest n u _
termination_by n - cs.length
decreasing_by
  simp only [List.length_append, List.length_take, length_cells8] at *
  omega

/-- A hash entry leaves group values unchanged. -/
theorem gv_append_inl (ℓ : Log) (e : Bytes × Digest) :
    ∀ (d : KeccakState) (h : List Ev) (p : VerifierProgram Bool), gv D (ℓ ++ [.inl e]) d h p = gv D
        ℓ d h p
  | d, h, .sample k => by
    simp only [gv, lookF_append_inl]
    split
    · exact gv_append_inl ℓ e _ _ _
    · rfl
  | d, h, .samplePacked n k => by
    simp only [gv]
    exact chunks_append_inl ℓ e (fun cs u ↦ gv_append_inl ℓ e u _ (k cs)) _ n d []
  | d, h, .query i ps k => by
    simp only [gv]
    split
    · exact gv_append_inl ℓ e _ _ _
    · rfl
  | _, _, .ret _ => rfl
  | _, _, .fail => rfl
  | _, _, .read _ => rfl
  | _, _, .readPacked _ _ => rfl
  | _, _, .grind _ _ => rfl
  | _, _, .commit _ _ _ => rfl

/-- The log with one more permutation entry. -/
abbrev logF (ℓ : Log) (t v : KeccakState) : Log := ℓ ++ [.inr (t, v)]

/-- **Chunks are supermartingales**, if their completions are, and are `E0` from a fresh
state. -/
theorem chunks_step {ℓ : Log} {t : KeccakState} (ht : lookF ℓ t = none)
    (E0 : List E → ℝ≥0∞) (n : ℕ) (fin : Log → List E → KeccakState → ℝ≥0∞)
    (hfin : ∀ cs u, (∑ v, ind (Fresh (logF ℓ t v) v) * fin (logF ℓ t v) cs u) /
      Fintype.card KeccakState ≤ fin ℓ cs u)
    (hfresh : ∀ ℓ' cs u, Fresh ℓ' u → fin ℓ' cs u = E0 cs) (d : KeccakState) (cs : List E) :
    (∑ v, ind (Fresh (logF ℓ t v) v) *
        chunks (logF ℓ t v) (fin (logF ℓ t v)) (restAvg E0 n) n d cs) /
      Fintype.card KeccakState ≤ chunks ℓ (fin ℓ) (restAvg E0 n) n d cs := by
  rcases hl : lookF ℓ (sqIn d) with _ | u
  · rw [chunks_none _ hl]
    by_cases hx : sqIn d = t
    · have hval : ∀ v, ind (Fresh (logF ℓ t v) v) *
          chunks (logF ℓ t v) (fin (logF ℓ t v)) (restAvg E0 n) n d cs ≤
            drawVal E0 (restAvg E0 n) n (cs ++ (cells8 v).take (n - cs.length)) := by
        intro v
        rw [chunks_some _ (by rw [hx]; exact lookF_append_inr_self ht v)]
        by_cases hf : Fresh (logF ℓ t v) v
        · rw [ind_of hf, one_mul]
          unfold drawVal
          split
          · exact (hfresh _ _ _ hf).le
          · exact (chunks_fresh _ hf).le
        · rw [ind_of_not hf, zero_mul]; exact bot_le
      calc _ ≤ (∑ v, drawVal E0 (restAvg E0 n) n (cs ++ (cells8 v).take (n - cs.length))) /
            Fintype.card KeccakState := by gcongr with v; exact hval v
        _ = restAvg E0 n cs := by
          rw [sum_cells8_div (fun L ↦ drawVal E0 (restAvg E0 n) n (cs ++ L.take (n - cs.length))),
            avgPk_drawVal]
    · have : ∀ v, chunks (logF ℓ t v) (fin (logF ℓ t v)) (restAvg E0 n) n d cs =
          restAvg E0 n cs := fun v ↦
        chunks_none _ (by rw [lookF_append_inr_of_ne hx]; exact hl)
      simp only [this]
      exact avg_ind_mul_const_le _ _
  · rw [chunks_some _ hl]
    have : ∀ v, chunks (logF ℓ t v) (fin (logF ℓ t v)) (restAvg E0 n) n d cs =
        drawVal (fun cs' ↦ fin (logF ℓ t v) cs' u) (chunks (logF ℓ t v) (fin (logF ℓ t v))
          (restAvg E0 n) n u) n (cs ++ (cells8 u).take (n - cs.length)) := fun v ↦
      chunks_some _ (lookF_append_of_some hl _)
    simp only [this]
    unfold drawVal
    split
    · exact hfin _ _
    · exact chunks_step ht E0 n fin hfin hfresh u _
termination_by n - cs.length
decreasing_by
  simp only [List.length_append, List.length_take, length_cells8] at *
  omega

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
  | d, h, .samplePacked n k => by
    simp only [gv]
    exact chunks_step ht (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)) n
      (fun ℓ' cs u ↦ gv D ℓ' u (h ++ [Ev.samplePacked cs]) (k cs))
      (fun cs u ↦ gv_step ht u _ (k cs)) (fun ℓ' cs u hu ↦ gv_fresh D hu _ _) d []
  | d, h, .query i ps k => by
    simp only [gv]
    split
    · exact gv_step ht d _ _
    · simp only [mul_zero, Finset.sum_const_zero, ENNReal.zero_div, le_refl]
  | d, h, .ret a => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .fail => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .read k => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .readPacked n k => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .grind b k => by simp only [gv]; exact avg_ind_mul_const_le _ _
  | d, h, .commit ht' w k => by simp only [gv]; exact avg_ind_mul_const_le _ _

/-- The group value with its first draw's challenges taken from the cells `L` of the state `u`
(a squeeze's eight, `cells8`, or a grind's seven, `groundCells`): follow the openings to the
draw, take its challenges from `L` (a packed draw's first chunk), then `gv` from `u`. -/
noncomputable def gvF (ℓ : Log) (L : List E) (u : KeccakState) :
    List Ev → VerifierProgram Bool → ℝ≥0∞
  | h, .sample k => gv D ℓ u (h ++ [Ev.sample (L.headD 0)]) (k (L.headD 0))
  | h, .samplePacked n k =>
    drawVal (fun cs ↦ gv D ℓ u (h ++ [Ev.samplePacked cs]) (k cs))
      (chunks ℓ (fun cs u ↦ gv D ℓ u (h ++ [Ev.samplePacked cs]) (k cs))
        (restAvg (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)) n) n u) n (L.take n)
  | h, .query i ps k => match answer h i ps with
    | some rows => gvF ℓ L u (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | h, .ret a => esc D h (.ret a)
  | h, .fail => esc D h .fail
  | h, .read k => esc D h (.read k)
  | h, .readPacked n k => esc D h (.readPacked n k)
  | h, .grind b k => esc D h (.grind b k)
  | h, .commit ht w k => esc D h (.commit ht w k)

/-- The group value with the first squeeze answered by `u`. -/
noncomputable abbrev gv1 (ℓ : Log) (u : KeccakState) := gvF D ℓ (cells8 u) u

/-- The group value whose first draw a grind's permutation `u` made. -/
noncomputable abbrev gvG (ℓ : Log) (u : KeccakState) := gvF D ℓ (groundCells u) u

theorem gvF_append_inl (ℓ : Log) (e : Bytes × Digest) (L : List E) (u : KeccakState) :
    ∀ (h : List Ev) (p : VerifierProgram Bool), gvF D (ℓ ++ [.inl e]) L u h p = gvF D ℓ L u h p
  | h, .sample k => gv_append_inl D ℓ e _ _ _
  | h, .samplePacked n k => by
    simp only [gvF, drawVal]
    split
    · exact gv_append_inl D ℓ e _ _ _
    · exact chunks_append_inl ℓ e (fun cs u ↦ gv_append_inl D ℓ e u _ (k cs)) _ n u _
  | h, .query i ps k => by
    simp only [gvF]
    split
    · exact gvF_append_inl ℓ e L u _ _
    · rfl
  | _, .ret _ => rfl
  | _, .fail => rfl
  | _, .read _ => rfl
  | _, .readPacked _ _ => rfl
  | _, .grind _ _ => rfl
  | _, .commit _ _ _ => rfl

/-- `gvF` is a supermartingale, as `gv` is. -/
theorem gvF_step {ℓ : Log} {t : KeccakState} (ht : lookF ℓ t = none) (L : List E)
    (u : KeccakState) :
    ∀ (h : List Ev) (p : VerifierProgram Bool),
      (∑ v, ind (Fresh (ℓ ++ [.inr (t, v)]) v) * gvF D (ℓ ++ [.inr (t, v)]) L u h p) /
          Fintype.card KeccakState ≤ gvF D ℓ L u h p
  | h, .sample k => gv_step D ht _ _ _
  | h, .samplePacked n k => by
    simp only [gvF, drawVal]
    split
    · exact gv_step D ht _ _ _
    · exact chunks_step ht (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)) n
        (fun ℓ' cs u ↦ gv D ℓ' u (h ++ [Ev.samplePacked cs]) (k cs))
        (fun cs u ↦ gv_step D ht u _ (k cs)) (fun ℓ' cs u hu ↦ gv_fresh D hu _ _) u _
  | h, .query i ps k => by
    simp only [gvF]
    split
    · exact gvF_step ht L u _ _
    · simp only [mul_zero, Finset.sum_const_zero, ENNReal.zero_div, le_refl]
  | h, .ret a => by simp only [gvF]; exact avg_ind_mul_const_le _ _
  | h, .fail => by simp only [gvF]; exact avg_ind_mul_const_le _ _
  | h, .read k => by simp only [gvF]; exact avg_ind_mul_const_le _ _
  | h, .readPacked n k => by simp only [gvF]; exact avg_ind_mul_const_le _ _
  | h, .grind b k => by simp only [gvF]; exact avg_ind_mul_const_le _ _
  | h, .commit ht' w k => by simp only [gvF]; exact avg_ind_mul_const_le _ _

/-- The escape probability of a group whose first draw takes its challenges from `L`. -/
noncomputable def escF (L : List E) : List Ev → VerifierProgram Bool → ℝ≥0∞
  | h, .sample k => esc D (h ++ [Ev.sample (L.headD 0)]) (k (L.headD 0))
  | h, .samplePacked n k =>
    drawVal (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs))
      (restAvg (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)) n) n (L.take n)
  | h, .query i ps k => match answer h i ps with
    | some rows => escF L (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | h, .ret a => esc D h (.ret a)
  | h, .fail => esc D h .fail
  | h, .read k => esc D h (.read k)
  | h, .readPacked n k => esc D h (.readPacked n k)
  | h, .grind b k => esc D h (.grind b k)
  | h, .commit ht w k => esc D h (.commit ht w k)

/-- From a fresh state, `gvF` is the escape probability after the first draw's cells. -/
theorem gvF_fresh {ℓ : Log} {u : KeccakState} (hu : Fresh ℓ u) (L : List E) :
    ∀ (h : List Ev) (p : VerifierProgram Bool), gvF D ℓ L u h p = escF D L h p
  | h, .sample k => gv_fresh D hu _ _
  | h, .samplePacked n k => by
    simp only [gvF, escF, drawVal]
    split
    · exact gv_fresh D hu _ _
    · exact chunks_fresh _ hu
  | h, .query i ps k => by
    simp only [gvF, escF]
    split
    · exact gvF_fresh hu L _ _
    · rfl
  | _, .ret _ => rfl
  | _, .fail => rfl
  | _, .read _ => rfl
  | _, .readPacked _ _ => rfl
  | _, .grind _ _ => rfl
  | _, .commit _ _ _ => rfl

/-- **Averaging the first draw's cells gives the escape probability.** -/
theorem avg_escF {M : ℕ} (hM : 1 ≤ M) :
    ∀ (h : List Ev) (p : VerifierProgram Bool), avgPk M (fun L ↦ escF D L h p) = esc D h p
  | h, .sample k => by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    simp only [escF, avgPk_succ, List.headD_cons, avgPk_const, esc_sample]
  | h, .samplePacked n k => by
    have := avgPk_drawVal (fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)) n M []
    simp only [List.nil_append, List.length_nil, Nat.sub_zero] at this
    simp only [escF, esc_samplePacked]
    exact this
  | h, .query i ps k => by
    simp only [escF, esc_query]
    split
    · exact avg_escF hM _ _
    · exact avgPk_const _ _
  | h, .ret a => avgPk_const _ _
  | h, .fail => avgPk_const _ _
  | h, .read k => avgPk_const _ _
  | h, .readPacked n k => avgPk_const _ _
  | h, .grind b k => avgPk_const _ _
  | h, .commit ht w k => avgPk_const _ _

/-- **The first squeeze of a group, fresh, averages to the escape probability.** -/
theorem gv1_new {ℓ : Log} {t : KeccakState} (h : List Ev) (p : VerifierProgram Bool) :
    (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * gv1 D (ℓ ++ [.inr (t, u)]) u h p) /
        Fintype.card KeccakState ≤ esc D h p := by
  calc (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) * gv1 D (ℓ ++ [.inr (t, u)]) u h p) /
          Fintype.card KeccakState
      ≤ (∑ u, escF D (cells8 u) h p) / Fintype.card KeccakState := by
        gcongr with u
        by_cases hf : Fresh (ℓ ++ [.inr (t, u)]) u
        · rw [ind_of hf, one_mul]; exact (gvF_fresh D hf _ h p).le
        · rw [ind_of_not hf, zero_mul]; exact bot_le
    _ = esc D h p := by
        rw [sum_cells8_div (fun L ↦ escF D L h p), avg_escF D (by norm_num)]

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
  | some _, u, h, p => gvG D ℓ u h p

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
  | st h p pw => cases pw <;> simp only [term, stGv, gv_append_inl, gvF_append_inl]
  | sq h p => simp only [term, gvF_append_inl]

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
    · exact gvF_step D ht _ d h p
  | sq h p =>
    simp only [term]
    rw [hpull]
    gcongr
    exact gvF_step D ht _ d h p

end
end LeanVM.Protocol.Compile.Rom
