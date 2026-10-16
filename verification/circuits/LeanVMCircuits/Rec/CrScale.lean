module

public import LeanVMCircuits.Rec.TreeBound
public import LeanVMCircuits.Rec.PcsMatch

@[expose] public section

/-!
The collision term per execution, the prover model's straight-line extraction, and the tree's bound at deployed sizes.

The round theorems (`Bind.sumcheck_run_sound_at` and the like) ask collision resistance only between two answers of a run's family sharing the prefix of the transcript before a check's challenge, both off their executions' event `C`, and only on the rows that prefix binds (`Bind.PairCR`, `Bind.Run.cr`); `Bind.run_frac_off` charges `C` once per execution.

The prover model (`Bind.Run.cr_of_extract`): the prover at oracle `ρ` is an adaptive strategy `σ ρ` against the compression oracle `H`, causal (`hcaus`: the oracles agreeing with `ρ` on the answers drawn by `k`, and on those drawn at `k + 1` but the words `ownL`, give it the same first `n ρ k ownL` queries, those it makes before that squeeze), normalized (`hnorm`: every row it commits is a query among its first `Q`, its output the oracle's answer), and the rows the prefix binds output words fixed by the prefix (`hout`: an answer to a query before the squeeze, or one of the targets `tg ρ` its answers by then fix, at most `B` of them). Straight-line extraction (`Bind.oracleRows_of_late`): a row whose input is first queried after the squeeze answers a word fixed before it; if that word is an earlier answer the two queries collide (`Collision.Coll`), and otherwise the late query hits a target (`Collision.LateHit`), at most `Q · B / |V|^4` of the oracles (`Collision.late_card`, `Edges.lateEvent_frac`). Off the execution's collision, window and late-hit events every such row is a prefix query, the two executions share the prefix's queries, and `cr` follows from `Bind.pairCR_of_oracle`. A later query's hit on a word the prefix fixed is a collision only when the word is an earlier answer: a word the prover wrote without computing it is a preimage target, charged by `LateHit`.

`AirLink.tree_sound_exec` is the tree's bound over outcomes pairing the oracle on the transcripts' words with the compression oracle, child `v`'s `crBad` its execution's `Edges.crEvent` and `Edges.lateEvent` of `Q v` queries, bounded by `Edges.epsCR K (Q v) + Edges.epsLate K (Q v) (B v)` once per child, and each check's `testBad` by a bound holding at every compression oracle (the round theorems', `n · d / |E|` and the like). `Edges.exec_bound_deployed` evaluates the terms this bound proves at deployed sizes: with `card_E` (`|E| = 2^192`), per child at most `2^40 / |E| + epsCR K Q + epsLate K Q B` for `B ≤ 2^86` targets, below `2^-1` for `Q ≤ 2^84`, `2^-7` for `Q ≤ 2^82`, `2^-32` for `Q ≤ 2^74` and `2^-64` for `Q ≤ 2^63`; `Edges.epsCR_cap`: at `Q = 2^86` the window term alone is past one.
-/

namespace LeanVMCircuits.Rec.Collision

open Finset

variable {X Y : Type}

/-- A late hit: one of the first `Q` first queries answers a target `tg` fixed by the answers before it. -/
def LateHit (σ : List Y → X) (h : X → Y) (Q : ℕ) (tg : List Y → Finset Y) : Prop :=
  ∃ m < Q, Fresh σ h m ∧ h (query σ h m) ∈ tg (answers σ h m)

open Classical in
/-- The late-hit bound: at most `B` targets fixed by any answers, the oracles at which one of the first `Q` first
queries answers a target, times `|Y|`, are at most `Q · B` times all, each query's by resampling its answer
(`fresh_card`). -/
theorem late_card [Fintype X] [Fintype Y] (σ : List Y → X) (Q : ℕ) (tg : List Y → Finset Y) {B : ℕ}
    (hB : ∀ as, #(tg as) ≤ B) :
    #{h : X → Y | LateHit σ h Q tg} * Fintype.card Y ≤ Q * B * Fintype.card (X → Y) := by
  have hsub : ({h : X → Y | LateHit σ h Q tg} : Finset (X → Y)) ⊆ (range Q).biUnion fun m =>
      univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ tg (answers σ h m) := by
    intro h hh
    obtain ⟨m, hm, hf, ht⟩ := (mem_filter.mp hh).2
    exact mem_biUnion.mpr ⟨m, mem_range.mpr hm, mem_filter.mpr ⟨mem_univ _, hf, ht⟩⟩
  calc #{h : X → Y | LateHit σ h Q tg} * Fintype.card Y
      ≤ (∑ m ∈ range Q, #(univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ tg (answers σ h m))) *
          Fintype.card Y := Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ m ∈ range Q, #(univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ tg (answers σ h m)) *
          Fintype.card Y := sum_mul _ _ _
    _ ≤ ∑ _m ∈ range Q, B * Fintype.card (X → Y) := sum_le_sum fun m _ =>
          (fresh_card σ m tg).trans ((sum_le_sum fun g _ => hB (answers σ g m)).trans
            (le_of_eq (by rw [sum_const, card_univ, smul_eq_mul, mul_comm])))
    _ = Q * B * Fintype.card (X → Y) := by rw [sum_const, card_range, smul_eq_mul, mul_assoc]

/-- Two strategies agreeing on answer lists shorter than `n` get the same first `n` answers. -/
theorem answers_strat {σ σ' : List Y → X} {h : X → Y} {n : ℕ} (hs : ∀ as : List Y, as.length < n → σ' as = σ as) :
    ∀ i ≤ n, answers σ' h i = answers σ h i
  | 0, _ => rfl
  | i + 1, hi => by
    have hl : (answers σ h i).length < n := by rw [answers_length]; omega
    simp only [answers, answers_strat (n := n) hs i (by omega), hs _ hl]

/-- Two strategies agreeing on answer lists shorter than `n` make the same first `n` queries. -/
theorem queries_strat {σ σ' : List Y → X} {h : X → Y} {n : ℕ} (hs : ∀ as : List Y, as.length < n → σ' as = σ as) :
    queries σ' h n = queries σ h n := by
  have hq : ∀ i < n, query σ' h i = query σ h i := fun i hi => by
    have hl : (answers σ h i).length < n := by rw [answers_length]; exact hi
    simp only [query, answers_strat hs i hi.le, hs _ hl]
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (hq i hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, hq i hi⟩

/-- Non-vacuity of `LateHit`: a first query whose answer is its own target hits it. -/
example (σ : List Bool → Bool) (h : Bool → Bool) : LateHit σ h 1 fun _ => {h (σ [])} :=
  ⟨0, by omega, fun i hi => absurd hi (by omega), by simp [query, answers]⟩

/-- Mutation test: with no targets there is no late hit. -/
example (σ : List Bool → Bool) (h : Bool → Bool) (Q : ℕ) : ¬ LateHit σ h Q fun _ => ∅ := by
  rintro ⟨m, -, -, hm⟩
  simp at hm

/-- A late hit is not a collision: one query, which collides with nothing, answering a target fixed before it (a word
the prover wrote without computing it) is a late hit, so `LateHit` is charged beside `Coll`. -/
example (σ : List Bool → Bool) (h : Bool → Bool) : ¬ Coll σ h 1 ∧ LateHit σ h 1 fun _ => {h (σ [])} :=
  ⟨fun ⟨i, hi, i', hi', hne, _⟩ => hne (by rw [show i = 0 by omega, show i' = 0 by omega]),
    ⟨0, by omega, fun i hi => absurd hi (by omega), by simp [query, answers]⟩⟩

/-- Two strategies agreeing along the first's answers before `n` get the same first `n` answers. -/
theorem answers_along {σ σ' : List Y → X} {h : X → Y} {n : ℕ}
    (hs : ∀ i < n, σ' (answers σ h i) = σ (answers σ h i)) : ∀ i ≤ n, answers σ' h i = answers σ h i
  | 0, _ => rfl
  | i + 1, hi => by simp only [answers, answers_along hs i (by omega), hs i (by omega)]

/-- Two strategies agreeing along the first's answers before `n` make the same first `n` queries. -/
theorem queries_along {σ σ' : List Y → X} {h : X → Y} {n : ℕ}
    (hs : ∀ i < n, σ' (answers σ h i) = σ (answers σ h i)) : queries σ' h n = queries σ h n := by
  have hq : ∀ i < n, query σ' h i = query σ h i := fun i hi => by
    simp only [query, answers_along hs i hi.le, hs i hi]
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (hq i hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, hq i hi⟩

/-- The prover normalized: its own first `Q` queries, then the entries of `extra` at its first `Q` answers, one per
query (`default` past their end). -/
def normalize [Inhabited X] (σ : List Y → X) (Q : ℕ) (extra : List Y → List X) : List Y → X := fun as =>
  if as.length < Q then σ as else (extra (as.take Q)).getD (as.length - Q) default

theorem normalize_lt [Inhabited X] {σ : List Y → X} {Q : ℕ} {extra : List Y → List X} (as : List Y)
    (h : as.length < Q) : normalize σ Q extra as = σ as := if_pos h

/-- The normalized prover's first `n ≤ Q` answers are the prover's. -/
theorem answers_normalize [Inhabited X] (σ : List Y → X) (h : X → Y) {Q n : ℕ} (extra : List Y → List X)
    (hn : n ≤ Q) : answers (normalize σ Q extra) h n = answers σ h n :=
  answers_strat (fun as has => normalize_lt as has) n hn

/-- Every entry of `extra` at the prover's first `Q` answers is among the normalized prover's first `Q + m` queries,
`m` bounding `extra`'s length. -/
theorem extra_mem_queries [Inhabited X] (σ : List Y → X) (h : X → Y) (Q m : ℕ) (extra : List Y → List X)
    (hm : ∀ as, (extra as).length ≤ m) {x : X} (hx : x ∈ extra (answers σ h Q)) :
    x ∈ queries (normalize σ Q extra) h (Q + m) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  refine ⟨Q + j, by have := hm (answers σ h Q); omega, ?_⟩
  have hlen : (answers (normalize σ Q extra) h (Q + j)).length = Q + j := answers_length _ _ _
  have htake : (answers (normalize σ Q extra) h (Q + j)).take Q = answers σ h Q := by
    rw [answers_take _ _ (by omega), answers_normalize σ h extra le_rfl]
  simp only [query, normalize, hlen, show ¬ (Q + j < Q) by omega, if_false, Nat.add_sub_cancel_left, htake,
    List.getD_eq_getElem _ _ hj]

/-- Non-vacuity of `extra_mem_queries`' bound: a prover making no query of its own queries its one extra entry. -/
example (h : Bool → Bool) : true ∈ queries (normalize (fun _ => false) 0 fun _ => [true]) h 1 :=
  extra_mem_queries _ h 0 1 _ (fun _ => le_rfl) (List.mem_singleton_self _)

end LeanVMCircuits.Rec.Collision

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset Collision

theorem WinOn.mono {X V C R : Type} {ch : X → C} {re : X → R} {H : X → Fin 4 → V} {A B : Set X} (hAB : A ⊆ B)
    (h : WinOn ch re H A) : WinOn ch re H B := by
  obtain ⟨a, ha, b, hb, a', ha', b', hb', rest⟩ := h
  exact ⟨a, hAB ha, b, hAB hb, a', hAB ha', b', hAB hb', rest⟩

/-- Straight-line extraction: rows consistent with the oracle `H` with their inputs among the prover's first `Q`
queries (`hnorm`), whose outputs are answers to its first `n` queries or targets its first `n` answers fix (`hout`),
have their inputs among its first `n` queries, off a collision and a late hit: a row's input first queried at `a ≥ n`
answers its output, an earlier answer (a collision) or a target fixed before `a` (a late hit). -/
theorem oracleRows_of_late (H : (Fin 14 → K) → Fin 4 → K) (σ : List (Fin 4 → K) → Fin 14 → K) {Q n : ℕ}
    (tg : List (Fin 4 → K) → Finset (Fin 4 → K)) (htg : ∀ as bs, tg as ⊆ tg (as ++ bs)) {s : State}
    {drop : List ℕ → Bool} {L : ℕ → Prop} {val : Val} (hnorm : OracleRows H (queries σ H Q) s drop L val)
    (hout : ∀ row ∈ s.hash, drop row = false → RowLive L row →
      rowOut val row ∈ tg (answers σ H n) ∨ ∃ i < n, rowOut val row = H (query σ H i))
    (hc : ¬ Coll σ H Q) (hl : ¬ LateHit σ H Q tg) : OracleRows H (queries σ H n) s drop L val := by
  intro row hr hd hlv
  obtain ⟨⟨i, hi, hx⟩, hy⟩ := hnorm row hr hd hlv
  refine ⟨?_, hy⟩
  obtain ⟨a, ha, hqa, hfa⟩ := first_fresh σ H i
  by_cases han : a < n
  · exact ⟨a, han, hqa.trans hx⟩
  · exfalso
    have hya : H (query σ H a) = rowOut val row := by rw [hqa, hx, hy]
    rcases hout row hr hd hlv with ht | ⟨j, hj, hjy⟩
    · have e : answers σ H n ++ (answers σ H a).drop n = answers σ H a := by
        rw [← answers_take σ H (show n ≤ a by omega), List.take_append_drop]
      have hsub := htg (answers σ H n) ((answers σ H a).drop n)
      rw [e] at hsub
      exact hl ⟨a, by omega, hfa, by rw [hya]; exact hsub ht⟩
    · exact hc ⟨a, by omega, j, by omega, fun he => hfa j (by omega) he.symm, hya.trans hjy⟩

/-- The old prover-model premise, every row the prefix binds an oracle row among the first `n` queries, gives `hout`
with any targets: `oracleRows_of_late`'s premise is weaker. -/
theorem out_of_prefix (H : (Fin 14 → K) → Fin 4 → K) (σ : List (Fin 4 → K) → Fin 14 → K) {n : ℕ}
    (tg : List (Fin 4 → K) → Finset (Fin 4 → K)) {s : State} {drop : List ℕ → Bool} {L : ℕ → Prop} {val : Val}
    (hv : OracleRows H (queries σ H n) s drop L val) :
    ∀ row ∈ s.hash, drop row = false → RowLive L row →
      rowOut val row ∈ tg (answers σ H n) ∨ ∃ i < n, rowOut val row = H (query σ H i) := fun row hr hd hl =>
  let ⟨⟨i, hi, hx⟩, hy⟩ := hv row hr hd hl
  Or.inr ⟨i, hi, hy.trans (congrArg H hx.symm)⟩

variable {c : Cert} {s : State} {T : ℕ} {val : (ℕ → K) → Val}

/-- One execution's event: among the first `Q` compression queries of the prover `σ ρ`, a collision, a window hit or
a late hit on the targets `tg ρ`. -/
def ExecBad (H : (Fin 14 → K) → Fin 4 → K) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ)
    (tg : (ℕ → K) → List (Fin 4 → K) → Finset (Fin 4 → K)) (ρ : ℕ → K) : Prop :=
  Coll (σ ρ) H Q ∨ WinHit chainOf restOf (σ ρ) H Q ∨ LateHit (σ ρ) H Q (tg ρ)

/-- The prover model's collision premise by straight-line extraction: a run's `cr`, off both executions' `ExecBad`,
from a causal prover (`hcaus`: its first `n ρ k ownL` queries, those before the squeeze after time `k`, the same at
every oracle agreeing with `ρ` on the answers drawn by `k` and on those drawn at `k + 1` but the words `ownL`, asked
along its own answers), normalized (`hnorm`: the rows the prefix binds consistent with `H`, their inputs among its first
`Q` queries), whose rows the prefix binds output words fixed by then (`hout`: answers to its queries before the
squeeze, or targets its answers by then fix, `tg` growing with the answers). -/
theorem Run.cr_of_extract (H : (Fin 14 → K) → Fin 4 → K) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ)
    (n : (ℕ → K) → ℕ → List ℕ → ℕ) (hn : ∀ ρ k ownL, n ρ k ownL ≤ Q)
    (tg : (ℕ → K) → List (Fin 4 → K) → Finset (Fin 4 → K)) (htg : ∀ ρ as bs, tg ρ as ⊆ tg ρ (as ++ bs))
    (hcaus : ∀ ρ ρ' k ownL, (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      n ρ' k ownL = n ρ k ownL ∧ ∀ i < n ρ k ownL, σ ρ' (answers (σ ρ) H i) = σ ρ (answers (σ ρ) H i))
    (hnorm : ∀ ρ k ownL, OracleRows H (queries (σ ρ) H Q) s (dropOf s (c.transcripts.getD T default))
      (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL))
      (val ρ))
    (hout : ∀ ρ k ownL, ∀ row ∈ s.hash, dropOf s (c.transcripts.getD T default) row = false →
      RowLive (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++
        sibSeeds s (c.transcripts.getD T default) k ownL)) row →
      rowOut (val ρ) row ∈ tg ρ (answers (σ ρ) H (n ρ k ownL)) ∨
        ∃ i < n ρ k ownL, rowOut (val ρ) row = H (query (σ ρ) H i)) :
    ∀ ρ ρ' k (ownL : List ℕ), (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      ¬ ExecBad H σ Q tg ρ → ¬ ExecBad H σ Q tg ρ' →
      PairCR c s T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL)
        (val ρ) (val ρ') := by
  intro ρ ρ' k ownL h1 h2 hC hC'
  simp only [ExecBad, not_or] at hC hC'
  obtain ⟨hnn, hσ⟩ := hcaus ρ ρ' k ownL h1 h2
  have hv := oracleRows_of_late H (σ ρ) (tg ρ) (htg ρ) (hnorm ρ k ownL) (hout ρ k ownL) hC.1 hC.2.2
  have hv' := oracleRows_of_late H (σ ρ') (tg ρ') (htg ρ') (hnorm ρ' k ownL) (hout ρ' k ownL) hC'.1 hC'.2.2
  rw [hnn, queries_along hσ] at hv'
  have hsub : queries (σ ρ) H (n ρ k ownL) ⊆ queries (σ ρ) H Q := fun x ⟨i, hi, hx⟩ =>
    ⟨i, lt_of_lt_of_le hi (hn ρ k ownL), hx⟩
  exact pairCR_of_oracle H _ ((injOn_of_not_coll hC.1).mono hsub) (fun hw => hC.2.1 (WinOn.mono hsub hw)) hv hv'

/-- Non-vacuity of the prover model's premises: no live rows meet `hnorm` and `hout` for every prover. -/
example (H : (Fin 14 → K) → Fin 4 → K) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ)
    (n : (ℕ → K) → ℕ → List ℕ → ℕ) (tg : (ℕ → K) → List (Fin 4 → K) → Finset (Fin 4 → K))
    (hnone : ∀ k ownL row, ¬ RowLive (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++
      sibSeeds s (c.transcripts.getD T default) k ownL)) row) :
    (∀ ρ k ownL, OracleRows H (queries (σ ρ) H Q) s (dropOf s (c.transcripts.getD T default))
      (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL))
      (val ρ)) ∧
    (∀ ρ k ownL, ∀ row ∈ s.hash, dropOf s (c.transcripts.getD T default) row = false →
      RowLive (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++
        sibSeeds s (c.transcripts.getD T default) k ownL)) row →
      rowOut (val ρ) row ∈ tg ρ (answers (σ ρ) H (n ρ k ownL)) ∨
        ∃ i < n ρ k ownL, rowOut (val ρ) row = H (query (σ ρ) H i)) :=
  ⟨fun _ k ownL row _ _ hl => absurd hl (hnone k ownL row), fun _ k ownL row _ _ hl => absurd hl (hnone k ownL row)⟩

/-- `Run.cr_of_extract` without `hnorm`: the prover normalized to query, after its own first `Q` queries, the input of
every hash row of its output (`Collision.normalize`), so every committed row is among its first `Q + |rows|` queries.
Asked instead: its output is a function `out` of its first `Q` compression answers (`hval`), and its rows but the
transcript's own are consistent with the oracle (`hrows`, the ideal model's compression). Causality and `hout` are the
prover's own, the normalized prover agreeing with it on its first `Q` queries. Off both executions' `ExecBad` of the
normalized prover's `Q + |rows|` queries, `cr` holds. -/
theorem Run.cr_of_normal (H : (Fin 14 → K) → Fin 4 → K) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ)
    (n : (ℕ → K) → ℕ → List ℕ → ℕ) (hn : ∀ ρ k ownL, n ρ k ownL ≤ Q)
    (tg : (ℕ → K) → List (Fin 4 → K) → Finset (Fin 4 → K)) (htg : ∀ ρ as bs, tg ρ as ⊆ tg ρ (as ++ bs))
    (hcaus : ∀ ρ ρ' k ownL, (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      n ρ' k ownL = n ρ k ownL ∧ ∀ i < n ρ k ownL, σ ρ' (answers (σ ρ) H i) = σ ρ (answers (σ ρ) H i))
    (out : (ℕ → K) → List (Fin 4 → K) → Val) (hval : ∀ ρ, val ρ = out ρ (answers (σ ρ) H Q))
    (hrows : ∀ ρ, ∀ row ∈ s.hash, dropOf s (c.transcripts.getD T default) row = false →
      rowOut (val ρ) row = H (rowIn (val ρ) row))
    (hout : ∀ ρ k ownL, ∀ row ∈ s.hash, dropOf s (c.transcripts.getD T default) row = false →
      RowLive (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++
        sibSeeds s (c.transcripts.getD T default) k ownL)) row →
      rowOut (val ρ) row ∈ tg ρ (answers (σ ρ) H (n ρ k ownL)) ∨
        ∃ i < n ρ k ownL, rowOut (val ρ) row = H (query (σ ρ) H i)) :
    ∀ ρ ρ' k (ownL : List ℕ), (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      ¬ ExecBad H (fun ρ => normalize (σ ρ) Q fun as => s.hash.toList.map (rowIn (out ρ as))) (Q + s.hash.size) tg ρ →
      ¬ ExecBad H (fun ρ => normalize (σ ρ) Q fun as => s.hash.toList.map (rowIn (out ρ as))) (Q + s.hash.size) tg ρ' →
      PairCR c s T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL)
        (val ρ) (val ρ') := by
  refine Run.cr_of_extract H (fun ρ => normalize (σ ρ) Q fun as => s.hash.toList.map (rowIn (out ρ as)))
    (Q + s.hash.size) n (fun ρ k ownL => (hn ρ k ownL).trans (Nat.le_add_right _ _)) tg htg ?_ ?_ ?_
  · intro ρ ρ' k ownL h1 h2
    obtain ⟨hnn, hσ⟩ := hcaus ρ ρ' k ownL h1 h2
    refine ⟨hnn, fun i hi => ?_⟩
    have hiQ : i < Q := lt_of_lt_of_le hi (hn ρ k ownL)
    have hlen : (answers (σ ρ) H i).length < Q := by rw [answers_length]; exact hiQ
    rw [answers_normalize (σ ρ) H _ hiQ.le, normalize_lt _ hlen, normalize_lt _ hlen]
    exact hσ i hi
  · intro ρ k ownL row hr hd _
    refine ⟨?_, hrows ρ row hr hd⟩
    rw [hval ρ]
    exact extra_mem_queries (σ ρ) H Q s.hash.size _ (fun as => by simp)
      (List.mem_map.mpr ⟨row, Array.mem_toList_iff.mpr hr, rfl⟩)
  · intro ρ k ownL row hr hd hl
    rcases hout ρ k ownL row hr hd hl with ht | ⟨i, hi, hy⟩
    · left
      rwa [answers_normalize (σ ρ) H _ (hn ρ k ownL)]
    · right
      refine ⟨i, hi, hy.trans (congrArg H ?_)⟩
      have hiQ : i < Q := lt_of_lt_of_le hi (hn ρ k ownL)
      simp only [query]
      rw [answers_normalize (σ ρ) H _ hiQ.le, normalize_lt _ (by rw [answers_length]; exact hiQ)]

/-- Non-vacuity of `cr_of_normal`'s new premises: a prover whose output is fixed meets `hval`, and on a circuit with no
hash rows `hrows`. -/
example (H : (Fin 14 → K) → Fin 4 → K) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ) (v : Val)
    (hs : s.hash = #[]) :
    (∀ ρ : ℕ → K, (fun _ => v) ρ = (fun _ _ => v : (ℕ → K) → List (Fin 4 → K) → Val) ρ (answers (σ ρ) H Q)) ∧
    ∀ ρ : ℕ → K, ∀ row ∈ s.hash, dropOf s (c.transcripts.getD T default) row = false →
      rowOut ((fun _ => v) ρ) row = H (rowIn ((fun _ => v) ρ) row) :=
  ⟨fun _ => rfl, fun _ row hr => absurd hr (by simp [hs])⟩

/-! Causality from staging. -/

/-- A staged prover: at its answers `as` it is at transcript time `tm ρ as`, and its query there and that time read the
transcript's challenges `seeds` only through those drawn by any time `k` it has not passed: oracles agreeing on the
challenges drawn by `k`, at answers where the prover is at time at most `k`, give it the same query and time. A
Fiat-Shamir prover is staged: before it asks for the challenge after time `k` it has seen none drawn later. -/
def Staged (seeds : List (ℕ × ℕ)) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K)
    (tm : (ℕ → K) → List (Fin 4 → K) → ℕ) : Prop :=
  ∀ ρ ρ' k as, (∀ p ∈ seeds, p.1 ≤ k → ρ p.2 = ρ' p.2) → tm ρ as ≤ k → σ ρ' as = σ ρ as ∧ tm ρ' as = tm ρ as

section Stage

variable (H : (Fin 14 → K) → Fin 4 → K) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K)
  (tm : (ℕ → K) → List (Fin 4 → K) → ℕ) (Q k : ℕ) (ρ : ℕ → K)

open Classical in
/-- A staged prover's queries before it passes time `k`, at most `Q`: the first query at which its time is past `k`. -/
noncomputable def stageN : ℕ := Nat.find (⟨Q, Or.inl rfl⟩ : ∃ i, i = Q ∨ k < tm ρ (answers (σ ρ) H i))

theorem stageN_eq_iff (m : ℕ) : stageN H σ tm Q k ρ = m ↔
    (m = Q ∨ k < tm ρ (answers (σ ρ) H m)) ∧ ∀ i < m, ¬ (i = Q ∨ k < tm ρ (answers (σ ρ) H i)) := by
  classical
  exact Nat.find_eq_iff _

theorem stageN_spec : stageN H σ tm Q k ρ = Q ∨ k < tm ρ (answers (σ ρ) H (stageN H σ tm Q k ρ)) :=
  ((stageN_eq_iff H σ tm Q k ρ _).mp rfl).1

theorem stageN_le : stageN H σ tm Q k ρ ≤ Q := by
  classical
  exact Nat.find_min' _ (Or.inl rfl)

theorem stageN_lt {i : ℕ} (hi : i < stageN H σ tm Q k ρ) : tm ρ (answers (σ ρ) H i) ≤ k :=
  not_lt.mp fun h => ((stageN_eq_iff H σ tm Q k ρ _).mp rfl).2 i hi (Or.inr h)

end Stage

/-- Causality from staging: oracles agreeing on the challenges drawn by `k` give a staged prover the same queries
before it passes `k`, along its answers, and it passes `k` at the same query. -/
theorem hcaus_of_staged (H : (Fin 14 → K) → Fin 4 → K) {seeds : List (ℕ × ℕ)}
    {σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K} {tm : (ℕ → K) → List (Fin 4 → K) → ℕ} (hst : Staged seeds σ tm)
    (Q k : ℕ) (ρ ρ' : ℕ → K) (h1 : ∀ p ∈ seeds, p.1 ≤ k → ρ p.2 = ρ' p.2) :
    stageN H σ tm Q k ρ' = stageN H σ tm Q k ρ ∧
      ∀ i < stageN H σ tm Q k ρ, σ ρ' (answers (σ ρ) H i) = σ ρ (answers (σ ρ) H i) := by
  have hag : ∀ i < stageN H σ tm Q k ρ, σ ρ' (answers (σ ρ) H i) = σ ρ (answers (σ ρ) H i) ∧
      tm ρ' (answers (σ ρ) H i) = tm ρ (answers (σ ρ) H i) :=
    fun i hi => hst ρ ρ' k _ h1 (stageN_lt H σ tm Q k ρ hi)
  have hans := answers_along (h := H) (fun i hi => (hag i hi).1)
  refine ⟨(stageN_eq_iff H σ tm Q k ρ' _).mpr ⟨?_, fun i hi hP => ?_⟩, fun i hi => (hag i hi).1⟩
  · rcases stageN_spec H σ tm Q k ρ with hQ | hk
    · exact Or.inl hQ
    · right
      rw [hans _ le_rfl]
      by_contra hle
      have := (hst ρ' ρ k _ (fun p hp hk' => (h1 p hp hk').symm) (not_lt.mp hle)).2
      omega
  · rcases hP with hQ | hk
    · have := stageN_le H σ tm Q k ρ
      omega
    · rw [hans i hi.le, (hag i hi).2] at hk
      exact absurd (stageN_lt H σ tm Q k ρ hi) (not_le.mpr hk)

/-- `Run.cr_of_normal` for a staged prover: causality is not asked, the queries before the squeeze after time `k`
being those the prover makes before it passes `k` (`stageN`). The premises left: the prover is staged (`Staged`), its
output a function of its first `Q` answers, its rows consistent with the oracle, and its rows the prefix binds output
words fixed by then (`hout`). -/
theorem Run.cr_of_staged (H : (Fin 14 → K) → Fin 4 → K) (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ)
    (tm : (ℕ → K) → List (Fin 4 → K) → ℕ) (hst : Staged (chalSeeds s (c.transcripts.getD T default)) σ tm)
    (tg : (ℕ → K) → List (Fin 4 → K) → Finset (Fin 4 → K)) (htg : ∀ ρ as bs, tg ρ as ⊆ tg ρ (as ++ bs))
    (out : (ℕ → K) → List (Fin 4 → K) → Val) (hval : ∀ ρ, val ρ = out ρ (answers (σ ρ) H Q))
    (hrows : ∀ ρ, ∀ row ∈ s.hash, dropOf s (c.transcripts.getD T default) row = false →
      rowOut (val ρ) row = H (rowIn (val ρ) row))
    (hout : ∀ ρ k (ownL : List ℕ), ∀ row ∈ s.hash, dropOf s (c.transcripts.getD T default) row = false →
      RowLive (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++
        sibSeeds s (c.transcripts.getD T default) k ownL)) row →
      rowOut (val ρ) row ∈ tg ρ (answers (σ ρ) H (stageN H σ tm Q k ρ)) ∨
        ∃ i < stageN H σ tm Q k ρ, rowOut (val ρ) row = H (query (σ ρ) H i)) :
    ∀ ρ ρ' k (ownL : List ℕ), (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      ¬ ExecBad H (fun ρ => normalize (σ ρ) Q fun as => s.hash.toList.map (rowIn (out ρ as))) (Q + s.hash.size) tg ρ →
      ¬ ExecBad H (fun ρ => normalize (σ ρ) Q fun as => s.hash.toList.map (rowIn (out ρ as))) (Q + s.hash.size) tg ρ' →
      PairCR c s T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL)
        (val ρ) (val ρ') :=
  Run.cr_of_normal H σ Q (fun ρ k _ => stageN H σ tm Q k ρ) (fun ρ k _ => stageN_le H σ tm Q k ρ) tg htg
    (fun ρ ρ' k _ h1 _ => hcaus_of_staged H hst Q k ρ ρ' h1) out hval hrows hout

/-- Non-vacuity of `Staged`: a prover reading no challenge, at time zero throughout, is staged. -/
example (seeds : List (ℕ × ℕ)) (σ₀ : List (Fin 4 → K) → Fin 14 → K) : Staged seeds (fun _ => σ₀) fun _ _ => 0 :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl⟩

/-- Mutation test of `Staged`: a prover querying the challenge word drawn at time one while at time zero is not
staged, when the word can vary. -/
example (ρ₀ ρ₁ : ℕ → K) (h4 : ρ₀ 4 = ρ₁ 4) (h : ρ₀ 5 ≠ ρ₁ 5) :
    ¬ Staged [(0, 4), (1, 5)] (fun ρ _ _ => ρ 5) fun _ _ => 0 := by
  intro hst
  have := (hst ρ₀ ρ₁ 0 [] (fun p hp hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h4
    · simp at hk) le_rfl).1
  exact h (congrFun this 0).symm

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Finset Collision

variable {Ω₀ X V : Type}

open Classical in
/-- The late-hit event over outcomes pairing other coins `ω.1` with the compression oracle `ω.2`: one of the first `Q`
first compression queries of the prover `σ ω.1` answers a target `tg ω.1` fixed by the answers before it. -/
noncomputable def lateEvent [Fintype Ω₀] [Fintype X] [Fintype V] (tg : Ω₀ → List (Fin 4 → V) → Finset (Fin 4 → V))
    (σ : Ω₀ → List (Fin 4 → V) → X) (Q : ℕ) : Finset (Ω₀ × (X → Fin 4 → V)) :=
  univ.filter fun ω => LateHit (σ ω.1) ω.2 Q (tg ω.1)

/-- The late-hit term for `Q` compression queries and at most `B` targets: `Q · B / |V|^4`. -/
noncomputable def epsLate (V : Type) [Fintype V] (Q B : ℕ) : ℚ≥0 :=
  ((Q * B : ℕ) : ℚ≥0) / ((Fintype.card V ^ 4 : ℕ) : ℚ≥0)

open Classical in
/-- `lateEvent`'s fraction of the outcomes is at most `epsLate`. -/
theorem lateEvent_frac [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V]
    (tg : Ω₀ → List (Fin 4 → V) → Finset (Fin 4 → V)) (σ : Ω₀ → List (Fin 4 → V) → X) (Q : ℕ) {B : ℕ}
    (hB : ∀ ρ as, #(tg ρ as) ≤ B) :
    ((lateEvent tg σ Q).card : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsLate V Q B := by
  refine frac_le (by positivity) ?_
  have hY : Fintype.card (Fin 4 → V) = Fintype.card V ^ 4 := by simp
  have hc : (lateEvent tg σ Q).card = ∑ a, (univ.filter fun h => LateHit (σ a) h Q (tg a)).card :=
    card_filter_prod fun a h => LateHit (σ a) h Q (tg a)
  rw [hc, sum_mul, Fintype.card_prod]
  calc ∑ a, (univ.filter fun h => LateHit (σ a) h Q (tg a)).card * Fintype.card V ^ 4
      ≤ ∑ _a : Ω₀, Q * B * Fintype.card (X → Fin 4 → V) := sum_le_sum fun a _ => by
        rw [← hY]
        exact late_card (σ a) Q (tg a) (hB a)
    _ = Q * B * (Fintype.card Ω₀ * Fintype.card (X → Fin 4 → V)) := by
        rw [sum_const, card_univ, smul_eq_mul]
        ring

open Classical in
/-- Off `crEvent` and `lateEvent`, the execution at `ω.1` is off `Bind.ExecBad` at the oracle `ω.2`: what
`Bind.Run.cr_of_extract` asks. -/
theorem not_mem_exec [Fintype Ω₀] (σ : Ω₀ → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ)
    (tg : Ω₀ → List (Fin 4 → K) → Finset (Fin 4 → K)) {ω : Ω₀ × ((Fin 14 → K) → Fin 4 → K)}
    (h : ω ∉ crEvent chainOf restOf σ Q ∪ lateEvent tg σ Q) :
    ¬ (Coll (σ ω.1) ω.2 Q ∨ WinHit chainOf restOf (σ ω.1) ω.2 Q ∨ LateHit (σ ω.1) ω.2 Q (tg ω.1)) := by
  classical
  simp only [crEvent, lateEvent, mem_union, mem_filter, mem_univ, true_and, not_or] at h ⊢
  exact ⟨h.1.1, h.1.2, h.2⟩

end LeanVMCircuits.Rec.Edges

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset Edges Bind Collision

/-- A fraction over pairs at most `b` when it is at every second coordinate. -/
theorem frac_prod_le {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (S : Finset (A × B))
    (b : ℚ≥0) (h : ∀ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) / Fintype.card A ≤ b) :
    (#S : ℚ≥0) / Fintype.card (A × B) ≤ b := by
  rcases isEmpty_or_nonempty A with hA | hA
  · simp [Fintype.card_prod, Fintype.card_eq_zero]
  have hcA : (0 : ℚ≥0) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hS : (#S : ℚ≥0) = ∑ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) := by
    have : #S = ∑ y : B, #{x : A | (x, y) ∈ S} := by
      rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
      refine sum_congr rfl fun y _ => ?_
      refine card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p hp q hq he => ?_) (fun x hx => ⟨(x, y), ?_, rfl⟩)
      · simp only [mem_filter, mem_univ, true_and] at hp ⊢
        rw [← hp.2]
        exact hp.1
      · simp only [mem_filter] at hp hq
        exact Prod.ext he (hp.2.trans hq.2.symm)
      · simp only [mem_filter, mem_univ, true_and] at hx ⊢
        simpa using hx
    exact_mod_cast this
  rw [hS, Fintype.card_prod, Nat.cast_mul, sum_div]
  calc ∑ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) / (Fintype.card A * Fintype.card B)
      = ∑ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) / Fintype.card A / Fintype.card B := by
        refine sum_congr rfl fun y _ => ?_
        rw [div_div]
    _ ≤ ∑ _y : B, b / Fintype.card B := sum_le_sum fun y _ => div_le_div_of_nonneg_right (h y) (by positivity)
    _ ≤ b := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos (Fintype.card B) with h0 | h0
        · simp [h0]
        · rw [mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]

section Exec

variable {ι : Type}

open Classical in
/-- The tree's bound per execution: over outcomes pairing the oracle `ρ` on the transcripts' words `U` with the
compression oracle `H`, child `v`'s `crBad` its execution's collision, window and late-hit events among its first `Q v`
compression queries (`Edges.crEvent` and `Edges.lateEvent`, `σ v ρ` its prover at `ρ`, `tg v ρ` the at most `B v`
targets its answers fix), charged once per child at `Edges.epsCR K (Q v) + Edges.epsLate K (Q v) (B v)`; check `j`'s
`testBad` at most `epsTest v j` of the `ρ` at every `H` (the round theorems' bounds off the executions' event,
`Bind.sumcheck_run_sound_at` and the like); the bus's and constraint batch's draw events at most `epsBus v` and
`epsBatch v` of the `ρ` at every `H` (`busRun_frac`, `batchRun_frac`). The bound is the sum over the nodes of their
reduction's `bad` fraction and those bounds, with the PCS bound `epsPCS v` (#551). -/
theorem tree_sound_exec (U : Finset ℕ) (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : (U → K) × ((Fin 14 → K) → Fin 4 → K) → ℕ → Fin 4 → K)
    (val : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (batchBad : ι → Finset ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (draw : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Fin 5 → E)
    (wit : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveRows T cert (fun v => stmtFirst (t v)) os L slot stRoot val P batchBad draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (σ : ι → (U → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ι → ℕ)
    (tg : ι → (U → K) → List (Fin 4 → K) → Finset (Fin 4 → K)) (B : ι → ℕ) (hB : ∀ v ρ as, #(tg v ρ as) ≤ B v)
    (hcrEq : ∀ v, P.crBad v = crEvent chainOf restOf (σ v) (Q v) ∪ lateEvent (tg v) (σ v) (Q v))
    (epsTest : ι → ℕ → ℚ≥0)
    (htest : ∀ v ∈ T.nodes, ∀ j < P.J v, ∀ H, (#{ρ : U → K | (ρ, H) ∈ P.testBad v j} : ℚ≥0) /
      Fintype.card (U → K) ≤ epsTest v j)
    (epsPCS epsBus epsBatch : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hbus : ∀ v ∈ T.nodes, ∀ H, (#{ρ : U → K | (ρ, H) ∈ busBad (stmtFirst (t v)) (wit v) (draw v)} : ℚ≥0) /
      Fintype.card (U → K) ≤ epsBus v)
    (hbatch : ∀ v ∈ T.nodes, ∀ H, (#{ρ : U → K | (ρ, H) ∈ batchBad v} : ℚ≥0) / Fintype.card (U → K) ≤
      epsBatch v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤
      ∑ v ∈ T.nodes, ((bad v).card / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) +
        ∑ j ∈ range (P.J v), epsTest v j + epsPCS v + (Edges.epsCR K (Q v) + Edges.epsLate K (Q v) (B v)) + epsBus v +
          epsBatch v) := by
  have hcr : ∀ v ∈ T.nodes, ((P.crBad v).card : ℚ≥0) / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤
      Edges.epsCR K (Q v) + Edges.epsLate K (Q v) (B v) := fun v _ => by
    rw [hcrEq v]
    set M := Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K))
    have h1 : ((crEvent chainOf restOf (σ v) (Q v)).card : ℚ≥0) / M ≤ Edges.epsCR K (Q v) := by
      convert crEvent_frac (Ω₀ := U → K) chainOf restOf (fun _ _ hr hc => input_ext hc hr) (σ v) (Q v)
    have h2 : ((lateEvent (tg v) (σ v) (Q v)).card : ℚ≥0) / M ≤ Edges.epsLate K (Q v) (B v) := by
      convert lateEvent_frac (Ω₀ := U → K) (tg v) (σ v) (Q v) (hB v)
    have hu : ((crEvent chainOf restOf (σ v) (Q v) ∪ lateEvent (tg v) (σ v) (Q v)).card : ℚ≥0) ≤
        (crEvent chainOf restOf (σ v) (Q v)).card + (lateEvent (tg v) (σ v) (Q v)).card := by
      exact_mod_cast card_union_le _ _
    calc ((crEvent chainOf restOf (σ v) (Q v) ∪ lateEvent (tg v) (σ v) (Q v)).card : ℚ≥0) / M
        ≤ ((crEvent chainOf restOf (σ v) (Q v)).card + (lateEvent (tg v) (σ v) (Q v)).card : ℚ≥0) / M :=
          div_le_div_of_nonneg_right hu (by positivity)
      _ = ((crEvent chainOf restOf (σ v) (Q v)).card : ℚ≥0) / M + ((lateEvent (tg v) (σ v) (Q v)).card : ℚ≥0) / M :=
          add_div _ _ _
      _ ≤ _ := add_le_add h1 h2
  have hbus' : ∀ v ∈ T.nodes, ((busBad (stmtFirst (t v)) (wit v) (draw v)).card : ℚ≥0) /
      Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤ epsBus v := fun v hv => by
    convert frac_prod_le _ _ (hbus v hv)
  have hbatch' : ∀ v ∈ T.nodes, ((batchBad v).card : ℚ≥0) /
      Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤ epsBatch v := fun v hv => by
    convert frac_prod_le _ _ (hbatch v hv)
  refine (tree_sound_bound T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP batchBad draw wit hval
    hlink tD tM bad hstep hroot epsPCS (fun v => Edges.epsCR K (Q v) + Edges.epsLate K (Q v) (B v)) epsBus epsBatch hpcs
    hcr hbus' hbatch').trans
    (sum_le_sum fun v hv => ?_)
  have hj : ∑ j ∈ range (P.J v), ((P.testBad v j).card : ℚ≥0) /
      Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤ ∑ j ∈ range (P.J v), epsTest v j :=
    sum_le_sum fun j hjr => frac_prod_le _ _ (htest v hv j (mem_range.mp hjr))
  simp only [add_div, Nat.cast_sum, sum_div]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hj) le_rfl) le_rfl) le_rfl) le_rfl

/-- The per-child terms rearranged: the reduction's, checks', bus's and batch's together, then the rest. -/
theorem add_rearr {a b c g h e f x : ℚ≥0} (hx : a + b + e + f ≤ x) : a + b + c + (g + h) + e + f ≤ x + c + g + h :=
  calc a + b + c + (g + h) + e + f = (a + b + e + f) + (c + g + h) := by abel
    _ ≤ x + (c + g + h) := add_le_add hx le_rfl
    _ = x + c + g + h := by abel

open Classical in
/-- The end-to-end bound for one tree: `tree_sound_exec` with each child's PCS term #551's bound (`Edges.Pcs551`, by
`Edges.pcsBound_of_551`) and its reduction's, checks', bus's and batch's terms together at most `D v / |E|` (`hD`: the
round theorems' `n · d / |E|` and the like, `busRun_frac`'s `4 N / |E|`, `batchRun_frac`'s `(n + 67) / |E|`). Per
child: `D v / |E|`, #551's `∑ k, finalBound (Q_k)`, and the execution's `epsCR K (Q v) + epsLate K (Q v) (B v)`. -/
theorem tree_sound_end {Node Digest Coins : Type} [Fintype Node] [DecidableEq Node] [Fintype Digest]
    [DecidableEq Digest] [Fintype Coins] [DecidableEq Coins] (U : Finset ℕ) (T : TreeSound.Tree ι)
    (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : (U → K) × ((Fin 14 → K) → Fin 4 → K) → ℕ → Fin 4 → K)
    (val : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (batchBad : ι → Finset ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (draw : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Fin 5 → E)
    (wit : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveRows T cert (fun v => stmtFirst (t v)) os L slot stRoot val P batchBad draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (σ : ι → (U → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ι → ℕ)
    (tg : ι → (U → K) → List (Fin 4 → K) → Finset (Fin 4 → K)) (B : ι → ℕ) (hB : ∀ v ρ as, #(tg v ρ as) ≤ B v)
    (hcrEq : ∀ v, P.crBad v = crEvent chainOf restOf (σ v) (Q v) ∪ lateEvent (tg v) (σ v) (Q v))
    (epsTest : ι → ℕ → ℚ≥0)
    (htest : ∀ v ∈ T.nodes, ∀ j < P.J v, ∀ H, (#{ρ : U → K | (ρ, H) ∈ P.testBad v j} : ℚ≥0) /
      Fintype.card (U → K) ≤ epsTest v j)
    (m : ∀ v, Pcs551 (Node := Node) (Digest := Digest) (Coins := Coins) P v) (epsBus epsBatch : ι → ℚ≥0)
    (hbus : ∀ v ∈ T.nodes, ∀ H, (#{ρ : U → K | (ρ, H) ∈ busBad (stmtFirst (t v)) (wit v) (draw v)} : ℚ≥0) /
      Fintype.card (U → K) ≤ epsBus v)
    (hbatch : ∀ v ∈ T.nodes, ∀ H, (#{ρ : U → K | (ρ, H) ∈ batchBad v} : ℚ≥0) / Fintype.card (U → K) ≤
      epsBatch v) (D : ι → ℕ)
    (hD : ∀ v ∈ T.nodes, ((bad v).card : ℚ≥0) / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) +
      ∑ j ∈ range (P.J v), epsTest v j + epsBus v + epsBatch v ≤ (D v : ℚ≥0) / Fintype.card E) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤
      ∑ v ∈ T.nodes, ((D v : ℚ≥0) / Fintype.card E + (∑ k, finalBound ((m v).Q k)).toNNRat +
        Edges.epsCR K (Q v) + Edges.epsLate K (Q v) (B v)) := by
  refine (tree_sound_exec U T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP batchBad draw wit hval
    hlink tD tM bad hstep hroot σ Q tg B hB hcrEq epsTest htest _ epsBus epsBatch (pcsBound_of_551 P m) hbus
    hbatch).trans (sum_le_sum fun v hv => ?_)
  exact add_rearr (hD v hv)

end Exec

end LeanVMCircuits.Rec.AirLink

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Bind

/-- `|E| = 2^192`: three coordinates over `K`. -/
theorem card_E : Fintype.card E = 2 ^ 192 := by
  rw [← Fintype.card_of_bijective (f := fun p : K × K × K => toE p.1 p.2.1 p.2.2)
    ⟨fun p q h => by
      obtain ⟨h0, h1, h2⟩ := toE_injective _ _ _ _ _ _ h
      exact Prod.ext h0 (Prod.ext h1 h2), fun e => by
      obtain ⟨a, b, c, h⟩ := toE_surjective e
      exact ⟨(a, b, c), h⟩⟩]
  simp [Fintype.card_prod, card_K]

/-- `epsCR` grows with the number of queries. -/
theorem epsCR_mono (V : Type) [Fintype V] {Q Q' : ℕ} (h : Q ≤ Q') : epsCR V Q ≤ epsCR V Q' := by
  unfold epsCR
  gcongr <;> omega

/-- `epsLate` grows with the number of queries and of targets. -/
theorem epsLate_mono (V : Type) [Fintype V] {Q Q' B B' : ℕ} (h : Q ≤ Q') (hB : B ≤ B') :
    epsLate V Q B ≤ epsLate V Q' B' := by
  unfold epsLate
  gcongr

/-- The terms the tree's bound proves per child at deployed sizes: its checks', bus's and batch's bounds, at most
`2^40 / |E|` together, and one execution's `epsCR K Q + epsLate K Q B` with at most `2^86` targets. -/
theorem exec_bound_deployed {Q D B : ℕ} (hD : D ≤ 2 ^ 40) (hB : B ≤ 2 ^ 86) :
    (Q ≤ 2 ^ 84 → (D : ℚ≥0) / Fintype.card E + epsCR K Q + epsLate K Q B ≤ 1 / 2) ∧
    (Q ≤ 2 ^ 82 → (D : ℚ≥0) / Fintype.card E + epsCR K Q + epsLate K Q B ≤ 1 / 2 ^ 7) ∧
    (Q ≤ 2 ^ 74 → (D : ℚ≥0) / Fintype.card E + epsCR K Q + epsLate K Q B ≤ 1 / 2 ^ 32) ∧
    (Q ≤ 2 ^ 63 → (D : ℚ≥0) / Fintype.card E + epsCR K Q + epsLate K Q B ≤ 1 / 2 ^ 64) := by
  have hDE : (D : ℚ≥0) / Fintype.card E ≤ 2 ^ 40 / 2 ^ 192 := by
    rw [card_E]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hD) (by positivity)
  have key : ∀ (e : ℕ) (b : ℚ≥0),
      (2 ^ 40 / 2 ^ 192 : ℚ≥0) + epsCR K (2 ^ e) + epsLate K (2 ^ e) (2 ^ 86) ≤ b → Q ≤ 2 ^ e →
      (D : ℚ≥0) / Fintype.card E + epsCR K Q + epsLate K Q B ≤ b :=
    fun e b hb hQ => le_trans (add_le_add (add_le_add hDE (epsCR_mono K hQ)) (epsLate_mono K hQ hB)) hb
  refine ⟨key 84 _ ?_, key 82 _ ?_, key 74 _ ?_, key 63 _ ?_⟩ <;>
  · simp only [epsCR, epsLate, card_K]
    rw [← NNRat.coe_le_coe]
    push_cast
    norm_num

/-- The cap: at `2^86` queries the window term alone is past one, so the bound is vacuous there. -/
theorem epsCR_cap : 1 ≤ epsCR K (2 ^ 86) := by
  simp only [epsCR, card_K]
  rw [← NNRat.coe_le_coe]
  push_cast
  norm_num

/-- #551's `finalBound` grows with the budget. -/
theorem finalBound_mono {Q Q' : ℕ} (h : Q ≤ Q') : finalBound Q ≤ finalBound Q' := by
  rcases h.eq_or_lt with rfl | hlt
  · exact le_rfl
  unfold finalBound
  have hq : (Q : ℚ) ≤ Q' := by exact_mod_cast h
  have h0 : (0 : ℚ) ≤ Q := by positivity
  have h1 : (1 : ℚ) ≤ Q' := by exact_mod_cast (show 1 ≤ Q' by omega)
  have hd : (0 : ℚ) ≤ (Q' : ℚ) - Q := by linarith
  have e1 := mul_le_mul_of_nonneg_right hq (show (0 : ℚ) ≤ (17 / 32 : ℚ) ^ 56 + 1 / 2 ^ 78 by positivity)
  have e2 : 2 * (Q : ℚ) ^ 2 - Q ≤ 2 * (Q' : ℚ) ^ 2 - Q' := by
    nlinarith [mul_nonneg hd (show (0 : ℚ) ≤ 2 * Q' + 2 * Q - 1 by linarith)]
  have e3 : (Q : ℚ) ^ 3 + 3 * Q ^ 2 - 2 * Q ≤ (Q' : ℚ) ^ 3 + 3 * Q' ^ 2 - 2 * Q' := by
    nlinarith [mul_nonneg hd (show (0 : ℚ) ≤ Q' ^ 2 + Q' * Q + Q ^ 2 + 3 * Q' + 3 * Q - 2 by nlinarith)]
  have e2' := min_le_min_left 1 (div_le_div_of_nonneg_right e2 (show (0 : ℚ) ≤ 2 ^ 256 by positivity))
  have e3' := div_le_div_of_nonneg_right e3 (show (0 : ℚ) ≤ 2 ^ 256 by positivity)
  linarith

/-- One child's terms in `AirLink.tree_sound_end` at deployed sizes: degrees at most `2^40` for its reduction's,
checks', bus's and batch's terms, `2^64` compression queries, `2^86` late-hit targets and #551 budgets `2^e` per
binding shape. #551's term is about `4 · 2^e · 2^-51.1`, the rest below `2^-62`: below `2^-29` for `e = 20` and
`2^-17` for `e = 32`. -/
theorem child_bound_deployed {D Q B : ℕ} {Qp : Fin 4 → ℕ} (hD : D ≤ 2 ^ 40) (hQ : Q ≤ 2 ^ 64) (hB : B ≤ 2 ^ 86) :
    ((∀ k, Qp k ≤ 2 ^ 20) → (D : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp k)).toNNRat + epsCR K Q +
      epsLate K Q B ≤ 1 / 2 ^ 29) ∧
    ((∀ k, Qp k ≤ 2 ^ 32) → (D : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp k)).toNNRat + epsCR K Q +
      epsLate K Q B ≤ 1 / 2 ^ 17) := by
  have hDE : (D : ℚ≥0) / Fintype.card E ≤ 2 ^ 40 / 2 ^ 192 := by
    rw [card_E]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hD) (by positivity)
  have hrest : epsCR K Q + epsLate K Q B ≤ epsCR K (2 ^ 64) + epsLate K (2 ^ 64) (2 ^ 86) :=
    add_le_add (epsCR_mono K hQ) (epsLate_mono K hQ hB)
  have key : ∀ (e : ℕ) (b : ℚ≥0), (∀ k, Qp k ≤ 2 ^ e) →
      (2 ^ 40 / 2 ^ 192 : ℚ≥0) + (4 * finalBound ((2 ^ e : ℕ) : ℚ)).toNNRat +
        (epsCR K (2 ^ 64) + epsLate K (2 ^ 64) (2 ^ 86)) ≤ b →
      (D : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp k)).toNNRat + epsCR K Q + epsLate K Q B ≤ b := by
    intro e b hQp hb
    have hX : (∑ k, finalBound (Qp k)).toNNRat ≤ (4 * finalBound ((2 ^ e : ℕ) : ℚ)).toNNRat := by
      refine NNRat.toNNRat_mono ?_
      calc ∑ k, finalBound (Qp k) ≤ ∑ _k : Fin 4, finalBound ((2 ^ e : ℕ) : ℚ) :=
            Finset.sum_le_sum fun k _ => finalBound_mono (hQp k)
        _ = 4 * finalBound ((2 ^ e : ℕ) : ℚ) := by simp
    calc (D : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp k)).toNNRat + epsCR K Q + epsLate K Q B
        = (D : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp k)).toNNRat + (epsCR K Q + epsLate K Q B) := by ring
      _ ≤ _ := add_le_add (add_le_add hDE hX) hrest
      _ ≤ b := hb
  refine ⟨fun h => key 20 _ h ?_, fun h => key 32 _ h ?_⟩ <;>
  · rw [← NNRat.coe_le_coe, NNRat.coe_add, NNRat.coe_add,
      Rat.coe_toNNRat _ (mul_nonneg (by norm_num) (finalBound_nonneg _))]
    simp only [epsCR, epsLate, finalBound, card_K]
    push_cast
    norm_num

/-- The tree at deployed sizes: at most `2^10` nodes, each within `child_bound_deployed`'s sizes, `AirLink.tree_sound_end`'s
bound is below `2^-19` with #551 budgets `2^20` per binding shape and below `2^-7` with `2^32`. -/
theorem tree_bound_deployed {ι : Type} (S : Finset ι) (hS : S.card ≤ 2 ^ 10) (D Q B : ι → ℕ) (Qp : ι → Fin 4 → ℕ)
    (hD : ∀ v ∈ S, D v ≤ 2 ^ 40) (hQ : ∀ v ∈ S, Q v ≤ 2 ^ 64) (hB : ∀ v ∈ S, B v ≤ 2 ^ 86) :
    ((∀ v ∈ S, ∀ k, Qp v k ≤ 2 ^ 20) → ∑ v ∈ S, ((D v : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp v k)).toNNRat +
      epsCR K (Q v) + epsLate K (Q v) (B v)) ≤ 1 / 2 ^ 19) ∧
    ((∀ v ∈ S, ∀ k, Qp v k ≤ 2 ^ 32) → ∑ v ∈ S, ((D v : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp v k)).toNNRat +
      epsCR K (Q v) + epsLate K (Q v) (B v)) ≤ 1 / 2 ^ 7) := by
  have hsum : ∀ (b : ℚ≥0) (f : ι → ℚ≥0), (∀ v ∈ S, f v ≤ b) → ∑ v ∈ S, f v ≤ 2 ^ 10 * b := fun b f hf =>
    (Finset.sum_le_sum hf).trans (by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity))
  refine ⟨fun h => (hsum _ _ fun v hv => (child_bound_deployed (hD v hv) (hQ v hv) (hB v hv)).1 (h v hv)).trans
    (by norm_num), fun h => (hsum _ _ fun v hv => (child_bound_deployed (hD v hv) (hQ v hv) (hB v hv)).2 (h v hv)).trans
    (by norm_num)⟩

/-- Which term dominates at those sizes: #551's term at budgets `2^32` per binding shape is at least `2^-18` per
child, while the collision, window and late-hit terms at `2^64` compression queries and `2^86` targets are at most
`2^-62` together. -/
theorem pcs_dominates : (1 / 2 ^ 18 : ℚ) ≤ 4 * finalBound ((2 ^ 32 : ℕ) : ℚ) ∧
    epsCR K (2 ^ 64) + epsLate K (2 ^ 64) (2 ^ 86) ≤ 1 / 2 ^ 62 := by
  refine ⟨?_, ?_⟩
  · simp only [finalBound]
    push_cast
    norm_num
  · simp only [epsCR, epsLate, card_K]
    rw [← NNRat.coe_le_coe]
    push_cast
    norm_num

end LeanVMCircuits.Rec.Edges
