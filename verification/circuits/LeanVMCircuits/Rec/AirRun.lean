module

public import LeanVMCircuits.Rec.AirBatch
public import LeanVMCircuits.Rec.TreeBound
public import LeanVMCircuits.Rec.Run

@[expose] public section

/-!
The AIR's draws as the prover's Fiat-Shamir draws.

`AirLink.busBad_frac` and `AirLink.batchBad_frac` take the bus's draw `(β, A)` and the constraint batch's `(ζ, ξ)` uniform after the commitment, as lenses on the outcomes. Here they are a run's challenges (`Bind.Run`): words of the oracle read as elements of `E` (`Bind.readR`), each a challenge seed of the transcript after a time `k` before which the committed witness and the bus parts are fixed (`Bind.CommittedBefore`: functions of what the transcript absorbs before `k`, the commitment among it). The prover is adaptive: its witness and every message may depend on the oracle's earlier answers, and its messages between the draws on the draws before them.

`busRun_frac` and `batchRun_frac` bound the oracles at which the draw is in the committed witness's draw event by `4N/|E|` and `(n + 66 + 1)/|E|`: `Bind.Run.committed_at` makes the committed values fixed across the draws put in, and `Bind.run_frac` makes the draws uniform. `DrawsRun` bundles a run in which a child's draws are so drawn, and `tree_sound_run` is `tree_sound_batch` over a uniform oracle with every child's bus and batch draws a run's, in place of the lenses.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model LeanVMCircuits.Rec.Bind Finset Edges

/-- The batch's draw from `n + 1` challenges: `ζ` the first `n`, `ξ` the last. -/
def batchOf {n : ℕ} (r : Fin (n + 1) → E) : (Fin n → E) × E := (Fin.init r, r (Fin.last n))

open Classical in
/-- `batchOf` is a bijection: the challenge vectors whose batch draw is in a set are as many as the set. -/
theorem batchOf_card {n : ℕ} (S : Finset ((Fin n → E) × E)) : #{r : Fin (n + 1) → E | batchOf r ∈ S} = #S := by
  refine card_bij' (fun r _ => batchOf r) (fun x _ => (Fin.snoc x.1 x.2 : Fin (n + 1) → E)) ?_ ?_ ?_ ?_
  · intro r hr
    simpa only [mem_filter, mem_univ, true_and] using hr
  · intro x hx
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simpa [batchOf] using hx
  · intro r _
    simp only [batchOf, Fin.snoc_init_self]
  · intro x _
    simp only [batchOf, Fin.init_snoc, Fin.snoc_last, Prod.mk.eta]

section Run

variable {c : Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K} {val : (ℕ → K) → Val}

open Classical in
/-- The bus's draw `(β, A)` as a run's five challenges `own`, drawn after time `k`: where the committed witness is fixed before `k` (`hwit`), the oracles at which the draw is in its draw event are at most a `4N/|E|` fraction. -/
theorem busRun_frac (hR : Run c s T C st val) {own : Fin 5 → Fin 3 → ℕ} {time : Fin 5 → ℕ}
    (hown : OwnAt s (c.transcripts.getD T default) own time) (hinj : OwnInj own) {k : ℕ} (hk : ∀ i, k ≤ time i)
    (sc : State) (wit : (ℕ → K) → Witness) (hwit : CommittedBefore s (c.transcripts.getD T default) val k wit)
    (hfit : ∀ ρ T', (wit ρ).height T' ≤ 2 ^ 32) (N : ℕ) (hN : ∀ ρ, (slots (wit ρ)).length ≤ N)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | readR own (extU U ρ) ∈ busDraws sc (wit (extU U ρ))} : ℚ≥0) / Fintype.card (U → K) ≤
      ((4 * N : ℕ) : ℚ≥0) / Fintype.card E := by
  have key := run_frac hinj (fun i j => hU (own_mem_oracleWords hown i j))
    (fun ρ => readR own ρ ∈ busDraws sc (wit ρ)) (4 * N) fun ρ => by
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card (t := busDraws sc (wit ρ)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, readR_oracleAt hinj, hR.committed_at hown hinj hk hwit ρ] at hr
        exact hr
      · calc #(busDraws sc (wit ρ)) * Fintype.card E ≤ 4 * (slots (wit ρ)).length * Fintype.card E ^ 5 :=
            busDraws_card sc (wit ρ) (hfit ρ)
          _ ≤ 4 * N * Fintype.card E ^ 5 := by gcongr; exact hN ρ
  convert key

open Classical in
/-- The batch's draw `(ζ, ξ)` as a run's `n + 1` challenges `own`, drawn after time `k`: where the committed witness and the bus parts' dependence on `ζ` are fixed before `k` (`hwit`, `haOf`), the oracles at which the draw is in the witness's draw event are at most an `(n + 66 + 1)/|E|` fraction. -/
theorem batchRun_frac (hR : Run c s T C st val) {n : ℕ} {own : Fin (n + 1) → Fin 3 → ℕ} {time : Fin (n + 1) → ℕ}
    (hown : OwnAt s (c.transcripts.getD T default) own time) (hinj : OwnInj own) {k : ℕ} (hk : ∀ i, k ≤ time i)
    (wit : (ℕ → K) → Witness) (aOf : (ℕ → K) → (Fin n → E) → Fin 2 → E)
    (hwit : CommittedBefore s (c.transcripts.getD T default) val k wit)
    (haOf : CommittedBefore s (c.transcripts.getD T default) val k aOf) (htau : ∀ ρ T', tauOf (wit ρ) T' ≤ n)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | batchOf (readR own (extU U ρ)) ∈ batchDraws (wit (extU U ρ)) (aOf (extU U ρ))} : ℚ≥0) /
      Fintype.card (U → K) ≤ ((n + allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E := by
  have key := run_frac hinj (fun i j => hU (own_mem_oracleWords hown i j))
    (fun ρ => batchOf (readR own ρ) ∈ batchDraws (wit ρ) (aOf ρ)) (n + allIds.length + 1) fun ρ => by
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card
        (t := ({r : Fin (n + 1) → E | batchOf r ∈ batchDraws (wit ρ) (aOf ρ)} : Finset _)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, readR_oracleAt hinj, hR.committed_at hown hinj hk hwit ρ,
          hR.committed_at hown hinj hk haOf ρ] at hr ⊢
        exact hr
      · rw [batchOf_card]
        exact batchDraws_card (wit ρ) (htau ρ) (aOf ρ)
  convert key

end Run

/-- A run in which `m` challenges `own` are drawn after `f` is committed: a run of some transcript (`Bind.Run`) whose oracle words are among `U`, `own` its challenges at times at least `k` (`Bind.OwnAt`, `Bind.OwnInj`), and `f` fixed before `k` (`Bind.CommittedBefore`). -/
def DrawsRun (U : Finset ℕ) {m : ℕ} (own : Fin m → Fin 3 → ℕ) {α : Type} (f : (ℕ → K) → α) : Prop :=
  ∃ (c : Cert) (s : State) (T : ℕ) (C : (ℕ → K) → Prop) (st : (ℕ → K) → ℕ → Fin 4 → K) (val : (ℕ → K) → Val)
    (time : Fin m → ℕ) (k : ℕ),
    Run c s T C st val ∧ OwnAt s (c.transcripts.getD T default) own time ∧ OwnInj own ∧ (∀ i, k ≤ time i) ∧
      CommittedBefore s (c.transcripts.getD T default) val k f ∧ oracleWords s (c.transcripts.getD T default) ⊆ U

section Tree

variable {ι : Type}

open Classical in
/-- `tree_sound_batch` over a uniform oracle on the words `U`, every child's bus draw `(β, A)` (`own v`) and batch draw `(ζ, ξ)` (`bown v`) a run's challenges drawn after its committed witness `wit v` and bus parts `aOf v` (`DrawsRun`): the bound is the sum over the nodes of their reduction's `bad` and checks' `testBad` fractions, `epsPCS v`, `epsCR v`, `4 N_v/|E|` and `(n_v + 66 + 1)/|E|`. -/
theorem tree_sound_run (U : Finset ℕ) (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : (U → K) → ℕ → Fin 4 → K) (val : ι → (U → K) → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι (U → K))
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (n : ι → ℕ) (own : ι → Fin 5 → Fin 3 → ℕ) (bown : (v : ι) → Fin (n v + 1) → Fin 3 → ℕ)
    (wit : ι → (ℕ → K) → Witness) (aOf : (v : ι) → (ℕ → K) → (Fin (n v) → E) → Fin 2 → E)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v (extU U ω)))
    (hlink : ChecksGiveBatch T cert (fun v => stmtFirst (t v)) os L slot stRoot val P n (fun v ω => batchOf (readR (bown v) (extU U ω)))
      (fun v ω => aOf v (extU U ω)) (fun v ω => readR (own v) (extU U ω)) (fun v ω => wit v (extU U ω)))
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset (U → K))
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (hbusRun : ∀ v ∈ T.nodes, DrawsRun U (own v) (wit v))
    (hbatchRun : ∀ v ∈ T.nodes, DrawsRun U (bown v) fun ρ => (wit v ρ, aOf v ρ))
    (hfit : ∀ v ρ T', (wit v ρ).height T' ≤ 2 ^ 32) (N : ι → ℕ) (hN : ∀ v ρ, (slots (wit v ρ)).length ≤ N v)
    (htau : ∀ v ρ T', tauOf (wit v ρ) T' ≤ n v)
    (epsPCS epsCR : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hcr : ∀ v ∈ T.nodes, ((P.crBad v).card : ℚ≥0) / Fintype.card (U → K) ≤ epsCR v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card (U → K) ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) / Fintype.card (U → K) +
        epsPCS v + epsCR v + ((4 * N v : ℕ) : ℚ≥0) / Fintype.card E +
        ((n v + allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E) := by
  refine tree_sound_bound T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP
    (fun v => batchBad (fun ω => wit v (extU U ω)) (fun ω => aOf v (extU U ω))
      (fun ω => batchOf (readR (bown v) (extU U ω))))
    (fun v ω => readR (own v) (extU U ω)) (fun v ω => wit v (extU U ω)) hval
    (checksGiveRows_of_batch T cert (fun v => stmtFirst (t v)) os L slot stRoot val P n _ _ _ _ hlink) tD tM bad hstep hroot
    epsPCS epsCR _ _ hpcs hcr (fun v hv => ?_) (fun v hv => ?_)
  · obtain ⟨c, s, Tr, C, st, val', time, k, hR, hown, hinj, hk, hwit, hU⟩ := hbusRun v hv
    exact busRun_frac hR hown hinj hk (stmtFirst (t v)) (wit v) hwit (hfit v) (N v) (hN v) U hU
  · obtain ⟨c, s, Tr, C, st, val', time, k, hR, hown, hinj, hk, hwa, hU⟩ := hbatchRun v hv
    exact batchRun_frac hR hown hinj hk (wit v) (aOf v) (hwa.comp Prod.fst) (hwa.comp Prod.snd) (htau v) U hU

end Tree

end LeanVMCircuits.Rec.AirLink
