/-
  LeanVM.Prover.Complete.Keccak.Exec.Rounds

  Generic pieces of the Keccak prover's refinement: the stateful sumcheck over a bounded number
  of rounds, the sampled challenges' lengths, and the openings' sums of products of folded
  tables.
-/

module

public import LeanVM.Prover.Complete.Keccak.Exec.Tables

/-!
# Rounds

* `OpenInv`: an opening's state lists, per pair, two folded tables of affine families `F z`,
  `G z`; `polyEval_openRound`: its round polynomial is
  `scale · Σ_z Σ_u F z (pre ++ x :: u)·G z (pre ++ x :: u)`; `openInv_fold`, `openInv_full`.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Prover.Complete.Keccak

@[expose] public section

/-- Two results related. -/
theorem corr_ret {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Corr R (Script.ret a) (Script.ret b) := h

/-! ## Sums of products of folded tables -/

/-- An opening's state: scale `sc`, `m` pairs of tables, pair `z` folded tables of `F z`, `G z`
over `n` coordinates at the challenges `pre`. -/
def OpenInv (sc : E) (m n : ℕ) (F G : ℕ → List E → E) (pre : List E) (st : OpenState) : Prop :=
  st.scale = sc ∧ st.pairs.length = m ∧ ∀ z < m,
    TabInv (st.pairs.getD z (#[], #[])).1 (F z) n pre ∧
      TabInv (st.pairs.getD z (#[], #[])).2 (G z) n pre

theorem length_prodCoeffs (a b : Array E) : (prodCoeffs a b).length = 3 :=
  (polyEval_sumCoeffs 3 _ _ (fun _ _ ↦ rfl) 0).1

theorem polyEval_prodCoeffs (a b : Array E) (x : E) :
    polyEval (prodCoeffs a b) x = ∑ u ∈ range (a.size / 2),
      (a.getD (2 * u) 0 + x * (a.getD (2 * u) 0 + a.getD (2 * u + 1) 0)) *
        (b.getD (2 * u) 0 + x * (b.getD (2 * u) 0 + b.getD (2 * u + 1) 0)) := by
  rw [prodCoeffs, (polyEval_sumCoeffs 3 _ _ (fun _ _ ↦ rfl) x).2]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [polyEval_cons', polyEval_nil']
  ring

theorem polyEval_foldl_pairs (x : E) : ∀ (L : List (Array E × Array E)) (acc : List E),
    acc.length = 3 →
    (L.foldl (fun acc p ↦ addCoeffs acc (prodCoeffs p.1 p.2)) acc).length = 3 ∧
      polyEval (L.foldl (fun acc p ↦ addCoeffs acc (prodCoeffs p.1 p.2)) acc) x =
        polyEval acc x + ∑ z ∈ range L.length,
          polyEval (prodCoeffs (L.getD z (#[], #[])).1 (L.getD z (#[], #[])).2) x
  | [], acc, h => ⟨h, by simp⟩
  | p :: L, acc, h => by
    rw [List.foldl_cons]
    have hl : (addCoeffs acc (prodCoeffs p.1 p.2)).length = 3 := by
      rw [length_addCoeffs, h, length_prodCoeffs, min_self]
    obtain ⟨h1, h2⟩ := polyEval_foldl_pairs x L _ hl
    refine ⟨h1, ?_⟩
    rw [h2, polyEval_addCoeffs _ _ (by rw [h, length_prodCoeffs]), List.length_cons,
      Finset.sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    rfl

/-- **An opening round's polynomial.** -/
theorem polyEval_openRound {sc : E} {m n : ℕ} {F G : ℕ → List E → E}
    (hF : ∀ z, Affine (F z)) (hG : ∀ z, Affine (G z)) {pre : List E} {st : OpenState}
    (h : OpenInv sc m n F G pre st) (hlt : pre.length < n) :
    (openRound st).length = 3 ∧ ∀ x, polyEval (openRound st) x =
      sc * ∑ z ∈ range m, ∑ u ∈ range (2 ^ (n - (pre.length + 1))),
        F z (pre ++ x :: bitsE u (n - (pre.length + 1))) *
          G z (pre ++ x :: bitsE u (n - (pre.length + 1))) := by
  obtain ⟨hsc, hm, hz⟩ := h
  have hlen := (polyEval_foldl_pairs 0 st.pairs (List.replicate 3 0) (by simp)).1
  refine ⟨by rw [openRound, length_scaleCoeffs, hlen], fun x ↦ ?_⟩
  rw [openRound, polyEval_scaleCoeffs, hsc,
    (polyEval_foldl_pairs x st.pairs (List.replicate 3 0) (by simp)).2, polyEval_replicate_zero,
    zero_add, hm]
  congr 1
  refine Finset.sum_congr rfl fun z hzm ↦ ?_
  obtain ⟨h1, h2⟩ := hz z (Finset.mem_range.1 hzm)
  have hsz : (st.pairs.getD z (#[], #[])).1.size / 2 = 2 ^ (n - (pre.length + 1)) := by
    rw [h1.2.1, show n - pre.length = n - (pre.length + 1) + 1 by omega, pow_succ]; omega
  rw [polyEval_prodCoeffs, hsz]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [tabInv_split (hF z) h1 hlt (Finset.mem_range.1 hu),
    tabInv_split (hG z) h2 hlt (Finset.mem_range.1 hu)]

theorem openInv_fold {sc : E} {m n : ℕ} {F G : ℕ → List E → E}
    (hF : ∀ z, Affine (F z)) (hG : ∀ z, Affine (G z)) {pre : List E} {st : OpenState}
    (h : OpenInv sc m n F G pre st) (hlt : pre.length < n) (c : E) :
    OpenInv sc m n F G (pre ++ [c]) (openFold st c) := by
  obtain ⟨hsc, hm, hz⟩ := h
  refine ⟨hsc, by simp [openFold, hm], fun z hzm ↦ ?_⟩
  have hget : (openFold st c).pairs.getD z (#[], #[]) =
      (foldPairsA c (st.pairs.getD z (#[], #[])).1, foldPairsA c (st.pairs.getD z (#[], #[])).2) := by
    simp [openFold, List.getD_eq_getElem?_getD, hm, hzm]
  rw [hget]
  exact ⟨tabInv_fold (hF z) (hz z hzm).1 hlt c, tabInv_fold (hG z) (hz z hzm).2 hlt c⟩

end
end LeanVM.Prover.KeccakGkr
