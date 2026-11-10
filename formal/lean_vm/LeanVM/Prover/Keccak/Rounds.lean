/-
  LeanVM.Prover.Keccak.Rounds

  Generic pieces of the Keccak prover's refinement: the stateful sumcheck over a bounded number
  of rounds, the sampled challenges' lengths, and the openings' sums of products of folded
  tables.
-/

module

public import LeanVM.Prover.Keccak.Tables

/-!
# Rounds

* `corr_sumcheckBy_lt`: `corr_sumcheckBy` with the invariant asked of the rounds still to come
  only (`pre.length < n`), the rounds counted;
* `corr_sampleN`: the challenges drawn have the length asked;
* `OpenInv`: an opening's state lists, per pair, two folded tables of affine families `F z`,
  `G z`; `polyEval_openRound`: its round polynomial is
  `scale · Σ_z Σ_u F z (pre ++ x :: u)·G z (pre ++ x :: u)`; `openInv_fold`, `openInv_full`.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Protocol.EndToEnd.Complete (coeffsOf hSumcheck)

@[expose] public section

/-- Two results related. -/
theorem corr_ret {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Corr R (Script.ret a) (Script.ret b) := h

/-- **The stateful sumcheck over at most `n` rounds** makes the specification's moves, given the
invariant along the rounds before the `n`-th. -/
theorem corr_sumcheckBy_lt {σ : Type} (count : ℕ) (hc : 1 ≤ count) (hc' : count ≤ 2 ^ 128)
    (claimOf : List E → E) (round : σ → List E) (fold : σ → E → σ) (Inv : List E → σ → Prop)
    (n : ℕ)
    (hround : ∀ pre st, Inv pre st → pre.length < n →
      (round st).length = count ∧ ∀ x, polyEval (round st) x = claimOf (pre ++ [x]))
    (hfold : ∀ pre st c, Inv pre st → pre.length < n → Inv (pre ++ [c]) (fold st c)) :
    ∀ (modes : List (Option E)) (pre : List E) (st : σ), Inv pre st →
      pre.length + modes.length ≤ n →
      Corr (fun a b ↦ a.1 = b.1 ∧ Inv (pre ++ a.1) a.2 ∧ b.2 = claimOf (pre ++ b.1) ∧
          a.1.length = modes.length)
        (sumcheckBy round fold modes st) (hSumcheck count claimOf modes pre)
  | [], pre, st, h, _ => by
    exact corr_ret ⟨rfl, by simpa using h, by simp, rfl⟩
  | mode :: modes, pre, st, h, hn => by
    have hlt : pre.length < n := by simp at hn; omega
    obtain ⟨hlen, hev⟩ := hround pre st h hlt
    have hco : coeffsOf (count - 1) (fun x ↦ claimOf (pre ++ [x])) = round st :=
      coeffsOf_eq (by omega) (by omega) hev
    simp only [sumcheckBy, hSumcheck, hco, ← wire_eq, Script.bind_assoc', roundGrind_eq hlen]
    refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun c ↦ ?_
    refine Corr.bind (fun a b hab ↦ ?_) _ _
      (corr_sumcheckBy_lt count hc hc' claimOf round fold Inv n hround hfold modes (pre ++ [c])
        (fold st c) (hfold pre st c h hlt) (by simp at hn ⊢; omega))
    obtain ⟨h1, h2, h3, h4⟩ := hab
    simp only [Corr, List.append_assoc, List.singleton_append] at h2 h3 ⊢
    exact ⟨by rw [h1], h2, h3, by simp [h4]⟩

/-- The challenges drawn. -/
theorem corr_sampleN : ∀ n : ℕ,
    Corr (fun a b ↦ a = b ∧ a.length = n) (Script.sampleN n) (Script.sampleN n)
  | 0 => corr_ret ⟨rfl, rfl⟩
  | n + 1 => by
    show Corr _ (Script.sampleE.bind fun x ↦ (Script.sampleN n).bind fun xs ↦ .ret (x :: xs))
      (Script.sampleE.bind fun x ↦ (Script.sampleN n).bind fun xs ↦ .ret (x :: xs))
    refine Corr.bind_same _ fun x ↦ Corr.bind (fun a b h ↦ ?_) _ _ (corr_sampleN n)
    obtain ⟨rfl, h⟩ := h
    exact corr_ret ⟨rfl, by simp [h]⟩

/-- Equal lists sent, then related continuations. -/
theorem corr_sendList {α β : Type} {S : α → β → Prop} {l l' : List E} (h : l = l')
    {f : Unit → Script α} {g : Unit → Script β} (hk : Corr S (f ()) (g ())) :
    Corr S ((Script.sendList l).bind f) ((Script.sendList l').bind g) := by
  subst h
  exact Corr.bind_same _ fun _ ↦ hk

/-- Equal scalars sent, then related continuations. -/
theorem corr_sendE {α β : Type} {S : α → β → Prop} {x x' : E} (h : x = x')
    {f : Unit → Script α} {g : Unit → Script β} (hk : Corr S (f ()) (g ())) :
    Corr S ((Script.sendE x).bind f) ((Script.sendE x').bind g) := by
  subst h
  exact Corr.bind_same _ fun _ ↦ hk

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
