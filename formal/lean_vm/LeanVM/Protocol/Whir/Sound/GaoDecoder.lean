/-
  LeanVM.Protocol.Whir.Sound.GaoDecoder

  A near-tuple decoder from Gao's Reed-Solomon decoder: each lane decoded on the agreement set's
  points with CompPoly's `Gao.decode`, the tuple kept if it is near.
-/

module

public import LeanVM.Protocol.Whir.Sound.Descent
public import CompPoly.Univariate.ReedSolomon.GaoCorrectness

/-!
# The near-tuple decoder of Gao

`gaoNearDecoder`: on a set `S` of columns, every lane `v` of the word is decoded by Gao's
algorithm (`CompPoly.ReedSolomon.Gao.decode`, message length `d + 1`) on the points of `S` in
increasing order; if every lane decodes, and the decoded tuple is near (`NearT`), it is the
output. It returns only near tuples (`sound`), and a near tuple whenever one exists on at least
`d + 3` columns (`complete`): a near tuple disagrees with each lane on at most one column of `S`,
within Gao's radius `⌊(|S| − d − 1)/2⌋ ≥ 1`, so Gao returns it (`Gao.decode_eq_some`).

Credits: Gao's decoder and its correctness (`decode_eq_some`) are CompPoly's
(github.com/Verified-zkEVM/CompPoly, Apache-2.0; `Univariate/ReedSolomon/{GaoDecoder,GaoCorrectness}.lean`,
Juan Conejero).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters Polynomial CompPoly CompPoly.ReedSolomon

@[expose] public section

variable {n m : ℕ}

/-- The columns of `S`, in increasing order. -/
def setPts (S : Finset (Fin n)) : List (Fin n) := S.sort (· ≤ ·)

theorem nodup_setPts (S : Finset (Fin n)) : (setPts S).Nodup := Finset.sort_nodup _ _

theorem length_setPts (S : Finset (Fin n)) : (setPts S).length = S.card := Finset.length_sort _

theorem mem_setPts {S : Finset (Fin n)} {x : Fin n} : x ∈ setPts S ↔ x ∈ S := Finset.mem_sort _

/-- The evaluation domain of `S`'s columns. -/
def setDomain (dom : Fin n ↪ E) (S : Finset (Fin n)) : Domain E :=
  ⟨((setPts S).map dom).toArray, by
    rw [List.toList_toArray]
    exact (nodup_setPts S).map dom.injective⟩

theorem setDomain_n (dom : Fin n ↪ E) (S : Finset (Fin n)) : (setDomain dom S).n = S.card := by
  simp [setDomain, Domain.n, length_setPts]

theorem setDomain_get (dom : Fin n ↪ E) (S : Finset (Fin n)) (i : Fin (setDomain dom S).n) :
    (setDomain dom S).val[i] =
      dom ((setPts S)[i.val]'(by have := i.isLt; simp [setDomain, Domain.n] at this; exact this)) := by
  exact List.getElem_map _

/-- Lane `v` of the word on `S`'s columns. -/
def recvLane (dom : Fin n ↪ E) (Q : (Fin (m + 1) → Bool) → Fin n → E) (S : Finset (Fin n))
    (v : Fin (m + 1) → Bool) : Vector E (setDomain dom S).n :=
  ⟨((setPts S).map (Q v)).toArray, by simp [setDomain, Domain.n]⟩

theorem recvLane_get (dom : Fin n ↪ E) (Q : (Fin (m + 1) → Bool) → Fin n → E) (S : Finset (Fin n))
    (v : Fin (m + 1) → Bool) (i : Fin (setDomain dom S).n) :
    (recvLane dom Q S v).get i =
      Q v ((setPts S)[i.val]'(by have := i.isLt; simp [setDomain, Domain.n] at this; exact this)) := by
  simp [recvLane, Vector.get]
  rfl

/-- Gao's decoding of lane `v` on `S`'s columns, at message length `d + 1`. -/
def gaoLane (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E)
    (S : Finset (Fin n)) (v : Fin (m + 1) → Bool) : Option (CPolynomial E) :=
  Gao.decode (d + 1) (setDomain dom S) (recvLane dom Q S v)

open Classical in
/-- **Gao's near-tuple decoding**: every lane decoded, the tuple kept if near. -/
noncomputable def gaoDec (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E)
    (S : Finset (Fin n)) : Option ((Fin (m + 1) → Bool) → E[X]) :=
  if h : ∀ v, (gaoLane dom d Q S v).isSome then
    if NearT dom Q d S (fun v ↦ ((gaoLane dom d Q S v).get (h v)).toPoly) then
      some fun v ↦ ((gaoLane dom d Q S v).get (h v)).toPoly
    else none
  else none

/-- A lane of degree at most `d` that disagrees with the word on at most one column of `S`, with
`|S| ≥ d + 3`, is what Gao decodes. -/
theorem gaoLane_eq {dom : Fin n ↪ E} {d : ℕ} {Q : (Fin (m + 1) → Bool) → Fin n → E}
    {S : Finset (Fin n)} (hS : d + 3 ≤ S.card) {v : Fin (m + 1) → Bool} {P : E[X]}
    (hP : P.natDegree ≤ d) (hdis : (S.filter fun x ↦ P.eval (dom x) ≠ Q v x).card ≤ 1) :
    gaoLane dom d Q S v = some (CPolynomial.toPolyLinearEquiv.symm P) := by
  set c := CPolynomial.toPolyLinearEquiv.symm P with hc
  have hcP : c.toPoly = P := by rw [hc, ← CPolynomial.toPolyLinearEquiv_apply, LinearEquiv.apply_symm_apply]
  have hdeg : c.degree < (d + 1 : ℕ) := by
    rw [CPolynomial.degree_toPoly, hcP]
    have h1 : (P.natDegree : WithBot ℕ) ≤ (d : WithBot ℕ) := by exact_mod_cast hP
    have h2 : (d : WithBot ℕ) < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
    exact (Polynomial.degree_le_natDegree.trans h1).trans_lt h2
  have hmsg := messagePoly_ofFn_coeff (d + 1) c hdeg
  have hn : (setDomain dom S).n = S.card := setDomain_n dom S
  unfold gaoLane
  rw [← hmsg]
  refine Gao.decode_eq_some (d + 1) _ _ (by omega) _ ?_
  have hham : hammingDist (recvLane dom Q S v).get
      (encode (setDomain dom S) (Vector.ofFn fun i : Fin (d + 1) ↦ c.coeff i)).get ≤ 1 := by
    refine le_trans ?_ hdis
    unfold hammingDist
    refine Finset.card_le_card_of_injOn
      (fun i ↦ (setPts S)[i.val]'(by have := i.isLt; rw [length_setPts]; omega))
      (fun i hi ↦ ?_) (fun i _ j _ hij ↦ ?_)
    · have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨mem_setPts.mp (List.getElem_mem _), fun he ↦ hi' ?_⟩)
      rw [recvLane_get, encode_get, hmsg, CPolynomial.eval_toPoly, hcP, setDomain_get, ← he]
    · exact Fin.ext ((List.Nodup.getElem_inj_iff (nodup_setPts S)).mp hij)
  omega

/-- **Gao's near-tuple decoder.** -/
noncomputable def gaoNearDecoder : NearDecoder where
  dec dom d Q S := gaoDec dom d Q S
  sound dom d Q S T h := by
    unfold gaoDec at h
    split_ifs at h with h1 h2
    · rw [Option.some.injEq] at h
      exact h ▸ h2
  complete dom d Q S T hS hT := by
    have hlane : ∀ v, gaoLane dom d Q S v = some (CPolynomial.toPolyLinearEquiv.symm (T v)) := fun v ↦
      gaoLane_eq hS (hT.1 v) ((Finset.card_le_card fun x hx ↦ by
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, v, hx.2⟩).trans hT.2)
    have hall : ∀ v, (gaoLane dom d Q S v).isSome := fun v ↦ by rw [hlane v]; rfl
    have hTeq : (fun v ↦ ((gaoLane dom d Q S v).get (hall v)).toPoly) = T := by
      funext v
      simp only [hlane v, Option.get_some]
      rw [← CPolynomial.toPolyLinearEquiv_apply, LinearEquiv.apply_symm_apply]
    unfold gaoDec
    rw [dite_eq_left hall, hTeq]
    simp only [hT, ↓reduceIte, Option.isSome_some]

end
end LeanVM.Protocol.Whir.Sound
