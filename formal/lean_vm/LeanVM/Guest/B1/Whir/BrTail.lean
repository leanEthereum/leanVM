/-
  LeanVM.Guest.B1.Whir.BrTail

  The Spec's tail rounds as the guest's tail.
-/

module

public import LeanVM.Guest.B1.Whir.BrChain

/-!
# The tail

`tailTr_succ`: `n + 1` tail rounds are `n` fold rounds and a last squeeze. `tailC`: the
`tail_challenges` buffer's honest words, the tail challenges zero-padded. `tail_sp`: at the end of
the chain (`ChainEnd`), with that buffer at `T`, the tail's hypotheses of `osBodyA_complete` hold
and its claim is the run's final claim.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

theorem tailTr_succ : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E),
    tailTr (n + 1) F q t xs = ((foldsTr n F q t xs).1.squeeze.2,
      (foldsTr n F q t xs).2.1 ++ [(foldsTr n F q t xs).1.squeeze.1],
      polyEval (foldsTr n F q t xs).2.2.1 (foldsTr n F q t xs).1.squeeze.1)
  | 0, F, q, t, xs => by simp only [tailTr, foldsTr, List.nil_append]
  | n + 1, F, q, t, xs => by
    simp only [tailTr, foldsTr]
    rw [tailTr_succ n]
    simp only [List.cons_append]

/-- The run's tail challenges. -/
def tailChs (Lf : SpLv) (xsR : List E) : List E :=
  (tailTr Lf.ml Lf.Fend Lf.wsEnd.quad Lf.wsEnd.target xsR).2.1

/-- **The `tail_challenges` buffer's honest words.** -/
def tailC (Lf : SpLv) (xsR : List E) : List E :=
  tailChs Lf xsR ++ List.replicate (yrLogCap - Lf.ml) 0

theorem tailChs_length (Lf : SpLv) (xsR : List E) : (tailChs Lf xsR).length = Lf.ml :=
  tailTr_length _ _ _ _ _

/-- **The tail from the chain's end.** -/
theorem tail_sp {rd : Reader} {lane : ℕ} {O : Fs × List E × E × E} {Lf : SpLv} {xsR : List E}
    {res : WhirEnd × FSt} (hE : ChainEnd rd lane O Lf xsR res) {m : ℕ} (hml : Lf.ml = m)
    (hm1 : 1 ≤ m) (hcap : m ≤ yrLogCap) {T : E} (hT : ReadsAt rd T (tailC Lf xsR)) :
    (xsR.take (2 * (m - 1))).length = 2 * (m - 1) ∧ ReadsAt rd O.2.2.2 (xsR.take (2 * (m - 1))) ∧
      (∀ j, j < m - 1 → LoadHolds rd T j
        ((foldsTr (m - 1) O.1 O.2.1 O.2.2.1 (xsR.take (2 * (m - 1)))).2.1.getD j 0)) ∧
      LoadHolds rd T (m - 1) (foldsTr (m - 1) O.1 O.2.1 O.2.2.1 (xsR.take (2 * (m - 1)))).1.squeeze.1 ∧
      (∀ i < yrLogCap - m, LoadHolds rd T (m + i) 0) ∧
      polyEval (foldsTr (m - 1) O.1 O.2.1 O.2.2.1 (xsR.take (2 * (m - 1)))).2.2.1
        (foldsTr (m - 1) O.1 O.2.1 O.2.2.1 (xsR.take (2 * (m - 1)))).1.squeeze.1 =
        (tailTr Lf.ml Lf.Fend Lf.wsEnd.quad Lf.wsEnd.target xsR).2.2 := by
  have hlen := hE.len
  rw [hml] at hlen
  have htr : tailTr Lf.ml Lf.Fend Lf.wsEnd.quad Lf.wsEnd.target xsR =
      tailTr (m - 1 + 1) O.1 O.2.1 O.2.2.1 xsR := by
    rw [hE.F, hE.quad, hE.t, hml, Nat.sub_add_cancel hm1]
  rw [foldsTr_take]
  have hTc : tailC Lf xsR = (foldsTr (m - 1) O.1 O.2.1 O.2.2.1 xsR).2.1 ++
      [(foldsTr (m - 1) O.1 O.2.1 O.2.2.1 xsR).1.squeeze.1] ++ List.replicate (yrLogCap - m) 0 := by
    rw [tailC, tailChs, htr, tailTr_succ, hml]
  have hfl := foldsTr_chs_length (m - 1) O.1 O.2.1 O.2.2.1 xsR
  rw [hTc] at hT
  refine ⟨by simp; omega, readsAt_left (ys := xsR.drop (2 * (m - 1)))
    (by rw [List.take_append_drop]; exact hE.reads), fun j hj ↦ ?_, ?_, fun i hi ↦ ?_, ?_⟩
  · have := readsAt_get hT (k := j) (by simp; omega)
    rwa [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)] at this
  · have := readsAt_get hT (k := m - 1) (by simp; omega)
    rwa [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega),
      hfl, Nat.sub_self, List.getD_cons_zero] at this
  · have := readsAt_get hT (k := m + i) (by simp; omega)
    rw [List.getD_append_right _ _ _ _ (by simp; omega)] at this
    simpa [hfl, show m + i - (m - 1 + 1) = i by omega, List.getD_replicate, hi] using this
  · rw [htr, tailTr_succ]

end
end LeanVM.Guest.B1.Whir
