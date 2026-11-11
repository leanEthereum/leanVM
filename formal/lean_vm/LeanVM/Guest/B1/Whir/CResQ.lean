/-
  LeanVM.Guest.B1.Whir.CResQ

  The inline `residual_query` and the residual chain's steps, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CPrim
public import LeanVM.Guest.B1.Whir.ResQuery

/-!
# The residual chain, honestly

`osResQ_complete`: the coordinates `t ..` of the product `Π (d_t + chain_t)`, the chain stepped by
the vanishing values. `osResQuery_complete`: the whole product from the position.
`osResStep_complete`: one step `h ← (h + R(p))·μ`, the position read; `osResSteps_complete`: the
steps at a list of offsets, the chain `resFoldC`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The residual chain: from `h`, each position's product added, then scaled by `mu`. -/
def resFoldC (D : ℕ → E) (vo ml : ℕ) (mu h : E) (ps : List E) : E :=
  ps.foldl (fun a p ↦ (a + residualProd (osVals vo ml) p D ml) * mu) h

theorem resFoldC_append (D : ℕ → E) (vo ml : ℕ) (mu h : E) (ps qs : List E) :
    resFoldC D vo ml mu h (ps ++ qs) = resFoldC D vo ml mu (resFoldC D vo ml mu h ps) qs := by
  simp [resFoldC, List.foldl_append]

/-- One coordinate's values: the vanishing value, the chain stepped, the row's word, the factor,
the product. -/
def resQVals (vals : List E) (p : E) (D : ℕ → E) (t : ℕ) (pe : E) : List E :=
  let v := vals.getD (t - 1) 0
  let c := residualChain vals p (t - 1)
  [v, c + v, c * (c + v), D t, D t + c * (c + v), pe * (D t + c * (c + v))]

/-- The values of the coordinates `t ..`. -/
def resQF (vals : List E) (p : E) (D : ℕ → E) : ℕ → ℕ → ℕ → Val → ℕ → E
  | 0, _, _, _ => fun _ ↦ 0
  | n + 1, t, k, σ =>
    seqF σ k (k + 6) (fun j ↦ (resQVals vals p D t (σ (.n (k - 1)))).getD (j - k) 0)
      fun σ1 ↦ resQF vals p D n (t + 1) (k + 6) σ1

theorem osResQ_k (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ),
    (osResQ pos bd row vo n t pe k).2.2 = k + 6 * n ∧
      (n = 0 → (osResQ pos bd row vo n t pe k).2.1 = pe) ∧
      (0 < n → (osResQ pos bd row vo n t pe k).2.1 = k + 6 * n - 1)
  | 0, _, _, _ => ⟨by simp [osResQ], fun _ ↦ rfl, fun h ↦ absurd h (by omega)⟩
  | n + 1, t, pe, k => by
    have := osResQ_k pos bd row vo n (t + 1) (k + 5) (k + 6)
    simp only [osResQ]
    refine ⟨by rw [this.1]; ring, fun h ↦ absurd h (by omega), fun _ ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [this.2.1 rfl]; omega
    · rw [this.2.2 hn]; omega

/-- **The coordinates `t ..` of the product, honestly**: from the chain at `t - 1` and the
product at `t` (the value just before `k`). -/
theorem osResQ_complete {pos bd row vo L : ℕ} {D : ℕ → E} : ∀ (n t k : ℕ) (σ : Val),
    1 ≤ t → t + n ≤ L → 1 ≤ k → pos < k → bd < k →
    σ (.n (if t = 1 then pos else k - 4)) = residualChain (osVals vo L) (σ (.n pos)) (t - 1) →
    σ (.n (k - 1)) = residualProd (osVals vo L) (σ (.n pos)) D t →
    (∀ s, t ≤ s → s < t + n → LoadHolds rd (σ (.n bd)) (row + s) (D s)) →
    BlkF C rd σ k (osResQ pos bd row vo n t (k - 1) k).2.2
      (resQF (osVals vo L) (σ (.n pos)) D n t k σ) (osResQ pos bd row vo n t (k - 1) k).1
      (fun σ' ↦ σ' (.n (osResQ pos bd row vo n t (k - 1) k).2.1) =
        residualProd (osVals vo L) (σ (.n pos)) D (t + n) ∧ AgreeBelow k σ σ')
  | 0, t, k, σ, _, _, hk, _, _, _, hpe, _ => by
    simp only [osResQ, resQF]
    exact BlkF.nil fun σ' ha ↦ ⟨by rw [ha _ (by omega), hpe, Nat.add_zero], ha⟩
  | n + 1, t, k, σ, ht, hL, hk, hpos, hbd, hch, hpe, hD => by
    set vals := osVals vo L with hvals
    set v := vals.getD (t - 1) 0 with hv
    set c := residualChain vals (σ (.n pos)) (t - 1) with hc
    have hvw : v = word (vanishVal (vo + t - 1)) 0 0 := by
      rw [hv, hvals, osVals_getD (by omega)]
      congr 2; omega
    have hchain : residualChain vals (σ (.n pos)) t = c * (c + v) := by
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      simp only [residualChain, hc, hv, Nat.add_sub_cancel]
    have e : osResQ pos bd row vo (n + 1) t (k - 1) k =
        ([.atom (.const (.n k) (word (vanishVal (vo + t - 1)) 0 0)),
          .atom (.add (.n (k + 1)) (.n (if t = 1 then pos else k - 4)) (.n k)),
          .atom (.mul (.n (k + 2)) (.n (if t = 1 then pos else k - 4)) (.n (k + 1))),
          .atom (.load (.n (k + 3)) (.n bd) (row + t)),
          .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))),
          .atom (.mul (.n (k + 5)) (.n (k - 1)) (.n (k + 4)))] ++
          (osResQ pos bd row vo n (t + 1) (k + 5) (k + 6)).1,
        (osResQ pos bd row vo n (t + 1) (k + 5) (k + 6)).2) := rfl
    rw [e]
    dsimp only
    simp only [resQF]
    have hk6 := (osResQ_k pos bd row vo n (t + 1) (k + 5) (k + 6)).1
    have hblk : BlkF C rd σ k (k + 6) (fun j ↦ (resQVals vals (σ (.n pos)) D t (σ (.n (k - 1)))).getD
        (j - k) 0)
        [.atom (.const (.n k) (word (vanishVal (vo + t - 1)) 0 0)),
          .atom (.add (.n (k + 1)) (.n (if t = 1 then pos else k - 4)) (.n k)),
          .atom (.mul (.n (k + 2)) (.n (if t = 1 then pos else k - 4)) (.n (k + 1))),
          .atom (.load (.n (k + 3)) (.n bd) (row + t)),
          .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))),
          .atom (.mul (.n (k + 5)) (.n (k - 1)) (.n (k + 4)))]
        (fun σ' ↦ σ' (.n (k + 2)) = residualChain vals (σ (.n pos)) t ∧
          σ' (.n (k + 5)) = residualProd vals (σ (.n pos)) D (t + 1) ∧ AgreeBelow k σ σ') := by
      intro σ' ha hr
      have V : ∀ j < 6, σ' (.n (k + j)) =
          (resQVals vals (σ (.n pos)) D t (σ (.n (k - 1)))).getD j 0 := fun j hj ↦ by
        rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
      simp only [resQVals, ← hv, ← hc, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
      have ech : σ' (.n (if t = 1 then pos else k - 4)) = c := by
        rw [ha _ (by split_ifs <;> omega), hch]
      have epe := ha (k - 1) (by omega)
      have ebd := ha bd hbd
      refine ⟨?_, by rw [v2, hchain], by rw [v5, hpe, residualProd, hchain], ha⟩
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨by rw [v0, hvw], by rw [v1, ech, v0], by rw [v2, ech, v1], ?_,
        by rw [v4, v3, v2], by rw [v5, epe, v4]⟩
      rw [v3, ebd]; exact hD t le_rfl (by omega)
    refine BlkF.then (k1 := k + 6) (by omega) (by omega) hblk fun σ1 _ ⟨h2, h5, ha1⟩ ↦ ?_
    have hrec := osResQ_complete (pos := pos) (bd := bd) (row := row) (vo := vo) (L := L) (D := D)
      n (t + 1) (k + 6) σ1 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by
        have h1 : (t + 1 = 1) = False := eq_false (by omega)
        simp only [h1, ↓reduceIte, Nat.add_sub_cancel, show k + 6 - 4 = k + 2 by omega]
        rw [h2, ha1 pos hpos])
      (by rw [show k + 6 - 1 = k + 5 by omega, h5, ha1 pos hpos])
      (fun s h1 h2 ↦ by rw [ha1 bd hbd]; exact hD s (by omega) (by omega))
    rw [ha1 pos hpos, show k + 6 - 1 = k + 5 by omega] at hrec
    refine BlkF.mono hrec fun σ' ⟨hv', ha2⟩ ↦ ⟨by rw [hv', show t + 1 + n = t + (n + 1) by ring],
      fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩

/-- The values of the inline `residual_query`. -/
def resQueryF (vo n : ℕ) (pos k : ℕ) (σ : Val) (D : ℕ → E) : ℕ → E :=
  seqF σ k (k + 2) (fun j ↦ [D 0, D 0 + σ (.n pos)].getD (j - k) 0)
    fun σ1 ↦ resQF (osVals vo n) (σ1 (.n pos)) D (n - 1) 1 (k + 2) σ1

/-- **The inline `residual_query`, honestly.** -/
theorem osResQuery_complete {pos bd row vo n k : ℕ} {D : ℕ → E} (σ : Val) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hpos : pos < k) (hbd : bd < k)
    (hD : ∀ s < n, LoadHolds rd (σ (.n bd)) (row + s) (D s)) :
    BlkF C rd σ k (osResQuery pos bd row vo n k).2.2 (resQueryF vo n pos k σ D)
      (osResQuery pos bd row vo n k).1
      (fun σ' ↦ σ' (.n (osResQuery pos bd row vo n k).2.1) =
        residualProd (osVals vo n) (σ (.n pos)) D n ∧ AgreeBelow k σ σ') := by
  simp only [osResQuery]
  have hk2 := (osResQ_k pos bd row vo (n - 1) 1 (k + 1) (k + 2)).1
  have hA : BlkF C rd σ k (k + 2) (fun j ↦ [D 0, D 0 + σ (.n pos)].getD (j - k) 0)
      [.atom (.load (.n k) (.n bd) row), .atom (.add (.n (k + 1)) (.n k) (.n pos))]
      (fun σ' ↦ σ' (.n (k + 1)) = D 0 + σ (.n pos) ∧ AgreeBelow k σ σ') := by
    intro σ' ha hr
    have v0 := hr k le_rfl (by omega)
    have v1 := hr (k + 1) (by omega) (by omega)
    simp only [Nat.sub_self, Nat.add_sub_cancel_left, List.getD_cons_zero, List.getD_cons_succ] at v0 v1
    refine ⟨?_, v1, ha⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨by rw [v0, ha bd hbd]; simpa using hD 0 hn, by rw [v1, v0, ha pos hpos]⟩
  refine BlkF.then (k1 := k + 2) (by omega) (by omega) hA fun σ1 _ ⟨h1, ha1⟩ ↦ ?_
  have hrec := osResQ_complete (C := C) (rd := rd) (pos := pos) (bd := bd) (row := row) (vo := vo)
    (L := n) (D := D) (n - 1) 1 (k + 2) σ1 le_rfl (by omega) (by omega) (by omega) (by omega)
    (by simp [residualChain])
    (by rw [show k + 2 - 1 = k + 1 by omega, h1, ha1 pos hpos]; simp [residualProd, residualChain])
    (fun s h1 h2 ↦ by rw [ha1 bd hbd]; exact hD s (by omega))
  rw [show k + 2 - 1 = k + 1 by omega] at hrec
  refine BlkF.mono hrec fun σ' ⟨hv, ha2⟩ ↦ ⟨by rw [hv, ha1 pos hpos, show 1 + (n - 1) = n by omega],
    fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩

theorem osResQuery_k (pos bd row vo n k : ℕ) :
    k + 2 ≤ (osResQuery pos bd row vo n k).2.2 ∧
      (osResQuery pos bd row vo n k).2.1 < (osResQuery pos bd row vo n k).2.2 := by
  have h := osResQ_k pos bd row vo (n - 1) 1 (k + 1) (k + 2)
  simp only [osResQuery]
  refine ⟨by omega, ?_⟩
  rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
  · rw [h.2.1 h0]; omega
  · rw [h.2.2 h0]; omega

/-- The values of one residual step from `k`: the position, its `residual_query`, the chain's
sum and product. -/
def resStepF (bd row vo ncols : ℕ) (D : ℕ → E) (M p hv : E) (k : ℕ) (σ : Val) : ℕ → E :=
  let e := (osResQuery k bd row vo ncols (k + 1)).2.2
  let R := residualProd (osVals vo ncols) p D ncols
  seqF σ k (k + 1) (fun _ ↦ p) fun σ1 ↦
  seqF σ1 (k + 1) e (resQueryF vo ncols k (k + 1) σ1 D) fun _ ↦
  fun i ↦ if i = e then hv + R else (hv + R) * M

/-- **One residual step, honestly.** -/
theorem osResStep_complete {pp bd row vo ncols mu j h k : ℕ} {D : ℕ → E} {M p hv PP BD : E}
    (σ : Val) (hn : 1 ≤ ncols) (hk : 1 ≤ k) (hpp : pp < k) (hbd : bd < k) (hh : h < k)
    (hmu : mu < k) (ePP : σ (.n pp) = PP) (eBD : σ (.n bd) = BD) (eh : σ (.n h) = hv)
    (eM : σ (.n mu) = M) (hp : LoadHolds rd PP j p)
    (hD : ∀ s < ncols, LoadHolds rd BD (row + s) (D s)) :
    BlkF C rd σ k (osResStep pp bd row vo ncols mu j h k).2.2 (resStepF bd row vo ncols D M p hv k σ)
      (osResStep pp bd row vo ncols mu j h k).1
      (fun σ' ↦ σ' (.n (osResStep pp bd row vo ncols mu j h k).2.1) =
        (hv + residualProd (osVals vo ncols) p D ncols) * M ∧ AgreeBelow k σ σ') := by
  obtain ⟨he1, he2⟩ := osResQuery_k k bd row vo ncols (k + 1)
  set e := osResQuery k bd row vo ncols (k + 1) with hedef
  set R := residualProd (osVals vo ncols) p D ncols
  have est : (osResStep pp bd row vo ncols mu j h k).1 = [.atom (.load (.n k) (.n pp) j)] ++
      (e.1 ++ [.atom (.add (.n e.2.2) (.n h) (.n e.2.1)), .atom (.mul (.n (e.2.2 + 1)) (.n e.2.2) (.n mu))]) := by
    simp only [osResStep, List.append_assoc]; rfl
  have ek : (osResStep pp bd row vo ncols mu j h k).2 = (e.2.2 + 1, e.2.2 + 2) := rfl
  rw [est, ek]
  unfold resStepF
  have hA : BlkF C rd σ k (k + 1) (fun _ ↦ p) [.atom (.load (.n k) (.n pp) j)]
      (fun σ' ↦ σ' (.n k) = p ∧ AgreeBelow k σ σ') := by
    intro σ' ha hr
    have v := hr k le_rfl (by omega)
    refine ⟨?_, v, ha⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    rw [v, ha _ hpp, ePP]; exact hp
  refine BlkF.then (k1 := k + 1) (by omega) (by omega) hA fun σ1 _ ⟨h1, ha1⟩ ↦ ?_
  have hQ := osResQuery_complete (C := C) (rd := rd) (pos := k) (bd := bd) (row := row) (vo := vo)
    (n := ncols) (k := k + 1) (D := D) σ1 hn (by omega) (by omega) (by omega)
    (fun s hs ↦ by rw [ha1 _ hbd, eBD]; exact hD s hs)
  refine BlkF.then (k1 := e.2.2) (by omega) (by omega) hQ fun σ2 _ ⟨h2, ha2⟩ ↦ ?_
  rw [h1] at h2
  intro σ' ha hr
  have v0 := hr e.2.2 le_rfl (by omega)
  have v1 := hr (e.2.2 + 1) (by omega) (by omega)
  try rw [← hedef] at v0 v1 h2
  beta_reduce at v0 v1
  simp only [show e.2.2 + 1 ≠ e.2.2 by omega, ↓reduceIte] at v0 v1
  have eh' : σ' (.n h) = hv := by rw [ha _ (by omega), ha2 _ (by omega), ha1 _ hh, eh]
  have eM' : σ' (.n mu) = M := by rw [ha _ (by omega), ha2 _ (by omega), ha1 _ hmu, eM]
  have eR : σ' (.n e.2.1) = R := by rw [ha _ he2, h2]
  refine ⟨?_, show σ' (.n (e.2.2 + 1)) = (hv + R) * M from v1,
    fun i hi ↦ (ha i (by omega)).trans ((ha2 i (by omega)).trans (ha1 i hi))⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  exact ⟨by rw [v0, eh', eR], by rw [v1, v0, eM']⟩

/-- The values of the residual steps from `k`, the chain at `hv`. -/
def resStepsF (bd row vo ncols : ℕ) (D : ℕ → E) (M : E) : List E → E → ℕ → Val → ℕ → E
  | [], _, _, _ => fun _ ↦ 0
  | p :: ps, hv, k, σ =>
    let e := (osResQuery k bd row vo ncols (k + 1)).2.2
    seqF σ k (e + 2) (resStepF bd row vo ncols D M p hv k σ) fun σ1 ↦
      resStepsF bd row vo ncols D M ps ((hv + residualProd (osVals vo ncols) p D ncols) * M) (e + 2) σ1

theorem osResSteps_k (pp bd row vo ncols mu : ℕ) : ∀ (js : List ℕ) (h k : ℕ), h < k →
    k ≤ (osResSteps pp bd row vo ncols mu js h k).2.2 ∧
      (osResSteps pp bd row vo ncols mu js h k).2.1 < (osResSteps pp bd row vo ncols mu js h k).2.2
  | [], h, k, hh => ⟨le_rfl, hh⟩
  | j :: js, h, k, _ => by
    have := osResQuery_k k bd row vo ncols (k + 1)
    have ih := osResSteps_k pp bd row vo ncols mu js
      ((osResQuery k bd row vo ncols (k + 1)).2.2 + 1) ((osResQuery k bd row vo ncols (k + 1)).2.2 + 2)
      (by omega)
    show k ≤ (osResSteps pp bd row vo ncols mu js ((osResQuery k bd row vo ncols (k + 1)).2.2 + 1)
      ((osResQuery k bd row vo ncols (k + 1)).2.2 + 2)).2.2 ∧ _
    exact ⟨by omega, ih.2⟩

/-- **The residual steps, honestly.** -/
theorem osResSteps_complete {pp bd row vo ncols mu : ℕ} {D : ℕ → E} {M PP BD : E} (hn : 1 ≤ ncols) :
    ∀ (js : List ℕ) (ps : List E) (h k : ℕ) (hv : E) (σ : Val), 1 ≤ k → pp < k → bd < k → h < k →
      mu < k → σ (.n pp) = PP → σ (.n bd) = BD → σ (.n h) = hv → σ (.n mu) = M →
      List.Forall₂ (fun j p ↦ LoadHolds rd PP j p) js ps →
      (∀ s < ncols, LoadHolds rd BD (row + s) (D s)) →
      BlkF C rd σ k (osResSteps pp bd row vo ncols mu js h k).2.2
        (resStepsF bd row vo ncols D M ps hv k σ) (osResSteps pp bd row vo ncols mu js h k).1
        (fun σ' ↦ σ' (.n (osResSteps pp bd row vo ncols mu js h k).2.1) = resFoldC D vo ncols M hv ps ∧
          AgreeBelow k σ σ')
  | [], [], h, k, hv, σ, _, _, _, hh, _, _, _, eh, _, _, _ => by
    simp only [osResSteps]
    exact BlkF.nil fun σ' ha ↦ ⟨by rw [ha _ hh, eh]; rfl, ha⟩
  | j :: js, p :: ps, h, k, hv, σ, hk, hpp, hbd, hh, hmu, ePP, eBD, eh, eM, hF, hD => by
    obtain ⟨-, hFs⟩ := List.forall₂_cons.mp hF
    have hp := (List.forall₂_cons.mp hF).1
    have hA := osResStep_complete (C := C) (rd := rd) (pp := pp) (bd := bd) (row := row) (vo := vo)
      (ncols := ncols) (mu := mu) (j := j) (h := h) (k := k) (D := D) σ hn hk hpp hbd hh hmu ePP eBD
      eh eM hp hD
    have hqk := osResQuery_k k bd row vo ncols (k + 1)
    set e := osResQuery k bd row vo ncols (k + 1) with hedef
    have e1 : (osResStep pp bd row vo ncols mu j h k).2 = (e.2.2 + 1, e.2.2 + 2) := rfl
    rw [e1] at hA
    dsimp only at hA
    have hk2 := (osResSteps_k pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2) (by omega)).1
    have eS : osResSteps pp bd row vo ncols mu (j :: js) h k =
        ((osResStep pp bd row vo ncols mu j h k).1 ++
          (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).1,
          (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).2) := rfl
    have eF : resStepsF bd row vo ncols D M (p :: ps) hv k σ = seqF σ k (e.2.2 + 2)
        (resStepF bd row vo ncols D M p hv k σ) (fun σ1 ↦ resStepsF bd row vo ncols D M ps
          ((hv + residualProd (osVals vo ncols) p D ncols) * M) (e.2.2 + 2) σ1) := rfl
    rw [eS, eF]
    dsimp only
    have hB : ∀ σ1, AgreeBelow k σ σ1 →
        (σ1 (.n (e.2.2 + 1)) = (hv + residualProd (osVals vo ncols) p D ncols) * M ∧
          AgreeBelow k σ σ1) →
        BlkF C rd σ1 (e.2.2 + 2) (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).2.2
          (resStepsF bd row vo ncols D M ps ((hv + residualProd (osVals vo ncols) p D ncols) * M)
            (e.2.2 + 2) σ1)
          (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).1
          (fun σ' ↦ σ' (.n (osResSteps pp bd row vo ncols mu js (e.2.2 + 1) (e.2.2 + 2)).2.1) =
            resFoldC D vo ncols M ((hv + residualProd (osVals vo ncols) p D ncols) * M) ps ∧
            AgreeBelow k σ σ') := fun σ1 _ ⟨h1, ha1⟩ ↦
      BlkF.mono (osResSteps_complete hn js ps (e.2.2 + 1) (e.2.2 + 2) _ σ1 (by omega) (by omega)
        (by omega) (by omega) (by omega) (by rw [ha1 _ hpp, ePP]) (by rw [ha1 _ hbd, eBD]) h1
        (by rw [ha1 _ hmu, eM]) hFs hD) fun σ' ⟨hv', ha2⟩ ↦
          ⟨hv', fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩
    refine BlkF.mono (BlkF.seq (k1 := e.2.2 + 2) (by omega) hk2 hA hB)
      fun σ' ⟨_, hv', ha2⟩ ↦ ⟨?_, ha2⟩
    rw [hv']; simp [resFoldC, List.foldl_cons]
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, hF, _ => by cases hF
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, hF, _ => by cases hF

end
end LeanVM.Guest.B1.Whir
