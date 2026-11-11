/-
  LeanVM.Guest.B1.Whir.CFoldCall

  The fold rounds' calls hold under the program's relation: `opening_fold`, and the rate's
  `opening_fold_round` specialization at its bits.
-/

module

public import LeanVM.Guest.B1.Whir.COfr
public import LeanVM.Guest.B1.Whir.CFinal
public import LeanVM.Guest.B1.Opening.Fold

/-!
# The fold rounds' calls, honestly

`foldCallC_none`: `opening_fold`'s call holds of every meaning a fold round without proof of work
has (`opening_fold_holds`). `ofr_rel`: `opening_fold_round` at `b` bits relates every meaning of a
round at `b` bits, its grinding check complete. `foldCallC_some`: the dispatch on the rate's
selector `g^ri` into the rate's specialization holds.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- A round's meaning at `0` bits, on canonical capacity cells, is `opening_fold`'s. -/
theorem meaningOpeningFold_of {args rets : List E} (hcan : AllCanonical (args.take 5))
    (h : MeaningFoldRound 0 rd args rets) : MeaningOpeningFold rd args rets := by
  match args, h with
  | [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2], ⟨nonce, d0, d2, hrd, _, hret⟩ =>
    refine ⟨by simpa using hcan, d0, d2, by simpa [powWords] using hrd, ?_⟩
    simpa [powSponge, roundLen] using hret

/-- **`opening_fold`'s calls hold.** -/
theorem foldCallC_none (R : E) : FoldCallC (coreProgram.Rel rd) rd none 0 R :=
  fun _ _ _ _ hcan h ↦
    (opening_fold_holds rd _ _).mpr (meaningOpeningFold_of hcan h)

/-- The nonce absorbed after two waiting scalars. -/
theorem absorb_nonce (fs : List E) (w0 w1 nonce : E) :
    (⟨fs, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorb nonce dsPowNonce =
      ⟨fs, [(w0, dsObserve), (w1, dsObserve), (nonce, dsPowNonce)]⟩ := by
  simp [Fs.absorb, rateScalars]

/-- **`opening_fold_round` at `b > 0` bits relates every round's meaning**, on canonical capacity
cells, its grinding check complete. -/
theorem ofr_rel {b : ℕ} (hb : b ≠ 0) {name : String} (hfn : FnIs name (osParams 11) (ofrBody b))
    (hgr : ∀ w, MeaningGrindCheck b [w] [] →
      coreProgram.Rel rd ("grind_check__L" ++ natStr b) [w] [])
    {args rets : List E} (hcan : AllCanonical (args.take 5))
    (h : MeaningFoldRound b rd args rets) : coreProgram.Rel rd name args rets := by
  match args, h with
  | [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2], ⟨nonce, d0, d2, hrd, hpow, hret⟩ =>
    have hF := absorb_nonce [f0, f1, f2, f3, f4] w0 w1 nonce
    have hrd' : ReadsAt rd cur [nonce, d0, d2] := by simpa [powWords, hb] using hrd
    have hS : ((⟨[f0, f1, f2, f3, f4], [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorb nonce
        dsPowNonce).perm = ofrS [f0, f1, f2, f3, f4] w0 w1 nonce := by rw [hF]; rfl
    have hg := grind_meaning hb (hpow hb)
    rw [hS] at hg
    have hrel := ofr_complete (rd := rd) hfn (fs := [f0, f1, f2, f3, f4]) rfl (by simpa using hcan)
      (w0 := w0) (w1 := w1) (cur := cur) (c0 := c0) (c1 := c1) (c2 := c2) hrd' (hgr _ hg)
    have hr : rets = ofrRets [f0, f1, f2, f3, f4] w0 w1 cur c0 c1 c2 nonce d0 d2 := by
      rw [hret]
      simp only [powSponge, hb, ↓reduceIte, hF, Fs.squeeze, ofrRets, ofrS2, ofrS, roundLen]
    rw [hr]
    simpa using hrel

/-- `opening_fold_round` at `0` bits relates every round's meaning. -/
theorem ofr0_rel {name : String} (hfn : FnIs name (osParams 11) ofrZeroBody) {args rets : List E}
    (hcan : AllCanonical (args.take 5)) (h : MeaningFoldRound 0 rd args rets) :
    coreProgram.Rel rd name args rets := by
  have hm := meaningOpeningFold_of hcan h
  match args, hm with
  | [_, _, _, _, _, _, _, _, _, _, _], hm' =>
    have hr : rets.length = 10 := by
      obtain ⟨-, d0, d2, -, hret⟩ := hm'
      rw [hret]; simp [Fs.squeeze, capOf]
    exact ofrZero_complete hfn rfl hr ((opening_fold_holds rd _ _).mpr hm')

/-- **The dispatch into the rate's `opening_fold_round` holds**: at the selector `g^ri`, the
rate's name `names[ri]` a specialization at `b` bits complete. -/
theorem foldCallC_some {names : List String} {ri b : ℕ} (hri : ri < names.length)
    (hrel : ∀ args rets, AllCanonical (args.take 5) → MeaningFoldRound b rd args rets →
      coreProgram.Rel rd names[ri] args rets) :
    FoldCallC (coreProgram.Rel rd) rd (some names) b (ofK (addressOfIndex ri)) :=
  fun _ hσ _ _ hcan h ↦ ⟨ri, hri, hσ, hrel _ _ hcan h⟩

end
end LeanVM.Guest.B1.Whir
