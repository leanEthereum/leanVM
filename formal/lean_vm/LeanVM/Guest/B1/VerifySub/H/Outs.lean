/-
  LeanVM.Guest.B1.VerifySub.H.Outs

  What `verify_sub`'s callees return on an honest child: their results, as their `Out` says.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Loads

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **The callees' results.** -/
structure VsOuts {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) (outs : List (List E × Main.Layout)) : Prop where
  len : outs.length = 13
  o0 : (outs.getD 0 ([], [])).1 = [gen ^ S.rate]
  o1 : (outs.getD 1 ([], [])).1 = [gen ^ S.logMem]
  o2 : (outs.getD 2 ([], [])).1 = [gen ^ max 0 (log2Ceil (pushTotal S.logMem S.hs))]
  o3 : (outs.getD 3 ([], [])).1 = [0]
  o4 : (outs.getD 4 ([], [])).1 = [0]
  o5 : (outs.getD 5 ([], [])).1 =
    S.s5.cap ++ [ofK (addressOfIndex (vcG bs)) * gen ^ S.xsG.length] ++ S.vals
  o6 : (outs.getD 6 ([], [])).1 = S.vtRetsOf bs
  o7 : (outs.getD 7 ([], [])).1 =
    S.s7.cap ++ [ofK (addressOfIndex (S.cK bs)) * gen ^ S.xsK.length, S.word, S.m0]
  o8 : (outs.getD 8 ([], [])).1 = [polyEval (S.slices.map (phiMap · S.rchs)) gen]
  o9 : Tables.cpOut S.logMem S.hs (outs.getD 9 ([], [])).1 (outs.getD 9 ([], [])).2
  o10 : (outs.getD 10 ([], [])).1 = [gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas))]
  o11 : vsOsOut S.μs S.w (outs.getD 11 ([], [])).1 (outs.getD 11 ([], [])).2
  o12 : (outs.getD 12 ([], [])).1 = []
  term : S.termOk (outs.take 12)

theorem take_getD {α : Type} (l : List α) (d : α) {m n : ℕ} (h : m < n) :
    (l.take n).getD m d = l.getD m d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem vs_outs {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) (outs : List (List E × Main.Layout)) (hl : outs.length = 13)
    (ho : OutsOk (kidsAt (S.kids bs sqE) [] outs) outs) : VsOuts S bs sqE outs := by
  have h := fun m (hm : m < 12) ↦ outsOk_at ho m (by simp [ChildSegs.kids]; omega) (by omega)
  have r : ∀ {a b : List E} {L : Main.Layout}, Returns a b L → b = a := fun h ↦ h.1
  have h9 := h 9 (by norm_num) rfl
  have h11 := h 11 (by norm_num) rfl
  have hterm : S.termOk (outs.take 12) := by
    refine ⟨?_, ?_⟩
    · show Tables.cpOut S.logMem S.hs ((outs.take 12).getD 9 ([], [])).1
        ((outs.take 12).getD 9 ([], [])).2
      rw [take_getD _ _ (by norm_num)]; exact h9
    · show vsOsOut S.μs S.w ((outs.take 12).getD 11 ([], [])).1 ((outs.take 12).getD 11 ([], [])).2
      rw [take_getD _ _ (by norm_num)]; exact h11
  have h12 := outsOk_at ho 12 (by simp [ChildSegs.kids]) (by omega)
    (@decide_eq_true _ (Classical.propDecidable _) hterm)
  exact ⟨hl, r (h 0 (by norm_num) rfl), r (h 1 (by norm_num) rfl), r (h 2 (by norm_num) rfl),
    r (h 3 (by norm_num) rfl), r (h 4 (by norm_num) rfl), r (h 5 (by norm_num) rfl),
    r (h 6 (by norm_num) rfl), r (h 7 (by norm_num) rfl), r (h 8 (by norm_num) rfl), h9,
    r (h 10 (by norm_num) rfl), h11, r h12, hterm⟩

end
end LeanVM.Guest.B1.VerifySub
