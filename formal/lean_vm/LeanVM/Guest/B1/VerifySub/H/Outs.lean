/-
  LeanVM.Guest.B1.VerifySub.H.Outs

  What `verify_sub`'s callees return on an honest child: their results, as their `Out` says.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Kids

/-!
# The callees' results

`VsOuts S bs sqE outs`: the fourteen callees' results, read from `S.kids`' `Out`s; `verify_tables`'
at the GKR leaves `verify_bus_gkr` returned. `vs_outs`: callees whose results satisfy their `Out`s
(`OutsOk`) have these.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **The callees' results.** -/
structure VsOuts {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) (outs : List (List E × Main.Layout)) : Prop where
  len : outs.length = 14
  o0 : (outs.getD 0 ([], [])).1 = [gen ^ S.rate]
  o1 : (outs.getD 1 ([], [])).1 = [gen ^ S.logMem]
  o2 : (outs.getD 2 ([], [])).1 = [gen ^ max 0 (log2Ceil S.pushT)]
  o3 : Tables.cpOut S.logMem S.hs (outs.getD 3 ([], [])).1 (outs.getD 3 ([], [])).2
  o4 : (outs.getD 4 ([], [])).1 = [gen ^ max 16 (log2Ceil (Tables.stackTotal S.kappas))]
  o5 : (outs.getD 5 ([], [])).1 = S.sZ.cap
  o6 : (outs.getD 6 ([], [])).1 = [cellsOfState S.busSt false 0, cellsOfState S.busSt false 1] ++
    capOf S.busSt ++ [ptr (vb bs 1) * gen ^ 11 * gen ^ 2]
  o7 : (outs.getD 7 ([], [])).1 = [0]
  o8 : Tables.VbgOut S.s4.cap (ptr (ChildSegs.cG bs) * gen ^ S.xsG.length) S.rG.2.2
    (outs.getD 8 ([], [])).1 (outs.getD 8 ([], [])).2
  o9 : (outs.getD 9 ([], [])).1 = S.H.retsH (S.vtB bs sqE (S.leavesB (outs.take 9)))
  o10 : (outs.getD 10 ([], [])).1 =
    capOf S.s6.perm ++ [ptr (S.cK bs) * gen ^ S.xsK.length, S.kOut.value]
  o11 : (outs.getD 11 ([], [])).1 =
    [ringTarget S.kc.2.2 (S.rchs.take ringMapWidth) (S.rchs.drop ringMapWidth)]
  o12 : vsOsOut S.μs S.w (outs.getD 12 ([], [])).1 (outs.getD 12 ([], [])).2
  o13 : (outs.getD 13 ([], [])).1 = []
  term : S.termOk (outs.take 13)

theorem take_getD {α : Type} (l : List α) (d : α) {m n : ℕ} (h : m < n) :
    (l.take n).getD m d = l.getD m d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem vs_outs {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) (outs : List (List E × Main.Layout)) (hl : outs.length = 14)
    (ho : OutsOk (kidsAt (S.kids bs sqE) [] outs) outs) : VsOuts S bs sqE outs := by
  have h := fun m (hm : m < 13) ↦ outsOk_at ho m (by rw [S.kids_length]; omega) (by omega)
  have r : ∀ {a b : List E} {L : Main.Layout}, Returns a b L → b = a := fun h ↦ h.1
  have h3 := h 3 (by norm_num) rfl
  have h12 := h 12 (by norm_num) rfl
  have hterm : S.termOk (outs.take 13) := by
    refine ⟨?_, ?_⟩
    · show Tables.cpOut S.logMem S.hs ((outs.take 13).getD 3 ([], [])).1
        ((outs.take 13).getD 3 ([], [])).2
      rw [take_getD _ _ (by norm_num)]; exact h3
    · show vsOsOut S.μs S.w ((outs.take 13).getD 12 ([], [])).1
        ((outs.take 13).getD 12 ([], [])).2
      rw [take_getD _ _ (by norm_num)]; exact h12
  have h13 := outsOk_at ho 13 (by rw [S.kids_length]; omega) (by omega)
    (@decide_eq_true _ (Classical.propDecidable _) hterm)
  refine ⟨hl, ?_, ?_, ?_, h3, ?_, ?_, ?_, ?_, h 8 (by norm_num) rfl, ?_, ?_, ?_, h12, ?_, hterm⟩
  · exact r (h 0 (by norm_num) rfl)
  · exact r (h 1 (by norm_num) rfl)
  · exact r (h 2 (by norm_num) rfl)
  · exact r (h 4 (by norm_num) rfl)
  · exact r (h 5 (by norm_num) rfl)
  · exact r (h 6 (by norm_num) rfl)
  · exact r (h 7 (by norm_num) rfl)
  · exact r (h 9 (by norm_num) rfl)
  · exact r (h 10 (by norm_num) rfl)
  · exact r (h 11 (by norm_num) rfl)
  · exact r h13

end
end LeanVM.Guest.B1.VerifySub
