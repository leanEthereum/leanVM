/-
  LeanVM.Guest.B1.Whir.CHonest

  The honest data of every accepting run of the stacked opening, as the placed lift takes it.
-/

module

public import LeanVM.Guest.B1.Place.OsHonestSpec
public import LeanVM.Guest.B1.Whir.CHonEnd
public import LeanVM.Guest.B1.Whir.CHonFields5
public import LeanVM.Guest.B1.Whir.CHonRes
public import LeanVM.Guest.B1.Whir.CHonBodyRun1
public import LeanVM.Guest.B1.Whir.CHonLvs

/-!
# `OsHonestSpec`

`osHonestSpec_holds`: every accepting run of `whirOpen μ r target` with no zero challenge, no vanishing
combiner and agreeing caps has `OsHonest` at its candidate (`Place/OsHonestSpec`): the buffers'
honest words `own` (`Whir/CHonBuf`), the squeezes' words and capacities, the levels'
`opening_queries` data, the memory facts on every memory holding the buffers, and the body at
values fixed before the callees and the memory, returning the run's claim, point buffers, glued
weight and residual (`Whir/CHonComp`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The honest data of a run.** -/
theorem osHonest_run {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
    {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt} {cur tabs : E}
    (hR : HonRun μ r target S root xs os w cfg Ls) :
    Nonempty (OsHonest (osCfg (candidate μ r))
      (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]) cur tabs xs
      w.target w.inner w.residual (w.point ++ List.replicate (pointCap - μ) 0)
      (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)) :=
  ⟨{ own := (hdOf μ r Ls).own
     own_len := (hdOf μ r Ls).own_len
     own_pt := hR.fld_own_pt
     own_pt1 := hR.fld_own_pt1
     word := fun l j ↦ (Ls.getD l default).word μ j
     cap := fun l j ↦ (Ls.getD l default).capSq μ j
     cap_len := fld_cap_len Ls μ
     cap_word := fld_cap_word Ls μ
     lamInv := (hdOf μ r Ls).lamInv
     rounds := fun l ↦ (Ls.getD l default).rounds
     hsv := fun l ↦ if l = (osCfg (candidate μ r)).yrLevel then (hdOf μ r Ls).hsFC else []
     qs := fun l k ↦ ((Ls.getD l default).qs μ).getD k 0
     rows := fun l k ↦ ((Ls.getD l default).phase.map (·.leaf)).getD k []
     sibs := fun l k ↦ ((Ls.getD l default).phase.map (fun o ↦
       o.path.take ((osLvAt (osCfg (candidate μ r)) l).depth - (osLvAt (osCfg (candidate μ r)) l).capDepth))).getD k []
     batched := (hdOf μ r Ls).bat
     mu := (hdOf μ r Ls).li
     rounds_len := hR.fld_rounds_len
     hsv_len := hR.fld_hsv_len
     static := fun l hl ↦ by have key := hR.fld_static l hl; exact key
     qs_eq := hR.fld_qs_eq
     batched_eq := fun l _ ↦ by unfold OsHD.bat; rfl
     rowsMem := hR.fld_rowsMem
     posMem := hR.fld_posMem
     qMem := fun b rd hm l hl ↦ by have key := hR.fld_qMem b rd hm l hl; exact key
     resRel := fun b rd hm l hl ↦ by have key := hR.fld_resRel b rd hm l hl; exact key
     body := fun b ↦ by
       have key := hR.body_run (cur := cur) (tabs := tabs) b
       have hc : (hdOf μ r Ls).c = osCfg (candidate μ r) := rfl
       have hres := hR.residual_eq
       rw [hc] at hres
       have hw : (hdOf μ r Ls).word = fun l j ↦ (Ls.getD l default).word μ j := by
         funext l j; rfl
       rw [← hR.target_eq, ← hR.inner_eq, ← hres, hw] at key
       exact key }⟩

/-- **Every accepting run has its honest data** (`Place/OsHonestSpec`). -/
theorem osHonestSpec_holds : OsHonestSpec := by
  intro μ r h1 h2 h3 h4 S root target cur tabs xs os w s' roots' hrun hnz hnc hca
  obtain ⟨cfg, Ls, hR⟩ := honRun_of h1 h2 h3 h4 hrun hnz hnc hca
  exact osHonest_run hR

end
end LeanVM.Guest.B1.Whir
