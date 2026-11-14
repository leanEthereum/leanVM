/-
  LeanVM.Guest.B1.Whir.CHonest

  The honest data of every accepting run of the stacked opening, as the placed lift takes it.
-/

module

public import LeanVM.Guest.B1.Whir.CHonEnd
public import LeanVM.Guest.B1.Whir.CHonFields5
public import LeanVM.Guest.B1.Whir.CHonBodyRun1

/-!
# `os_honest_Spec`

`osHonest`, `osHonest_run`: every accepting run (`HonRun`) has `OsHonestA` at the arm of `μ` and the rate `r`:
the buffers' honest words `own` (`Whir/CHonBuf`), the helpers' data `D` (`OsHD.D`), the stored
positions, the hinted caps and flags (`capW`, `flW`), the levels' `opening_queries` data, the
memory facts on every memory holding the buffers, and the body at values fixed before the callees
and the memory, returning the run's claim, point buffers, glued weight and residual
(`Whir/CHonBodyRun`). `os_honest_proved`: `B1.os_honest_Spec`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- The final level is the one whose `opening_queries` is final. -/
theorem final_iff {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).final = 1 ↔ l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := by
  obtain ⟨-, -, -, -, -, -, hfinal, -⟩ := (hR.lvb hl).qsh
  rw [oqSA, oq_final, hfinal]
  by_cases h : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel <;> simp [h]

/-- **OsHonestA's `batched_eq`.** -/
theorem fld_batched_eq : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    ((hdOf μ r Ls).D l).batched = if (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).final = 1 then 0 else
      oqChain (oqOddA (osCfgR (μ - minOpenLog) (r - 1)) l) (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).base
        ((hdOf μ r Ls).D l).lamInv
        (fun k ↦ foldRow (lanesOf (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).base
          (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (K.ofBits (((Ls.getD l default).qs μ).getD k 0)) (Ls.getD l default).rounds)
        (oqNA (osCfgR (μ - minOpenLog) (r - 1)) l) := by
  intro l hl
  have hD := (hdOf μ r Ls).D_eq l
  rw [hD.2.2.2]
  unfold OsHD.bat
  rw [show (hdOf μ r Ls).c = osCfgR (μ - minOpenLog) (r - 1) from rfl,
    show (hdOf μ r Ls).L l = Ls.getD l default from rfl, show (hdOf μ r Ls).logN = μ from rfl]
  by_cases hf : (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).final = 1
  · simp only [hf, ↓reduceIte]
  · have hne : l ≠ (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := fun h ↦ hf ((hR.final_iff hl).2 h)
    have e : (hdOf μ r Ls).lamInv l = ((hdOf μ r Ls).D l).lamInv := by
      rw [(hD.2.2.1 hne).2]
      show (if l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel then 0 else (hdOf μ r Ls).li l) = _
      simp only [hne, ↓reduceIte]
    simp only [hf, ↓reduceIte]
    rw [e]

/-- **OsHonestA's `qs_eq`.** -/
theorem fld_qs_eqA : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    ∀ k < oqQA (osCfgR (μ - minOpenLog) (r - 1)) l,
      ((Ls.getD l default).qs μ).getD k 0 =
        qwPosOf (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
          (sqSample ((hdOf μ r Ls).D l).w0 ((hdOf μ r Ls).D l).capL (k / osPerA (osCfgR (μ - minOpenLog) (r - 1)) l))
          (k % osPerA (osCfgR (μ - minOpenLog) (r - 1)) l) := by
  intro l hl k hk
  have ew : ((hdOf μ r Ls).D l).w0 = (Ls.getD l default).word μ 0 := by simp [OsHD.D, OsHD.word]; rfl
  have ec : ((hdOf μ r Ls).D l).capL = capOf ((Ls.getD l default).qS μ) := by simp [OsHD.D, OsHD.capL]; rfl
  rw [ew, ec, sqSample_word]
  exact hR.fld_qs_eq l hl k hk

/-- **The honest data of a run.** -/
noncomputable def osHonest {cur tabs : E} :
    OsHonestA (osCfgR (μ - minOpenLog) (r - 1))
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]) cur tabs xs
      w.target w.inner w.residual (w.point ++ List.replicate (pointCap - μ) 0)
      (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1) :=
  by
  refine { own := (hdOf μ r Ls).own
           own_len := ?_
           own_pt := ?_
           own_pt1 := ?_
           D := (hdOf μ r Ls).D
           capL_len := ?_
           posW := ?_
           lam_inv := ?_
           capW := capW Ls μ r
           flW := flW Ls μ r
           rounds := fun l ↦ (Ls.getD l default).rounds
           hsv := fun l ↦ if l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel then (hdOf μ r Ls).hsFC else []
           qs := fun l k ↦ ((Ls.getD l default).qs μ).getD k 0
           rows := fun l k ↦ ((Ls.getD l default).phase.map (·.leaf)).getD k []
           sibs := fun l k ↦ ((Ls.getD l default).phase.map (fun o ↦
             o.path.take (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth -
               ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth))).getD k []
           rounds_len := ?_
           hsv_len := ?_
           static := ?_
           qs_eq := ?_
           batched_eq := ?_
           caps := ?_
           qMem := ?_
           body := ?_ }
  · exact (hdOf μ r Ls).own_len
  · exact hR.fld_own_pt
  · exact hR.fld_own_pt1
  · intro l _; simp [OsHD.D, OsHD.capL, capOf]
  · exact hR.fld_posW
  · intro l hl
    obtain ⟨e1, e2⟩ := ((hdOf μ r Ls).D_eq l).2.2.1
      (by show l ≠ (osCfgR (μ - minOpenLog) (r - 1)).yrLevel; omega)
    rw [e1, e2]
    have h0 : (Ls.getD l default).lam μ ≠ 0 := (hR.recRun_run l hl).lam
    show (Ls.getD l default).lam μ * ((Ls.getD l default).lam μ)⁻¹ = 1
    have e := mul_inv_cancel₀ h0
    exact e
  · exact hR.fld_rounds_len
  · exact hR.fld_hsv_len
  · exact hR.fld_static
  · exact hR.fld_qs_eqA
  · exact hR.fld_batched_eq
  · exact hR.fld_caps
  · exact hR.fld_qMem
  · intro b
    have key := hR.body_run (cur := cur) (tabs := tabs) b
    rw [← hR.target_eq, ← hR.inner_eq] at key
    rw [hR.residual_eq]
    exact key

/-- **The honest data's hints are the run's.** -/
theorem osHonest_fields {cur tabs : E} :
    (hR.osHonest (cur := cur) (tabs := tabs)).capW = capW Ls μ r ∧
      (hR.osHonest (cur := cur) (tabs := tabs)).flW = flW Ls μ r ∧
      (hR.osHonest (cur := cur) (tabs := tabs)).qs = (fun l k ↦ ((Ls.getD l default).qs μ).getD k 0) ∧
      (hR.osHonest (cur := cur) (tabs := tabs)).rows =
        (fun l k ↦ ((Ls.getD l default).phase.map (·.leaf)).getD k []) ∧
      (hR.osHonest (cur := cur) (tabs := tabs)).sibs = (fun l k ↦ ((Ls.getD l default).phase.map (fun o ↦
        o.path.take (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth -
          ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth))).getD k []) := by
  unfold HonRun.osHonest
  dsimp only
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem osHonest_run {cur tabs : E} :
    Nonempty (OsHonestA (osCfgR (μ - minOpenLog) (r - 1))
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]) cur tabs xs
      w.target w.inner w.residual (w.point ++ List.replicate (pointCap - μ) 0)
      (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)) :=
  ⟨hR.osHonest⟩

end HonRun

/-- **Every accepting run has its honest data** (`Place/OsProtoSpec`). -/
theorem os_honest_proved : B1.os_honest_Spec := by
  intro μ r h1 h2 h3 h4 S root target cur tabs xs os w s' roots' hrun hnz hca
  obtain ⟨cfg, Ls, hR⟩ := honRun_of h1 h2 h3 h4 hrun hnz hca
  exact hR.osHonest_run

end
end LeanVM.Guest.B1.Whir
