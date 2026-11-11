/-
  LeanVM.Guest.B1.Whir.CHonLvs

  Each level's step of open_stacked's body at an accepting run's honest data.
-/

module

public import LeanVM.Guest.B1.Whir.CHonInv
public import LeanVM.Guest.B1.Whir.CHonStep

/-!
# The levels' steps on a run

`OsHD.bat h l`: the guest's batch of level `l` (`opening_queries`' return, `0` at the final level).
`lvMid_run`: on a run (`HonRun`), a non-final level's step from its calls and memory (`MidC`) at the
honest data, every other hypothesis of `lvMid_step` discharged from the run.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The guest's batch of level `l`.** -/
noncomputable def OsHD.bat (h : OsHD) (l : ℕ) : E :=
  if (oqS h.c l).final = 1 then 0 else
    oqChain (oqOdd h.c l) (oqS h.c l).base (h.lamInv l)
      (fun k ↦ foldRow (lanesOf (oqS h.c l).base (((h.L l).phase.map (·.leaf)).getD k []))
        (K.ofBits (((h.L l).qs h.logN).getD k 0)) (h.L l).rounds) (oqN h.c l)

theorem OsHD.capAt_of (h : OsHD) {l : ℕ} (hl : l ≤ h.c.yrLevel) : h.capAt l = (h.L l).cap := by
  simp [OsHD.capAt, hl]

theorem OsHD.claimAt_of (h : OsHD) {l : ℕ} (hl : l ≤ h.c.yrLevel) : h.claimAt l = h.gclAt l := by
  simp [OsHD.claimAt, hl]

theorem OsHD.xsAt_of (h : OsHD) {l : ℕ} (hl : l ≤ h.c.yrLevel) : h.xsAt l = (h.L l).xs := by
  simp [OsHD.xsAt, hl]

theorem LvAt.lam_next {L L' : LvAt} {logN index : ℕ} (hN : LvAt.NextStep logN index L L') :
    L.lam logN ≠ 0 := by
  obtain ⟨rw, W, hd, -, -, -, -, hnext, -⟩ := hN
  have hrw : L.rw = rw := by unfold LvAt.rw; rw [hd]
  unfold LvAt.lam; rw [hd]
  simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
  exact hnext.lam

theorem LvAt.qs_next_length {L L' : LvAt} {logN index : ℕ} (hN : LvAt.NextStep logN index L L') :
    (L.qs logN).length = L.level.queries := by
  obtain ⟨rw, W, hd, -⟩ := hN
  unfold LvAt.qs; rw [hd]; simp [NextW.qs, sqPositions]

theorem LvAt.phase_next_length {L L' : LvAt} {logN index : ℕ} (hN : LvAt.NextStep logN index L L') :
    L.phase.length = (L.qs logN).length := by
  obtain ⟨rw, W, hd, -, -, -, -, hnext, -⟩ := hN
  have hrw : L.rw = rw := by unfold LvAt.rw; rw [hd]
  unfold LvAt.phase LvAt.qs; rw [hd]
  simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
  exact hnext.plen

variable {H : CallRel → Reader → Prop}

/-- **A non-final level's step**, from the run's facts at the level. -/
theorem lvMid_gen {h : OsHD} {xs : List E} {b : ℕ} {tabs cur : E} (hS : BodyStatic h.c) {l : ℕ}
    (hl : l < h.c.yrLevel) (hy : h.c.yrLevel + 1 = h.c.levels.length) (hLl : l + 1 < h.Ls.length)
    (hN : LvAt.NextStep h.logN l (h.Ls.getD l default) (h.Ls.getD (l + 1) default))
    (hmo : MidOk h.c h.logN l (osLvAt h.c l) (h.Ls.getD l default).level (h.Ls.getD (l + 1) default).level
      (osLvAt h.c (l + 1)))
    (hg : (h.Ls.getD l default).s.alphas.length = (osLvAt h.c l).foldsOff)
    (hrecF : ∀ q ∈ lvsRecs h.logN h.Ls l, q.F ≤ (h.Ls.getD l default).s.alphas.length)
    (hsuf : ∃ p, xs = p ++ (h.Ls.getD l default).xs)
    {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs l st σ)
    (hMC : ∀ C rd, H C rd → MidC C rd σ h.c l (osLvAt h.c l) (h.capAt l) (h.claimAt l)
      (cur * gen ^ (xs.length - (h.xsAt l).length))
      ((h.Ls.getD l default).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 (h.bat l)
        (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l)))) :
    BlkA H σ st.k (osLevel h.c l (osLvAt h.c l) st).2.k (osLevel h.c l (osLvAt h.c l) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c l (osLvAt h.c l) st).2.k ∧
      QAt h b tabs cur xs (l + 1) (osLevel h.c l (osLvAt h.c l) st).2 σ' ∧
      RAt h b tabs l σ' ∧ RQ h b l (h.bat l) σ') := by
  obtain ⟨hnf, hfold, hcols, hcols1, hdepth, hqueries, hq0, hqu, hP1, hsq, hpwP, hpwQ, hpo, hsq1, hsqo,
    hS5, hr3, hood, hc4, hh8, hshape, hoff', hqsh, hNo, -⟩ := hmo
  have hmu : (h.Ls.getD l default).mu h.logN = (osLvAt h.c l).logCols := by
    show h.logN - (h.Ls.getD l default).s1.alphas.length = _
    rw [LvAt.s1, roundsSpec_alphas_length, hg, hfold]; exact hcols
  have hdep : (osLvAt h.c l).depth = (h.Ls.getD l default).dp h.logN := by
    rw [hdepth]; show _ = (h.Ls.getD l default).mu h.logN + _; rw [hmu]
  have E := midEqs hN hfold hmu hdep hqueries hsq hcols1 (digestHalves (h.root l)).1
    (digestHalves (h.root l)).2 (h.bat l)
    (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l))
    (h.claimAt l)
  have hcapl : h.capAt l = (h.Ls.getD l default).cap := h.capAt_of
    (show l ≤ h.c.yrLevel by omega)
  have hcap1 : h.capAt (l + 1) = (h.Ls.getD (l + 1) default).cap := h.capAt_of
    (show l + 1 ≤ h.c.yrLevel by omega)
  have hcl0 : h.claimAt l = (h.Ls.getD l default).gcl (lvsRecs h.logN h.Ls l) :=
    h.claimAt_of (show l ≤ h.c.yrLevel by omega)
  have hcl1 : h.claimAt (l + 1) = (h.Ls.getD (l + 1) default).gcl (lvsRecs h.logN h.Ls (l + 1)) :=
    h.claimAt_of (show l + 1 ≤ h.c.yrLevel by omega)
  have hx0 : h.xsAt l = (h.Ls.getD l default).xs :=
    h.xsAt_of (show l ≤ h.c.yrLevel by omega)
  have hx1 : h.xsAt (l + 1) = (h.Ls.getD (l + 1) default).xs :=
    h.xsAt_of (show l + 1 ≤ h.c.yrLevel by omega)
  have hlam : (h.Ls.getD l default).lam h.logN ≠ 0 := LvAt.lam_next hN
  have hli : h.lamInv l = ((h.Ls.getD l default).lam h.logN)⁻¹ := by
    simp [OsHD.lamInv, OsHD.li, show l ≠ h.c.yrLevel by omega]
  -- the batch
  obtain ⟨-, hodd, hbase, -, -, -, hfinal, -, -, -, hcount⟩ := hqsh
  have hbat0 : h.bat l = oqChain (oqOdd h.c l)
      (oqS h.c l).base ((h.Ls.getD l default).lam h.logN)⁻¹
      (fun k ↦ foldRow (lanesOf (oqS h.c l).base
        (((h.Ls.getD l default).phase.map (·.leaf)).getD k []))
        (K.ofBits (((h.Ls.getD l default).qs h.logN).getD k 0)) (h.Ls.getD l default).rounds)
      (oqN h.c l) := by
    rw [OsHD.bat, hli]
    have : (oqS h.c l).final = 0 := by simp only [oqS, OqShape.oq]; exact hfinal
    simp only [this, zero_ne_one, ↓reduceIte]
  have hob : (oqS h.c l).base = 1 ∨ oqOdd h.c l = 0 := by
    have e1 : (oqS h.c l).base = if l = 0 then 1 else 0 := by
      simp only [oqS, OqShape.oq]; exact hbase
    have e2 : oqOdd h.c l = (osLvAt h.c l).queries % 2 *
      (if l = 0 then 1 else 0) := by simp only [oqOdd]; exact hodd
    by_cases h0 : l = 0
    · left; rw [e1]; simp [h0]
    · right; rw [e2]; simp [h0]
  have hodd1 : oqOdd h.c l ≤ 1 := by
    have e2 : oqOdd h.c l = (osLvAt h.c l).queries % 2 *
      (if l = 0 then 1 else 0) := by simp only [oqOdd]; exact hodd
    rw [e2]; split_ifs <;> omega
  have hQ : oqCount (oqOdd h.c l) (oqS h.c l).base
      (oqN h.c l) = (h.Ls.getD l default).level.queries := by
    rw [hqueries]; simp only [oqOdd, oqS, OqShape.oq, oqN]; exact hcount
  have hbat : ((h.Ls.getD l default).lam h.logN) ^ (h.Ls.getD l default).level.queries * h.bat l =
      ∑ k ∈ Finset.range ((h.Ls.getD l default).qs h.logN).length, ((h.Ls.getD l default).lam h.logN) ^ k *
        foldRow (specLanes l (((h.Ls.getD l default).phase.map (·.leaf)).getD k []))
          (K.ofBits (((h.Ls.getD l default).qs h.logN).getD k 0)) (h.Ls.getD l default).rounds := by
    rw [hbat0, LvAt.qs_next_length hN]
    refine hbat_of hlam hodd1 hob hQ fun k _ ↦ ?_
    have e1 : (oqS h.c l).base = if l = 0 then 1 else 0 := by
      simp only [oqS, OqShape.oq]; exact hbase
    rw [e1, lanesOf_base]
  have hC := midClaim hN hfold hmu hdep hqueries hsq hcols1 hrecF (digestHalves (h.root l)).1
    (digestHalves (h.root l)).2 (h.bat l)
    (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l)) hbat
  have := lvMid_step (H := H) (h := h) hS hl hq _ rfl rfl hr3 hood hpo hS5 hc4 hh8 hqu hpwQ
    (by rw [hcapl, E.lam]; exact hlam)
    hMC (by rw [hcapl, hcap1, ← E.cap']) (by rw [hcapl, hcl0, hcl1, lvsRecs_succ (by omega)]; exact hC.1)
    (by
      rw [hx0, hx1]
      obtain ⟨rw, W, hd, hrl, -, hxs, -, hnext, -⟩ := hN
      obtain ⟨p, hp⟩ := hsuf
      have e1 := congrArg List.length hxs
      have e2 := congrArg List.length hp
      have e3 := hnext.hlen
      simp only [List.length_append, NextW.words, List.length_cons, List.length_nil] at e1 e2
      rw [e3, hfold] at e1
      rw [hrl, hfold] at e1
      omega)
    (by rw [hcapl, E.S2]; exact ((lvAt_words _ h.logN hdep hqueries hsq).1).symm) (by rw [hcapl, E.lam, hli])
  have eb : ((h.Ls.getD l default).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 (h.bat l)
      (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l))).batched = h.bat l := by
    simp only [LvAt.midW]
  rw [eb] at this
  exact this

end
end LeanVM.Guest.B1.Whir
