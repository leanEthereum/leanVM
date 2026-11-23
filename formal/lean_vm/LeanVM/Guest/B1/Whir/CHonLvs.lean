/-
  LeanVM.Guest.B1.Whir.CHonLvs

  Each level's step of open_stacked's body at an accepting run's honest data.
-/

module

public import LeanVM.Guest.B1.Whir.Facts
public import LeanVM.Guest.B1.Whir.CHonLvP
public import LeanVM.Guest.B1.Whir.CHonStep

/-!
# The levels' steps on a run

`OsHD.bat h l`: the guest's batch of level `l` (`opening_queries`' return, `0` at the final level).
`lvMid_gen`: a non-final level's step from its calls and memory (`MidC`) at the honest data, every
other hypothesis of `lvMid_step` discharged from the level's facts (`LvAt.NextStep`, `MidOk`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The guest's batch of level `l`.** -/
noncomputable def OsHD.bat (h : OsHD) (l : ℕ) : E :=
  if (oqSA h.c l).final = 1 then 0 else
    oqChain (oqOddA h.c l) (oqSA h.c l).base (h.lamInv l)
      (fun k ↦ foldRow (lanesOf (oqSA h.c l).base (((h.L l).phase.map (·.leaf)).getD k []))
        (K.ofBits (((h.L l).qs h.logN).getD k 0)) (h.L l).rounds) (oqNA h.c l)

theorem OsHD.capAt_of (h : OsHD) {l : ℕ} (hl : l ≤ h.c.yrLevel) : h.capAt l = (h.L l).cap := by
  simp [OsHD.capAt, hl]

theorem OsHD.claimAt_of (h : OsHD) {l : ℕ} (hl : l ≤ h.c.yrLevel) : h.claimAt l = h.gclAt l := by
  simp [OsHD.claimAt, hl]

theorem OsHD.xsAt_of (h : OsHD) {l : ℕ} (hl : l ≤ h.c.yrLevel) : h.xsAt l = (h.L l).xs := by
  simp [OsHD.xsAt, hl]

theorem LvAt.qs_next_length {L L' : LvAt} {logN index : ℕ} (hN : LvAt.NextStep logN index L L') :
    (L.qs logN).length = L.level.queries := by
  obtain ⟨rw, W, hd, -⟩ := hN
  unfold LvAt.qs; rw [hd]; simp [NextW.qs, sqPositions]

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-- **A non-final level's step**, from the run's facts at the level. -/
theorem lvMid_gen {h : OsHD} {xs : List E} {b : ℕ} {tabs cur : E} (hS : BodyStatic h.c) {l : ℕ}
    (hl : l < h.c.yrLevel) (hy : h.c.yrLevel + 1 = h.c.levels.length) (hLl : l + 1 < h.Ls.length)
    (hN : LvAt.NextStep h.logN l (h.Ls.getD l default) (h.Ls.getD (l + 1) default))
    (hmo : MidOk h.c h.logN l ((h.c.levels.getD l default)) (h.Ls.getD l default).level (h.Ls.getD (l + 1) default).level
      ((h.c.levels.getD (l + 1) default)))
    (hg : (h.Ls.getD l default).s.alphas.length = ((h.c.levels.getD l default)).foldsOff)
    (hrecF : ∀ q ∈ lvsRecs h.logN h.Ls l, q.F ≤ (h.Ls.getD l default).s.alphas.length)
    (hsuf : ∃ p, xs = p ++ (h.Ls.getD l default).xs)
    {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs l st σ) (hiz : IsZeroC (HM M H)) (rd0 : Reader)
    (hl0 : LowDef 11 rd0)
    (hMC : ∀ C rd, HM M H C rd → MidC C rd σ h.c l ((h.c.levels.getD l default)) (h.capAt l) (h.claimAt l)
      (cur * gen ^ (xs.length - (h.xsAt l).length))
      ((h.Ls.getD l default).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 (h.bat l)
        (osPtrA h.c b (12 + l)))) (hag0 : ∀ C rd, H C rd → LowAgree rd rd0) :
    BlkA M H σ st.k (osLevel h.c l ((h.c.levels.getD l default)) st).2.k (osLevel h.c l ((h.c.levels.getD l default)) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c l ((h.c.levels.getD l default)) st).2.k ∧
      QAt h b tabs cur xs (l + 1) (osLevel h.c l ((h.c.levels.getD l default)) st).2 σ' ∧
      RAt h b tabs l (h.bat l) σ' ∧
      cvOf (osLevel h.c l (h.c.levels.getD l default) st).1 σ' = cvMid l (h.c.levels.getD l default)
        (h.capAt l) (h.claimAt l) (cur * gen ^ (xs.length - (h.xsAt l).length))
        ((h.Ls.getD l default).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 (h.bat l)
          (osPtrA h.c b (12 + l))) (σ' (.n osRate)) (osPtrA h.c b 7) (osPtrA h.c b 3) (osPtrA h.c b 6)
        (osPtrA h.c b osIxQposA) (osPtrA h.c b osIxQbpA) tabs) := by
  obtain ⟨hnf, hfold, hcols, hcols1, hdepth, hqueries, hq0, hqu, hP1, hsq, hpwP, hpwQ, hpo, hsq1, hsqo,
    hS5, hr3, hf5, hood, hh8, hshape, hfo', hqsh, -⟩ := hmo
  have hmu : (h.Ls.getD l default).mu h.logN = ((h.c.levels.getD l default)).logCols := by
    show h.logN - (h.Ls.getD l default).s1.alphas.length = _
    rw [LvAt.s1, roundsSpec_alphas_length, hg, hfold]; exact hcols
  have hdep : ((h.c.levels.getD l default)).depth = (h.Ls.getD l default).dp h.logN := by
    rw [hdepth]; show _ = (h.Ls.getD l default).mu h.logN + _; rw [hmu]
  have E := midEqs hN hfold hmu hdep hqueries hsq hcols1 (digestHalves (h.root l)).1
    (digestHalves (h.root l)).2 (h.bat l)
    (osPtrA h.c b (12 + l))
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
  have hli : h.lamInv l = lamInvOf ((h.Ls.getD l default).lam h.logN) := by
    simp [OsHD.lamInv, OsHD.li, show l ≠ h.c.yrLevel by omega]
  -- the batch
  obtain ⟨-, hbase, -, -, hfinal, -⟩ := hqsh
  have hbat0 : h.bat l = oqChain (oqOddA h.c l)
      (oqSA h.c l).base (lamInvOf ((h.Ls.getD l default).lam h.logN))
      (fun k ↦ foldRow (lanesOf (oqSA h.c l).base
        (((h.Ls.getD l default).phase.map (·.leaf)).getD k []))
        (K.ofBits (((h.Ls.getD l default).qs h.logN).getD k 0)) (h.Ls.getD l default).rounds)
      (oqNA h.c l) := by
    rw [OsHD.bat, hli]
    have : (oqSA h.c l).final = 0 := by simp only [oqSA, OqShape.oq, osLvA]; exact hfinal
    simp only [this, zero_ne_one, ↓reduceIte]
  have e1 : (oqSA h.c l).base = if l = 0 then 1 else 0 := by
    simp only [oqSA, OqShape.oq, osLvA]; exact hbase
  have hob : (oqSA h.c l).base = 1 ∨ oqOddA h.c l = 0 := by
    by_cases h0 : l = 0
    · left; rw [e1]; simp [h0]
    · right; simp [oqOddA, lqOdd, lvBase, h0]
  have hodd1 : oqOddA h.c l ≤ 1 := by
    simp only [oqOddA, lqOdd]; split_ifs <;> omega
  have hQ : oqCount (oqOddA h.c l) (oqSA h.c l).base
      (oqNA h.c l) = (h.Ls.getD l default).level.queries := by
    rw [hqueries, e1]
    simp only [oqCount, oqOddA, oqNA, lqOdd, lqIters, osLvA, lvBase]
    split_ifs <;> omega
  have hbat : (h.Ls.getD l default).lam h.logN * (h.Ls.getD l default).lam h.logN *
      (((h.Ls.getD l default).lam h.logN) ^ (h.Ls.getD l default).level.queries * h.bat l) =
      (h.Ls.getD l default).lam h.logN * (h.Ls.getD l default).lam h.logN *
      ∑ k ∈ Finset.range ((h.Ls.getD l default).qs h.logN).length, ((h.Ls.getD l default).lam h.logN) ^ k *
        foldRow (specLanes l (((h.Ls.getD l default).phase.map (·.leaf)).getD k []))
          (K.ofBits (((h.Ls.getD l default).qs h.logN).getD k 0)) (h.Ls.getD l default).rounds := by
    rw [hbat0, LvAt.qs_next_length hN]
    refine hbat_of hodd1 hob hQ fun k _ ↦ ?_
    rw [e1, lanesOf_base]
  have hC := midClaim hN hfold hmu hdep hqueries hsq hcols1 hrecF (digestHalves (h.root l)).1
    (digestHalves (h.root l)).2 (h.bat l)
    (osPtrA h.c b (12 + l)) hbat
  have hrwl : ((h.Ls.getD l default).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 (h.bat l)
      (osPtrA h.c b (12 + l))).rw.length = 5 * (h.c.levels.getD l default).folds := by
    obtain ⟨rw, W, hd, hrl, -⟩ := hN
    show (h.Ls.getD l default).rw.length = _
    unfold LvAt.rw; rw [hd, hrl, hfold]
  have := lvMid_step (M := M) (H := H) (h := h) hS hl hq _ rd0 hl0 hrwl rfl hf5 hood hpo (by omega) hqu
    (by omega) hh8 hiz hMC hag0 (by rw [hcapl, hcap1, ← E.cap']) (by rw [hcapl, hcl0, hcl1, lvsRecs_succ (by omega)]; exact hC.1)
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
    (by rw [hcapl, E.S2]; exact ((lvAt_words _ h.logN hdep hqueries hsq).1).symm)
    (by rw [hcapl, E.S2]; rfl) (by rw [hcapl, E.lam]; rfl) rfl rfl
  have eb : ((h.Ls.getD l default).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 (h.bat l)
      (osPtrA h.c b (12 + l))).batched = h.bat l := by
    simp only [LvAt.midW]
  rw [eb] at this
  exact this

end
end LeanVM.Guest.B1.Whir
