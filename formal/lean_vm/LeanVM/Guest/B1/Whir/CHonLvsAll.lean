/-
  LeanVM.Guest.B1.Whir.CHonLvsAll

  open_stacked's levels in sequence at an accepting run's honest data.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLvs
public import LeanVM.Guest.B1.Whir.CHonLvF
public import LeanVM.Guest.B1.Whir.CHonLvCF

/-!
# The levels, honestly

`LvFacts h xs lane w`: what the levels' completeness takes of the honest data: the
configuration's facts (`BodyStatic`, `HonStatic`, `HonNames`), each level's step of the run and
checked facts, the challenges and words before it, the carried capacities' lengths, the next
roots, the rounds' counts and the out-of-domain points' lengths.

`LvFacts.lv`: a level's step from `QAt l` to `QAt (l + 1)` and `RAt l` under `OsHA` (`lvMid_gen`
with `midC_of`, `lvFin_gen` with `finC_of`). `LvFacts.levels`: the levels in sequence
(`osLevels_complete`), every level's `RAt`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **What the levels' completeness takes of the honest data.** -/
structure LvFacts (h : OsHD) (xs : List E) (lane : ℕ) (w : WhirEnd) : Prop where
  bs : BodyStatic h.c
  hs : HonStatic h.c
  nm : HonNames h.c
  len : h.Ls.length = h.c.levels.length
  step : ∀ l < h.c.yrLevel, LvAt.NextStep h.logN l (h.L l) (h.L (l + 1))
  mid : ∀ l < h.c.yrLevel, MidOk h.c h.logN l (h.c.levels.getD l default) (h.L l).level (h.L (l + 1)).level
    (h.c.levels.getD (l + 1) default)
  last : LvAt.FinStep h.logN lane h.c.yrLevel h.Lf w
  fin : FinOkF h.c h.logN h.c.yrLevel (h.c.levels.getD h.c.yrLevel default) h.Lf.level
  gam : ∀ l < h.c.levels.length, (h.L l).s.alphas.length = (h.c.levels.getD l default).foldsOff
  recF : ∀ l < h.c.levels.length, ∀ q ∈ lvsRecs h.logN h.Ls l, q.F ≤ (h.L l).s.alphas.length
  suf : ∀ l < h.c.levels.length, ∃ p, xs = p ++ (h.L l).xs
  cap5 : ∀ l < h.c.levels.length, (h.L l).cap.length = 5
  rootN : ∀ l < h.c.yrLevel, digestHalves (h.root (l + 1)) = ((h.L l).nw.x0, (h.L l).nw.x1)
  G : ∀ l < h.c.levels.length, ∀ j < (h.c.levels.getD l default).folds,
    h.G.getD ((h.c.levels.getD l default).foldsOff + j) 0 =
      (roundsSpec (h.c.levels.getD l default).folds (h.L l).s (h.L l).cap (h.L l).rw).1.alphas.getD
        ((h.L l).s.alphas.length + j) 0
  rl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (h.c.levels.getD i default).folds
  z0 : ∀ l < h.c.yrLevel, ((h.L l).osRec h.logN).z0.length = (h.c.levels.getD l default).logCols
  lane : h.Lf.fw.fold.length = h.c.yrLen + (h.c.levels.getD h.c.yrLevel default).folds

namespace LvFacts

variable {h : OsHD} {xs : List E} {lane : ℕ} {w : WhirEnd} (F : LvFacts h xs lane w)
include F

theorem yrE : h.c.yrLevel + 1 = h.c.levels.length := F.hs.yr

/-- **A level's step**, from its calls and memory by `midC_of` and `finC_of`. -/
theorem lv {b : ℕ} {cur tabs : E} :
    ∀ l < h.c.levels.length, ∀ st σ, QAt h b tabs cur xs l st σ →
      BlkA (fun C rd ↦ OsHA C rd h.c b h.own cur tabs xs) σ st.k
        (osLevel h.c l (h.c.levels.getD l default) st).2.k (osLevel h.c l (h.c.levels.getD l default) st).1
        (fun σ' ↦ st.k ≤ (osLevel h.c l (h.c.levels.getD l default) st).2.k ∧
          QAt h b tabs cur xs (l + 1) (osLevel h.c l (h.c.levels.getD l default) st).2 σ' ∧
          RAt h b tabs l (h.bat l) σ') := by
  intro l hl st σ hq
  have hy := F.yrE
  have hsfx : (h.L l).xs <:+ xs := by obtain ⟨p, hp⟩ := F.suf l hl; exact ⟨p, hp.symm⟩
  by_cases hfin : l = h.c.yrLevel
  · subst hfin
    obtain ⟨-, hfold, hlog, -, hdepth, hqueries, -, -, -, hsq, -⟩ := F.fin
    have hdep : (h.c.levels.getD h.c.yrLevel default).depth = h.Lf.dp h.logN := by
      rw [hdepth]
      show _ = h.logN - h.Lf.s1.alphas.length + _
      rw [LvAt.s1, roundsSpec_alphas_length, F.gam _ hl, hfold, hlog]
    exact lvFin_gen F.bs F.last F.fin (F.gam _ hl) (F.suf _ hl) hq fun C rd hH ↦
      finC_of F.hs F.nm hq.ptr hq.tabs (h.bat h.c.yrLevel) F.last hfold hdep hqueries hsq (F.cap5 _ hl)
        hsfx F.lane (F.G _ hl) F.len F.rl C rd hH
  · have hl' : l < h.c.yrLevel := by omega
    obtain ⟨-, hfold, hcols, hcols1, hdepth, hqueries, -, -, -, hsq, -⟩ := F.mid l hl'
    have hmu : (h.L l).mu h.logN = (h.c.levels.getD l default).logCols := by
      show h.logN - (h.L l).s1.alphas.length = _
      rw [LvAt.s1, roundsSpec_alphas_length, F.gam l hl, hfold]; exact hcols
    have hdep : (h.c.levels.getD l default).depth = (h.L l).dp h.logN := by
      rw [hdepth]; show _ = (h.L l).mu h.logN + _; rw [hmu]
    exact lvMid_gen F.bs hl' hy (by rw [F.len]; omega) (F.step l hl') (F.mid l hl') (F.gam l hl)
      (F.recF l hl) (F.suf l hl) hq fun C rd hH ↦
      midC_of F.hs F.nm hl' hq.ptr hq.tabs (h.bat l) (F.step l hl') hfold hmu hdep hqueries hsq hcols1
        (F.cap5 l hl) hsfx (F.rootN l hl') (F.G l hl) F.len F.rl (F.z0 l hl') C rd hH

/-- **The levels in sequence**, every level's allocation and dispatches. -/
theorem levels {b : ℕ} {cur tabs : E} (st : OsSt) (σ : Val) (hq : QAt h b tabs cur xs 0 st σ) :
    BlkA (fun C rd ↦ OsHA C rd h.c b h.own cur tabs xs) σ st.k (osLevels h.c 0 h.c.levels st).2.k
      (osLevels h.c 0 h.c.levels st).1 (fun σ' ↦ st.k ≤ (osLevels h.c 0 h.c.levels st).2.k ∧
        QAt h b tabs cur xs h.c.levels.length (osLevels h.c 0 h.c.levels st).2 σ' ∧
        ∀ i < h.c.levels.length, RAt h b tabs i (h.bat i) σ') := by
  have key := osLevels_complete (H := fun C rd ↦ OsHA C rd h.c b h.own cur tabs xs) h.c
    (fun l st σ ↦ QAt h b tabs cur xs l st σ) (fun l σ' ↦ RAt h b tabs l (h.bat l) σ')
    (fun _ _ _ _ hq ha ↦ hq.agree ha) h.c.levels 0 (fun i hi st σ hq ↦ by
      rw [Nat.zero_add] at hq ⊢
      rw [show h.c.levels[i] = h.c.levels.getD i default from (List.getD_eq_getElem _ _ hi).symm]
      exact F.lv i hi st σ hq) st σ hq
  refine key.mono fun σ' ⟨k1, k2, k3⟩ ↦ ⟨k1, by rwa [Nat.zero_add] at k2, fun i hi ↦ ?_⟩
  have := k3 i hi
  rwa [Nat.zero_add] at this

end LvFacts

end
end LeanVM.Guest.B1.Whir
