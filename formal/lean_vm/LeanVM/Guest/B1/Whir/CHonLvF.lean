/-
  LeanVM.Guest.B1.Whir.CHonLvF

  The final level's step of open_stacked's body at an accepting run's honest data.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStep
public import LeanVM.Guest.B1.Whir.CHonLvP
public import LeanVM.Guest.B1.Whir.Facts

/-!
# The final level's step on a run

`lvFin_gen`: the final level's step from its calls and memory (`FinC`) at the honest data, every
other hypothesis of `lvFin_step` discharged from the final level's run facts (`FinStep`, `FinOkF`,
the challenges before it).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- **The final level's step**, from the run's facts at the level, its batch `bt`. -/
theorem lvFin_gen {h : OsHD} {xs : List E} {b : ℕ} {tabs cur bt : E} {lane : ℕ} {w : WhirEnd}
    (hS : BodyStatic h.c)
    (hF : LvAt.FinStep h.logN lane h.c.yrLevel (h.Ls.getD h.c.yrLevel default) w)
    (hfo : FinOkF h.c h.logN h.c.yrLevel (osLvAt h.c h.c.yrLevel) (h.Ls.getD h.c.yrLevel default).level)
    (hg : (h.Ls.getD h.c.yrLevel default).s.alphas.length = (osLvAt h.c h.c.yrLevel).foldsOff)
    (hsuf : ∃ p, xs = p ++ (h.Ls.getD h.c.yrLevel default).xs)
    {st : OsSt} {σ : Val} (hq : QAt h b tabs cur xs h.c.yrLevel st σ)
    (hFC : ∀ C rd, H C rd → FinC C rd σ h.c h.c.yrLevel (osLvAt h.c h.c.yrLevel) (h.capAt h.c.yrLevel)
      (h.claimAt h.c.yrLevel) (cur * gen ^ (xs.length - (h.xsAt h.c.yrLevel).length))
      ((h.Ls.getD h.c.yrLevel default).finWD (digestHalves (h.root h.c.yrLevel)).1
        (digestHalves (h.root h.c.yrLevel)).2 bt (osPtrF h.c b (13 + 2 * h.c.yrLevel))
        (osPtrF h.c b (14 + 2 * h.c.yrLevel)))) :
    BlkA H σ st.k (osLevel h.c h.c.yrLevel (osLvAt h.c h.c.yrLevel) st).2.k
      (osLevel h.c h.c.yrLevel (osLvAt h.c h.c.yrLevel) st).1 (fun σ' ↦
      st.k ≤ (osLevel h.c h.c.yrLevel (osLvAt h.c h.c.yrLevel) st).2.k ∧
      QAt h b tabs cur xs (h.c.yrLevel + 1) (osLevel h.c h.c.yrLevel (osLvAt h.c h.c.yrLevel) st).2 σ' ∧
      RAt h b tabs h.c.yrLevel σ' ∧ RQ h b h.c.yrLevel bt σ') := by
  obtain ⟨-, hfold, hlog, hylen, hdepth, hqueries, -, hqu, -, hsq, -, hpo, -, -, hS5, hr3, hc4, hh8, -⟩ := hfo
  set L := h.Ls.getD h.c.yrLevel default with hL
  have hmu : L.mu h.logN = h.c.yrLog := by
    show h.logN - L.s1.alphas.length = _
    rw [LvAt.s1, roundsSpec_alphas_length, hg, hfold]; exact hlog
  have hdep : (osLvAt h.c h.c.yrLevel).depth = L.dp h.logN := by
    rw [hdepth]; show _ = L.mu h.logN + _; rw [hmu]
  have E := finEqs hF hfold hdep hqueries hsq (digestHalves (h.root h.c.yrLevel)).1
    (digestHalves (h.root h.c.yrLevel)).2 bt (osPtrF h.c b (13 + 2 * h.c.yrLevel))
    (osPtrF h.c b (14 + 2 * h.c.yrLevel)) (h.claimAt h.c.yrLevel)
  have i0 : h.c.yrLevel ≤ h.c.yrLevel := le_rfl
  have i1 : ¬ h.c.yrLevel + 1 ≤ h.c.yrLevel := by omega
  have hcap0 : h.capAt h.c.yrLevel = L.cap := by unfold OsHD.capAt; simp only [i0, ↓reduceIte]; rfl
  have hcap1 : h.capAt (h.c.yrLevel + 1) = (L.F3 h.logN).cap := by
    unfold OsHD.capAt; simp only [i1, ↓reduceIte]; rfl
  have hcl1 : h.claimAt (h.c.yrLevel + 1) = h.cl1F := by unfold OsHD.claimAt; simp only [i1, ↓reduceIte]
  have hcl0 : h.claimAt h.c.yrLevel = h.gclAt h.c.yrLevel := by
    unfold OsHD.claimAt; simp only [i0, ↓reduceIte]
  have hx0 : h.xsAt h.c.yrLevel = L.xs := by unfold OsHD.xsAt; simp only [i0, ↓reduceIte]; rfl
  have hx1 : h.xsAt (h.c.yrLevel + 1) = tailWords L.fw.pairs := by
    unfold OsHD.xsAt; simp only [i1, ↓reduceIte]; rfl
  refine lvFin_step (H := H) (h := h) hS hq _ rfl rfl hr3 hpo hS5 hc4 hh8 hqu hFC ?_ ?_ ?_ ?_
  · rw [hcap1, ← E.cap3, hcap0]
  · rw [hcl1, hcap0, hcl0]
    rfl
  · rw [hx0, hx1]
    obtain ⟨rw, W, hd, hrl, -, hxs, -, hok, -⟩ := hF
    have hrw : L.rw = rw := by unfold LvAt.rw; rw [hd]
    have hfw : L.fw = W := by unfold LvAt.fw; rw [hd]
    have hfl := hok.flen
    rw [← hrw] at hfl
    have e0 : W.fold.length = h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds := by
      rw [hfl, show h.logN - L.s1.alphas.length = h.c.yrLog from hmu, hylen, hfold]
    obtain ⟨p, hp⟩ := hsuf
    have e1 := congrArg List.length hxs
    have e2 := congrArg List.length hp
    rw [hfw]
    simp only [List.length_append, FinW.words, List.length_singleton] at e1 e2
    rw [hrl, hfold, e0] at e1
    omega
  · rw [hcap0, E.S2]
    exact ((lvAt_words _ h.logN hdep hqueries hsq).1).symm

end
end LeanVM.Guest.B1.Whir
