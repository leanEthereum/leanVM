/-
  LeanVM.Guest.B1.Whir.CHonBuf

  The honest words of open_stacked's own buffers, from the run's levels.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLv
public import LeanVM.Guest.B1.Whir.CFinA
public import LeanVM.Guest.B1.Place.OsBos

/-!
# The buffers' honest words

`OsHD`: the honest data, the configuration, the stack log, the run's levels (`Whir/CHon`) and
each level's Merkle cap cells and flags. From it: the levels' records `recs`, every fold
challenge `G`, the guest's claims `gclAt`, the closing rounds `tr` and their challenges `T`,
`λ⁻¹`, and each buffer's words (`ownAt j`, of buffer `j`'s size, `osSizesL` order: the head's
eleven, each non-final level's message, the final lane, the finish's seven); `own`.

`fitTo n xs`: `xs` cut or zero-padded to `n` words; the buffers split by levels are `segAt`
(`Place/OsBos`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `xs` cut or zero-padded to `n` words. -/
def fitTo (n : ℕ) (xs : List E) : List E := (List.range n).map fun j ↦ xs.getD j 0

theorem fitTo_length (n : ℕ) (xs : List E) : (fitTo n xs).length = n := by simp [fitTo]

theorem fitTo_getD {n : ℕ} {xs : List E} {j : ℕ} (hj : j < n) : (fitTo n xs).getD j 0 = xs.getD j 0 := by
  simp [fitTo, hj]

theorem fitTo_eq {n : ℕ} {xs : List E} (h : xs.length = n) : fitTo n xs = xs := by
  subst h
  refine List.ext_getElem (by simp [fitTo]) fun j h1 h2 ↦ ?_
  simp [fitTo, List.getElem?_eq_getElem h2]

/-- **The honest data**: the configuration, the stack log, the run's levels and each level's cap
cells and flags. -/
structure OsHD where
  c : OsCfg
  logN : ℕ
  Ls : List LvAt
  cv : ℕ → ℕ → E
  fv : ℕ → ℕ → E

namespace OsHD

variable (h : OsHD)

/-- Level `i` of the run. -/
abbrev L (i : ℕ) : LvAt := h.Ls.getD i default

/-- Level `i`'s row. -/
abbrev lv (i : ℕ) : OsLv := h.c.levels.getD i default

/-- The final level. -/
abbrev Lf : LvAt := h.L h.c.yrLevel

/-- The non-final levels' records. -/
def recs : List OsRec := lvsRecs h.logN h.Ls h.c.yrLevel

/-- Every fold challenge. -/
def G : List E := h.Lf.s1.alphas

/-- The guest's claim at level `i`'s start. -/
def gclAt (i : ℕ) : E := (h.L i).gcl (lvsRecs h.logN h.Ls i)

/-- The guest's claim after the final level's folds. -/
def cl1F : E := (roundsTr (h.lv h.c.yrLevel).folds h.Lf.cap (h.gclAt h.c.yrLevel) h.Lf.rw).2

/-- The closing rounds, the guest's: challenges, final claim, capacity. -/
def tr : List E × E × List E := tailRun h.Lf.fw.pairs (h.Lf.F3 h.logN).cap h.cl1F

/-- The tail challenges. -/
def T : List E := h.tr.1

/-- `λ⁻¹` of level `i`. -/
def li (i : ℕ) : E := ((h.L i).lam h.logN)⁻¹

/-- The fold rounds of every level, in order. -/
def allRounds : List FoldRound := h.Ls.flatMap (·.rounds)

/-- Level `i`'s root. -/
def root (i : ℕ) : Digest := ((h.L i).R.getD i default).1

/-! ## The head's buffers -/

/-- `final_msg`: the final lane. -/
def fmsgC : List E := h.Lf.fw.fold

/-- `level_roots`: each level's root's two cells. -/
def rootsC : List E := (List.range (2 * h.c.levels.length)).map fun e ↦
  if e % 2 = 0 then (digestHalves (h.root (e / 2))).1 else (digestHalves (h.root (e / 2))).2

/-- `fold_challenges`. -/
def fchC : List E := h.G

/-- `round_coefs`: each round's `α, β`. -/
def coefsC : List E := (List.range (2 * h.c.nFolds)).map fun e ↦
  let r := h.allRounds.getD (e / 2) ⟨0, 0⟩
  if e % 2 = 0 then r.alpha else r.beta

/-- `level_scales`: `λ²·λ^Q`. -/
def betasC : List E := (List.range h.c.levels.length).map fun i ↦
  if i < h.c.yrLevel then ((h.L i).lam h.logN) ^ 2 * ((h.L i).lam h.logN) ^ (h.lv i).queries else 0

/-- `level_lam_invs`: `λ⁻¹`. -/
def musC : List E := (List.range h.c.levels.length).map fun i ↦
  if i < h.c.yrLevel then h.li i else 0

/-- `level_hs`: each non-final level's high part, normalized, at its folds' offset. -/
def hsC : List E := (List.range h.c.nFolds).map
  (segAt h.c.yrLevel (fun l ↦ (h.lv l).foldsOff) (fun l ↦ (h.lv l).folds) fun l j ↦
    (h.L l).nw.high.getD j 0 *
      word (hsScale (h.lv l).vanish (h.lv l).highBits j (vanishInv ((h.lv l).vanish + (h.lv l).logCols))) 0)

/-- `ood_z`: each non-final level's out-of-domain point at the earlier levels' columns. -/
def oodzC : List E := (List.range h.c.colsTotal).map
  (segAt h.c.yrLevel (fun l ↦ (h.lv l).colsOff) (fun l ↦ (h.lv l).logCols) fun l t ↦
    ((h.L l).osRec h.logN).z0.getD t 0)

/-- `ood_scalars`: `λ` at `i + 1`. -/
def oodC : List E := (List.range h.c.levels.length).map fun e ↦
  if 1 ≤ e ∧ e - 1 < h.c.yrLevel then (h.L (e - 1)).lam h.logN else 0

/-- `query_positions`: each level's positions from its offset. -/
def qposC : List E :=
  (List.range h.c.posTotal).map
    (segAt h.c.levels.length (fun l ↦ (h.lv l).posOff) (fun l ↦ (h.lv l).squeezes * (128 / (h.lv l).depth))
      fun l k ↦ eOfNat (qwPosOf (h.lv l).depth ((h.L l).word h.logN (k / (128 / (h.lv l).depth)))
        (k % (128 / (h.lv l).depth))))

/-! ## Each level's buffers -/

/-- `sent`: a non-final level's message. -/
def sentC (i : ℕ) : List E := (h.L i).nw.x0 :: (h.L i).nw.x1 :: (h.L i).nw.high

/-- The final level's normalized lane. -/
def hsFC : List E := (List.range (h.c.yrLen + (h.lv h.c.yrLevel).folds)).map fun j ↦
  h.Lf.fw.fold.getD j 0 * word (hsScale (h.lv h.c.yrLevel).vanish (h.c.yrLog + 1) j 1) 0

/-! ## The buffers -/

/-- Buffer `j`'s honest words, before fitting to its size. -/
def ownW (j : ℕ) : List E :=
  let y := h.c.yrLevel
  if j < 11 then
    [h.fmsgC, h.rootsC, h.fchC, h.coefsC, h.betasC, h.musC, h.hsC, h.oodzC, h.oodC, h.qposC, []].getD j []
  else if j < 11 + y then h.sentC (j - 11)
  else if j = 11 + y then h.hsFC
  else [h.T, finPtC h.c h.G h.T, finPt1C h.c h.G h.T, finBdC h.c h.G h.T h.recs, finLsC h.c h.G h.T h.recs,
      finLaC h.c h.G h.T h.recs, finIchC h.c h.G h.T h.recs h.li h.tr.2.1].getD (j - (12 + y)) []

/-- **Buffer `j`'s honest words**, of its size. -/
def ownAt (j : ℕ) : List E := fitTo ((osSizesL h.c).getD j 0) (h.ownW j)

/-- **The buffers' honest words.** -/
def own : List (List E) := (List.range (osSizesL h.c).length).map h.ownAt

theorem own_len : List.Forall₂ (fun w s ↦ w.length = s) h.own (osSizesL h.c) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [own], fun i h1 h2 ↦ ?_⟩
  simp [own, ownAt, fitTo_length, List.getElem?_eq_getElem h2]

theorem own_getD {j : ℕ} (hj : j < (osSizesL h.c).length) : h.own.getD j [] = h.ownAt j := by
  simp [own, hj]

end OsHD

end
end LeanVM.Guest.B1.Whir
