/-
  LeanVM.Guest.B1.Whir.CHonBuf

  The honest words of open_stacked's own buffers on f128, from the run's levels.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLv
public import LeanVM.Guest.B1.Whir.CFinA
public import LeanVM.Guest.B1.Place.OsHonest

/-!
# The buffers' honest words

`OsHD`: the honest data, the configuration, the stack log, the run's levels (`Whir/CHon`) and
each level's Merkle cap cells and flags. From it: the levels' records `recs`, every fold
challenge `G`, the guest's claims `gclAt`, the closing rounds `tr` and their challenges `T`,
`λ⁻¹`, and each buffer's words (`ownAt j`, of buffer `j`'s size, `osSizesF` order: the head's
thirteen, each level's two, the finish's seven, each non-final level's residual chain); `own`.

`fitTo n xs`: `xs` cut or zero-padded to `n` words. `segAt`: a buffer split by levels at offsets,
`segAt_at` reading a level's word back where the segments are disjoint.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
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

/-- A buffer split by levels: word `e` is level `l`'s word `e - off l` where `l < n` is the first
level whose segment `[off l, off l + span l)` holds `e`, else `0`. -/
def segAt (n : ℕ) (off span : ℕ → ℕ) (val : ℕ → ℕ → E) (e : ℕ) : E :=
  match (List.range n).find? (fun l ↦ decide (off l ≤ e ∧ e < off l + span l)) with
  | some l => val l (e - off l)
  | none => 0

/-- **A level's word of a split buffer**, the segments disjoint. -/
theorem segAt_at {n : ℕ} {off span : ℕ → ℕ} {val : ℕ → ℕ → E}
    (hd : ∀ l l', l < n → l' < n → l < l' → off l + span l ≤ off l')
    {l k : ℕ} (hl : l < n) (hk : k < span l) : segAt n off span val (off l + k) = val l k := by
  unfold segAt
  have hs : ((List.range n).find? (fun l' ↦ decide (off l' ≤ off l + k ∧ off l + k < off l' + span l'))).isSome := by
    rw [List.find?_isSome]
    exact ⟨l, List.mem_range.mpr hl, by simp; omega⟩
  obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp hs
  rw [hl']
  have hm := List.find?_some hl'
  have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hl')
  simp only [decide_eq_true_eq] at hm
  obtain rfl : l' = l := by
    rcases Nat.lt_trichotomy l' l with h | h | h
    · have := hd l' l hmem hl h; omega
    · exact h
    · have := hd l l' hl hmem h; omega
  simp

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
abbrev lv (i : ℕ) : OsLv := osLvAt h.c i

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

/-- `merkle_caps`. -/
def capsC : List E :=
  (List.range (4 * h.c.capLen)).map
    (segAt h.c.levels.length (fun l ↦ 4 * (h.lv l).capOff) (fun l ↦ 2 ^ ((h.lv l).capDepth + 2)) h.cv)

/-- `merkle_cap_active`. -/
def flagsC : List E :=
  (List.range h.c.capLen).map
    (segAt h.c.levels.length (fun l ↦ (h.lv l).capOff) (fun l ↦ 2 ^ (h.lv l).capDepth) h.fv)

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

/-- `level_betas`: `λ³·λ^Q`. -/
def betasC : List E := (List.range h.c.levels.length).map fun i ↦
  if i < h.c.yrLevel then ((h.L i).lam h.logN) ^ 3 * ((h.L i).lam h.logN) ^ (h.lv i).queries else 0

/-- `level_mus`: `λ⁻¹`. -/
def musC : List E := (List.range h.c.levels.length).map fun i ↦
  if i < h.c.yrLevel then h.li i else 0

/-- `level_hs`: each non-final level's high part, normalized. -/
def hsC : List E := (List.range (h.c.levels.length * hsStride)).map fun e ↦
  if e / hsStride < h.c.yrLevel ∧ e % hsStride < (h.lv (e / hsStride)).folds then
    (h.L (e / hsStride)).nw.high.getD (e % hsStride) 0 *
      word (hsScale (h.lv (e / hsStride)).vanish (h.lv (e / hsStride)).highBits (e % hsStride)
        (vanishInv ((h.lv (e / hsStride)).vanish + (h.lv (e / hsStride)).logCols))) 0
  else 0

/-- `ood_z`: row `2(i + 1)` level `i`'s first out-of-domain point, row `2(i + 1) + 1` its second. -/
def oodzC : List E := (List.range (oodSamples * h.c.levels.length * ligColsCap)).map fun e ↦
  let row := e / ligColsCap
  let i := row / 2 - 1
  if 2 ≤ row ∧ i < h.c.yrLevel then
    (if row % 2 = 0 then ((h.L i).osRec h.logN).z0 else ((h.L i).osRec h.logN).z1).getD (e % ligColsCap) 0
  else 0

/-- `ood_scalars`: `λ`, `λ²` at `2(i + 1)`, `2(i + 1) + 1`. -/
def oodC : List E := (List.range (oodSamples * h.c.levels.length)).map fun e ↦
  if 2 ≤ e ∧ e / 2 - 1 < h.c.yrLevel then
    (if e % 2 = 0 then (h.L (e / 2 - 1)).lam h.logN else ((h.L (e / 2 - 1)).lam h.logN) ^ 2)
  else 0

/-- `query_positions`: each level's positions from its offset. -/
def qposC : List E :=
  (List.range h.c.posLen).map
    (segAt h.c.levels.length (fun l ↦ (h.lv l).posOff) (fun l ↦ (h.lv l).squeezes * sqPer (h.lv l))
      fun l k ↦ eOfNat (qwPosOf (h.lv l).depth ((h.L l).word h.logN (k / sqPer (h.lv l)))
        (k % sqPer (h.lv l))))

/-! ## Each level's buffers -/

/-- `sent`: a non-final level's message. -/
def sentC (i : ℕ) : List E := (h.L i).nw.x0 :: (h.L i).nw.x1 :: (h.L i).nw.high

/-- `sqz`: row `j ≥ 1` the capacity before sample `j`. -/
def sqzC (i : ℕ) : List E := (List.range ((h.c.maxSq + 1) * 5)).map fun e ↦
  if 1 ≤ e / 5 ∧ e / 5 ≤ (h.lv i).squeezes then ((h.L i).capSq h.logN (e / 5)).getD (e % 5) 0 else 0

/-- The final level's normalized lane. -/
def hsFC : List E := (List.range (h.c.yrLen + (h.lv h.c.yrLevel).folds)).map fun j ↦
  h.Lf.fw.fold.getD j 0 * word (hsScale (h.lv h.c.yrLevel).vanish (h.c.yrLog + 1) j 1) 0

/-! ## The buffers -/

/-- Buffer `j`'s honest words, before fitting to its size. -/
def ownW (j : ℕ) : List E :=
  let n := h.c.levels.length
  if j < 13 then
    [h.capsC, h.flagsC, h.fmsgC, h.rootsC, h.fchC, h.coefsC, h.betasC, h.musC, h.hsC, h.oodzC,
      h.oodC, h.qposC, []].getD j []
  else if j < 13 + 2 * n then
    let l := (j - 13) / 2
    if (j - 13) % 2 = 0 then (if l = h.c.yrLevel then h.sqzC l else h.sentC l)
    else (if l = h.c.yrLevel then h.hsFC else h.sqzC l)
  else if j < 20 + 2 * n then
    [h.T, finPtC h.c h.G h.T, finPt1C h.c h.G h.T, finBdC h.c h.G h.T h.recs, finLsC h.c h.G h.T h.recs,
      finLaC h.c h.G h.T h.recs, finIchC h.c h.G h.T h.recs h.li h.tr.2.1].getD (j - (13 + 2 * n)) []
  else finRcC h.c h.G h.T h.recs h.li (j - (20 + 2 * n))

/-- **Buffer `j`'s honest words**, of its size. -/
def ownAt (j : ℕ) : List E := fitTo ((osSizesF h.c).getD j 0) (h.ownW j)

/-- **The buffers' honest words.** -/
def own : List (List E) := (List.range (osSizesF h.c).length).map h.ownAt

theorem own_len : List.Forall₂ (fun w s ↦ w.length = s) h.own (osSizesF h.c) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [own], fun i h1 h2 ↦ ?_⟩
  simp [own, ownAt, fitTo_length, List.getElem?_eq_getElem h2]

theorem own_getD {j : ℕ} (hj : j < (osSizesF h.c).length) : h.own.getD j [] = h.ownAt j := by
  simp [own, hj]

end OsHD

end
end LeanVM.Guest.B1.Whir
