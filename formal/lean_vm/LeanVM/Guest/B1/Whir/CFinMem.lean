/-
  LeanVM.Guest.B1.Whir.CFinMem

  What the body after the tail reads, its pointers named.
-/

module

public import LeanVM.Guest.B1.Whir.CFinOod

/-!
# The finish's memory, its pointers named

`BasisMemP`, `ResMemP`, `OodAllP`: `BasisMem`, `ResMem`, `OodAll` with the pointers they read given
as words (the fixed buffers' `OsPtrs`, the tail's buffer `T`, the basis, scale and inner buffers),
so that they can be stated before the valuation holding those pointers; `basisMem_of_P`,
`resMem_of_P`, `oodAll_of_P`: at a valuation holding them, the original forms.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The pointer a basis coordinate reads: the fold challenges, then the tail's. -/
def coordPtr (P : OsPtrs) (T : E) (lv : OsLv) (t : ℕ) : E := if t < lv.prefixLen then P.fch else T

theorem coordSrc_ptr (σ : Val) (tch : ℕ) (lv : OsLv) (t : ℕ) :
    σ (.n (coordSrc tch lv t).1) = coordPtr (ptrsOf σ) (σ (.n tch)) lv t := by
  unfold coordSrc coordPtr; split_ifs <;> rfl

/-- `BasisMem` with its pointers named. -/
def BasisMemP (rd : Reader) (P : OsPtrs) (T BD LS : E) (c : OsCfg) (L : ℕ) (lv : OsLv) (β : E)
    (X : ℕ → E) : Prop :=
  LoadHolds rd P.betas L β ∧
    (∀ t < lv.prefixLen + c.yrLog, X t ≠ 0 ∧ invW lv t ≠ 0 ∧
      LoadHolds rd (coordPtr P T lv t) (coordSrc 0 lv t).2 (X t) ∧
      LoadHolds rd BD (L * ligColsCap + t) ((1 + X t) / (X t * invW lv t))) ∧
    LoadHolds rd LS L (β * ∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), (X t * invW lv t))

theorem basisMem_of_P {σ : Val} {c : OsCfg} {tch bd ls L : ℕ} {lv : OsLv} {β : E} {X : ℕ → E}
    (h : BasisMemP rd (ptrsOf σ) (σ (.n tch)) (σ (.n bd)) (σ (.n ls)) c L lv β X) :
    BasisMem rd σ c tch bd ls L lv β X := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun t ht ↦ ?_, h3⟩
  obtain ⟨g1, g2, g3, g4⟩ := h2 t ht
  refine ⟨g1, g2, ?_, g4⟩
  rw [coordSrc_ptr σ tch lv t]
  have : (coordSrc tch lv t).2 = (coordSrc 0 lv t).2 := by unfold coordSrc; split_ifs <;> rfl
  rw [this]; exact g3

/-- `ResMem` with its pointers named. -/
structure ResMemP (C : CallRel) (rd : Reader) (P : OsPtrs) (BD ICH LS : E) (c : OsCfg) (lvl : ℕ)
    (lv : OsLv) (RC acc M I L : E) (Pq D : ℕ → E) : Prop where
  hml : 1 ≤ lv.logCols
  hn : lv.queries / resBatch < u128Bound
  hM : LoadHolds rd P.mus lvl M
  hL : IsInK (1 + gen ^ (lv.queries / resBatch)) ∧ (1 + gen ^ (lv.queries / resBatch) ≠ 0 →
    C (c.resLoop lvl) [1, gen ^ (lv.queries / resBatch), P.qpos, BD, RC, M] [])
  h0 : LoadHolds rd RC 0 0
  hacc : LoadHolds rd RC (lv.queries / resBatch) acc
  hP : ∀ i < lv.queries % resBatch,
    LoadHolds rd P.qpos (lv.posOff + (lv.queries - lv.queries % resBatch) + i) (Pq i)
  hD : ∀ s < lv.logCols, LoadHolds rd BD (lvl * ligColsCap + s) (D s)
  hI : LoadHolds rd ICH lvl I
  hLs : LoadHolds rd LS lvl L
  hout : LoadHolds rd ICH (lvl + 1)
    (I + L * resFold D lv.vanish lv.logCols M acc ((List.range (lv.queries % resBatch)).map Pq))

theorem resMem_of_P {σ : Val} {c : OsCfg} {ich bd ls lvl : ℕ} {lv : OsLv} {RC acc M I L : E}
    {Pq D : ℕ → E}
    (h : ResMemP C rd (ptrsOf σ) (σ (.n bd)) (σ (.n ich)) (σ (.n ls)) c lvl lv RC acc M I L Pq D) :
    ResMem C rd σ c ich bd ls lvl lv RC acc M I L Pq D :=
  ⟨h.hml, h.hn, h.hM, h.hL, h.h0, h.hacc, h.hP, h.hD, h.hI, h.hLs, h.hout⟩

/-- The pointer an out-of-domain coordinate reads. -/
def oodPtr (P : OsPtrs) (T : E) (zf t : ℕ) : E := if t < zf then P.fch else T

/-- `OodAll` with its pointers named. -/
def OodAllP (rd : Reader) (P : OsPtrs) (T : E) (c : OsCfg) (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) :
    ℕ → ℕ → List OsLv → Prop
  | _, _, [] => True
  | prevCols, ol, lv :: rest =>
    (LoadHolds rd P.ood (ol * oodSlots) (Λ ol) ∧
      ∀ t < prevCols - c.yrLog + c.yrLog,
        LoadHolds rd P.oodz (ol * ligColsCap + t) (Z ol t) ∧
        LoadHolds rd (oodPtr P T (prevCols - c.yrLog) t) (oodSrc 0 (prevCols - c.yrLog) lv t).2
          (Y ol t)) ∧
      OodAllP rd P T c Λ Z Y lv.logCols (ol + 1) rest

theorem oodAll_of_P {σ : Val} {c : OsCfg} {tch : ℕ} {Λ : ℕ → E} {Z Y : ℕ → ℕ → E} :
    ∀ (levels : List OsLv) (prevCols ol : ℕ),
      OodAllP rd (ptrsOf σ) (σ (.n tch)) c Λ Z Y prevCols ol levels →
      OodAll rd σ c tch Λ Z Y prevCols ol levels
  | [], _, _, _ => trivial
  | lv :: rest, prevCols, ol, ⟨⟨h1, h2⟩, hr⟩ => by
    refine ⟨⟨h1, fun t ht ↦ ?_⟩, oodAll_of_P rest _ _ hr⟩
    obtain ⟨g1, g2⟩ := h2 t ht
    refine ⟨g1, ?_⟩
    have e1 : σ (.n (oodSrc tch (prevCols - c.yrLog) lv t).1) = oodPtr (ptrsOf σ) (σ (.n tch))
        (prevCols - c.yrLog) t := by unfold oodSrc oodPtr; split_ifs <;> rfl
    have e2 : (oodSrc tch (prevCols - c.yrLog) lv t).2 = (oodSrc 0 (prevCols - c.yrLog) lv t).2 := by
      unfold oodSrc; split_ifs <;> rfl
    rw [e1, e2]; exact g2

end
end LeanVM.Guest.B1.Whir
