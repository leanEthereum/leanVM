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
structure ResMemP (C : CallRel) (rd : Reader) (P : OsPtrs) (R BD ICH LS : E) (c : OsCfg) (lvl : ℕ)
    (lv : OsLv) (M h I L : E) : Prop where
  hpo : lv.posOff < u128Bound
  hlc : lvl * ligColsCap < u128Bound
  hM : LoadHolds rd P.mus lvl M
  hD : DispC C rd R ((c.lvAt lvl).map osResidualName)
    [P.qpos * gen ^ lv.posOff, BD * gen ^ (lvl * ligColsCap), M] [h]
  hI : LoadHolds rd ICH lvl I
  hLs : LoadHolds rd LS lvl L
  hout : LoadHolds rd ICH (lvl + 1) (I + L * h)

theorem resMem_of_P {σ : Val} {R : E} {c : OsCfg} {ich bd ls lvl : ℕ} {lv : OsLv} {M h I L : E}
    (hh : ResMemP C rd (ptrsOf σ) R (σ (.n bd)) (σ (.n ich)) (σ (.n ls)) c lvl lv M h I L) :
    ResMem C rd σ R c ich bd ls lvl lv M h I L :=
  ⟨hh.hpo, hh.hlc, hh.hM, hh.hD, hh.hI, hh.hLs, hh.hout⟩

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

/-! ## The finish's statements -/

/-- `osFinish` before its `ret`. -/
def osFinA (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt :=
  let n := c.levels.length
  let yat := st.k
  let pt := yat + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bd := pts.2 + 1
  let ls := pts.2 + 3
  let bs := osBases c tch bd ls 0 c.levels (pts.2 + 4)
  let ich := bs.2 + 1
  let rs := osResiduals c ich bd ls 0 c.levels st.mats (bs.2 + 3)
  let od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2
  let k := od.2.2
  [.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n yat],
    .atom (.hint (.alloc (.n pt) pointCap)), .atom (.hint (.alloc (.n (pt + 1)) pointCap))] ++
    pts.1 ++ osHeap (n * ligColsCap) pts.2 ++ osHeap n (pts.2 + 2) ++ bs.1 ++
    osHeap (n + 1) bs.2 ++
    [.atom (.const (.n (bs.2 + 2)) (word 0 0 0)), .atom (.load (.n (bs.2 + 2)) (.n ich) 0)] ++
    rs.1 ++ od.1 ++
    [.atom (.copy (.n k) (.n st.t)), .atom (.copy (.n (k + 1)) (.n pt)),
      .atom (.copy (.n (k + 2)) (.n (pt + 1))), .atom (.load (.n (k + 3)) (.n ich) n),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (od.2.1.getD 0))), .atom (.copy (.n (k + 5)) (.n yat))]

/-- `osFinish`'s returns. -/
def osFinRet (c : OsCfg) (st : OsSt) (tch : ℕ) : List V :=
  let pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)
  let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels (pts.2 + 4)
  let rs := osResiduals c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels st.mats (bs.2 + 3)
  let k := (osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2).2.2
  [.n k, .n (k + 1), .n (k + 2), .n (k + 4), .n (k + 5)]

theorem osFinish_splitC (c : OsCfg) (st : OsSt) (tch : ℕ) :
    osFinish c st tch = osFinA c st tch ++ [.ret (osFinRet c st tch)] := by
  simp only [osFinish, osFinA, osFinRet, List.append_assoc, List.cons_append, List.nil_append]

end
end LeanVM.Guest.B1.Whir
