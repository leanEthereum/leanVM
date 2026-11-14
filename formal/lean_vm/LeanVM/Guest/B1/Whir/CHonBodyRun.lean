/-
  LeanVM.Guest.B1.Whir.CHonBodyRun

  open_stacked's body at the honest data, from the honest data's facts.
-/

module

public import LeanVM.Guest.B1.Whir.CHonComp
public import LeanVM.Guest.B1.Whir.CHonLvsAll
public import LeanVM.Guest.B1.Whir.CHonFin
public import LeanVM.Guest.B1.Whir.CHonRes

/-!
# The body at the honest data

`BodyFacts h args xs lane w`: what the body's completeness takes of the honest data `h`: the
levels' facts (`LvFacts`), the closing rounds' and the finish's, the residual chains equal to
`level_residual`'s over the buffers (`OsHD.finRes_eq`), the arguments' values and the rate's
selector. `OsHD.D`: the helpers' data. `body_gen`: the body before its return holds under `OsHA`
and gives `OsOutA` (`body_of`, the levels by `LvFacts.levels`, the closing rounds by `tailC_from`,
`tail_zero`, the finish by `fin_of`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **What the body's completeness takes of the honest data.** -/
structure BodyFacts (h : OsHD) (args xs : List E) (lane : ℕ) (w : WhirEnd) : Prop where
  lv : LvFacts h xs lane w
  tsuf : tailWords h.Lf.fw.pairs <:+ xs
  pl : h.Lf.fw.pairs.length = h.c.yrLog
  f3 : (h.Lf.F3 h.logN).cap.length = 5
  finS : FinStatic h.c h.G h.T h.recs
  rrun : ∀ i < h.c.yrLevel, RecRun h i
  ylen : 2 ^ h.c.yrLog = h.c.yrLen
  fold : h.c.yrLen ≤ h.Lf.fw.fold.length
  ffm : osKindOf ("fold_final_msg__L" ++ natStr h.c.yrLog) = some (.ffm h.c.yrLog)
  res : ∀ l < h.c.yrLevel, finRes h.c h.G h.T h.recs h.li l = osLrRetA h.c h.own l (h.li l)
  a0 : [args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0, args.getD 5 0] = h.capAt 0
  a6 : args.getD 6 0 = h.claimAt 0
  x0 : (h.xsAt 0).length = xs.length
  r0 : (args.getD 7 0, args.getD 8 0) = digestHalves (h.root 0)
  rate : ∀ l < h.c.levels.length, LvRate (Val.ofArgs args) h.c l (h.c.levels.getD l default)

namespace OsHD

variable (h : OsHD)

/-- **The helpers' data**: the first word and capacity of the positions, `λ`, `1/λ`, the batch and
`μ`. -/
noncomputable def D (l : ℕ) : OsLvData := ⟨h.word l 0, h.capL l, h.lamAt l, h.li l, h.bat l, h.li l⟩

theorem D_eq (l : ℕ) : (h.D l).w0 = h.word l 0 ∧ (h.D l).capL = h.capL l ∧
    (l ≠ h.c.yrLevel → (h.D l).lam = h.lamAt l ∧ (h.D l).lamInv = h.li l) ∧ (h.D l).batched = h.bat l := by
  simp only [OsHD.D, implies_true, and_self]

/-- **A level's root** in `level_roots`. -/
theorem rootA (hHS : HonStatic h.c) {l : ℕ} (hl : l < h.c.levels.length) :
    osRootA h.own l = digestHalves (h.root l) := by
  have h1 := hHS.head (j := 1) (by omega)
  have hlt0 : 2 * l < (osSizesL h.c).getD 1 0 := by rw [h1]; show 2 * l < 2 * h.c.levels.length; omega
  have hlt1 : 2 * l + 1 < (osSizesL h.c).getD 1 0 := by rw [h1]; show _ < 2 * h.c.levels.length; omega
  unfold osRootA
  rw [h.own_word (hHS.headLt (j := 1) (by omega)) hlt0, h.own_word (hHS.headLt (j := 1) (by omega)) hlt1,
    ownW_roots, rootsC, getD_mapRange _ (by omega), getD_mapRange _ (by omega)]
  simp only [show 2 * l % 2 = 0 by omega, show (2 * l + 1) % 2 = 1 by omega, show 2 * l / 2 = l by omega,
    show (2 * l + 1) / 2 = l by omega, ↓reduceIte, one_ne_zero]

end OsHD

/-- **The body at the honest data**, from its facts. -/
theorem body_gen {h : OsHD} {args xs : List E} {lane : ℕ} {w : WhirEnd} {cur tabs : E}
    (F : BodyFacts h args xs lane w) (ha9 : args.getD 9 0 = cur) (ha10 : args.getD 10 0 = tabs) (b : ℕ) :
    ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader), OsHA C rd h.c b h.own cur tabs xs →
      BlkF C rd (Val.ofArgs args) 11 kEnd f (osBodyA h.c)
        (OsOutA h.c b tabs (h.tr.2.1 + h.T.prod * recsDeficit h.recs h.G)
          ((h.recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((h.G ++ h.T).drop g.foldStart)) 0)
          (multilinearEval (h.Lf.fw.fold.take h.c.yrLen) h.T) h.own h.D) := by
  have hy := F.lv.yrE
  obtain ⟨kEnd, f, hf⟩ := body_of (H := fun C rd ↦ OsHA C rd h.c b h.own cur tabs xs) (h := h) (b := b)
    (args := args) (cur := cur) (tabs := tabs) (xs := xs) (own := h.own) (D := h.D) F.lv.bs F.a0 F.a6 ha9 ha10
    F.x0 F.rate
    (fun C rd hH ↦ by
      obtain ⟨r0, r1⟩ := h.mid_roots F.lv.hs hH.2.2.1 (l := 0) (by omega)
      have e1 : args.getD 7 0 = (digestHalves (h.root 0)).1 := congrArg Prod.fst F.r0
      have e2 : args.getD 8 0 = (digestHalves (h.root 0)).2 := congrArg Prod.snd F.r0
      rw [e1, e2]
      exact ⟨r0, r1⟩)
    (fun st σ hq ↦ F.lv.levels st σ hq) (fun l _ ↦ h.D_eq l)
    (fun l hl ↦ h.rootA F.lv.hs hl) F.pl (tailC_from F.lv.hs F.lv.nm F.tsuf F.pl F.f3)
    (fun C rd hH ↦ tail_zero F.lv.hs hH.2.2.1 F.pl)
    (fin_of F.lv.hs F.lv.nm F.finS F.lv.len F.rrun F.ylen F.fold F.ffm fun l hl ↦ ⟨rfl, F.res l hl⟩)
  exact ⟨kEnd, f, hf⟩

end
end LeanVM.Guest.B1.Whir
