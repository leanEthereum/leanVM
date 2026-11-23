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
`tail_zero`, the finish by `fin_of`), its calls' values `OsHD.cvBody`.
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
  slow : ∀ l < h.c.yrLevel, h.lamAt l = (h.recs.getD l default).lam ∧
    finZ h.c h.G h.T h.recs l = osZA h.c h.own l ∧
    finSlow h.c h.G h.T h.recs l = osSlowRetA h.c h.own l (h.lamAt l) (osZA h.c h.own l)
  a0 : [args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0, args.getD 5 0] = h.capAt 0
  a6 : args.getD 6 0 = h.claimAt 0
  x0 : (h.xsAt 0).length = xs.length
  r0 : (args.getD 7 0, args.getD 8 0) = digestHalves (h.root 0)
  rate : ∀ l < h.c.levels.length, LvRate (Val.ofArgs args) h.c l (h.c.levels.getD l default)
  sel : ∃ ri < ligNRates, args.getD 0 0 = gen ^ ri ∧ h.c.posTotal.getD ri 0 = osPosTotal h.c

namespace OsHD

variable (h : OsHD)

/-- **The helpers' data**: the first word and capacity of the positions, `λ`, `1/(λ + is_zero(λ))`, the
batch and `μ`. -/
noncomputable def D (l : ℕ) : OsLvData := ⟨h.word l 0, h.capL l, h.lamAt l, h.li l, h.bat l, h.li l⟩

theorem D_eq (l : ℕ) : (h.D l).w0 = h.word l 0 ∧ (h.D l).capL = h.capL l ∧
    (l ≠ h.c.yrLevel → (h.D l).lam = h.lamAt l ∧ (h.D l).lamInv = h.li l) ∧ (h.D l).batched = h.bat l := by
  simp only [OsHD.D, implies_true, and_self]

/-- **`pos_totals`' words** in memory. -/
theorem posTot_load (hHS : HonStatic h.c) {rd : Reader} {b : ℕ} (hm : OsMemA rd h.c b h.own) {r : ℕ}
    (hr : r < ligNRates) : LoadHolds rd (osPtrA h.c b 9) r (gw (h.c.posTotal.getD r 0)) := by
  have h9 := hHS.head (j := 9) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h9
  have a := h.load hm (hHS.headLt (j := 9) (by omega)) (by unfold osIxQbpA; omega) (e := r) (by rw [h9]; exact hr)
  rwa [ownW_posTot, posTotC, getD_mapRange _ hr] at a

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

/-- **The body's calls' values** at the honest data: the levels' (`cvLv`), the closing rounds'
(`tailCV`) and the finish's (`finCV`), at the arguments' rate selector. -/
noncomputable def cvBody (b : ℕ) (tabs cur : E) (xs args : List E) : List (List E) :=
  (List.range h.c.levels.length).flatMap (fun i ↦ h.cvLv b tabs cur xs i (Val.ofArgs args (.n osRate))) ++
    tailCV tabs h.Lf.fw.pairs (h.capAt h.c.levels.length) (h.claimAt h.c.levels.length)
      (cur * gen ^ (xs.length - (h.xsAt h.c.levels.length).length)) ++
    finCV h.c h.G h.T h.recs h.li (osPtrA h.c b 0) (osPtrA h.c b (13 + h.c.yrLevel)) (Val.ofArgs args (.n osRate))
      (osPtrA h.c b 10) (osPtrA h.c b 6) (osPtrA h.c b 2) (multilinearEval (h.Lf.fw.fold.take h.c.yrLen) h.T)
      (osPtrA h.c b (16 + h.c.yrLevel))

end OsHD

/-- **The body at the honest data**, from its facts. -/
theorem body_gen {h : OsHD} {args xs : List E} {lane : ℕ} {w : WhirEnd} {cur tabs : E}
    (F : BodyFacts h args xs lane w) (ha9 : args.getD 9 0 = cur) (ha10 : args.getD 10 0 = tabs) (b : ℕ)
    (rd0 : Reader) (hl0 : LowDef 11 rd0) :
    ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader), OsHA C rd h.c b h.own cur tabs xs →
      LowAgree rd rd0 →
      BlkF C rd (Val.ofArgs args) 11 kEnd f (osBodyA h.c)
        (fun σ' ↦ OsOutA h.c b tabs (h.tr.2.1 + h.T.prod * recsDeficit h.recs h.G)
          ((h.recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((h.G ++ h.T).drop g.foldStart)) 0)
          (multilinearEval (h.Lf.fw.fold.take h.c.yrLen) h.T) h.own h.D σ' ∧
          cvOf (osBodyA h.c) σ' = h.cvBody b tabs cur xs args ∧
          LoadsIn (OsM h.c b h.own cur tabs xs) (osBodyA h.c) σ' ∧ WinEx (osBodyA h.c) σ') := by
  have hy := F.lv.yrE
  obtain ⟨ri, hri, hsel, hpt⟩ := F.sel
  obtain ⟨kEnd, f, hf⟩ := body_of (H := fun C rd ↦ OsHA C rd h.c b h.own cur tabs xs ∧ LowAgree rd rd0)
    (h := h) (b := b) (args := args) (cur := cur) (tabs := tabs) (xs := xs) (own := h.own) (D := h.D)
    (CVL := h.cvLv b tabs cur xs) (CVF := fun x ↦ finCV h.c h.G h.T h.recs h.li (osPtrA h.c b 0)
      (osPtrA h.c b (13 + h.c.yrLevel)) x (osPtrA h.c b 10) (osPtrA h.c b 6) (osPtrA h.c b 2)
      (multilinearEval (h.Lf.fw.fold.take h.c.yrLen) h.T) (osPtrA h.c b (16 + h.c.yrLevel))) F.lv.bs
    hsel hri hpt F.a0 F.a6 ha9 ha10 F.x0 F.rate
    (fun C rd hH ↦ by
      replace hH := osHA_of_hm (fun _ _ h ↦ h.1) hH
      obtain ⟨r0, r1⟩ := h.mid_roots F.lv.hs hH.2.2.1 (l := 0) (by omega)
      have e1 : args.getD 7 0 = (digestHalves (h.root 0)).1 := congrArg Prod.fst F.r0
      have e2 : args.getD 8 0 = (digestHalves (h.root 0)).2 := congrArg Prod.snd F.r0
      rw [e1, e2]
      exact ⟨r0, r1, fun r hr ↦ h.posTot_load F.lv.hs hH.2.2.1 hr⟩)
    (fun st σ hq ↦ F.lv.levels rd0 hl0 st σ hq) (fun l _ ↦ h.D_eq l)
    (fun l hl ↦ h.rootA F.lv.hs hl) F.pl (fun C rd hH ↦ tailC_from F.lv.hs F.lv.nm F.tsuf F.pl F.f3 C rd (osHA_of_hm (fun _ _ h ↦ h.1) hH))
    (fun C rd hH ↦ tail_zero F.lv.hs (osHA_of_hm (fun _ _ h ↦ h.1) hH).2.2.1 F.pl)
    (fun σ hsf hok hrt hrv hp hqp ht htc hcl ↦ (fin_of F.lv.hs F.lv.nm F.finS F.lv.len F.rrun F.ylen F.fold
      F.ffm (b := b) (cur := cur) (tabs := tabs) (xs := xs) (D := h.D) (fun l hl ↦ ⟨rfl, F.res l hl⟩) F.slow σ hsf hok hrt
      hrv hp hqp ht htc hcl).weaken fun C rd hH ↦ hH.1)
  exact ⟨kEnd, f, fun C rd hH hag ↦ (hf C rd ⟨hH, hag⟩).mono fun σ' ⟨l, o, cv⟩ ↦ ⟨o, cv, l⟩⟩

end
end LeanVM.Guest.B1.Whir
