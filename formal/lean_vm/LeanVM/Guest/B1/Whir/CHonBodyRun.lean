/-
  LeanVM.Guest.B1.Whir.CHonBodyRun

  open_stacked's body at the honest data, from the run's facts at every level.
-/

module

public import LeanVM.Guest.B1.Whir.CHonComp
public import LeanVM.Guest.B1.Whir.CHonLvs
public import LeanVM.Guest.B1.Whir.CHonLvF
public import LeanVM.Guest.B1.Whir.CHonFin
public import LeanVM.Guest.B1.Whir.CHonLvCF

/-!
# The body from the run's facts

`BodyFacts h args xs lane w`: what the body's completeness takes of the honest data `h` (generic,
so no concrete configuration meets the elaborator): the configuration's decided facts, each
level's step and checked facts, its words a suffix of the stream, its carried capacity, the next
root, the fold challenges, the rounds' counts, the cap's height, cells, flags and agreement, the
positions, the final lane, the closing rounds, the finish's facts, the call's arguments.

`body_gen`: from them, at every base, values on which the body before its return holds on every
`OsH` and gives `OsOutF` (`body_of`, each level's step by `lvMid_gen` with `midC_of` or
`lvFin_gen` with `finC_of`, the closing rounds by `tailC_from`, `tail_zero`, the finish by
`fin_of`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **What the body's completeness takes of the honest data.** -/
structure BodyFacts (h : OsHD) (args xs : List E) (lane : ℕ) (w : WhirEnd) : Prop where
  bs : BodyStatic h.c
  hs : HonStatic h.c
  nm : HonNames h.c
  res : ∀ l < h.c.yrLevel, osKindOf (h.c.resLoop l) = none
  len : h.Ls.length = h.c.levels.length
  step : ∀ l < h.c.yrLevel, LvAt.NextStep h.logN l (h.L l) (h.L (l + 1))
  mid : ∀ l < h.c.yrLevel, MidOk h.c h.logN l (osLvAt h.c l) (h.L l).level (h.L (l + 1)).level
    (osLvAt h.c (l + 1))
  last : LvAt.FinStep h.logN lane h.c.yrLevel h.Lf w
  fin : FinOkF h.c h.logN h.c.yrLevel (osLvAt h.c h.c.yrLevel) h.Lf.level
  gam : ∀ l < h.c.levels.length, (h.L l).s.alphas.length = (osLvAt h.c l).foldsOff
  recF : ∀ l < h.c.levels.length, ∀ q ∈ lvsRecs h.logN h.Ls l, q.F ≤ (h.L l).s.alphas.length
  suf : ∀ l < h.c.levels.length, ∃ p, xs = p ++ (h.L l).xs
  cap5 : ∀ l < h.c.levels.length, (h.L l).cap.length = 5
  rootN : ∀ l < h.c.yrLevel, digestHalves (h.root (l + 1)) = ((h.L l).nw.x0, (h.L l).nw.x1)
  G : ∀ l < h.c.levels.length, ∀ j < (osLvAt h.c l).folds, h.G.getD ((osLvAt h.c l).foldsOff + j) 0 =
    (roundsSpec (osLvAt h.c l).folds (h.L l).s (h.L l).cap (h.L l).rw).1.alphas.getD
      ((h.L l).s.alphas.length + j) 0
  rl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (osLvAt h.c i).folds
  ht : ∀ l < h.c.levels.length, ((h.L l).R.getD l default).2.1 = (osLvAt h.c l).depth
  cv : ∀ l < h.c.levels.length, h.cv l = capCellH (osLvAt h.c l).depth ((h.L l).qs h.logN) (h.L l).phase
  fv : ∀ l < h.c.levels.length,
    h.fv l = capFlH (osLvAt h.c l).depth (osLvAt h.c l).capDepth ((h.L l).qs h.logN) (h.L l).phase
  ag : ∀ l < h.c.levels.length,
    Guest.Limits.OpeningsAgree (osLvAt h.c l).depth (((h.L l).qs h.logN).zip (h.L l).phase)
  ps : ∀ l < h.c.levels.length, ∀ q ∈ (h.L l).qs h.logN, q < 2 ^ (osLvAt h.c l).depth
  q0 : ∀ l < h.c.levels.length, 0 < ((h.L l).qs h.logN).length
  lane : h.Lf.fw.fold.length = h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds
  tsuf : tailWords h.Lf.fw.pairs <:+ xs
  pl : h.Lf.fw.pairs.length = h.c.yrLog
  f3 : (h.Lf.F3 h.logN).cap.length = 5
  finS : FinStatic h.c h.G h.T h.recs
  rrun : ∀ i < h.c.yrLevel, RecRun h i
  ylen : 2 ^ h.c.yrLog = h.c.yrLen
  fold : h.c.yrLen ≤ h.Lf.fw.fold.length
  ffm : osKindOf ("fold_final_msg__L" ++ natStr h.c.yrLog) = some (.ffm h.c.yrLog)
  a0 : [args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0] = h.capAt 0
  a5 : args.getD 5 0 = h.claimAt 0
  x0 : (h.xsAt 0).length = xs.length
  r0 : (args.getD 6 0, args.getD 7 0) = digestHalves (h.root 0)

namespace BodyFacts

variable {h : OsHD} {args xs : List E} {lane : ℕ} {w : WhirEnd} (F : BodyFacts h args xs lane w)
include F

theorem yrE : h.c.yrLevel + 1 = h.c.levels.length := F.hs.yr

/-- **A level's step**, from its calls and memory by `midC_of` and `finC_of`. -/
theorem lv {b : ℕ} {cur tabs : E} :
    ∀ l < h.c.levels.length, ∀ st σ, QAt h b tabs cur xs l st σ →
      BlkA (fun C rd ↦ OsH C rd h.c b h.own cur tabs xs) σ st.k (osLevel h.c l (osLvAt h.c l) st).2.k
        (osLevel h.c l (osLvAt h.c l) st).1 (fun σ' ↦
        st.k ≤ (osLevel h.c l (osLvAt h.c l) st).2.k ∧
        QAt h b tabs cur xs (l + 1) (osLevel h.c l (osLvAt h.c l) st).2 σ' ∧ RAt h b tabs l σ' ∧
        RQ h b l (h.bat l) σ') := by
  intro l hl st σ hq
  have hy := F.yrE
  have hsfx : (h.L l).xs <:+ xs := by obtain ⟨p, hp⟩ := F.suf l hl; exact ⟨p, hp.symm⟩
  by_cases hfin : l = h.c.yrLevel
  · subst hfin
    obtain ⟨-, hfold, hlog, -, hdepth, hqueries, -, -, -, hsq, -, -, hsq1, -⟩ := F.fin
    have hdep : (osLvAt h.c h.c.yrLevel).depth = h.Lf.dp h.logN := by
      rw [hdepth]
      show _ = h.logN - h.Lf.s1.alphas.length + _
      rw [LvAt.s1, roundsSpec_alphas_length, F.gam _ hl, hfold, hlog]
    exact lvFin_gen F.bs F.last F.fin (F.gam _ hl) (F.suf _ hl) hq fun C rd hH ↦
      finC_of F.hs F.nm hq.ptr hq.tabs (h.bat h.c.yrLevel) F.last hfold hdep hqueries hsq (F.cap5 _ hl)
        hsfx F.lane (F.G _ hl) F.len F.rl (F.ht _ hl) (F.cv _ hl) (F.fv _ hl) (F.ag _ hl) (F.ps _ hl)
        (F.q0 _ hl) hsq1 C rd hH
  · have hl' : l < h.c.yrLevel := by omega
    obtain ⟨-, hfold, hcols, hcols1, hdepth, hqueries, -, -, -, hsq, -, -, -, hsq1, -⟩ := F.mid l hl'
    have hmu : (h.L l).mu h.logN = (osLvAt h.c l).logCols := by
      show h.logN - (h.L l).s1.alphas.length = _
      rw [LvAt.s1, roundsSpec_alphas_length, F.gam l hl, hfold]; exact hcols
    have hdep : (osLvAt h.c l).depth = (h.L l).dp h.logN := by
      rw [hdepth]; show _ = (h.L l).mu h.logN + _; rw [hmu]
    exact lvMid_gen F.bs hl' hy (by rw [F.len]; omega) (F.step l hl') (F.mid l hl') (F.gam l hl)
      (F.recF l hl) (F.suf l hl) hq fun C rd hH ↦
      midC_of F.hs F.nm hl' hq.ptr hq.tabs (h.bat l) (F.step l hl') hfold hmu hdep hqueries hsq hcols1
        (F.cap5 l hl) hsfx (F.rootN l hl') (F.G l hl) F.len F.rl (F.rrun l hl').z0
        (F.ht l hl) (F.cv l hl) (F.fv l hl) (F.ag l hl) (F.ps l hl) (F.q0 l hl) hsq1 C rd hH

end BodyFacts

/-- **The body at the honest data**, from its facts. -/
theorem body_gen {h : OsHD} {args xs : List E} {lane : ℕ} {w : WhirEnd} {cur tabs : E}
    (F : BodyFacts h args xs lane w) (ha8 : args.getD 8 0 = cur) (ha9 : args.getD 9 0 = tabs) (b : ℕ) :
    ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader), OsH C rd h.c b h.own cur tabs xs →
      BlkF C rd (Val.ofArgs args) 10 kEnd f (osBodyA h.c)
        (OsOutF h.c b tabs (h.tr.2.1 + h.T.prod * recsDeficit h.recs h.G)
          ((h.recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((h.G ++ h.T).drop g.foldStart)) 0)
          (multilinearEval (h.Lf.fw.fold.take h.c.yrLen) h.T) h.word h.lamInv h.bat h.li) := by
  have hy := F.yrE
  obtain ⟨kEnd, f, hf⟩ := body_of (H := fun C rd ↦ OsH C rd h.c b h.own cur tabs xs) (h := h) (b := b)
    (args := args) (cur := cur) (tabs := tabs) (xs := xs) (batched := h.bat) F.bs F.a0 F.a5 ha8 ha9 F.x0
    (fun C rd hH ↦ by
      obtain ⟨r0, r1⟩ := h.mid_roots F.hs hH.2.2.1 (l := 0) (by omega)
      have e1 : args.getD 6 0 = (digestHalves (h.root 0)).1 := congrArg Prod.fst F.r0
      have e2 : args.getD 7 0 = (digestHalves (h.root 0)).2 := congrArg Prod.snd F.r0
      rw [e1, e2]
      exact ⟨r0, r1⟩)
    F.lv F.pl (tailC_from F.hs F.nm F.tsuf F.pl F.f3) (fun C rd hH ↦ tail_zero F.hs hH.2.2.1 F.pl)
    (fun σ hsf ↦ fin_of F.hs F.finS F.len F.rrun F.ylen F.fold F.ffm F.res hsf σ)
  exact ⟨kEnd, f, hf⟩

end
end LeanVM.Guest.B1.Whir
