/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlaced

  **`keccak_layer` is complete, placed** (`CompleteAtF`), for its two specializations.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCLift
public import LeanVM.Guest.B1.Tables.VtC.Kids
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# `keccak_layer`, complete and placed

`layer_completeAtFB` (`LayerCPlacedBE`): for a layer's honest data `D` (the claim's projection check, the nonce's
grind and the layer's final check holding, `1 ≤ y ≤ 30`), the claim's layout `CL` holding its
record (`ClaimLay.Ok`), the stream at `ptr bcur`, the next claim's record at `ptr bout` and the
window tables at `ptr tbE`, on memories defined below `2^κ`, `11 ≤ κ`, `keccak_layer__L{first}`
is complete at every frame pointer `fp`: the caller's words are `layerLin … (fp + fs name)` (the
next claim's record pointing into the layer's buffers from `fp + fs name`), the function returns
`D.rets` and the buffers `layerBufs … (fp + fs name)` (the pack challenges, the round records,
the local point, the next claim's lanes and flips).

The honest valuation (`layerσ`) with the buffers' bases as its oracle (`layerW`) satisfies the
body (`layer_body_complete`), the inlined `grind_check`'s windows those of the grind's word
`D.gw first` and its table reads in the window tables (`gcInline_ptrs_of_good`); the eight-round and remainder loops are pure callees loading from the
layout (`layer_kids`), placed by `completeAtDTB_of_relIn`; `completeAt_flatOutFBE` places the rest.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- The word `grind_check` reads: the nonce's permutation's output `1`. -/
noncomputable def LayerData.gw (D : LayerData) (first : ℕ) : E :=
  cellsOfState (((D.s0 first).absorbAll D.product dsObserve).nonceState D.nonce) false
    ⟨1, by omega⟩

/-- The oracle: the bases of the layer's buffers from `b`, and the inlined `grind_check`'s windows
of the grind's word. -/
noncomputable def layerW (D : LayerData) (first b : ℕ) (i : ℕ) : E :=
  if i = layOff first + 782 then ptr b else if i = layOff first + 783 then ptr (b + D.y)
  else if i = layOff first + 809 then ptr (b + D.y + 77)
  else if i = tW first + 25 then ptr (b + D.y + 88)
  else if i = topV (tW first) + 3 then ptr (b + D.y + 113)
  else if layOff first + 544 ≤ i ∧ i ≤ layOff first + 544 + gcW 3 then
    gcWin 3 (D.gw first) (i - (layOff first + 544))
  else 0

theorem weightEnd_big {first : ℕ} (hf : first < 2) :
    layOff first ≤ 21 ∧ 1100 < tW first ∧ tW first + 25 < topV (tW first) := by
  interval_cases first <;> exact ⟨by decide, by decide +kernel, by decide +kernel⟩

theorem layerW_vals {first : ℕ} (hf : first < 2) (D : LayerData) (b : ℕ) :
    layerW D first b (layOff first + 782) = ptr b ∧
      layerW D first b (layOff first + 783) = ptr (b + D.y) ∧
      layerW D first b (layOff first + 809) = ptr (b + D.y + 77) ∧
      layerW D first b (tW first + 25) = ptr (b + D.y + 88) ∧
      layerW D first b (topV (tW first) + 3) = ptr (b + D.y + 113) := by
  obtain ⟨hO, hW, hT⟩ := weightEnd_big hf
  refine ⟨by simp [layerW], by simp [layerW], by simp [layerW], ?_, ?_⟩
  · simp only [layerW, show ¬ (tW first + 25 = layOff first + 782) by omega,
      show ¬ (tW first + 25 = layOff first + 783) by omega,
      show ¬ (tW first + 25 = layOff first + 809) by omega, ↓reduceIte]
  · simp only [layerW, show ¬ (topV (tW first) + 3 = layOff first + 782) by omega,
      show ¬ (topV (tW first) + 3 = layOff first + 783) by omega,
      show ¬ (topV (tW first) + 3 = layOff first + 809) by omega,
      show ¬ (topV (tW first) + 3 = tW first + 25) by omega, ↓reduceIte]

theorem layerW_win {first : ℕ} (hf : first < 2) (D : LayerData) (b : ℕ) :
    ∀ j ≤ gcW 3, layerW D first b (layOff first + 544 + j) = gcWin 3 (D.gw first) j := by
  intro j hj
  have hW : gcW 3 = 5 := by decide
  obtain ⟨hO, hT, hV⟩ := weightEnd_big hf
  simp only [layerW, show ¬ (layOff first + 544 + j = layOff first + 782) by omega,
    show ¬ (layOff first + 544 + j = layOff first + 783) by omega,
    show ¬ (layOff first + 544 + j = layOff first + 809) by omega,
    show ¬ (layOff first + 544 + j = tW first + 25) by omega,
    show ¬ (layOff first + 544 + j = topV (tW first) + 3) by omega,
    show layOff first + 544 ≤ layOff first + 544 + j ∧ layOff first + 544 + j ≤ layOff first + 544 + gcW 3
      by omega, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

/-- The layer's callees, placed from `b`: the eight-round loop and the remainder loop. -/
noncomputable def layerKids (D : LayerData) (first : ℕ) (CL : ClaimLay) (bcur bout tbE b : ℕ) :
    List Kid :=
  [⟨packLoopName first, decide (1 + gen ^ (D.y / 8) ≠ 0),
    [1, gen ^ (D.y / 8), ptr (b + D.y), ptr CL.bpp, ptr b, ptr tbE],
    layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b, Returns []⟩,
   ⟨remLoopName first, decide (1 + gen ^ (D.y % 8) ≠ 0),
    [1, gen ^ (D.y % 8), ptr (b + D.y) * gen ^ (D.y / 8), ptr CL.bpp * (gen ^ (D.y / 8)) ^ 8,
      ptr tbE, ptr b * (gen ^ (D.y / 8)) ^ 8],
    layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b, Returns []⟩]

/-- The layer's pure callees, directly or not. -/
def layerKidS : List String := [name% «keccak_layer__L1_loop0», name% «keccak_layer__L1_loop1»,
    name% «keccak_layer__L0_loop0», name% «keccak_layer__L0_loop1»]

theorem layerKidS_pure : coreProgram.PureIn layerKidS :=
  Tables.pureIn_of_pureInB (by decide +kernel)

theorem packLoopName_mem (first : ℕ) : packLoopName first ∈ layerKidS := by
  unfold packLoopName; split <;> simp [layerKidS]

theorem remLoopName_mem (first : ℕ) : remLoopName first ∈ layerKidS := by
  unfold remLoopName; split <;> simp [layerKidS]

theorem alloc_good {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {pre : List Stmt}
    (hg : ∀ s ∈ pre, GoodS rd S w σ s) :
    ∀ x ∈ pre.filterMap Main.Stmt.allocSz, σ x.1 = w x.1.idx := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  have h := hg s hs
  cases s with
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | alloc d n =>
        simp only [Main.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx
        exact h
      | allocDyn d sz =>
        simp only [Main.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx
        exact h
      | _ => simp [Main.Stmt.allocSz] at hsx
    | _ => simp [Main.Stmt.allocSz] at hsx
  | _ => simp [Main.Stmt.allocSz] at hsx

theorem inR_split {A B : Main.Layout} {p : E} {off : ℕ} (h : InR (RegionL (A ++ B)) p off) :
    ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ (RegionL A i ∨
        RegionL B i) := by
  obtain ⟨i, hi, q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact ⟨i, hi, Or.inl ⟨q, hq, h1, h2⟩⟩
  · exact ⟨i, hi, Or.inr ⟨q, hq, h1, h2⟩⟩

theorem layerKids_lin {D : LayerData} {first : ℕ} {CL : ClaimLay} {bcur bout tbE b : ℕ} :
    ∀ k ∈ layerKids D first CL bcur bout tbE b,
      k.Lin = layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b := by
  intro k hk
  simp only [layerKids, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> rfl

theorem layerPre_noLoadIte {first : ℕ} (hf : first < 2) :
    (layerPre first).all noLoadIte = true := by
  interval_cases first <;> decide +kernel

theorem tabs_mem {D : LayerData} {first : ℕ} {CL : ClaimLay} {bcur bout tbE b : ℕ} :
    (tbE, winTabWords) ∈ layerLin D first CL bcur bout tbE b := by
  simp [layerLin]

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxHeartbeats 300000 in
set_option maxRecDepth 20000 in
/-- **The layer's honest valuation, placed from `b`**: the obligation `completeAt_flatOutFBE`
asks of the body, on a memory holding the caller's words and the
buffers. -/
theorem layer_obl {first : ℕ} (hf : first < 2) {κ : ℕ} (hκ : 11 ≤ κ) (D : LayerData)
    (CL : ClaimLay) (bcur bout tbE : ℕ) {p0 p1 iota st : E}
    (hcl : D.cap.length = 5)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hgrind : ((D.s0 first).absorbAll D.product dsObserve).GrindOk sGrindBits D.nonce)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) (b : ℕ) (outs : List (List E × Main.Layout))
    (hout : OutsOk (layerKids D first CL bcur bout tbE b) outs) (rd : Reader) (hlow : LowDef κ rd)
    (hB : MemL rd (layerBufs D first (ptr bcur) b))
    (hLin : MemL rd (layerLin D first CL bcur bout tbE b)) :
    ∃ σ : Val, [V.n (valf% «keccak_layer» "fs0"), .n (valf% «keccak_layer» "fs1"), .n (valf% «keccak_layer» "fs2"), .n (valf% «keccak_layer» "fs3"), .n (valf% «keccak_layer» "fs4"), .n (valf% «keccak_layer» "p0"), .n (valf% «keccak_layer» "p1"), .n (valf% «keccak_layer» "cursor@1"), .n (valf% «keccak_layer» "y_g"), .n (valf% «keccak_layer» "step_g"), .n (valf% «keccak_layer» "rem_g"), .n (valf% «keccak_layer» "claim"), .n (valf% «keccak_layer» "out"),
        .n (valf% «keccak_layer» "iota"), .n (valf% «keccak_layer» "tabs"), .n (valf% «keccak_layer» "stream")].map σ = D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8),
          gen ^ (D.y % 8), ptr CL.bclaim, ptr bout, iota, ptr tbE, st] ∧
      (∀ s ∈ layerPre first, DispOk σ s) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (layerT first) False
        (fun r => r = D.rets first (ptr bcur)) ∧
      ((layerPre first).filterMap Main.Stmt.allocSz).map
        (fun x => x.2.elim id fun s => logG (σ s)) = layerSizes D ∧
      (((layerPre first).filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b (layerSizes D)).map (fun b => ofK (Parameters.addressOfIndex b)) ∧
      CallsMatch σ (((layerPre first).filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (layerKids D first CL bcur bout tbE b) outs ∧
      (∀ q ∈ (layerPre first).filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 *
          Parameters.addressOfIndex q.2 = Parameters.addressOfIndex i ∧
        (RegionL (layerLin D first CL bcur bout tbE b) i ∨
          RegionL (layerBufs D first (ptr bcur) b) i)) ∧
      ∀ e ∈ (layerPre first).flatMap (flEvs σ), e.Exact rd σ := by
  obtain ⟨hflat, -, halloc, -, -, hloads⟩ := layerPre_kernel hf
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hm : MemL rd (layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b) :=
    Main.memL_append.mpr ⟨hLin, hB⟩
  obtain ⟨hK1, hK2⟩ := layer_kids hf D CL bcur bout tbE b hy30 hpl hpm hlm hm
  obtain ⟨w719, w720, w748, w27, wfl⟩ := layerW_vals hf D b
  have hcr0 := hCL
  obtain ⟨hcwL, -, -, -, -, h2, h3, -, -, hwt⟩ := hcr0
  have mem : ∀ q ∈ layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b,
      ReadsAt rd (ptr q.1) q.2 := hm
  have hCLm : MemL rd (CL.L first D.c) := fun q hq ↦ hLin q (by simp [layerLin, hq])
  have hcr := ClaimLay.claimRec hCL hCLm
  have mB : ∀ {bb ws}, (bb, ws) ∈ layerBufs D first (ptr bcur) b → ReadsAt rd (ptr bb) ws :=
    fun {bb ws} hq ↦ mem (bb, ws) (List.mem_append_right _ hq)
  have mL : ∀ {bb ws}, (bb, ws) ∈ layerLin D first CL bcur bout tbE b → ReadsAt rd (ptr bb) ws :=
    fun {bb ws} hq ↦ mem (bb, ws) (List.mem_append_left _ hq)
  have hcw : ReadsAt rd (ptr CL.bclaim) CL.cw := mL (by simp [layerLin, ClaimLay.L])
  have hxs : ReadsAt rd (ptr bcur) D.xs := mL (by simp [layerLin])
  have hout' : ReadsAt rd (ptr bout) (D.outW first (layerW D first b (layOff first + 782))
      (layerW D first b (tW first + 25)) (layerW D first b (layOff first + 809))
      (layerW D first b (topV (tW first) + 3))) := by
    rw [w719, w27, w748, wfl]; exact mL (by simp [layerLin])
  have hbody' := layer_body_complete hf D (rd := rd) (w := layerW D first b) (p0 := p0)
    (p1 := p1) (cur := ptr bcur) (claim := ptr CL.bclaim) (out := ptr bout) (iota := iota)
    (tb := ptr tbE) (st := st) (cw := CL.cw) hcl hw hy1 hy30 hpl hpm hlm hproj hgrind hfin hcr hcw
    (by omega) hxs
    (by rw [w719]; exact mB (by simp [layerBufs_eq]))
    (by rw [w720]; exact mB (by simp [layerBufs_eq]))
    (by rw [w748]; exact mB (by simp [layerBufs_eq]))
    (by rw [w27]; exact mB (by simp [layerBufs_eq]))
    (by rw [wfl]; exact mB (by simp [layerBufs_eq])) hout'
    (gcRc_of_lowDef hκ hlow) (winTabs_of_memL hm (List.mem_append_left _ tabs_mem))
    (layerW_win hf D b)
    (fun hne ↦ by rw [w720, w719, h2]; exact (hK1 hne).rel)
    (fun hne ↦ by rw [w720, w719, h2]; exact (hK2 hne).rel)
  dsimp only at hbody'
  obtain ⟨⟨e739, e532, e745, e1190, e1191, e718⟩, hH⟩ := hbody'
  -- the valuation's equations
  have hl : (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8),
      ptr CL.bclaim, ptr bout, iota, ptr tbE, st]).length = 16 := by simp [hcl]
  have hG := layer_good (rd := rd) (w := layerW D first b) hf hl
  have hGi := hG
  have hpar := fun i (hi : i < 16) ↦ layer_param (rd := rd) (w := layerW D first b) hf hl hi
  generalize layerσ rd (layerW D first b) (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y,
    gen ^ (D.y / 8), gen ^ (D.y % 8), ptr CL.bclaim, ptr bout, iota, ptr tbE, st]) first = σ
    at hG hGi hpar hH e739 e532 e745 e1190 e1191 e718 ⊢
  have hGpre : ∀ s ∈ layerPre first, GoodS rd (layerSt first) (layerW D first b) σ s :=
    fun s hs ↦ hG s (by rw [layerT_pre]; exact List.mem_append_left _ hs)
  have ga := alloc_good hGpre
  rw [halloc] at ga
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ga
  obtain ⟨a719, a720, a748, a27, afl⟩ := ga
  simp only [V.n] at a719 a720 a748 a27 afl
  rw [w719] at a719
  rw [w720] at a720
  rw [w748] at a748
  rw [w27] at a27
  rw [wfl] at afl
  rw [layerT_sections] at hG
  have gP : ∀ s ∈ packSetupT (layOff first) first, GoodS rd (layerSt first) (layerW D first b) σ s :=
    fun s hs ↦ hG s (by simp [hs])
  obtain ⟨f0, f1, f2, f3, f4, hcapE⟩ := five_of_length hcl
  rw [hcapE] at hpar
  have a7 : σ (.n (valf% «keccak_layer» "cursor@1")) = ptr bcur := hpar 7 (by norm_num)
  have a8 : σ (.n (valf% «keccak_layer» "y_g")) = gen ^ D.y := hpar 8 (by norm_num)
  have a9 : σ (.n (valf% «keccak_layer» "step_g")) = gen ^ (D.y / 8) := hpar 9 (by norm_num)
  have a10 : σ (.n (valf% «keccak_layer» "rem_g")) = gen ^ (D.y % 8) := hpar 10 (by norm_num)
  have a11 : σ (.n (valf% «keccak_layer» "claim")) = ptr CL.bclaim := hpar 11 (by norm_num)
  have a12 : σ (.n (valf% «keccak_layer» "out")) = ptr bout := hpar 12 (by norm_num)
  have a14 : σ (.n (valf% «keccak_layer» "tabs")) = ptr tbE := hpar 14 (by norm_num)
  -- the inlined `grind_check`'s table pointers
  obtain ⟨gp0, gpI⟩ := gcInline_ptrs_of_good (rd := rd) (S := layerSt first) (wo := layerW D first b)
    (σ := σ) (o := layOff first + 544) (by decide) (by show layOff first + 532 < _; omega)
    (by show _ < layOff first + 544; simp only; omega) (fun s hs ↦ hGi s (gcInline_mem_layerT hf s hs))
    (layerSt_noGrind hf) (gcRc_of_lowDef hκ hlow)
    (by rw [a14]; exact winTabs_of_memL hm (List.mem_append_left _ tabs_mem))
    (fun j hj ↦ by rw [e532]; exact layerW_win hf D b j hj)
  have GX := gcInline_exact_of_good (rd := rd) (S := layerSt first) (wo := layerW D first b)
    (σ := σ) (o := layOff first + 544) (by decide) (by show layOff first + 532 < _; omega)
    (by show _ < layOff first + 544; simp only; omega) (fun s hs ↦ hGi s (gcInline_mem_layerT hf s hs))
    (layerSt_noGrind hf) (gcRc_of_lowDef hκ hlow)
    (by rw [a14]; exact winTabs_of_memL hm (List.mem_append_left _ tabs_mem))
    (fun j hj ↦ by rw [e532]; exact layerW_win hf D b j hj)
  rw [a14] at gp0 gpI
  refine ⟨σ, ?_, layerPre_disp hf σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  pick_goal 2
  · -- the body, `layerT first` kept folded
    generalize layerT first = T at hH ⊢
    exact hH
  · -- the parameters
    rw [hcapE]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
    simp only [List.length_cons, List.length_nil] at h1
    have := hpar i (by omega)
    interval_cases i <;> simpa using this
  · -- the sizes
    rw [halloc]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, layerSizes, a8,
      gen_pow_eq_ofK]
    rw [logG_spec (by omega)]
  · -- the bases
    rw [halloc]
    simp only [List.map_cons, List.map_nil, a719, a720, a748, a27, afl, layerSizes, bases]
  · -- the calls
    rw [layerPre_callSF hf σ]
    obtain ⟨e725', e726, e727, e731, e735, e737', e738⟩ := packSetup_vals (layOff_ok hf) gP
    rw [a9] at e725' e731 e735
    rw [a10] at e737'
    have epp : σ (.n (layOff first + 781)) = ptr CL.bpp := by rw [e718, h2]
    simp only [layerCalls, layerKids, List.map_cons, List.map_nil] at hout ⊢
    match outs, hout with
    | [o1, o2], ⟨ho1, ho2, _⟩ =>
      refine ⟨rfl, by simp [Main.mkCall, e725'],
        fun ht ↦ ⟨?_, ?_⟩, rfl, by simp [Main.mkCall, e737'], fun ht ↦ ⟨?_, ?_⟩, trivial⟩
      · simp [Main.mkCall, e726, a9, a720, epp, a719, a14]
      · simp only [Main.mkCall, List.map_nil]; exact ((ho1 ht).1).symm
      · simp [Main.mkCall, e738, a10, e727, e731, e735, a9, a720, epp, a719, a14]
      · simp only [Main.mkCall, List.map_nil]; exact ((ho2 ht).1).symm
  · -- the loads
    have fin : ∀ {bb : ℕ} {ws : List E} {j off : ℕ},
        (bb, ws) ∈ layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b →
        j + off < ws.length → ∃ i, (ptr bb * gen ^ j).limb 0 * Parameters.addressOfIndex off =
          Parameters.addressOfIndex i ∧ (RegionL (layerLin D first CL bcur bout tbE b) i ∨
            RegionL (layerBufs D first (ptr bcur) b) i) :=
      fun hq h ↦ inR_split (inR_entry hq h)
    have fin0 : ∀ {bb : ℕ} {ws : List E} {off : ℕ},
        (bb, ws) ∈ layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b →
        off < ws.length → ∃ i, (ptr bb).limb 0 * Parameters.addressOfIndex off =
          Parameters.addressOfIndex i ∧ (RegionL (layerLin D first CL bcur bout tbE b) i ∨
            RegionL (layerBufs D first (ptr bcur) b) i) := fun {bb ws off} hq h ↦ by
      have := fin (bb := bb) (ws := ws) (j := 0) (off := off) hq (by omega)
      simpa using this
    have hxl := LayerData.xs_length hpl hpm hlm
    have hcl' := LayerData.chs_length (D := D) (first := first) hpm
    intro q hq
    have hg := List.all_eq_true.mp hloads q hq
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hg
    rcases hg with hg | ⟨hgp, hg0⟩
    pick_goal 2
    · -- the inlined `grind_check`'s table reads
      obtain ⟨p, off⟩ := q
      simp only at hgp hg0 ⊢
      subst hg0
      have hwl : winTabWords.length = 2 ^ 11 := by simp [winTabWords, winTabBits]
      simp only [grindPtrs, List.mem_cons, List.mem_map, List.mem_range] at hgp
      rcases hgp with rfl | ⟨i, hi, rfl⟩
      · obtain ⟨e, he, hpe⟩ := gp0
        rw [hpe]
        exact fin (bb := tbE) (ws := winTabWords) (j := e) (off := 0)
          (List.mem_append_left _ tabs_mem) (by omega)
      · obtain ⟨e, he, hpe⟩ := gpI i hi
        rw [hpe]
        exact fin (bb := tbE) (ws := winTabWords) (j := e) (off := 0)
          (List.mem_append_left _ tabs_mem) (by omega)
    obtain ⟨g, hgm, hg1, hg2⟩ := hg
    obtain ⟨p, off⟩ := q
    simp only at hg1 hg2 ⊢
    subst hg1
    simp only [layerGroups, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hgm
    rcases hgm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hgm
    · rw [a7]; exact fin0 (bb := bcur) (ws := D.xs) (by simp [layerLin]) (by simp only at hg2; omega)
    · rw [a11]; exact fin0 (bb := CL.bclaim) (ws := CL.cw) (by simp [layerLin, ClaimLay.L])
        (by simp only at hg2; omega)
    · rw [a12]; exact fin0 (bb := bout) (ws := D.outW first (ptr b) (ptr (b + D.y + 88))
        (ptr (b + D.y + 77)) (ptr (b + D.y + 113))) (by simp [layerLin])
        (by simp [LayerData.outW, LayerData.next, layerClaim, keccakInstanceWeights_length]; omega)
    · rw [a720]; exact fin0 (bb := b + D.y) (ws := D.recWords first (ptr bcur))
        (by simp [layerBufs_eq]) (by rw [recWords_length]; omega)
    · rw [e739, w720, mul_assoc, ← pow_add]
      exact fin (bb := b + D.y) (ws := D.recWords first (ptr bcur))
        (by simp [layerBufs_eq]) (by rw [recWords_length]; simp only at hg2; omega)
    · rw [e745]; exact fin (bb := bcur) (ws := D.xs) (by simp [layerLin]) (by simp only at hg2; omega)
    · rw [e1190, h3]; exact fin0 (bb := CL.blp) (ws := CL.lanes) (by simp [layerLin, ClaimLay.L])
        (by have := hCL.2.2.2.2.2.2.2.2.1; simp only at hg2; omega)
    · rw [a748]; exact fin0 (bb := b + D.y + 77) (ws := D.locPt first) (by simp [layerBufs_eq])
        (by simp only at hg2; omega)
    · rw [a27]; exact fin0 (bb := b + D.y + 88) (ws := lanesOut (D.locPt first) (D.beta first).1)
        (by simp [layerBufs_eq]) (by rw [lanesOut_length]; simp only at hg2; omega)
    · rw [afl]; exact fin0 (bb := b + D.y + 113) (ws := flipsOf (laterWeights
        (lanesOut (D.locPt first) (D.beta first).1) (eqKernel ((D.locPt first).take 6))))
        (by simp [layerBufs_eq]) (by simp [flipsOf]; simp only at hg2; omega)
    · split at hgm
      · simp at hgm
      · rename_i hf1
        simp only [List.mem_singleton] at hgm
        subst hgm
        have hf0 : first = 0 := by omega
        simp only [hf1, ↓reduceIte] at hwt
        obtain ⟨h4, -, hlcl, -⟩ := hwt
        rw [e1191 hf0, h4]
        exact fin0 (bb := CL.blc) (ws := CL.locC) (by simp [layerLin, ClaimLay.L, hf1])
          (by simp only at hg2; omega)
  · -- the path is exact: the inlined `grind_check`'s windows by `gcInline_exact_of_good`
    obtain ⟨fn, hfind, hbody, -⟩ := layer_fn hf
    have hw : walk σ (layerT first) = .ret ((layerPre first).flatMap (flEvs σ)) (layerVs first) := by
      rw [layerT_pre]; exact walk_flat σ _ _ hflat (layerPre_disp hf σ)
    have hsat := walk_sat (P := coreProgram) fn.body
      (coreProgram_wf fn (List.mem_of_find?_eq_some hfind)) (by rw [hbody]; exact hH)
    rw [hbody, hw] at hsat
    have hes : ∀ e ∈ (layerPre first).flatMap (flEvs σ), e.Holds rd σ := fun e he ↦ (hsat.1 e he).1
    refine exact_of_sites (layer_pinnedSites hf) hw hes fun a ha _ ↦ ?_
    obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp ha
    cases s
    case atom a' =>
      dsimp only at hsa
      split at hsa
      · obtain rfl := Option.some.inj hsa
        exact GX a' hs
      · exact absurd hsa (by simp)
    all_goals exact absurd hsa (by simp)

end
end LeanVM.Guest.B1.VerifySub
