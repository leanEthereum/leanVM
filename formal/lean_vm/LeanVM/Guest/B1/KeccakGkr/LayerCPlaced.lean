/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlaced

  **`keccak_layer` is complete, placed** (`CompleteAtF`), for its two specializations.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCLift
public import LeanVM.Guest.B1.Tables.VtC.Kids

/-!
# `keccak_layer`, complete and placed

`layer_completeAtF`: for a layer's honest data `D` (the claim's projection check and the layer's
final check holding, `1 ≤ y ≤ 30`), the claim's layout `CL` holding its record (`ClaimLay.Ok`),
the stream at `ptr bcur` and the next claim's record at `ptr bout`, `keccak_layer__L{first}`
is complete at every frame pointer `fp`: the caller's words are `layerLin … (fp + fs name)` (the
next claim's record pointing into the layer's buffers from `fp + fs name`), the function returns
`D.rets` and the buffers `layerBufs … (fp + fs name)` (the pack challenges, the round records,
the local point, the next claim's lanes and flips).

The honest valuation (`layerσ`) with the buffers' bases as its oracle (`layerW`) satisfies the
body (`layer_body_complete`); the eight-round and remainder loops are pure callees loading from
the layout (`layer_kids`), placed by `completeAtD_of_relIn`; `completeAt_flatOutF` places the rest.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- The oracle: the bases of the layer's buffers from `b`. -/
noncomputable def layerW (D : LayerData) (first b : ℕ) (i : ℕ) : E :=
  if i = 1052 then ptr b else if i = 1053 then ptr (b + D.y)
  else if i = 1081 then ptr (b + D.y + 128)
  else if i = weightEnd first + 33 then ptr (b + D.y + 139)
  else if i = topV (weightEnd first) + 3 then ptr (b + D.y + 164) else 0

theorem weightEnd_big {first : ℕ} (hf : first < 2) :
    1100 < weightEnd first ∧ weightEnd first + 33 < topV (weightEnd first) := by
  interval_cases first <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem layerW_vals {first : ℕ} (hf : first < 2) (D : LayerData) (b : ℕ) :
    layerW D first b 1052 = ptr b ∧ layerW D first b 1053 = ptr (b + D.y) ∧
      layerW D first b 1081 = ptr (b + D.y + 128) ∧
      layerW D first b (weightEnd first + 33) = ptr (b + D.y + 139) ∧
      layerW D first b (topV (weightEnd first) + 3) = ptr (b + D.y + 164) := by
  obtain ⟨hW, hT⟩ := weightEnd_big hf
  refine ⟨by simp [layerW], by simp [layerW], by simp [layerW], ?_, ?_⟩
  · simp only [layerW, show ¬ (weightEnd first + 33 = 1052) by omega,
      show ¬ (weightEnd first + 33 = 1053) by omega,
      show ¬ (weightEnd first + 33 = 1081) by omega, ↓reduceIte]
  · simp only [layerW, show ¬ (topV (weightEnd first) + 3 = 1052) by omega,
      show ¬ (topV (weightEnd first) + 3 = 1053) by omega,
      show ¬ (topV (weightEnd first) + 3 = 1081) by omega,
      show ¬ (topV (weightEnd first) + 3 = weightEnd first + 33) by omega, ↓reduceIte]

/-- The layer's callees, placed from `b`: the eight-round loop and the remainder loop. -/
noncomputable def layerKids (D : LayerData) (first : ℕ) (CL : ClaimLay) (bcur bout b : ℕ) :
    List Kid :=
  [⟨packLoopName first, decide (1 + gen ^ (D.y / 8) ≠ 0),
    [1, gen ^ (D.y / 8), ptr (b + D.y), ptr CL.bpp, ptr b],
    layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b, Returns []⟩,
   ⟨remLoopName first, decide (1 + gen ^ (D.y % 8) ≠ 0),
    [1, gen ^ (D.y % 8), ptr (b + D.y) * gen ^ (D.y / 8), ptr CL.bpp * (gen ^ (D.y / 8)) ^ 8,
      ptr b * (gen ^ (D.y / 8)) ^ 8],
    layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b, Returns []⟩]

/-- The layer's callees, directly or not. -/
def layerKidS : List String := ["__loop37", "__loop38", "__loop39", "__loop40"]

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

theorem layerKids_lin {D : LayerData} {first : ℕ} {CL : ClaimLay} {bcur bout b : ℕ} :
    ∀ k ∈ layerKids D first CL bcur bout b,
      k.Lin = layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b := by
  intro k hk
  simp only [layerKids, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> rfl

theorem layerPre_noLoadIte {first : ℕ} (hf : first < 2) :
    (layerPre first).all noLoadIte = true := by
  interval_cases first <;> decide +kernel

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxHeartbeats 300000 in
set_option maxRecDepth 20000 in
/-- **The layer's honest valuation, placed from `b`**: the obligation `completeAt_flatOutF`
(and `completeAt_flatOutFB`) asks of the body, on a memory holding the caller's words and the
buffers. -/
theorem layer_obl {first : ℕ} (hf : first < 2) (D : LayerData)
    (CL : ClaimLay) (bcur bout : ℕ) {p0 p1 iota : E}
    (hcl : D.cap.length = 5) (hcap : AllCanonical D.cap)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) (b : ℕ) (outs : List (List E × Main.Layout))
    (hout : OutsOk (layerKids D first CL bcur bout b) outs) (rd : Reader)
    (hB : MemL rd (layerBufs D first (ptr bcur) b))
    (hLin : MemL rd (layerLin D first CL bcur bout b)) :
    ∃ σ : Val, [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12,
        .n 13].map σ = D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8),
          ptr CL.bclaim, ptr bout, iota] ∧ (∀ s ∈ layerPre first, DispOk σ s) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (layerT first) False
        (fun r => r = D.rets first (ptr bcur)) ∧
      ((layerPre first).filterMap Main.Stmt.allocSz).map
        (fun x => x.2.elim id fun s => logG (σ s)) = layerSizes D ∧
      (((layerPre first).filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b (layerSizes D)).map (fun b => ofK (Parameters.addressOfIndex b)) ∧
      CallsMatch σ (((layerPre first).filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (layerKids D first CL bcur bout b) outs ∧
      ∀ q ∈ (layerPre first).filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 *
          Parameters.addressOfIndex q.2 = Parameters.addressOfIndex i ∧
        (RegionL (layerLin D first CL bcur bout b) i ∨
          RegionL (layerBufs D first (ptr bcur) b) i) := by
  obtain ⟨-, -, halloc, -, -, hloads⟩ := layerPre_kernel hf
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hm : MemL rd (layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b) :=
    Main.memL_append.mpr ⟨hLin, hB⟩
  obtain ⟨hK1, hK2⟩ := layer_kids hf D CL bcur bout b hy30 hpl hpm hlm hm
  obtain ⟨w1052, w1053, w1081, w33, wfl⟩ := layerW_vals hf D b
  have hcr0 := hCL
  obtain ⟨hcwL, -, -, -, -, h2, h3, -, -, hwt⟩ := hcr0
  have mem : ∀ q ∈ layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b,
      ReadsAt rd (ptr q.1) q.2 := hm
  have hCLm : MemL rd (CL.L first D.c) := fun q hq ↦ hLin q (by simp [layerLin, hq])
  have hcr := ClaimLay.claimRec hCL hCLm
  have mB : ∀ {bb ws}, (bb, ws) ∈ layerBufs D first (ptr bcur) b → ReadsAt rd (ptr bb) ws :=
    fun {bb ws} hq ↦ mem (bb, ws) (List.mem_append_right _ hq)
  have mL : ∀ {bb ws}, (bb, ws) ∈ layerLin D first CL bcur bout b → ReadsAt rd (ptr bb) ws :=
    fun {bb ws} hq ↦ mem (bb, ws) (List.mem_append_left _ hq)
  have hcw : ReadsAt rd (ptr CL.bclaim) CL.cw := mL (by simp [layerLin, ClaimLay.L])
  have hxs : ReadsAt rd (ptr bcur) D.xs := mL (by simp [layerLin])
  have hout' : ReadsAt rd (ptr bout) (D.outW first (layerW D first b 1052)
      (layerW D first b (weightEnd first + 33)) (layerW D first b 1081)
      (layerW D first b (topV (weightEnd first) + 3))) := by
    rw [w1052, w33, w1081, wfl]; exact mL (by simp [layerLin])
  have hbody' := layer_body_complete hf D (rd := rd) (w := layerW D first b) (p0 := p0)
    (p1 := p1) (cur := ptr bcur) (claim := ptr CL.bclaim) (out := ptr bout) (iota := iota)
    (cw := CL.cw) hcl hcap hw hy1 hy30 hpl hpm hlm hproj hfin hcr hcw (by omega) hxs
    (by rw [w1052]; exact mB (by simp [layerBufs_eq]))
    (by rw [w1053]; exact mB (by simp [layerBufs_eq]))
    (by rw [w1081]; exact mB (by simp [layerBufs_eq]))
    (by rw [w33]; exact mB (by simp [layerBufs_eq]))
    (by rw [wfl]; exact mB (by simp [layerBufs_eq])) hout'
    (fun hne ↦ by rw [w1053, w1052, h2]; exact (hK1 hne).rel)
    (fun hne ↦ by rw [w1053, w1052, h2]; exact (hK2 hne).rel)
  dsimp only at hbody'
  obtain ⟨⟨e1072, e1078, e1841, e1842, e1051⟩, hH⟩ := hbody'
  -- the valuation's equations
  have hl : (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8),
      ptr CL.bclaim, ptr bout, iota]).length = 14 := by simp [hcl]
  have hG := layer_good (rd := rd) (w := layerW D first b) hf hl
  have hpar := fun i (hi : i < 14) ↦ layer_param (rd := rd) (w := layerW D first b) hf hl hi
  generalize layerσ rd (layerW D first b) (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y,
    gen ^ (D.y / 8), gen ^ (D.y % 8), ptr CL.bclaim, ptr bout, iota]) first = σ
    at hG hpar hH e1072 e1078 e1841 e1842 e1051 ⊢
  have hGpre : ∀ s ∈ layerPre first, GoodS rd (layerSt first) (layerW D first b) σ s :=
    fun s hs ↦ hG s (by rw [layerT_pre]; exact List.mem_append_left _ hs)
  have ga := alloc_good hGpre
  rw [halloc] at ga
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ga
  obtain ⟨a1052, a1053, a1081, a33, afl⟩ := ga
  simp only [V.n] at a1052 a1053 a1081 a33 afl
  rw [w1052] at a1052
  rw [w1053] at a1053
  rw [w1081] at a1081
  rw [w33] at a33
  rw [wfl] at afl
  rw [layerT_sections] at hG
  have gP : ∀ s ∈ packSetupT first, GoodS rd (layerSt first) (layerW D first b) σ s :=
    fun s hs ↦ hG s (by simp [hs])
  obtain ⟨f0, f1, f2, f3, f4, hcapE⟩ := five_of_length' hcl
  rw [hcapE] at hpar
  have a7 : σ (.n 7) = ptr bcur := hpar 7 (by norm_num)
  have a8 : σ (.n 8) = gen ^ D.y := hpar 8 (by norm_num)
  have a9 : σ (.n 9) = gen ^ (D.y / 8) := hpar 9 (by norm_num)
  have a10 : σ (.n 10) = gen ^ (D.y % 8) := hpar 10 (by norm_num)
  have a11 : σ (.n 11) = ptr CL.bclaim := hpar 11 (by norm_num)
  have a12 : σ (.n 12) = ptr bout := hpar 12 (by norm_num)
  refine ⟨σ, ?_, layerPre_disp hf σ, ?_, ?_, ?_, ?_, ?_⟩
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
    simp only [List.map_cons, List.map_nil, a1052, a1053, a1081, a33, afl, layerSizes, bases]
  · -- the calls
    rw [layerPre_callSF hf σ]
    obtain ⟨e1058', e1059, e1060, e1064, e1068, e1070', e1071⟩ := packSetup_vals gP
    rw [a9] at e1058' e1064 e1068
    rw [a10] at e1070'
    have epp : σ (.n 1051) = ptr CL.bpp := by rw [e1051, h2]
    simp only [layerCalls, layerKids, List.map_cons, List.map_nil] at hout ⊢
    match outs, hout with
    | [o1, o2], ⟨ho1, ho2, _⟩ =>
      refine ⟨rfl, by simp [Main.mkCall, e1058'], fun ht ↦ ⟨?_, ?_⟩, rfl,
        by simp [Main.mkCall, e1070'], fun ht ↦ ⟨?_, ?_⟩, trivial⟩
      · simp [Main.mkCall, e1059, a9, a1053, epp, a1052]
      · simp only [Main.mkCall, List.map_nil]; exact ((ho1 ht).1).symm
      · simp [Main.mkCall, e1071, a10, e1060, e1064, e1068, a9, a1053, epp, a1052]
      · simp only [Main.mkCall, List.map_nil]; exact ((ho2 ht).1).symm
  · -- the loads
    have fin : ∀ {bb : ℕ} {ws : List E} {j off : ℕ},
        (bb, ws) ∈ layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b →
        j + off < ws.length → ∃ i, (ptr bb * gen ^ j).limb 0 * Parameters.addressOfIndex off =
          Parameters.addressOfIndex i ∧ (RegionL (layerLin D first CL bcur bout b) i ∨
            RegionL (layerBufs D first (ptr bcur) b) i) :=
      fun hq h ↦ inR_split (inR_entry hq h)
    have fin0 : ∀ {bb : ℕ} {ws : List E} {off : ℕ},
        (bb, ws) ∈ layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b →
        off < ws.length → ∃ i, (ptr bb).limb 0 * Parameters.addressOfIndex off =
          Parameters.addressOfIndex i ∧ (RegionL (layerLin D first CL bcur bout b) i ∨
            RegionL (layerBufs D first (ptr bcur) b) i) := fun {bb ws off} hq h ↦ by
      have := fin (bb := bb) (ws := ws) (j := 0) (off := off) hq (by omega)
      simpa using this
    have hxl := LayerData.xs_length hpl hpm hlm
    have hcl' := LayerData.chs_length (D := D) (first := first) hpm
    intro q hq
    have hg := List.all_eq_true.mp hloads q hq
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
    obtain ⟨g, hgm, hg1, hg2⟩ := hg
    obtain ⟨p, off⟩ := q
    simp only at hg1 hg2 ⊢
    subst hg1
    simp only [layerGroups, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hgm
    rcases hgm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hgm
    · rw [a7]; exact fin0 (bb := bcur) (ws := D.xs) (by simp [layerLin]) (by simp only at hg2; omega)
    · rw [a11]; exact fin0 (bb := CL.bclaim) (ws := CL.cw) (by simp [layerLin, ClaimLay.L])
        (by simp only at hg2; omega)
    · rw [a12]; exact fin0 (bb := bout) (ws := D.outW first (ptr b) (ptr (b + D.y + 139))
        (ptr (b + D.y + 128)) (ptr (b + D.y + 164))) (by simp [layerLin])
        (by simp [LayerData.outW, LayerData.next, layerClaim, keccakInstanceWeights_length]; omega)
    · rw [a1053]; exact fin0 (bb := b + D.y) (ws := D.recWords first (ptr bcur))
        (by simp [layerBufs_eq]) (by rw [recWords_length]; omega)
    · rw [e1072, w1053, mul_assoc, ← pow_add]
      exact fin (bb := b + D.y) (ws := D.recWords first (ptr bcur))
        (by simp [layerBufs_eq]) (by rw [recWords_length]; simp only at hg2; omega)
    · rw [e1078]; exact fin (bb := bcur) (ws := D.xs) (by simp [layerLin]) (by simp only at hg2; omega)
    · rw [e1841, h3]; exact fin0 (bb := CL.blp) (ws := CL.lanes) (by simp [layerLin, ClaimLay.L])
        (by have := hCL.2.2.2.2.2.2.2.2.1; simp only at hg2; omega)
    · rw [a1081]; exact fin0 (bb := b + D.y + 128) (ws := D.locPt first) (by simp [layerBufs_eq])
        (by simp only at hg2; omega)
    · rw [a33]; exact fin0 (bb := b + D.y + 139) (ws := lanesOut (D.locPt first) (D.beta first).1)
        (by simp [layerBufs_eq]) (by rw [lanesOut_length]; simp only at hg2; omega)
    · rw [afl]; exact fin0 (bb := b + D.y + 164) (ws := flipsOf (laterWeights
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
        rw [e1842 hf0, h4]
        exact fin0 (bb := CL.blc) (ws := CL.locC) (by simp [layerLin, ClaimLay.L, hf1])
          (by simp only at hg2; omega)


set_option maxRecDepth 20000 in
/-- **`keccak_layer` is complete, placed**, for its two specializations. -/
theorem layer_completeAtF {first : ℕ} (hf : first < 2) (κ : ℕ) (D : LayerData)
    (CL : ClaimLay) (bcur bout : ℕ) {p0 p1 iota : E}
    (hcl : D.cap.length = 5) (hcap : AllCanonical D.cap)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) :
    CompleteAtF fs cert κ (layerName first)
      (fun fp ↦ layerLin D first CL bcur bout (fp + fs (layerName first)))
      (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8), ptr CL.bclaim,
        ptr bout, iota])
      (fun fp rets Lout ↦ rets = D.rets first (ptr bcur) ∧
        Lout = layerBufs D first (ptr bcur) (fp + fs (layerName first))) := by
  obtain ⟨fn, hfind, hbody, hparams⟩ := layer_fn hf
  obtain ⟨hflat, haddrs, halloc, -, -, hloads⟩ := layerPre_kernel hf
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  refine completeAt_flatOutF (fs := fs) (cert := cert) hfind (layer_loop hf) κ _ _
    (fun _ ↦ D.rets first (ptr bcur)) _ (hbody.trans (layerT_pre first)) hflat haddrs
    (layerPre_noLoadIte hf)
    (layerSizes D) (fun _ ↦ layerOwn D first (ptr bcur)) (fun _ ↦ ?_) (fun _ ↦ ⟨rfl, rfl⟩)
    (fun fp ↦ layerKids D first CL bcur bout (fp + fs (layerName first))) ?_ ?_ ?_ ?_
  · -- the buffers' words fit
    simp only [layerOwn, layerSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    refine ⟨by rw [LayerData.chs_length hpm], by rw [recWords_length], by rw [hlocL],
      by rw [lanesOut_length], by simp [flipsOf]⟩
  · -- the callees, placed
    intro fp k hk ht
    simp only [layerKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · have hne : 1 + gen ^ (D.y / 8) ≠ 0 := by simpa using ht
      exact completeAtD_of_relIn layerKidS_pure (packLoopName_mem first)
        fun rd _ hm ↦ (layer_kids hf D CL bcur bout _ hy30 hpl hpm hlm hm).1 hne
    · have hne : 1 + gen ^ (D.y % 8) ≠ 0 := by simpa using ht
      exact completeAtD_of_relIn layerKidS_pure (remLoopName_mem first)
        fun rd _ hm ↦ (layer_kids hf D CL bcur bout _ hy30 hpl hpm hlm hm).2 hne
  · intro fp k hk _ i hi
    rw [layerKids_lin k hk] at hi
    obtain ⟨q, hq, h1, h2⟩ := hi
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr ⟨q, hq, h1, h2⟩
  · intro fp rd hB hLin k hk
    rw [layerKids_lin k hk]
    exact Main.memL_append.mpr ⟨hLin, hB⟩
  · -- the honest valuation
    intro fp outs hout rd _ hB hLin
    rw [hparams, hbody]
    exact layer_obl hf D CL bcur bout hcl hcap hw hy1 hy30 hpl hpm hlm hproj hfin hCL _ outs hout rd
      hB hLin
end
end LeanVM.Guest.B1.VerifySub
