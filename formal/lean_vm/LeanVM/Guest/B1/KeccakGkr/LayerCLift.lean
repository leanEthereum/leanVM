/-
  LeanVM.Guest.B1.KeccakGkr.LayerCLift

  `keccak_layer` complete, placed: the caller's words (its claim, the stream, the next claim's
  record with pointers to the layer's buffers) at the frame pointer, the layer's buffers returned.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCLift1
public import LeanVM.Guest.B1.KeccakGkr.PackCompleteIn
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Bits.GrindPlaced

/-!
# `keccak_layer`, placed

* `ClaimLay`: where the caller keeps a claim's record and its buffers (`ClaimLay.L`), and what
  they hold (`ClaimLay.Ok`); `ClaimLay.claimRec`: a memory holding them holds the claim's record.
* `layerBufs D first cur b`: the layer's buffers from `b`: the pack challenges, the round records,
  the local point, the next claim's lanes and flips. `layerLin`: the caller's words, the next
  claim's record at `out` pointing into `layerBufs`, and the grind's window tables
  (`winTabWords`, at `tbE`).
* `layer_kids`: on a memory holding both, the eight-round loop and the remainder loop hold,
  loading from them; `layer_grind`: `grind_check__L3` holds of any word passing the grind.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The address word of `Parameters.addressOfIndex b`. -/
noncomputable abbrev ptr (b : ℕ) : E := ofK (Parameters.addressOfIndex b)

theorem ptr_mul_gen_limb (b j off : ℕ) : (ptr b * gen ^ j).limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex (b + j + off) := by
  have e : ptr b * gen ^ j = ofK (Parameters.addressOfIndex (b + j)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, Parameters.addressOfIndex, Parameters.addressOfIndex,
        Parameters.addressOfIndex, pow_add]
  rw [e, Main.addr_ofK]

/-- A load at `ptr b·g^j + off` inside an entry `(b, ws)` of a layout. -/
theorem inR_entry {L : Main.Layout} {b : ℕ} {ws : List E} (hq : (b, ws) ∈ L) {j off : ℕ}
    (h : j + off < ws.length) : InR (RegionL L) (ptr b * gen ^ j) off :=
  ⟨b + j + off, ptr_mul_gen_limb b j off, ⟨(b, ws), hq, by simp; omega, by simp; omega⟩⟩

theorem memL_entry {rd : Reader} {L : Main.Layout} (h : MemL rd L) {b : ℕ} {ws : List E}
    (hq : (b, ws) ∈ L) : ReadsAt rd (ptr b) ws := h _ hq

/-- The window tables' words (`WinTabs`). -/
def winTabWords : List E := (List.range (2 ^ winTabBits)).map eOfNat

/-- **A memory holding the window tables' words at `tbE` holds the window tables there.** -/
theorem winTabs_of_memL {rd : Reader} {L : Main.Layout} {tbE : ℕ} (h : MemL rd L)
    (hq : (tbE, winTabWords) ∈ L) : WinTabs rd (ptr tbE) := by
  intro n hn
  have := memL_entry h hq n (by simp [winTabWords]; omega)
  simpa [winTabWords] using this

/-! ## The claim's record -/

/-- Where the caller keeps a claim's record and its buffers. -/
structure ClaimLay where
  bclaim : ℕ
  cw : List E
  bpp : ℕ
  blp : ℕ
  lanes : List E
  blc : ℕ
  locC : List E
  bfl : ℕ

namespace ClaimLay

/-- The record, the point, the lanes and, for a later claim, the local point and the flips. -/
def L (CL : ClaimLay) (first : ℕ) (c : KeccakClaim) : Main.Layout :=
  [(CL.bclaim, CL.cw), (CL.bpp, c.point), (CL.blp, CL.lanes)] ++
    if first = 1 then [] else [(CL.blc, CL.locC), (CL.bfl, flipsOf c.weights)]

/-- What the record holds (`KC_*`, G:237-244). -/
def Ok (CL : ClaimLay) (first : ℕ) (c : KeccakClaim) (y : ℕ) : Prop :=
  CL.cw.length = 22 ∧ c.mu.length = 16 ∧ c.point.length = y ∧ CL.cw.getD 0 0 = c.value ∧
    CL.cw.getD 1 0 = sumE c.mu ∧ CL.cw.getD 2 0 = ptr CL.bpp ∧ CL.cw.getD 3 0 = ptr CL.blp ∧
    (∀ i < 16, CL.cw.getD (6 + i) 0 = c.mu.getD i 0) ∧ CL.lanes.length = 25 ∧
    if first = 1 then c.weights = firstWeights CL.lanes
    else CL.cw.getD 4 0 = ptr CL.blc ∧ CL.cw.getD 5 0 = ptr CL.bfl ∧ CL.locC.length = 11 ∧
      c.weights = laterWeights CL.lanes (eqKernel (CL.locC.take 6))

theorem getD_load {rd : Reader} {p : E} {ws : List E} (h : ReadsAt rd p ws) {k : ℕ}
    (hk : k < ws.length) : LoadHolds rd p k (ws.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- **A memory holding the claim's layout holds its record.** -/
theorem claimRec {CL : ClaimLay} {first : ℕ} {c : KeccakClaim} {y : ℕ} (h : CL.Ok first c y)
    {rd : Reader} (hm : MemL rd (CL.L first c)) :
    ClaimRec rd (first = 1) (ptr CL.bclaim) c y := by
  obtain ⟨hl, hmu, hpt, h0, h1, h2, h3, h6, hll, hw⟩ := h
  have hcw := memL_entry hm (b := CL.bclaim) (ws := CL.cw) (by simp [L])
  have hpp := memL_entry hm (b := CL.bpp) (ws := c.point) (by simp [L])
  have hlp := memL_entry hm (b := CL.blp) (ws := CL.lanes) (by simp [L])
  refine ⟨hmu, hpt, by rw [← h0]; exact getD_load hcw (by omega),
    by rw [← h1]; exact getD_load hcw (by omega),
    fun i hi ↦ by
      have hi' : i < 16 := hi
      rw [← h6 i hi']; exact getD_load hcw (by omega),
    ⟨ptr CL.bpp, by rw [← h2]; exact getD_load hcw (by omega), hpp⟩,
    ptr CL.blp, CL.lanes, by rw [← h3]; exact getD_load hcw (by omega), hll, hlp, ?_⟩
  by_cases hf : first = 1
  · simp only [hf, decide_true, ↓reduceIte] at hw ⊢
    exact hw
  · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    obtain ⟨h4, h5, hlc, hwt⟩ := hw
    have hlcR := memL_entry hm (b := CL.blc) (ws := CL.locC) (by simp [L, hf])
    have hslR := memL_entry hm (b := CL.bfl) (ws := flipsOf c.weights) (by simp [L, hf])
    exact ⟨ptr CL.blc, ptr CL.bfl, CL.locC, by rw [← h4]; exact getD_load hcw (by omega), hlc,
      hlcR, by rw [← h5]; exact getD_load hcw (by omega), hslR, hwt⟩

end ClaimLay

/-! ## The layer's layout -/

/-- The sizes of the layer's buffers. -/
def layerSizes (D : LayerData) : List ℕ := [D.y, 128, 11, 25, 7]

/-- The words of the layer's buffers. -/
def layerOwn (D : LayerData) (first : ℕ) (cur : E) : List (List E) :=
  [D.chs first, D.recWords first cur, D.locPt first, lanesOut (D.locPt first) (D.beta first).1,
    flipsOf (laterWeights (lanesOut (D.locPt first) (D.beta first).1)
      (eqKernel ((D.locPt first).take 6)))]

/-- **The layer's buffers from `b`.** -/
def layerBufs (D : LayerData) (first : ℕ) (cur : E) (b : ℕ) : Main.Layout :=
  bufL b (layerSizes D) (layerOwn D first cur)

theorem layerBufs_eq (D : LayerData) (first : ℕ) (cur : E) (b : ℕ) :
    layerBufs D first cur b = [(b, D.chs first), (b + D.y, D.recWords first cur),
      (b + D.y + 128, D.locPt first), (b + D.y + 139, lanesOut (D.locPt first) (D.beta first).1),
      (b + D.y + 164, flipsOf (laterWeights (lanesOut (D.locPt first) (D.beta first).1)
        (eqKernel ((D.locPt first).take 6))))] := by
  simp [layerBufs, bufL, layerSizes, layerOwn, bases]

/-- **The caller's words**: the next claim's record at `out` (its pointers into `layerBufs` from
`b`), the stream at `cur`, the claim's layout, the window tables at `tbE`. -/
noncomputable def layerLin (D : LayerData) (first : ℕ) (CL : ClaimLay) (bcur bout tbE b : ℕ) :
    Main.Layout :=
  [(bout, D.outW first (ptr b) (ptr (b + D.y + 139)) (ptr (b + D.y + 128)) (ptr (b + D.y + 164))),
    (bcur, D.xs)] ++ CL.L first D.c ++ [(tbE, winTabWords)]

theorem recWords_length (D : LayerData) (first : ℕ) (cur : E) :
    (D.recWords first cur).length = 128 := by simp [LayerData.recWords]

/-- **The callees, honestly and loading from the layout**: on a memory holding the caller's words
and the buffers, the eight-round loop and the remainder loop hold. -/
theorem layer_kids {first : ℕ} (hf : first < 2) (D : LayerData) (CL : ClaimLay) (bcur bout tbE b : ℕ)
    (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11) {rd : Reader}
    (hm : MemL rd (layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b)) :
    (1 + gen ^ (D.y / 8) ≠ 0 → coreProgram.RelIn rd
      (RegionL (layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b))
      (packLoopName first) [1, gen ^ (D.y / 8), ptr (b + D.y), ptr CL.bpp, ptr b, ptr tbE] []) ∧
    (1 + gen ^ (D.y % 8) ≠ 0 → coreProgram.RelIn rd
      (RegionL (layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b))
      (remLoopName first) [1, gen ^ (D.y % 8), ptr (b + D.y) * gen ^ (D.y / 8),
        ptr CL.bpp * (gen ^ (D.y / 8)) ^ 8, ptr tbE, ptr b * (gen ^ (D.y / 8)) ^ 8] []) := by
  have hy' : D.y = D.c.point.length := rfl
  set L := layerLin D first CL bcur bout tbE b ++ layerBufs D first (ptr bcur) b with hL
  have mRec : (b + D.y, D.recWords first (ptr bcur)) ∈ L := by
    simp [hL, layerBufs_eq]
  have mPp : (CL.bpp, D.c.point) ∈ L := by simp [hL, layerLin, ClaimLay.L]
  have mXs : (bcur, D.xs) ∈ L := by simp [hL, layerLin]
  have mPt : (b, D.chs first) ∈ L := by simp [hL, layerBufs_eq]
  have hrec := memL_entry hm mRec
  have hpp := memL_entry hm mPp
  have hxs := memL_entry hm mXs
  have hpt := memL_entry hm mPt
  have hrl := recWords_length D first (ptr bcur)
  have hcl := LayerData.chs_length (D := D) (first := first) hpm
  have hxl := LayerData.xs_length hpl hpm hlm
  -- record `j`'s cursor
  have hcur : ∀ j < 16, j ≤ D.y / 8 + D.y % 8 → ∀ c', LoadHolds rd (ptr (b + D.y) * gen ^ j) 80 c' →
      c' = ptr bcur * gen ^ (48 + 2 * D.recK j) := by
    intro j hj hjy c' hc'
    have := (LayerData.recWords_rec hrec hj hjy).2.1
    simp only [krCap] at this
    exact loadHolds_unique hc' this
  have hrecR : ∀ j ≤ 14, ∀ k ∈ roundRecOffs, InR (RegionL L) (ptr (b + D.y) * gen ^ j) k := by
    intro j hj k hk
    refine inR_entry mRec ?_
    simp only [roundRecOffs, List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [hrl]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> omega
  have hpow : ∀ (p : E) (a c : ℕ), p * (gen ^ a) ^ 8 * gen ^ c = p * gen ^ (8 * a + c) := by
    intro p a c
    rw [mul_assoc, ← pow_mul, ← pow_add, show a * 8 = 8 * a by ring]
  refine ⟨fun hne ↦ ?_, fun hne ↦ ?_⟩
  · refine (pack8Loop_relIn hf (m := D.y / 8) (tb := ptr tbE)
      (fun j hj ↦ LayerData.pack8_honest hpl hpm hrec hpp hxs hpt hy30 hj)
      (fun j hj ↦ ⟨hrecR j (by omega), fun q hq ↦ ?_, fun q hq ↦ ?_, fun c' hc' k hk ↦ ?_⟩)).2 hne
    · rw [← pow_mul]; exact inR_entry mPp (by omega)
    · rw [← pow_mul]; exact inR_entry mPt (by omega)
    · rw [hcur j (by omega) (by omega) c' hc']
      refine inR_entry mXs ?_
      have : D.recK j = 8 * j := by unfold LayerData.recK; split <;> omega
      rw [this]
      omega
  · refine (packRemLoop_relIn hf (m := D.y % 8) (tb := ptr tbE)
      (fun i hi ↦ LayerData.packRem_honest hpl hpm hrec hpp hxs hpt hy30 hi)
      (fun i hi ↦ ⟨?_, ?_, ?_, fun c' hc' k hk ↦ ?_⟩)).2 hne
    · rw [mul_assoc, ← pow_add]; exact hrecR _ (by omega)
    · rw [hpow, show 8 * (D.y / 8) + i = 8 * (D.y / 8) + i + 0 from rfl]
      exact inR_entry mPp (by omega)
    · rw [hpow]; exact inR_entry mPt (by omega)
    · rw [mul_assoc, ← pow_add] at hc'
      rw [hcur _ (by omega) (by omega) c' hc']
      refine inR_entry mXs ?_
      have : D.recK (D.y / 8 + i) = 8 * (D.y / 8) + i := by
        unfold LayerData.recK; split <;> omega
      rw [this]
      omega

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`grind_check__L3`, placed, on the window tables at `tbE`**, of any word passing the grind. -/
theorem layer_grind_completeD {κ : ℕ} (hκ : 11 ≤ κ) {L : Main.Layout} {tbE : ℕ}
    (hq : (tbE, winTabWords) ∈ L) {v : E} (hv : (v.limb 0).lane.toNat % 2 ^ 3 = 0) :
    CompleteAtD fs cert κ (grindCheckName 3) L [v, ptr tbE] (Returns []) :=
  grind_check_completeD (bits := 3) (by decide) hκ [v, ptr tbE] [] L
    fun _ _ hm ↦ ⟨rfl, v, ptr tbE, rfl, winTabs_of_memL hm hq, hv⟩

/-- **`grind_check__L3` holds** of any word passing the grind, on a memory holding the window
tables at `tbE`. -/
theorem layer_grind {κ : ℕ} (hκ : 11 ≤ κ) {L : Main.Layout} {tbE : ℕ}
    (hq : (tbE, winTabWords) ∈ L) {rd : Reader} (hlow : LowDef κ rd) (hm : MemL rd L) {v : E}
    (hv : (v.limb 0).lane.toNat % 2 ^ 3 = 0) :
    coreProgram.Rel rd (grindCheckName 3) [v, ptr tbE] [] :=
  (grind_relAtIn (fs := fun _ ↦ 0) (cert := fun _ _ ↦ 0) (bits := 3) (by decide) hκ
    (fun _ _ hm' ↦ ⟨rfl, v, ptr tbE, rfl, winTabs_of_memL hm' hq, hv⟩) 0 hlow hm).relAt.rel

end
end LeanVM.Guest.B1.VerifySub
