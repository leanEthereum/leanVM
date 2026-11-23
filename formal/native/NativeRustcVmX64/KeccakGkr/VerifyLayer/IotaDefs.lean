module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Segs

/-!
# `verify_layer` on x86-64: ι's tools

The state kept from the segment kernel to the first check (`K0`: the body, the `TState`, the
product, the spills but the pack's, the segment kernel, R12 and R13 the projection), kept by a
block writing the frame below `24` only (`K0.blk`) and by a leaf call
(`K0.leaf`). A round constant's bit tested by raw `bt` (`rcBit`) and its next bit as a
mask (`rcMask`), by `decide` over the 24 constants; the bit weights loaded (`wLoad`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The spills kept through ι: `spills2` but the pack's word (at `24`, overwritten). -/
def spills3 (m0 : MachineData) (c : KeccakClaimW) : List (Nat × UInt64) :=
  [(32, c.mu.size.toUInt64), (40, .ofBitVec (tA m0)),
    (48, .ofBitVec (cA m0 + 24#64)), (56, .ofBitVec (reg m0 .rdx)),
    (64, .ofBitVec (cA m0 + 288#64)), (80, .ofBitVec (sA m0)), (96, .ofBitVec (cA m0)),
    (224, .ofBitVec (cA m0 + 16#64))]

/-- The spills of ι's loops: `spills3`, the bit weights' and the point's addresses. -/
def spillsI (m0 : MachineData) (c : KeccakClaimW) : List (Nat × UInt64) :=
  spills3 m0 c ++ [(120, .ofBitVec (sA m0 + 25600#64)), (128, .ofBitVec (cA m0 + 280#64))]

/-- **What ι keeps**, the spills `L`. -/
structure K0 [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (L : List (Nat × UInt64)) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s1
  prod : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 472) p.toList
  sp : FWs m0 d.dmem L
  seg : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 232) (segK m0 c).toList
  acc : ewArg (reg d .r12) (reg d .r13) = projectedOf c.mu p
  psize : p.size = 47
  ssize : 2 ≤ (segK m0 c).size

/-- The round constant `r`. -/
abbrev rcW (r : Nat) : UInt64 := keccakRCW.getD r 0

/-- All ones, or zero. -/
def maskOf (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0#64

end

public section

theorem spills3_in (c : KeccakClaimW) {m0 : MachineData} :
    ∀ q ∈ spills3 m0 c, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232 := by
  intro q hq
  simp only [spills3, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem spillsI_in (c : KeccakClaimW) {m0 : MachineData} :
    ∀ q ∈ spillsI m0 c, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232 := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact spills3_in c q hq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp

theorem spills3_sub {m0 : MachineData} {c : KeccakClaimW} {d : DataMem}
    (h : FWs m0 d (spills2 m0 c)) : FWs m0 d (spills3 m0 c) := fun q hq ↦ h q (by
  unfold spills2
  exact List.mem_cons_of_mem _ hq)

/-- **The raw `bt`**: bit `j` of a round constant. -/
theorem rcBit : ∀ r < 24, ∀ j < 64,
    CmpOp.apply .bit .W64 (rcW r).toBitVec (BitVec.ofNat 64 j) = testBitW (rcW r) j := by
  unfold rcW
  rw [NativeVm.Math.Keccak.keccakRCW_eq]
  decide +kernel

/-- **The next bit as a mask.** -/
theorem rcMask : ∀ r < 24, ∀ j < 63,
    BinOp.apply .sar .W64 (BinOp.apply .shl .W64 (BinOp.apply .shr .W64 (rcW r).toBitVec
      (BitVec.ofNat 64 j)) (BitVec.ofNat 64 62)) (BitVec.ofNat 64 63) = maskOf (testBitW (rcW r) (j + 1)) := by
  unfold rcW
  rw [NativeVm.Math.Keccak.keccakRCW_eq]
  decide +kernel

theorem and_mask (x : BitVec 64) (b : Bool) :
    BinOp.apply .and .W64 x (maskOf b) = if b then x else 0#64 := by
  cases b
  · simp [BinOp.apply, maskOf]
  · simp [BinOp.apply, maskOf]; exact BitVec.and_allOnes

theorem mask_and (x : BitVec 64) (b : Bool) :
    BinOp.apply .and .W64 (maskOf b) x = if b then x else 0#64 := by
  cases b
  · simp [BinOp.apply, maskOf]
  · simp [BinOp.apply, maskOf]; exact BitVec.allOnes_and

theorem sel_ewArg' (b : Bool) (x y : BitVec 64) :
    ewArg (if b then x else 0#64) (if b then y else 0#64) = sel b (ewArg x y) := by
  cases b <;> rfl

theorem sel_ewArg (b : Bool) (x : EW) :
    ewArg (if b then x.c0.toBitVec else 0#64) (if b then x.c1.toBitVec else 0#64) = sel b x := by
  cases b
  · rfl
  · exact ewArg_ew x

theorem segK_le4 {m0 : MachineData} {c : KeccakClaimW} (h : SegmentsFit (reg m0 .rsi).toNat c) :
    (segK m0 c).size ≤ 4 := by
  rw [segK_size]
  have h2 : c.point.size - ((reg m0 .rsi).toNat - 4) ≤ 2 := h.2
  calc 2 ^ (c.point.size - ((reg m0 .rsi).toNat - 4)) ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by decide) h2
    _ = 4 := rfl

theorem ew_add_assoc'' (x y z : EW) : x + y + z = x + (y + z) := by
  show (⟨(x.c0 ^^^ y.c0) ^^^ z.c0, (x.c1 ^^^ y.c1) ^^^ z.c1⟩ : EW) =
    ⟨x.c0 ^^^ (y.c0 ^^^ z.c0), x.c1 ^^^ (y.c1 ^^^ z.c1)⟩
  rw [UInt64.xor_assoc, UInt64.xor_assoc]

/-- Two terms of a sum, added in the loops' order. -/
theorem xs_two (f : Nat → EW) (i : Nat) (acc : EW) (h : acc = xs f (2 * i)) :
    f (2 * i + 1) + (acc + f (2 * i)) = xs f (2 * (i + 1)) := by
  rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, xs_succ, xs_succ, h, ew_add_comm' (f (2 * i + 1))]

theorem ofBitVec_eq (x : BitVec 64) : UInt64.ofBitVec x = UInt64.ofNat x.toNat := by
  apply UInt64.toBitVec_inj.mp
  simp

theorem low4 : ∀ n < 12, BitVec.ofInt 64 (Int.ofBytes ((NativeRustcVm.wordBytes (UInt64.ofNat n)).take 4)) =
    BitVec.ofNat 64 n := by decide +kernel

/-- A small word's low four bytes, loaded. -/
theorem load4_small [Labels] {env : Env} {r o n : Nat} (hn : n < 12)
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) (UInt64.ofNat n)) :
    env.load r o 4 = BitVec.ofNat 64 n := by
  have h1 : NativeRustcVm.BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o)
      ((NativeRustcVm.wordBytes (UInt64.ofNat n)).take 4) := fun i hi ↦ by
    have hi' : i < 4 := by simp at hi; omega
    have := h i (by simp [NativeRustcVm.wordBytes, LeanVM.Protocol.KeccakHash.wordBytes]; omega)
    rw [List.getElem_take]
    exact this
  rw [Env.load_of_bytesAt (n := 4) (by simp [NativeRustcVm.wordBytes,
    LeanVM.Protocol.KeccakHash.wordBytes]) h1]
  exact low4 n hn

/-- `8 (b - step)` as the code computes it, `step ≤ b < 2^31`. -/
theorem idx8 (b st : Nat) (h : st ≤ b) (hb : b < 2 ^ 28) :
    BinOp.apply .shl .W32 (BinOp.apply .sub .W32 (BitVec.ofNat 64 b) (BitVec.ofNat 64 st))
      (BitVec.ofNat 64 3) = BitVec.ofNat 64 (8 * (b - st)) := by
  simp only [BinOp.apply, shiftCount, shiftMask]
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_ext, BitVec.toNat_shiftLeft, toNat_low, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  have : st < 2 ^ 64 := by omega
  rw [show Width.W32.bits = 32 from rfl, show Width.W8.bits = 8 from rfl,
    show (3 % 2 ^ 64 % 2 ^ 8 &&& 31) = 3 from rfl]
  omega

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {p : Array EW} {s1 : TState}

/-- A region of the scratch beside the frame. -/
theorem wfScr (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {o : Nat}
    {d : MachineData} (hb : Body m0 W o d) {x : BitVec 64} {n : Nat}
    (h1 : (sA m0).toNat ≤ x.toNat) (h2 : x.toNat + n ≤ (sA m0).toNat + 205824)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (envB m0 d [(x, n)] vars ret).WF := by
  have g := geo_of hpre
  have hs := g.hs; have := g.fbN; have := g.hN; have := g.hss; have := g.top
  have hok := areas_ok (pre_areas hpre) (r := ⟨sA m0, 205824⟩) (.inl (by simp))
  refine wf1 (pre_stack hpre) hb (fun i hi ↦ ?_) (by unfold NativeRustcVm.NoWrap; dsimp only; omega) ?_
  · dsimp only at hi ⊢
    have hx : x + BitVec.ofNat 64 i = sA m0 + BitVec.ofNat 64 (x.toNat - (sA m0).toNat + i) := by
      apply BitVec.eq_of_toNat_eq
      rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
      omega
    rw [hx]
    exact hb.fr.kept _ (hok.1 _ (by dsimp only; omega))
  · unfold NativeRustcVm.Apart
    dsimp only
    omega

/-- The round constant `r`, loaded from its region. -/
theorem rcLoad (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {r : Nat} (hr : r < 24) :
    (envB m0 d [(rcAddr, 192)] vars ret).load 1 (8 * r) 8 = (rcW r).toBitVec := by
  have hw : NativeRustcVm.WordsAt d.dmem rcAddr keccakRC := by
    have := hb.keep_ro hpre hWo (r := rcRegion) (by simp) (bs := _) (pre_rc hpre).1
      (by rw [NativeRustcVm.length_wordsBytes]; rfl)
    exact this
  have := hw.getElem (i := r) (by rw [show keccakRC.length = 24 from rfl]; exact hr)
  apply load_of_wordAt
  rw [show rcW r = keccakRC[r]'(by rw [show keccakRC.length = 24 from rfl]; exact hr) by
    unfold rcW keccakRCW
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem]; rfl]
  exact this

/-- A pair of bit weights, loaded from a region at them. -/
theorem wLoad (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → wFront m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {i oo : Nat} (hi : i < 1600) {n : Nat}
    {x : BitVec 64} (hx : x + BitVec.ofNat 64 oo = lA m0 + BitVec.ofNat 64 (16 * i)) :
    ewArg ((envB m0 d [(x, n)] vars ret).load 1 oo 8)
      ((envB m0 d [(x, n)] vars ret).load 1 (oo + 8) 8) = c.weights.getD i 0 := by
  obtain ⟨hs, hw⟩ := hb.weights hpre hW
  have hs' : c.weights.size = 1600 := hs
  have := hw.getElem (i := i) (by rw [Array.length_toList, hs']; exact hi)
  rw [NativeRustcVm.ewAt_iff, Array.getElem_toList] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hs']; exact hi),
    Option.getD_some]
  have hb1 : (envB m0 d [(x, n)] vars ret).base 1 = x := rfl
  have l0 : (envB m0 d [(x, n)] vars ret).load 1 oo 8 = c.weights[i].c0.toBitVec := by
    apply load_of_wordAt
    rw [hb1, hx]; exact this.1
  have l1 : (envB m0 d [(x, n)] vars ret).load 1 (oo + 8) 8 = c.weights[i].c1.toBitVec := by
    apply load_of_wordAt
    rw [hb1, show x + BitVec.ofNat 64 (oo + 8) = (x + BitVec.ofNat 64 oo) + BitVec.ofNat 64 8 by
      bv_omega, hx]; exact this.2
  rw [l0, l1, ewArg_ew]

/-- **A block writing the frame below `24` only** keeps ι's state. -/
theorem K0.blk (hpre : VerifyLayerPre a s c m0) {L : List (Nat × UInt64)}
    (hL : ∀ q ∈ L, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232) {d d' : MachineData} (h : K0 m0 a c p s1 L d)
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d ex vars ret).WF) (hm : Match (envB m0 d ex vars ret) S d')
    (hb' : Body m0 (wFront m0) 24 d') (h0 : S.mem.all (fun w ↦ w.r == 0) = true)
    (hbr : belowRet 2016 S = true) (hin : writesIn S = true) (hmiss : missB 24 1992 S = true)
    (hr : ∀ r ∈ [Reg64.r12, .r13], reg d' r = reg d r) : K0 m0 a c p s1 L d' := by
  have hfr := frSame_blk (o := 24) (n := 1992) hwf hm hin (by decide) hmiss
  exact ⟨hb', ts_blk0 hpre hwf hm h0 hbr h.ts,
    (hfr.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews h.prod
      (by rw [Array.length_toList, h.psize]),
    h.sp.keepIn hfr fun q hq ↦ by have := hL q hq; omega,
    (hfr.sub (o' := 232) (n' := 64) (by decide) (by decide)).ews h.seg
      (by rw [Array.length_toList]; have := segK_le4 (pre_seg hpre); omega),
    by rw [hr .r12 (by simp), hr .r13 (by simp)]; exact h.acc, h.psize, h.ssize⟩

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
