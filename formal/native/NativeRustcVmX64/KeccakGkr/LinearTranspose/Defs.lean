module

public import NativeRustcVmX64.KeccakGkr.Common
public import NativeRustcVmX64.KeccakGkr.LinearTranspose.Exec
public import NativeRustcVm.KeccakGkr.Transpose
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Loop
import Mathlib.Tactic.IntervalCases

/-!
# `linear_transpose`: the body's context (x86-64)

The entry's arguments (`wA` the weights, `gA` `g`, `cA` the columns, `oA` the output), what the
precondition gives (`PreOk`: the regions' numbers, their apartness), what the function may change
(`Out`), the body's context (`Ctx`: the frame, memory changed only in `Out`, R12 the weights, R14
the columns). What the loops fill, by linear index (`gF`, `cF`, `oF`, after
`NativeRustcVm.KeccakGkr.gW`, `colW`, `outW`). Reading the weights (`w_at`) and `KECCAK_RHO`
(`load_rho`); a frame kept by a block that keeps RSP and writes off it (`Frame.keep`).
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)
open NativeRustcVm.KeccakGkr (gW colW weightsBytes)

@[expose] public section

/-- The weights `w`. -/
abbrev wA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- `g`. -/
abbrev gA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The columns. -/
abbrev cA (m0 : MachineData) : BitVec 64 := reg m0 .rdx
/-- The output. -/
abbrev oA (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The frame's base. -/
abbrev fbA (m0 : MachineData) : BitVec 64 := stackBelow m0 64

/-- `g`'s entry `i`. -/
def gF (ws : Array EW) (i : Nat) : EW := gW ws (i / 64) (i % 64)
/-- The columns' entry `i`. -/
def cF (ws : Array EW) (i : Nat) : EW := colW ws (i / 64) (i % 64)
/-- The output's entry `i`. -/
def oF (ws : Array EW) (i : Nat) : EW := NativeRustcVm.KeccakGkr.outW ws (i / 64) (i % 64)

/-- What the function may change: `g`, the columns, the output, its stack. -/
def Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (gA m0) 25600 q ∨ NativeRustcVm.InRange (cA m0) 5120 q ∨
    NativeRustcVm.InRange (oA m0) 25600 q ∨
    NativeRustcVm.InRange (stackBelow m0 linearTransposeStack) linearTransposeStack q

/-- **The precondition's numbers.** -/
structure PreOk [Labels] (m0 : MachineData) (ws : Array EW) : Prop where
  st : StackOk m0 linearTransposeStack
  rho : RhoAt m0
  sz : ws.size = 1600
  wAt : NativeRustcVm.EWsAt m0.dmem (wA m0) ws.toList
  gM : NativeRustcVm.Mapped m0.dmem (gA m0) 25600
  cM : NativeRustcVm.Mapped m0.dmem (cA m0) 5120
  oM : NativeRustcVm.Mapped m0.dmem (oA m0) 25600
  wM : NativeRustcVm.Mapped m0.dmem (wA m0) 25600
  rM : NativeRustcVm.Mapped m0.dmem rhoAddr 100
  sp : 64 ≤ (rspOf m0).toNat ∧ (rspOf m0).toNat + 8 ≤ 2 ^ 64
  gn : (gA m0).toNat + 25600 ≤ 2 ^ 64
  cn : (cA m0).toNat + 5120 ≤ 2 ^ 64
  on : (oA m0).toNat + 25600 ≤ 2 ^ 64
  wn : (wA m0).toNat + 25600 ≤ 2 ^ 64
  rn : rhoAddr.toNat + 100 ≤ 2 ^ 64
  /-- The stack's bottom `S = rsp - 64`, apart from every region. -/
  gS : (gA m0).toNat + 25600 ≤ (rspOf m0).toNat - 64 ∨ (rspOf m0).toNat + 8 ≤ (gA m0).toNat
  cS : (cA m0).toNat + 5120 ≤ (rspOf m0).toNat - 64 ∨ (rspOf m0).toNat + 8 ≤ (cA m0).toNat
  oS : (oA m0).toNat + 25600 ≤ (rspOf m0).toNat - 64 ∨ (rspOf m0).toNat + 8 ≤ (oA m0).toNat
  wS : (wA m0).toNat + 25600 ≤ (rspOf m0).toNat - 64 ∨ (rspOf m0).toNat + 8 ≤ (wA m0).toNat
  rS : rhoAddr.toNat + 100 ≤ (rspOf m0).toNat - 64 ∨ (rspOf m0).toNat + 8 ≤ rhoAddr.toNat
  gc : (gA m0).toNat + 25600 ≤ (cA m0).toNat ∨ (cA m0).toNat + 5120 ≤ (gA m0).toNat
  go : (gA m0).toNat + 25600 ≤ (oA m0).toNat ∨ (oA m0).toNat + 25600 ≤ (gA m0).toNat
  co : (cA m0).toNat + 5120 ≤ (oA m0).toNat ∨ (oA m0).toNat + 25600 ≤ (cA m0).toNat
  gw : (gA m0).toNat + 25600 ≤ (wA m0).toNat ∨ (wA m0).toNat + 25600 ≤ (gA m0).toNat
  cw : (cA m0).toNat + 5120 ≤ (wA m0).toNat ∨ (wA m0).toNat + 25600 ≤ (cA m0).toNat
  ow : (oA m0).toNat + 25600 ≤ (wA m0).toNat ∨ (wA m0).toNat + 25600 ≤ (oA m0).toNat
  gr : (gA m0).toNat + 25600 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ (gA m0).toNat
  cr : (cA m0).toNat + 5120 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ (cA m0).toNat
  or : (oA m0).toNat + 25600 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ (oA m0).toNat

/-- **The body's context**: the frame, memory changed only in `Out`, R12 the weights, R14 the
columns. -/
structure Ctx (m0 : MachineData) (st : MachineData) : Prop where
  frame : Frame m0 64 slots 8 st
  same : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0)
  r12 : reg st .r12 = wA m0
  r14 : reg st .r14 = cA m0

/-- The column `(x + 1) % 5` the output of lane `l` reads at its position. -/
abbrev ca (l : Nat) : Nat := (l % 5 + 1) % 5
/-- The column `(x + 4) % 5` the output of lane `l` reads at the next position. -/
abbrev cb (l : Nat) : Nat := (l % 5 + 4) % 5

end

public section

variable {ws : Array EW} {m0 d d' : MachineData}

theorem stack_eq : linearTransposeStack = 64 := rfl

theorem all_slots : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = true := by
  intro r hr
  cases r <;> simp only [calleeSaved] at hr <;> first | exact absurd hr (by decide) | decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

theorem slots_ge : ∀ p ∈ slots, 16 ≤ p.1 := by decide

theorem stack_side {a r n : Nat} (h : a + n ≤ r - 64 ∨ r - 64 + (64 + 8) ≤ a) (h64 : 64 ≤ r) :
    a + n ≤ r - 64 ∨ r + 8 ≤ a := by omega

theorem preOk [Labels] (h : LinearTransposePre ws m0) : PreOk m0 ws := by
  have hst := h.1
  have hrho := h.2.1
  have hsz := h.2.2.1
  have hw := h.2.2.2.1
  have hA := h.2.2.2.2
  have mg : (⟨gA m0, weightsBytes⟩ : Region) ∈ [⟨gA m0, weightsBytes⟩, ⟨cA m0, 5120⟩,
      ⟨oA m0, weightsBytes⟩] := List.mem_cons_self
  have mc : (⟨cA m0, 5120⟩ : Region) ∈ [⟨gA m0, weightsBytes⟩, ⟨cA m0, 5120⟩,
      ⟨oA m0, weightsBytes⟩] := List.mem_cons_of_mem _ List.mem_cons_self
  have mo : (⟨oA m0, weightsBytes⟩ : Region) ∈ [⟨gA m0, weightsBytes⟩, ⟨cA m0, 5120⟩,
      ⟨oA m0, weightsBytes⟩] := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mw : (⟨wA m0, weightsBytes⟩ : Region) ∈ [⟨wA m0, weightsBytes⟩, rhoRegion] :=
    List.mem_cons_self
  have mr : rhoRegion ∈ [⟨wA m0, weightsBytes⟩, rhoRegion] :=
    List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ogm, ogn⟩ := Areas.ok hA (List.mem_append_left _ mg)
  obtain ⟨ocm, ocn⟩ := Areas.ok hA (List.mem_append_left _ mc)
  obtain ⟨oom, oon⟩ := Areas.ok hA (List.mem_append_left _ mo)
  obtain ⟨owm, own⟩ := Areas.ok hA (List.mem_append_right _ mw)
  obtain ⟨orm, orn⟩ := Areas.ok hA (List.mem_append_right _ mr)
  have sg : _ ∨ _ := Areas.apart_stack hA mg
  have sc : _ ∨ _ := Areas.apart_stack hA mc
  have so : _ ∨ _ := Areas.apart_stack hA mo
  have sw : _ ∨ _ := Areas.stack_read hA mw
  have sr : _ ∨ _ := Areas.stack_read hA mr
  have hd := (List.pairwise_cons.mp hA.2.1).2
  have dgc : _ ∨ _ := List.rel_of_pairwise_cons hd (List.mem_cons_self (a := (⟨cA m0, 5120⟩ : Region)))
  have dgo : _ ∨ _ := List.rel_of_pairwise_cons hd
    (List.mem_cons_of_mem _ (List.mem_singleton.mpr (rfl : (⟨oA m0, weightsBytes⟩ : Region) = _)))
  have dco : _ ∨ _ := List.rel_of_pairwise_cons (List.pairwise_cons.mp hd).2 (List.mem_singleton.mpr rfl)
  have agw : _ ∨ _ := Areas.apart_read hA mg mw
  have acw : _ ∨ _ := Areas.apart_read hA mc mw
  have aow : _ ∨ _ := Areas.apart_read hA mo mw
  have agr : _ ∨ _ := Areas.apart_read hA mg mr
  have acr : _ ∨ _ := Areas.apart_read hA mc mr
  have aor : _ ∨ _ := Areas.apart_read hA mo mr
  have hsb := stackBelow_toNat (m := m0) (n := 64) hst.1
  have h1 := hst.1
  have h2 := hst.2.1
  dsimp only [stackRegion, rhoRegion, weightsBytes, stack_eq, NativeRustcVm.NoWrap] at sg sc so sw sr
  dsimp only [rhoRegion, weightsBytes, NativeRustcVm.NoWrap] at dgc dgo dco agw acw aow agr acr aor
  dsimp only [rhoRegion, weightsBytes, stack_eq, NativeRustcVm.NoWrap] at ogn ocn oon own orn h1
  rw [hsb] at sg sc so sw sr
  exact ⟨hst, hrho, hsz, hw, ogm, ocm, oom, owm, orm, ⟨h1, h2⟩, ogn, ocn, oon, own, orn,
    stack_side sg h1, stack_side sc h1, stack_side so h1, stack_side (Or.symm sw) h1,
    stack_side (Or.symm sr) h1, dgc, dgo, dco, agw, acw, aow, agr, acr, aor⟩

/-- **A frame kept** by a step that keeps RSP and the mapped bytes and writes off the frame. -/
theorem Frame.keep {o : Nat} (hf : Frame m0 64 slots o d) (hk : Kept d.dmem d'.dmem)
    (hrsp : rspOf d' = rspOf d) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (stackBelow m0 64) (64 + 8) q)
    (hnw : NativeRustcVm.NoWrap (stackBelow m0 64) (64 + 8)) : Frame m0 64 slots o d' := by
  have hnw' : (stackBelow m0 64).toNat + (64 + 8) ≤ 2 ^ 64 := hnw
  refine ⟨hrsp.trans hf.sp, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hk,
    fun r hr hsl ↦ absurd (all_slots r hr) (by rw [hsl]; decide)⟩
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [NativeRustcVm.Transcript.off_add]
    exact hso _ fun h ↦ hR _ h (inRange_off_self (by have := slots_le p hp; omega)
      (by omega))
  · rw [hso _ fun h ↦ hR _ h (inRange_off_self (by omega) (by omega))]
    exact hf.ret j hj

/-- **An element of the weights**, in a state changed only in `Out`. -/
theorem w_at [Labels] (h : PreOk m0 ws) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)) {i : Nat}
    (hi : i < 1600) : NativeRustcVm.EWAt d.dmem (off (wA m0) (16 * i)) (ws.getD i 0) := by
  have h' := ewsAt_getD h.wAt (i := i) (by rw [h.sz]; exact hi)
  refine bytesAt_congr h' fun j hj ↦ hs _ fun hO ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hj
  have hq : (off (wA m0) (16 * i) + BitVec.ofNat 64 j).toNat = (wA m0).toNat + (16 * i + j) := by
    rw [NativeRustcVm.Transcript.off_add, toNat_off (by have := h.wn; omega)]
  have hsb := stackBelow_toNat (m := m0) (n := 64) h.sp.1
  have := h.gn; have := h.cn; have := h.on; have := h.wn
  have := h.gw; have := h.cw; have := h.ow; have := h.wS; have := h.sp
  rcases hO with hO | hO | hO | hO
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at hO; omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at hO; omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at hO; omega
  · rw [stack_eq, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq, hsb] at hO; omega

/-! ## `KECCAK_RHO` -/

theorem rhoBytes_length : rhoBytes.length = 100 := by decide

theorem rho_lt {l : Nat} (hl : l < 25) : keccakRhoW.getD l 0 < 64 := by
  interval_cases l <;> decide

theorem rho_word {l : Nat} (hl : l < 25) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 4).map fun i ↦ rhoBytes.getD (4 * l + i) 0)) =
      BitVec.ofNat 64 (keccakRhoW.getD l 0) := by
  interval_cases l <;> decide

/-- `KECCAK_RHO` in a state changed only in `Out`. -/
theorem rho_at [Labels] (h : PreOk m0 ws) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)) :
    NativeRustcVm.BytesAt d.dmem rhoAddr rhoBytes := by
  refine bytesAt_congr h.rho fun j hj ↦ hs _ fun hO ↦ ?_
  rw [rhoBytes_length] at hj
  have hq : (rhoAddr + BitVec.ofNat 64 j).toNat = rhoAddr.toNat + j := toNat_off (by
    have := h.rn; omega)
  have hsb := stackBelow_toNat (m := m0) (n := 64) h.sp.1
  have := h.gn; have := h.cn; have := h.on; have := h.rn
  have := h.gr; have := h.cr; have := h.or; have := h.rS; have := h.sp
  rcases hO with hO | hO | hO | hO
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at hO; omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at hO; omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at hO; omega
  · rw [stack_eq, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq, hsb] at hO; omega

/-- **ρ of a lane**, loaded as a `u32`. -/
theorem load_rho [Labels] {env : Env} {r : Nat} (hb : env.base r = rhoAddr)
    (h : NativeRustcVm.BytesAt env.mem0 rhoAddr rhoBytes) {l : Nat} (hl : l < 25) :
    env.load r (4 * l) 4 = BitVec.ofNat 64 (keccakRhoW.getD l 0) := by
  rw [← rho_word hl]
  unfold Env.load
  congr 2
  refine List.map_congr_left fun i hi ↦ ?_
  have hi : i < 4 := List.mem_range.mp hi
  have hlt : 4 * l + i < rhoBytes.length := by rw [rhoBytes_length]; omega
  rw [hb, h _ hlt, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    Option.getD_some]

/-! ## Positions -/

/-- A position's byte offset: `16 (x % 64)`, for `x < 2 ^ 32`. -/
theorem posS_eval [Labels] (env : Env) (x : Sym) (hx : (x.eval env).toNat < 2 ^ 32) :
    ((posS x).eval env).toNat = 16 * ((x.eval env).toNat % 64) := by
  unfold posS
  simp only [Sym.eval, BinOp.apply, UnOp.apply, toNat_ext,
    show shiftCount .W32 (BitVec.ofNat 64 4) = 4 by decide]
  rw [BitVec.toNat_shiftLeft, low, BitVec.toNat_setWidth, toNat_ext, BitVec.toNat_and, low,
    BitVec.toNat_setWidth, toNat_ext, low, BitVec.toNat_setWidth, low, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  simp only [Width.bits]
  rw [Nat.mod_eq_of_lt (show (x.eval env).toNat < 2 ^ 32 from hx),
    show 63 % 2 ^ 64 % 2 ^ 32 = 63 from rfl, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  omega

/-! ## The model -/

theorem cF_eq (ws : Array EW) {x z : Nat} (hz : z < 64) :
    cF ws (64 * x + z) = gF ws (64 * (x + 5 * 0) + z) + gF ws (64 * (x + 5 * 1) + z) +
      gF ws (64 * (x + 5 * 2) + z) + gF ws (64 * (x + 5 * 3) + z) +
        gF ws (64 * (x + 5 * 4) + z) := by
  simp only [cF, gF, colW]
  rw [show (64 * x + z) / 64 = x by omega, show (64 * x + z) % 64 = z by omega]
  simp only [show ∀ y, (64 * (x + 5 * y) + z) / 64 = x + 5 * y from fun y ↦ by omega,
    show ∀ y, (64 * (x + 5 * y) + z) % 64 = z from fun y ↦ by omega]
  rfl

theorem oF_eq (ws : Array EW) {l z : Nat} (hz : z < 64) :
    oF ws (64 * l + z) =
      gF ws (64 * l + z) + cF ws (64 * ca l + z) + cF ws (64 * cb l + (z + 1) % 64) := by
  have h1 : (z + 1) % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [oF, gF, cF, NativeRustcVm.KeccakGkr.outW]
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega,
    show (64 * ca l + z) / 64 = ca l by omega, show (64 * ca l + z) % 64 = z by omega,
    show (64 * cb l + (z + 1) % 64) / 64 = cb l by omega,
    show (64 * cb l + (z + 1) % 64) % 64 = (z + 1) % 64 by omega]

/-- The column's five elements summed as the `xor` chains. -/
theorem col_ew (a0 a1 a2 a3 a4 : EW) :
    (⟨UInt64.ofBitVec ((((a1.c0.toBitVec ^^^ a0.c0.toBitVec) ^^^ a2.c0.toBitVec) ^^^
        a3.c0.toBitVec) ^^^ a4.c0.toBitVec),
      UInt64.ofBitVec ((((a1.c1.toBitVec ^^^ a0.c1.toBitVec) ^^^ a2.c1.toBitVec) ^^^
        a3.c1.toBitVec) ^^^ a4.c1.toBitVec)⟩ : EW) = a0 + a1 + a2 + a3 + a4 := by
  show EW.mk _ _ = EW.mk ((((a0.c0 ^^^ a1.c0) ^^^ a2.c0) ^^^ a3.c0) ^^^ a4.c0)
    ((((a0.c1 ^^^ a1.c1) ^^^ a2.c1) ^^^ a3.c1) ^^^ a4.c1)
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;> simp only [UInt64.toBitVec_xor] <;> ac_rfl

/-- The output element as the loop's `xor`s. -/
theorem out_ew (g a b : EW) :
    (⟨UInt64.ofBitVec ((a.c0.toBitVec ^^^ g.c0.toBitVec) ^^^ b.c0.toBitVec),
      UInt64.ofBitVec ((a.c1.toBitVec ^^^ g.c1.toBitVec) ^^^ b.c1.toBitVec)⟩ : EW) = g + a + b := by
  show EW.mk _ _ = EW.mk ((g.c0 ^^^ a.c0) ^^^ b.c0) ((g.c1 ^^^ a.c1) ^^^ b.c1)
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;> simp only [UInt64.toBitVec_xor] <;> ac_rfl

/-- The output's elements as the model's list. -/
theorem out_list {D : DataMem} {a : BitVec 64} (h : ElemsAt D a (oF ws) 1600) :
    NativeRustcVm.EWsAt D a (keccakLinearTranspose ws).toList := by
  apply ElemsAt.ewsAt
  rw [Array.length_toList, NativeRustcVm.KeccakGkr.linearTranspose_size']
  intro i hi
  obtain ⟨l, z, hz, rfl⟩ : ∃ l z, z < 64 ∧ i = 64 * l + z :=
    ⟨i / 64, i % 64, Nat.mod_lt _ (by decide), by omega⟩
  have e : (keccakLinearTranspose ws).toList.getD (64 * l + z) 0 = oF ws (64 * l + z) := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?,
      NativeRustcVm.KeccakGkr.linearTranspose_getD' ws (by omega) hz, oF,
      show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega]
  have := h _ hi
  rw [← e] at this
  exact this

/-- A register the block left as its atom. -/
theorem atoms_eq [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {rs : List Reg64} (h : atoms S rs = true) {r : Reg64} (hr : r ∈ rs) :
    reg m r = env.regs r := by
  unfold atoms at h
  have := List.all_eq_true.mp h r hr
  rw [beq_iff_eq] at this
  exact hm.regs r _ this

theorem regOk_mem {S : SState} (h : regOk S = true) : S.mem = [] := by
  unfold regOk at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.1

theorem regOk_rsp {S : SState} (h : regOk S = true) : S.reg .rsp = some (.reg .rsp) := by
  unfold regOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- A register holding another's atom plus a literal, by `isAddLit`. -/
theorem isAddLit_eval [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r r' : Reg64} {c : Nat} (h : isAddLit (S.reg r) r' c = true) :
    reg m r = env.regs r' + BitVec.ofNat 64 c := by
  unfold isAddLit at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with (h | h) | ⟨hc, h⟩
  · rw [show reg m r = _ from hm.regs r _ h]; simp [Sym.eval, BinOp.apply]
  · rw [show reg m r = _ from hm.regs r _ h]; simp [Sym.eval, BinOp.apply, BitVec.add_comm]
  · rw [show reg m r = _ from hm.regs r _ h, hc]; simp [Sym.eval]

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
