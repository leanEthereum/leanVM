/-
  Rv64mc.Proof.Hash.KeccakHashT

  `verifier::hash::keccak_hash(data) -> Digest` is total (`KeccakHashSafeT`): from a digest slot at `sret` in a
  window apart from the static data and `NEXT` and from the stack below the stack pointer, and the data's bytes
  (`a1`, `a2`) in a window apart from that stack unless there are none, it returns, writing at most the slot's
  doublewords (`Spec.Hash.DigestOut`). It does not state the digest, which is `Spec.Hash.KeccakHash`'s partial
  contract, not proved; no caller's safety reads it as an address.

  The full blocks' bytes are computed by `mulhu` by the reciprocal of `136` (`full_toNat`). The block loop is
  `Total.loop` with the blocks left as the measure (`loop_ok`); after it, the last partial block is copied by
  `memcpy` into a zeroed buffer of the frame (`tail_ok`). The parts keep `MemInv`: the frame writing at most the slot,
  the static data, the code and the saved registers' slots.

  ## Main definitions

  * `HashPreT`, `KeccakHashSafeT`

  ## Main results

  * `full_toNat`
  * `total`
-/

import Rv64mc.Spec.Hash.Keccak
import Rv64mc.Proof.Hash.XorBlockT
import Rv64mc.Proof.Hash.KeccakFT
import Rv64mc.Gen.Tmpl.Verifier.Hash.KeccakHash

namespace Rv64mc.Proof.Hash.KeccakHashT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Hash
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.MemsetT (MemsetSafeT InWin)
open Rv64mc.Proof.Hash.XorBlockT (XorBlockSafeT)
open Rv64mc.Proof.Hash.KeccakFT (KeccakFSafeT)
open Rv64mc.Gen.Verifier.Hash.KeccakHash (Link tmpl)

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

/-- `keccak_hash`'s total precondition: the digest's slot in a window apart from the static data and `NEXT`, and
    from the stack below the stack pointer; the data in a window apart from that stack, unless it is empty. -/
def HashPreT (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  InWin env (regs .x10) Layouts.Digest.byteSize ∧ OffStack env (regs .x2) (regs .x10) Layouts.Digest.byteSize ∧
    ((regs .x12).toNat = 0 ∨
      (inWindow (regs .x11) (regs .x12).toNat = true ∧ OffStack env (regs .x2) (regs .x11) (regs .x12).toNat))

/-- **The total contract of `keccak_hash`**: it returns, writing at most the digest's slot. -/
def KeccakHashSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (HashPreT env) (fun _ _ _ _ => True) fun regs _ => DigestOut (regs .x10)

/-- `mulhu` as the quotient of the product. -/
theorem mulhu_eval' (a c : Word) : BinOp.mulhu.eval a c = BitVec.ofNat 64 (a.toNat * c.toNat / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.eval, BitVec.truncate_eq_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt; have hc := c.isLt
  have h : a.toNat * c.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hc
  have e : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by rw [← Nat.pow_add]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show c.toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show a.toNat * c.toNat < 2 ^ 128 by omega)]

/-- The quotient by `136` as a product by its reciprocal. -/
theorem div136 {j : Nat} (hj : j < 2 ^ 64) : j * 17361641481138401521 / 2 ^ 64 / 2 ^ 7 = j / 136 := by
  rw [Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 * 2 ^ 7 = 2361183241434822606848 from rfl]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 136 ∧ j = 136 * q + r :=
    ⟨j / 136, j % 136, Nat.mod_lt _ (by omega), (Nat.div_add_mod j 136).symm⟩
  rw [show (136 * q + r) / 136 = q by omega]
  apply Nat.div_eq_of_lt_le <;> omega

/-- The bytes of the full blocks, computed by `mulhu`: `136` times the blocks. -/
theorem full_toNat (len : Word) :
    ((BinOp.mulhu.eval len 17361641481138401521#64 &&& 18446744073709551488#64) +
      (BinOp.mulhu.eval len 17361641481138401521#64 >>> 4 &&& 18446744073709551608#64)).toNat =
      136 * (len.toNat / 136) := by
  rw [show (18446744073709551488#64 : Word) = BitVec.allOnes 64 <<< 7 by decide,
    show (18446744073709551608#64 : Word) = BitVec.allOnes 64 <<< 3 by decide,
    ← BitVec.shiftLeft_ushiftRight, ← BitVec.shiftLeft_ushiftRight, mulhu_eval',
    show (17361641481138401521#64 : Word).toNat = 17361641481138401521 from rfl]
  have hl := len.isLt
  have hq := div136 hl
  have h1 : len.toNat * 17361641481138401521 / 2 ^ 64 < 2 ^ 64 := by omega
  generalize len.toNat * 17361641481138401521 / 2 ^ 64 = h at hq h1 ⊢
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, show (2 : Nat) ^ 4 * 2 ^ 3 = 2 ^ 7 from rfl, hq]
  have : len.toNat / 136 < 2 ^ 58 := by omega
  omega

/-- The memory after the prologue's saves. -/
def saves (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
    (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
    (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)

/-- The saved slots' words. -/
theorem saves_get {m : MachineState} {top ret : Word} {regs : Reg → Word} :
    (saves m top ret regs).getMem (top + 0xfffffffffffffff8#64) = ret ∧
    (saves m top ret regs).getMem (top + 0xfffffffffffffff0#64) = regs .x8 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffe8#64) = regs .x9 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffe0#64) = regs .x18 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffd8#64) = regs .x19 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffd0#64) = regs .x20 := by
  unfold saves
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne, BitVec.add_right_inj]

/-- What the parts keep of memory: the frame (writing at most the slot), the static data, the code and the saved
    registers' slots. -/
def MemInv (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  env.Frame top (DigestOut (regs .x10)) m M ∧ env.Static M ∧ M.code = m.code ∧
    ∀ a, top + 0xffffffffffffffd0#64 ≤ a → a ≤ top + 0xfffffffffffffff8#64 →
      M.getMem a = (saves m top ret regs).getMem a

/-- The saved registers' lowest slot, `top - 0x30`, as a natural number. -/
theorem lo_toNat {top : Word} (h : 0x30 ≤ top.toNat) : (top + 0xffffffffffffffd0#64).toNat = top.toNat - 0x30 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The prologue's memory keeps `MemInv`. -/
theorem MemInv.prologue {ret top : Word} {regs : Reg → Word} {m : MachineState} (hS : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hroom : env.stackLimit.toNat + 0x30 ≤ top.toNat) :
    MemInv env ret top regs m (saves m top ret regs) := by
  refine ⟨?_, ?_, by simp only [saves, MachineState.code_setMem], fun _ _ _ => rfl⟩
  · unfold saves
    repeat refine Tactic.frame_slot ?_ ?_ ?_
    · exact Env.Frame.refl hnx
    all_goals (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  · unfold saves
    repeat refine Env.static_setMem_stack ?_ ?_
    · exact hS
    all_goals (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

/-- A call writing at most the stack below the saved slots keeps `MemInv`. -/
theorem MemInv.call {ret top t : Word} {regs : Reg → Word} {m M M' : MachineState} {out : Word → Prop}
    (hroom : env.stackLimit.toNat + 0x30 ≤ top.toNat) (h : MemInv env ret top regs m M)
    (hf : env.Frame t out M M') (ht : t.toNat + 0x30 ≤ top.toNat)
    (hout : ∀ a, out a → env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 0x30 < top.toNat) (hs : env.Static M')
    (hc : M'.code = M.code) : MemInv env ret top regs m M' := by
  obtain ⟨hF, hS, hc0, hsv⟩ := h
  have := env.layout
  refine ⟨hF.trans hf (by omega) fun a ha => Or.inl ⟨(hout a ha).1, by have := (hout a ha).2; omega⟩, hs,
    hc.trans hc0, fun a h1 h2 => ?_⟩
  have := BitVec.le_def.1 h1
  rw [lo_toNat (by omega)] at this
  rw [hf.2.2 a fun hw => ?_]
  · exact hsv a h1 h2
  have := hf.2.1
  have := hF.2.1
  rcases hw with hw | hw | hw | hw
  · omega
  · omega
  · subst hw; omega
  · have := hout a hw; omega

/-- A store into the stack below the saved slots keeps `MemInv`. -/
theorem MemInv.stack {ret top x v : Word} {regs : Reg → Word} {m M : MachineState}
    (h : MemInv env ret top regs m M) (hlo : env.stackLimit.toNat ≤ x.toNat) (hhi : x.toNat + 0x38 ≤ top.toNat) :
    MemInv env ret top regs m (M.setMem x v) := by
  obtain ⟨hF, hS, hc, hsv⟩ := h
  refine ⟨Tactic.frame_slot hF hlo (by omega), Env.static_setMem_stack hS hlo, by rw [MachineState.code_setMem, hc],
    fun a h1 h2 => ?_⟩
  rw [MachineState.getMem_setMem_ne (fun he => ?_)]
  · exact hsv a h1 h2
  · subst he
    have := BitVec.le_def.1 h1
    rw [lo_toNat (by omega)] at this
    omega

/-- The full blocks' bytes as the code computes them from the length. -/
def full (len : Word) : Word :=
  (BinOp.mulhu.eval len 17361641481138401521#64 &&& 18446744073709551488#64) +
    (BinOp.mulhu.eval len 17361641481138401521#64 >>> 4 &&& 18446744073709551608#64)

/-- The bytes left after the full blocks: the length modulo `136`. -/
theorem sub_full (len : Word) : (len - full len).toNat = len.toNat - 136 * (len.toNat / 136) := by
  have h := full_toNat len
  unfold full; rw [BitVec.toNat_sub, h]; omega

/-- The data pointer advanced past the full blocks, when it does not wrap. -/
theorem add_full (d len : Word) (h : len.toNat = 0 ∨ d.toNat + len.toNat < 2 ^ 64) :
    (d + full len).toNat = d.toNat + 136 * (len.toNat / 136) := by
  have h' := full_toNat len
  unfold full; rw [BitVec.toNat_add, h']; omega

/-- What the entry gives every part. -/
structure Fx (env : Env) (needC : Nat) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  win : Windows env top m
  room : env.stackLimit.toNat + (0x180 + needC) ≤ top.toNat
  al : top.toNat % 16 = 0
  sw : InWin env (regs .x10) Layouts.Digest.byteSize
  soff : OffStack env top (regs .x10) Layouts.Digest.byteSize
  dat : (regs .x12).toNat = 0 ∨
    (inWindow (regs .x11) (regs .x12).toNat = true ∧ OffStack env top (regs .x11) (regs .x12).toNat)

/-- The continuation every part is proved against: the contract's, at the return. -/
abbrev Cont (env : Env) (p : Lprog (Op Reg) Reg) (Q : State rvIsa → Prop) (ret top : Word) (rest : List Frame)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun regs _ => DigestOut (regs .x10)) ret top regs m r' m' →
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩

/-- The fixed facts every part takes. -/
structure Ctx (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (needC : Nat) (Q : State rvIsa → Prop)
    (ret top : Word) (rest : List Frame) (regs : Reg → Word) (m : MachineState) : Prop where
  hp : p[i]? = some (tmpl L)
  hL : L.WF p
  hcpy : MemcpySpecT env p L.memcpy.idx needC
  hset : MemsetSafeT env p L.memset.idx needC
  hxb : XorBlockSafeT env p L.xorBlock.idx needC
  hkf : KeccakFSafeT env p L.keccakF.idx needC
  F : Fx env needC top regs m
  hk : Cont env p Q ret top rest regs m

variable {needC : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
  {m : MachineState}

/-- A byte store into the stack below the saved slots keeps `MemInv`. -/
theorem MemInv.byte {ret top x : Word} {c : BitVec 8} {regs : Reg → Word} {m M : MachineState}
    (h : MemInv env ret top regs m M) (h8 : top.toNat % 8 = 0) (hlo : env.stackLimit.toNat + 7 ≤ x.toNat)
    (hhi : x.toNat + 0x31 ≤ top.toNat) : MemInv env ret top regs m (M.setByte x c) := by
  rw [setByte_def]
  have := toNat_alignToDword x
  exact h.stack (by omega) (by omega)

/-- A byte store into the digest's slot keeps `MemInv`. -/
theorem MemInv.out {ret top x : Word} {c : BitVec 8} {regs : Reg → Word} {m M : MachineState}
    (h : MemInv env ret top regs m M) (hw : InWin env (regs .x10) Layouts.Digest.byteSize)
    (ho : OffStack env top (regs .x10) Layouts.Digest.byteSize) (hroom : env.stackLimit.toNat + 0x30 ≤ top.toNat)
    (hx1 : (regs .x10).toNat ≤ x.toNat) (hx2 : x.toNat < (regs .x10).toNat + Layouts.Digest.byteSize) :
    MemInv env ret top regs m (M.setByte x c) := by
  obtain ⟨hF, hS, hc, hsv⟩ := h
  have ha := toNat_alignToDword x
  have ⟨hs, hn⟩ := hw.apart (b := alignToDword x) (by omega) (by omega)
  have hsb : Layouts.Digest.byteSize = 32 := rfl
  unfold OffStack at ho
  refine ⟨frame_byte_out hF ?_ hn, static_byte hS hs, by rw [setByte_def, MachineState.code_setMem, hc],
    fun a h1 h2 => ?_⟩
  · unfold DigestOut DwordsOf InRange; rw [toNat_alignToDword, toNat_alignToDword]; omega
  rw [getMem_setByte_ne (fun he => ?_)]
  · exact hsv a h1 h2
  · have := BitVec.le_def.1 h1
    rw [lo_toNat (by omega)] at this
    have h2' := BitVec.le_def.1 h2
    rw [show (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega] at h2'
    have := congrArg BitVec.toNat he
    rw [toNat_alignToDword] at this
    have := (regs .x10).isLt
    unfold InWin at hw
    omega

/-- A byte store at offset `k` of the digest's slot keeps `MemInv`. -/
theorem MemInv.outK {ret top : Word} {c : BitVec 8} {regs : Reg → Word} {m M : MachineState} {k : Nat}
    (h : MemInv env ret top regs m M) (hw : InWin env (regs .x10) Layouts.Digest.byteSize)
    (ho : OffStack env top (regs .x10) Layouts.Digest.byteSize) (hroom : env.stackLimit.toNat + 0x30 ≤ top.toNat)
    (hk : k < 32) : MemInv env ret top regs m (M.setByte (regs .x10 + BitVec.ofNat 64 k) c) := by
  have := (regs .x10).isLt
  unfold InWin at hw
  have hsb : Layouts.Digest.byteSize = 32 := rfl
  refine h.out hw ho hroom ?_ ?_ <;> rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

/-- A byte store at the digest's slot keeps `MemInv`. -/
theorem MemInv.out0 {ret top : Word} {c : BitVec 8} {regs : Reg → Word} {m M : MachineState}
    (h : MemInv env ret top regs m M) (hw : InWin env (regs .x10) Layouts.Digest.byteSize)
    (ho : OffStack env top (regs .x10) Layouts.Digest.byteSize) (hroom : env.stackLimit.toNat + 0x30 ≤ top.toNat) :
    MemInv env ret top regs m (M.setByte (regs .x10) c) := by
  have := h.outK (k := 0) (c := c) hw ho hroom (by decide)
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this

/-- What a call on the state at `sp` writes lies below the saved slots. -/
theorem state_out {top a : Word} {R : Reg → Word} {n : Nat}
    (hroom : env.stackLimit.toNat + (0x180 + n) ≤ top.toNat) (h10 : R .x10 = top + 0xfffffffffffffe80#64)
    (ha : InRange (R .x10) stateBytes a) : env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 0x30 < top.toNat := by
  have e : (top + 0xfffffffffffffe80#64).toNat = top.toNat - 0x180 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  unfold InRange at ha; rw [h10, e] at ha
  have : stateBytes = 200 := rfl
  omega

/-- A byte of the frame's buffer at `sp + 0xc8`. -/
theorem buf_toNat {top n : Word} (hroom : 0x180 ≤ top.toNat) (hl : top.toNat ≤ 0xc0000000) (hn : n.toNat < 136) :
    (top + 0xffffffffffffff48#64 + n).toNat = top.toNat - 0xb8 + n.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- What `memset` writes at entry, the state at `sp`, lies below the saved slots. -/
theorem state_out' {top a : Word} {R : Reg → Word} {M : MachineState} {n : Nat} (h16 : top.toNat % 16 = 0)
    (hroom : env.stackLimit.toNat + (0x180 + n) ≤ top.toNat) (h10 : R .x10 = top + 0xfffffffffffffe80#64)
    (h12 : R .x12 = 200#64) (ha : CopyOut R M a) :
    env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 0x30 < top.toNat := by
  have := KeccakFT.copyOut_frame (o := 0x180) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega) h10 ha
  rw [h12, show (200#64).toNat = 200 from rfl] at this
  omega

/-- What a copy into the frame's buffer at `sp + 0xc8` writes lies below the saved slots. -/
theorem buf_out {top a : Word} {R : Reg → Word} {M : MachineState} {n : Nat} (h16 : top.toNat % 16 = 0)
    (hroom : env.stackLimit.toNat + (0x180 + n) ≤ top.toNat) (h10 : R .x10 = top + 0xffffffffffffff48#64)
    (h12 : (R .x12).toNat ≤ 136) (ha : CopyOut R M a) :
    env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 0x30 < top.toNat := by
  have := KeccakFT.copyOut_frame (o := 0xb8) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega) h10 ha
  omega

/-- The callee-saved registers the function never writes. -/
def Rest (regs r : Reg → Word) : Prop :=
  r .x21 = regs .x21 ∧ r .x22 = regs .x22 ∧ r .x23 = regs .x23 ∧ r .x24 = regs .x24 ∧ r .x25 = regs .x25 ∧
    r .x26 = regs .x26 ∧ r .x27 = regs .x27

/-- Inside the last block: the buffer at `sp + 0xc8` in `s3`, the last bytes' count in `s1`. -/
def Tail2 (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (r : Reg → Word) (M : MachineState) :
    Prop :=
  r .x2 = top + 0xfffffffffffffe80#64 ∧ r .x8 = regs .x10 ∧ r .x19 = top + 0xffffffffffffff48#64 ∧
    r .x9 = regs .x12 - full (regs .x12) ∧ Rest regs r ∧ MemInv env ret top regs m M

/-- The return, from `MemInv` and the calling convention's registers. -/
theorem ret_of (hk : Cont env p Q ret top rest regs m) {r' : Reg → Word} {M : MachineState}
    (hM : MemInv env ret top regs m M) (ha : AbiRegs top regs r') : rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', M⟩ :=
  hk _ _ ⟨⟨ha, hM.1, hM.2.1, trivial⟩, hM.2.2.1⟩

/-- After the full blocks: the last bytes' pointer in `s2` and their count in `s1`. -/
def Tail (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (r : Reg → Word) (M : MachineState) :
    Prop :=
  r .x2 = top + 0xfffffffffffffe80#64 ∧ r .x8 = regs .x10 ∧ r .x18 = regs .x11 + full (regs .x12) ∧
    r .x9 = regs .x12 - full (regs .x12) ∧ Rest regs r ∧ MemInv env ret top regs m M

set_option hygiene false in
/-- The fixed facts and a part's memory facts as hypotheses. -/
local macro "fx_facts " C:term:max hM:term:max : tactic => `(tactic| (
  have hp := ($C).hp; have hL := ($C).hL; have hcpy := ($C).hcpy; have hset := ($C).hset; have hxb := ($C).hxb
  have hkf := ($C).hkf; have hk := ($C).hk; have F := ($C).F
  have hW := F.win; have hroom := F.room; have h16 := F.al; have hsw := F.sw; have hsoff := F.soff
  have hdat := F.dat; unfold OffStack at hsoff hdat; unfold InWin at hsw; rw [inWindow_iff] at hdat
  have hsb : Layouts.Digest.byteSize = 32 := rfl
  have hS := ($hM).2.1; have hcode := ($hM).2.2.1; have hsv := ($hM).2.2.2
  have hfull := full_toNat (regs .x12)
  have hsub := sub_full (regs .x12)
  have hadd := add_full (regs .x11) (regs .x12) (by omega)
  have hly := env.layout; have hl := hW.top_le; have hna := hW.nextAddr_ge; have hhe := hW.heapEnd_le))

/-- `MemInv` through byte stores into the digest's slot. -/
local macro "out_close " F:term:max hM:term:max : tactic => `(tactic| (
  repeat (first
    | with_reducible refine MemInv.out0 ?_ ($F).sw ($F).soff (by omega)
    | with_reducible refine MemInv.outK ?_ ($F).sw ($F).soff (by omega) (by decide))
  exact $hM))

/-- After the last block's permutation: the digest's slot in `s0`. -/
def Fin (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (r : Reg → Word) (M : MachineState) :
    Prop :=
  r .x2 = top + 0xfffffffffffffe80#64 ∧ r .x8 = regs .x10 ∧ Rest regs r ∧ MemInv env ret top regs m M

set_option rv_sym.heap true in
/-- The saved registers restored, the return. -/
theorem fin2_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hT : Fin env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 256, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, hr, hM⟩ := hT
  fx_facts C hM
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := saves_get (m := m) (top := top) (ret := ret) (regs := regs)
  have hR := And.intro h2 (And.intro h8 hr)
  rv_introT hR
  rv_symT hp
  open Tactic in
    exact ret_of hk hM ⟨rf_get_x2 .., (rf_get_x8 ..).trans s2, (rf_get_x9 ..).trans s3, (rf_get_x18 ..).trans s4,
      (rf_get_x19 ..).trans s5, (rf_get_x20 ..).trans s6, rf_get_x21 .., rf_get_x22 .., rf_get_x23 .., rf_get_x24 ..,
      rf_get_x25 .., rf_get_x26 .., rf_get_x27 ..⟩

set_option rv_sym.heap true in
/-- The digest's last bytes written into its slot. -/
theorem finB_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hT : Fin env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, hr, hM⟩ := hT
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 hr)
  rv_introT hR
  rv_symT hp stop [256]
  refine fin2_ok C ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?mem⟩
  case mem => out_close F hM
  all_goals rfl

set_option rv_sym.heap true in
/-- The digest's first bytes written into its slot. -/
theorem fin_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hT : Fin env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 128, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, hr, hM⟩ := hT
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 hr)
  rv_introT hR
  rv_symT hp stop [192]
  refine finB_ok C ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?mem⟩
  case mem => out_close F hM
  all_goals rv_closeT

set_option rv_sym.heap true in
/-- The last block absorbed and permuted. -/
theorem tail3_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hT : Fin env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, hr, hM⟩ := hT
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 hr)
  rv_introT hR
  rv_symT hp stop [128] with [hL] using [hcpy, hset, hxb, hkf]
  refine fin_ok C ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?mem⟩
  case mem =>
    have e : (top + 0xfffffffffffffe80#64).toNat + 0x30 ≤ top.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact MemInv.call (by omega) (MemInv.call (by omega) hM hret1_14 e (fun a ha => state_out hroom rfl ha)
      hret1_15 hret1_16) hret2_14 e (fun a ha => state_out hroom rfl ha) hret2_15 hret2_16
  all_goals rfl

set_option rv_sym.heap true in
/-- The last block's padding. -/
theorem tail2_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hT : Tail2 env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 100, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, h19, h9, hr, hM⟩ := hT
  fx_facts C hM
  have e1 : (top + 0xffffffffffffff48#64).toNat = top.toNat - 0xb8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eb := buf_toNat (n := regs .x12 - full (regs .x12)) (by omega) hl (by rw [hsub]; omega)
  rw [hsub] at eb
  have hR := And.intro h2 (And.intro h8 (And.intro h19 (And.intro h9 hr)))
  rv_introT hR
  rv_symT hp stop [114]
  refine tail3_ok C ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?mem⟩
  case mem =>
    have e2 : (top + 0xffffffffffffffcf#64).toNat = top.toNat - 0x31 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine (hM.byte (by omega) ?_ ?_).byte (by omega) ?_ ?_ <;> (try rw [eb]) <;> (try rw [e2]) <;> omega
  all_goals rfl

set_option rv_sym.heap true in
/-- The last partial block, the digest written, the return. -/
theorem tail_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hT : Tail env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, h18, h9, hr, hM⟩ := hT
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 (And.intro h18 (And.intro h9 hr)))
  rv_introT hR
  rv_symT hp stop [100] with [hL] using [hcpy, hset, hxb, hkf]
  · have e1 : (top + 0xffffffffffffff48#64).toNat = top.toNat - 0xb8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e2 : (top + 0xfffffffffffffe80#64).toNat = top.toNat - 0x180 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    unfold OffStack
    rw [hsub, hadd, e1, e2, inWindow_iff]
    omega
  · refine tail2_ok C ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?mem⟩
    case mem =>
      refine MemInv.call (by omega) (MemInv.call (by omega) hM hret1_14 (by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (fun a ha => buf_out h16 hroom rfl (Nat.le_of_eq rfl) ha)
        hret1_15 hret1_17) hret2_14 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (fun a ha => buf_out h16 hroom rfl
          (by show (regs .x12 - full (regs .x12)).toNat ≤ 136; rw [hsub]; omega) ha) hret2_15 hret2_19
    all_goals rv_closeT

/-- The block loop's head, `k` full blocks left: the next block at `a1`, its bytes left in `s4`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Tail env ret top regs m r M ∧ (r .x20).toNat = 136 * k ∧ 0 < k ∧ k ≤ (regs .x12).toNat / 136 ∧
    (r .x11).toNat = (regs .x11).toNat + 136 * ((regs .x12).toNat / 136 - k)

set_option rv_sym.heap true in
/-- **The block loop**, by `Total.loop` with the blocks left as the measure. -/
theorem loop_ok (C : Ctx env p i L needC Q ret top rest regs m) :
    ∀ k r M, LInv env ret top regs m k r M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 58, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m) fun k r M ⟨hT, h20, hk0, hkq, h11⟩ ih => ?_
  obtain ⟨h2, h8, h18, h9, hr, hM⟩ := hT
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 (And.intro h18 (And.intro h9 hr)))
  rv_introT hR
  rv_symT hp stop [78] with [hL] using [hcpy, hset, hxb, hkf]
  all_goals
    have hM' : MemInv env ret top regs m m2 := by
      have e : (top + 0xfffffffffffffe80#64).toNat + 0x30 ≤ top.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact MemInv.call (by omega) (MemInv.call (by omega) hM hret1_14 e (fun a ha => state_out hroom rfl ha)
        hret1_15 hret1_16) hret2_14 e (fun a ha => state_out hroom rfl ha) hret2_15 hret2_16
    have e20 : (r .x20 + 18446744073709551480#64).toNat = (r .x20).toNat - 136 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have hk1 : k ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [e20]; simp; omega))
    have hdw := hdat.resolve_left (by omega)
    have e11 : (r .x11 + 136#64).toNat = (r .x11).toNat + 136 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ih (k - 1) _ _ (by omega)
      ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hM'⟩, ?h20, by omega, by omega, ?h11⟩
    case h20 => rw [Tactic.rf_get_x20, e20]; omega
    case h11 => rw [Tactic.rf_get_x11, e11]; omega
    all_goals rv_closeT
  · refine tail_ok C ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hM'⟩
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- **`keccak_hash` is total**, with its `0x180`-byte frame and the stack its callees need. -/
theorem total (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {needC : Nat}
    (hcpy : MemcpySpecT env p L.memcpy.idx needC) (hset : MemsetSafeT env p L.memset.idx needC)
    (hxb : XorBlockSafeT env p L.xorBlock.idx needC) (hkf : KeccakFSafeT env p L.keccakF.idx needC) :
    KeccakHashSafeT env p i (0x180 + needC) := by
  rv_autoT hp stop [58, 78] with [hL] using [hcpy, hset, hxb, hkf]
  all_goals
    have F : Fx env needC top regs m := ⟨hpre_10, hpre_3, hpre_9, hpre_6, by rw [← hpre_2]; exact hpre_7,
      by rw [← hpre_2]; exact hpre_8⟩
    have C : Ctx env p i L needC Q ret top rest regs m := ⟨hp, hL, hcpy, hset, hxb, hkf, F, hk⟩
    have hM : MemInv env ret top regs m m1 := MemInv.call (by omega)
      (MemInv.prologue (ret := ret) hpre_4 hpre_5 (by omega)) hret1_14
      (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (fun a ha => state_out' hpre_9 hpre_3 rfl rfl ha)
      hret1_15 hret1_17
    have hfull := full_toNat (regs .x12)
  · have hq := BitVec.lt_def.1 hc
    rw [show (136#64 : Word).toNat = 136 from rfl] at hq
    refine tail_ok C ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hM⟩
    all_goals rfl
  · have hq := BitVec.le_def.1 hc
    rw [show (136#64 : Word).toNat = 136 from rfl] at hq
    refine loop_ok C ((regs .x12).toNat / 136) _ _
      ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hM⟩, ?h20, by omega, le_rfl, ?h11⟩
    case h20 => rw [Tactic.rf_get_x20]; exact hfull
    case h11 => rw [Tactic.rf_get_x11]; omega
    all_goals rfl

end Rv64mc.Proof.Hash.KeccakHashT

/-- info: 'Rv64mc.Proof.Hash.KeccakHashT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Hash.KeccakHashT.total
