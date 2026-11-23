module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Update.Names
public import NativeRustcX64.Code.Xmss.XmssVerify.Names

public import NativeRustcX64.XmssVerify.Top

/-!
# `xmss_verify`: a turn of the loop over the top layer's path (x86-64)

Block 19 (the head, `.LXmssVerify_7`): the current node in RCX and RDX and the path node at R14
stored at `88` in the order bit `z` of the key index says (`R12 - 1 = z`), the address at `24`
(the layer's bit `1 << 23` in its high field), `memset` of the hasher at `184`. Blocks 20 to 24:
the node's hash (`hashNode`, the copy's pointer in RBP). Block 25: its first 16 bytes into RCX
and RDX, R12 and R14 on, back to block 19 until `R12 = 17`.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

/-- `R12 - 1`. -/
def r12m1 : Sym := .bin .add .W64 (.reg .r12) (.lit 18446744073709551615)

/-- The address's high byte of a top node: bits 16 to 23 of `R12 | 1 << 23`. -/
def hiB1 : Sym := .un .trunc .W8 (.bin .shr .W32 (.bin .or .W32 (.un .trunc .W32 (.reg .r12))
  (.lit 8388608)) (.lit 16))

end

public section

theorem st19_regs : (after b19 st19).reg .rdi = some (.ptr 0 184) ∧
    (after b19 st19).reg .rsi = some (.lit 0) ∧ (after b19 st19).reg .rdx = some (.lit 344) ∧
    (after b19 st19).reg .rsp = some (.ptr 0 16) ∧ (after b19 st19).reg .rbp = some (.ptr 0 608) ∧
    (after b19 st19).reg .r13 = some (.ptr 0 120) ∧ (after b19 st19).reg .r14 = some (.ptr 1 0) ∧
    (after b19 st19).reg .r15 = some (.ptr 0 184) ∧ (after b19 st19).reg .rbx = some (.reg .rbx) ∧
    (after b19 st19).reg .r12 = some (.reg .r12) ∧
    writesBelow (after b19 st19) [(0, 136)] = true ∧
    (∀ w ∈ (after b19 st19).mem, w.r = 0 ∧ (w.off + w.n ≤ 40 ∨ 88 ≤ w.off)) := by
  decide +kernel

theorem st19_children :
    (∀ t < 8, findWrite 0 (88 + t) (after b19 st19).mem =
      some (.ite (bitC r12m1) (.reg .rcx) (.load 1 0 8), t)) ∧
    (∀ t < 8, findWrite 0 (96 + t) (after b19 st19).mem =
      some (.ite (bitC r12m1) (.reg .rdx) (.load 1 8 8), t)) ∧
    (∀ t < 8, findWrite 0 (104 + t) (after b19 st19).mem =
      some (.ite (bitC r12m1) (.load 1 0 8) (.reg .rcx), t)) ∧
    (∀ t < 8, findWrite 0 (112 + t) (after b19 st19).mem =
      some (.ite (bitC r12m1) (.load 1 8 8) (.reg .rdx), t)) := by
  decide +kernel

theorem st19_addr :
    (∀ t < 4, findWrite 0 (24 + t) (after b19 st19).mem = some (loW (.reg .r12), t)) ∧
    (∀ t < 2, findWrite 0 (28 + t) (after b19 st19).mem = some (.un .trunc .W16 (.reg .r12), t)) ∧
    (∀ t < 1, findWrite 0 (30 + t) (after b19 st19).mem = some (hiB1, t)) ∧
    (∀ t < 1, findWrite 0 (31 + t) (after b19 st19).mem = some (.lit 3, t)) ∧
    (∀ t < 8, findWrite 0 (32 + t) (after b19 st19).mem = some (.lit 0, t)) := by
  decide +kernel

theorem run_b20' : exec b20 stH = some (after b20 stH, .call NativeRustcX64.Common.Update.entryLabel) := by
  rw [after_eq run_b20]; exact run_b20

theorem run_b21' : exec b21 stH = some (after b21 stH, .call NativeRustcX64.Common.Update.entryLabel) := by
  rw [after_eq run_b21]; exact run_b21

theorem run_b22' : exec b22 stH2 = some (after b22 stH2, .call NativeRustcX64.Common.Memcpy.entryLabel) := by
  rw [after_eq run_b22]; exact run_b22

theorem run_b23' : exec b23 stH2 = some (after b23 stH2, .call NativeRustcX64.Common.Update.entryLabel) := by
  rw [after_eq run_b23]; exact run_b23

theorem run_b24' : exec b24 stH2 = some (after b24 stH2, .call NativeRustcX64.Common.Finalize.entryLabel) := by
  rw [after_eq run_b24]; exact run_b24

theorem f20 : (writesBelow (after b20 stH) [(0, 24)] = true ∧ keepsBut .rax stH (after b20 stH) = true ∧
      (after b20 stH).reg .rsp = some (.ptr 0 16)) ∧ (after b20 stH).reg .rdi = some (.ptr 0 184) ∧
    (after b20 stH).reg .rsi = some (.ptr 0 56) ∧ (after b20 stH).reg .rdx = some (.lit 16) := by
  decide +kernel

theorem f21 : (writesBelow (after b21 stH) [(0, 24)] = true ∧ keepsBut .rax stH (after b21 stH) = true ∧
      (after b21 stH).reg .rsp = some (.ptr 0 16)) ∧ (after b21 stH).reg .rdi = some (.ptr 0 184) ∧
    (after b21 stH).reg .rsi = some (.ptr 0 24) ∧ (after b21 stH).reg .rdx = some (.lit 16) := by
  decide +kernel

theorem f22 : (writesBelow (after b22 stH2) [(0, 24)] = true ∧
      keepsBut .rax stH2 (after b22 stH2) = true ∧ (after b22 stH2).reg .rsp = some (.ptr 0 16)) ∧
    (after b22 stH2).reg .rdi = some (.ptr 0 608) ∧ (after b22 stH2).reg .rsi = some (.ptr 0 184) ∧
    (after b22 stH2).reg .rdx = some (.lit 344) ∧ (after b22 stH2).reg .r15 = some (.ptr 0 184) ∧
    (after b22 stH2).reg .rbp = some (.ptr 0 608) := by
  decide +kernel

theorem f23 : (writesBelow (after b23 stH2) [(0, 24)] = true ∧
      keepsBut .rax stH2 (after b23 stH2) = true ∧ (after b23 stH2).reg .rsp = some (.ptr 0 16)) ∧
    (after b23 stH2).reg .rdi = some (.ptr 0 608) ∧ (after b23 stH2).reg .rsi = some (.ptr 0 88) ∧
    (after b23 stH2).reg .rdx = some (.lit 32) ∧ (after b23 stH2).reg .rbp = some (.ptr 0 608) := by
  decide +kernel

theorem f24 : (writesBelow (after b24 stH2) [(0, 24)] = true ∧
      keepsBut .rax stH2 (after b24 stH2) = true ∧ (after b24 stH2).reg .rsp = some (.ptr 0 16)) ∧
    (after b24 stH2).reg .rdi = some (.ptr 0 184) ∧ (after b24 stH2).reg .rsi = some (.ptr 0 608) := by
  decide +kernel

/-- Another turn: `R12 + 1 ≠ 17`. -/
theorem run_b25' : exec b25 (stF []) = some (after b25 (stF []),
    .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.reg .r12) (.lit 1)) (.lit 17))) NativeRustcX64.Xmss.XmssVerify.label_7) := by
  rw [after_eq run_b25]; exact run_b25

theorem st25_facts : (after b25 (stF [])).reg .rsp = some (.ptr 0 24) ∧
    (after b25 (stF [])).reg .rcx = some (.load 0 184 8) ∧
    (after b25 (stF [])).reg .rdx = some (.load 0 192 8) ∧
    (after b25 (stF [])).reg .r12 = some (.bin .add .W64 (.reg .r12) (.lit 1)) ∧
    (after b25 (stF [])).reg .r14 = some (.bin .add .W64 (.lit 16) (.reg .r14)) ∧
    (∀ r ∈ [Reg64.rbx, .rbp, .r13, .r15], (after b25 (stF [])).reg r = some (.reg r)) ∧
    (after b25 (stF [])).mem = [] := by
  decide +kernel

/-- **A hash's first 16 bytes** at `184` loaded into two registers. -/
theorem regs16 {m₀ m : MachineData} {N : Nat} {rest : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {ret : BitVec 64} {X : List UInt8} (hX : X.length = 32)
    (hb : BytesAt m.dmem (ad m₀ (fr + 184)) X) :
    regBytes ((Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret).load 0 184 8) ++
      regBytes ((Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret).load 0 192 8) = X.take 16 := by
  have hh := halves hb
  have l1 : (X.take 8).length = 8 := by simp [hX]
  have l2 : ((X.drop 8).take 8).length = 8 := by simp [hX]
  have h2 : BytesAt m.dmem (ad m₀ (fr + 192)) ((X.drop 8).take 8) := by
    rw [show fr + 192 = fr + 184 + 8 by omega]
    exact hh.2
  rw [regBytes_frame l1 hh.1, regBytes_frame l2 h2, ← List.take_add]

/-! ## Values -/

variable [Labels] {env : Env}

/-- `R12 - 1` at level `z`. -/
theorem r12m1_eval {z : Nat} (h : env.regs .r12 = BitVec.ofNat 64 (z + 1)) :
    r12m1.eval env = BitVec.ofNat 64 z := by
  simp only [r12m1, Sym.eval, BinOp.apply, low_W64, ext_W64, h, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- The high field's bytes of a top node's address. -/
theorem hi1_eval {z : Nat} (hz : z < 16) (h : (Sym.reg .r12).eval env = BitVec.ofNat 64 (z + 1)) :
    [UInt8.ofNat ((Sym.un .trunc .W16 (.reg .r12)).eval env).toNat,
      UInt8.ofNat (((Sym.un .trunc .W16 (.reg .r12)).eval env).toNat / 256),
      UInt8.ofNat (hiB1.eval env).toNat] = (u32Bytes (layerHi 1 (z + 1).toUInt32)).take 3 := by
  have e1 : ((Sym.un .trunc .W16 (.reg .r12)).eval env).toNat = (z + 1) % 2 ^ 16 := by
    show (UnOp.apply .trunc .W16 ((Sym.reg .r12).eval env)).toNat = _
    rw [trunc_toNat, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z + 1 < 2 ^ 64 by omega)]
  have e2 : (hiB1.eval env).toNat = ((z + 1) % 2 ^ 32 ||| 8388608) % 2 ^ 32 / 2 ^ 16 % 2 ^ 8 := by
    show (UnOp.apply .trunc .W8 (BinOp.apply .shr .W32 (BinOp.apply .or .W32
      (UnOp.apply .trunc .W32 ((Sym.reg .r12).eval env)) (BitVec.ofNat 64 8388608))
      (BitVec.ofNat 64 16))).toNat = _
    rw [trunc_toNat, shr16_toNat, or_toNat _ _ (by decide), trunc_toNat, h, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show z + 1 < 2 ^ 64 by omega)]
    show ((z + 1) % 2 ^ 32 % 2 ^ 32 ||| 8388608) % 2 ^ 32 / 2 ^ 16 % 2 ^ 8 = _
    rw [Nat.mod_mod]
  rw [e1, e2]
  exact hiBytes_top z hz

omit [Labels] in
theorem beq17 {z : Nat} (hz : z < 16) :
    (BitVec.ofNat 64 (z + 1 + 1) == BitVec.ofNat 64 17) = decide (z + 1 = 16) := by
  by_cases h : z + 1 = 16
  · rw [h]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    omega

end

end NativeRustcX64.Xmss.XmssVerify
