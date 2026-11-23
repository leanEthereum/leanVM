module

public import NativeRustcX64.Code.Xmss.XmssVerify.Names

public import NativeRustcX64.XmssVerify.ParseRun
public import NativeRustcX64.XmssVerify.Layer

/-!
# `xmss_verify`: the bottom layer's one-time leaf (x86-64)

Block 5: `wots_leaf` of the bottom layer (its output at `184`, the randomizer and the chain values
passed on the stack); block 6: to the failure (block 27) if its tag is not `1` (`FailAt`, the
model's `xmssVerify` false); block 7: the codeword and the leaf copied to `534` (`memcpy`);
block 8: to the loop over the bottom layer's path (`TreeAt0` at level `0`, the leaf at `592`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

/-- At the failure (block 27): the model's verdict is `false`. -/
structure FailAt (w : Nat → UInt64) (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  rsp : rspOf m = ad m₀ (fr + 24)
  bad : xmssVerify w = false

/-- The bottom layer's one-time leaf. -/
def leaf0 (w : Nat → UInt64) : Option (List UInt8 × List UInt8) :=
  wotsLeaf (pp w) 0 (li w) (msgB w) (bottomL w).randomizer (bottomL w).chainValues

/-- At the head of the loop over the bottom layer's path (block 9), before level `z`, from the
leaf `leaf`. -/
structure TreeAt0 (w : Nat → UInt64) (m₀ : MachineData) (leaf : List UInt8) (m : MachineData)
    (z : Nat) : Prop where
  common : Common m₀ m
  rsp : rspOf m = ad m₀ (fr + 24)
  rbp : reg m .rbp = BitVec.ofNat 64 z
  rbx : reg m .rbx = u32W (w 8)
  r12 : reg m .r12 = ad m₀ (fr + 3356 + 16 * z)
  r15 : reg m .r15 = ad m₀ (fr + 184)
  pk : BytesAt m.dmem (ad m₀ (fr + 40)) (pkB w)
  w8 : BytesAt m.dmem (ad m₀ (fr + 80)) (regBytes (w 8).toBitVec)
  bottom : BytesAt m.dmem (ad m₀ (fr + 3356)) (bottomL w).memBytes
  top : BytesAt m.dmem (ad m₀ (fr + 4556)) (topL w).memBytes
  cur : BytesAt m.dmem (ad m₀ (fr + 592)) (pf (pp w) 0 (li w).toNat (bottomL w).path leaf z)

end

public section

theorem st5_facts : (after b5 st5).reg .rdi = some (.ptr 0 184) ∧
    (after b5 st5).reg .rsi = some (.ptr 0 56) ∧ (after b5 st5).reg .rdx = some (.lit 0) ∧
    (after b5 st5).reg .rcx = some (.un .trunc .W32 (.reg .r13)) ∧
    (after b5 st5).reg .r8 = some (.ptr 0 152) ∧ (after b5 st5).reg .r9 = some (.lit 32) ∧
    (after b5 st5).reg .rsp = some (.ptr 0 0) ∧
    (∀ r ∈ [Reg64.r12, .r13, .rbp], (after b5 st5).reg r = some (.reg r)) ∧
    writesBelow (after b5 st5) [(0, 5760)] = true ∧
    (∀ u < 8, findWrite 0 (8 + u) (after b5 st5).mem = some (.ptr 0 4540, u)) ∧
    (∀ u < 8, findWrite 0 (16 + u) (after b5 st5).mem = some (.ptr 0 3612, u)) ∧
    writesBelow (after b5 st5) [(0, 24), (0, 5760)] = true := by decide +kernel

theorem st5_low : ∀ w ∈ (after b5 st5).mem, w.r = 0 ∧ (w.off + w.n ≤ 24 ∨ 5756 ≤ w.off) := by
  decide +kernel

theorem run_b6' : exec b6 stR = some (after b6 stR,
    .cond (.not (.cmp .eq .W8 (.load 0 184 1) (.lit 1))) NativeRustcX64.Xmss.XmssVerify.label_10) := by
  rw [run_b6]
  rfl

theorem st6_facts : (after b6 stR).reg .rsp = some (.ptr 0 24) ∧ (after b6 stR).mem = [] ∧
    (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r15], (after b6 stR).reg r = some (.reg r)) := by
  decide +kernel

theorem st7_facts : (after b7 (stF [])).reg .rdi = some (.ptr 0 534) ∧
    (after b7 (stF [])).reg .rsi = some (.ptr 0 185) ∧
    (after b7 (stF [])).reg .rdx = some (.lit 74) ∧
    (after b7 (stF [])).reg .rsp = some (.ptr 0 16) ∧
    (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r15], (after b7 (stF [])).reg r = some (.reg r)) ∧
    (∀ u < 8, findWrite 0 (80 + u) (after b7 (stF [])).mem = some (.reg .r13, u)) ∧
    writesBelow (after b7 (stF [])) [(0, 88)] = true ∧
    (∀ w ∈ (after b7 (stF [])).mem, w.r = 0 ∧ (w.off + w.n ≤ 24 ∨ 80 ≤ w.off)) := by
  decide +kernel

theorem st8_facts : (after b8 (stF [])).reg .rbx = some (.reg .rbp) ∧
    (after b8 (stF [])).reg .rbp = some (.lit 0) ∧
    (after b8 (stF [])).reg .r15 = some (.ptr 0 184) ∧
    (after b8 (stF [])).reg .rsp = some (.ptr 0 24) ∧
    (after b8 (stF [])).reg .r12 = some (.reg .r12) ∧ (after b8 (stF [])).mem = [] := by
  decide +kernel

end

end NativeRustcX64.Xmss.XmssVerify
