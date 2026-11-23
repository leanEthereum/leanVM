module

public import NativeRustcX64.Code.Xmss.XmssVerify.Names

public import NativeRustcX64.XmssVerify.BottomRun
public import NativeRustcX64.XmssVerify.Tree0Run

/-!
# `xmss_verify`: the top layer's one-time leaf (x86-64)

Block 16: `wots_leaf` of the top layer (its output at `184`, the message the bottom root at
`592`, the key index the leaf index's high half from `80`, the randomizer and the chain values
passed on the stack); block 17: to the failure (block 27) if its tag is not `1`; block 18: the
leaf into RCX and RDX, to the loop over the top layer's path (`TreeAt1` at level `0`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

/-- The bottom layer's root from its leaf `leaf`. -/
def root0 (w : Nat → UInt64) (leaf : List UInt8) : List UInt8 :=
  pf (pp w) 0 (li w).toNat (bottomL w).path leaf 16

/-- The top layer's one-time leaf, its message the bottom root `r0`. -/
def leaf1 (w : Nat → UInt64) (r0 : List UInt8) : Option (List UInt8 × List UInt8) :=
  wotsLeaf (pp w) 1 (li1 w) r0 (topL w).randomizer (topL w).chainValues

/-- At the head of the loop over the top layer's path (block 19), before level `z`, from the
leaf `leaf`: R12 `z + 1`, the current node in RCX and RDX, R14 the path's node `z`. -/
structure TreeAt1 (w : Nat → UInt64) (m₀ : MachineData) (leaf : List UInt8) (m : MachineData)
    (z : Nat) : Prop where
  common : Common m₀ m
  rsp : rspOf m = ad m₀ (fr + 24)
  r12 : reg m .r12 = BitVec.ofNat 64 (z + 1)
  rbx : reg m .rbx = BitVec.ofNat 64 (li1 w).toNat
  r13 : reg m .r13 = ad m₀ (fr + 120)
  r14 : reg m .r14 = ad m₀ (fr + 4556 + 16 * z)
  rbp : reg m .rbp = ad m₀ (fr + 608)
  r15 : reg m .r15 = ad m₀ (fr + 184)
  pk : BytesAt m.dmem (ad m₀ (fr + 40)) (pkB w)
  top : BytesAt m.dmem (ad m₀ (fr + 4556)) (topL w).memBytes
  cur : regBytes (reg m .rcx) ++ regBytes (reg m .rdx) =
    pf (pp w) 1 (li1 w).toNat (topL w).path leaf z

end

public section

/-- The bottom layer's root. -/
theorem layerRoot0 {w : Nat → UInt64} {x leaf : List UInt8} (h : leaf0 w = some (x, leaf)) :
    layerRoot (pp w) 0 (li w) (msgB w) (bottomL w) = some (x, root0 w leaf) := by
  unfold layerRoot
  rw [show wotsLeaf (pp w) 0 (li w) (msgB w) (bottomL w).randomizer (bottomL w).chainValues =
    some (x, leaf) from h]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  exact pathFold_eq _ _ _ _ _ length_path

/-- The top layer's root. -/
theorem layerRoot1 {w : Nat → UInt64} {r0 x leaf : List UInt8} (h : leaf1 w r0 = some (x, leaf)) :
    layerRoot (pp w) 1 (li1 w) r0 (topL w) =
      some (x, pf (pp w) 1 (li1 w).toNat (topL w).path leaf 16) := by
  unfold layerRoot
  rw [show wotsLeaf (pp w) 1 (li1 w) r0 (topL w).randomizer (topL w).chainValues =
    some (x, leaf) from h]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  exact pathFold_eq _ _ _ _ _ length_path

theorem layerRoot1_none {w : Nat → UInt64} {r0 : List UInt8} (h : leaf1 w r0 = none) :
    layerRoot (pp w) 1 (li1 w) r0 (topL w) = none := by
  unfold layerRoot
  rw [show wotsLeaf (pp w) 1 (li1 w) r0 (topL w).randomizer (topL w).chainValues = none from h]

/-- The top layer's key index: bits 16 to 31 of the leaf index. -/
theorem li1_toNat (w : Nat → UInt64) : (li1 w).toNat = (w 8).toNat % 2 ^ 32 / 2 ^ 16 := by
  rw [li1, layerIndex, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64,
    li_toNat]
  show ((w 8).toNat % 2 ^ 32) >>> 16 % 2 ^ 32 = _
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem st16_facts : (after b16 (stF [])).reg .rdi = some (.ptr 0 184) ∧
    (after b16 (stF [])).reg .rsi = some (.ptr 0 56) ∧
    (after b16 (stF [])).reg .rdx = some (.lit 1) ∧
    (after b16 (stF [])).reg .rcx = some (.bin .shr .W32 (.load 0 80 8) (.lit 16)) ∧
    (after b16 (stF [])).reg .rbx = some (.bin .shr .W32 (.load 0 80 8) (.lit 16)) ∧
    (after b16 (stF [])).reg .r8 = some (.ptr 0 592) ∧
    (after b16 (stF [])).reg .r9 = some (.lit 16) ∧
    (after b16 (stF [])).reg .rsp = some (.ptr 0 0) ∧
    (after b16 (stF [])).reg .r12 = some (.lit 1) ∧
    writesBelow (after b16 (stF [])) [(0, 24)] = true ∧
    (∀ u < 8, findWrite 0 (8 + u) (after b16 (stF [])).mem = some (.ptr 0 5740, u)) ∧
    (∀ u < 8, findWrite 0 (16 + u) (after b16 (stF [])).mem = some (.ptr 0 4812, u)) := by
  decide +kernel

theorem run_b17' : exec b17 stR = some (after b17 stR,
    .cond (.not (.cmp .eq .W8 (.load 0 184 1) (.lit 1))) NativeRustcX64.Xmss.XmssVerify.label_10) := by
  rw [run_b17]
  rfl

theorem st17_facts : (after b17 stR).reg .rsp = some (.ptr 0 24) ∧ (after b17 stR).mem = [] ∧
    (∀ r ∈ [Reg64.rbx, .r12], (after b17 stR).reg r = some (.reg r)) := by
  decide +kernel

theorem st18_facts : (after b18 (stF [])).reg .rcx = some (.load 0 243 8) ∧
    (after b18 (stF [])).reg .rdx = some (.load 0 251 8) ∧
    (after b18 (stF [])).reg .rbx = some (.un .trunc .W32 (.reg .rbx)) ∧
    (after b18 (stF [])).reg .rsp = some (.ptr 0 24) ∧
    (after b18 (stF [])).reg .rbp = some (.ptr 0 608) ∧
    (after b18 (stF [])).reg .r13 = some (.ptr 0 120) ∧
    (after b18 (stF [])).reg .r14 = some (.ptr 0 4556) ∧
    (after b18 (stF [])).reg .r15 = some (.ptr 0 184) ∧
    (after b18 (stF [])).reg .r12 = some (.reg .r12) ∧ (after b18 (stF [])).mem = [] := by
  decide +kernel

end

end NativeRustcX64.Xmss.XmssVerify
