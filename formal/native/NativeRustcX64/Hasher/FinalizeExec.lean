module

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Common.Finalize
public meta import NativeRustcX64.Code.Common.Finalize

/-!
# `Hasher::finalize`'s blocks, run by the symbolic executor (x86-64)

The frame: the 392 bytes from 384 below the entry's RSP (`frAt`): the return-address slot of its
calls (offset 0), the final block (16 to 151), the state's copy (152 to 351), the pushed
registers (352 to 383) and its return address (384). After the prologue RSP is the frame's
offset 8.

The symbolic states its proof starts blocks from and the executor's results (`run_*`):
- `entryS`, at the entry (`b0`, ending in an indirect `memcpy` call): region 0 the frame
  (RSP at 384), region 1 the hasher, region 2 the loader's `memcpy` slot;
- `copyS`, after the first `memcpy` (`b1`, `b2`, `b3`, ending in an indirect `memset` call):
  region 0 the frame, region 1 the hasher (R15), region 2 the loader's `memset` slot;
- `setS`, after `memset` (`b4`, ending in an indirect `memcpy` call): likewise with the
  `memcpy` slot, R15 the hasher's buffer;
- `padS`, after the second `memcpy` (`b5`'s first instruction, `b5a`: `PAD_FIRST` XORed into the
  byte after the buffered ones): region 0 that byte, at RSP + R14 + 8;
- `xorS`, after it (the rest of `b5`, `b5b`: `PAD_LAST`, the block's lanes XORed into the state's,
  ending in `callq keccak_f`; its writes `finMem`, `findWrite_finMem`): region 0 the frame;
- `outS`, after `keccak_f` (`b6`: the digest copied out, the epilogue, `retq`): region 0 the frame,
  region 1 the output (RBX).
-/

namespace NativeRustcX64.Hasher.Finalize

open NativeRustcX64.Sym NativeRustcX64.Common.Finalize

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

/-- `b5`'s first instruction: `PAD_FIRST`. -/
def b5a : List Directive := b5.take 1
/-- The rest of `b5`. -/
def b5b : List Directive := b5.drop 1

/-- The loader's slot description is knowledge, not a write by this function. -/
def knownGot (l : Label) : List Write := [⟨2, 0, 8, .label l⟩]

/-- At the entry. -/
def entryS : SState :=
  (init [392, 344, 8] [(.rsp, .ptr 0 384)]
    (aliases := [(.gotSlot "memcpy", 2, 0)])).withKnownBytes 2 0 8 (.label "memcpy")

/-- After the first `memcpy`. -/
def copyS : SState :=
  (init [392, 344, 8] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]
    (aliases := [(.gotSlot "memset", 2, 0)])).withKnownBytes 2 0 8 (.label "memset")

/-- After `memset`. -/
def setS : SState :=
  (init [392, 344, 8] [(.rsp, .ptr 0 8), (.r12, .ptr 0 16), (.r15, .ptr 1 200)]
    (aliases := [(.gotSlot "memcpy", 2, 0)])).withKnownBytes 2 0 8 (.label "memcpy")

/-- The address `8(%rsp,%r14)`. -/
def padAddr : Sym := .bin .add .W64 (.bin .add .W64 (.reg .rsp) (.reg .r14)) (.lit 8)

/-- After the second `memcpy`: the byte at `8(%rsp,%r14)` (region 0). -/
def padS : SState := init [1] [] (aliases := [(padAddr, (0, 0))])

/-- After `PAD_FIRST`. -/
def xorS : SState := init [392] [(.rsp, .ptr 0 8)]

/-- After `keccak_f`. -/
def outS : SState := init [392, 32] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- `PAD_LAST`'s write. -/
def padW : Write := ⟨0, 151, 1, .bin .xor .W8 (.load 0 151 1) (.lit 18446744073709551488)⟩

/-- Lane `i < 16` of the state XOR lane `i` of the block. -/
def laneW (i : Nat) : Write :=
  ⟨0, 152 + 8 * i, 8, .bin .xor .W64 (.load 0 (152 + 8 * i) 8) (.load 0 (16 + 8 * i) 8)⟩

/-- Lane 16: the block's lane holds `PAD_LAST`'s byte. -/
def lane16 : Write := ⟨0, 280, 8, .bin .xor .W64 (.load 0 280 8) (assemble [padW] 0 144 8)⟩

/-- `b5b`'s writes, newest first: the return address of `callq keccak_f`, the lanes, `PAD_LAST`. -/
def finMem : List Write :=
  ⟨0, 0, 8, .retAddr⟩ :: lane16 :: ((List.range 16).reverse.map laneW ++ [padW])

/-- The prologue's slots in the frame. -/
def slots : List (Nat × Reg64) := [(352, .rbx), (360, .r12), (368, .r14), (376, .r15)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 copyS
sym_block run_b2 := exec b2 (after b1 copyS)
sym_block run_b3 := exec b3 (after b2 (after b1 copyS))
sym_block run_b4 := exec b4 setS
sym_block run_b5a := exec b5a padS
sym_block run_b5b := exec b5b xorS
sym_block run_b6 := exec b6 outS

public theorem b0_slots : ∀ p ∈ slots, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 384 := by
  decide +kernel

public theorem b3_mem : (after b3 (after b2 (after b1 copyS))).mem = [⟨0, 0, 8, .retAddr⟩] := by
  decide +kernel

public theorem b4_mem : (after b4 setS).mem = [⟨0, 0, 8, .retAddr⟩] := by
  decide +kernel

public theorem b5a_mem : (after b5a padS).mem =
    [⟨0, 0, 1, .bin .xor .W8 (.load 0 0 1) (.lit 1)⟩] := by decide +kernel

public theorem b5b_mem : (after b5b xorS).mem = finMem := by decide +kernel

public theorem finMem_bounds : ∀ w ∈ finMem, w.r = 0 ∧ w.off + w.n ≤ 352 := by decide +kernel

/-- The write covering byte `j` of the state after `b5b`. -/
public theorem findWrite_finMem : ∀ j < 200, findWrite 0 (152 + j) finMem =
    if j < 128 then some ((laneW (j / 8)).v, j % 8)
    else if j < 136 then some (lane16.v, j - 128)
    else none := by
  decide +kernel

public theorem b6_out : ∀ j < 32, findWrite 1 j (after b6 outS).mem =
    some (.load 0 (152 + 8 * (j / 8)) 8, j % 8) := by
  decide +kernel

public theorem b6_mem : ∀ w ∈ (after b6 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 32 := by
  decide +kernel


end NativeRustcX64.Hasher.Finalize
