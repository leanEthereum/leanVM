module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Common.Finalize
public meta import NativeRustcArm.Code.Common.Finalize

/-!
# `Hasher::finalize`'s blocks, run by the symbolic executor

The symbolic states its proof starts blocks from and the executor's results (`run_*`):
- `entryS`, at the entry (`b0`, ending in `bl memcpy`): region 0 the 384-byte frame below SP;
- `copyS`, after the first `memcpy` (`b1`, `b2`, `b3`, ending in `bl memcpy`): region 0 the
  frame (SP, X29 at its byte 336), region 1 the hasher (X21);
- `padS`, after the second `memcpy` (`b4`'s first three instructions, `b4a`: `PAD_FIRST` XORed
  into the byte after the buffered ones): region 0 that byte, at X21 + X20;
- `xorS`, after them (the rest of `b4`, `b4b`: `PAD_LAST`, the block's lanes XORed into the
  state's, ending in `bl keccak_f`; its writes `finMem`, `findWrite_finMem`): region 0 the frame;
- `outS`, after `keccak_f` (`b5`, the digest copied out, the epilogue): region 0 the frame, region 1
  the output (X19).
-/

namespace NativeRustcArm.Hasher.Finalize

open NativeRustcArm.Sym NativeRustcArm.Common.Finalize

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

/-- `b4`'s first three instructions: `PAD_FIRST`. -/
def b4a : List Directive := b4.take 3
/-- The rest of `b4`. -/
def b4b : List Directive := b4.drop 3

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(384, true)] (.ptr 0 384)

/-- After the first `memcpy`: the frame (region 0) and the hasher (region 1, X21). -/
def copyS : SState := init [(384, true), (344, false)] (.ptr 0 0) [(.X21, .ptr 1 0), (.X29, .ptr 0 336)]

/-- The address `[x21, x20]`. -/
def padAddr : Sym := .bin .add .W64 (.reg .X21) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X20))

/-- After the second `memcpy`: the byte at `[x21, x20]` (region 0). -/
def padS : SState := init [(1, false)] .sp [] (aliases := [(padAddr, (0, 0))])

/-- After `PAD_FIRST`: the frame (region 0). -/
def xorS : SState := init [(384, true)] (.ptr 0 0) [(.X29, .ptr 0 336)]

/-- After `keccak_f`: the frame (region 0) and the output (region 1, X19). -/
def outS : SState := init [(384, true), (32, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- `PAD_LAST`'s write. -/
def padW : Write := ⟨0, 335, 1, .bin .eor .W32 (.load 0 335 1) (.lit 128)⟩

/-- Lane `i < 16` of the state XOR lane `i` of the block. -/
def laneW (i : Nat) : Write := ⟨0, 8 * i, 8, .bin .eor .W64 (.load 0 (8 * i) 8) (.load 0 (200 + 8 * i) 8)⟩

/-- Lane 16: the block's lane holds `PAD_LAST`'s byte. -/
def lane16 : Write := ⟨0, 128, 8, .bin .eor .W64 (.load 0 128 8) (assemble [padW] 0 328 8)⟩

/-- `b4b`'s writes, newest first. -/
def finMem : List Write := lane16 :: ((List.range 16).reverse.map laneW ++ [padW])

/-- The prologue's slots in the frame. -/
def slots : List (Nat × XReg) :=
  [(376, .X19), (368, .X20), (360, .X21), (352, .X28), (344, .X30), (336, .X29)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 copyS
sym_block run_b2 := exec b2 (after b1 copyS)
sym_block run_b3 := exec b3 (after b2 (after b1 copyS))
sym_block run_b4a := exec b4a padS
sym_block run_b4b := exec b4b xorS
sym_block run_b5 := exec b5 outS

public theorem b0_slots : ∀ p ∈ slots, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 336 ≤ w.off ∧ w.off + w.n ≤ 384 := by
  decide +kernel

public theorem b3_mem : ∀ j < 384, findWrite 0 j (after b3 (after b2 (after b1 copyS))).mem =
    if 200 ≤ j ∧ j < 336 then some (.lit 0, (j - 200) % 8) else none := by
  decide +kernel

public theorem b3_mem1 : ∀ w ∈ (after b3 (after b2 (after b1 copyS))).mem,
    w.r = 0 ∧ 200 ≤ w.off ∧ w.off + w.n ≤ 336 := by
  decide +kernel

public theorem b5_out : ∀ j < 32, findWrite 1 j (after b5 outS).mem =
    some (.load 0 (8 * (j / 8)) 8, j % 8) := by
  decide +kernel

public theorem b5_mem : ∀ w ∈ (after b5 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 32 := by
  decide +kernel

public theorem b4b_mem : (after b4b xorS).mem = finMem := by decide +kernel

public theorem finMem_bounds : ∀ w ∈ finMem, w.r = 0 ∧ w.off + w.n ≤ 336 := by decide +kernel

public theorem b4a_mem : (after b4a padS).mem =
    [⟨0, 0, 1, .bin .eor .W32 (.load 0 0 1) (.lit 1)⟩] := by decide +kernel

/-- The write covering byte `j` of the frame after `b4b`. -/
public theorem findWrite_finMem : ∀ j < 384, findWrite 0 j finMem =
    if j < 128 then some ((laneW (j / 8)).v, j % 8)
    else if j < 136 then some (lane16.v, j - 128)
    else if j = 335 then some (padW.v, 0)
    else none := by
  decide +kernel

end NativeRustcArm.Hasher.Finalize
