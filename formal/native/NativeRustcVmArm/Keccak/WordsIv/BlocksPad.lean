module

public import NativeRustcVmArm.Keccak.WordsIv.Blocks
public meta import NativeRustcVmArm.Keccak.WordsIv.Blocks

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`'s padding block, run by the symbolic executor

The padding block (`b108`) XORs X0 (lane 16's word) into lane 16, `PAD_FIRST` into the lane at
byte `(len % 136) & !7` of the state and `PAD_LAST` into lane 16, then calls `keccak_f`. It runs
as `pad t` for the padded lane `t < 17`, from `startPad t`: the padded lane's address an alias of
region 0 at `8 + 8 t`.
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym Vm.Keccak256WordsOfFiatShamirIv

set_option Elab.async false

@[expose] public section

/-- `len / 136`, by the high word of a product. -/
def nbS : Sym :=
  .un (.ubfm 7 63) .W64 (.bin .umulh .W64 (.reg .X20) (.lit 17361641481138401521))

/-- `len % 136`. -/
def remS : Sym := .bin .sub .W64 (.reg .X20) (.bin .mul .W64 nbS (.lit 136))

/-- The byte offset of the padded lane in the state: `(len % 136) & !7`. -/
def padIdx : Sym := .bin .and .W64 remS (.lit 248)

/-- The padding at lane `t`: the padded lane's address an alias of region 0 at `8 + 8 t`. -/
def startPad (t : Nat) : SState :=
  init [(288, true)] (.ptr 0 0) [] [] []
    [(.bin .add .W64 (.ptr 0 8) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 padIdx), 0, 8 + 8 * t)]

end

sym_block pad0 := exec b108 (startPad 0)
sym_block pad1 := exec b108 (startPad 1)
sym_block pad2 := exec b108 (startPad 2)
sym_block pad3 := exec b108 (startPad 3)
sym_block pad4 := exec b108 (startPad 4)
sym_block pad5 := exec b108 (startPad 5)
sym_block pad6 := exec b108 (startPad 6)
sym_block pad7 := exec b108 (startPad 7)
sym_block pad8 := exec b108 (startPad 8)
sym_block pad9 := exec b108 (startPad 9)
sym_block pad10 := exec b108 (startPad 10)
sym_block pad11 := exec b108 (startPad 11)
sym_block pad12 := exec b108 (startPad 12)
sym_block pad13 := exec b108 (startPad 13)
sym_block pad14 := exec b108 (startPad 14)
sym_block pad15 := exec b108 (startPad 15)
sym_block pad16 := exec b108 (startPad 16)

end NativeRustcVmArm.WordsIv
