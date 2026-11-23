module

public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.VerifyLayer
public meta import NativeRustcVmArm.Code.Vm.VerifyLayer

/-!
# `verify_layer`'s blocks, run by the symbolic executor

Region 0 is the 2032-byte frame below the entry's SP (`frS`, SP its base), but in the blocks
that touch only other memory and write nothing (`b4`, `b10`, `b13`, `b18`, `b20`): there the
regions are the elements they load. The other regions: the claim (768 bytes, `b2`, `b15`, `b25`,
`b33`, `b65`, `b66`, through X19, X20 or the frame's word `136`), `KECCAK_RC` (192 bytes, `b17`,
`b19`, the index `11 - step` or `23 - step` bounded), an element of the local equality kernel
(`b53`, `b54`, `b58`, by aliases), the layer's weight written (`b56`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyLayer

@[expose] public section

/-- `KECCAK_RC`'s label. -/
def rcL : Label := NativeRustcVmArm.Vm.Symbols.rodata1Label

/-- `x << 4`. -/
def shl4 (x : Sym) : Sym := .un (.shift .LSL 4) .W64 x

/-- The entry: region 0 the frame below SP. -/
def entryS : SState := init [(2032, true)] (.ptr 0 2032)
/-- Region 0 the frame, SP its base. -/
def frS : SState := init [(2032, true)] (.ptr 0 0)
/-- No regions. -/
def regsS : SState := init [] .sp
/-- The frame and the claim at X19. -/
def claim19S : SState := init [(2032, true), (768, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
/-- The frame and the claim at X20. -/
def claim20S : SState := init [(2032, true), (768, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]
/-- The frame and the claim at the frame's word `136`. -/
def claimFS : SState :=
  init [(2032, true), (768, false)] (.ptr 0 0) [] [] [] [(.load 0 136 8, (1, 0))]
/-- The product's element at X28 + X29. -/
def prodS : SState :=
  init [(16, false)] .sp [] [] [] [(.bin .add .W64 (.reg .X28) (.reg .X29), (0, 0))]
/-- Two masks at X14 - 8, two weights at X13 - 16. -/
def pairS : SState := init [(16, false), (32, false)] .sp [(.X14, .ptr 0 8), (.X13, .ptr 1 16)]
/-- A mask at X9, a weight at X10 - 8. -/
def oneS : SState := init [(8, false), (16, false)] .sp [(.X9, .ptr 0 0), (.X10, .ptr 1 8)]
/-- The frame and `KECCAK_RC`, the index `11 - step`. -/
def rc1S : SState :=
  init [(2032, true), (192, false)] (.ptr 0 0) [] [(rcL, 1)]
    [(.bin .sub .W64 (.lit 11) (.load 0 128 8), 12)]
/-- The frame and `KECCAK_RC` at X0, the index `23 - X1`. -/
def rc2S : SState :=
  init [(2032, true), (192, false)] (.ptr 0 0) [(.X0, .ptr 1 0)] []
    [(.bin .sub .W64 (.lit 23) (.reg .X1), 24)]
/-- Four bit weights at X2 - 56. -/
def bits2S : SState := init [(64, false)] .sp [(.X2, .ptr 0 56)]
/-- Four bit weights at X13 - 56. -/
def bits13S : SState := init [(64, false)] .sp [(.X13, .ptr 0 56)]
/-- The claim's value at X20. -/
def valueS : SState := init [(16, false)] .sp [(.X20, .ptr 0 0)]
/-- The frame and the kernel's element at the frame's word `144` plus `16 (X9 + X8)`. -/
def at3S : SState :=
  init [(2032, true), (16, false)] (.ptr 0 0) [] [] []
    [(.bin .add .W64 (.bin .add .W64 (.load 0 144 8) (shl4 (.reg .X9))) (shl4 (.reg .X8)), (1, 0))]
/-- The frame and the kernel's element at the frame's word `144` plus `16 (X11 + X8)`. -/
def at4S : SState :=
  init [(2032, true), (16, false)] (.ptr 0 0) [] [] []
    [(.bin .add .W64 (.bin .add .W64 (.load 0 144 8) (shl4 (.reg .X11))) (shl4 (.reg .X8)), (1, 0))]
/-- The frame and the kernel's element at the frame's word `96` less 8. -/
def atjS : SState :=
  init [(2032, true), (16, false)] (.ptr 0 0) [] [] [] [(.load 0 96 8, (1, 8))]
/-- The frame and the layer's weight at X29 (its low word) and X20 (its high word). -/
def storeS : SState :=
  init [(2032, true), (16, false)] (.ptr 0 0) [(.X29, .ptr 1 0), (.X20, .ptr 1 8)]

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 frS
sym_block e2 := exec b2 claim19S
sym_block e3 := exec b3 frS
sym_block e4 := exec b4 prodS
sym_block e5 := exec b5 frS
sym_block e6 := exec b6 frS
sym_block e7 := exec b7 frS
sym_block e8 := exec b8 frS
sym_block e9 := exec b9 frS
sym_block e10 := exec b10 pairS
sym_block e11 := exec b11 frS
sym_block e12 := exec b12 frS
sym_block e13 := exec b13 oneS
sym_block e14 := exec b14 frS
sym_block e15 := exec b15 claimFS
sym_block e16 := exec b16 frS
sym_block e17 := exec b17 rc1S
sym_block e18 := exec b18 bits2S
sym_block e19 := exec b19 rc2S
sym_block e20 := exec b20 bits13S
sym_block e21 := exec b21 frS
sym_block e22 := exec b22 frS
sym_block e23 := exec b23 frS
sym_block e24 := exec b24 frS
sym_block e25 := exec b25 claimFS
sym_block e26 := exec b26 valueS
sym_block e27 := exec b27 frS
sym_block e28 := exec b28 frS
sym_block e29 := exec b29 frS
sym_block e30 := exec b30 frS
sym_block e31 := exec b31 frS
sym_block e32 := exec b32 frS
sym_block e33 := exec b33 claim20S
sym_block e34 := exec b34 frS
sym_block e35 := exec b35 frS
sym_block e36 := exec b36 frS
sym_block e37 := exec b37 frS
sym_block e38 := exec b38 frS
sym_block e39 := exec b39 frS
sym_block e40 := exec b40 frS
sym_block e41 := exec b41 frS
sym_block e42 := exec b42 frS
sym_block e43 := exec b43 frS
sym_block e44 := exec b44 frS
sym_block e45 := exec b45 frS
sym_block e46 := exec b46 frS
sym_block e47 := exec b47 frS
sym_block e48 := exec b48 frS
sym_block e49 := exec b49 frS
sym_block e50 := exec b50 frS
sym_block e51 := exec b51 frS
sym_block e52 := exec b52 frS
sym_block e53 := exec b53 at3S
sym_block e54 := exec b54 atjS
sym_block e55 := exec b55 frS
sym_block e56 := exec b56 storeS
sym_block e57 := exec b57 frS
sym_block e58 := exec b58 at4S
sym_block e59 := exec b59 frS
sym_block e60 := exec b60 frS
sym_block e61 := exec b61 frS
sym_block e62 := exec b62 frS
sym_block e63 := exec b63 frS
sym_block e64 := exec b64 frS
sym_block e65 := exec b65 claimFS
sym_block e66 := exec b66 claim19S
sym_block e67 := exec b67 frS
sym_block e68 := exec b68 frS
sym_block e69 := exec b69 frS
sym_block e70 := exec b70 frS

end NativeRustcVmArm.KeccakGkr.VerifyLayer
