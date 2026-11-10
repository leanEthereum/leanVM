import Rv64Verifier.Proofs.Hash.Lanes
import Rv64Verifier.Proofs.Hash.Contracts
import Rv64Verifier.Blocks.F5

/-!
# `keccak_f`'s blocks against the round's lanes

The kernel checks of `Proofs/Hash/KeccakF.lean`: at the loop head (`0x800042e4`) lane `j` is
`hd j`, a register or a stack slot; θ (`b800042e4`) writes `thetaE hd` to the lanes; one iteration
of the ρ and π loop (`0x80004528`) starts from a symbolic state in which `a1`, the pointer into
`KECCAK_RHO`'s `u32`s, is a constant (`piX`, `piSigma`), so that its load is a doubleword's half;
χ and ι (`0x80004564` to the loop's branch, `chiX`) write `outE` to the lanes and the loop head's
registers and slots.
-/

namespace Rv64Verifier.Hash.KeccakF
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Blocks.F5 Rv64Verifier.Contracts Rv64Verifier.Model

def cfg : Config := { noAlias := true }

/-- The stack slot `sp + off`, as a load. -/
def slot (off : Nat) : E := .ld (.bin .add (.reg .x2) (.c (BitVec.ofNat 64 off)))

def key (r : Reg) (off : Nat) : Addr := ⟨some (.reg r), BitVec.ofNat 64 off⟩

/-- Where the loop head holds the lanes. -/
def headE : List E :=
  [.reg .x12, slot 104, .reg .x14, .reg .x5, .reg .x31, .reg .x16, .reg .x29, slot 96, .reg .x15,
    .reg .x26, .reg .x20, slot 80, slot 112, .reg .x21, .reg .x28, .reg .x17, .reg .x27, .reg .x19,
    .reg .x9, .reg .x18, slot 64, slot 72, .reg .x30, .reg .x6, .reg .x11]

def hd (j : Nat) : E := headE.getD j (.c 0)

/-- The lanes, then the slots, in memory. -/
def stateR : Region := ⟨.x8, 0, 25⟩
def slotsR : Region := ⟨.x2, 0, 16⟩
def bR : Region := ⟨.x2, 336, 25⟩

/-! ## θ -/

theorem theta_obl : b800042e4.obl.all (oblCheck [stateR, slotsR] [] []) = true := by decide +kernel

theorem theta_mem : (List.range 22).all
    (fun i ↦ memOk b800042e4 (key .x8 (8 * i)) (thetaE hd i)) = true := by decide +kernel

theorem theta_regs : (regOk b800042e4 .x11 (thetaE hd 22) && regOk b800042e4 .x5 (thetaE hd 23) &&
    regOk b800042e4 .x16 (thetaE hd 24)) = true := by decide +kernel

theorem theta_writes : writesIn b800042e4 [stateR, slotsR] = true := by decide +kernel

/-- The slot that `0x800044e4` loads the round constant from. -/
def rcR : Region := ⟨.x10, 0, 1⟩

theorem rc_obl : b800044e4.obl.all (oblCheck [stateR, slotsR, rcR] [] []) = true := by decide +kernel

theorem rc_writes : writesIn b800044e4 [stateR, slotsR] = true := by decide +kernel

/-! ## ρ and π -/

def rhoAddr (i : Nat) : Word := 0xa0000550 + BitVec.ofNat 64 (4 * i)

/-- `KECCAK_RHO[i]`, as the loop loads it. -/
def rhoE (i : Nat) : E := .un (.ld .w (byteOffset (rhoAddr i))) (.ld (.c (alignToDword (rhoAddr i))))

/-- Where `b[KECCAK_PI[i]]` goes. -/
def piKey : Addr := ⟨some (.bin .add (.reg .x17) (.bin .sll (.ld (.reg .x13)) (.c 3))), 0⟩

/-- `b[KECCAK_PI[i]]`: lane `i` rotated by `KECCAK_RHO[i]`. -/
def piVal (i : Nat) : E :=
  .bin .or (.bin .sll (.ld (.reg .x12)) (rhoE i)) (.bin .srl (.ld (.reg .x12)) (.bin .sub (.c 0) (rhoE i)))

def piSigma (i : Nat) : SymState := Hash.withConsts [(.x11, rhoAddr i)]

def piX (i : Nat) : Expect where
  steps := 15
  pc := .ite .ne (.bin .add (.reg .x13) (.c 8)) (.bin .add (.reg .x10) (.c 200)) (.c 0x80004528)
    (.c 0x80004564)
  regs := [(.x2, .reg .x2), (.x8, .reg .x8), (.x10, .reg .x10), (.x11, .c (rhoAddr (i + 1))),
    (.x12, .bin .add (.reg .x12) (.c 8)), (.x13, .bin .add (.reg .x13) (.c 8)), (.x17, .reg .x17)]
  mem := [(piKey, piVal i)]
  writes := [piKey]
  obl := [.valid piKey 8, .valid ⟨some (.reg .x13), 0⟩ 8, .valid ⟨some (.reg .x12), 0⟩ 8]

theorem pi_run : (List.range 25).all (fun i ↦
    (symRunCodeAux cfg (codeWindow Image.code 4426 15) 0x80004528 15 (piSigma i)).any
      (Hash.meetsR cfg [] [] · (piX i))) = true := by decide +kernel

/-- `KECCAK_PI[i]` and `KECCAK_RHO[i]` where the loop loads them, in `keccakTableWords`. -/
theorem pi_table : (List.range 25).all (fun i ↦
    keccakTableWords.getD (37 + i) 0 == BitVec.ofNat 64 (keccakPiRust.getD i 0) &&
    decide (keccakPiRust.getD i 0 < 25)) = true := by decide +kernel

theorem rho_table : (List.range 25).all (fun i ↦
    alignToDword (rhoAddr i) == keccakTablesAddr + BitVec.ofNat 64 (8 * (24 + i / 2)) &&
    (extractWord32 (keccakTableWords.getD (24 + i / 2) 0) (byteOffset (rhoAddr i) / 4)).signExtend 64
      == BitVec.ofNat 64 (keccakRhoRust.getD i 0) &&
    decide (keccakRhoRust.getD i 0 < 64)) = true := by decide +kernel

/-! ## χ and ι -/

/-- `b[j]`. -/
def bE (j : Nat) : E := slot (336 + 8 * j)

/-- Lane `i` after the round. -/
def outE (i : Nat) : E := if i = 0 then .bin .xor (chiE bE 0) (slot 112) else chiE bE i

def headOut : List (Reg × E) :=
  ((List.range 25).zip headE).filterMap fun p ↦ match p.2 with
    | .reg r => some (r, outE p.1)
    | _ => none

def slotOut : List (Addr × E) :=
  ((List.range 25).zip headE).filterMap fun p ↦ match p.2 with
    | .ld (.bin .add (.reg .x2) (.c off)) => some (⟨some (.reg .x2), off⟩, outE p.1)
    | _ => none

def chiX : Expect where
  steps := 158
  pc := .ite .ne (.bin .add (slot 88) (.c 1)) (.c 24) (.c 0x800042e4) (.c 0x800047dc)
  regs := [(.x2, .reg .x2), (.x8, .reg .x8), (.x25, .bin .add (slot 88) (.c 1))] ++ headOut
  mem := (List.range 25).map (fun i ↦ (key .x8 (8 * i), outE i)) ++ slotOut
  writes := (List.range 25).map (key .x8 <| 8 * ·) ++ (List.range 16).map (key .x2 <| 8 * ·)
  obl := []

theorem chi_run : (symRunCodeAux cfg (codeWindow Image.code 4441 158) 0x80004564 158 SymState.init).any
    (Hash.meetsR cfg [stateR, slotsR, bR] [] · chiX) = true := by decide +kernel

theorem chi_head : (List.range 25).all (fun j ↦ atomOk chiX (hd j) (outE j)) = true := by
  decide +kernel

theorem chi_writes : writesIn chiX [stateR, slotsR] = true := by decide +kernel

/-! ## Entry and exit -/

theorem setup_obl : b80004264.obl.all (oblCheck [stateR, slotsR] [] []) = true := by decide +kernel

theorem setup_head : (List.range 25).all
    (fun j ↦ atomOk b80004264 (hd j) (.ld (Addr.toE (key .x8 (8 * j))))) = true := by decide +kernel

theorem setup_writes : writesIn b80004264 [slotsR] = true := by decide +kernel

theorem rc_table : (List.range 24).all
    (fun j ↦ keccakTableWords.getD j 0 == keccakRCRust.getD j 0) = true := by decide +kernel

end Rv64Verifier.Hash.KeccakF
