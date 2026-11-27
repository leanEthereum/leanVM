/-
  LeanVM.Guest.B1.Merkle.CapBody

  `verify_merkle_cap`'s body as a template, `mcBody (2^D)` at its deployed depths, for the witness-stream
  pops it makes (`CapPops.lean`: none); its meaning is its reference function's (`CapRef.lean`).
-/

module

public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.CoreFind
public import LeanVM.Guest.Pack.P4.Core
public import LeanVM.Guest.Pack.P6.Core
public import LeanVM.Guest.Pack.P11.Core
public import LeanVM.Guest.Pack.P23.Core
public import LeanVM.Guest.Pack.P42.Core
public import LeanVM.Guest.Pack.P56.Core
public import LeanVM.Guest.Pack.P61.Core
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_merkle_cap__L»
import LeanVM.Guest.KernelLit
import LeanVM.Guest.StmtsAppend

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value.Keccak

@[expose] public section

/-- The `0x80` padding constant of a 64-byte message's last byte (`0x80 << 56`). -/
abbrev w63 : E := word 9223372036854775808 0

/-- The first value of the padding run. -/
def mcP (L : ℕ) : ℕ := 4 * L

/-- Node `k`'s `KECCAK` inputs: its children's cells, the padding run, the constant `c`. -/
def mcIns (L k c : ℕ) : List V :=
  [.n (4 * k), .n (4 * k + 1), .n (4 * k + 2), .n (4 * k + 3), .n (mcP L), .n (mcP L + 1),
    .n (mcP L + 2), .n (mcP L + 3), .n c, .n (mcP L + 1), .n (mcP L + 2), .n (mcP L + 3),
    .n (mcP L + 4)]

/-- Node `k`'s `KECCAK` outputs: its two cells. -/
def mcOuts (k : ℕ) : List V := [.n (2 * k), .n (2 * k + 1)]

/-- Node `k`'s constant's offset from its first value: after the two pins, or right after the
flag. -/
def mcOc (L k : ℕ) : ℕ := if 2 * k < L then 3 else 1

/-- Node `k`'s first value (`2 ≤ k ≤ L`; at `k = L`, the return's). -/
def mcBase (L k : ℕ) : ℕ :=
  if 2 * k < L then 4 * L + 6 + 4 * (k - 2)
  else 4 * L + 6 + 4 * (L / 2 - 2) + 2 * (k - L / 2)

/-- Node `k`'s atoms from the value `b`. -/
def mcNode (L k b : ℕ) : List Stmt :=
  [.atom (.load (.n b) (.n (valf% «verify_merkle_cap» "flags")) k),
    .ite (.n b)
      (if 2 * k < L then
        [.atom (.const (.n (b + 1)) (word 0 0)), .atom (.load (.n (b + 1)) (.n (valf% «verify_merkle_cap» "flags")) (2 * k)),
          .atom (.const (.n (b + 2)) (word 0 0)), .atom (.load (.n (b + 2)) (.n (valf% «verify_merkle_cap» "flags")) (2 * k + 1))]
      else [])
      [.atom (.const (.n (b + mcOc L k)) w63),
        keccakA (mcIns L k (b + mcOc L k)) (mcOuts k)]]

/-- The expansion of `verify_merkle_cap` at `L` leaves. -/
def mcBody (L : ℕ) : List Stmt :=
  ((List.range (4 * L - 2)).map fun i ↦ [.atom (.load (.n (i + 2)) (.n (valf% «verify_merkle_cap» "cap")) (i + 2))]).flatten ⧺
  [.atom (.const (.n (mcP L)) (word 1 0)), .atom (.const (.n (mcP L + 1)) (word 0 0)),
    .atom (.const (.n (mcP L + 2)) (word 0 0)), .atom (.const (.n (mcP L + 3)) (word 0 0)),
    .atom (.const (.n (mcP L + 4)) (word 0 0)), .atom (.const (.n (mcP L + 5)) w63),
    keccakA (mcIns L 1 (mcP L + 5)) (mcOuts 1)] ⧺
  ((List.range (L - 2)).map fun j ↦ mcNode L (j + 2) (mcBase L (j + 2))).flatten ⧺
  [.atom (.copy (.n (mcBase L L)) (.n (valf% «verify_merkle_cap» "runs[0]"))), .atom (.copy (.n (mcBase L L + 1)) (.n (valf% «verify_merkle_cap» "runs[1]"))),
    .ret [.n (mcBase L L), .n (mcBase L L + 1)]]

open LeanVM.Guest.KernelLit in
kernel_rfl verify_merkle_cap_L2_body : (Fn.«verify_merkle_cap__L2».core).body = mcBody (2 ^ 2)

open LeanVM.Guest.KernelLit in
kernel_rfl verify_merkle_cap_L3_body : (Fn.«verify_merkle_cap__L3».core).body = mcBody (2 ^ 3)

open LeanVM.Guest.KernelLit in
kernel_rfl verify_merkle_cap_L4_body : (Fn.«verify_merkle_cap__L4».core).body = mcBody (2 ^ 4)

open LeanVM.Guest.KernelLit in
kernel_rfl verify_merkle_cap_L5_body : (Fn.«verify_merkle_cap__L5».core).body = mcBody (2 ^ 5)

open LeanVM.Guest.KernelLit in
kernel_rfl verify_merkle_cap_L6_body : (Fn.«verify_merkle_cap__L6».core).body = mcBody (2 ^ 6)

open LeanVM.Guest.KernelLit in
kernel_rfl verify_merkle_cap_L7_body : (Fn.«verify_merkle_cap__L7».core).body = mcBody (2 ^ 7)

open LeanVM.Guest.KernelLit in
kernel_rfl verify_merkle_cap_L8_body : (Fn.«verify_merkle_cap__L8».core).body = mcBody (2 ^ 8)

end
end LeanVM.Guest.B1
