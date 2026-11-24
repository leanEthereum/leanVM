/-
  LeanVM.Guest.B1.Sig.XmssCore

  A layer of `verify_lean_xmss`: its step addresses a sequential block, and base-4 digits below a
  power.
-/

module

public import LeanVM.Guest.B1.Sig.CompleteKit
public import LeanVM.Guest.B1.Sig.XmssStep

/-!
# A layer of `verify_lean_xmss`

* `mod_pow_div_mod`: digit `t` of `x mod 4^n` is digit `t` of `x`, `t < n`;
* `xStepAddrs_seq`: the step addresses are a sequential block (`SeqOK`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

theorem mod_pow_div_mod (x n t : Nat) (ht : t < n) : x % 4 ^ n / 4 ^ t % 4 = x / 4 ^ t % 4 := by
  rw [show 4 ^ n = 4 ^ t * 4 ^ (n - t) by rw [← pow_add]; congr 1; omega, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 4 (by omega))]

theorem xStepAddrs_seq {idx : V} {a : Nat} (h : NBv a idx) : SeqOK a (xStepAddrs idx a) (a + 6) :=
  ⟨rfl, ⟨rfl, h.mono' (by omega), ⟨a, by omega, rfl⟩⟩, rfl, ⟨rfl, h.mono' (by omega), ⟨a + 2, by omega, rfl⟩⟩,
    rfl, ⟨rfl, h.mono' (by omega), ⟨a + 4, by omega, rfl⟩⟩, rfl⟩

attribute [local irreducible] kMsg

variable {C : CallRel} {rd : Reader}

end
end LeanVM.Guest.B1.Sig
