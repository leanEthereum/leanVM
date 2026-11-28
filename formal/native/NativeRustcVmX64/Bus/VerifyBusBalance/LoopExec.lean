module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Exec
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public meta import NativeRustcVmX64.Bus.VerifyBusBalance.Exec

/-!
# `verify_bus_balance`'s zeroing loops, round by round (x86-64)

Both loops run a fixed number of rounds; each round runs from a literal state with RAX its
counter's value (`l1S k`, `l2S k`), checked for every round at once by the kernel:

- `NativeRustcVmX64.Vm.VerifyBusBalance.label_6` (`b16`, 21 rounds, RAX `40 + 48 k`): six zero words at `672 + 48 k`, the
  loop goes on unless `k = 20` (`of_ok16`);
- `NativeRustcVmX64.Vm.VerifyBusBalance.label_17` (`b36`, 17 rounds, RAX `56 + 64 k`): six zero words at `672 + 64 k`,
  leaves at `k = 16` (`of_ok36`); `b37` (16 rounds): two more at `720 + 64 k` (`of_ok37`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus

@[expose] public section

def l1S (k : Nat) : SState := init [5528] [(.rsp, .ptr 0 104), (.rax, .lit (40 + 48 * k))]
def l2S (k : Nat) : SState := init [5528] [(.rsp, .ptr 0 104), (.rax, .lit (56 + 64 * k))]

/-- `n` zero words from `o`. -/
def zeros (o n : Nat) : List (Nat × Sym) := (List.range n).map fun i ↦ (o + 8 * i, .lit 0)

def ok16 (k : Nat) : Bool :=
  match exec b16 (l1S k) with
  | some (S, .cond (.lit b) l) => MidOk 5520 104 slots S && decide (W0 (672 + 48 * k) (720 + 48 * k) S) &&
      decide (Wrote 0 (zeros (672 + 48 * k) 6) S) && decide (Keeps cs S) &&
      (S.reg .rax == some (.lit (88 + 48 * k))) && (b == !decide (k = 20)) && (l == NativeRustcVmX64.Vm.VerifyBusBalance.label_6)
  | _ => false

def ok36 (k : Nat) : Bool :=
  match exec b36 (l2S k) with
  | some (S, .cond (.lit b) l) => MidOk 5520 104 slots S && decide (W0 (672 + 64 * k) (720 + 64 * k) S) &&
      decide (Wrote 0 (zeros (672 + 64 * k) 6) S) && decide (Keeps cs S) &&
      (S.reg .rax == some (.lit (56 + 64 * k))) && (b == decide (k = 16)) && (l == NativeRustcVmX64.Vm.VerifyBusBalance.label_19)
  | _ => false

def ok37 (k : Nat) : Bool :=
  match exec b37 (l2S k) with
  | some (S, .jump l) => MidOk 5520 104 slots S && decide (W0 (720 + 64 * k) (736 + 64 * k) S) &&
      decide (Wrote 0 (zeros (720 + 64 * k) 2) S) && decide (Keeps cs S) &&
      (S.reg .rax == some (.lit (120 + 64 * k))) && (l == NativeRustcVmX64.Vm.VerifyBusBalance.label_17)
  | _ => false

end

set_option Elab.async false

public theorem ok16_all : ∀ k < 21, ok16 k = true := by decide +kernel
public theorem ok36_all : ∀ k < 17, ok36 k = true := by decide +kernel
public theorem ok37_all : ∀ k < 16, ok37 k = true := by decide +kernel

public section

theorem of_ok16 {k : Nat} (h : ok16 k = true) : ∃ S, exec b16 (l1S k) =
    some (S, .cond (.lit (!decide (k = 20))) NativeRustcVmX64.Vm.VerifyBusBalance.label_6) ∧ Mid 104 S ∧
    W0 (672 + 48 * k) (720 + 48 * k) S ∧ Wrote 0 (zeros (672 + 48 * k) 6) S ∧ Keeps cs S ∧
    S.reg .rax = some (.lit (88 + 48 * k)) := by
  unfold ok16 at h
  split at h
  · rename_i S b l he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h7⟩, h5⟩, h6⟩ := h
    subst h5 h6
    exact ⟨S, he, h1, h2, h3, h4, h7⟩
  · cases h

theorem of_ok36 {k : Nat} (h : ok36 k = true) : ∃ S, exec b36 (l2S k) =
    some (S, .cond (.lit (decide (k = 16))) NativeRustcVmX64.Vm.VerifyBusBalance.label_19) ∧ Mid 104 S ∧
    W0 (672 + 64 * k) (720 + 64 * k) S ∧ Wrote 0 (zeros (672 + 64 * k) 6) S ∧ Keeps cs S ∧
    S.reg .rax = some (.lit (56 + 64 * k)) := by
  unfold ok36 at h
  split at h
  · rename_i S b l he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h7⟩, h5⟩, h6⟩ := h
    subst h5 h6
    exact ⟨S, he, h1, h2, h3, h4, h7⟩
  · cases h

theorem of_ok37 {k : Nat} (h : ok37 k = true) : ∃ S, exec b37 (l2S k) =
    some (S, .jump NativeRustcVmX64.Vm.VerifyBusBalance.label_17) ∧ Mid 104 S ∧
    W0 (720 + 64 * k) (736 + 64 * k) S ∧ Wrote 0 (zeros (720 + 64 * k) 2) S ∧ Keeps cs S ∧
    S.reg .rax = some (.lit (120 + 64 * k)) := by
  unfold ok37 at h
  split at h
  · rename_i S l he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h7⟩, h5⟩ := h
    subst h5
    exact ⟨S, he, h1, h2, h3, h4, h7⟩
  · cases h

theorem mem_zeros {o n i : Nat} (hi : i < n) : (o + 8 * i, Sym.lit 0) ∈ zeros o n :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

end

end NativeRustcVmX64.Bus.VerifyBusBalance
