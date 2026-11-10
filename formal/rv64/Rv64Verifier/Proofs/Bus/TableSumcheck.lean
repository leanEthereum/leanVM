import Rv64Verifier.Proofs.Bus.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F30

/-!
# `table_sumcheck`, the first stage

```rust
let n_rounds = table_log_heights.iter().copied().max().unwrap_or(0);
let (challenges, claim) = sumcheck(transcript, target, 4, &vec![None; n_rounds])?;
```

compiled at `0x80008010` (`Blocks/F30.lean`): the loop at `0x800080a4` takes the maximum of the
heights; `0x800080b8` calls `vec![None; n_rounds]` into `S - 248`, `0x800080cc` calls `sumcheck`
into `S - 152`, `0x800080ec` returns the `Err` through `0x800084e0`.

Proved here: the maximum loop (`maxLoop`), whose value is the mirror's `heights.max?.getD 0`.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The maximum of the first `k` heights from `hp`. -/
def maxOf (u : MachineState) (hp : Word) (k : Nat) : Nat :=
  ((List.range k).map fun i ↦ (u.getMem (hp + BitVec.ofNat 64 (8 * i))).toNat).foldl max 0

theorem maxOf_succ (u : MachineState) (hp : Word) (k : Nat) :
    maxOf u hp (k + 1) = max (maxOf u hp k) (u.getMem (hp + BitVec.ofNat 64 (8 * k))).toNat := by
  simp only [maxOf, List.range_succ, List.map_append, List.foldl_append, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil]

theorem maxOf_eq (u : MachineState) (hp : Word) (n : Nat) :
    maxOf u hp n = (natsAt u hp n).max?.getD 0 := by
  rw [max?_getD, natsAt, readWords_eq_map, List.map_map]
  rfl

/-- The loop at `0x800080a4`, `k` heights seen: it reaches `0x800080b8` with their maximum in
`a2`, writing nothing. -/
theorem maxLoop {hp : Word} {n : Nat} (hval : ValidMemRange hp n) :
    ∀ m k (u : MachineState), n - k = m → 1 ≤ k → k < n → u.pc = 0x800080a4 →
      u.getReg .x10 = hp + BitVec.ofNat 64 (8 * k) → u.getReg .x11 = hp + BitVec.ofNat 64 (8 * n) →
      (u.getReg .x12).toNat = maxOf u hp k →
      ∃ t, Reaches Image.code u t ∧ t.pc = 0x800080b8 ∧ (t.getReg .x12).toNat = maxOf u hp n ∧
        (∀ a, t.getMem a = u.getMem a) ∧
        ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x13 → t.getReg r = u.getReg r := by
  intro m
  induction m with
  | zero => intro k u hm hk1 hkn; omega
  | succ m ih =>
    intro k u hm hk1 hkn hpc h10 h11 h12
    have hv := ValidMemRange.bounds hval (by omega)
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800080a4_spec hpc (by
      rv_eval [h10]
      valid_access hval [hv, hkn])
    have k₁ := b800080a4_keeps h₁
    have hm₁ := b800080a4_mem_same h₁
    have hx13 := b800080a4_x13 h₁
    rw [h10] at hx13
    -- the new maximum, in `a2`, at `0x8000809c`
    obtain ⟨u₂, hr₂, hpc₂, h12₂, hm₂, k₂⟩ : ∃ u₂, Reaches Image.code u₁ u₂ ∧ u₂.pc = 0x8000809c ∧
        (u₂.getReg .x12).toNat = maxOf u hp (k + 1) ∧ (∀ a, u₂.getMem a = u₁.getMem a) ∧
        ∀ r, r ≠ .x12 → u₂.getReg r = u₁.getReg r := by
      rw [maxOf_succ, ← h12]
      by_cases hlt : (u.getMem (hp + BitVec.ofNat 64 (8 * k))).toNat < (u.getReg .x12).toNat
      · refine ⟨u₁, Reaches.refl _, b800080a4_pc_taken h₁ (by rw [h10]; exact hlt), ?_,
          fun _ ↦ rfl, fun _ _ ↦ rfl⟩
        rw [k₁ .x12 (by decide)]; omega
      · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800080ac_spec
          (b800080a4_pc_not_taken h₁ (by rw [h10]; omega)) trivial
        refine ⟨u₂, hr₂, b800080ac_pc h₂, ?_, b800080ac_mem_same h₂, fun r hr ↦ ?_⟩
        · rw [b800080ac_x12 h₂, hx13]; omega
        · have := b800080ac_keeps h₂
          rcases r <;> first | (exfalso; exact hr rfl) | exact this _ (by decide) | rfl
    obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000809c_spec hpc₂ trivial
    have k₃ := b8000809c_keeps h₃
    have hm₃ := b8000809c_mem_same h₃
    have h10₂ : u₂.getReg .x10 = hp + BitVec.ofNat 64 (8 * k) := by
      rw [k₂ .x10 (by decide), k₁ .x10 (by decide), h10]
    have h11₂ : u₂.getReg .x11 = hp + BitVec.ofNat 64 (8 * n) := by
      rw [k₂ .x11 (by decide), k₁ .x11 (by decide), h11]
    have hmem (a : Word) : u₃.getMem a = u.getMem a := by rw [hm₃, hm₂, hm₁]
    have hx10₃ : u₃.getReg .x10 = hp + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [b8000809c_x10 h₃, h10₂]; addr_omega [hv, hkn]
    have hkeep (r : Reg) (h10' : r ≠ .x10) (h12' : r ≠ .x12) (h13' : r ≠ .x13) :
        u₃.getReg r = u.getReg r := by
      rw [show u₃.getReg r = u₂.getReg r by
          have := k₃; rcases r <;> first | (exfalso; exact h10' rfl) | exact this _ (by decide) | rfl,
        k₂ r h12', show u₁.getReg r = u.getReg r by
          have := k₁; rcases r <;> first | (exfalso; exact h13' rfl) | exact this _ (by decide) | rfl]
    by_cases hlast : k + 1 = n
    · refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), b8000809c_pc_taken h₃ (by
        rw [h10₂, h11₂]; addr_omega [hv, hkn, hlast]), ?_, hmem, hkeep⟩
      rw [k₃ .x12 (by decide), h12₂, hlast]
    · have hmax : maxOf u₃ hp (k + 1) = maxOf u hp (k + 1) := by
        simp only [maxOf, hmem]
      obtain ⟨t, hr, ht⟩ := ih (k + 1) u₃ (by omega) (by omega) (by omega)
        (b8000809c_pc_not_taken h₃ (by rw [h10₂, h11₂]; addr_omega [hv, hkn, hlast])) hx10₃
        (by rw [k₃ .x11 (by decide), h11₂]) (by rw [k₃ .x12 (by decide), h12₂, hmax])
      obtain ⟨hpc', h12', hm', hk'⟩ := ht
      refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), hpc', ?_, fun a ↦ (hm' a).trans (hmem a),
        fun r h1 h2 h3 ↦ (hk' r h1 h2 h3).trans (hkeep r h1 h2 h3)⟩
      rw [h12']
      simp only [maxOf, hmem]

end Rv64Verifier.Proofs.Bus.TableSumcheck
