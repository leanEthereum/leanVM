module

public import LeanVMCircuits.ShiftSemantics

@[expose] public section

namespace LeanVMCircuits.Adder

theorem value_injective {n : ℕ} {x y : Vector Bit n} (h : value x = value y) : x = y := by
  induction n with
  | zero => apply Vector.ext; intro i hi; omega
  | succ n ih =>
    have hlower : value x.pop = value y.pop := by
      have hm := congrArg (fun v => v % 2 ^ n) h
      rw [value_pop x, value_pop y] at hm
      have hx : value x.pop < 2 ^ n := value_lt x.pop
      have hy : value y.pop < 2 ^ n := value_lt y.pop
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hm
    have hupper : x[n].val = y[n].val := by
      rw [value_pop x, value_pop y, hlower] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_left_cancel h)
    have hbit : x[n] = y[n] := by
      rw [← ZMod.natCast_zmod_val x[n], ← ZMod.natCast_zmod_val y[n], hupper]
    calc
      x = x.pop.push x[n] := x.push_pop_back.symm
      _ = y.pop.push y[n] := by rw [ih hlower, hbit]
      _ = y := y.push_pop_back

theorem value_three (bits : Vector Bit 3) :
    value bits = bits[0].val + 2 * bits[1].val + 4 * bits[2].val := by
  rw [value_pop bits, value_pop bits.pop, value_pop bits.pop.pop]
  simp only [value_zero, zero_add]
  norm_num

end LeanVMCircuits.Adder

namespace LeanVMCircuits.Words

def ofNat : (n : ℕ) → ℕ → Vector Bit n
  | 0, _ => #v[]
  | n + 1, value => (ofNat n value).push ((value / 2 ^ n : ℕ) : Bit)

theorem value_ofNat (n value : ℕ) : Adder.value (ofNat n value) = value % 2 ^ n := by
  induction n with
  | zero => simp [ofNat, Adder.value, Nat.mod_one]
  | succ n ih =>
    rw [ofNat, Adder.value_push, ih]
    simpa only [ZMod.val_natCast] using (Nat.mod_pow_succ (x := value) (b := 2) (k := n)).symm

theorem ofNat_value {n : ℕ} (bits : Vector Bit n) : ofNat n (Adder.value bits) = bits := by
  apply Adder.value_injective
  rw [value_ofNat, Nat.mod_eq_of_lt (Adder.value_lt bits)]

end LeanVMCircuits.Words
