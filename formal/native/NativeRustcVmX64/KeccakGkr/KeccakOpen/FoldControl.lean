module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldBase

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (off)

public section

theorem atoms_reg {S : SState} {rs : List Reg64} (ha : atoms S rs = true) {r : Reg64}
    (hr : r ∈ rs) : S.reg r = some (.reg r) := by
  have := List.all_eq_true.mp ha r hr
  simpa only [beq_iff_eq] using this

variable [Labels]

theorem KAt.regs_keep {m0 d d' : MachineData} {vars : Nat → BitVec 64}
    {ks : List (Reg64 × Sym)} (hk : KAt m0 vars ks d)
    (hr : ∀ r ∈ ks.map Prod.fst, reg d' r = reg d r) : KAt m0 vars ks d' :=
  allOf_imp hk fun p hp h ↦ (hr p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)).trans h

theorem notEnd_eval {env : Env} {nib : Sym} {s0 j : Nat} (hj : j < 64)
    (hs : s0 + 1024 < 2 ^ 64) (he : nib.eval env = BitVec.ofNat 64 (s0 + 16 * (j + 1))) :
    (notEnd nib (s0 + 1024)).eval env = decide (j + 1 < 64) := by
  simp only [notEnd, SBool.eval, CmpOp.apply, low_W64, Sym.eval, he]
  by_cases hj' : j + 1 = 64
  · have heq : s0 + 16 * (j + 1) = s0 + 1024 := by omega
    simp [heq, show ¬j + 1 < 64 by omega]
  · have hne : BitVec.ofNat 64 (s0 + 16 * (j + 1)) ≠ BitVec.ofNat 64 (s0 + 1024) := by
      intro heq
      have hh := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s0 + 16 * (j + 1) < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt hs] at hh
      omega
    simp [hne, show j + 1 < 64 by omega]

theorem counter_next {env : Env} {ib : Reg64} {s0 j : Nat}
    (hi : env.regs ib = BitVec.ofNat 64 (s0 + 16 * j)) :
    (Sym.bin .add .W64 (.lit 16) (.reg ib)).eval env = BitVec.ofNat 64 (s0 + 16 * (j + 1)) := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hi]
  change BitVec.ofNat 64 16 + BitVec.ofNat 64 (s0 + 16 * j) = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

omit [Labels] in
theorem counter_addr (b : BitVec 64) {dst s0 so i j : Nat} (hd : dst + s0 = 1024 * i + so) :
    off b dst + BitVec.ofNat 64 (s0 + 16 * j) =
      off b (16 * (64 * i + j)) + BitVec.ofInt 64 (so : Int) := by
  simp only [off, BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
