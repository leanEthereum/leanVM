module

public import NativeRustcVmX64.Ring.Coeff.Turn
public import NativeRustcX64.Hasher.Bytes

/-!
# `ring_coefficients`: between turns (x86-64)

`row_at`: at a turn's end (`tRn`), the row of `out` holds the turn's products. `next_head`: the end
of turn `p` is the head of turn `p + 1` (`tH`, `G`'s Frobenius images the next `g`), in its own
layout. `to_exit`: the end of the last turn is the epilogue's state (`tX`).
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingCoefficients

public section

variable {m0 m : MachineData} {p : Nat}

theorem bv17_row {F : EW} {g G' : Nat → EW} {k : Nat} (hk : k < 8) :
    bvG m0 p F g G' 17 (29 + 2 * k) = c0 (F * g k) ∧
      bvG m0 p F g G' 17 (30 + 2 * k) = c1 (F * g k) := by
  interval_cases k <;> exact ⟨rfl, rfl⟩

theorem byteOf_c (x : UInt64) : (List.range 8).map (byteOf x.toBitVec) = NativeRustcVm.wordBytes x :=
  (Hasher.wordBytes_ofBitVec x.toBitVec).symm

/-- **The row** at a turn's end. -/
theorem row_at [Labels] {F : EW} {g G' : Nat → EW} {d : MachineData}
    (hB : Bnd (own m0 m) 176 NC (rsP m0 p) wrRow tRn (bvG m0 p F g G' 17) d) :
    NativeRustcVm.EWsAt d.dmem (oA m0 + BitVec.ofNat 64 (128 * p)) ((List.range 8).map fun k ↦ F * g k) := by
  have hm := hB.mt 0
  rw [NativeRustcVm.ewsAt_iff]
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  have hrow := tRn_row i hi
  have hb : (envS (own m0 m) d 176 (rsP m0 p) (bvG m0 p F g G' 17) 0).regions[1]? =
      some (oA m0 + BitVec.ofNat 64 (128 * p), 128) := rfl
  have w0 := hm.bytesAt_write hb (o := 16 * i) (n := 8) (by omega)
    (v := .var (29 + 2 * i)) fun t ht ↦ (hrow t ht).1
  have w1 := hm.bytesAt_write hb (o := 16 * i + 8) (n := 8) (by omega)
    (v := .var (30 + 2 * i)) fun t ht ↦ (hrow t ht).2
  simp only [Sym.eval, Env.ofMachine] at w0 w1
  rw [(bv17_row hi).1, byteOf_c] at w0
  rw [(bv17_row hi).2, byteOf_c] at w1
  rw [NativeRustcVm.ewAt_iff]
  refine ⟨w0, ?_⟩
  rw [NativeRustcVm.addr_add_add]
  exact w1

/-- The links' values, evaluated: what `rfl` closes. -/
macro "ltac" : tactic => `(tactic|
  (simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval]
   and_intros
   all_goals (first | rfl | exact fun _ h ↦ nomatch h)))

/-- **The next head**: the end of turn `p` is the head of turn `p + 1`. -/
theorem next_head [Labels] {F : EW} {g G' : Nat → EW} {d : MachineData}
    (hB : Bnd (own m0 m) 176 NC (rsP m0 p) wrRow tRn (bvG m0 p F g G' 17) d) :
    Bnd (own m0 d) 176 NC (rsP m0 (p + 1)) wrRow tH (hvG m0 (p + 1) G') d :=
  ⟨fun ret ↦ match_links (hB.mt 0) (by decide) rfl rfl (fun _ ↦ rfl) rfl rfl rfl (by ltac) rfl
      (regions_envS rfl) rfl (fun _ _ h ↦ by cases h) (keys_ok rfl rfl rfl rfl d ret),
    fun _ _ ↦ rfl, fun _ h ↦ h⟩

/-- **The epilogue's state**: the end of the last turn. -/
theorem to_exit [Labels] {F : EW} {g G' : Nat → EW} {d : MachineData}
    (hB : Bnd (own m0 m) 176 NC (rsP m0 p) wrRow tRn (bvG m0 p F g G' 17) d) :
    Bnd (own m0 m) 176 NC (rsP m0 p) wrRow tX (bvG m0 p F g G' 17) d :=
  ⟨fun ret ↦ match_links (hB.mt 0) (by decide) rfl rfl (fun _ ↦ rfl) rfl rfl rfl (by ltac) rfl
      (regions_envS rfl) rfl (fun _ _ h ↦ by cases h) (fun _ _ _ h ↦ by cases h),
    hB.same, hB.kept⟩

end

end NativeRustcVmX64.Ring.Coeff
