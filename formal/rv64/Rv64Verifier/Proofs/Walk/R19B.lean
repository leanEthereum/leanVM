import Rv64Verifier.Proofs.Walk.R19A

/-!
# `walk` R19, the public input's claims: to the loop's head

`r19a`: from `ExitR18` (`0x80003a48`): the challenge (`duplex`, `sample`), `vec![E::ZERO;
log_memory]` (`from_elem`, the zero from `.rodata`), the length check (`0x80003a78`: an empty
point traps), the challenge into the point's first element and the loop's table on the stack
(`0x80003a84`), to `HeadR19` with no claim pushed.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem spAdd {s u : MachineState} (hpre : WalkPre s) (sp : u.getReg .x2 = s.getReg .x2 - 2656)
    (c d : Word) (hc : c.toNat + d.toNat = 2656) : u.getReg .x2 + c = s.getReg .x2 - d := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]

theorem limbs_zeroE : Model.limbs (0 : E) = (0, 0, 0) := by
  decide +kernel

/-- The point `c, 0, ..`: its first element `c`, the others zero. -/
theorem eList_point {u : MachineState} {p : Word} {n : Nat} {c : E} (hn : 0 < n)
    (h0 : eAt u p = c) (hz : ∀ i, 0 < i → i < n → eAt u (p + BitVec.ofNat 64 (24 * i)) = 0) :
    eListAt u p n = c :: List.replicate (n - 1) 0 := by
  apply List.ext_getElem
  · simp only [eListAt_length, List.length_cons, List.length_replicate]; omega
  · intro i h1 h2
    rw [eListAt_length] at h1
    simp only [eListAt, List.getElem_map, List.getElem_range]
    rcases i with _ | i
    · simp only [List.getElem_cons_zero, Nat.mul_zero, add_ofNat_zero, h0]
    · simp only [List.getElem_cons_succ, List.getElem_replicate]
      exact hz _ (by omega) h1

/-- `0x80003a84`'s frame writes. -/
@[rv_addr] def W84 (s : MachineState) (a : Word) : Prop :=
  a = s.getReg .x2 - 2544 ∨ a = s.getReg .x2 - 2536 ∨ a = s.getReg .x2 - 2528 ∨
  a = s.getReg .x2 - 928 ∨ a = s.getReg .x2 - 920 ∨ a = s.getReg .x2 - 912 ∨
  a = s.getReg .x2 - 904 ∨ a = s.getReg .x2 - 896 ∨ a = s.getReg .x2 - 888 ∨
  a = s.getReg .x2 - 880 ∨ a = s.getReg .x2 - 872 ∨ a = s.getReg .x2 - 864 ∨
  a = s.getReg .x2 - 856 ∨ a = s.getReg .x2 - 848 ∨ a = s.getReg .x2 - 840 ∨
  a = s.getReg .x2 - 832 ∨ a = s.getReg .x2 - 824 ∨ a = s.getReg .x2 - 816 ∨
  a = s.getReg .x2 - 2520

theorem W84_within {s : MachineState} (hpre : WalkPre s) {a : Word} (ha : W84 s a) :
    Within a (s.getReg .x2 - 2544) 32 ∨ Within a (s.getReg .x2 - 928) 120 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [W84] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (left; simp only [Within]; constructor <;> addr_omega [hb1])
      | (right; simp only [Within]; constructor <;> addr_omega [hb1])

theorem W84_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {a : Word}
    (ha : W84 s a) : InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368 ∧
      ¬ Within a (s.getReg .x2 - 1632) 16 ∧ ¬ Within a (s.getReg .x2 - 2616) 16 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases W84_within hpre ha with lo | lo
  · obtain ⟨o1, o2⟩ := range_ok hpre h (c := 2544) (k := 2544) (n := 32) rfl (by omega) (by omega) lo
    simp only [Within] at lo
    refine ⟨o1, o2, ?_, ?_, ?_⟩ <;> simp only [Within, tp] <;> addr_omega [lo, hb1]
  · obtain ⟨o1, o2⟩ := range_ok hpre h (c := 928) (k := 928) (n := 120) rfl (by omega) (by omega) lo
    simp only [Within] at lo
    refine ⟨o1, o2, ?_, ?_, ?_⟩ <;> simp only [Within, tp] <;> addr_omega [lo, hb1]

/-- A frame range's facts, for the steps' writes. -/
theorem range_okT {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {c : Word}
    {k n : Nat} (hc : c.toNat = k) (hk : 112 + n ≤ k + 8 ∧ k ≤ 2656)
    (hn : (k ≤ 1768 ∨ 1800 + n ≤ k) ∧ (k ≤ 1872 ∨ 2088 + n ≤ k) ∧ (k ≤ 2440 ∨ 2448 + n ≤ k) ∧
      (k ≤ 2480 ∨ 2488 + n ≤ k) ∧ (k ≤ 2544 ∨ 2584 + n ≤ k))
    (ht : k ≤ 2080 ∨ 2448 + n ≤ k) (h1 : k ≤ 1616 ∨ 1632 + n ≤ k) (h2 : k ≤ 2600 ∨ 2616 + n ≤ k)
    {a : Word} (ha : Within a (s.getReg .x2 - c) n) :
    InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368 ∧
      ¬ Within a (s.getReg .x2 - 1632) 16 ∧ ¬ Within a (s.getReg .x2 - 2616) 16 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2⟩ := range_ok hpre h hc hk hn ha
  simp only [Within] at ha
  refine ⟨o1, o2, ?_, ?_, ?_⟩ <;> simp only [Within, tp] <;> addr_omega [ha, hb1, hc, hk, ht, h1, h2]

end Rv64Verifier.Proofs.Walk
