module

public import NativeRustcVmArm.Top.VerifyExecution.Keep

/-!
# `verify_execution`: `keccak_phase`'s areas

The regions `keccak_phase` writes (the `TState`, the scratch, the column claims, the Keccak output)
and reads (the decoded area, the tables' evaluations, the round constants, `RMFE_PROJECT`,
`KECCAK_RHO`) are data memory, the written ones and the stack pairwise apart and apart from the
read ones (`At.keccakAreas`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVm.Transcript
open NativeRustcVm (Region)
local notation "Ap" => NativeRustcVm.Apart
open NativeVm.Model (TState)

public section

variable [Labels] {a : DecArea} {m0 st : MachineData}

theorem projectAddr_eq : projectAddr = rodataAddr .rmfeProject := rfl
theorem rhoAddr_eq : rhoAddr = rodataAddr .keccakRho := rfl

/-- A read-only item apart from a range apart from all of them. -/
theorem itemApart {x : BitVec 64} {n : Nat} (h : RodataApart x n) :
    Ap x n rcAddr 192 ∧ Ap x n projectAddr 128 ∧ Ap x n rhoAddr 100 := by
  have h1 := h .keccakRC
  have h2 := h .rmfeProject
  have h3 := h .keccakRho
  rw [keccakRC_length] at h1
  rw [rmfeProject_length] at h2
  rw [keccakRho_length] at h3
  exact ⟨h1, h2, h3⟩

/-- The read-only items apart from the stack below SP. -/
theorem itemStack {m : MachineData} {N : Nat} (h : RodataAt m N) :
    Ap rcAddr 192 (stackBelow m N) N ∧ Ap projectAddr 128 (stackBelow m N) N ∧
      Ap rhoAddr 100 (stackBelow m N) N := by
  have h1 := NativeRustcVm.RodataAt.apart h .keccakRC
  have h2 := NativeRustcVm.RodataAt.apart h .rmfeProject
  have h3 := NativeRustcVm.RodataAt.apart h .keccakRho
  rw [keccakRC_length] at h1
  rw [rmfeProject_length] at h2
  rw [keccakRho_length] at h3
  exact ⟨h1, h2, h3⟩

/-- The read-only items are data memory, not wrapping. -/
theorem itemOk {m : MachineData} {N : Nat} (h : RodataAt m N) :
    Region.Ok m.dmem ⟨rcAddr, 192⟩ ∧ Region.Ok m.dmem ⟨projectAddr, 128⟩ ∧
      Region.Ok m.dmem ⟨rhoAddr, 100⟩ := by
  have b1 := NativeRustcVm.RodataAt.bytesAt h .keccakRC
  have b2 := NativeRustcVm.RodataAt.bytesAt h .rmfeProject
  have b3 := NativeRustcVm.RodataAt.bytesAt h .keccakRho
  have n1 := NativeRustcVm.RodataAt.noWrap h .keccakRC
  have n2 := NativeRustcVm.RodataAt.noWrap h .rmfeProject
  have n3 := NativeRustcVm.RodataAt.noWrap h .keccakRho
  have m1 := b1.mapped
  have m2 := b2.mapped
  have m3 := b3.mapped
  rw [keccakRC_length] at n1 m1
  rw [rmfeProject_length] at n2 m2
  rw [keccakRho_length] at n3 m3
  exact ⟨⟨m1, n1⟩, ⟨m2, n2⟩, ⟨m3, n3⟩⟩

/-- A working-area range apart from the decoded area. -/
theorem Geo.apartWA (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    Ap (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n a.words (8 * a.len) := by
  have := g.aw
  show _ ∨ _
  rw [g.wAddr ho]
  omega

/-- **`keccak_phase`'s areas.** -/
theorem At.keccakAreas (h : At m0 st) (g : Geo a m0) {s : TState}
    (hts : TStateAt st.dmem m0.regs.X0.toBitVec a s) {N : Nat} (hN : N ≤ 18288) :
    NativeRustcVmArm.Areas st N
      [⟨m0.regs.X0.toBitVec, tstateBytes⟩,
        ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 289728, NativeRustcVm.KeccakGkr.scratchBytes⟩,
        ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 123992, NativeRustcVm.Layout.claimsBytes⟩,
        ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 221280, NativeRustcVm.KeccakGkr.outBytes⟩]
      [a.region,
        ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 112184, NativeRustcVm.Tables.tableEvalsBytes⟩,
        NativeRustcVmArm.rcRegion, NativeRustcVmArm.projectRegion,
        NativeRustcVmArm.rhoRegion] := by
  have hR := h.rodataAt g hN
  have hT := h.tstateOk g hN
  obtain ⟨o1, o2, o3⟩ := itemOk hR
  obtain ⟨s1, s2, s3⟩ := itemStack hR
  obtain ⟨t1, t2, t3⟩ := itemApart g.rt
  show NativeRustcVmArm.Areas st N
    [⟨m0.regs.X0.toBitVec, 760⟩, ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 289728, 205824⟩,
      ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 123992, 97288⟩,
      ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 221280, 1608⟩]
    [⟨a.words, 8 * a.len⟩, ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 112184, 11808⟩,
      ⟨rcAddr, 192⟩, ⟨projectAddr, 128⟩, ⟨rhoAddr, 100⟩]
  have wOk : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      Region.Ok st.dmem ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 o, n⟩ := fun ho hn ↦
    h.readable g ho hn
  have wSt : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      Ap (stackBelow st N) N (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun ho hn ↦
    (h.offStack g ho hn hN).symm
  have wIt : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      Ap (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n rcAddr 192 ∧
        Ap (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n projectAddr 128 ∧
        Ap (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n rhoAddr 100 := fun ho hn ↦
    itemApart (g.rodataApart ho hn)
  refine ⟨fun r hr ↦ ?_, ?_, fun w hw r hr ↦ ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    · exact hts.footprint.1
    · exact wOk (o := 289728) (n := 205824) (by omega) (by omega)
    · exact wOk (o := 123992) (n := 97288) (by omega) (by omega)
    · exact wOk (o := 221280) (n := 1608) (by omega) (by omega)
    · exact hts.footprint.2.1
    · exact wOk (o := 112184) (n := 11808) (by omega) (by omega)
    · exact o1
    · exact o2
    · exact o3
  · simp only [NativeRustcVm.disjoint_cons_iff, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, NativeRustcVm.disjoint_nil, and_true,
      NativeRustcVmArm.stackRegion]
    refine ⟨⟨hT.1.symm, wSt (o := 289728) (n := 205824) (by omega) (by omega),
      wSt (o := 123992) (n := 97288) (by omega) (by omega),
      wSt (o := 221280) (n := 1608) (by omega) (by omega)⟩,
      ⟨(g.apartWT (o := 289728) (n := 205824) (by omega)
        (by omega)).symm, (g.apartWT (o := 123992) (n := 97288) (by omega) (by omega)).symm,
      (g.apartWT (o := 221280) (n := 1608) (by omega) (by omega)).symm⟩,
      ⟨g.apartW (o := 289728) (n := 205824) (o' := 123992) (n' := 97288) (by omega) (by omega)
        (by omega), g.apartW (o := 289728) (n := 205824) (o' := 221280) (n' := 1608) (by omega)
        (by omega) (by omega)⟩, ?_⟩
    exact ⟨g.apartW (o := 123992) (n := 97288) (o' := 221280) (n' := 1608) (by omega)
      (by omega) (by omega), fun _ h ↦ h.elim⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, NativeRustcVmArm.stackRegion]
      at hw hr
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hT.2.1.symm
    · exact wSt (o := 112184) (n := 11808) (by omega) (by omega)
    · exact s1.symm
    · exact s2.symm
    · exact s3.symm
    · exact hts.footprint.2.2
    · exact (g.apartWT (o := 112184) (n := 11808) (by omega) (by omega)).symm
    · exact t1
    · exact t2
    · exact t3
    · exact g.apartWA (o := 289728) (n := 205824) (by omega) (by omega)
    · exact g.apartW (o := 289728) (n := 205824) (o' := 112184) (n' := 11808) (by omega) (by omega)
        (by omega)
    · exact (wIt (o := 289728) (n := 205824) (by omega) (by omega)).1
    · exact (wIt (o := 289728) (n := 205824) (by omega) (by omega)).2.1
    · exact (wIt (o := 289728) (n := 205824) (by omega) (by omega)).2.2
    · exact g.apartWA (o := 123992) (n := 97288) (by omega) (by omega)
    · exact g.apartW (o := 123992) (n := 97288) (o' := 112184) (n' := 11808) (by omega) (by omega)
        (by omega)
    · exact (wIt (o := 123992) (n := 97288) (by omega) (by omega)).1
    · exact (wIt (o := 123992) (n := 97288) (by omega) (by omega)).2.1
    · exact (wIt (o := 123992) (n := 97288) (by omega) (by omega)).2.2
    · exact g.apartWA (o := 221280) (n := 1608) (by omega) (by omega)
    · exact g.apartW (o := 221280) (n := 1608) (o' := 112184) (n' := 11808) (by omega) (by omega)
        (by omega)
    · exact (wIt (o := 221280) (n := 1608) (by omega) (by omega)).1
    · exact (wIt (o := 221280) (n := 1608) (by omega) (by omega)).2.1
    · exact (wIt (o := 221280) (n := 1608) (by omega) (by omega)).2.2

end

end NativeRustcVmArm.Top.VerifyExecution
