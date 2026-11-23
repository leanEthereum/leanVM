module

public import NativeRustcVmX64.Wire.PhaseM.Climb
public import NativeRustcVm.Arrays.ReadLemmas

/-! # The widened frame for `phase_m`'s four stack arguments -/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap mapped_off
  stackOk_callee)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off Mapped.keeps)

public section

variable [Labels] {m0 : MachineData} {bp : BitVec 64} {L : Nat}

theorem wide_addr (G : Geo m0 bp L) {j : Nat} (hj : j < 168) :
    off (stackBelow m0 192) (j + 32) = off (stackBelow m0 160) j := by
  have := G.sp
  apply BitVec.eq_of_toNat_eq
  rw [frame_toNat (by omega) G.top (by omega), G.fr hj]
  omega

omit [Labels] in
theorem slotsW_le : ∀ p ∈ slotsW, p.1 + 8 ≤ 192 := by decide

theorem frame_widen (G : Geo m0 bp L) {d : MachineData} {o : Nat} (ho : o < 168)
    (h : Frame m0 160 slots o d) : Frame m0 192 slotsW (o + 32) d := by
  refine ⟨by rw [wide_addr G ho]; exact h.sp, ?_, ?_, h.kept, ?_⟩
  · rintro p hp
    change p ∈ slots.map (fun p ↦ (p.1 + 32, p.2)) at hp
    obtain ⟨p, hp0, rfl⟩ := List.mem_map.mp hp
    dsimp
    rw [wide_addr G (by have := slots_le p hp0; omega)]
    exact h.slot p hp0
  · intro j hj
    rw [show 192 + j = (160 + j) + 32 by omega, wide_addr G (by omega)]
    exact h.ret j hj
  · intro r hr hs
    apply h.regs r hr
    simpa only [slotsW, List.any_map, Function.comp_def] using hs

theorem frame_narrow (G : Geo m0 bp L) {d : MachineData} {o : Nat} (ho : o < 168)
    (h : Frame m0 192 slotsW (o + 32) d) : Frame m0 160 slots o d := by
  refine ⟨by rw [← wide_addr G ho]; exact h.sp, ?_, ?_, h.kept, ?_⟩
  · intro p hp
    rw [← wide_addr G (by have := slots_le p hp; omega)]
    exact h.slot (p.1 + 32, p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · intro j hj
    rw [← wide_addr G (by omega), show 160 + j + 32 = 192 + j by omega]
    exact h.ret j hj
  · intro r hr hs
    apply h.regs r hr
    simpa only [slotsW, List.any_map, Function.comp_def] using hs

theorem wide_wf (G : Geo m0 bp L) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64 := 0) : (frameEnv m0 d 192 [] (fun _ ↦ 0) ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped G.st (by decide)) hk,
    frame_noWrap G.st (by decide)⟩ (by simp) (List.pairwise_singleton _ _)

omit [Labels] in
theorem wide_word {d : MachineData} {fb : BitVec 64} (hsp : rspOf d = fb) {i : Nat}
    {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (off fb (8 + 8 * i)) w) :
    stackArg d i = w.toBitVec := by
  unfold stackArg
  rw [hsp]
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h)

/-- The call's concrete register and stack arguments satisfy `write_openings`'s contract. -/
theorem openings_pre {B : List UInt8} (G : Geo m0 bp B.length) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) (hsp : rspOf d = stackBelow m0 192)
    {nq np lw ht : Nat} (hnq : nq ≤ 256) (hnp : np ≤ 256) (hlw : lw ≤ 64) (hht : ht ≤ 32)
    (hq0 : 0 < nq) (hp0 : 0 < np)
    (hdi : reg d .rdi = WK m0) (hsi : (reg d .rsi).toNat = nq)
    (hdx : reg d .rdx = wa m0 2048) (hcx : (reg d .rcx).toNat = np)
    (hr8 : reg d .r8 = wa m0 352512) (hr9 : (reg d .r9).toNat = lw)
    (ha0 : (stackArg d 0).toNat = ht) (ha1 : stackArg d 1 = wa m0 24832)
    (ha2 : stackArg d 2 = wa m0 24576) (ha3 : stackArg d 3 = OUT m0) :
    WriteOpeningsPre d := by
  have hsp0 := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hon := G.oNw
  have hsW := G.sW
  have hsO := G.sO
  have hoW := G.oW
  have hWS : writeOpeningsStack = 160 := rfl
  have hw0 := G.wa (o := 0) (by omega)
  have hw2 := G.wa (o := 2048) (by omega)
  have hwL := G.wa (o := 352512) (by omega)
  have hwS := G.wa (o := 24832) (by omega)
  have hwC := G.wa (o := 24576) (by omega)
  have hs := stackBelow_toNat (m := m0) (n := 192) (by omega)
  have ha : (off (rspOf d) 8).toNat = SP0 m0 - 184 := by
    rw [hsp, frame_toNat (by omega) G.top (by omega)]
    omega
  obtain ⟨hcs, -⟩ := callee_toNat (n := writeOpeningsStack) hsp (by rw [hWS]; omega)
  have hcs' : (stackBelow d 160).toNat = SP0 m0 - 192 - 160 := hcs
  have hregions : writeOpeningsRegions d =
      [⟨WK m0, 8 * nq⟩, ⟨wa m0 2048, 8 * np⟩, ⟨wa m0 352512, 512 * np⟩,
        ⟨wa m0 24832, 10240 * ht⟩, ⟨wa m0 24576, 8 * ht⟩, ⟨OUT m0, 395288⟩] := by
    simp only [writeOpeningsRegions, hdi, hsi, hdx, hcx, hr8, ha0, ha1, ha2, ha3]
    rfl
  refine ⟨stackOk_callee G.st hk hsp (by rw [hWS]; omega), ?_, hsi ▸ hnq,
    hcx ▸ hnp, hr9 ▸ hlw, ha0 ▸ hht, hsi ▸ hq0, hcx ▸ hp0, ?_, ?_⟩
  · constructor
    · rw [hsp]
      exact mapped_off (N := 200) (o := 8) (k := 32)
        (Mapped.keeps (frame_mapped G.st (by decide)) hk) (by omega)
    · rw [hsp, hs]; omega
  · rw [hregions]
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [wa, off_zero] using wa_ok G hk (o := 0) (n := 8 * nq) (by omega) (by omega)
    · exact wa_ok G hk (by omega) (by omega)
    · exact wa_ok G hk (by omega) (by omega)
    · exact wa_ok G hk (by omega) (by omega)
    · exact wa_ok G hk (by omega) (by omega)
    · exact ⟨Mapped.keeps G.oOk.1 hk, G.oOk.2⟩
  · rw [hregions]
    simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true, NativeRustcVm.Apart, stackR, hWS, hcs', ha, hw2, hwL, hwS, hwC]
    repeat' apply And.intro
    all_goals omega

end

end NativeRustcVmX64.Wire.PhaseM
