module

public import NativeRustcVmArm.KeccakGkr.KeccakPhase.Steps
public import NativeVm.Equiv.KeccakRmfe

/-!
# `keccak_phase`: `verify_keccak`'s precondition

In a state of the frame without outputs written (`Fr … (fun _ ↦ False)`): the entry's bytes apart
from the stack (`bytes_keep`), the `TState` (`ts_keep`), the read-only data (`rc_keep`,
`project_keep`, `rho_keep`), and `verify_keccak`'s footprint (`areas_vk`): the outputs, its
stack below the frame, `KECCAK`'s point in the evaluations, the output lanes in the frame.
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakPhase

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region InAny)

public section

theorem ok_keep {d d' : DataMem} {r : Region} (h : r.Ok d) (hk : Kept d d') : r.Ok d' :=
  ⟨Mapped.kept' h.1 hk, h.2⟩

section
variable [Labels] {a : DecArea} {m0 m : MachineData} {outs' : BitVec 64 → Prop}

/-- **Bytes apart from the stack** are the entry's. -/
theorem bytes_keep (hn : Nums a m0)
    (hfr : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m) {A : BitVec 64}
    {bs : List UInt8} (h : NativeRustcVm.BytesAt m0.dmem A bs)
    (hW : A.toNat + bs.length ≤ 2 ^ 64)
    (hA : A.toNat + bs.length ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ A.toNat) :
    NativeRustcVm.BytesAt m.dmem A bs :=
  NativeRustcVm.Layout.BytesAt.of_same h (same_m0 hn hfr hW hA) le_rfl

/-- **Bytes of the evaluations** are the entry's. -/
theorem evals_keep (hn : Nums a m0)
    (hfr : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m) {o : Nat}
    {bs : List UInt8}
    (h : NativeRustcVm.BytesAt m0.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 o) bs)
    (hle : o + bs.length ≤ 11808) (ho : o < 11808) :
    NativeRustcVm.BytesAt m.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 o) bs := by
  have hW := hn.eW
  have hS := hn.eS
  have e : (m0.regs.X2.toBitVec + BitVec.ofNat 64 o).toNat = m0.regs.X2.toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by rw [UInt64.toNat_toBitVec]; omega)
  exact bytes_keep hn hfr h (by rw [e]; omega) (by rw [e]; omega)

theorem sb_toNat (hn : Nums a m0) (hfr : Fr m0 480 keccakPhaseStack slots keep outs' m) :
    (stackBelow m verifyKeccakStack).toNat = m0.regs.SP.toNat - 7488 := by
  have := hn.hN
  rw [vk_stack_eq, stackBelow_eq hfr.sp (by omega), base_toNat (by omega)]

/-- **The `TState`** stays. -/
theorem ts_keep (hn : Nums a m0) (hfr : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m)
    {s : TState} (h : TStateAt m0.dmem m0.regs.X0.toBitVec a s) :
    TStateAt m.dmem m0.regs.X0.toBitVec a s := by
  refine h.frame hfr.kept (fun q hq ↦ ?_) hfr.same
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  rcases hq with hq | hq
  · have hbN : (base m0 keccakPhaseStack).toNat = m0.regs.SP.toNat - 7488 := by
      rw [stack_eq]; exact base_toNat hN
    rw [Sym.inRange_iff (by rw [hbN, stack_eq]; omega), hbN, stack_eq] at hq
    have := hn.tS; have := hn.tW; have := hn.wS; have := hn.wW
    refine ⟨fun h1 ↦ ?_, fun h1 ↦ ?_⟩
    · rw [NativeRustcVm.inRange_iff (by
        unfold NativeRustcVm.NoWrap tstateBytes; rw [UInt64.toNat_toBitVec]; omega)] at h1
      simp only [UInt64.toNat_toBitVec, tstateBytes] at h1; omega
    · rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega)] at h1; omega
  · exact hq.elim

theorem rc_keep (hn : Nums a m0) (hfr : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m)
    (h : RcAt m0 keccakPhaseStack) : RcAt m verifyKeccakStack := by
  have hl : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 := by
    rw [NativeRustcVm.length_wordsBytes]; rfl
  refine ⟨bytes_keep hn hfr h.1 (by rw [hl]; exact hn.rcW) (by rw [hl]; exact hn.rcS), h.2.1, ?_⟩
  unfold Apart; rw [sb_toNat hn hfr, vk_stack_eq]; have := hn.rcS; have := hn.hN; omega

theorem project_keep (hn : Nums a m0)
    (hfr : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m) (h : ProjectAt m0) :
    ProjectAt m := by
  have hl : (rmfeProjectW.toList.flatMap NativeRustcVm.wordBytes).length = 128 := by
    rw [NativeRustcVm.length_wordsBytes]
    simp [rmfeProjectW, NativeVm.Equiv.rmfeProject_length]
  exact bytes_keep hn hfr h (by rw [hl]; exact hn.pjW) (by rw [hl]; exact hn.pjS)

theorem rho_keep (hn : Nums a m0)
    (hfr : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m) (h : RhoAt m0) :
    RhoAt m := by
  have hl : rhoBytes.length = 100 := by decide
  exact bytes_keep hn hfr h (by rw [hl]; exact hn.rhW) (by rw [hl]; exact hn.rhS)

omit [Labels] in
theorem ap_frame {x n o sp : Nat} (ho : o = sp - 480) (hN : 7488 ≤ sp)
    (h : x + n ≤ sp - 7488 ∨ sp ≤ x) : x + n ≤ o ∨ o + 16 * 25 ≤ x := by
  omega

/-- A byte of a region apart from the stack is not the frame's. -/
theorem not_frame (hn : Nums a m0) {A : BitVec 64} {n : Nat} (hW : A.toNat + n ≤ 2 ^ 64)
    (hS : A.toNat + n ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ A.toNat) {q : BitVec 64}
    (hq : NativeRustcVm.InRange A n q) : ¬InRange (fb m0) 480 q := by
  intro hf
  have := hn.hN
  have := m0.regs.SP.toNat_lt
  rw [NativeRustcVm.inRange_iff hW] at hq
  rw [Sym.inRange_iff (by rw [fb_toNat hn]; omega), fb_toNat hn] at hf
  omega

/-- The outputs are apart from the frame. -/
theorem outs_frame (hn : Nums a m0) : ∀ q, outs m0 q → ¬InRange (fb m0) 480 q := by
  rintro q ⟨w, hw, hq⟩
  simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact not_frame hn hn.tW hn.tS hq
  · exact not_frame hn hn.sW hn.sS hq
  · exact not_frame hn hn.cW hn.cS hq
  · exact not_frame hn hn.oW hn.oS hq

omit [Labels] in
theorem e_ts : tstateBytes = 760 := rfl
omit [Labels] in
theorem e_sc : scratchBytes = 205824 := rfl
omit [Labels] in
theorem e_cl : NativeRustcVm.Layout.claimsBytes = 97288 := by decide
omit [Labels] in
theorem e_out : outBytes = 1608 := rfl

/-- **`verify_keccak`'s footprint.** -/
theorem areas_vk (hn : Nums a m0)
    (hA : Areas m0 keccakPhaseStack (wsOf m0) (rsOf a m0))
    (hfr : Fr m0 480 keccakPhaseStack slots keep outs' m) {np : Nat} (hnp : np ≤ 30)
    {ip op : BitVec 64} (hip : ip.toNat = m0.regs.X2.toNat + 9848)
    (hipm : Mapped m.dmem ip (16 * np)) (hop : op.toNat = m0.regs.SP.toNat - 480)
    (hopm : Mapped m.dmem op 400) :
    Areas m verifyKeccakStack (wsOf m0)
      [a.region, ewsRegion ip np, ewsRegion op 25, rcRegion, projectRegion, rhoRegion] := by
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hsb : (stackBelow m 7008).toNat = m0.regs.SP.toNat - 7488 := by
    rw [← vk_stack_eq]; exact sb_toNat hn hfr
  have hX2 := hn.eW
  refine ⟨fun r hr ↦ ?_, List.pairwise_cons.mpr ⟨fun w hw ↦ ?_, (List.pairwise_cons.mp hA.2.1).2⟩,
    fun w hw r hr ↦ ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact ok_keep (Areas.ok hA (.inl hr)) hfr.kept
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok_keep (Areas.ok hA (.inr (by simp))) hfr.kept
      · exact ⟨hipm, by show ip.toNat + 16 * np ≤ _; omega⟩
      · exact ⟨hopm, by show op.toNat + 16 * 25 ≤ _; omega⟩
      · exact ok_keep (Areas.ok hA (.inr (by simp))) hfr.kept
      · exact ok_keep (Areas.ok hA (.inr (by simp))) hfr.kept
      · exact ok_keep (Areas.ok hA (.inr (by simp))) hfr.kept
  · simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hw
    unfold NativeRustcVm.Apart stackRegion
    rcases hw with rfl | rfl | rfl | rfl
    all_goals simp only [hsb, UInt64.toNat_toBitVec, e_ts, e_sc, vk_stack_eq, e_cl, e_out]
    all_goals first
      | (have := hn.tS; omega)
      | (have := hn.sS; omega)
      | (have := hn.cS; omega)
      | (have := hn.oS; omega)
  · simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hw hr
    unfold Apart
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [hsb, hip, UInt64.toNat_toBitVec, vk_stack_eq, e_ts, e_sc, e_cl,
      e_out, stackRegion, ewsRegion, DecArea.region, rcRegion, projectRegion, rhoRegion]
    · have := hn.wS; omega
    · have := hn.eS; omega
    · omega
    · have := hn.rcS; omega
    · have := hn.pjS; omega
    · have := hn.rhS; omega
    · have := hn.t_w; omega
    · have := hn.t_e; omega
    · exact ap_frame hop hn.hN hn.tS
    · have := hn.t_rc; omega
    · have := hn.t_pj; omega
    · have := hn.t_rh; omega
    · have := hn.s_w; omega
    · have := hn.s_e; omega
    · exact ap_frame hop hn.hN hn.sS
    · have := hn.s_rc; omega
    · have := hn.s_pj; omega
    · have := hn.s_rh; omega
    · have := hn.c_w; omega
    · have := hn.c_e; omega
    · exact ap_frame hop hn.hN hn.cS
    · have := hn.c_rc; omega
    · have := hn.c_pj; omega
    · have := hn.c_rh; omega
    · have := hn.o_w; omega
    · have := hn.o_e; omega
    · exact ap_frame hop hn.hN hn.oS
    · have := hn.o_rc; omega
    · have := hn.o_pj; omega
    · have := hn.o_rh; omega

end

end

end NativeRustcVmArm.KeccakGkr.KeccakPhase
