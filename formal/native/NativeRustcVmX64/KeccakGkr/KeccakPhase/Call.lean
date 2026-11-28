module

public import NativeRustcVmX64.KeccakGkr.KeccakPhase.Front
public import NativeVm.Equiv.KeccakRmfe

/-!
# `keccak_phase`: the call of `verify_keccak`

`b2` sets `verify_keccak`'s arguments (`KECCAK`'s point, its count, the lanes in the frame) and
pushes its stack arguments (the claims, the `KeccakOutW`); `vk_pre`: its precondition, from the
entry's facts kept in the frame's states (`same_m0`). After it (`call_vk`), the frame with the
outputs changed (`W2`) and its postcondition.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakPhase NativeRustcVmX64.Transcript
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVmX64.KeccakGkr.Fn
open NativeRustcVm (Region InAny)
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)

public section

variable [Labels] {a : DecArea} {m0 d : MachineData}

/-- **Bytes apart from the stack** stay as at the entry while the code writes the frame only. -/
theorem same_m0 (hn : Nums a m0) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (W1 m0))
    {A : BitVec 64} {n : Nat} (hW : A.toNat + n ≤ 2 ^ 64)
    (hA : Sep A.toNat n (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)) :
    NativeRustcVm.Layout.Same m0.dmem d.dmem A n :=
  same_num hs hW fun q ⟨h1, h2⟩ ↦ by
    have := hn.hB; have := hn.hK; have hKV := kps_eq; unfold Sep at hA; omega

theorem bytes_m0 (hn : Nums a m0) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (W1 m0))
    {A : BitVec 64} {bs : List UInt8} (h : NativeRustcVm.BytesAt m0.dmem A bs)
    (hW : A.toNat + bs.length ≤ 2 ^ 64)
    (hA : Sep A.toNat bs.length (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)) :
    NativeRustcVm.BytesAt d.dmem A bs :=
  NativeRustcVm.Layout.BytesAt.of_same h (same_m0 hn hs hW hA) le_rfl

omit [Labels] in
theorem rc_len : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 := by
  rw [NativeRustcVm.length_wordsBytes]; rfl

omit [Labels] in
theorem pj_len : (rmfeProjectW.toList.flatMap NativeRustcVm.wordBytes).length = 128 := by
  rw [NativeRustcVm.length_wordsBytes]
  simp [rmfeProjectW, NativeVm.Equiv.rmfeProject_length]

omit [Labels] in
theorem rh_len : rhoBytes.length = 100 := by decide

omit [Labels] in
/-- A written region apart from the stack and the evaluations is apart from what the callee reads
in them and in the frame. -/
theorem sep_reads {x n K V B e ip np op ar P : Nat} (hP : P = 480 + V)
    (hS : Sep x n K (P + 8)) (he : Sep x n e 11808) (hB : B = K + V)
    (hip : ip = e + 9848) (hnp : np ≤ 30) (hop : op = B + 32) (har : ar = B + 8) :
    Sep x n ip (16 * np) ∧ Sep x n op (16 * 25) ∧ Sep x n ar (8 * 2) := by
  unfold Sep at *
  omega

omit [Labels] in
theorem sep_stack {x n K N P : Nat} (hS : Sep x n K (P + 8)) (hN : N ≤ P) :
    Sep x n K (N + 8) := by
  unfold Sep at *
  omega

omit [Labels] in
theorem sep_stack' {x n K N P : Nat} (hS : Sep x n K (P + 8)) (hN : N ≤ P) :
    Sep K (N + 8) x n := by
  unfold Sep at *
  omega

/-- **`verify_keccak`'s footprint**: the outputs, its stack below the frame, the regions read:
`KECCAK`'s point in the evaluations, the output lanes and the stack arguments in the frame. -/
theorem areas_vk (hn : Nums a m0) (hA : Areas m0 keccakPhaseStack (wsOf m0)
      [a.region, ⟨reg m0 .rdx, NativeRustcVm.Tables.tableEvalsBytes⟩, rcRegion, projectRegion,
        rhoRegion])
    (hke : Kept m0.dmem d.dmem) {N : Nat}
    (hsb : (stackBelow d N).toNat = (stackBelow m0 keccakPhaseStack).toNat)
    (hN : N + 480 = keccakPhaseStack)
    {ip op ar : BitVec 64} {np : Nat} (hip : ip.toNat = (reg m0 .rdx).toNat + 9848) (hnp : np ≤ 30)
    (hipm : NativeRustcVm.Mapped d.dmem ip (16 * np))
    (hop : op.toNat = (stackBelow m0 480).toNat + 32) (hopm : NativeRustcVm.Mapped d.dmem op 400)
    (har : ar.toNat = (stackBelow m0 480).toNat + 8) (harm : NativeRustcVm.Mapped d.dmem ar 16) :
    Areas d N (wsOf m0)
      [a.region, ewsRegion ip np, ewsRegion op 25, rcRegion, projectRegion, rhoRegion,
        ⟨ar, 8 * 2⟩] := by
  obtain ⟨hB, hK, top, tW, sW, cW, oW, wW, eW, rcW, pjW, rhW, tS, sS, cS, oS, wS, eS, rcS, pjS, rhS,
    ts, tc, tou, sc, so, co, tw, te, trc, tpj, trh, sw, se, src, spj, srh, cw, ce, crc, cpj, crh,
    ow, oe, orc, opj, orh⟩ := hn
  have hKV : keccakPhaseStack = 480 + verifyKeccakStack := kps_eq
  have hBK : (stackBelow m0 480).toNat = (stackBelow m0 keccakPhaseStack).toNat + verifyKeccakStack :=
    by omega
  have hN' : N ≤ keccakPhaseStack := by omega
  have hmw : ∀ r ∈ wsOf m0, NativeRustcVm.Mapped d.dmem r.addr r.size :=
    fun r hr ↦ NativeRustcVm.Transcript.Mapped.keeps (Areas.mapped hA (Or.inl hr)) hke
  have hmr : ∀ r ∈ [a.region, rcRegion, projectRegion, rhoRegion],
      NativeRustcVm.Mapped d.dmem r.addr r.size := by
    intro r hr
    refine NativeRustcVm.Transcript.Mapped.keeps (Areas.mapped hA (Or.inr ?_)) hke
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  clear hA hke
  simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    tsz, ssz, csz, osz] at hmw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    DecArea.region, rcRegion, projectRegion, rhoRegion] at hmr
  have rt := sep_reads hKV tS te hBK hip hnp hop har
  have rs := sep_reads hKV sS se hBK hip hnp hop har
  have rc := sep_reads hKV cS ce hBK hip hnp hop har
  have ro := sep_reads hKV oS oe hBK hip hnp hop har
  refine areas_of ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [wsOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, ewsRegion,
      DecArea.region, rcRegion, projectRegion, rhoRegion, tsz, ssz, csz, osz]
    rintro r ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl))
    exacts [hmw.1, hmw.2.1, hmw.2.2.1, hmw.2.2.2, hmr.1, hipm, hopm, hmr.2.1, hmr.2.2.1,
      hmr.2.2.2, harm]
  · simp only [wsOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, ewsRegion,
      DecArea.region, rcRegion, projectRegion, rhoRegion, tsz, ssz, csz, osz]
    rintro r ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) <;> dsimp only <;>
      omega
  · simp only [wsOf, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, tsz, ssz, csz, osz]
    exact ⟨⟨ts, tc, tou⟩, ⟨sc, so⟩, co, fun _ h ↦ h.elim⟩
  · simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      tsz, ssz, csz, osz, hsb]
    exact ⟨sep_stack tS hN', sep_stack sS hN', sep_stack cS hN', sep_stack oS hN'⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ewsRegion,
      DecArea.region, rcRegion, projectRegion, rhoRegion, hsb]
    refine ⟨sep_stack' wS hN', ?_, ?_, sep_stack' rcS hN', sep_stack' pjS hN', sep_stack' rhS hN', ?_⟩
    all_goals unfold Sep at eS ⊢; omega
  · simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      ewsRegion, DecArea.region, rcRegion, projectRegion, rhoRegion, tsz, ssz, csz, osz]
    exact ⟨⟨tw, rt.1, rt.2.1, trc, tpj, trh, rt.2.2⟩, ⟨sw, rs.1, rs.2.1, src, spj, srh, rs.2.2⟩,
      ⟨cw, rc.1, rc.2.1, crc, cpj, crh, rc.2.2⟩, ⟨ow, ro.1, ro.2.1, orc, opj, orh, ro.2.2⟩⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakPhase
