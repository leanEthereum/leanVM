module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Body

/-! # `keccak_open`: the `slot_weights` call's memory contract -/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero toNat_off Mapped.keeps bytesAt_congr DecArea)

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 d : MachineData}

theorem slot_pre (h : PreOk a s c m0) (hb : Body m0 0 d)
    (hdi : reg d .rdi = reg m0 .rdx) (hsi : reg d .rsi = reg m0 .rcx)
    (hdx : reg d .rdx = reg m0 .r8) (hcx : reg d .rcx = reg m0 .r9)
    (h8 : reg d .r8 = openFirst m0) (h9 : reg d .r9 = openCount m0)
    (harg : stackArg d 0 = rwA m0) : SlotWeightsPre c d := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.w; have := hn.q; have := hn.b
  have := hn.sw; have := hn.sq; have := hn.sb; have := hn.wq; have := hn.wb
  have hfb := fbA_toNat h
  have hat := hb.at h
  have hle : 2208 + slotWeightsStack ≤ keccakOpenStack := by decide
  have hsp : rspOf d = fbA m0 := hat.sp
  have hargN : (rspOf d + 8#64).toNat = (rspOf m0).toNat - 2208 + 8 := by
    rw [hsp]
    exact fb_off h (by decide)
  have hstN : (stackBelow d slotWeightsStack).toNat =
      (rspOf m0).toNat - 2208 - slotWeightsStack := by
    have hstack : slotWeightsStack ≤ 992 := by decide
    rw [stackBelow_toNat (by rw [hsp, hfb]; omega), hsp, hfb]
  have ptkept : NativeRustcVm.EWsAt d.dmem (reg m0 .rcx) c.point.toList := by
    refine bytesAt_congr h.pt fun i hi ↦ read_kept h hb.same (.tail _ (.head _)) ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at hi
    change NativeRustcVm.InRange (reg m0 .rcx) (16 * c.point.size) _
    exact NativeRustcVm.Transcript.inRange_off_self hi (by omega)
  have wtkept : NativeRustcVm.KeccakGkr.WeightsAt d.dmem (reg m0 .r9) c := by
    refine ⟨h.wt.1, bytesAt_congr h.wt.2 fun i hi ↦ read_kept h hb.same
      (.tail _ (.tail _ (.head _))) ?_⟩
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, h.wt.1] at hi
    change i < 25600 at hi
    change NativeRustcVm.InRange (reg m0 .r9) 25600 _
    exact NativeRustcVm.Transcript.inRange_off_self hi (by omega)
  unfold SlotWeightsPre slotRows
  rw [hdi, hsi, hdx, hcx, h8, h9, harg]
  refine ⟨(context h).stackOk hat hle, ⟨?_, ?_⟩, h.psz, ptkept, wtkept, h.seg, h.cnt, h.fc, ?_⟩
  · rw [hsp]
    exact mapped_off (o := 8) ((context h).mapped_frame hb.fr.kept) (by decide)
  · rw [hsp, hfb]; omega
  have hrow : (⟨rwA m0, NativeRustcVm.KeccakGkr.rowsBytes⟩ : Region) ∈ wsOf m0 :=
    .tail _ (.tail _ (.tail _ (.head _)))
  have hp : ewsRegion (reg m0 .rcx) c.point.size ∈ rsOf a c m0 := .tail _ (.head _)
  have hw : (⟨reg m0 .r9, NativeRustcVm.KeccakGkr.weightsBytes⟩ : Region) ∈ rsOf a c m0 :=
    .tail _ (.tail _ (.head _))
  refine ⟨?_, List.pairwise_pair.mpr ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have hh := Areas.ok h.areas (List.mem_append_left _ hrow)
      exact ⟨Mapped.keeps hh.1 hb.fr.kept, hh.2⟩
    · have hh := Areas.ok h.areas (List.mem_append_right _ hp)
      exact ⟨Mapped.keeps hh.1 hb.fr.kept, hh.2⟩
    · have hh := Areas.ok h.areas (List.mem_append_right _ hw)
      exact ⟨Mapped.keeps hh.1 hb.fr.kept, hh.2⟩
    · refine ⟨?_, ?_⟩
      · change NativeRustcVm.Mapped d.dmem (rspOf d + 8#64) (8 * 1)
        rw [hsp]
        exact mapped_off (o := 8) ((context h).mapped_frame hb.fr.kept) (by decide)
      · change (rspOf d + 8#64).toNat + 8 * 1 ≤ 2 ^ 64
        rw [hargN]; omega
  · change (stackBelow d slotWeightsStack).toNat + (slotWeightsStack + 8) ≤ (rwA m0).toNat ∨
      (rwA m0).toNat + 65536 ≤ (stackBelow d slotWeightsStack).toNat
    rw [hstN]
    have : slotWeightsStack ≤ 992 := by decide
    omega
  · intro w hw' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw' hr
    rcases hw' with rfl | rfl <;> rcases hr with rfl | rfl | rfl
    · change (stackBelow d slotWeightsStack).toNat + (slotWeightsStack + 8) ≤ (reg m0 .rcx).toNat ∨
        (reg m0 .rcx).toNat + 16 * c.point.size ≤ (stackBelow d slotWeightsStack).toNat
      rw [hstN]
      have hstack : slotWeightsStack ≤ 992 := by decide
      omega
    · change (stackBelow d slotWeightsStack).toNat + (slotWeightsStack + 8) ≤ (reg m0 .r9).toNat ∨
        (reg m0 .r9).toNat + 25600 ≤ (stackBelow d slotWeightsStack).toNat
      rw [hstN]
      have hstack : slotWeightsStack ≤ 992 := by decide
      omega
    · change (stackBelow d slotWeightsStack).toNat + (slotWeightsStack + 8) ≤ (rspOf d + 8#64).toNat ∨
        (rspOf d + 8#64).toNat + 8 ≤ (stackBelow d slotWeightsStack).toNat
      rw [hstN, hargN]
      have hstack : slotWeightsStack ≤ 992 := by decide
      omega
    · exact Areas.apart_read h.areas hrow hp
    · exact Areas.apart_read h.areas hrow hw
    · change (rwA m0).toNat + 65536 ≤ (rspOf d + 8#64).toNat ∨
        (rspOf d + 8#64).toNat + 8 ≤ (rwA m0).toNat
      rw [hargN]; omega

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
