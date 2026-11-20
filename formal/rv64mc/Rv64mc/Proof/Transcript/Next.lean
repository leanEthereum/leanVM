/-
  Rv64mc.Proof.Transcript.Next

  `Transcript::next` keeps its contract (`Spec.Transcript.Next.spec`), over any program holding its template.
  `rv_auto` runs both paths; what is left is the frame of the stores into the slot and the stream offset, and the
  mirror's step (`Model.TM.next`): the comparison with the stream's length, the element read through the proof
  (`ProofAt.stream_elem`), and the transcript with its offset advanced (`TranscriptAt.setStream`), kept by the
  slot's stores.
-/

import Rv64mc.Spec.Transcript.Next
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.Next
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.Next

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Next
open Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Transcript.Next (Link tmpl)

/-- The mirror's step where the offset is past the stream. -/
theorem next_none {t : Model.TState} (h : t.proof.stream.length ≤ t.streamOffset) : Model.TM.next.run t = none := by
  simp only [StateT.run, Model.TM.next, List.getElem?_eq_none h]

/-- The mirror's step where the offset is within the stream. -/
theorem next_some {t : Model.TState} (h : t.streamOffset < t.proof.stream.length) :
    Model.TM.next.run t = some (t.proof.stream[t.streamOffset], { t with streamOffset := t.streamOffset + 1 }) := by
  simp only [StateT.run, Model.TM.next, List.getElem?_eq_getElem h]

/-- **`Transcript::next` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (_hL : L.WF p)
    {need : Nat} : spec env p i need := by
  intro t
  rv_auto hp
  all_goals
    rw [hpre_2] at hpre_7 hpre_9
    simp only [Layouts.Transcript.byteSize, Layouts.ResultE.byteSize, Layouts.Proof.byteSize, proofAddr,
      Layouts.Transcript.proof] at hpre_8 hpre_10 hpre_11 hpre_12
    have hlim : env.stackLimit.toNat ≤ top.toNat := Nat.le_trans (Nat.le_add_right _ _) hpre_3
    have hT := hpre_6
    obtain ⟨hle, -, -, hpf, -, hso, -, -⟩ := hpre_6
    simp only [Layouts.Transcript.proof, Layouts.Transcript.stream_offset] at hpf hso
    obtain ⟨hlen, hlt⟩ := hpf.stream_len
    rw [hso, hlen] at hc
  -- the offset past the stream: `Err`
  · exact frame_store_out (frame_store_out (Env.Frame.refl hpre_5) hlim hpre_9 (Or.inl (inRange_self (by decide))))
      hlim (Nat.le_trans hpre_9 (toNat_le_add (n := 24) hpre_10 (by decide)))
      (Or.inl (inRange_add (k := 8) hpre_10 (by decide)))
  · exact static_store (static_store hpre_4 hlim hpre_9) hlim
      (Nat.le_trans hpre_9 (toNat_le_add (n := 24) hpre_10 (by decide)))
  · rw [next_none ((ofNat_le_iff (by omega) (by omega)).1 hc)]
    simp only [ResultEAt, Layouts.ResultE.tagOffset, Layouts.ResultE.Err.tag, BitVec.add_zero]
    rw [MachineState.getMem_setMem_ne (ne_add_self (n := 24) hpre_10 (by decide) (by decide)),
      MachineState.getMem_setMem_eq]
  -- within the stream: `Ok`
  all_goals
    have hlt' : t.streamOffset < t.proof.stream.length := (ofNat_lt_iff (by omega) (by omega)).1 hc
    have h8 := toNat_le_add (k := 8) (n := 24) hpre_10 (by decide)
    have h16 := toNat_le_add (k := 16) (n := 24) hpre_10 (by decide)
    have h336 := toNat_le_add (k := 336) (n := 360) hpre_8 (by decide)
  · exact frame_store_out (frame_store_out (frame_store_out (frame_store_out (Env.Frame.refl hpre_5) hlim
      (Nat.le_trans hpre_7 h336) (Or.inr rfl)) hlim (Nat.le_trans hpre_9 h16)
      (Or.inl (inRange_add hpre_10 (by decide)))) hlim hpre_9 (Or.inl (inRange_self (by decide))))
      hlim (Nat.le_trans hpre_9 h8) (Or.inl (inRange_add hpre_10 (by decide)))
  · exact static_store (static_store (static_store (static_store hpre_4 hlim (Nat.le_trans hpre_7 h336)) hlim
      (Nat.le_trans hpre_9 h16)) hlim hpre_9) hlim (Nat.le_trans hpre_9 h8)
  · rw [next_some hlt']
    obtain ⟨e0, e1⟩ := hpf.stream_elem hlt'
    have hne08 := ne_add_self (k := 8) (n := 24) hpre_10 (by decide) (by decide)
    have hne016 := ne_add_self (k := 16) (n := 24) hpre_10 (by decide) (by decide)
    have hne816 := add_ne_add (j := 16) (k := 8) (n := 24) hpre_10 (by decide) (by decide) (by decide)
    have h1 := hT.setStream hpre_8 (Nat.le_trans hlim hpre_7) hpre_5 (o := t.streamOffset + 1) (by omega)
    have hnx1 := hpre_5
    rw [← Env.next_setMem_stack (a := regs .x11 + BitVec.ofNat 64 Layouts.Transcript.stream_offset)
      (v := BitVec.ofNat 64 (t.streamOffset + 1)) (Nat.le_trans hlim (Nat.le_trans hpre_7 h336))] at hnx1
    simp only [Layouts.Transcript.stream_offset] at h1 hnx1
    rw [hso, ofNat_succ]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [Layouts.ResultE.tagOffset, Layouts.ResultE.Ok.tag, BitVec.add_zero]
      rw [MachineState.getMem_setMem_ne hne08, MachineState.getMem_setMem_eq]
    · simp only [Layouts.ResultE.Ok.f0, Layouts.E.c0, BitVec.add_zero]
      rw [MachineState.getMem_setMem_eq, e0]
    · simp only [Layouts.ResultE.Ok.f0, Layouts.E.c1]
      rw [show regs .x10 + 8#64 + 8#64 = regs .x10 + 16#64 by rw [BitVec.add_assoc]; rfl,
        MachineState.getMem_setMem_ne hne816, MachineState.getMem_setMem_ne hne016.symm,
        MachineState.getMem_setMem_eq, e1]
    · refine h1.keep hpre_8 ?_ ?_ ?_
      · exact keeps_store (keeps_store (keeps_store keeps_refl (not_inRange_apart' hpre_11 hpre_10 (by decide))
          ) (not_inRange_apart0 hpre_11 (by decide))) (not_inRange_apart' hpre_11 hpre_10 (by decide))
      · rw [MachineState.getMem_setMem_ne (add_ne_add (n := 360) (j := 328) (k := 336) hpre_8 (by decide) (by decide)
          (by decide))]
        exact keeps_store (keeps_store (keeps_store keeps_refl (not_inRange_apart' hpre_12 hpre_10 (by decide))
          ) (not_inRange_apart0 hpre_12 (by decide))) (not_inRange_apart' hpre_12 hpre_10 (by decide))
      · exact heapKept_store (heapKept_store (heapKept_store heapKept_refl (Nat.le_trans hlim hpre_9)
          h16 hnx1) (Nat.le_trans hlim hpre_9) (Nat.le_refl _) hnx1)
          (Nat.le_trans hlim hpre_9) h8 hnx1

end Rv64mc.Proof.Transcript.Next
