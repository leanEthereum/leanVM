import Rv64Verifier.Proofs.Gkr.KeccakDone

/-!
# `keccak::verify_keccak`'s contract

The body's steps in order, every callee's contract a hypothesis.
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.MultilinearContracts Rv64Verifier.FieldContracts

theorem seqD {s u : MachineState} {P : MachineState → Prop}
    (h : ∃ v, Reaches Image.code u v ∧ (P v ∨ Done s v))
    (k : ∀ v, P v → ∃ t, Reaches Image.code v t ∧ Done s t) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  obtain ⟨v, hr, hp | hd⟩ := h
  · obtain ⟨t, hr', ht⟩ := k v hp
    exact ⟨t, hr.trans hr', ht⟩
  · exact ⟨v, hr, hd⟩

theorem seqX {s u : MachineState} {P : MachineState → Prop}
    (h : ∃ v, Reaches Image.code u v ∧ (P v ∨ Dead Image.code v))
    (k : ∀ v, P v → ∃ t, Reaches Image.code v t ∧ Done s t) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  obtain ⟨v, hr, hp | hd⟩ := h
  · obtain ⟨t, hr', ht⟩ := k v hp
    exact ⟨t, hr.trans hr', ht⟩
  · exact ⟨v, hr, Or.inr hd⟩

theorem verify_keccak_spec (hS : SamplesSpec) (hC : SliceConcatSpec) (hEK : EqKernelSpec)
    (hA : AllocSpec) (hR : ReserveFastSpec 0x80008a10) (hMK : MulKSpec) (hD : DotSpec)
    (hM : MulSpec) (hNS : NextScalarSpec) (hVL : VerifyLayerSpec)
    (hMC : Runtime.MemcpySpec 0x800126e4) (hO : OpenSpec) (hSC : SumcheckSpec)
    (hNSs : NextScalarsSpec) (hME : MleEvalSpec) : VerifyKeccakSpecW := by
  intro s hpc hpre
  obtain ⟨u, hr, P, hok, hbad⟩ := prologue hpre hpc
  suffices k : ∃ t, Reaches Image.code u t ∧ Done s t by
    obtain ⟨t, hr', ht⟩ := k
    exact ⟨t, hr.trans hr', ht⟩
  by_cases h : OK s
  swap
  · exact sizes_err hpre P (hbad h) h
  refine seqX (to_seg hS hpre P h (hok h)) fun _ A ↦ ?_
  refine seqX (to_point hC hpre A) fun _ A ↦ ?_
  refine seqX (to_lanePoint hS hpre A) fun _ A ↦ ?_
  refine seqX (to_lanes hEK hpre A) fun _ A ↦ ?_
  refine seqX (to_wbuf hA hR hpre A) fun _ A ↦ ?_
  refine seqX (to_weights hMK hpre A) fun _ A ↦ ?_
  refine seqX (to_eqseg hEK hpre A) fun _ A ↦ ?_
  refine seqX (to_last hD hM hpre A) fun _ A ↦ ?_
  refine seqD (to_committed hNS hpre A) fun _ ⟨_, A⟩ ↦ ?_
  refine seqX (to_claim hEK hpre A) fun _ A ↦ ?_
  refine seqD (to_loop hVL hMC hpre A) fun _ ⟨_, A⟩ ↦ ?_
  refine seqD (loop hVL hMC hpre 11 1 _ _ rfl A) fun _ ⟨_, A⟩ ↦ ?_
  refine seqD (to_row hO hMC hpre A) fun _ ⟨_, _, _, _, _, A⟩ ↦ ?_
  refine seqD (to_checked hNS hM hpre A) fun _ ⟨_, A⟩ ↦ ?_
  refine seqX (to_concat hC hpre A) fun _ A ↦ ?_
  refine seqD (to_low hSC hpre A) fun _ ⟨_, _, _, _, A⟩ ↦ ?_
  refine seqD (to_slices hO hMC hNSs hpre A) fun _ ⟨_, _, _, _, _, _, _, _, _, A⟩ ↦ ?_
  refine seqD (to_check2 hME hpre A) fun _ ⟨_, A⟩ ↦ ?_
  refine seqD (to_dotmul hD hM hpre A) fun _ A ↦ ?_
  refine seqD (to_cmp hpre A) fun _ A ↦ ?_
  refine seqD (to_done hC hpre A) fun _ ⟨_, _, _, A⟩ ↦ ?_
  exact finish hpre A

/-- `VerifyKeccakSpec` from the contract with `a7` free. -/
theorem spec_of_w (h : VerifyKeccakSpecW) : VerifyKeccakSpec := fun s hpc hp ↦ by
  have e : kOutputLen s = 25 := hp.outputLen
  have ho : Region (kOutput s) (24 * 25) := (e ▸ hp.output).resolve_left (by decide)
  obtain ⟨t, hr, ht⟩ := h s hpc
    { toTPre := hp.toTPre, depth := hp.depth, checked := hp.checked, inst := hp.inst, output := ho,
      instFree := Or.inr hp.instFree, outputFree := e ▸ hp.outputFree,
      instStack := hp.instStack, outputStack := e ▸ hp.outputStack, instOut := hp.instOut,
      outputOut := e ▸ hp.outputOut, instSelf := hp.instSelf, outputSelf := e ▸ hp.outputSelf }
  refine ⟨t, hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, c.heap, c.mono, fun T hT ↦ ?_, c.frame⟩⟩
  rw [e]
  exact c.value T hT

end Rv64Verifier.Gkr.Keccak
