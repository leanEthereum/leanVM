import Rv64Verifier.Proofs.Multilinear.MleEval
import Rv64Verifier.Proofs.Bus.VbbContracts
import Rv64Verifier.Proofs.Gkr.Contracts

/-!
# Other agents' copies of the multilinear contracts, from these

`Bus.Vbb.MleEvalSpec` reads its slices as `Held` (valid doublewords, free, off the stack), where
`MleEvalSpec` asks for `Region`s: `memcpy`'s contract maps its source below `0xc0000000`, and a
`Held` slice may end at `0xc0000008`. `mleEval_vbb` gives the copy with that bound added
(`MleEnds`). `Gkr.OptFromElemSpec` is `Bus.OptFromElemSpec` with a doubleword frame.
-/

namespace Rv64Verifier.Proofs.Multilinear.Bridges
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts

/-- A slice read only, of two doublewords or more, ending below `0xc0000000`, is a region. -/
theorem region_of_held {s : MachineState} {n : Nat} {a : Word} {m : Nat} (h : Bus.Held s n a m)
    (hh : heapNext s ≤ heapEnd) (hm : 16 ≤ m) (h8 : m % 8 = 0) (htop : a.toNat + m ≤ 0xc0000000) :
    Transcript.Region a m := by
  have hb := ValidMemRange.bounds h.valid (by omega)
  have h0 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h.valid 0 (by omega)))
  have h1 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h.valid 1 (by omega)))
  simp only [Nat.mul_zero, BitVec.add_zero] at h0
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * 1) (by norm_num),
    Nat.mod_eq_of_lt (by omega)] at h1
  have hf := h.free
  simp only [Outside, heapNext, heapEnd] at hf hh
  refine ⟨?_, hb.2.1⟩
  simp only [Mapped]
  omega

/-- The ends of `multilinear_eval`'s slices, below `0xc0000000` unless empty. -/
def MleEnds (s : MachineState) : Prop :=
  ((s.getReg .x12).toNat = 0 ∨ (s.getReg .x11).toNat + 24 * (s.getReg .x12).toNat ≤ 0xc0000000) ∧
    ((s.getReg .x14).toNat = 0 ∨ (s.getReg .x13).toNat + 24 * (s.getReg .x14).toNat ≤ 0xc0000000)

/-- `Bus.Vbb.MleEvalSpec`, for slices ending below `0xc0000000`. -/
theorem mleEval_vbb (h : MleEvalSpec) :
    FunSpec Image.code 0x8000d28c (fun s ↦ Bus.Vbb.MleEvalPre s ∧ MleEnds s)
      Bus.Vbb.MleEvalPost := by
  intro s hpc ⟨hp, he⟩
  have hh := hp.heap.hi
  have reg {a : Word} {k : Nat} (hk : Bus.Held s Bus.Vbb.mleEvalStack a (24 * k))
      (hend : k = 0 ∨ a.toNat + 24 * k ≤ 0xc0000000) : k = 0 ∨ Transcript.Region a (24 * k) := by
    by_cases h0 : k = 0
    · exact Or.inl h0
    · exact Or.inr (region_of_held hk hh (by omega) (by omega) (hend.resolve_left h0))
  have hpre : MleEvalPre s := {
    heap := hp.heap
    out := hp.out
    mle := reg hp.mle he.1
    point := reg hp.point he.2
    stack := hp.stack
    outFree := hp.outFree
    mleFree := Or.inr hp.mle.free
    pointFree := Or.inr hp.point.free
    outStack := hp.outStack
    mleStack := hp.mle.stack
    pointStack := hp.point.stack
    mleOut := hp.mleOut
    pointOut := hp.pointOut
    rodata := hp.rodata
    outRodata := hp.outRodata }
  obtain ⟨t, hr, ⟨hpc', hpres, hpost⟩ | hd⟩ := h s hpc hpre
  · refine ⟨t, hr, Or.inl ⟨hpc', hpres, {
      heap := hpost.heap
      mono := hpost.mono
      value := ?_
      frame := hpost.frame }⟩⟩
    have hv := hpost.value
    split
    · rename_i v hv'
      rw [hv'] at hv
      exact hv
    · rename_i hv'
      rw [hv'] at hv
      rw [hv]
      decide
  · exact ⟨t, hr, Or.inr hd⟩

/-- `Gkr.OptFromElemSpec` from `Bus.OptFromElemSpec`: the same precondition, a weaker frame. -/
theorem optFromElem_gkr (h : Bus.OptFromElemSpec) : Gkr.OptFromElemSpec := by
  intro s hpc hp
  obtain ⟨t, hr, ⟨hpc', hpres, hpost⟩ | hd⟩ := h s hpc {
    heap := hp.heap
    out := hp.out
    elem := hp.elem
    stack := hp.stack
    outFree := hp.outFree
    outStack := hp.outStack
    elemFree := hp.elemFree
    elemStack := hp.elemStack
    elemOut := hp.elemOut }
  · exact ⟨t, hr, Or.inl ⟨hpc', hpres, {
      heap := hpost.heap
      mono := hpost.mono
      vec := hpost.vec
      len := hpost.len
      elems := hpost.elems
      fresh := hpost.fresh
      frame := Transcript.DFrame.of_byteFrame hpost.frame }⟩⟩
  · exact ⟨t, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Multilinear.Bridges
