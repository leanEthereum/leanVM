import Rv64Verifier.Proofs.Pcs.VsoOpenings

/-!
# `VsoPre`'s openings give `VsoOpenMem`, and `Transcript.OpeningsAt` gives `VsoOpeningsAt`

`VsoPre.openMem` places the openings for a function writing at most the free heap, `NEXT`, the
stack, the sponge and the root: that is `VsoOpenMem` (`vsoOpenMem_of`). Both read a sibling as 32
bytes (`digestBytesAt`), so `Transcript.OpeningsAt` is `VsoOpeningsAt`'s `count` and `phases`
(`vsoOpeningsAt_of`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol
  LeanVM.Protocol.Compile

/-- **The openings' memory, from `VsoPre`.** -/
theorem vsoOpenMem_of {s : MachineState} (hpre : VsoPre s) : VsoOpenMem s (s.getReg .x10) := by
  have hO := hpre.openMem
  refine ⟨hO.mapped.buf, fun i hi ↦ (hO.mapped.phases i hi).buf,
    fun i hi j hj ↦ ⟨((hO.mapped.phases i hi).paths j hj).leaf,
      ((hO.mapped.phases i hi).paths j hj).siblings⟩, fun y hy ↦ ?_⟩
  have h := hO.apart y hy
  simp only [not_or, not_and, not_lt] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h3, h2, h4, h5⟩
  by_cases hl : heapNext s ≤ y.toNat
  · exact Or.inr (h1 hl)
  · exact Or.inl (by omega)

/-- A `MerklePath` that `PathAt` reads is `openingAt`'s. -/
theorem openingAt_of_pathAt {s : MachineState} {a : Word} {o : Opening} (h : PathAt s a o) :
    openingAt s a = o := by
  obtain ⟨li, leaf, path⟩ := o
  obtain ⟨hl, hp, hi⟩ := h
  dsimp only at hl hp hi
  simp only [openingAt]
  congr 1
  rw [← hl, kListAt, vecWords, readWords_eq_map, List.map_map]
  rfl

/-- **`VsoOpeningsAt` from `Transcript.OpeningsAt`**, given the openings' memory. -/
theorem vsoOpeningsAt_of {s : MachineState} {p : Word} {T : Model.TState}
    (hO : Transcript.OpeningsAt s p T) (hM : VsoOpenMem s p) : VsoOpeningsAt s p T := by
  refine { toVsoOpenMem := hM, count := hO.len, phases := fun i hi ↦ ?_ }
  have hph := hO.phases i hi
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  unfold phaseAt
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]; exact hph.len
  · intro j hj1 hj2
    rw [List.getElem_map, List.getElem_range]
    exact openingAt_of_pathAt (hph.paths j hj2)

end Rv64Verifier.Proofs.Pcs.Vso
