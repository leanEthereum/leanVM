module

public import NativeRustcVm.Wire.Rep
public import NativeVm.Equiv.Basic
import NativeVm.Equiv.Field
import NativeVm.Wire.Read

/-!
# The decoded proof as the model's arrays

`decodeM_toProof`: the proof `decodeM` decodes is the one the arrays `streamW`, `openingsW` of its
result denote (`EW.toE`, `Equiv.phaseOpenings`), every leaf index being below `2 ^ 32`
(`phaseM_leafIndex`).
-/

namespace NativeRustcVm.Wire

open NativeVm NativeVm.Model NativeVm.Wire LeanVM.Parameters LeanVM.Protocol
open LeanVM.Protocol.Compile

public section

theorem rdU32s_lt (B : List UInt8) : ∀ (n c : Nat) {qs : List Nat} {c' : Nat},
    rdU32s B n c = some (qs, c') → ∀ q ∈ qs, q < 2 ^ 32
  | 0, c, qs, c', h => by cases h; simp
  | n + 1, c, qs, c', h => by
    simp only [rdU32s, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨v, c1⟩, h1, ⟨vs, c2⟩, h2, he⟩ := h
    cases he
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact rdU32_lt h1
    · exact rdU32s_lt B n c1 h2 q hq

/-- **The leaf indices** of a decoded phase are its queries, below `2 ^ 32`. -/
theorem phaseM_leafIndex {B : List UInt8} {c : Nat} {po : PhaseOut} {c' : Nat}
    (h : phaseM B c = some (po, c')) : ∀ o ∈ po.openings, o.leafIndex < 2 ^ 32 := by
  unfold phaseM at h
  simp only [Option.bind_eq_bind, Option.bind_none] at h
  obtain ⟨⟨n, c1⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  obtain ⟨⟨qs, c2⟩, hqs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨ht, c3⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨lw, c4⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨rw, c5⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  obtain ⟨⟨rows, c6⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  obtain ⟨⟨sibs, c7⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  intro o ho
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
  exact rdU32s_lt B n c1 hqs q hq

theorem phasesM_leafIndex (B : List UInt8) : ∀ (n c : Nat) {ps : List PhaseOut} {c' : Nat},
    phasesM B n c = some (ps, c') → ∀ po ∈ ps, ∀ o ∈ po.openings, o.leafIndex < 2 ^ 32
  | 0, c, ps, c', h => by cases h; simp
  | n + 1, c, ps, c', h => by
    simp only [phasesM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨p, c1⟩, h1, ⟨qs, c2⟩, h2, he⟩ := h
    cases he
    intro po hpo
    rcases List.mem_cons.mp hpo with rfl | hpo
    · exact phaseM_leafIndex h1
    · exact phasesM_leafIndex B n c1 h2 po hpo

/-- The leaf indices of a decoded proof are below `2 ^ 32`. -/
theorem decodeM_leafIndex {B : List UInt8} {r : List E × List PhaseOut} (h : decodeM B = some r) :
    ∀ po ∈ r.2, ∀ o ∈ po.openings, o.leafIndex < 2 ^ 32 := by
  unfold decodeM at h
  simp only [Option.bind_eq_bind, Option.bind_none] at h
  obtain ⟨⟨s, c1⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨p, c2⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  obtain ⟨⟨ps, c3⟩, hps, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  cases h
  exact phasesM_leafIndex B p c2 hps

theorem toOpening_openingW {o : Opening} (h : o.leafIndex < 2 ^ 64) : (openingW o).toOpening = o := by
  obtain ⟨i, leaf, path⟩ := o
  simp only [openingW, OpeningW.toOpening, List.map_map, List.toList_toArray]
  congr
  · exact Nat.mod_eq_of_lt h
  · exact (List.map_congr_left fun x _ ↦ (rfl : K.ofLane x.lane = x)).trans (List.map_id _)

theorem streamW_toE (s : List E) : (streamW s).toList.map EW.toE = s := by
  simp only [streamW, List.toList_toArray, List.map_map]
  exact (List.map_congr_left fun x _ ↦ Equiv.EW.toE_ofE x).trans (List.map_id _)

/-- **The decoded proof** is the one the arrays `streamW`, `openingsW` of `decodeM`'s result
denote. -/
theorem decodeM_toProof {B : List UInt8} {r : List E × List PhaseOut} (h : decodeM B = some r) :
    toProof r = ⟨(streamW r.1).toList.map EW.toE, (openingsW r.2).toList.map Equiv.phaseOpenings⟩ := by
  have hl := decodeM_leafIndex h
  rw [toProof, streamW_toE]
  congr 1
  simp only [openingsW, List.toList_toArray, List.map_map]
  refine List.map_congr_left fun po hpo ↦ ?_
  simp only [Function.comp, Equiv.phaseOpenings, phaseW, List.toList_toArray, List.map_map]
  refine ((List.map_congr_left fun o ho ↦ ?_).trans (List.map_id _)).symm
  exact toOpening_openingW (by have := hl po hpo o ho; omega)

end

end NativeRustcVm.Wire
