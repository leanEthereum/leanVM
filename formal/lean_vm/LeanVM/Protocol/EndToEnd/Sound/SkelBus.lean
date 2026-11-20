/-
  LeanVM.Protocol.EndToEnd.Sound.SkelBus

  The bus phase's skeleton: fixed by the push side's depth.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelLeaves
import LeanVM.Protocol.Verifier.Claims

/-!
# The bus phase's skeleton

The GKR step's skeleton is fixed by its levels and the length of the point it starts at, which
grows by the levels (`skel_gkrStep`); the walk's, by its depth (`skel_gkrLayers`); the bus
phase's, by the push side's depth (`skel_verifyBusBalance`), the bytecode's value checked without
a transcript operation (`computedBytecodeValue`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier

@[expose] public section

/-- The skeleton of a GKR step of `step` levels from a point of `L` coordinates. -/
def skGkrStep (step : ℕ) (last : Bool) (L : ℕ) : List Op :=
  skGrind (grindingBits (nTrees - 1)) ++ [.sample] ++ skSum (2 ^ step + 1) (List.replicate L true) ++
    List.replicate (2 ^ step) .read ++ List.replicate (2 ^ step) .read ++
    List.replicate (2 ^ step) .read ++ skGrind (grindingBits (if last then 2 * step else step)) ++
    List.replicate step .sample

theorem map_isSome_map_some (l : List E) :
    (l.map some).map Option.isSome = List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

theorem skel_gkrStep (step : ℕ) (last : Bool) (s : GkrState) :
    SkelP (gkrStep step last s) (skGkrStep step last s.point.length)
      fun t ↦ t.point.length = step + s.point.length := by
  unfold gkrStep
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine ((skel_grindProofOfWork _).bind fun _ _ ↦ skel_sampleChallenge.bind fun c _ ↦
    (skel_sumcheck _ _ (s.point.map some)).bind fun r hr ↦
    (skel_readScalars _).bind fun c0 _ ↦ (skel_readScalars _).bind fun c1 _ ↦
    (skel_readScalars _).bind fun c2 _ ↦ (skel_require _).bind fun _ _ ↦
    (skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallenges step).bind fun y hy ↦
    SkelP.ret (Q := fun t : GkrState ↦ t.point.length = step + s.point.length)
      (by simp only [List.length_map] at hr; simp [hy, hr])).mono ?_ fun _ h ↦ h
  simp only [skGkrStep, map_isSome_map_some, List.append_assoc, List.append_nil, List.nil_append]

/-- The skeleton of the GKR walk over `n` levels from a point of `L` coordinates. -/
def skGkrLayers : ℕ → ℕ → List Op
  | 0, _ => []
  | 1, L => skGkrStep 1 true L
  | n + 2, L => if n % 2 = 1 then skGkrStep 1 false L ++ skGkrLayers (n + 1) (1 + L)
      else skGkrStep 2 (n = 0) L ++ skGkrLayers n (2 + L)

theorem skel_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    SkelP (gkrLayers n s) (skGkrLayers n s.point.length) fun _ ↦ True
  | 0, _ => SkelP.ret trivial
  | 1, s => by
    simp only [gkrLayers, VerifierProgram.bind_eq]
    refine ((skel_gkrStep 1 true s).bind fun t _ ↦ SkelP.ret trivial).mono ?_ fun _ h ↦ h
    simp [skGkrLayers]
  | n + 2, s => by
    simp only [gkrLayers, VerifierProgram.bind_eq]
    split
    · refine ((skel_gkrStep 1 false s).bind fun t ht ↦
        (skel_gkrLayers (n + 1) t).mono (by rw [ht]) fun _ h ↦ h).mono ?_ fun _ h ↦ h
      simp [skGkrLayers, *]
    · refine ((skel_gkrStep 2 _ s).bind fun t ht ↦
        (skel_gkrLayers n t).mono (by rw [ht]) fun _ h ↦ h).mono ?_ fun _ h ↦ h
      simp [skGkrLayers, *]

theorem skel_verifyGkrGrandProducts (depth : ℕ) :
    SkelP (verifyGkrGrandProducts depth) (.read :: .read :: skGkrLayers depth 0) fun _ ↦ True := by
  unfold verifyGkrGrandProducts
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact (skel_readScalar.bind fun a _ ↦ skel_readScalar.bind fun b _ ↦
    ((skel_gkrLayers depth ⟨[a, a, b], []⟩).mono (sk' := skGkrLayers depth 0) rfl fun _ h ↦ h).bind
      fun _ _ ↦ SkelP.ret (Q := fun _ : E × List E × List E ↦ True) trivial).mono (by simp)
    fun _ h ↦ h

/-- The skeleton of the bytecode's share. -/
def skBytecodeShare : List Op := .read :: skSum 3 (List.replicate busBits false) ++ [.read]

theorem skel_bytecodeShare (weights bytecodeLow : List E) :
    SkelP (bytecodeShare weights bytecodeLow) skBytecodeShare fun _ ↦ True := by
  unfold bytecodeShare
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact (skel_readScalar.bind fun _ _ ↦ (skel_sumcheck _ _ _).bind fun r _ ↦
    skel_readScalar.bind fun _ _ ↦ (skel_require _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : E × List E × E ↦ True) trivial).mono (by simp [skBytecodeShare])
    fun _ h ↦ h

/-- The skeleton of the bus phase at the push side's depth. -/
def skBus (depth : ℕ) : List Op :=
  skGrind (busGrindingBits depth) ++ List.replicate (2 ^ busBits) .sample ++ [.sample] ++
    (.read :: .read :: skGkrLayers depth 0) ++ List.replicate 2 .read ++ [.read, .read] ++
    skBytecodeShare

/-- The claims are on no `KECCAK` output column. -/
def OffKeccak (claims : List Verifier.ColumnClaim) : Prop := ∀ c ∈ claims, c.column ∉ keccakOutputColumns

theorem bus_columns_off : memory0 ∉ keccakOutputColumns ∧ memory1 ∉ keccakOutputColumns ∧
    memoryFinalCounters ∉ keccakOutputColumns ∧ bytecodeFinalCounters ∉ keccakOutputColumns := by
  decide

/-- **The bus phase's skeleton**, at the push side's depth: its forms one per table, its claims on
no `KECCAK` output column. -/
theorem skel_verifyBusBalance (layout : Verifier.Layout) :
    SkelP (verifyBusBalance computedBytecodeValue layout)
      (skBus (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth)
      fun r ↦ r.forms.length = tables.length ∧ OffKeccak r.claims := by
  unfold verifyBusBalance computedBytecodeValue
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_require _).bind fun _ _ ↦ (skel_grindProofOfWork _).bind fun _ _ ↦
    (skel_sampleChallenges _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    (skel_verifyGkrGrandProducts _).bind fun r _ ↦
    (skel_require _).bind fun _ _ ↦ (skel_readScalars 2).bind fun memory _ ↦
    skel_readScalar.bind fun _ _ ↦ skel_readScalar.bind fun _ _ ↦
    (skel_bytecodeShare _ _).bind fun r' _ ↦ (skel_require _).bind fun _ _ ↦
    SkelP.ret (Q := fun r : BusResult ↦ r.forms.length = tables.length ∧ OffKeccak r.claims)
      ⟨by simp only [Claims.accumulateSide_length, List.length_map], by
        obtain ⟨h0, h1, h2, h3⟩ := bus_columns_off
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with hc | rfl | rfl
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
          simp only [List.getElem_zipWith]
          rw [List.length_zipWith] at hi
          have : i < 2 := by simp at hi; omega
          interval_cases i
          · exact h0
          · exact h1
        · exact h2
        · exact h3⟩).mono (by simp [skBus, List.append_assoc]) fun _ h ↦ h

end
end LeanVM.Protocol.EndToEnd.Sound
