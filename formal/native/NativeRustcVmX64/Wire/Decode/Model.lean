module

public import NativeRustcVm.Wire.Rep
public import NativeRustcVm.Transcript.Update
public import NativeRustcVm.MemLemmas

/-!
# `decodeM` as `decode` runs it

The model's decoder (`NativeVm.Wire.decodeM`) read by read: the stream's count and words
(`decodeM_eq`), then the phase count and the phases (`afterStream`), each phase in turn
(`tailPh`, `tailPh_succ`, `tailPh_none`), and the decoded area from what the run wrote
(`decodedAt_of`).
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeVm NativeVm.Model NativeVm.Wire NativeRustcVm NativeRustcVm.Wire
open NativeRustcVm.Transcript (off off_off DecArea DecodedAt PhaseAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The stream of `n` elements from the words `ws`. -/
def streamOf (n : Nat) (ws : List K) : List E :=
  (List.range n).map fun i ↦ E.ofLimbs (ws.getD (2 * i) 0) (ws.getD (2 * i + 1) 0)

/-- The phases from `c` on: `m` more after `done`, then no byte left. -/
def tailPh (B : List UInt8) (s : List E) (done : List PhaseOut) (m c : Nat) :
    Option (List E × List PhaseOut) :=
  match phasesM B m c with
  | none => none
  | some (ph, c) => if c ≠ B.length then none else some (s, done ++ ph)

/-- After the stream: the phase count and the phases. -/
def afterStream (B : List UInt8) (s : List E) (c : Nat) : Option (List E × List PhaseOut) :=
  match rdU32 B c with
  | none => none
  | some (p, c) => if wireMaxPhases < p then none else tailPh B s [] p c

end

public section

/-- **The decoder** read by read. -/
theorem decodeM_eq (B : List UInt8) : decodeM B =
    match rdU32 B 0 with
    | none => none
    | some (n, c) => match rdWords B (2 * n) c with
      | none => none
      | some (ws, c) => afterStream B (streamOf n ws) c := by
  unfold decodeM streamM afterStream tailPh streamOf
  simp only [Option.bind_eq_bind]
  rcases h1 : rdU32 B 0 with _ | ⟨n, c1⟩
  · rfl
  simp only [Option.bind_some]
  rcases h2 : rdWords B (2 * n) c1 with _ | ⟨ws, c2⟩
  · rfl
  simp only [Option.bind_some]
  rcases h3 : rdU32 B c2 with _ | ⟨p, c3⟩
  · rfl
  simp only [Option.bind_some]
  by_cases hp : wireMaxPhases < p
  · simp [hp]
  simp only [hp, ↓reduceIte]
  rcases h4 : phasesM B p c3 with _ | ⟨ph, c4⟩
  · rfl
  simp only [Option.bind_some, List.nil_append]
  by_cases hc : c4 ≠ B.length
  · simp [hc]
  · simp [hc]

theorem tailPh_none {B : List UInt8} {s : List E} {done : List PhaseOut} {m c : Nat}
    (h : phaseM B c = none) : tailPh B s done (m + 1) c = none := by
  simp [tailPh, phasesM, h]

theorem tailPh_succ {B : List UInt8} {s : List E} {done : List PhaseOut} {m c : Nat}
    {po : PhaseOut} {c' : Nat} (h : phaseM B c = some (po, c')) :
    tailPh B s done (m + 1) c = tailPh B s (done ++ [po]) m c' := by
  simp only [tailPh, phasesM, Option.bind_eq_bind, h, Option.bind_some]
  rcases phasesM B m c' with _ | ⟨ph, c''⟩
  · rfl
  · simp

theorem tailPh_zero (B : List UInt8) (s : List E) (done : List PhaseOut) (c : Nat) :
    tailPh B s done 0 c = if c = B.length then some (s, done) else none := by
  simp only [tailPh, phasesM, List.append_nil]
  by_cases h : c = B.length <;> simp [h]

theorem length_streamOf (n : Nat) (ws : List K) : (streamOf n ws).length = n := by
  simp [streamOf]

/-- Element `i` of the stream, in its two words. -/
theorem ofE_streamOf {n : Nat} {ws : List K} (hl : ws.length = 2 * n) {i : Nat} (hi : i < n) :
    EW.ofE ((streamOf n ws)[i]'(by rw [length_streamOf]; exact hi)) =
      ⟨(ws[2 * i]'(by omega)).lane, (ws[2 * i + 1]'(by omega)).lane⟩ := by
  simp only [streamOf, List.getElem_map, List.getElem_range, EW.ofE]
  rw [show ws.getD (2 * i) 0 = ws[2 * i] by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 2 * i < ws.length by omega)],
    show ws.getD (2 * i + 1) 0 = ws[2 * i + 1] by
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 2 * i + 1 < ws.length by omega)]]
  rfl

/-- **The decoded area** from the stream's count and words, the phase count and the phases. -/
theorem decodedAt_of {d : Mem 64} {a : DecArea} {n : Nat} {ws : List K} {ps : List PhaseOut}
    (hl : a.l < 2 ^ 64) (hlen : decodedWords a.l ≤ a.len) (hn : n ≤ maxStream a.l)
    (hws : ws.length = 2 * n) (hcnt : WordAt d (a.word 0) n.toUInt64)
    (hw : WordsAt d (a.word 1) (ws.map K.lane)) (hp : ps.length ≤ wireMaxPhases)
    (hpc : WordAt d (a.word (streamEnd a.l)) ps.length.toUInt64)
    (hph : ∀ j (h : j < ps.length), PhaseAt d (a.word (phaseBase a.l j)) (phaseW ps[j])) :
    DecodedAt d a (streamW (streamOf n ws)) (openingsW ps) := by
  refine ⟨hl, hlen, ?_, ?_, fun i hi ↦ ?_, ?_, ?_, fun j hj ↦ ?_⟩
  · simp [streamW, length_streamOf, hn]
  · simpa [streamW, length_streamOf] using hcnt
  · have hi' : i < n := by simpa [streamW, length_streamOf] using hi
    simp only [streamW, List.getElem_toArray, List.getElem_map]
    rw [ofE_streamOf hws hi', NativeRustcVm.ewAt_iff]
    rw [NativeRustcVm.Transcript.wordsAt_iff] at hw
    have h0 := hw (2 * i) (by simp; omega)
    have h1 := hw (2 * i + 1) (by simp; omega)
    simp only [List.getElem_map, off_off] at h0 h1
    refine ⟨?_, ?_⟩
    · show WordAt d (off a.words (8 * (1 + 2 * i))) _
      rw [show 8 * (1 + 2 * i) = 8 * 1 + 8 * (2 * i) by omega]; exact h0
    · show WordAt d (off a.words (8 * (1 + 2 * i)) + BitVec.ofNat 64 8) _
      rw [NativeRustcVm.Transcript.off_add, show 8 * (1 + 2 * i) + 8 = 8 * 1 + 8 * (2 * i + 1) by omega]
      exact h1
  · simpa [openingsW] using hp
  · simpa [openingsW] using hpc
  · have hj' : j < ps.length := by simpa [openingsW] using hj
    simpa [openingsW] using hph j hj'

end

end NativeRustcVmX64.Wire.Decode
