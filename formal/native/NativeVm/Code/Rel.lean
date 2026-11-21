module

public import NativeVm.Transcript.Layout
public import NativeVm.Equiv.Basic

/-!
# The machine state against the model's

`CodeRel env t s`: the machine state `s` holds the model's transcript state `t`. It goes through the
statement's state: some `st` with `t.Rel st` (`NativeVm.Equiv`) and `SimState env st s`
(`NativeVm.Transcript`), and the model's whole stream and openings are the decoded proof's, which
`TState.Rel` alone leaves open (it sees them from the cursors on). From it the cursors' words hold
the model's absolute cursors (`CodeRel.cursor`, `CodeRel.phase`) and the roots' table the model's
roots (`CodeRel.rootCount`, `CodeRel.root`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript NativeVm.Equiv LeanVM.Parameters LeanVM.Semantics
open LeanVM.Protocol LeanVM.Protocol.Compile

/-- **The machine state `s` holds the model's state `t`.** -/
def CodeRel (env : Env) (t : TState) (s : QState) : Prop :=
  ∃ st, t.Rel st ∧ SimState env st s ∧ t.stream.toList.map EW.toE = env.proof.stream ∧
    t.openings.toList.map phaseOpenings = env.proof.openings

variable {env : Env} {t : TState} {s : QState}

namespace CodeRel

theorem of {st : VerifierProgramState} (h : t.Rel st) (hs : SimState env st s)
    (hstream : t.stream.toList.map EW.toE = env.proof.stream)
    (hop : t.openings.toList.map phaseOpenings = env.proof.openings) : CodeRel env t s :=
  ⟨st, h, hs, hstream, hop⟩

theorem rdi (h : CodeRel env t s) : s.reg .rdi = env.ctx := by
  obtain ⟨_, _, hs, -⟩ := h
  exact hs.rdi

theorem layout (h : CodeRel env t s) : Layout env s.mem := by
  obtain ⟨_, _, hs, -⟩ := h
  exact hs.layout

theorem decoded (h : CodeRel env t s) : Decoded s.mem env.dec env.L env.proof := by
  obtain ⟨_, _, hs, -⟩ := h
  exact hs.decoded

theorem stream (h : CodeRel env t s) : t.stream.toList.map EW.toE = env.proof.stream := by
  obtain ⟨_, _, _, h', -⟩ := h
  exact h'

theorem openings (h : CodeRel env t s) : t.openings.toList.map phaseOpenings = env.proof.openings := by
  obtain ⟨_, _, _, _, h'⟩ := h
  exact h'

theorem stream_size (h : CodeRel env t s) : t.stream.size = env.proof.stream.length := by
  rw [← h.stream, List.length_map, Array.length_toList]

theorem openings_size (h : CodeRel env t s) : t.openings.size = env.proof.openings.length := by
  rw [← h.openings, List.length_map, Array.length_toList]

theorem cursor_le (h : CodeRel env t s) : t.cursor ≤ t.stream.size := by
  obtain ⟨_, hr, -⟩ := h
  exact hr.cursor_le

theorem phase_le (h : CodeRel env t s) : t.phase ≤ t.openings.size := by
  obtain ⟨_, hr, -⟩ := h
  exact hr.phase_le

/-- Two cursors into one list that leave equal suffixes are equal. -/
theorem drop_cursor_eq {α : Type} {l : List α} {a b : Nat} (ha : a ≤ l.length) (hb : b ≤ l.length)
    (h : l.drop a = l.drop b) : a = b := by
  have := congrArg List.length h
  rw [List.length_drop, List.length_drop] at this
  omega

/-- The cursor's word holds the model's cursor. -/
theorem cursor (h : CodeRel env t s) : s.mem (wd env.work workCursor) = some t.cursor.toUInt64 := by
  obtain ⟨st, hr, hs, hstream, -⟩ := h
  obtain ⟨c, hc, hw, hst⟩ := hs.cursor
  have hle := hr.cursor_le
  have e : env.proof.stream.drop t.cursor = env.proof.stream.drop c := by
    rw [← hst, ← hr.stream, ← hstream, List.map_drop]
  rw [hw, drop_cursor_eq hc (by rw [← hstream, List.length_map, Array.length_toList]; exact hle) e.symm]

/-- The phase cursor's words hold the model's phase cursor and its phase's address. -/
theorem phase (h : CodeRel env t s) : s.mem (wd env.work workPhase) = some t.phase.toUInt64 ∧
    s.mem (wd env.work workPhasePtr) = some (wd env.dec (phaseBase env.L t.phase)) := by
  obtain ⟨st, hr, hs, -, hop⟩ := h
  obtain ⟨p, hp, hw, hptr, hst⟩ := hs.phase
  have hle := hr.phase_le
  have e : env.proof.openings.drop t.phase = env.proof.openings.drop p := by
    rw [← hst, ← hr.openings, ← hop, List.map_drop]
  rw [← drop_cursor_eq hp (by rw [← hop, List.length_map, Array.length_toList]; exact hle) e.symm]
  exact ⟨hw, hptr⟩

theorem phaseCount (h : CodeRel env t s) :
    s.mem (wd env.work workPhaseCount) = some t.openings.size.toUInt64 := by
  rw [h.openings_size]
  obtain ⟨_, _, hs, -⟩ := h
  exact hs.phaseCount

theorem roots_toRoot (h : CodeRel env t s) :
    ∃ st, t.Rel st ∧ SimState env st s ∧ st.roots = t.roots.toList.map RootW.toRoot := by
  obtain ⟨st, hr, hs, -⟩ := h
  exact ⟨st, hr, hs, hr.roots.symm⟩

theorem roots_size (h : CodeRel env t s) : t.roots.size ≤ maxRoots := by
  obtain ⟨st, -, hs, e⟩ := h.roots_toRoot
  have := hs.rootsLen
  rwa [e, List.length_map, Array.length_toList] at this

theorem rootCount (h : CodeRel env t s) :
    s.mem (wd env.work workRootCount) = some t.roots.size.toUInt64 := by
  obtain ⟨st, -, hs, e⟩ := h.roots_toRoot
  have := hs.rootCount
  rwa [e, List.length_map, Array.length_toList] at this

/-- Root `j`'s entry holds the model's root `j`. -/
theorem root (h : CodeRel env t s) {j : Nat} (hj : j < t.roots.size) :
    RootAt s.mem env.work j t.roots[j].toRoot := by
  obtain ⟨st, -, hs, e⟩ := h.roots_toRoot
  have hj' : j < st.roots.length := by rw [e, List.length_map, Array.length_toList]; exact hj
  have := hs.roots j hj'
  simp only [e, List.getElem_map, Array.getElem_toList] at this
  exact this

theorem sponge (h : CodeRel env t s) : ∃ sp, t.sponge.Rel sp ∧ SpongeAt s.mem env.ctx sp := by
  obtain ⟨st, hr, hs, -⟩ := h
  exact ⟨st.sponge, hr.sponge, hs.sponge⟩

end CodeRel

end NativeVm.Code
