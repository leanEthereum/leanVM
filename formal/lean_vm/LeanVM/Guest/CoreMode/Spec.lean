module

public import LeanVM.Guest.Mode.InvDefs

/-!
# A function's frame interface

`FrameSpec C M Y Ct K Q`: what `Mode/InvRule.lean`'s stack needs of one function `K`, for a frame
predicate `Q i s` (frame `s.fp` of `K` at offset `i`) and contracts `Ct`, stated once for any `Q`: `Q`
is monotone in the memory (`mono`); it holds at entry from its contract's precondition (`PreAt`: the
signature's entry facts for a mode contract), the memory agreeing with `M` (`entry`); and at an
offset where it holds, at a state satisfying `Y` (the stack's instance: the other tracks' invariant
and the reference run, from which the core route reads the honest frame), the
step's obligations hold (`StepOk`: `OpModed`, each hint's needs), given the hints' agreement in order
(`HintsAt`), the residuals (`ResAt`) and the reference's part of the instruction's modedness, and what
the step does is an outcome (`Out`): it stays in the frame at an offset where `Q` holds (a
fall-through, a branch or a table jump), returns with its contract's guarantees (`PostAt`), halts
(`main`), or, given each callee's termination facts at its entry (`TermEntry`), makes a loop's tail
call (the header copied, the iteration returning what the next one does, `Back`) or a call (the
callee's contract's precondition, the caller resumable once the callee guarantees its contract,
`Resume`).

The core route is its instance (`CoreMode/CoreSound.lean`, `frameSpec_core`, `Q = CoreAt`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- Each hint at `s.pc` meets its needs once its inputs are written, at the state its predecessors
reach. -/
def HintsAt (C : Ctx) (M : ℕ → E) (s : St) : Prop :=
  ∀ pre h post, (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
    Moves M s s1 → HintIn s1 h → HintOk C M s1 h

/-- The residuals of `K`'s certificate at offset `i` hold once their cells are written. -/
def ResAt (M : ℕ → E) (K : Cert) (i : ℕ) (s : St) : Prop :=
  ∀ s1, Moves M s s1 → ∀ r ∈ (K.F.res.get i).getD [], ResIn s1 r → ResHolds s1 r

/-- Each callee `K`'s environment names at `s.pc` has its termination facts at frame `s.fp`, once its
entry cells are written. -/
def TermEntry (K : Cert) (s : St) : Prop :=
  ∀ G, K.E.sigs.get s.pc = some G → (∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) →
    TermAt s.mem s.fp G

/-- **What a step of `K`'s frame does**, from the state `s1` after the pc's hints, at offset `i`, to
the executor's next state `s'`. -/
inductive Out (Ct : Cts) (K : Cert) (Q : ℕ → St → Prop) (i : ℕ) (s1 s' : St) : Prop
  /-- In the frame, at offset `j`, where `Q` holds. -/
  | move (j : ℕ) : s'.fp = s1.fp → j < K.code.length → s'.pc = K.F.entry + j → Q j s' → Out Ct K Q i s1 s'
  /-- A return, to the header's pc and frame, with the contract's guarantees. -/
  | ret (c : ℕ) : K.code[i]? = some (.jump c 0 1) → s'.pc < 2 ^ 62 →
      s1.mem.get (s1.fp + 0) = some (ofK (g ^ s'.pc)) → s1.mem.get (s1.fp + 1) = some (ofK (g ^ s'.fp)) →
      PostAt Ct K.F.entry K.F.sig s1.mem s1.fp → Out Ct K Q i s1 s'
  /-- `main`'s halting jump. -/
  | halt : K.F.main = true → s'.pc = K.E.halt → s'.fp = 0 → Out Ct K Q i s1 s'
  /-- A loop's tail call: its own entry in a new frame, its header copied, the iteration returning
  what the next one does. -/
  | tail : K.E.sigs.get K.F.entry = some K.F.sig →
      (TermEntry K s' → s'.pc = K.F.entry ∧ (∀ o ∈ K.F.sig.entry, s'.mem.written (s'.fp + o) = true) ∧
        (∀ o < 2, ∃ u, s'.mem.get (s1.fp + o) = some u ∧ s'.mem.get (s'.fp + o) = some u) ∧
        Back Ct K.F.entry K.F.sig s'.mem s1.fp s'.fp ∧ PreAt Ct K.E K.F.entry K.F.sig s') → Out Ct K Q i s1 s'
  /-- A call: a callee's entry, its header naming the return offset `ro` and this frame, its
  contract's precondition, and this frame resumable at `ro` once the callee guarantees its contract. -/
  | call : (TermEntry K s' → ∃ G ro, K.E.sigs.get s'.pc = some G ∧ ro < K.code.length ∧
        s'.mem.get (s'.fp + 0) = some (ofK (g ^ (K.F.entry + ro))) ∧
        s'.mem.get (s'.fp + 1) = some (ofK (g ^ s1.fp)) ∧
        (∀ o ∈ G.entry, s'.mem.written (s'.fp + o) = true) ∧ PreAt Ct K.E s'.pc G s' ∧
        Resume Ct Q s1.fp ro s'.pc G s'.fp s'.mem) → Out Ct K Q i s1 s'

/-- **A function's frame interface**, for the frame predicate `Q` (see the module doc), the states
where a step starts satisfying `Y` (the stack's instance: the other tracks' invariant, on the
reference run). The step's hypotheses on the frame are the stack's: the program within `2^30` pcs, its halting pc too, the
jump table written (`EnvOk`, `RW … jtRng`), the environment's targets small, the frame's termination
facts, `main`'s frame `0`, and the function's own signature its environment's at its entry. -/
structure FrameSpec (C : Ctx) (M : ℕ → E) (Y : St → Prop) (Ct : Cts) (K : Cert) (Q : ℕ → St → Prop) : Prop where
  mono : ∀ {i : ℕ} {s s' : St}, s.mem ≤ s'.mem → s'.fp = s.fp → Q i s → Q i s'
  entry : ∀ {s : St}, PreAt Ct K.E K.F.entry K.F.sig s → Fine M s → Q 0 s
  step : ∀ {s : St} {i : ℕ} (_hi : i < K.code.length), s.pc = K.F.entry + i → Q i s → Fine M s → Y s →
    C.ops.size ≤ 2 ^ 30 → K.E.halt < 2 ^ 30 → EnvOk s K.E → EnvSmall K.E →
    (∀ s', s.mem ≤ s'.mem → RW s' (jtRng K.E)) → TermAt s.mem s.fp K.F.sig →
    (K.F.main = true → s.fp = 0) → (∀ G, K.E.sigs.get K.F.entry = some G → G = K.F.sig) →
    HintsAt C M s → ResAt M K i s → RefOk M s (opOfOff K.code[i]) →
    ∀ {Inv : St → Prop}, (∀ s1 s', ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 →
      Moves M s s1 → OpModed M s1 (opOfOff K.code[i]) → runOp C s1 (opOfOff K.code[i]) = .ok s' →
      Fine M s' → s1.mem ≤ s'.mem → Out Ct K Q i s1 s' → Inv { s' with steps := s'.steps + 1 }) →
    StepOk C M Inv (opOfOff K.code[i]) ((C.hints[s.pc]?).getD []) s

end

end LeanVM.Guest.Mode
