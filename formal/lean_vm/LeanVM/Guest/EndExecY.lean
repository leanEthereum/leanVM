/-
  LeanVM.Guest.EndExecY

  The witness streams' track: the executor's cursor is the tree track's entries done, stream by
  stream; each witness hint pops the next entry of its stream, the reference's words at its
  destination.
-/

module

public import LeanVM.Guest.EndExecX
public import LeanVM.Guest.EndExecYCur
public import LeanVM.Guest.EndExecYStep
public import LeanVM.Guest.EndExecYAdv
public import LeanVM.Guest.Bridge.Cells

/-!
# The witness streams' track

`YCur A r s`: in the prologue every cursor is `0`; past it, on the reference run, a state of the
tree track at the state's pc and frame (`RefTrack`) whose entries done agree with the cursor on every
stream (`CurOk`). `initY_cur`: it holds initially. `keepY_cur`: each step keeps it,
by the step rule with its entries (`Bridge.stepD_of`): the hints at a pc move the cursor by the
entries they pop (`hints_cursor`), the flow ones compiling the atoms the track moves past one for one
(`count_pairs`). `hintWitness_cur`: a
witness hint, the `j`-th flow hint of its pc, compiles the `j`-th flow atom the track moves past;
the track past the atoms before it pops that atom's entry next (`TrackOk.witness_next`), which the
honest pushes put at the cursor (`Ref.Ok.pops`, `streams_guest`); its words are the reference's at
the destination, a stack run's at the frame's cells, a heap run's the reference's own words there
(`Ref.Ok.hintWords`).

What it rests on beyond `ExecGaps.ofX`'s premises: the alignment's advice is the executor's hints
(`AdvAl`), each witness atom's destination cells hold its values in the reference, a heap pointer a
power below `maxCells` (`WitCells`), and the honest pushes read the bytecode only through its length
(`PushShape`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.End (mainEntry)
open LeanVM.Prover.Exec

@[expose] public section

/-! ## What the track rests on -/

/-- **The alignment's advice is the executor's hints**, at each offset of each function's code. -/
def AdvAl (A : String → FnAl) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ off ins, (A f).code[off]? = some ins →
    (((A f).d.2.2.lookup ((A f).X.entry + off)).getD []) = Mode.hintsAt Data.adviceHints ((A f).X.entry + off)

/-- **A witness destination in the reference**: a stack run's values at their cells below
`maxCells`, a heap run's pointer at its cell, a power below `maxCells`. -/
def WitDest (loc : ℕ → ℕ) (M : ℕ → E) (fp : ℕ) (σ : Val) : Dest → Prop
  | .stack vs => ∀ v ∈ vs, fp + loc v.idx < maxCells ∧ M (fp + loc v.idx) = σ v
  | .heap p _ _ => ∃ b < maxCells, σ p = ofK (Parameters.g ^ b) ∧ fp + loc p.idx < maxCells ∧ M (fp + loc p.idx) = σ p

/-- **The witness atoms' destinations in the reference**, at each frame of the tree track. -/
def WitCells (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ pc fp done e st, RefTrack A r pc fp (done, e :: st) → ∀ es vs,
    walk e.σ e.fn.body = .ret es vs → ∀ S d, Ev.atom (.hint (.witness S d)) ∈ es →
      WitDest (A e.I.t.name).X.locAt (refMem r.img) e.I.fp e.σ d

/-- **The honest pushes read the bytecode only through its length.** -/
def PushShape : Prop :=
  ∀ seed s w, Hints.honestPushes End.bytecode seed s w = Hints.honestPushes bytecodeShape seed s w

/-! ## The track -/

/-- The entries done agree with the cursor on every stream. -/
def CurOk (s : St) (done : List Pop) : Prop :=
  ∀ S, s.cursor.getD S 0 = (done.filter (·.1 == S)).length

/-- **The witness streams' track**: in the prologue every cursor `0`; past it, on the reference run,
a state of the tree track at the state's pc and frame whose entries done are the cursor's. -/
def YCur (A : String → FnAl) (r : Ref) (s : St) : Prop :=
  (s.steps < proLen → ∀ S, s.cursor.getD S 0 = 0) ∧
    (proLen ≤ s.steps → s.steps < r.n → ∃ done st, RefTrack A r s.pc s.fp (done, st) ∧ CurOk s done)

end

public section

/-! ## Counting entries -/

/-- **A compiled hint pops what its atom pops**, of each stream. -/
theorem count_pair {loc : ℕ → ℕ} {hc : Core.Hint} {h : Hint} (hcp : compiles loc hc h = true) (rd : Reader)
    (σ : Val) (S : String) :
    ((hc.pops rd σ).filter (·.1 == S)).length = if popsOn S h then 1 else 0 := by
  cases hc with
  | witness s d =>
    cases d <;> cases h <;> simp only [compiles, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hcp
    · obtain ⟨⟨rfl, -⟩, -⟩ := hcp
      simp only [Core.Hint.pops, popsOn, List.filter_cons, List.filter_nil]
      split <;> simp_all
    · obtain ⟨⟨⟨rfl, -⟩, -⟩, -⟩ := hcp
      simp only [Core.Hint.pops, popsOn, List.filter_cons, List.filter_nil]
      split <;> simp_all
  | _ => cases h <;> simp_all [compiles, popsOn, Core.Hint.pops]

/-- **Atoms paired with hints pop what the hints pop**, of each stream. -/
theorem count_pairs {X : AlignCtx} (rd : Reader) (σ : Val) (S : String) :
    ∀ {as : List Atom} {hs : List Hint}, List.Forall₂ (Pairs X) as hs →
      ((as.flatMap (fun a ↦ a.pops rd σ)).filter (·.1 == S)).length = (hs.filter (popsOn S)).length
  | [], [], .nil => rfl
  | a :: as, h :: hs, .cons hp hr => by
    obtain ⟨hc, rfl, hcp⟩ := hp
    rw [List.flatMap_cons, List.filter_append, List.length_append, count_pairs rd σ S hr, Atom.pops,
      count_pair hcp, List.filter_cons]
    split <;> simp_all; omega

/-- Atoms that are no flow atoms pop nothing. -/
theorem flatMap_flow (rd : Reader) (σ : Val) : ∀ as : List Atom,
    as.flatMap (fun a ↦ a.pops rd σ) = (as.filter flowAtom).flatMap (fun a ↦ a.pops rd σ)
  | [] => rfl
  | a :: as => by
    rw [List.flatMap_cons, List.filter_cons, flatMap_flow rd σ as]
    cases hf : flowAtom a
    · rw [flowAtom_pops hf, List.nil_append]; rfl
    · rfl

/-- The hints that are no flow hints pop no stream. -/
theorem filter_flow {S : String} :
    ∀ {l : List Hint}, (l.filter (popsOn S)).length = ((l.filter isaFlowHint).filter (popsOn S)).length
  | [] => rfl
  | h :: l => by
    have ih := filter_flow (S := S) (l := l)
    have key : isaFlowHint h = false → popsOn S h = false := fun hf ↦ by
      cases h <;> simp_all [isaFlowHint, popsOn]
    by_cases hf : isaFlowHint h = true
    · rw [List.filter_cons_of_pos hf, List.filter_cons, List.filter_cons]
      split <;> simp [ih]
    · rw [List.filter_cons_of_neg hf, List.filter_cons_of_neg (by simp [key (by simpa using hf)]), ih]

theorem foldl_set_size : ∀ (l : List (ℕ × List Hint)) (a : Array (List Hint)),
    (l.foldl (fun hs (p : ℕ × List Hint) ↦ hs.setIfInBounds p.1 p.2) a).size = a.size
  | [], _ => rfl
  | p :: l, a => by rw [List.foldl_cons, foldl_set_size l, Array.size_setIfInBounds]

/-- **The executor's hints at a pc are the advice's.** -/
theorem hints_adv {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints)
    (pc : ℕ) : ∀ h ∈ (C.hints[pc]?).getD [], advHintOk h = true := by
  intro h hh
  by_cases hpc : pc < 2 ^ guestProgram.logSize
  · rw [Mode.ctx_hints hC (ha ▸ Mode.adviceHints_incr) hpc, ha] at hh
    unfold Mode.hintsAt at hh
    split at hh
    · rename_i p hp
      exact List.all_eq_true.mp (List.all_eq_true.mp adviceHints_ok p (List.mem_of_find?_eq_some hp)) h hh
    · cases hh
  · have hsz : C.hints.size = 2 ^ guestProgram.logSize := by
      simp only [Ctx.of, bind_ok, pure_ok] at hC
      obtain ⟨ops, -, rfl⟩ := hC
      exact (foldl_set_size _ _).trans (Array.size_replicate ..)
    rw [Array.getElem?_eq_none (by omega)] at hh
    cases hh

end

end LeanVM.Guest.EndExec
