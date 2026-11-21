/-
  LeanVM.Guest.Bridge.RefTrace

  The tree track along the reference run: the top frame at the registers, each suspended frame at the registers its callee's header holds, and a trace of track states, one per step of the run, each reached from the previous by moves.
-/

module

public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.Logic

/-!
# The tree track along the reference run

The registers `(g^pc, g^fp)` are `regs pc fp`. A frame is **at** pc `pc` (`AtPc`) when `pc` is its function's entry (`ent`, by name) plus an offset whose aligned body position (`al`, by name and offset: the position a function's alignment check computes there) is the frame's past atoms that pop nothing (those the alignment's normalization skips). `Linked M ent al pc fp st`: the top frame of the stack `st` is the instance at frame `fp`, at pc `pc`; each frame below is at the registers the header of the frame above holds in the reference memory `M` (`M (fp + 0) = g^r`, `M (fp + 1) = g^fp'`); the bottom one is at frame `0`. `RefOk`: `TrackOk` and `Linked`, the track's invariant against the run.

`StepRule`: from a state of an invariant `Q` at registers `(pc, fp)`, a step of the reference to registers short of the final ones lands at `regs pc' fp'` with a state of `Q` there, reached by moves. `refTrace`: given that rule and a run of `n` steps to the final registers from a state of `Q`, a trace `tr` of states, the `k`-th at the run's registers after `k` steps for every `k < n`, each reached from the one before by moves. `run_after`: the run past its first `m` steps, so a trace can start at `main`'s entry, after the prologue.

The frame lemmas: `Linked.top` (the top frame is at the registers: the frame-to-instance map the hints' and residuals' premises read), `Linked.retop` (a step inside the top frame), `Linked.push` (a call: the callee entered, its header holding the return pc and the caller's frame, the caller at the return pc), `Linked.pop` (a return: the caller at the registers the callee's header holds), `Linked.tail` (a loop's tail call: the callee in the caller's place, its header the caller's).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The registers of pc `g^pc` and frame `g^fp`. -/
abbrev regs (pc fp : ℕ) : Registers K := ⟨addressOfIndex pc, addressOfIndex fp⟩

/-- **Frame `e` at pc `pc`**: an offset of its function past its entry whose aligned position is
the frame's past atoms that pop nothing. -/
def AtPc (ent : String → ℕ) (al : String → ℕ → Option (List Stmt)) (e : Ent) (pc : ℕ) : Prop :=
  ∃ off, pc = ent e.I.t.name + off ∧ ∃ p, al e.I.t.name off = some p ∧ ∃ as : List Atom,
    (∀ a ∈ as, ∀ rd σ, a.pops rd σ = []) ∧ e.pos = as.map Stmt.atom ++ p

/-- **The stack at the registers**: the top frame at `(pc, fp)`, each frame below at the registers
the header of the frame above holds in `M`, the bottom one at frame `0`. -/
def Linked (M : ℕ → E) (ent : String → ℕ) (al : String → ℕ → Option (List Stmt)) :
    ℕ → ℕ → List Ent → Prop
  | _, _, [] => False
  | pc, fp, [e] => e.I.fp = fp ∧ fp = 0 ∧ AtPc ent al e pc
  | pc, fp, e :: e' :: st => e.I.fp = fp ∧ AtPc ent al e pc ∧ ∃ r, M (fp + 0) = ofK (addressOfIndex r) ∧
      M (fp + 1) = ofK (addressOfIndex e'.I.fp) ∧ Linked M ent al r e'.I.fp (e' :: st)

/-- **The tree track against the run**: on the honest tree, at the registers. -/
structure RefOk (P : Core.Program) (rd : Reader) (Is : List Inst) (T : Tree) (M : ℕ → E)
    (ent : String → ℕ) (al : String → ℕ → Option (List Stmt)) (pc fp : ℕ) (s : List Pop × List Ent) :
    Prop where
  track : TrackOk P rd Is T s.1 s.2
  linked : Linked M ent al pc fp s.2

/-- **A step rule for an invariant along a run**: from a state of `Q` at `(pc, fp)`, a step to
registers short of the final ones lands at registers of `Q`'s, by moves. -/
def StepRule {α : Type} (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (R : α → α → Prop)
    (Q : ℕ → ℕ → α → Prop) : Prop :=
  ∀ pc fp s r', Q pc fp s → regs pc fp ≠ Registers.final prog → step prog img (regs pc fp) = some r' →
    r' ≠ Registers.final prog → ∃ pc' fp' s', r' = regs pc' fp' ∧ Relation.ReflTransGen R s s' ∧ Q pc' fp' s'

end

public section

/-! ## Runs -/

section Run

variable {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ}

theorem run_one (r : Registers K) :
    run prog img 1 r = if r = Registers.final prog then none else step prog img r := by
  rw [run_succ]
  split_ifs
  · rfl
  · cases step prog img r <;> rfl

/-- The `k + 1`-th registers of a run are a step from the `k`-th. -/
theorem step_of_run {k : ℕ} {r0 r r' : Registers K} (h : run prog img k r0 = some r)
    (h' : run prog img (k + 1) r0 = some r') : r ≠ Registers.final prog ∧ step prog img r = some r' := by
  rw [run_add, h] at h'
  change run prog img 1 r = some r' at h'
  rw [run_one] at h'
  split_ifs at h' with hf
  exact ⟨hf, h'⟩

theorem run_of_step {k : ℕ} {r0 r r' : Registers K} (h : run prog img k r0 = some r)
    (hf : r ≠ Registers.final prog) (hs : step prog img r = some r') : run prog img (k + 1) r0 = some r' := by
  rw [run_add, h]
  change run prog img 1 r = some r'
  rw [run_one, ite_eq_right hf, hs]

/-- **The run past its first `m` steps**: a run of `n` steps to `t` passing through `r'` after
`m` steps takes `m ≤ n`, and goes on from `r'` to `t` in `n - m`. -/
theorem run_after {n m : ℕ} {r t r' : Registers K} (ht : run prog img n r = some t)
    (htf : t = Registers.final prog) (hm : run prog img m r = some r') :
    m ≤ n ∧ run prog img (n - m) r' = some t := by
  have hle : m ≤ n := by
    by_contra hc
    obtain ⟨j, rfl⟩ : ∃ j, m = n + (j + 1) := ⟨m - n - 1, by omega⟩
    rw [run_add, ht] at hm
    change run prog img (j + 1) t = some r' at hm
    rw [run_succ_of_eq htf] at hm
    cases hm
  refine ⟨hle, ?_⟩
  have := ht
  rw [show n = m + (n - m) by omega, run_add, hm] at this
  exact this

/-- **The trace of an invariant along a run**: from a state of `Q` at the run's first registers,
one state per step before the last, at the run's registers, each reached by moves from the one
before. -/
theorem refTrace {α : Type} {R : α → α → Prop} {Q : ℕ → ℕ → α → Prop} (h : StepRule prog img R Q)
    {n pc0 fp0 : ℕ} {s0 : α} (hrun : run prog img n (regs pc0 fp0) = some (Registers.final prog))
    (h0 : Q pc0 fp0 s0) :
    ∃ tr : ℕ → ℕ × ℕ × α, tr 0 = (pc0, fp0, s0) ∧
      (∀ k < n, run prog img k (regs pc0 fp0) = some (regs (tr k).1 (tr k).2.1) ∧
        Q (tr k).1 (tr k).2.1 (tr k).2.2) ∧
      ∀ k, k + 1 < n → Relation.ReflTransGen R (tr k).2.2 (tr (k + 1)).2.2 := by
  classical
  let Rl : ℕ × ℕ × α → ℕ × ℕ × α → Prop := fun x y ↦
    step prog img (regs x.1 x.2.1) = some (regs y.1 y.2.1) ∧ Relation.ReflTransGen R x.2.2 y.2.2 ∧
      Q y.1 y.2.1 y.2.2
  let adv : ℕ × ℕ × α → ℕ × ℕ × α := fun x ↦ if hx : ∃ y, Rl x y then hx.choose else x
  have hadv : ∀ x, (∃ y, Rl x y) → Rl x (adv x) := fun x hx ↦ by
    simp only [adv]
    split
    · rename_i hx'
      exact hx'.choose_spec
    · contradiction
  let x0 : ℕ × ℕ × α := (pc0, fp0, s0)
  have key : ∀ k < n, run prog img k (regs pc0 fp0) = some (regs (adv^[k] x0).1 (adv^[k] x0).2.1) ∧
      Q (adv^[k] x0).1 (adv^[k] x0).2.1 (adv^[k] x0).2.2 ∧
      (k + 1 < n → Rl (adv^[k] x0) (adv^[k + 1] x0)) := by
    have hnext : ∀ k, k + 1 < n → run prog img k (regs pc0 fp0) = some (regs (adv^[k] x0).1 (adv^[k] x0).2.1) →
        Q (adv^[k] x0).1 (adv^[k] x0).2.1 (adv^[k] x0).2.2 → Rl (adv^[k] x0) (adv^[k + 1] x0) := by
      intro k hk hr hq
      obtain ⟨r1, hr1, hne1⟩ := run_intermediate hrun (m := k + 1) hk
      obtain ⟨hne, hs⟩ := step_of_run hr hr1
      obtain ⟨pc', fp', s', rfl, hR, hQ⟩ := h _ _ _ _ hq hne hs hne1
      rw [Function.iterate_succ_apply']
      exact hadv _ ⟨(pc', fp', s'), hs, hR, hQ⟩
    intro k
    induction k with
    | zero =>
      intro hn
      exact ⟨rfl, h0, fun hk ↦ hnext 0 hk rfl h0⟩
    | succ k ih =>
      intro hk
      obtain ⟨hr, -, hR⟩ := ih (by omega)
      obtain ⟨hs, -, hq⟩ := hR hk
      have hr' : run prog img (k + 1) (regs pc0 fp0) =
          some (regs (adv^[k + 1] x0).1 (adv^[k + 1] x0).2.1) := by
        obtain ⟨r1, hr1, -⟩ := run_intermediate hrun (m := k + 1) hk
        obtain ⟨hne, hs1⟩ := step_of_run hr hr1
        rw [run_of_step hr hne hs]
      exact ⟨hr', hq, fun hk' ↦ hnext (k + 1) hk' hr' hq⟩
  exact ⟨fun k ↦ adv^[k] x0, rfl, fun k hk ↦ ⟨(key k hk).1, (key k hk).2.1⟩,
    fun k hk ↦ ((key k (by omega)).2.2 hk).2.1⟩

end Run

/-! ## The stack at the registers -/

section Linked

variable {M : ℕ → E} {ent : String → ℕ} {al : String → ℕ → Option (List Stmt)}

theorem linked_cons_cons {pc fp : ℕ} {e e' : Ent} {st : List Ent} :
    Linked M ent al pc fp (e :: e' :: st) ↔ e.I.fp = fp ∧ AtPc ent al e pc ∧ ∃ r,
      M (fp + 0) = ofK (addressOfIndex r) ∧ M (fp + 1) = ofK (addressOfIndex e'.I.fp) ∧
        Linked M ent al r e'.I.fp (e' :: st) := by
  rw [Linked]

/-- **The top frame is at the registers**: the instance at frame `fp`, at pc `pc`. -/
theorem Linked.top {pc fp : ℕ} {e : Ent} {st : List Ent} (h : Linked M ent al pc fp (e :: st)) :
    e.I.fp = fp ∧ AtPc ent al e pc := by
  cases st with
  | nil => exact ⟨h.1, h.2.2⟩
  | cons e' st => exact ⟨h.1, h.2.1⟩

/-- **A step inside the top frame**: the frame, its instance the same, at a new pc. -/
theorem Linked.retop {pc fp pc' : ℕ} {e e' : Ent} {st : List Ent} (h : Linked M ent al pc fp (e :: st))
    (hI : e'.I = e.I) (ha : AtPc ent al e' pc') : Linked M ent al pc' fp (e' :: st) := by
  cases st with
  | nil => exact ⟨hI ▸ h.1, h.2.1, ha⟩
  | cons e'' st => exact ⟨hI ▸ h.1, ha, h.2.2⟩

/-- **A call**: the callee `J` entered at frame `fp'`, its header holding the return pc `r` and the
caller's frame, the caller, its instance the same, at `r`. -/
theorem Linked.push {pc fp fp' pc' r : ℕ} {e e' J : Ent} {st : List Ent}
    (h : Linked M ent al pc fp (e :: st)) (hI : e'.I = e.I) (ha : AtPc ent al e' r) (hJ : J.I.fp = fp')
    (hJa : AtPc ent al J pc') (h0 : M (fp' + 0) = ofK (addressOfIndex r))
    (h1 : M (fp' + 1) = ofK (addressOfIndex fp)) : Linked M ent al pc' fp' (J :: e' :: st) := by
  have he := h.top
  refine ⟨hJ, hJa, r, h0, by rw [hI, he.1]; exact h1, ?_⟩
  rw [hI, he.1]
  exact h.retop hI ha

/-- **A return**: the caller at the registers the callee's header holds. -/
theorem Linked.pop {pc fp : ℕ} {e e' : Ent} {st : List Ent} (h : Linked M ent al pc fp (e :: e' :: st)) :
    ∃ r, M (fp + 0) = ofK (addressOfIndex r) ∧ M (fp + 1) = ofK (addressOfIndex e'.I.fp) ∧
      Linked M ent al r e'.I.fp (e' :: st) :=
  h.2.2

/-- **A loop's tail call**: the callee `J` in the caller's place at frame `fp'`, its header the
caller's (not the bottom frame's). -/
theorem Linked.tail {pc fp fp' pc' : ℕ} {e J : Ent} {e' : Ent} {st : List Ent}
    (h : Linked M ent al pc fp (e :: e' :: st)) (hJ : J.I.fp = fp') (hJa : AtPc ent al J pc')
    (h0 : M (fp' + 0) = M (fp + 0)) (h1 : M (fp' + 1) = M (fp + 1)) :
    Linked M ent al pc' fp' (J :: e' :: st) := by
  obtain ⟨r, hr0, hr1, hl⟩ := h.pop
  exact ⟨hJ, hJa, r, h0.trans hr0, h1.trans hr1, hl⟩

end Linked

/-! ## The track against the run -/

section Ref

variable {P : Core.Program} {rd : Reader} {Is : List Inst} {T : Tree} {M : ℕ → E} {ent : String → ℕ}
  {al : String → ℕ → Option (List Stmt)}

/-- **A frame moves past the atoms its position starts with**, popping their entries. -/
theorem moves_atoms : ∀ (as : List Atom) {done : List Pop} {e : Ent} {st : List Ent} {ps : List Stmt},
    e.pos = as.map Stmt.atom ++ ps → ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st)
      (done ++ as.flatMap (fun a ↦ a.pops rd e.σ), e' :: st) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.pos = ps ∧ e'.nb = e.nb
  | [], done, e, st, ps, h => ⟨e, by simpa using Relation.ReflTransGen.refl, rfl, rfl, by simpa using h, rfl⟩
  | a :: as, done, e, st, ps, h => by
    have hm : Move P rd Is (done, e :: st) (done ++ a.pops rd e.σ, e.adv (as.map Stmt.atom ++ ps) 1 :: st) :=
      .atom (by rw [h]; rfl)
    obtain ⟨e', h1, h2, h3, h4, h5⟩ := moves_atoms as (done := done ++ a.pops rd e.σ)
      (e := e.adv (as.map Stmt.atom ++ ps) 1) (st := st) (ps := ps) rfl
    refine ⟨e', ?_, h2, h3, h4, h5⟩
    have := Relation.ReflTransGen.head hm h1
    simpa [List.flatMap_cons, List.append_assoc, Ent.σ, Ent.adv] using this

/-- **The frame-to-instance map**: the top frame is an honest instance, a node of its function, at
frame `fp`, at an offset of its function aligned with its position. -/
theorem RefOk.top {pc fp : ℕ} {done : List Pop} {st : List Ent}
    (h : RefOk P rd Is T M ent al pc fp (done, st)) :
    ∃ e st', st = e :: st' ∧ EntOk P Is e ∧ e.I.fp = fp ∧ AtPc ent al e pc := by
  cases st with
  | nil => exact h.linked.elim
  | cons e st' =>
    obtain ⟨hfp, hat⟩ := h.linked.top
    exact ⟨e, st', rfl, h.track.ents e List.mem_cons_self, hfp, hat⟩

/-- **The track starts at the registers of its frame's entry**: a single frame at its body, at
frame `0`, where the alignment puts its body at offset `0`. -/
theorem refOk_init {I : Inst} {fn : Fn} (h : TrackOk P rd Is T [] [Ent.enter P I fn]) (hfp : I.fp = 0)
    (hal : al I.t.name 0 = some fn.body) :
    RefOk P rd Is T M ent al (ent I.t.name) 0 ([], [Ent.enter P I fn]) :=
  ⟨h, hfp, rfl, 0, rfl, fn.body, hal, [], by simp, rfl⟩

/-- Moves inside the top frame keep the track against the run, at the new pc. -/
theorem RefOk.within {pc fp pc' : ℕ} {done done' : List Pop} {e e' : Ent} {st : List Ent}
    (h : RefOk P rd Is T M ent al pc fp (done, e :: st))
    (hm : Relation.ReflTransGen (Move P rd Is) (done, e :: st) (done', e' :: st)) (hI : e'.I = e.I)
    (ha : AtPc ent al e' pc') : RefOk P rd Is T M ent al pc' fp (done', e' :: st) :=
  ⟨h.track.moves hm, h.linked.retop hI ha⟩

end Ref

end

end LeanVM.Guest.Bridge
