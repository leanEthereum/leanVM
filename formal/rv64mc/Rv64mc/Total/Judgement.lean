/-
  Rv64mc.Total.Judgement

  Total correctness at Lprog, for any instruction set: the counterpart of `Ascent.SafeN` that
  rules out traps and non-termination as well as `wrong`. Written against machine-checked's
  `lprog` package only, in its namespaces, so that it can move there unchanged.

  `Ascent.Total step accept G Q s` is the well-founded "always eventually": every run from `s`
  reaches an accepting state satisfying `Q` (`done`), and until it does, every state it visits
  satisfies the obligation `G`, has a successor, and neither traps nor goes `wrong` (`next`).
  Being inductive, it has no budget: a proof of it is a well-founded tree of steps, so a run
  that never accepts with `Q` is excluded (`Total.diverge`), and so is a run that stops early
  (`Total.run`). Unlike `SafeN`'s guard `G`, which a run may assume, `G` here is an obligation
  the proof discharges at every state the run passes before it ends.

  At Lprog (`Isa.Total`) the step is `Isa.step` with its events forgotten and the accepting
  states are `Isa.accept`: a returned program, or an `Lext` the context accepts. The rules are
  `SafeN`'s (`Lprog/Sem.lean`), in the same continuation form, with an existence obligation
  where `SafeN` has none: an operation must give a result (`opn`), an external call must give
  one and neither trap nor go `wrong` (`ext`), and there is no rule for a fault. An accepting
  external call or a returned program ends the run (`ext_done`, `returned`).

  ## Main definitions

  * `Ascent.Total`, `Isa.Total`

  ## Main results

  * `Ascent.Total.run`, `Ascent.Total.diverge`, `Ascent.Total.reaches`: what the judgement says
    of the runs
  * `Ascent.Total.mono`, `Ascent.Total.guard`, `Ascent.Total.of_not_end`
  * `Total.label`, `opn`, `set`, `goto`, `cond`, `call`, `tail`, `ret`, `ext`, `ext_done`,
    `returned`: one rule per instruction
  * `Total.loop`: a loop, by strong induction on a natural-number measure at its head
-/

import Lprog.Sem
import Lprog.Op

namespace Lprog.Ascent

variable {σ : Type}

/-- **Total correctness.** Every run from `s` reaches an accepting state satisfying `Q`; every
    state before it satisfies `G`, has a successor, and neither traps nor goes `wrong`. -/
inductive Total (R : σ → Outcome σ → Prop) (accept : σ → Prop) (G : σ → Prop) (Q : σ → Prop) :
    σ → Prop
  /-- The run ends here: an accepting state satisfying `Q`. -/
  | done {s : σ} : G s → accept s → Q s → Total R accept G Q s
  /-- The run goes on: `s` steps, only to states, and from each of them the run ends. -/
  | next {s : σ} : G s → ¬ R s .trap → ¬ R s .wrong → (∃ t, R s (.ok t)) →
      (∀ t, R s (.ok t) → Total R accept G Q t) → Total R accept G Q s

namespace Total

variable {R : σ → Outcome σ → Prop} {accept : σ → Prop} {G : σ → Prop} {Q : σ → Prop}

/-- The obligation holds where the judgement does. -/
theorem guard {s : σ} (h : Total R accept G Q s) : G s := by
  cases h <;> assumption

/-- Monotonicity in the obligation and in `Q`. -/
theorem mono {G' Q' : σ → Prop} {s : σ} (h : Total R accept G Q s) (hG : ∀ t, G t → G' t)
    (hQ : ∀ t, accept t → Q t → Q' t) : Total R accept G' Q' s := by
  induction h with
  | done hg ha hq => exact .done (hG _ hg) ha (hQ _ ha hq)
  | next hg ht hw hex _ ih => exact .next (hG _ hg) ht hw hex ih

/-- A state where the run does not end neither traps nor goes `wrong`, and the judgement holds at its successors. -/
theorem of_not_end {s : σ} (h : Total R accept G Q s) (hn : ¬ (accept s ∧ Q s)) :
    ¬ R s .trap ∧ ¬ R s .wrong ∧ ∀ t, R s (.ok t) → Total R accept G Q t := by
  cases h with
  | done _ ha hq => exact absurd ⟨ha, hq⟩ hn
  | next _ ht hw _ hk => exact ⟨ht, hw, hk⟩

/-- **No run stops early.** A run along which no state accepts with `Q` neither traps nor goes
    `wrong`: it ends in a state, where the judgement still holds. -/
theorem run {s : σ} (h : Total R accept G Q s) {n : Nat} {o : Outcome σ}
    (hr : Run R (fun t => ¬ (accept t ∧ Q t)) n s o) : ∃ t, o = .ok t ∧ Total R accept G Q t := by
  induction hr with
  | done _ => exact ⟨_, rfl, h⟩
  | next hg hs _ ih => exact ih ((h.of_not_end hg).2.2 _ hs)
  | trap hg hs => exact absurd hs (h.of_not_end hg).1
  | wrong hg hs => exact absurd hs (h.of_not_end hg).2.1

/-- **No run diverges.** Every infinite run from `s` meets an accepting state satisfying `Q`. -/
theorem diverge {s : σ} (h : Total R accept G Q s) (f : Nat → σ) (h0 : f 0 = s)
    (hf : ∀ i, R (f i) (.ok (f (i + 1)))) : ∃ i, accept (f i) ∧ Q (f i) := by
  induction h generalizing f with
  | done _ ha hq => exact ⟨0, h0 ▸ ha, h0 ▸ hq⟩
  | next _ _ _ _ _ ih =>
    obtain ⟨i, hi⟩ := ih (f 1) (by rw [← h0]; exact hf 0) (fun i => f (i + 1)) rfl fun i => hf (i + 1)
    exact ⟨i + 1, hi⟩

/-- **On a deterministic machine, the run reaches** an accepting state satisfying `Q`. -/
theorem reaches {f : σ → Option σ} {s : σ} (h : Total (detStep f) accept G Q s) :
    Reaches f (fun t => accept t ∧ Q t) s := by
  induction h with
  | done _ ha hq => exact .done ⟨ha, hq⟩
  | next _ _ _ hex _ ih =>
    obtain ⟨t, ht⟩ := hex
    cases hf : f _ with
    | none => rw [detStep_of_none hf] at ht; cases ht
    | some u =>
      rw [detStep_of_some hf] at ht
      cases ht
      exact .step hf (ih _ ((detStep_of_some hf).2 rfl))

end Total

end Lprog.Ascent

namespace Lprog

namespace Isa

variable (I : Isa) (p : Lprog I.Op I.Reg) {E : Type} (c : Context I E)

/-- **Total correctness at Lprog**: `Ascent.Total` at `step`, its events forgotten, and
    `accept`. -/
abbrev Total (G : State I → Prop) (Q : State I → Prop) (s : State I) : Prop :=
  Ascent.Total (Ascent.erase (I.step p c)) (I.accept p c) G Q s

end Isa

/-! ## One rule per instruction

Each rule takes the state at an instruction of the innermost activation (`⟨fn, pc, rv, top⟩`
over `rest`, in function `fd` of the program), the obligation `G` there, and gives `Total`
there from `Total` at every state the instruction may continue in. -/

namespace Total

open Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {G : State I → Prop}
  {Q : State I → Prop} {rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M}
  {fd : Lfundef I.Op I.Reg} {fn pc : Nat} {rv top : BitVec 64}

/-- An instruction with one result, a state. -/
theorem of_one {i : LinstrR I.Op I.Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some i)
    {t : State I} (hs : ∀ o, I.stepI p c fd.body ⟨fn, pc, rv, top⟩ rest regs m i o → o = .ok (t, []))
    (hex : I.stepI p c fd.body ⟨fn, pc, rv, top⟩ rest regs m i (.ok (t, [])))
    (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩) (h : I.Total p c G Q t) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  have hst := fun o => SafeN.step_eq (c := c) (fr := ⟨fn, pc, rv, top⟩) (rest := rest) (regs := regs)
    (m := m) hf hi o
  refine .next hg (fun ht => ?_) (fun hw => ?_) ⟨t, [], (hst _).2 hex⟩ fun t' ⟨es, ht'⟩ => ?_
  · cases hs _ ((hst _).1 ht)
  · cases hs _ ((hst _).1 hw)
  · cases hs _ ((hst _).1 ht')
    exact h

theorem label {kd : LabelKind} {l : LLabel} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Llabel kd l)) (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : I.Total p c G Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi (fun _ ho => ho) rfl hg h

theorem opn {op : I.Op} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn op))
    {r' : I.Reg → BitVec 64} {m' : I.M} (he : I.opn op regs m = some (r', m'))
    (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : I.Total p c G Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi (fun o ho => by simpa [Frame.at, Isa.stepI, he] using ho)
    (by simp [Frame.at, Isa.stepI, he]) hg h

/-- A register write over the shared operations (`Isa.ofOps`), which always gives a result. -/
theorem set {Reg M : Type} [DecidableEq Reg] {link sp : Reg} {mem : Mem M}
    {p : Lprog (Op Reg) Reg} {c : Context (Isa.ofOps Reg link sp M mem) E}
    {G Q : State (Isa.ofOps Reg link sp M mem) → Prop} {fd : Lfundef (Op Reg) Reg}
    {regs : Reg → BitVec 64} {m : M} {d : Reg} {e : Expr Reg} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.set d e))) (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : (Isa.ofOps Reg link sp M mem).Total p c G Q
      ⟨⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs d (e.eval regs), m⟩) :
    (Isa.ofOps Reg link sp M mem).Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  opn hf hi rfl hg h

theorem goto {l : LLabel} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lgoto l))
    {j : Nat} (hl : labelIdx fd.body l = some j) (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : I.Total p c G Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi (fun o ho => by simpa [Frame.at, Isa.stepI, hl] using ho)
    (by simp [Frame.at, Isa.stepI, hl]) hg h

theorem cond {cnd : LOperand I.Reg} {l : LLabel} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcond cnd l)) {b : Bool} (hc : I.cond cnd regs m = some b)
    {j : Nat} (hl : labelIdx fd.body l = some j) (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (ht : b = true → I.Total p c G Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩)
    (hn : b = false → I.Total p c G Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  cases b
  · exact of_one hf hi (fun o ho => by simpa [Frame.at, Isa.stepI, hc] using ho)
      (by simp [Frame.at, Isa.stepI, hc]) hg (hn rfl)
  · exact of_one hf hi (fun o ho => by simpa [Frame.at, Isa.stepI, hc, hl] using ho)
      (by simp [Frame.at, Isa.stepI, hc, hl]) hg (ht rfl)

theorem call {ret : BitVec 64} {tgt : Target I.Reg} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcall ret tgt)) {f : Nat} (hc : I.callee p regs tgt = some f)
    (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : I.Total p c G Q
      ⟨⟨f, 0, ret, regs I.sp⟩ :: ⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs I.link ret, m⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi (fun o ho => by simpa [Frame.at, Isa.stepI, hc] using ho)
    (by simp [Frame.at, Isa.stepI, hc]) hg h

theorem tail {tgt : Target I.Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Ltail tgt))
    (hsp : regs I.sp = top) {f : Nat} (hc : I.callee p regs tgt = some f)
    (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : I.Total p c G Q ⟨⟨f, 0, rv, top⟩ :: rest, regs, m⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi (fun o ho => by simpa [Frame.at, Isa.stepI, hsp, hc] using ho)
    (by simp [Isa.stepI, hsp, hc]) hg h

theorem ret (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some .Lret)
    (hra : regs I.link = rv) (hsp : regs I.sp = top) (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : I.Total p c G Q ⟨rest, regs, m⟩) : I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi (fun o ho => by simpa [Frame.at, Isa.stepI, hra, hsp] using ho)
    (by simp [Isa.stepI, hra, hsp]) hg h

/-- An external call the run goes on from: it neither traps nor goes `wrong`, it has a result,
    and every state it may continue in is total. -/
theorem ext {k : Nat} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lext k))
    (ht : ¬ c.ext k regs m .trap) (hw : ¬ c.ext k regs m .wrong)
    (hex : ∃ r' m' es, c.ext k regs m (.ok ((r', m'), es)))
    (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (h : ∀ r' m' es, c.ext k regs m (.ok ((r', m'), es)) →
      I.Total p c G Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  have hst := fun o => SafeN.step_eq (c := c) (fr := ⟨fn, pc, rv, top⟩) (rest := rest) (regs := regs)
    (m := m) hf hi o
  obtain ⟨r', m', es, he⟩ := hex
  refine .next hg (fun h' => ht ((hst _).1 h')) (fun h' => hw ((hst _).1 h'))
    ⟨⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩, es, (hst _).2 ⟨rfl, he⟩⟩ fun t ⟨es', ht'⟩ => ?_
  obtain ⟨hstk, he'⟩ := (hst _).1 ht'
  obtain ⟨stk, r'', m''⟩ := t
  simp only at hstk
  subst hstk
  exact h r'' m'' es' he'

/-- **An accepting external call ends the run**, where `Q` holds. -/
theorem ext_done {k : Nat} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lext k))
    (hacc : c.accept k regs m) (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (hq : Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  .done hg (.inr ⟨k, SafeN.fetch_eq (fr := ⟨fn, pc, rv, top⟩) hf hi, hacc⟩) hq

/-- **A returned program ends the run**, where `Q` holds. -/
theorem returned (hg : G ⟨[], regs, m⟩) (hq : Q ⟨[], regs, m⟩) : I.Total p c G Q ⟨[], regs, m⟩ :=
  .done hg (.inl rfl) hq

/-- A returned program has no step: the judgement holds there only by `returned`. -/
theorem of_nil (h : I.Total p c G Q ⟨[], regs, m⟩) : Q ⟨[], regs, m⟩ := by
  cases h with
  | done _ _ hq => exact hq
  | next _ _ _ hex _ => obtain ⟨_, _, h⟩ := hex; exact h.elim

/-- **A loop**, by strong induction on a measure `k` at its head `pc`: the head is total from
    every state satisfying `Inv k` if it is from there given that it is from every state
    satisfying `Inv k'` with `k' < k`. -/
theorem loop (Inv : Nat → (I.Reg → BitVec 64) → I.M → Prop)
    (hbody : ∀ k regs m, Inv k regs m →
      (∀ k' regs' m', k' < k → Inv k' regs' m' →
        I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs', m'⟩) →
      I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩) :
    ∀ k regs m, Inv k regs m → I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  fun k => Nat.strongRecOn k fun k ih regs m h => hbody k regs m h fun k' regs' m' hk => ih k' hk regs' m'

end Total

end Lprog
