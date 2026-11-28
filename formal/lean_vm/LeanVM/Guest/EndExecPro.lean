module

public import LeanVM.Guest.ExecDecodable
public import LeanVM.Guest.Mode.InvRule
public import LeanVM.Guest.Mode.HintsCtx
import all Statement.Data.Bytecode
import all Statement.Data.AdviceHints

/-!
# The prologue

`__jump_tables` (function `0`, from pc `0`) is straight-line `SET`s that write the jump table in
`main`'s frame before `main` runs. `ProAt`: a state of the prologue, at pc `i` of `__jump_tables`, in
frame `0`, the public input written and the cell each slot below `i` sets holding its word.
`pro_init`: the executor's initial state is one. `pro_step`: from one, the step is the slot's `SET`
(`op_pro`), no hint at its pc (`hints_pro`), and it lands in the next state of the prologue or, past
the last slot, at `main`'s entry (`StartMain`), the jump table written (`JtMem`), `main`'s entry facts
its header (`holds_entry_plain`). What it takes of `main`'s certificate and of the program the walks
share is `MainOk`: `main` entered past the prologue, the jump table the prologue's slots, `main`'s
entry facts its header alone.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-- The prologue's length: `__jump_tables`' instructions, `main`'s entry pc. -/
abbrev proLen : ℕ := Data.f0.instructionCount

/-- **A state of the prologue**: at pc `i` of `__jump_tables`, in frame `0`, the public input
written and the cell each slot below `i` sets holding its word. -/
def ProAt (s : St) : Prop :=
  s.pc < proLen ∧ s.fp = 0 ∧ s.mem.written 0 = true ∧ s.mem.written 1 = true ∧
    ∀ j < s.pc, ∀ o k0 k1, Data.f0.instructionAt j = .set o k0 k1 →
      s.mem.get o = some (OffsetInstruction.immediateWord k0 k1)

/-- **What the prologue takes of `main`'s certificate** and of the program the walks share: `main`
entered past the prologue, the jump table's cells the prologue's slots, each holding its target's
power, `main`'s entry facts its header alone. -/
structure MainOk (Km : Cert) (E0 : Env) : Prop where
  entry : Km.F.entry = proLen
  jtHi : E0.jtHi = E0.jtLo + proLen
  jtLt : E0.jtLo + proLen ≤ maxCells
  slots : ∀ i < proLen, ∃ k0 k1, Data.f0.instructionAt i = .set (E0.jtLo + i) k0 k1 ∧
    ∀ e, E0.jt.get (E0.jtLo + i) = some e → OffsetInstruction.immediateWord k0 k1 = ofK (g ^ e)
  sigEntry : ∀ o ∈ Km.F.sig.entry, o < 2
  self : Km.F.sig.self = none
  pre : Km.F.sig.pre = []
  preR : Km.F.sig.preR = []
  preP : Km.F.sig.preP = []

theorem proLen_pos : 0 < proLen := by decide

theorem f0_mem : Data.f0 ∈ Data.functions := List.mem_cons_self

theorem f0_entry' : Data.f0.entryPc = 0 := by rfl

/-- Every pc the advice gives hints at is past the prologue. -/
theorem adviceHints_ge : Data.adviceHints.all (fun p ↦ decide (proLen ≤ p.1)) = true := by
  decide +kernel

/-- **No hint in the prologue.** -/
theorem hints_pro {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C)
    (ha : adv.hints = Data.adviceHints) {pc : ℕ} (hpc : pc < proLen) : (C.hints[pc]?).getD [] = [] := by
  have hpc' : pc < 2 ^ guestProgram.logSize := by
    have := guest_pc_lt f0_mem hpc
    rw [f0_entry'] at this
    omega
  rw [ctx_hints hC (ha ▸ adviceHints_incr) hpc', ha]
  unfold hintsAt
  rw [List.find?_eq_none.mpr fun p hp ↦ ?_]
  have := List.all_eq_true.mp adviceHints_ge p hp
  simp only [decide_eq_true_eq] at this
  simp only [beq_iff_eq]
  omega

/-- **The prologue's instructions**: pc `i` is its slot's `SET`. -/
theorem op_pro {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) {i : ℕ}
    (hi : i < proLen) {o k0 k1 : ℕ} (hins : Data.f0.instructionAt i = .set o k0 k1) :
    C.ops[i]? = some (.set o (OffsetInstruction.immediateWord k0 k1)) := by
  have hpc : i < 2 ^ guestProgram.logSize := by
    have := guest_pc_lt f0_mem hi
    rw [f0_entry'] at this
    omega
  have hfe := guest_fetch f0_mem hi
  rw [f0_entry', Nat.zero_add, hins, show addressOfIndex i =
    addressOfIndex ((⟨i, hpc⟩ : Fin (2 ^ guestProgram.logSize)) : ℕ) from rfl,
    guestProgram.fetch_gpow, Option.some.injEq] at hfe
  have hs : offSmall (.set o k0 k1) = true := by
    have h := offSmall_instructionAt (List.all_eq_true.mp functions_offSmall _ f0_mem) i
    rwa [hins] at h
  exact ctx_op_off hC hpc hfe hs

/-- A `SET` writes its cell and moves to the next pc in its frame. -/
theorem set_step {C : Ctx} {s s' : St} {o : ℕ} {k : E} (hwf : s.mem.WF)
    (e : runOp C s (.set o k) = .ok s') :
    s'.pc = s.pc + 1 ∧ s'.fp = s.fp ∧ s.mem ≤ s'.mem ∧ s'.mem.get (s.fp + o) = some k := by
  simp only [runOp, bind_ok] at e
  obtain ⟨cc, hcc, s1, hs1, e⟩ := e
  simp only [pure_ok] at e
  subst e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  obtain ⟨rfl, -⟩ := cellAt_ok hcc
  have := Mem.put_ok hwf hm
  exact ⟨rfl, rfl, this.1, this.2.2⟩

/-- **An entry whose facts are its header's**: cells written, the jump table's run. -/
theorem holds_entry_plain {En : Env} {G : Sig} {s : St} (hself : G.self = none) (hpre : G.pre = [])
    (hpreR : G.preR = []) (hterm : G.term = []) (hpreP : G.preP = [])
    (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) (hjt : Mode.RW s (jtRng En)) :
    Mode.Holds s (entryAbs En G) := by
  unfold entryAbs
  rw [foldlT_eq, hself, hpre, hpreR, hterm, hpreP]
  exact {
    w := fun o ho ↦ by
      rcases entry_w ho with ho | ho
      · exact hw o ho
      · simp at ho
    v := fun o x ho ↦ by simp at ho
    nz := fun o ho ↦ by simp at ho
    hv := fun p hp ↦ by simp at hp
    h := fun m hm ↦ by simp at hm
    r := fun r hr ↦ by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hjt
      · simp at hr
    lt := fun p hp ↦ by simp at hp
    pr := fun p hp ↦ by simp at hp
    xs := fun c a b hc ↦ by simp at hc
    p := fun q hq ↦ by simp at hq
    c := fun _ hc ↦ by simp at hc }

/-- **The prologue's step**: from a state of the prologue, the step is its slot's `SET`, with no
hint, into the next state of the prologue or `main`'s entry. -/
theorem pro_step {Km : Cert} {E0 : Env} (hM : MainOk Km E0) (hlo : Km.E.jtLo = E0.jtLo)
    (hhi : Km.E.jtHi = E0.jtHi) (hterm : Km.F.sig.term = []) {adv : Advice} {C : Ctx}
    (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) {M : ℕ → E} {s : St}
    {op : Op} (hP : ProAt s) (hs : Fine M s) (hop : C.ops[s.pc]? = some op) :
    StepOk C M (fun s' ↦ ProAt s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s := by
  obtain ⟨hpc, hfp, h0, h1, hslots⟩ := hP
  obtain ⟨k0, k1, hins, hjt⟩ := hM.slots s.pc hpc
  rw [op_pro hC hpc hins] at hop
  obtain rfl := Option.some.inj hop
  rw [hints_pro hC ha hpc]
  refine ⟨trivial, fun s' e _ _ ↦ ?_⟩
  obtain ⟨hpc', hfp', hle, hget⟩ := set_step hs.agree.wf e
  rw [hfp, Nat.zero_add] at hget
  have hsl : ∀ j < s.pc + 1, ∀ o k0 k1, Data.f0.instructionAt j = .set o k0 k1 →
      s'.mem.get o = some (OffsetInstruction.immediateWord k0 k1) := by
    intro j hj o k0' k1' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hle.get _ _ (hslots j hj o k0' k1' hj')
    · rw [hins] at hj'
      cases hj'
      exact hget
  have hfp0 : s'.fp = 0 := hfp'.trans hfp
  by_cases hlast : s.pc + 1 < proLen
  · exact Or.inl ⟨hpc' ▸ hlast, hfp0, written_mono hle h0, written_mono hle h1, hpc' ▸ hsl⟩
  have hend : s.pc + 1 = proLen := by omega
  have hslot : ∀ i < proLen, ∃ k0 k1, s'.mem.get (E0.jtLo + i) =
      some (OffsetInstruction.immediateWord k0 k1) ∧
      ∀ e, E0.jt.get (E0.jtLo + i) = some e → OffsetInstruction.immediateWord k0 k1 = ofK (g ^ e) := by
    intro i hi
    obtain ⟨a, b, hab, hje⟩ := hM.slots i hi
    exact ⟨a, b, hsl i (by omega) _ a b hab, hje⟩
  have hJ : JtMem E0 s'.mem := by
    refine ⟨by rw [hM.jtHi]; exact hM.jtLt, fun j hj1 hj2 ↦ ?_, fun d e' hd1 hd2 hd ↦ ?_⟩
    · rw [hM.jtHi] at hj2
      obtain ⟨a, b, e2, -⟩ := hslot (j - E0.jtLo) (by omega)
      rw [Nat.add_sub_cancel' hj1] at e2
      exact written_of_get e2
    · rw [hM.jtHi] at hd2
      obtain ⟨a, b, e2, hje⟩ := hslot (d - E0.jtLo) (by omega)
      rw [Nat.add_sub_cancel' hd1] at e2 hje
      rw [e2, hje e' hd]
  refine Or.inr ⟨by show s'.pc = _; rw [hpc', hend, hM.entry], hfp0, hJ, ?_⟩
  refine holds_entry_plain hM.self hM.pre hM.preR hterm hM.preP (fun o ho ↦ ?_) (rw_jt hlo hhi hJ)
  show s'.mem.written (s'.fp + o) = true
  rw [hfp0, Nat.zero_add]
  rcases (show o = 0 ∨ o = 1 by have := hM.sigEntry o ho; omega) with rfl | rfl
  · exact written_mono hle h0
  · exact written_mono hle h1

/-- **The executor's initial state is the prologue's first.** -/
theorem pro_init {adv : Advice} {input : PublicInput} {C : Ctx} {m : Mem}
    (hm : initMem adv input = .ok m) : ProAt (initSt C adv m) := by
  have hwf0 : (⟨#[], #[], #[], #[], max adv.mainFrame 2⟩ : Mem).WF :=
    ⟨fun c k h ↦ by simp [Mem.cellOf] at h, fun c h ↦ by simp [Mem.cellOf] at h⟩
  unfold initMem at hm
  cases e1 : (⟨#[], #[], #[], #[], max adv.mainFrame 2⟩ : Mem).put 0 input.word0 with
  | error e => rw [e1] at hm; cases hm
  | ok m1 =>
  rw [e1] at hm
  have e2 : m1.put 1 input.word1 = .ok m := hm
  obtain ⟨-, hwf1, hg0⟩ := Mem.put_ok hwf0 e1
  obtain ⟨hle, -, hg1⟩ := Mem.put_ok hwf1 e2
  exact ⟨proLen_pos, rfl, written_of_get (hle.get _ _ hg0),
    written_of_get hg1, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩

end

end LeanVM.Guest.EndExec
