/-
  LeanVM.Guest.EndExecPro

  The prologue: `__jump_tables`' straight-line `SET`s run from the executor's initial state to
  `main`'s entry, writing the jump table.
-/

module

public import LeanVM.Guest.EndExec
public import LeanVM.Guest.Mode.JumpTables

/-!
# The prologue

`ProAt`: a state of the prologue, at pc `i` of `__jump_tables` (function `0`, from pc `0`), in
frame `0`, the public input written and the jump table's slots below `i` holding their targets'
powers. `pro_init`: the executor's initial state is one. `pro_step`: from one, the step is the
slot's `SET` (`f0_slot`), no hint at its pc (`hints_pro`), and it lands in the next state of the
prologue or, past the last slot, at `main`'s entry (`StartMain`), the jump table written
(`JtMem`), `main`'s entry facts its header (`holds_entry_plain`). What it takes of `main`'s
certificate and of the program the walks share is `MainOk`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-- The prologue's length: `__jump_tables`' instructions, `main`'s entry pc. -/
abbrev proLen : ℕ := Data.f0.instructionCount

/-- **A state of the prologue**: at pc `i` of `__jump_tables`, in frame `0`, the public input
written and the jump table's slots below `i` holding their targets' powers. -/
def ProAt (s : St) : Prop :=
  s.pc < proLen ∧ s.fp = 0 ∧ s.mem.written 0 = true ∧ s.mem.written 1 = true ∧
    ∀ j < s.pc, ∃ t, Data.jtTrie.get (Data.mainCells + j) = some t ∧
      s.mem.get (Data.mainCells + j) = some (ofK (Parameters.g ^ t))

/-- **What the prologue takes of `main`'s certificate** and of the program the walks share: `main`
entered past the prologue, the table the guest's, `main`'s entry facts its header alone. -/
structure MainOk (Km : Mode.Cert) (E0 : Mode.Env) : Prop where
  entry : Km.F.entry = proLen
  pows : E0.pows = Data.powTree
  jt : E0.jt = Data.jtTrie
  jtLo : E0.jtLo = Data.mainCells
  jtHi : E0.jtHi = Data.mainCells + proLen
  sigEntry : ∀ o ∈ Km.F.sig.entry, o < 2
  self : Km.F.sig.self = none
  pre : Km.F.sig.pre = []
  preR : Km.F.sig.preR = []
  preP : Km.F.sig.preP = []

theorem proLen_eq : proLen = 13937 := by
  have := jt_span
  show Data.f0.instructionCount = 13937
  omega

theorem mainCells_eq : Data.mainCells = 430 := jt_span.1

theorem f0_mem : Data.f0 ∈ Data.functions := List.mem_cons_self

theorem f0_entry' : Data.f0.entryPc = 0 := rfl

/-- Every pc the advice gives hints at is past the prologue. -/
theorem adviceHints_ge : Data.adviceHints.all (fun p ↦ decide (13937 ≤ p.1)) = true := by
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
  rw [proLen_eq] at hpc
  simp only [decide_eq_true_eq] at this
  simp only [beq_iff_eq]
  omega

/-- **The prologue's instructions**: pc `i` sets the jump table's slot `i` to its target's power. -/
theorem op_pro {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) {i : ℕ}
    (hi : i < proLen) : ∃ k0 t, C.ops[i]? = some (.set (Data.mainCells + i)
      (OffsetInstruction.immediateWord k0 0)) ∧ Data.jtTrie.get (Data.mainCells + i) = some t ∧
      Data.powTree.find k0 = some t := by
  obtain ⟨k0, t, hins, hjt, hfind⟩ := f0_slot hi
  have hpc : i < 2 ^ guestProgram.logSize := by
    have := guest_pc_lt f0_mem hi
    rw [f0_entry'] at this
    omega
  have hfe := guest_fetch f0_mem hi
  rw [f0_entry', Nat.zero_add, hins, show addressOfIndex i =
    addressOfIndex ((⟨i, hpc⟩ : Fin (2 ^ guestProgram.logSize)) : ℕ) from rfl,
    guestProgram.fetch_gpow, Option.some.injEq] at hfe
  have hs : offSmall (.set (Data.mainCells + i) k0 0) = true := by
    rw [proLen_eq] at hi
    simp only [offSmall, decide_eq_true_eq, mainCells_eq]
    omega
  exact ⟨k0, t, ctx_op_off hC hpc hfe hs, hjt, hfind⟩

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
theorem pro_step {Km : Mode.Cert} {E0 : Mode.Env} (hM : MainOk Km E0) (hpows : E0.pows.Ok)
    (hlo : Km.E.jtLo = E0.jtLo) (hhi : Km.E.jtHi = E0.jtHi) (hterm : Km.F.sig.term = [])
    {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints)
    {M : ℕ → E} {s : St} {op : Op} (hP : ProAt s) (hs : Fine M s) (hop : C.ops[s.pc]? = some op) :
    StepOk C M (fun s' ↦ ProAt s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s := by
  obtain ⟨hpc, hfp, h0, h1, hslots⟩ := hP
  obtain ⟨k0, t, hop', hjt, hfind⟩ := op_pro hC hpc
  rw [hop'] at hop
  obtain rfl := Option.some.inj hop
  rw [hints_pro hC ha hpc]
  refine ⟨trivial, fun s' e _ _ ↦ ?_⟩
  obtain ⟨hpc', hfp', hle, hget⟩ := set_step hs.agree.wf e
  have hval : OffsetInstruction.immediateWord k0 0 = ofK (Parameters.g ^ t) :=
    imm_of_ofBits' (PowTree.find_ok' (hM.pows ▸ hpows) hfind)
  rw [hfp, Nat.zero_add, hval] at hget
  have hsl : ∀ j < s.pc + 1, ∃ t, Data.jtTrie.get (Data.mainCells + j) = some t ∧
      s'.mem.get (Data.mainCells + j) = some (ofK (Parameters.g ^ t)) := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · obtain ⟨t', e1, e2⟩ := hslots j hj
      exact ⟨t', e1, hle.get _ _ e2⟩
    · exact ⟨t, hjt, hget⟩
  have hfp0 : s'.fp = 0 := hfp'.trans hfp
  by_cases hlast : s.pc + 1 < proLen
  · exact Or.inl ⟨hpc' ▸ hlast, hfp0, written_mono hle h0, written_mono hle h1, hpc' ▸ hsl⟩
  have hend : s.pc + 1 = proLen := by omega
  have hmc := mainCells_eq
  have hpl := proLen_eq
  have hJ : JtMem E0 s'.mem := by
    refine ⟨by rw [hM.jtHi]; unfold maxCells; omega, fun j hj1 hj2 ↦ ?_, fun d e' hd1 hd2 hd ↦ ?_⟩
    · rw [hM.jtLo] at hj1
      rw [hM.jtHi] at hj2
      obtain ⟨t', -, e2⟩ := hsl (j - Data.mainCells) (by omega)
      rw [Nat.add_sub_cancel' hj1] at e2
      exact written_of_get e2
    · rw [hM.jtLo] at hd1
      rw [hM.jtHi] at hd2
      rw [hM.jt] at hd
      obtain ⟨t', e1, e2⟩ := hsl (d - Data.mainCells) (by omega)
      rw [Nat.add_sub_cancel' hd1] at e1 e2
      rw [hd] at e1
      obtain rfl := Option.some.inj e1
      exact e2
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
  refine ⟨by show 0 < proLen; rw [proLen_eq]; norm_num, rfl, written_of_get (hle.get _ _ hg0),
    written_of_get hg1, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩

end

end LeanVM.Guest.EndExec
