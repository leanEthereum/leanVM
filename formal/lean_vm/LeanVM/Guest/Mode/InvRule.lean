module

public import LeanVM.Guest.Mode.InvJump
public import LeanVM.Prover.ExecuteCompleteX

/-!
# The invariant and its rule

`guestInv`: the other tracks' invariant `X` (the witness streams' cursor, the bump pointer, the cells
the run touches below `2^κ`), and the run either halted, in its prologue (`Pro`, the jump table
being written: `__jump_tables`, taken as given), or at the stack (`StackAt`) of the frame predicates
`Q`, the jump table written. `inv_rule_of_specs`: it satisfies `InvRule`, given the certificates
(`ProgOk`), each function's frame interface (`FrameSpec Ct K (Q K)`, for the contracts `Ct`, `main`'s
its mode signature's), the value facts left to the
reference (`Prem`: the hints' agreement in order, the residuals, the loops' termination facts at their
entries, the reference's part of each instruction's modedness, and `X` kept by each step), and the
prologue's steps. `inv_init`, `inv_used`: it holds initially and keeps the memory within `2^κ`.
`execute_complete_guest`: so the executor is complete on the program, within the reference's
committed size.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- **The invariant.** -/
def guestInv (prog : LeanIsaProgram) (Ks : List Cert) (Km : Cert) (E0 : Env) (Ct : Cts)
    (Q : Cert → ℕ → St → Prop) (X Pro : St → Prop) (s : St) : Prop :=
  X s ∧ (Halted prog s ∨ Pro s ∨ (JtMem E0 s.mem ∧ StackAt Ct Q Ks Km s))

/-- **What the invariant takes of the reference and of the other tracks**, at states on the
reference run where `X` holds, before their instruction's hints: each hint's agreement once its
inputs are written, at the state its predecessors reach; each residual once its cells are; each
function's termination facts at its entry, its entry cells written; the reference's part of each
instruction's modedness; and `X` after the hints and the instruction. -/
structure Prem (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (n : ℕ) (C : Ctx)
    (Ks : List Cert) (X : St → Prop) : Prop where
  hint : ∀ s, X s → Fine (refMem img) s → OnRef prog img n s → ∀ pre h post,
    (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
    Moves (refMem img) s s1 → HintIn s1 h → HintOk C (refMem img) s1 h
  res : ∀ K ∈ Ks, ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < K.code.length →
    s.pc = K.F.entry + i → ∀ s1, Moves (refMem img) s s1 → ∀ r ∈ (K.F.res.get i).getD [], ResIn s1 r →
    ResHolds s1 r
  term : ∀ K ∈ Ks, ∀ s, X s → Fine (refMem img) s → OnRef prog img n s → s.pc = K.F.entry →
    (∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true) → ∀ p ∈ K.F.sig.term, LTF s p.1 p.2
  ref : ∀ s op, X s → Fine (refMem img) s → OnRef prog img n s → C.ops[s.pc]? = some op →
    RefOk (refMem img) s op
  xo : ∀ s op s1 s', X s → Fine (refMem img) s → OnRef prog img n s → C.ops[s.pc]? = some op →
    ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 → Moves (refMem img) s s1 →
    runOp C s1 op = .ok s' → X { s' with steps := s'.steps + 1 }

/-- `main`'s entry is the stack of `main`'s activation alone. -/
theorem start_stack {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    {Ct : Cts} {Q : Cert → ℕ → St → Prop} (P : ProgOk prog C Ks Km E0) {s : St}
    (hQ : Holds s (entryAbs Km.E Km.F.sig) → Q Km 0 s) (h : StartMain Km E0 s) :
    JtMem E0 s.mem ∧ StackAt Ct Q Ks Km s := by
  obtain ⟨hpc, hfp, hjt, hH⟩ := h
  refine ⟨hjt, ⟨Km, [], 0, 0⟩, [], 0, ⟨P.main, rfl, fun p hp ↦ ?_, by unfold maxCells; norm_num⟩,
    hfp.symm, P.ne Km P.main, by simp [hpc], hQ hH, rfl, rfl, rfl⟩
  rw [P.mainTerm] at hp
  cases hp

/-- Each callee of `K`'s environment has its termination facts at its entry, once its entry cells are
written, at a state on the reference. -/
theorem termEntry_of {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx} {Ks : List Cert}
    {Km : Cert} {E0 : Env} {X : St → Prop} (P : ProgOk prog C Ks Km E0) (R : Prem prog img n C Ks X)
    {K : Cert} (hK : K ∈ Ks) {s : St} (hX : X s) (hs : Fine (refMem img) s) (hon : OnRef prog img n s) :
    TermEntry K s := by
  intro G hG hw p hp
  obtain ⟨K', hK', hent, rfl, -⟩ := P.sigs K hK _ G hG
  exact LTF.mono (s := s) (s' := stOf s.mem s.fp) (Mem.le_refl _) rfl
    (R.term K' hK' s hX hs hon hent.symm hw p hp)

/-- **The invariant rule from each function's frame interface**: from a state of the invariant on the
reference run, a step's obligations hold, the invariant after it among them. -/
theorem inv_rule_of_specs {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ}
    {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env} {Ct : Cts} {Q : Cert → ℕ → St → Prop}
    {X Pro : St → Prop}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) (P : ProgOk prog C Ks Km E0)
    (hQ : ∀ K ∈ Ks, FrameSpec C (refMem img) (fun s ↦ X s ∧ Fine (refMem img) s ∧ OnRef prog img n s) Ct K (Q K))
    (hCm : Ct Km.F.entry = none) (R : Prem prog img n C Ks X)
    (hpro : ∀ s op, X s → Pro s → Fine (refMem img) s → OnRef prog img n s → C.ops[s.pc]? = some op →
      StepOk C (refMem img) (fun s' ↦ Pro s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s) :
    InvRule prog img n C (refMem img) (guestInv prog Ks Km E0 Ct Q X Pro) := by
  obtain ⟨hsize, -⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have hmono : ∀ K ∈ Ks, ∀ {i : ℕ} {s s' : St}, s.mem ≤ s'.mem → s'.fp = s.fp → Q K i s → Q K i s' :=
    fun K hK ↦ (hQ K hK).mono
  intro s op ⟨hX, hI⟩ hs hon hop
  rcases hI with hH | hP | ⟨hjt, a, rest, i, ha, hfpa, hi, hpc, hat, hbel⟩
  · exact absurd hH (onRef_not_halted hon)
  · refine stepOk_conj s _ s (Moves.refl' hs) (fun s1 s' e1 hm e hf' hI' ↦
      ⟨R.xo s op s1 s' hX hs hon hop e1 hm e, ?_⟩) (hpro s op hX hP hs hon hop)
    rcases hI' with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (start_stack P (fun h ↦ (hQ Km P.main).entry (by rw [preAt_none hCm]; exact h)
        (fine_steps hf' _)) h))
  have hK := P.ok a.K ha.mem
  have hS := hQ a.K ha.mem
  have hop' : op = opOfOff a.K.code[i] := by
    have := hK.ops i hi
    rw [← hpc, hop] at this
    exact Option.some.inj this
  subst hop'
  obtain ⟨-, -, e3, e4, -⟩ := P.env a.K ha.mem
  have hown : ∀ G, a.K.E.sigs.get a.K.F.entry = some G → G = a.K.F.sig := by
    intro G hG
    obtain ⟨K', hK', hent, hsig, -⟩ := P.sigs a.K ha.mem _ G hG
    rw [← hsig, P.uniq K' hK' a.K ha.mem hent]
  refine hS.step hi hpc hat hs ⟨hX, hs, hon⟩ hsz (halt_lt P ha.mem) (envOk_of P ha.mem hjt) (envSmall_of P hsz ha.mem)
    (fun s' hle ↦ rw_jt e3 e4 (hjt.mono hle)) (hfpa ▸ ha.term)
    (fun hm ↦ by rw [← hfpa]; exact hbel.main_fp hm) hown
    (fun pre h post hp s1 e hm hin ↦ R.hint s hX hs hon pre h post hp s1 e hm hin)
    (fun s1 hm ↦ R.res a.K ha.mem s i hX hs hon hi hpc s1 hm) (R.ref s _ hX hs hon hop)
    (fun s1 s' e1 hm hmo e hf' hle' hout ↦ ?_)
  have hX' := R.xo s _ s1 s' hX hs hon hop e1 hm e
  refine ⟨hX', ?_⟩
  have hle1 := hm.le
  have hfpa1 : a.fp = s1.fp := hfpa.trans hm.fp.symm
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  have hjt' : JtMem E0 s'.mem := hjt.mono hle
  have hop1 : C.ops[s1.pc]? = some (opOfOff a.K.code[i]) := by rw [hm.pc, hop]
  cases hout with
  | move j hfp' hj hpcj hq =>
    exact Or.inr (Or.inr ⟨hjt', stack_move ha hfpa hbel hle (hfp'.trans hm.fp) hj hpcj
      (hS.mono (s := s') (Mem.le_refl _) rfl hq)⟩)
  | ret c hc hpcs hvd hvf hRA =>
    have hnot : a.K ≠ Km := fun h ↦ P.mainRet i c (by rw [← h]; exact hc)
    exact Or.inr (Or.inr ⟨hjt', ret_stack P hsz ha hfpa1 hbel hnot hle1 hmono hRA hf' hle' hpcs hvd hvf⟩)
  | halt hmain hpc' hfp' => exact Or.inl (halt_of P ha.mem hpc' hfp')
  | tail hsig h =>
    rcases onRef_next hκ hC hm.fine (onRef_moves hm hon) hop1 hmo e with hon' | hH'
    swap
    · exact Or.inl hH'
    have hTE := termEntry_of P R ha.mem hX' (fine_steps hf' _) hon'
    obtain ⟨hpc', hw, hhdr, hback, hen⟩ := h hTE
    obtain ⟨K', hK', hent, -, hmain'⟩ := P.sigs a.K ha.mem _ _ hsig
    obtain rfl := P.uniq K' hK' a.K ha.mem hent
    exact Or.inr (Or.inr ⟨hjt', tail_stack ha hfpa1 hbel hle1 hm.fine.fp hf' hle' P.mainF (P.ne _ ha.mem)
      hmain' hpc' (hTE _ (by rw [hpc']; exact hsig) hw) hhdr hback
      (hS.entry (PreAt.congr (s := s') rfl rfl hen) (fine_steps hf' _))⟩)
  | call h =>
    rcases onRef_next hκ hC hm.fine (onRef_moves hm hon) hop1 hmo e with hon' | hH'
    swap
    · exact Or.inl hH'
    have hTE := termEntry_of P R ha.mem hX' (fine_steps hf' _) hon'
    obtain ⟨G, ro, hG, hro, hd0, hd1, hw, hen, hres⟩ := h hTE
    obtain ⟨K', hK', hent, rfl, hmain'⟩ := P.sigs a.K ha.mem _ G hG
    obtain ⟨-, -, e3', e4', -⟩ := P.env K' hK'
    have hen' : PreAt Ct K'.E K'.F.entry K'.F.sig { s' with steps := s'.steps + 1 } := by
      rw [hent]
      exact PreAt.env (s := s') (e3.trans e3'.symm) (e4.trans e4'.symm) rfl rfl hen
    exact Or.inr (Or.inr ⟨hjt', call_stack ha hfpa1 hbel hle1 hf' hle' hK' (P.ne K' hK') hent hmain' hro
      hd0 hd1 (hTE _ hG hw) ((hQ K' hK').entry hen' (fine_steps hf' _)) (by rw [hent]; exact hres)⟩)

/-- **The invariant holds initially**, the prologue's and `X`'s initial states given. -/
theorem inv_init {prog : LeanIsaProgram} {Ks : List Cert} {Km : Cert} {E0 : Env} {X Pro : St → Prop}
    {Ct : Cts} {Q : Cert → ℕ → St → Prop} {s : St} (hX : X s) (hP : Pro s) : guestInv prog Ks Km E0 Ct Q X Pro s :=
  ⟨hX, Or.inr (Or.inl hP)⟩

/-- **The invariant keeps the memory within `2^κ`**, as `X` does. -/
theorem inv_used {prog : LeanIsaProgram} {Ks : List Cert} {Km : Cert} {E0 : Env} {X Pro : St → Prop}
    {Ct : Cts} {Q : Cert → ℕ → St → Prop} {κ : ℕ} (hu : ∀ s, X s → s.mem.used ≤ 2 ^ κ) :
    ∀ s, guestInv prog Ks Km E0 Ct Q X Pro s → s.mem.used ≤ 2 ^ κ :=
  fun s h ↦ hu s h.1

/-- **The executor is complete on the program**, within the reference's committed size: under
`execute_completeX`'s hypotheses on the reference, given the certificates, each function's frame
interface, the value facts and the prologue. -/
theorem execute_complete_guest {prog : LeanIsaProgram} {input : PublicInput} {adv : Advice} {κ n : ℕ}
    {img : MemoryImage κ} {Ks : List Cert} {Km : Cert} {E0 : Env} {Ct : Cts} {Q : Cert → ℕ → St → Prop}
    {X Pro : St → Prop} (hκ : κ ≤ 28) (hn : n ≤ maxSteps) (hval : ValidExecution prog input ⟨κ, img, n⟩)
    (hdec : ∀ i, Decodable (prog.instructions i)) (hmain : adv.mainFrame < maxCells)
    (P : ∀ C, Ctx.of prog adv = .ok C → ProgOk prog C Ks Km E0)
    (hQ : ∀ C, Ctx.of prog adv = .ok C → ∀ K ∈ Ks,
      FrameSpec C (refMem img) (fun s ↦ X s ∧ Fine (refMem img) s ∧ OnRef prog img n s) Ct K (Q K))
    (hCm : Ct Km.F.entry = none) (R : ∀ C, Ctx.of prog adv = .ok C → Prem prog img n C Ks X)
    (hpro : ∀ C, Ctx.of prog adv = .ok C → ∀ s op, X s → Pro s → Fine (refMem img) s →
      OnRef prog img n s → C.ops[s.pc]? = some op →
      StepOk C (refMem img) (fun s' ↦ Pro s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s)
    (hinit : ∀ C m, Ctx.of prog adv = .ok C → initMem adv input = .ok m →
      X (initSt C adv m) ∧ Pro (initSt C adv m))
    (hu : ∀ s, X s → s.mem.used ≤ 2 ^ κ) :
    ∃ t, execute prog input adv = .ok t ∧ ValidExecution prog input t ∧ t.stepCount = n ∧
      (∀ i, t.memory i = 0 ∨ t.memory i = refMem img i.val) ∧
      (∀ op, t.opcodeCount op = (⟨κ, img, n⟩ : Execution prog).opcodeCount op) ∧
      t.logMemorySize ≤ κ ∧ t.committedSize ≤ (⟨κ, img, n⟩ : Execution prog).committedSize :=
  execute_completeX (Inv := guestInv prog Ks Km E0 Ct Q X Pro) hκ hn hval hdec hmain
    (fun C m hC hm ↦ inv_init (hinit C m hC hm).1 (hinit C m hC hm).2)
    (fun C hC ↦ inv_rule_of_specs hκ hC (P C hC) (hQ C hC) hCm (R C hC) (hpro C hC)) (inv_used hu)

end

end LeanVM.Guest.Mode
