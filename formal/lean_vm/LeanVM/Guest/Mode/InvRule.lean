module

public import LeanVM.Guest.Mode.InvJump
public import LeanVM.Prover.ExecuteCompleteX

/-!
# The invariant and its rule

`guestInv`: the other tracks' invariant `X` (the witness streams' cursor, the bump pointer, the cells
the run touches below `2^κ`), and the run either halted, in its prologue (`Pro`, the jump table
being written: `__jump_tables`, taken as given), or at the stack the mode walk knows (`StackAt`), the
jump table written. `inv_rule`: it satisfies `InvRule`, given the certificates (`ProgOk`), the value
facts the walk leaves to the reference (`Prem`: the hints' agreement, the residuals, the loops'
termination facts at their entries, the reference's part of each instruction's modedness, and `X`
kept by each hint and instruction), and the prologue's steps. `inv_init`, `inv_used`: it holds
initially and keeps the memory within `2^κ`. `execute_complete_guest`: so the executor is complete
on the program, within the reference's committed size.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- **The invariant.** -/
def guestInv (prog : LeanIsaProgram) (Ks : List Cert) (Km : Cert) (E0 : Env) (X Pro : St → Prop)
    (s : St) : Prop :=
  X s ∧ (Halted prog s ∨ Pro s ∨ (JtMem E0 s.mem ∧ StackAt Ks Km s))

/-- **What the invariant takes of the reference and of the other tracks**, at states on the
reference run where `X` holds: each hint's agreement once its inputs are written, each residual once
its cells are, each function's termination facts at its entry, the reference's part of each
instruction's modedness, and `X` kept by each hint and instruction. -/
structure Prem (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (n : ℕ) (C : Ctx)
    (Ks : List Cert) (X : St → Prop) : Prop where
  hint : ∀ s h, X s → Fine (refMem img) s → OnRef prog img n s → h ∈ (C.hints[s.pc]?).getD [] →
    HintIn s h → HintOk C (refMem img) s h
  res : ∀ K ∈ Ks, ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < K.code.length →
    s.pc = K.F.entry + i → ∀ r ∈ (K.F.res.get i).getD [], ResIn s r → ResHolds s r
  term : ∀ K ∈ Ks, ∀ s, X s → Fine (refMem img) s → OnRef prog img n s → s.pc = K.F.entry →
    ∀ p ∈ K.F.sig.term, LTF s p.1 p.2
  ref : ∀ s op, X s → Fine (refMem img) s → OnRef prog img n s → C.ops[s.pc]? = some op →
    RefOk (refMem img) s op
  xh : ∀ s h s', X s → Fine (refMem img) s → OnRef prog img n s → h ∈ (C.hints[s.pc]?).getD [] →
    runHint C s h = .ok s' → X s'
  xo : ∀ s op s', X s → Fine (refMem img) s → OnRef prog img n s → C.ops[s.pc]? = some op →
    runOp C s op = .ok s' → X { s' with steps := s'.steps + 1 }

/-- `main`'s entry is the stack of `main`'s activation alone. -/
theorem start_stack {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) {s : St} (h : StartMain Km E0 s) : JtMem E0 s.mem ∧ StackAt Ks Km s := by
  obtain ⟨hpc, hfp, hjt, hH⟩ := h
  refine ⟨hjt, ⟨Km, [], 0, 0⟩, [], 0, ⟨P.main, rfl, fun p hp ↦ ?_, by unfold maxCells; norm_num⟩,
    hfp.symm, P.ne Km P.main, by simp [hpc], atOff_zero hH, rfl, rfl, rfl⟩
  rw [P.mainTerm] at hp
  cases hp

/-- **The invariant rule**: from a state of the invariant on the reference run, a step's obligations
hold, the invariant after it among them. -/
theorem inv_rule {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    {Ks : List Cert} {Km : Cert} {E0 : Env} {X Pro : St → Prop} (hκ : κ ≤ 28)
    (hC : Ctx.of prog adv = .ok C) (P : ProgOk prog C Ks Km E0) (R : Prem prog img n C Ks X)
    (hpro : ∀ s op, X s → Pro s → Fine (refMem img) s → OnRef prog img n s → C.ops[s.pc]? = some op →
      StepOk C (refMem img) (fun s' ↦ Pro s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s) :
    InvRule prog img n C (refMem img) (guestInv prog Ks Km E0 X Pro) := by
  obtain ⟨hsize, -⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  intro s op ⟨hX, hI⟩ hs hon hop
  have hXh : ∀ s1 h s2, X s1 → Moves (refMem img) s s1 → h ∈ (C.hints[s.pc]?).getD [] →
      runHint C s1 h = .ok s2 → X s2 := fun s1 h s2 hX1 hm hh e ↦
    R.xh s1 h s2 hX1 hm.fine (onRef_moves hm hon) (by rw [hm.pc]; exact hh) e
  have hXo : ∀ s1 s', X s1 → Moves (refMem img) s s1 → runOp C s1 op = .ok s' →
      X { s' with steps := s'.steps + 1 } := fun s1 s' hX1 hm e ↦
    R.xo s1 op s' hX1 hm.fine (onRef_moves hm hon) (by rw [hm.pc]; exact hop) e
  rcases hI with hH | hP | ⟨hjt, a, rest, i, ha, hfpa, hi, hpc, hat, hbel⟩
  · exact absurd hH (onRef_not_halted hon)
  · refine stepOk_conj X s _ s hX (Moves.refl' hs) hXh (fun s1 s' hX1 hm e _ hI' ↦
      ⟨hXo s1 s' hX1 hm e, ?_⟩) (hpro s op hX hP hs hon hop)
    rcases hI' with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (start_stack P h))
  have hK := P.ok a.K ha.mem
  have hop' : op = opOfOff a.K.code[i] := by
    have := hK.ops i hi
    rw [← hpc, hop] at this
    exact Option.some.inj this
  subst hop'
  have hlen : a.K.F.entry + a.K.F.len < 2 ^ 62 := by
    have := cert_pc hK (show a.K.code.length - 1 < a.K.code.length by omega)
    rw [hK.len]
    omega
  refine step_atX hK hi hpc hat hs (envOk_of P ha.mem hjt) X hX
    (fun s1 h s2 hX1 hm hh e ↦ hXh s1 h s2 hX1 hm (by rw [hpc, hK.hints i hi]; exact hh) e)
    (fun s1 h hX1 hm hh hin ↦ R.hint s1 h hX1 hm.fine (onRef_moves hm hon)
      (by rw [hm.pc, hpc, hK.hints i hi]; exact hh) hin)
    (fun s1 hX1 hm ↦ R.res a.K ha.mem s1 i hX1 hm.fine (onRef_moves hm hon) hi (hm.pc.trans hpc))
    (R.ref s _ hX hs hon hop)
    (fun s1 s' hX1 hm _ e hpc' hfp' hf' hle' hat' ↦ ?_)
    (fun c d f A go A' s1 s' hX1 hins hm hmo hA hj hk e hf' hle' hpcs hvd hvf ↦ ?_)
  · refine ⟨hXo s1 s' hX1 hm e, Or.inr (Or.inr ⟨hjt.mono hle', ?_⟩)⟩
    have hi' : i + 1 < a.K.code.length := by
      by_contra hn
      have heq : i + 1 = a.K.code.length := by omega
      obtain ⟨cur, pend, h0, hh⟩ := hat'
      rw [heq] at h0
      have hc := P.endOk a.K ha.mem cur pend h0
      have hp := preAt_end hK.walk le_rfl h0
      subst hc
      subst hp
      rcases hh with ⟨A, hA, -⟩ | ⟨G, hG, -⟩
      · exact absurd hA List.not_mem_nil
      · exact absurd hG List.not_mem_nil
    exact stack_move ha hfpa hbel hle' hfp' hi' (by show s'.pc = _; rw [hpc', hpc]; rfl)
      (AtOff.mono (s := s') (Mem.le_refl _) rfl hat')
  · have hX' := hXo s1 s' hX1 hm (by rw [hins]; exact e)
    refine ⟨hX', ?_⟩
    have hs1 := hm.fine
    have hle1 := hm.le
    have hfpa1 : a.fp = s1.fp := hfpa.trans hm.fp.symm
    have hbel1 := hbel.mono hle1
    have hjt' : JtMem E0 s'.mem := hjt.mono (Mem.le_trans hle1 hle')
    have hop1 : C.ops[s1.pc]? = some (.jump c d f) := by
      rw [hm.pc, hpc, hK.ops i hi, hins]
      rfl
    rcases onRef_next hκ hC hs1 (onRef_moves hm hon) hop1 hmo e with hon' | hH'
    swap
    · exact Or.inl hH'
    have hterm : ∀ K' ∈ Ks, s'.pc = K'.F.entry →
        ∀ p ∈ K'.F.sig.term, LTF { s' with steps := s'.steps + 1 } p.1 p.2 := fun K' hK' hent ↦
      R.term K' hK' _ hX' (fine_steps hf' _) hon' hent
    cases jumpI_cases hj with
    | ret hd hf hok =>
      subst hd
      subst hf
      have hnot : a.K ≠ Km := fun h ↦ P.mainRet i c (by rw [← h, List.getElem?_eq_getElem hi, hins])
      exact Or.inr (Or.inr ⟨hjt', ret_stack P hsz ha hfpa1 hbel hnot hle1 hs1 hA hok hf' hle'
        (by omega) hvd hvf⟩)
    | fwd e' hS hd h1 h2 =>
      obtain ⟨j, hj, hpcj, hjl⟩ := jump_to_pc hA (envOk_of P ha.mem (hjt.mono hle1))
        (.fwd e' hS hd h1 h2) hS (by omega) hlen hvd
      have hfp' := self_fp hbel1 hfpa1 hA hS hs1.fp hf'.fp hvf
      exact Or.inr (Or.inr ⟨hjt', stack_move ha hfpa hbel (Mem.le_trans hle1 hle')
        (hfp'.trans hm.fp) (hK.len ▸ hjl) hpcj (hk _ rfl _ j hj (Holds.mono (s := s1) (s' := { s' with steps := s'.steps + 1 }) hle' hfp' hA))⟩)
    | halt hS hd hmain =>
      exact Or.inl (halt_of P hsz ha.mem hbel1 hfpa1 hA hS hd hmain hs1.fp hf'.fp hpcs hvd hvf)
    | arms ts hS hts =>
      obtain ⟨j, hj, hpcj, hjl⟩ := jump_to_pc hA (envOk_of P ha.mem (hjt.mono hle1))
        (.arms ts hS hts) hS (by omega) hlen hvd
      have hfp' := self_fp hbel1 hfpa1 hA hS hs1.fp hf'.fp hvf
      exact Or.inr (Or.inr ⟨hjt', stack_move ha hfpa hbel (Mem.le_trans hle1 hle')
        (hfp'.trans hm.fp) (hK.len ▸ hjl) hpcj (hk _ rfl _ j hj (Holds.mono (s := s1) (s' := { s' with steps := s'.steps + 1 }) hle' hfp' hA))⟩)
    | tail e' G hfm hdm hG htail hloop =>
      exact Or.inr (Or.inr ⟨hjt', tail_stack P hsz ha hfpa1 hbel hjt hle1 hs1 hA hfm hdm hG htail hloop
        hf' hle' (by omega) hvd hvf hterm⟩)
    | call mq r G Gs _ hfm h1 h0 hc hok hr1 hr2 =>
      exact Or.inr (Or.inr ⟨hjt', call_stack P hsz ha hfpa1 hbel hjt hle1 hs1 hA hfm h1 h0 hc hok hr1 hr2
        (fun s3 h ↦ hk _ rfl s3 _ (List.mem_singleton_self _) h) hf' hle' (by omega) hvd hvf hterm⟩)

/-- **The invariant holds initially**, the prologue's and `X`'s initial states given. -/
theorem inv_init {prog : LeanIsaProgram} {Ks : List Cert} {Km : Cert} {E0 : Env} {X Pro : St → Prop}
    {s : St} (hX : X s) (hP : Pro s) : guestInv prog Ks Km E0 X Pro s :=
  ⟨hX, Or.inr (Or.inl hP)⟩

/-- **The invariant keeps the memory within `2^κ`**, as `X` does. -/
theorem inv_used {prog : LeanIsaProgram} {Ks : List Cert} {Km : Cert} {E0 : Env} {X Pro : St → Prop}
    {κ : ℕ} (hu : ∀ s, X s → s.mem.used ≤ 2 ^ κ) : ∀ s, guestInv prog Ks Km E0 X Pro s → s.mem.used ≤ 2 ^ κ :=
  fun s h ↦ hu s h.1

/-- **The executor is complete on the program**, within the reference's committed size: under
`execute_completeX`'s hypotheses on the reference, given the certificates, the value facts and the
prologue. -/
theorem execute_complete_guest {prog : LeanIsaProgram} {input : PublicInput} {adv : Advice} {κ n : ℕ}
    {img : MemoryImage κ} {Ks : List Cert} {Km : Cert} {E0 : Env} {X Pro : St → Prop} (hκ : κ ≤ 28)
    (hn : n ≤ maxSteps) (hval : ValidExecution prog input ⟨κ, img, n⟩)
    (hdec : ∀ i, Decodable (prog.instructions i)) (hmain : adv.mainFrame < maxCells)
    (P : ∀ C, Ctx.of prog adv = .ok C → ProgOk prog C Ks Km E0)
    (R : ∀ C, Ctx.of prog adv = .ok C → Prem prog img n C Ks X)
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
  execute_completeX (Inv := guestInv prog Ks Km E0 X Pro) hκ hn hval hdec hmain
    (fun C m hC hm ↦ inv_init (hinit C m hC hm).1 (hinit C m hC hm).2)
    (fun C hC ↦ inv_rule hκ hC (P C hC) (R C hC) (hpro C hC)) (inv_used hu)

end

end LeanVM.Guest.Mode
