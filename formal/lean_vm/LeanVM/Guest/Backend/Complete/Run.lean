/-
  LeanVM.Guest.Backend.Complete.Run

  Emission is complete: on a memory where the instructions of a path through a placed statement
  have their meaning, the emitted code runs along it, counted.
-/

module

public import LeanVM.Guest.Backend.Complete.Spec
public import LeanVM.Guest.Backend.Sound.Run

/-!
# The emitted code runs where its instructions hold

The converse of `PStmt.sem_of_run`. For a function whose code the program holds at its entry
(`Loaded`), and a placed statement whose instructions lie at instruction `pos` (`CodeAt`), the
instructions' meaning on `σ`'s path (`cplS`) gives a counted run from `pos` that leaves the
statement one of four ways (`Outc`): past its last instruction, by a taken straight-line jump, by
the frame's return, or by `main`'s closing jump. Its count is at most the path's (`opsS`) and the
callees' it entered.

The proof is one structural induction on the placed statement, a block, the stages of a chain
and the arms of a stage, as `sem_of_run`'s; each construct is a lemma of its own taking the runs
of its blocks as hypotheses.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (RunC)

@[expose] public section

/-- The callees' counts left. -/
def ksum (ks : List Kid) (op : Opcode) : ℕ := (ks.map (·.2 op)).sum

theorem ksum_cons (k : Kid) (ks : List Kid) (op : Opcode) : ksum (k :: ks) op = k.2 op + ksum ks op := by
  simp [ksum]

variable {κ : ℕ} (prog : LeanIsaProgram) (Γ : Site κ) (fp : K)

/-- **What a run from `s` does**, given the path's count `o.1` and whether the path falls through
(`o.2`), the callees `ks`: a counted run, its count and the callees' left within the path's and the
callees', that reaches instruction `e` with `next`, or leaves by a taken jump with `kj`, by the
frame's return with `kret`, or by `main`'s closing jump with `khalt`. Falling through and the
jump are paths that go on. -/
def Outc (s : Registers K) (e : ℕ) (o : (Opcode → ℕ) × Bool) (ks : List Kid)
    (next : List Kid → Prop) (kj : List Kid → E → E → Prop) (kret khalt : Prop) : Prop :=
  ∃ (c : Opcode → ℕ) (ks' : List Kid), (∀ op, c op + ksum ks' op ≤ o.1 op + ksum ks op) ∧
    ((o.2 = true ∧ RunC prog Γ.L s ⟨addressOfIndex (Γ.pc0 + e), fp⟩ c ∧ next ks') ∨
     (o.2 = true ∧ ∃ d f, RunC prog Γ.L s ⟨d.limb 0, f.limb 0⟩ c ∧ kj ks' d f) ∨
     (∃ r, RunC prog Γ.L s r c ∧ retRegs Γ.L fp = some r ∧ kret) ∨
     (∃ d f, RunC prog Γ.L s ⟨d.limb 0, f.limb 0⟩ c ∧
        d = OffsetInstruction.immediateWord (Γ.l.pow Γ.l.sentinel) 0 ∧ f = ofK fp ∧ khalt))

variable {prog Γ fp}

theorem limb_ofK (x : K) : (ofK x).limb 0 = x := by simp

theorem tgt_limb (q : ℕ) : (Γ.tgt q).limb 0 = addressOfIndex (Γ.pc0 + q) := by
  simp [Site.tgt]

/-- A run before. -/
theorem Outc.pre {s t : Registers K} {c0 : Opcode → ℕ} {e : ℕ} {o o' : (Opcode → ℕ) × Bool}
    {ks : List Kid} {next : List Kid → Prop} {kj : List Kid → E → E → Prop} {kret khalt : Prop}
    (h0 : RunC prog Γ.L s t c0) (h : Outc prog Γ fp t e o' ks next kj kret khalt)
    (hle : ∀ op, c0 op + o'.1 op ≤ o.1 op) (hb : o'.2 = true → o.2 = true) :
    Outc prog Γ fp s e o ks next kj kret khalt := by
  obtain ⟨c, ks', hc, halt⟩ := h
  refine ⟨c0 + c, ks', fun op => ?_, ?_⟩
  · have := hc op
    have := hle op
    simp only [Pi.add_apply]
    omega
  · rcases halt with ⟨hb', hr, hn⟩ | ⟨hb', d, f, hr, hk⟩ | ⟨r, hr, hrr, hk⟩ | ⟨d, f, hr, hd, hf, hk⟩
    · exact Or.inl ⟨hb hb', h0.trans hr, hn⟩
    · exact Or.inr (Or.inl ⟨hb hb', d, f, h0.trans hr, hk⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨r, h0.trans hr, hrr, hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨d, f, h0.trans hr, hd, hf, hk⟩))

/-- Weaker continuations, a larger count. -/
theorem Outc.mono {s : Registers K} {e : ℕ} {o o' : (Opcode → ℕ) × Bool} {ks : List Kid}
    {next next' : List Kid → Prop} {kj kj' : List Kid → E → E → Prop} {kret kret' khalt khalt' : Prop}
    (h : Outc prog Γ fp s e o ks next kj kret khalt) (hle : ∀ op, o.1 op ≤ o'.1 op)
    (hb : o.2 = true → o'.2 = true) (hn : ∀ ks', next ks' → next' ks')
    (hj : ∀ ks' d f, kj ks' d f → kj' ks' d f) (hr : kret → kret') (hh : khalt → khalt') :
    Outc prog Γ fp s e o' ks next' kj' kret' khalt' := by
  obtain ⟨c, ks', hc, halt⟩ := h
  refine ⟨c, ks', fun op => (hc op).trans (by have := hle op; omega), ?_⟩
  rcases halt with ⟨hb', hr', hn'⟩ | ⟨hb', d, f, hr', hk⟩ | ⟨r, hr', hrr, hk⟩ | ⟨d, f, hr', hd, hf, hk⟩
  · exact Or.inl ⟨hb hb', hr', hn _ hn'⟩
  · exact Or.inr (Or.inl ⟨hb hb', d, f, hr', hj _ _ _ hk⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr', hrr, hr hk⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨d, f, hr', hd, hf, hh hk⟩))

/-- A run that stops at `e`, counted. -/
theorem Outc.fall {s : Registers K} {e : ℕ} {o : (Opcode → ℕ) × Bool} {ks ks' : List Kid}
    {next : List Kid → Prop} {kj : List Kid → E → E → Prop} {kret khalt : Prop} {c : Opcode → ℕ}
    (hr : RunC prog Γ.L s ⟨addressOfIndex (Γ.pc0 + e), fp⟩ c) (hn : next ks') (hb : o.2 = true)
    (hle : ∀ op, c op + ksum ks' op ≤ o.1 op + ksum ks op) :
    Outc prog Γ fp s e o ks next kj kret khalt :=
  ⟨c, ks', hle, Or.inl ⟨hb, hr, hn⟩⟩

/-- The path through two pieces, the second from where the first falls through. -/
def seqO (o₁ o₂ : (Opcode → ℕ) × Bool) : (Opcode → ℕ) × Bool :=
  if o₁.2 then (o₁.1 + o₂.1, o₂.2) else (o₁.1, false)

/-- **One piece after another**: the second runs from where the first falls through; the first
leaves by a jump only where the second is empty. -/
theorem Outc.bind {s : Registers K} {e₁ e₂ : ℕ} {o₁ o₂ : (Opcode → ℕ) × Bool} {ks : List Kid}
    {next₁ next : List Kid → Prop} {kj₁ kj : List Kid → E → E → Prop} {kret khalt : Prop}
    (h₁ : Outc prog Γ fp s e₁ o₁ ks next₁ kj₁ kret khalt)
    (h₂ : ∀ ks', next₁ ks' →
      Outc prog Γ fp ⟨addressOfIndex (Γ.pc0 + e₁), fp⟩ e₂ o₂ ks' next kj kret khalt)
    (hj : ∀ ks' d f, kj₁ ks' d f → o₂ = (0, true) ∧ kj ks' d f) :
    Outc prog Γ fp s e₂ (seqO o₁ o₂) ks next kj kret khalt := by
  obtain ⟨c, ks', hc, halt⟩ := h₁
  rcases halt with ⟨hb, hr, hn⟩ | ⟨hb, d, f, hr, hk⟩ | ⟨r, hr, hrr, hk⟩ | ⟨d, f, hr, hd, hf, hk⟩
  · obtain ⟨c₂, ks'', hc₂, halt₂⟩ := h₂ ks' hn
    have hseq : seqO o₁ o₂ = (o₁.1 + o₂.1, o₂.2) := by simp [seqO, hb]
    refine ⟨c + c₂, ks'', fun op => ?_, ?_⟩
    · have := hc op
      have := hc₂ op
      rw [hseq]
      simp only [Pi.add_apply]
      omega
    · rw [hseq]
      rcases halt₂ with ⟨hb₂, hr₂, hn₂⟩ | ⟨hb₂, d, f, hr₂, hk⟩ | ⟨r, hr₂, hrr, hk⟩ |
          ⟨d, f, hr₂, hd, hf, hk⟩
      · exact Or.inl ⟨hb₂, hr.trans hr₂, hn₂⟩
      · exact Or.inr (Or.inl ⟨hb₂, d, f, hr.trans hr₂, hk⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨r, hr.trans hr₂, hrr, hk⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨d, f, hr.trans hr₂, hd, hf, hk⟩))
  · obtain ⟨ho, hk'⟩ := hj _ _ _ hk
    have hseq : seqO o₁ o₂ = (o₁.1, true) := by
      simp only [seqO, hb, ho, ↓reduceIte, Prod.mk.injEq, and_true]
      funext op
      simp
    refine ⟨c, ks', fun op => ?_, Or.inr (Or.inl ⟨by rw [hseq], d, f, hr, hk'⟩)⟩
    rw [hseq]
    exact hc op
  · refine ⟨c, ks', fun op => (hc op).trans ?_, Or.inr (Or.inr (Or.inl ⟨r, hr, hrr, hk⟩))⟩
    unfold seqO
    split <;> simp
  · refine ⟨c, ks', fun op => (hc op).trans ?_, Or.inr (Or.inr (Or.inr ⟨d, f, hr, hd, hf, hk⟩))⟩
    unfold seqO
    split <;> simp

/-! ## Steps -/

theorem R_opcode (Γ : Site κ) (o : LOp) : (Γ.R o).toLeanIsaInstruction.opcode = lopCode o := by
  cases o with
  | set o k => cases k <;> rfl
  | _ => rfl

theorem lopCnt_R (Γ : Site κ) (o : LOp) :
    (fun op => if op = (Γ.R o).toLeanIsaInstruction.opcode then 1 else 0) = lopCnt o := by
  rw [R_opcode]
  rfl

variable {code : List LOp}

/-- Through a straight-line instruction that holds, counted. -/
theorem op_runC (hL : Loaded prog Γ code) {pos : ℕ} {o : LOp} (hat : code[pos]? = some o)
    (hj : o.isJump = false) (h : Holds Γ.L (Γ.pc0 + pos) fp (Γ.R o)) :
    RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩ ⟨addressOfIndex (Γ.pc0 + pos + 1), fp⟩
      (lopCnt o) := by
  obtain ⟨hf, hpc⟩ := hL.at hat
  rw [← lopCnt_R Γ o]
  exact B2C.runC_fallThrough hf hpc (by rw [Γ.R_isJump, hj]) h

/-- Through a `JUMP` whose cells hold words of `K`: on to the next instruction at a zero
condition, else to the words of its target cells. -/
theorem jump_runC (hL : Loaded prog Γ code) {pos oc od of : ℕ} {fall : Prop}
    {taken : E → E → Prop} (hat : code[pos]? = some (LOp.jump oc od of))
    (h : JumpAt Γ fp oc od of fall taken) :
    (fall ∧ RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩
        ⟨addressOfIndex (Γ.pc0 + pos + 1), fp⟩ jumpCnt) ∨
      ∃ d f, taken d f ∧ RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩ ⟨d.limb 0, f.limb 0⟩
        jumpCnt := by
  obtain ⟨hf, hpc⟩ := hL.at hat
  obtain ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, hfall, htaken⟩ := h
  by_cases h0 : c = 0
  · refine Or.inl ⟨hfall h0, B2C.runC_jump hf hpc ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, ?_⟩⟩
    simp [h0]
  · refine Or.inr ⟨d, f, htaken h0, B2C.runC_jump hf hpc ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, ?_⟩⟩
    simp [h0]

/-- Through straight-line instructions that hold, counted. -/
theorem seg_runC (hL : Loaded prog Γ code) : ∀ (ops : List LOp) (pos : ℕ),
    (∀ o ∈ ops, o.isJump = false) → CodeAt code pos ops → SegHolds Γ fp ops pos →
    RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩
      ⟨addressOfIndex (Γ.pc0 + (pos + ops.length)), fp⟩ (opsCnt ops)
  | [], pos, _, _, _ => by
      have h0 : opsCnt [] = 0 := by funext op; simp [opsCnt]
      rw [h0]
      simpa using RunC.refl (prog := prog) (L := Γ.L) _
  | o :: os, pos, hj, hat, hs => by
      obtain ⟨h0, h1⟩ := codeAt_cons.mp hat
      have ho : Holds Γ.L (Γ.pc0 + pos) fp (Γ.R o) := hs 0 (by simp)
      have hos : SegHolds Γ fp os (pos + 1) := fun i hi => by
        have := hs (i + 1) (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      have r1 := op_runC hL h0 (hj o (by simp)) ho
      have r2 := seg_runC hL os (pos + 1) (fun o' h => hj o' (by simp [h])) h1 hos
      have e1 : Γ.pc0 + pos + 1 = Γ.pc0 + (pos + 1) := by omega
      rw [e1] at r1
      have := r1.trans r2
      have e2 : Γ.pc0 + (pos + 1 + os.length) = Γ.pc0 + (pos + (o :: os).length) := by
        simp; omega
      rw [e2] at this
      convert this using 1
      funext op
      simp [opsCnt]

theorem runC_cast {s t t' : Registers K} {c c' : Opcode → ℕ} (h : RunC prog Γ.L s t c)
    (ht : t = t') (hc : c = c') : RunC prog Γ.L s t' c' := by
  subst ht hc
  exact h

/-! ## The constructs -/

variable (prog Γ fp) (σ : Val) (code)

/-- A placed statement's instructions run where they hold. -/
def SRuns (s : PStmt) : Prop :=
  ∀ (cs : List Stmt) (pos : ℕ) (ks : List Kid) (next : List Stmt → List Kid → Prop)
    (kj : List Kid → E → E → Prop) (kret khalt : Prop),
    CodeAt code pos (stmtOps s pos) → cplS prog Γ fp σ s cs pos ks next kj kret khalt →
    Outc prog Γ fp ⟨addressOfIndex (Γ.pc0 + pos), fp⟩ (pos + stmtSize s)
      ((opsS σ s cs).1, (opsS σ s cs).2.2) ks (next (opsS σ s cs).2.1) kj kret khalt

/-- A placed block's instructions run where they hold. -/
def LRuns (ps : List PStmt) : Prop :=
  ∀ (cs : List Stmt) (pos : ℕ) (ks : List Kid) (next : List Kid → Prop)
    (kj : List Kid → E → E → Prop) (kret khalt : Prop),
    CodeAt code pos (blockOps ps pos) → cplL prog Γ fp σ ps cs pos ks next kj kret khalt →
    Outc prog Γ fp ⟨addressOfIndex (Γ.pc0 + pos), fp⟩ (pos + blockSize ps) (opsL σ ps cs) ks next
      kj kret khalt

/-- A jump into a chain's stages runs where their instructions hold. -/
def StRuns (sts : List (List (List PStmt))) : Prop :=
  ∀ (cms : List Stmt) (pos : ℕ) (next : List Kid → Prop) (kret khalt : Prop) (ks : List Kid)
    (d f : E), CodeAt code pos (stagesOps sts pos) →
    cplStages prog Γ fp σ sts cms pos next kret khalt ks d f →
    Outc prog Γ fp ⟨d.limb 0, f.limb 0⟩ (pos + stagesSize sts) (opsStages σ sts cms) ks next
      (fun _ _ _ => False) kret khalt

/-- A jump into a stage's arms runs where their instructions hold, and leaves by a jump. -/
def ArRuns (xv : V) (pas : List (List PStmt)) : Prop :=
  ∀ (arms : List (List Stmt)) (j pos : ℕ) (kj : List Kid → E → E → Prop) (kret khalt : Prop)
    (ks : List Kid) (d f : E), CodeAt code pos (armsOps pas pos) →
    cplArms prog Γ fp σ xv pas arms j pos kj kret khalt ks d f →
    Outc prog Γ fp ⟨d.limb 0, f.limb 0⟩ 0 (opsArms σ xv pas arms j) ks (fun _ => False) kj kret
      khalt

variable {prog Γ fp σ code}

/-- **One instruction.** -/
theorem op_runs (hL : Loaded prog Γ code) (h : List LHint) (o : LOp) :
    SRuns prog Γ fp code σ (.op h o) := by
  intro cs pos ks next kj kret khalt hat hc
  have h0 : code[pos]? = some o := (codeAt_cons.mp hat).1
  simp only [opsS, stmtSize]
  cases o
  case jump oc od of =>
    simp only [cplS, OpSem] at hc
    rcases jump_runC hL h0 hc with ⟨hn, hr⟩ | ⟨d, f, hk, hr⟩
    · exact Outc.fall hr hn rfl (fun _ => le_rfl)
    · exact ⟨jumpCnt, ks, fun _ => le_rfl, Or.inr (Or.inl ⟨rfl, d, f, hr, hk⟩)⟩
  all_goals
    simp only [cplS, OpSem] at hc
    obtain ⟨hh, hn⟩ := hc
    exact Outc.fall (op_runC hL h0 rfl hh) hn rfl (fun _ => le_rfl)

/-- **The empty block.** -/
theorem nil_runs : LRuns prog Γ fp code σ [] := by
  intro cs pos ks next kj kret khalt _ hc
  simp only [cplL] at hc
  refine Outc.fall (c := 0) (by simpa [blockSize] using RunC.refl (prog := prog) (L := Γ.L) _) hc rfl
    (fun op => by simp [opsL])

/-- **A statement, then a block.** -/
theorem cons_runs {s : PStmt} {ss : List PStmt} (hs : SRuns prog Γ fp code σ s)
    (hss : LRuns prog Γ fp code σ ss) : LRuns prog Γ fp code σ (s :: ss) := by
  intro cs pos ks next kj kret khalt hat hc
  simp only [blockOps, codeAt_append, stmtOps_length] at hat
  simp only [cplL] at hc
  have h1 := hs cs pos ks _ _ kret khalt hat.1 hc
  have h := Outc.bind (o₂ := opsL σ ss (opsS σ s cs).2.1) h1
    (fun ks' hn => hss _ (pos + stmtSize s) ks' next kj kret khalt hat.2 hn)
    (fun ks' d f hk => by
      cases ss with
      | nil => simp at hk; exact ⟨rfl, hk⟩
      | cons _ _ => simp at hk)
  have e : pos + blockSize (s :: ss) = pos + stmtSize s + blockSize ss := by
    simp [blockSize]; omega
  rw [e]
  convert h using 2
  simp only [opsL, seqO]

theorem Outc.cast_e {s : Registers K} {e e' : ℕ} {o : (Opcode → ℕ) × Bool} {ks : List Kid}
    {next : List Kid → Prop} {kj : List Kid → E → E → Prop} {kret khalt : Prop}
    (h : Outc prog Γ fp s e o ks next kj kret khalt) (he : e = e') :
    Outc prog Γ fp s e' o ks next kj kret khalt := he ▸ h

theorem set_jump (o : Cell) (k : KVal) (oc od of : Cell) :
    lopCnt (.set o k) + lopCnt (.jump oc od of) = setJump := by
  funext op
  cases op <;> rfl

/-- A `SET` that holds, then a `JUMP` with its cells in `K`. -/
theorem setJump_runC (hL : Loaded prog Γ code) {pos o oc od of : ℕ} {k : KVal} {fall : Prop}
    {taken : E → E → Prop} (h0 : code[pos]? = some (LOp.set o k))
    (h1 : code[pos + 1]? = some (LOp.jump oc od of)) (hs : Holds Γ.L (Γ.pc0 + pos) fp (Γ.R (.set o k)))
    (hj : JumpAt Γ fp oc od of fall taken) :
    (fall ∧ RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩
        ⟨addressOfIndex (Γ.pc0 + (pos + 2)), fp⟩ setJump) ∨
      ∃ d f, taken d f ∧ RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩ ⟨d.limb 0, f.limb 0⟩
        setJump := by
  have r0 := op_runC hL h0 rfl hs
  rcases jump_runC hL h1 hj with ⟨hf, r1⟩ | ⟨d, f, hk, r1⟩
  · exact Or.inl ⟨hf, runC_cast (r0.trans r1) (by congr 2) (set_jump o k oc od of)⟩
  · exact Or.inr ⟨d, f, hk, runC_cast (r0.trans r1) rfl (set_jump o k oc od of)⟩

/-- **A branch.** -/
theorem ite_runs (hL : Loaded prog Γ code) {h : List LHint} {c bdest sfp : Cell}
    {zero : List PStmt} {hasElse : Bool} {edest one : Cell} {nonzero : List PStmt}
    (hz : LRuns prog Γ fp code σ zero) (hn : LRuns prog Γ fp code σ nonzero) :
    SRuns prog Γ fp code σ (.ite h c bdest sfp zero hasElse edest one nonzero) := by
  intro cs pos ks next kj kret khalt hat hc
  simp only [stmtOps, List.cons_append, List.nil_append, codeAt_cons, codeAt_append,
    blockOps_length] at hat
  obtain ⟨h0, h1, hzat, hnat⟩ := hat
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [cplS, hcs] at hc
  cases s
  case ite cv z n =>
    simp only [cplS, hcs] at hc
    obtain ⟨hset, hjmp⟩ := hc
    simp only [opsS, hcs]
    rcases setJump_runC hL h0 h1 hset hjmp with ⟨⟨hσ, hzc⟩, r0⟩ | ⟨d, f, ⟨hσ, hd, hf, hk⟩, r0⟩
    · simp only [hσ, ↓reduceIte]
      have hZ := hz z (pos + 2) ks _ _ kret khalt hzat hzc
      cases hasElse
      · refine Outc.pre r0 ((hZ.mono (o' := opsL σ zero z) (fun _ => le_rfl) id (fun _ h => h)
          (fun _ _ _ h => h.elim) id id).cast_e (by simp [stmtSize]; omega))
          (fun op => by simp) (fun h => h)
      · simp only [↓reduceIte, codeAt_cons] at hnat
        obtain ⟨h2, h3, -⟩ := hnat
        have h2' : code[pos + 2 + blockSize zero]? = some _ := h2
        have hrest : ∀ ks', (Holds Γ.L (Γ.pc0 + (pos + 2 + blockSize zero)) fp
              (Γ.R (.set edest (.local (elseAt pos zero true + blockSize nonzero)))) ∧
            JumpAt Γ fp one edest sfp False (fun d f =>
              d = Γ.tgt (elseAt pos zero true + blockSize nonzero) ∧ f = ofK fp ∧ next rest ks')) →
            Outc prog Γ fp ⟨addressOfIndex (Γ.pc0 + (pos + 2 + blockSize zero)), fp⟩
              (pos + stmtSize (.ite h c bdest sfp zero true edest one nonzero)) (setJump, true) ks'
              (next rest) (fun _ _ _ => False) kret khalt := by
          rintro ks' ⟨hs', hj'⟩
          rcases setJump_runC hL h2' h3 hs' hj' with ⟨hfalse, -⟩ | ⟨d, f, ⟨hd, hf, hk⟩, r⟩
          · exact hfalse.elim
          · subst hd hf
            refine Outc.fall (runC_cast (c' := setJump) r ?_ rfl) hk rfl (fun op => by simp)
            rw [tgt_limb, limb_ofK]
            congr 2
            simp [elseAt, stmtSize]
            omega
        have hB := Outc.bind hZ hrest (fun _ _ _ h => h.elim)
        refine Outc.pre r0 (hB.mono (o' := seqO (opsL σ zero z) (setJump, true)) (fun _ => le_rfl)
          id (fun _ h => h) (fun _ _ _ h => h.elim) id id) (fun op => ?_) (fun h => ?_)
        · simp only [seqO]
          split
          · simp_all
            omega
          · simp_all
        · simp only [seqO] at h
          split at h <;> simp_all
    · subst hd hf
      have r0' : RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩
          ⟨addressOfIndex (Γ.pc0 + elseAt pos zero hasElse), fp⟩ setJump :=
        runC_cast r0 (by rw [tgt_limb, limb_ofK]) rfl
      simp only [hσ, ↓reduceIte]
      cases hasElse
      · simp only [Bool.false_eq_true, ↓reduceIte] at hk ⊢
        refine Outc.fall (runC_cast (c' := setJump) r0' ?_ rfl) hk rfl (fun op => by simp)
        congr 2
        simp [elseAt, stmtSize]
        omega
      · simp only [↓reduceIte, codeAt_cons] at hk hnat ⊢
        obtain ⟨-, -, hnat⟩ := hnat
        have hN := hn n (elseAt pos zero true) ks _ _ kret khalt
          (by simpa [elseAt, Nat.add_assoc] using hnat) hk
        refine Outc.pre r0' ((hN.mono (o' := opsL σ nonzero n) (fun _ => le_rfl) id (fun _ h => h)
          (fun _ _ _ h => h.elim) id id).cast_e ?_) (fun op => by simp) id
        simp [elseAt, stmtSize]
        omega
  all_goals simp [cplS, hcs] at hc

/-- A `JUMP` that cannot fall through reads its target words from its cells. -/
theorem jumpAt_reads {oc od of : ℕ} {fall : Prop} {taken : E → E → Prop}
    (h : JumpAt Γ fp oc od of fall taken) :
    JumpAt Γ fp oc od of fall (fun d f => taken d f ∧ Γ.L.read (fp * addressOfIndex od) = some d ∧
      Γ.L.read (fp * addressOfIndex of) = some f) := by
  obtain ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, hfall, htaken⟩ := h
  exact ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, hfall, fun h0 => ⟨htaken h0, hd, hf⟩⟩

/-- **The return.** -/
theorem ret_runs (hL : Loaded prog Γ code) (h : List LHint) (one : Cell) :
    SRuns prog Γ fp code σ (.ret h one) := by
  intro cs pos ks next kj kret khalt hat hc
  have h0 : code[pos]? = some (LOp.jump one 0 1) := (codeAt_cons.mp hat).1
  simp only [cplS] at hc
  simp only [opsS]
  rcases jump_runC hL h0 (jumpAt_reads hc) with ⟨hfalse, -⟩ | ⟨d, f, ⟨hk, hd, hf⟩, r⟩
  · exact hfalse.elim
  · refine ⟨jumpCnt, ks, fun _ => le_rfl, Or.inr (Or.inr (Or.inl ⟨_, r, ?_, hk⟩))⟩
    simp only [retRegs, hd, hf, Option.bind_some, Option.map_some]

theorem set_slot_jump (o : Cell) (k : KVal) (x first e oc od of : Cell) :
    lopCnt (.set o k) + lopCnt (.slot x first e) + lopCnt (.jump oc od of) = chainHead := by
  funext op
  cases op <;> rfl

/-- **`main`'s end.** -/
theorem halt_runs (hL : Loaded prog Γ code) (h : List LHint) (one dest : Cell) :
    SRuns prog Γ fp code σ (.halt h one dest) := by
  intro cs pos ks next kj kret khalt hat hc
  simp only [stmtOps, codeAt_cons] at hat
  obtain ⟨h0, h1, -⟩ := hat
  simp only [cplS] at hc
  obtain ⟨hs, hj⟩ := hc
  simp only [opsS]
  rcases setJump_runC hL h0 h1 hs (jumpAt_reads hj) with ⟨hfalse, -⟩ | ⟨d, f, ⟨⟨hf, hk⟩, hd, -⟩, r⟩
  · exact hfalse.elim
  · refine ⟨setJump, ks, fun _ => le_rfl, Or.inr (Or.inr (Or.inr ⟨d, f, r, ?_, hf, hk⟩))⟩
    have hs' : Γ.L.read (fp * addressOfIndex dest) =
        some (OffsetInstruction.immediateWord (Γ.l.pow Γ.l.sentinel) 0) := hs
    exact Option.some.inj (hd.symm.trans hs')

/-- **A call.** -/
theorem call_runs (hL : Loaded prog Γ code) (h : List LHint) (c : CallSite) :
    SRuns prog Γ fp code σ (.call h c) := by
  intro cs pos ks next kj kret khalt hat hc
  simp only [stmtOps, codeAt_append, codeAt_cons] at hat
  obtain ⟨⟨hpre, hj, -⟩, hrets⟩ := hat
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [cplS, hcs] at hc
  rcases ks with _ | ⟨⟨kfp, ck⟩, ks'⟩
  · simp [cplS, hcs] at hc
  simp only [cplS, hcs] at hc
  obtain ⟨hseg, hjmp⟩ := hc
  simp only [opsS, hcs]
  have hlen := callPre_length c
  have r0 := seg_runC hL (callPre c) pos (callPre_noJump c) hpre hseg
  have hrets' : CodeAt code (pos + (callPre c).length + 1) (callRets c.nfp c.args.length c.rets) := by
    simpa [List.length_append, Nat.add_assoc] using hrets
  have hend : pos + (callPre c).length + 1 + (callRets c.nfp c.args.length c.rets).length =
      pos + stmtSize (.call h c) := by
    simp only [stmtSize, callRets_length, hlen]; omega
  rcases jump_runC hL hj hjmp with ⟨⟨hnt, hsr, hn⟩, r1⟩ | ⟨d, f, ⟨ht, hd, hf, r, ⟨hrr, hrun⟩, hk⟩, r1⟩
  · have r2 := seg_runC hL _ _ (callRets_noJump _ _ _) hrets' hsr
    refine Outc.fall (runC_cast ((r0.trans r1).trans r2) (by rw [hend]) rfl) hn
      (by simp [hnt]) (fun op => ?_)
    simp only [Pi.add_apply, ksum_cons]
    omega
  · subst hd hf
    have r1' := runC_cast r1 (by rw [limb_ofK, limb_ofK]) rfl
    have rk := (r0.trans r1').trans hrun
    cases htl : c.tail
    · simp only [htl, Bool.false_eq_true, ↓reduceIte] at hk
      obtain ⟨rfl, hsr, hn⟩ := hk
      have r2 := seg_runC hL _ _ (callRets_noJump _ _ _) hrets' hsr
      refine Outc.fall (runC_cast (rk.trans r2) (by rw [hend]) rfl) hn (by simp)
        (fun op => ?_)
      simp only [Pi.add_apply, ksum_cons]
      omega
    · simp only [htl, ↓reduceIte] at hk
      obtain ⟨hrf, hk⟩ := hk
      refine ⟨_, ks', fun op => ?_, Or.inr (Or.inr (Or.inl ⟨r, rk, hrf, hk⟩))⟩
      simp only [Pi.add_apply, ksum_cons]
      omega

/-- **A loop helper's closing call.** -/
theorem loopNext_runs (hL : Loaded prog Γ code) (h : List LHint) (callee : String)
    (nfp entry oc one : Cell) (args : List Cell) :
    SRuns prog Γ fp code σ (.loopNext h callee nfp entry oc one args) := by
  intro cs pos ks next kj kret khalt hat hc
  simp only [stmtOps, codeAt_append, codeAt_cons] at hat
  obtain ⟨hpre, hj, -⟩ := hat
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [cplS, hcs] at hc
  rcases ks with _ | ⟨⟨kfp, ck⟩, ks'⟩
  · simp [cplS, hcs] at hc
  simp only [cplS, hcs] at hc
  obtain ⟨hseg, hjmp⟩ := hc
  simp only [opsS, hcs]
  have hlen := loopPre_length callee nfp entry one args
  have r0 := seg_runC hL _ pos (loopPre_noJump callee nfp entry one args) hpre hseg
  rcases jump_runC hL hj hjmp with ⟨⟨hnt, hn⟩, r1⟩ | ⟨d, f, ⟨ht, hd, hf, r, ⟨hrr, hrun⟩, hrf, hk⟩, r1⟩
  · refine Outc.fall (runC_cast (r0.trans r1) ?_ rfl) hn (by simp [hnt]) (fun op => ?_)
    · simp only [stmtSize, hlen]
      congr 2
    · simp only [Pi.add_apply, ksum_cons]
      omega
  · subst hd hf
    have r1' := runC_cast r1 (by rw [limb_ofK, limb_ofK]) rfl
    refine ⟨_, ks', fun op => ?_, Or.inr (Or.inr (Or.inl ⟨r, (r0.trans r1').trans hrun, hrf, hk⟩))⟩
    simp only [Pi.add_apply, ksum_cons]
    omega

theorem opsCnt_dispatchPre (pos : ℕ) (nfp joinCell x entry : Cell) (first : ℕ) (args : List Cell) :
    opsCnt (dispatchPre pos nfp joinCell x entry first args) =
      opsCnt (dispatchPre 0 nfp joinCell x entry first args) := by
  unfold opsCnt dispatchPre
  funext op
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons]
  rfl

/-- **A fused dispatch.** -/
theorem dispatch_runs (hL : Loaded prog Γ code) (h : List LHint) (callees : List String)
    (nfp joinCell x entry one : Cell) (first : ℕ) (args rets : List Cell) :
    SRuns prog Γ fp code σ (.dispatch h callees nfp joinCell x entry one first args rets) := by
  intro cs pos ks next kj kret khalt hat hc
  simp only [stmtOps, codeAt_append, codeAt_cons] at hat
  obtain ⟨⟨hpre, hj, -⟩, hrets⟩ := hat
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [cplS, hcs] at hc
  rcases ks with _ | ⟨⟨kfp, ck⟩, ks'⟩
  · simp [cplS, hcs] at hc
  simp only [cplS, hcs] at hc
  obtain ⟨hseg, hjmp⟩ := hc
  simp only [opsS, hcs]
  have hlen := dispatchPre_length pos nfp joinCell x entry first args
  have r0 := seg_runC hL _ pos (dispatchPre_noJump pos nfp joinCell x entry first args) hpre hseg
  rcases jump_runC hL hj hjmp with ⟨hfalse, -⟩ | ⟨d, f, ⟨hf, g, -, hd, r, ⟨hrr, hrun⟩, rfl, hsr, hn⟩, r1⟩
  · exact hfalse.elim
  · subst hd hf
    have r1' := runC_cast r1 (by rw [limb_ofK, limb_ofK]) rfl
    have hrets' : CodeAt code (pos + args.length + 5) (callRets nfp args.length rets) := by
      have e : pos + (dispatchPre pos nfp joinCell x entry first args ++
          [LOp.jump one entry nfp]).length = pos + args.length + 5 := by
        simp [hlen]; omega
      rw [← e]
      exact hrets
    have r2 := seg_runC hL _ _ (callRets_noJump _ _ _) hrets' hsr
    refine Outc.fall (runC_cast (((r0.trans r1').trans hrun).trans r2) ?_ rfl) hn rfl (fun op => ?_)
    · simp only [stmtSize, callRets_length]
      congr 2
      omega
    · simp only [Pi.add_apply, ksum_cons, opsCnt_dispatchPre pos]
      omega

/-- A block that falls off its end jumps to the next instruction. -/
theorem Outc.fall_jump {s : Registers K} {e : ℕ} {o : (Opcode → ℕ) × Bool} {ks : List Kid}
    {kj : List Kid → E → E → Prop} {kret khalt : Prop}
    (h : Outc prog Γ fp s e o ks (fun ks' => kj ks' (Γ.tgt e) (ofK fp)) kj kret khalt) (e' : ℕ) :
    Outc prog Γ fp s e' o ks (fun _ => False) kj kret khalt := by
  obtain ⟨c, ks', hc, halt⟩ := h
  refine ⟨c, ks', hc, ?_⟩
  rcases halt with ⟨hb, hr, hn⟩ | ⟨hb, d, f, hr, hk⟩ | ⟨r, hr, hrr, hk⟩ | ⟨d, f, hr, hd, hf, hk⟩
  · exact Or.inr (Or.inl ⟨hb, _, _, runC_cast hr (by rw [tgt_limb, limb_ofK]) rfl, hn⟩)
  · exact Or.inr (Or.inl ⟨hb, d, f, hr, hk⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr, hrr, hk⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨d, f, hr, hd, hf, hk⟩))

/-- **One piece, then another entered by its jump.** -/
theorem Outc.bindJ {s : Registers K} {e₁ e₂ : ℕ} {o₁ o₂ : (Opcode → ℕ) × Bool} {ks : List Kid}
    {next : List Kid → Prop} {kj₁ kj : List Kid → E → E → Prop} {kret khalt : Prop}
    (h₁ : Outc prog Γ fp s e₁ o₁ ks (fun _ => False) kj₁ kret khalt)
    (h₂ : ∀ ks' d f, kj₁ ks' d f →
      Outc prog Γ fp ⟨d.limb 0, f.limb 0⟩ e₂ o₂ ks' next kj kret khalt) :
    Outc prog Γ fp s e₂ (seqO o₁ o₂) ks next kj kret khalt := by
  obtain ⟨c, ks', hc, halt⟩ := h₁
  rcases halt with ⟨-, -, hn⟩ | ⟨hb, d, f, hr, hk⟩ | ⟨r, hr, hrr, hk⟩ | ⟨d, f, hr, hd, hf, hk⟩
  · exact hn.elim
  · obtain ⟨c₂, ks'', hc₂, halt₂⟩ := h₂ ks' d f hk
    have hseq : seqO o₁ o₂ = (o₁.1 + o₂.1, o₂.2) := by simp [seqO, hb]
    refine ⟨c + c₂, ks'', fun op => ?_, ?_⟩
    · have := hc op
      have := hc₂ op
      rw [hseq]
      simp only [Pi.add_apply]
      omega
    · rw [hseq]
      rcases halt₂ with ⟨hb₂, hr₂, hn₂⟩ | ⟨hb₂, d, f, hr₂, hk⟩ | ⟨r, hr₂, hrr, hk⟩ |
          ⟨d, f, hr₂, hd, hf, hk⟩
      · exact Or.inl ⟨hb₂, hr.trans hr₂, hn₂⟩
      · exact Or.inr (Or.inl ⟨hb₂, d, f, hr.trans hr₂, hk⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨r, hr.trans hr₂, hrr, hk⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨d, f, hr.trans hr₂, hd, hf, hk⟩))
  · refine ⟨c, ks', fun op => (hc op).trans ?_, Or.inr (Or.inr (Or.inl ⟨r, hr, hrr, hk⟩))⟩
    unfold seqO
    split <;> simp
  · refine ⟨c, ks', fun op => (hc op).trans ?_, Or.inr (Or.inr (Or.inr ⟨d, f, hr, hd, hf, hk⟩))⟩
    unfold seqO
    split <;> simp

/-- **No arms.** -/
theorem armsNil_runs (xv : V) : ArRuns prog Γ fp code σ xv [] := by
  intro arms j pos kj kret khalt ks d f _ hc
  simp [cplArms] at hc

/-- **An arm, then the arms after it.** -/
theorem armsCons_runs {xv : V} {pa : List PStmt} {pas : List (List PStmt)}
    (hpa : LRuns prog Γ fp code σ pa) (hpas : ArRuns prog Γ fp code σ xv pas) :
    ArRuns prog Γ fp code σ xv (pa :: pas) := by
  intro arms j pos kj kret khalt ks d f hat hc
  simp only [armsOps, codeAt_append, blockOps_length] at hat
  rcases arms with _ | ⟨a, as⟩
  · simp [cplArms] at hc
  simp only [cplArms] at hc
  simp only [opsArms]
  by_cases hx : σ xv = ofK (addressOfIndex j)
  · simp only [hx, ↓reduceIte] at hc ⊢
    obtain ⟨rfl, rfl, hb⟩ := hc
    rw [tgt_limb, limb_ofK]
    exact (hpa a pos ks _ kj kret khalt hat.1 hb).fall_jump 0
  · simp only [hx, ↓reduceIte] at hc ⊢
    exact hpas as (j + 1) (pos + blockSize pa) kj kret khalt ks d f hat.2 hc

/-- **Past the last stage: the join.** -/
theorem stagesNil_runs : StRuns prog Γ fp code σ [] := by
  intro cms pos next kret khalt ks d f _ hc
  simp only [cplStages] at hc
  obtain ⟨rfl, rfl, hn⟩ := hc
  rw [tgt_limb, limb_ofK]
  exact Outc.fall (c := 0) (by simpa [stagesSize] using RunC.refl (prog := prog) (L := Γ.L) _) hn
    rfl (fun op => by simp [opsStages])

/-- **A stage, then the stages after it.** -/
theorem stagesCons_runs {st : List (List PStmt)} {sts : List (List (List PStmt))}
    (har : ∀ xv, ArRuns prog Γ fp code σ xv st) (hsts : StRuns prog Γ fp code σ sts) :
    StRuns prog Γ fp code σ (st :: sts) := by
  intro cms pos next kret khalt ks d f hat hc
  simp only [stagesOps, codeAt_append, armsOps_length] at hat
  rcases cms with _ | ⟨m, cms'⟩
  · simp [cplStages] at hc
  cases m
  case match_ xv arms =>
    simp only [cplStages] at hc
    simp only [opsStages]
    have hA := har xv arms 0 pos _ kret khalt ks d f hat.1 hc
    have hB := Outc.bindJ hA (fun ks' d' f' hk =>
      hsts cms' (pos + armsSize st) next kret khalt ks' d' f' hat.2 hk)
    refine (hB.mono (o' := seqO (opsArms σ xv st arms 0) (opsStages σ sts cms')) (fun _ => le_rfl)
      id (fun _ h => h) (fun _ _ _ h => h) id id).cast_e (by simp [stagesSize]; omega) |>.mono
      (fun _ => ?_) ?_ (fun _ h => h) (fun _ _ _ h => h) id id
    · simp only [seqO]
      split <;> simp_all
    · simp only [seqO]
      split <;> simp_all
  all_goals simp [cplStages] at hc

/-- **A chain of `match`es.** -/
theorem chain_runs (hL : Loaded prog Γ code) {h : List LHint} {join x entry one sfp : Cell}
    {firsts : List ℕ} {stages : List (List (List PStmt))} (hst : StRuns prog Γ fp code σ stages) :
    SRuns prog Γ fp code σ (.chain h join x entry one sfp firsts stages) := by
  intro cs pos ks next kj kret khalt hat hc
  simp only [stmtOps, List.cons_append, List.nil_append, codeAt_cons] at hat
  obtain ⟨h0, h1, h2, hsat⟩ := hat
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [cplS, hcs] at hc
  simp only [cplS, hcs] at hc
  obtain ⟨hset, hslot, hjmp⟩ := hc
  simp only [opsS, hcs]
  have r0 := op_runC hL h0 rfl hset
  have r1 := op_runC hL h1 rfl hslot
  rcases jump_runC hL h2 hjmp with ⟨hfalse, -⟩ | ⟨d, f, hk, r2⟩
  · exact hfalse.elim
  have r012 : RunC prog Γ.L ⟨addressOfIndex (Γ.pc0 + pos), fp⟩ ⟨d.limb 0, f.limb 0⟩ chainHead :=
    runC_cast ((r0.trans r1).trans r2) rfl (set_slot_jump _ _ _ _ _ 0 0 0)
  have hS := hst _ (pos + 3) _ kret khalt ks d f hsat hk
  refine Outc.pre r012 ((hS.mono (fun _ => le_rfl) id (fun _ h => h) (fun _ _ _ h => h.elim) id
    id).cast_e (by simp [stmtSize]; omega)) (fun op => by simp) id

/-! ## Every statement -/

mutual
/-- **A placed statement's instructions run where they hold.** -/
theorem stmt_runs (hL : Loaded prog Γ code) : ∀ s : PStmt, SRuns prog Γ fp code σ s
  | .op h o => op_runs hL h o
  | .ite _ _ _ _ zero _ _ _ nonzero => ite_runs hL (block_runs hL zero) (block_runs hL nonzero)
  | .chain _ _ _ _ _ _ _ stages => chain_runs hL (stages_runs hL stages)
  | .call h c => call_runs hL h c
  | .loopNext h callee nfp entry oc one args => loopNext_runs hL h callee nfp entry oc one args
  | .dispatch h callees nfp joinCell x entry one first args rets =>
      dispatch_runs hL h callees nfp joinCell x entry one first args rets
  | .ret h one => ret_runs hL h one
  | .halt h one dest => halt_runs hL h one dest

/-- **A placed block's instructions run where they hold.** -/
theorem block_runs (hL : Loaded prog Γ code) : ∀ ps : List PStmt, LRuns prog Γ fp code σ ps
  | [] => nil_runs
  | s :: ss => cons_runs (stmt_runs hL s) (block_runs hL ss)

/-- **A jump into a chain's stages runs where their instructions hold.** -/
theorem stages_runs (hL : Loaded prog Γ code) :
    ∀ sts : List (List (List PStmt)), StRuns prog Γ fp code σ sts
  | [] => stagesNil_runs
  | st :: sts => stagesCons_runs (fun xv => arms_runs hL st xv) (stages_runs hL sts)

/-- **A jump into a stage's arms runs where their instructions hold.** -/
theorem arms_runs (hL : Loaded prog Γ code) :
    ∀ (pas : List (List PStmt)) (xv : V), ArRuns prog Γ fp code σ xv pas
  | [], xv => armsNil_runs xv
  | pa :: pas, xv => armsCons_runs (block_runs hL pa) (arms_runs hL pas xv)
end

end
end LeanVM.Guest.Backend.Complete
