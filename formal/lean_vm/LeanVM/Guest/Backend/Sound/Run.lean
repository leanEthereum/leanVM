/-
  LeanVM.Guest.Backend.Sound.Run

  Emission is sound: a halting run through the instructions of a placed statement has the
  statement's meaning, control flow included.
-/

module

public import LeanVM.Guest.Backend.Sound.Sem

/-!
# A run of emitted code has the placed statement's meaning

`PStmt.sem_of_run`: for a function whose code the program holds at its entry (`Loaded`), a run
that enters instruction `pos`, where the instructions of the placed statement `s` lie
(`CodeAt`), and halts after `k` steps, satisfies `PStmt.Sem s`, given every callee's contract
for runs shorter than `n ≥ k` (`FunSpecLtReached`). The continuations are what the run gives at
each exit: the run goes on with at most `k` steps after the statement's last instruction
(`NextOK`), with fewer after a taken jump (`JumpOK`), with fewer after a return (`RetOK`).

The proof is a mutual structural induction on the placed statement, a block, the arms of a stage
and the stages of a chain, for every `k`. A call, a loop helper's closing call and a fused
dispatch use the callee's contract at the steps left after the jump, which are fewer than `k`:
that is the only place the induction on steps enters, and `FunSpecLtReached` carries it.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-- Whether a labelled instruction is a `JUMP`. -/
def LOp.isJump : LOp → Bool
  | .jump .. => true
  | _ => false

/-- The instructions `ops` lie in `code` from instruction `pos`. -/
def CodeAt (code : List LOp) (pos : ℕ) (ops : List LOp) : Prop :=
  ∀ i (h : i < ops.length), code[pos + i]? = some ops[i]

theorem codeAt_nil (code : List LOp) (pos : ℕ) : CodeAt code pos [] :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem codeAt_cons {code : List LOp} {pos : ℕ} {o : LOp} {os : List LOp} :
    CodeAt code pos (o :: os) ↔ code[pos]? = some o ∧ CodeAt code (pos + 1) os := by
  constructor
  · intro h
    refine ⟨h 0 (Nat.zero_lt_succ _), fun i hi => ?_⟩
    have e : pos + 1 + i = pos + (i + 1) := by omega
    rw [e]
    exact h (i + 1) (Nat.succ_lt_succ hi)
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero => exact h0
    | succ i =>
        have e : pos + (i + 1) = pos + 1 + i := by omega
        rw [e]
        exact h1 i (Nat.lt_of_succ_lt_succ hi)

theorem codeAt_append {code : List LOp} {pos : ℕ} {a b : List LOp} :
    CodeAt code pos (a ++ b) ↔ CodeAt code pos a ∧ CodeAt code (pos + a.length) b := by
  induction a generalizing pos with
  | nil => simp [codeAt_nil]
  | cons o os ih =>
      rw [List.cons_append, codeAt_cons, codeAt_cons, ih, List.length_cons, and_assoc]
      have : pos + 1 + os.length = pos + (os.length + 1) := by omega
      rw [this]

theorem codeAt_self (code : List LOp) : CodeAt code 0 code :=
  fun i h => by simp [h]

/-- The program holds the function's code from its entry, before the halting slot. -/
structure Loaded {κ : ℕ} (prog : LeanIsaProgram) (Γ : Site κ) (code : List LOp) : Prop where
  fetch : ∀ i (h : i < code.length),
    prog.fetch (addressOfIndex (Γ.pc0 + i)) = some (Γ.R code[i]).toLeanIsaInstruction
  fits : Γ.pc0 + code.length ≤ 2 ^ prog.logSize - 1

variable {κ : ℕ} {prog : LeanIsaProgram} {Γ : Site κ} {code : List LOp} {fp : K}

theorem Site.R_isJump (Γ : Site κ) (o : LOp) : (Γ.R o).isJump = o.isJump := by
  cases o <;> rfl

theorem Loaded.at (hL : Loaded prog Γ code) {pos : ℕ} {o : LOp} (h : code[pos]? = some o) :
    prog.fetch (addressOfIndex (Γ.pc0 + pos)) = some (Γ.R o).toLeanIsaInstruction ∧
      Γ.pc0 + pos < 2 ^ prog.logSize - 1 := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact ⟨hL.fetch pos hlt, by have := hL.fits; omega⟩

/-! ## Steps -/

/-- The run is at instruction `q` of the function, at frame `fp`, with `k` steps left. -/
def SafeAt (prog : LeanIsaProgram) (Γ : Site κ) (fp : K) (k q : ℕ) : Prop :=
  SafeReached prog Γ.L k ⟨addressOfIndex (Γ.pc0 + q), fp⟩

theorem SafeAt.cast {k q q' : ℕ} (h : SafeAt prog Γ fp k q) (e : q = q') : SafeAt prog Γ fp k q' :=
  e ▸ h

/-- Through a straight-line instruction. -/
theorem step_op (hL : Loaded prog Γ code) {pos k : ℕ} {o : LOp} (hat : code[pos]? = some o)
    (hj : o.isJump = false) (hs : SafeAt prog Γ fp k pos) :
    ∃ k', k = k' + 1 ∧ Holds Γ.L (Γ.pc0 + pos) fp (Γ.R o) ∧ SafeAt prog Γ fp k' (pos + 1) := by
  obtain ⟨hf, hpc⟩ := hL.at hat
  exact SafeReached.fallThrough hf hpc (by rw [Γ.R_isJump, hj]) hs

/-- Through a run of straight-line instructions. -/
theorem seg_run (hL : Loaded prog Γ code) : ∀ (ops : List LOp) (pos k : ℕ),
    (∀ o ∈ ops, o.isJump = false) → CodeAt code pos ops → SafeAt prog Γ fp k pos →
    ∃ k', k = k' + ops.length ∧ SegHolds Γ fp ops pos ∧ SafeAt prog Γ fp k' (pos + ops.length)
  | [], pos, k, _, _, hs => ⟨k, rfl, fun _ h => absurd h (Nat.not_lt_zero _), hs⟩
  | o :: os, pos, k, hj, hat, hs => by
      obtain ⟨h0, h1⟩ := codeAt_cons.mp hat
      obtain ⟨k1, rfl, ho, hs1⟩ := step_op hL h0 (hj o (by simp)) hs
      obtain ⟨k2, rfl, hos, hs2⟩ := seg_run hL os (pos + 1) k1 (fun o' h => hj o' (by simp [h])) h1 hs1
      refine ⟨k2, by simp; omega, fun i hi => ?_, hs2.cast (by simp; omega)⟩
      cases i with
      | zero => simpa using ho
      | succ i =>
          have := hos i (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- Through a `JUMP`. -/
theorem jumpAt_of_run (hL : Loaded prog Γ code) {pos k oc od of : ℕ} {fall : Prop}
    {taken : E → E → Prop} (hat : code[pos]? = some (LOp.jump oc od of))
    (hs : SafeAt prog Γ fp k pos)
    (hfall : ∀ k', k = k' + 1 → SafeAt prog Γ fp k' (pos + 1) → fall)
    (htaken : ∀ k' d f, k = k' + 1 → SafeReached prog Γ.L k' ⟨d.limb 0, f.limb 0⟩ → taken d f) :
    JumpAt Γ fp oc od of fall taken := by
  obtain ⟨hf, hpc⟩ := hL.at hat
  obtain ⟨k', r, rfl, ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, rfl⟩, hs'⟩ :=
    SafeReached.jump (oc := oc) (od := od) (of := of) hf hpc hs
  refine ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, fun h0 => ?_, fun h0 => ?_⟩
  · rw [ite_eq_left h0] at hs'
    exact hfall k' rfl hs'
  · rw [ite_eq_right h0] at hs'
    exact htaken k' d f rfl hs'

/-! ## The continuations a run gives -/

/-- After the statement, the run goes on at instruction `q` with at most `k` steps left. -/
def NextOK (prog : LeanIsaProgram) (Γ : Site κ) (fp : K) (k q : ℕ) (next : Prop) : Prop :=
  ∀ k' ≤ k, SafeAt prog Γ fp k' q → next

/-- After a taken jump, the run goes on with fewer than `k` steps left. -/
def JumpOK (prog : LeanIsaProgram) (Γ : Site κ) (k : ℕ) (kj : E → E → Prop) : Prop :=
  ∀ k' < k, ∀ d f, SafeReached prog Γ.L k' ⟨d.limb 0, f.limb 0⟩ → kj d f

/-- After a return, the run goes on at the frame's return registers with fewer than `k` steps
left. -/
def RetOK (prog : LeanIsaProgram) (Γ : Site κ) (fp : K) (k : ℕ) (kret : Prop) : Prop :=
  ∀ k' < k, ∀ r, retRegs Γ.L fp = some r → SafeReached prog Γ.L k' r → kret

theorem NextOK.mono {k k' q : ℕ} {next : Prop} (h : NextOK prog Γ fp k q next) (hk : k' ≤ k) :
    NextOK prog Γ fp k' q next := fun k'' hk'' => h k'' (Nat.le_trans hk'' hk)

theorem NextOK.cast {k q q' : ℕ} {next : Prop} (h : NextOK prog Γ fp k q next) (e : q = q') :
    NextOK prog Γ fp k q' next := e ▸ h

theorem JumpOK.mono {k k' : ℕ} {kj : E → E → Prop} (h : JumpOK prog Γ k kj) (hk : k' ≤ k) :
    JumpOK prog Γ k' kj := fun k'' hk'' => h k'' (Nat.lt_of_lt_of_le hk'' hk)

theorem RetOK.mono {k k' : ℕ} {kret : Prop} (h : RetOK prog Γ fp k kret) (hk : k' ≤ k) :
    RetOK prog Γ fp k' kret := fun k'' hk'' => h k'' (Nat.lt_of_lt_of_le hk'' hk)

theorem callPre_noJump (c : CallSite) : ∀ o ∈ callPre c, o.isJump = false := by
  intro o ho
  unfold callPre at ho
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | ⟨⟨_, _, rfl⟩ | ho⟩ | ho
  · rfl
  · rfl
  · split at ho
    · obtain rfl := List.mem_singleton.mp ho; rfl
    · simp at ho
  · split at ho <;> simp at ho <;> rcases ho with rfl | rfl <;> rfl

theorem callRets_noJump (nfp : Cell) (nargs : ℕ) (rets : List Cell) :
    ∀ o ∈ callRets nfp nargs rets, o.isJump = false := by
  intro o ho
  simp only [callRets, List.mem_map] at ho
  obtain ⟨_, _, rfl⟩ := ho
  rfl

theorem loopPre_noJump (callee : String) (nfp entry one : Cell) (args : List Cell) :
    ∀ o ∈ loopPre callee nfp entry one args, o.isJump = false := by
  intro o ho
  simp only [loopPre, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false]
    at ho
  rcases ho with (rfl | ⟨_, _, rfl⟩) | rfl | rfl | rfl <;> rfl

theorem dispatchPre_noJump (pos : ℕ) (nfp joinCell x entry : Cell) (first : ℕ) (args : List Cell) :
    ∀ o ∈ dispatchPre pos nfp joinCell x entry first args, o.isJump = false := by
  intro o ho
  simp only [dispatchPre, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false]
    at ho
  rcases ho with (⟨_, _, rfl⟩ | rfl) | rfl | rfl | rfl <;> rfl

/-! ## The statements -/

/-- Positions and sizes agree. -/
local macro "sz" : tactic =>
  `(tactic| first
    | omega
    | (simp [stmtSize, blockSize, stagesSize, elseAt, callPre_length, callRets_length,
        loopPre_length]; done)
    | (simp [stmtSize, blockSize, stagesSize, elseAt, callPre_length, callRets_length,
        loopPre_length]; omega))

/-- A taken call's jump: the callee's contract gives its postcondition and the run back at the
return registers. -/
theorem callSem_of_run {n : ℕ}
    (hC : ∀ f, FunSpecLtReached prog Γ.L n (Γ.ent f) (Γ.Pre f) (Γ.Post f)) {callee : String}
    {k : ℕ} (hk : k < n) {ret : Option (Registers K)}
    {cont : Prop} {d f : E} (hs : SafeReached prog Γ.L k ⟨d.limb 0, f.limb 0⟩)
    (hcont : ∀ k' < k, ∀ r, ret = some r → SafeReached prog Γ.L k' r → cont) :
    CallSem Γ callee ret cont d f := by
  intro hd hpre hret
  have hs' : SafeReached prog Γ.L k ⟨addressOfIndex (Γ.ent callee), f.limb 0⟩ := by
    simpa [hd] using hs
  obtain ⟨k', hk', r, hr, hQ, hs''⟩ := hC callee (f.limb 0) k hk hpre hs'
  exact ⟨hQ, hcont k' hk' r (hret ▸ hr) hs''⟩

mutual
/-- **A run through a placed statement's instructions has its meaning.** -/
theorem PStmt.sem_of_run (hL : Loaded prog Γ code) {n : ℕ}
    (hC : ∀ f, FunSpecLtReached prog Γ.L n (Γ.ent f) (Γ.Pre f) (Γ.Post f)) : ∀ (s : PStmt) (pos k : ℕ) (next : Prop) (kj : E → E → Prop)
    (kret : Prop) (khalt : E → E → Prop), CodeAt code pos (stmtOps s pos) → k ≤ n →
    SafeAt prog Γ fp k pos → NextOK prog Γ fp k (pos + stmtSize s) next → JumpOK prog Γ k kj →
    RetOK prog Γ fp k kret → JumpOK prog Γ k khalt → PStmt.Sem Γ fp s pos next kj kret khalt
  | .op _ o, pos, k, next, kj, kret, khalt, hat, hk, hs, hnext, hjump, hret, hhalt => by
      have h0 : code[pos]? = some o := (codeAt_cons.mp hat).1
      simp only [PStmt.Sem]
      cases o with
      | jump oc od of =>
          exact jumpAt_of_run hL h0 hs (fun k' hk' h => hnext k' (by omega) h)
            (fun k' d f hk' h => hjump k' (by omega) d f h)
      | _ =>
          obtain ⟨k', rfl, ho, hs'⟩ := step_op hL h0 rfl hs
          exact ⟨ho, hnext k' (by omega) hs'⟩
  | .ite _ c bdest sfp zero hasElse edest one nonzero, pos, k, next, kj, kret, khalt, hat, hk, hs,
      hnext, hjump, hret, hhalt => by
      simp only [stmtOps, List.cons_append, List.nil_append, codeAt_cons, codeAt_append,
        blockOps_length] at hat
      obtain ⟨h0, h1, hz, hnz⟩ := hat
      obtain ⟨k1, rfl, hset, hs1⟩ := step_op hL h0 rfl hs
      simp only [PStmt.Sem]
      refine ⟨hset, jumpAt_of_run hL h1 hs1 (fun k2 hk2 hs2 => ?_) (fun k2 d f hk2 hs2 => ?_)⟩
      · subst hk2
        refine PStmt.semList_of_run hL hC zero (pos + 2) k2 _ kj kret khalt hz (by omega)
          (hs2.cast (by omega)) ?_ (hjump.mono (by omega)) (hret.mono (by omega))
          (hhalt.mono (by omega))
        intro k3 hk3 hs3
        cases hasElse with
        | false =>
            exact hnext k3 (by omega) (hs3.cast (by sz))
        | true =>
            simp only [↓reduceIte, codeAt_cons] at hnz ⊢
            obtain ⟨he0, he1, hnz⟩ := hnz
            obtain ⟨k4, rfl, hset', hs4⟩ := step_op hL he0 rfl (hs3.cast (by omega))
            refine ⟨by simpa [Nat.add_assoc] using hset',
              jumpAt_of_run hL he1 hs4 (fun k5 hk5 hs5 => ?_) (fun k5 d f hk5 hs5 => ?_)⟩
            · subst hk5
              exact PStmt.semList_of_run hL hC nonzero _ k5 next kj kret khalt
                (by simpa [elseAt, Nat.add_assoc] using hnz) (by omega)
                (hs5.cast (by sz))
                ((hnext.mono (by omega)).cast (by sz))
                (hjump.mono (by omega)) (hret.mono (by omega)) (hhalt.mono (by omega))
            · rintro rfl rfl
              subst hk5
              have hs6 : SafeAt prog Γ fp k5 (elseAt pos zero true + blockSize nonzero) := by
                simpa [Site.tgt, SafeAt] using hs5
              exact hnext k5 (by omega) (hs6.cast (by sz))
      · rintro rfl rfl
        subst hk2
        have hs3 : SafeAt prog Γ fp k2 (elseAt pos zero hasElse) := by
          simpa [Site.tgt, SafeAt] using hs2
        cases hasElse with
        | false =>
            exact hnext k2 (by omega) (hs3.cast (by sz))
        | true =>
            simp only [↓reduceIte, codeAt_cons] at hnz ⊢
            exact PStmt.semList_of_run hL hC nonzero _ k2 next kj kret khalt
              (by simpa [elseAt, Nat.add_assoc] using hnz.2.2) (by omega) hs3
              ((hnext.mono (by omega)).cast (by sz))
              (hjump.mono (by omega)) (hret.mono (by omega)) (hhalt.mono (by omega))
  | .chain _ join x entry one sfp firsts stages, pos, k, next, kj, kret, khalt, hat, hk, hs,
      hnext, hjump, hret, hhalt => by
      simp only [stmtOps, List.cons_append, List.nil_append, codeAt_cons] at hat
      obtain ⟨h0, h1, h2, hst⟩ := hat
      obtain ⟨k1, rfl, hset, hs1⟩ := step_op hL h0 rfl hs
      obtain ⟨k2, rfl, hslot, hs2⟩ := step_op hL h1 rfl hs1
      simp only [PStmt.Sem]
      refine ⟨hset, hslot, jumpAt_of_run hL h2 hs2 (fun _ _ _ => trivial)
        (fun k3 d f hk3 hs3 => ?_)⟩
      subst hk3
      exact PStmt.stagesJump_of_run hL hC stages (pos + 3) k3 next kret khalt
        (by simpa [Nat.add_assoc] using hst) (by omega)
        ((hnext.mono (by omega)).cast (by sz)) (hret.mono (by omega))
        (hhalt.mono (by omega)) d f hs3
  | .call _ c, pos, k, next, kj, kret, khalt, hat, hk, hs, hnext, hjump, hret, hhalt => by
      simp only [stmtOps, codeAt_append, codeAt_cons, List.length_append, List.length_cons,
        List.length_nil] at hat
      obtain ⟨⟨hpre, hj, -⟩, hrets⟩ := hat
      obtain ⟨k1, rfl, hsegs, hs1⟩ := seg_run hL _ pos k (callPre_noJump c) hpre hs
      have hafter : ∀ k' ≤ k1, SafeAt prog Γ fp k' (pos + (callPre c).length + 1) →
          SegHolds Γ fp (callRets c.nfp c.args.length c.rets) (pos + (callPre c).length + 1) ∧
            next := by
        intro k' hk' hs'
        obtain ⟨k'', rfl, hr, hs''⟩ := seg_run hL _ _ k' (callRets_noJump _ _ _)
          (by simpa [Nat.add_assoc] using hrets) hs'
        exact ⟨hr, hnext k'' (by omega) (hs''.cast (by sz))⟩
      simp only [PStmt.Sem]
      refine ⟨hsegs, jumpAt_of_run hL hj hs1 (fun k2 hk2 hs2 => hafter k2 (by omega) hs2)
        (fun k2 d f hk2 hs2 => ?_)⟩
      subst hk2
      split
      · exact callSem_of_run hC (by omega) hs2
          (fun k' hk' r hr hs' => hret k' (by omega) r hr hs')
      · exact callSem_of_run hC (by omega) hs2 (fun k' hk' r hr hs' => by
          obtain rfl := Option.some.inj hr
          exact hafter k' (by omega) hs')
  | .loopNext _ callee nfp entry oc one args, pos, k, next, kj, kret, khalt, hat, hk, hs, hnext,
      hjump, hret, hhalt => by
      simp only [stmtOps, codeAt_append, codeAt_cons] at hat
      obtain ⟨hpre, hj, -⟩ := hat
      obtain ⟨k1, rfl, hsegs, hs1⟩ := seg_run hL _ pos k (loopPre_noJump _ _ _ _ _) hpre hs
      simp only [PStmt.Sem]
      refine ⟨hsegs, jumpAt_of_run hL hj hs1
        (fun k2 hk2 hs2 => hnext k2 (by omega) (hs2.cast (by sz)))
        (fun k2 d f hk2 hs2 => ?_)⟩
      subst hk2
      exact callSem_of_run hC (by omega) hs2
        (fun k' hk' r hr hs' => hret k' (by omega) r hr hs')
  | .dispatch _ callees nfp joinCell x entry one first args rets, pos, k, next, kj, kret, khalt,
      hat, hk, hs, hnext, hjump, hret, hhalt => by
      simp only [stmtOps, codeAt_append, codeAt_cons, List.length_append, List.length_cons,
        List.length_nil, dispatchPre_length] at hat
      obtain ⟨⟨hpre, hj, -⟩, hrets⟩ := hat
      obtain ⟨k1, rfl, hsegs, hs1⟩ := seg_run hL _ pos k (dispatchPre_noJump _ _ _ _ _ _ _) hpre hs
      rw [dispatchPre_length] at hs1
      simp only [PStmt.Sem]
      refine ⟨hsegs, jumpAt_of_run hL hj hs1 (fun _ _ _ => trivial)
        (fun k2 d f hk2 hs2 callee _ => ?_)⟩
      subst hk2
      refine callSem_of_run hC (by omega) hs2 (fun k' hk' r hr hs' => ?_)
      obtain rfl := Option.some.inj hr
      obtain ⟨k'', rfl, hr', hs''⟩ := seg_run hL _ _ k' (callRets_noJump _ _ _)
        (by simpa [Nat.add_assoc] using hrets) hs'
      exact ⟨hr', hnext k'' (by omega) (hs''.cast (by sz))⟩
  | .ret _ one, pos, k, next, kj, kret, khalt, hat, hk, hs, hnext, hjump, hret, hhalt => by
      obtain ⟨hf, hpc⟩ := hL.at (codeAt_cons.mp hat).1
      obtain ⟨k', r, rfl, ⟨c, d, f, hc, hd, hf', -, -, -, rfl⟩, hs'⟩ :=
        SafeReached.jump (oc := one) (od := 0) (of := 1) hf hpc hs
      refine ⟨c, hc, fun h0 => ?_⟩
      rw [ite_eq_right h0] at hs'
      exact hret k' (by omega) _ (retRegs_eq_some_iff.mpr ⟨d, f, hd, hf', rfl⟩) hs'
  | .halt _ one dest, pos, k, next, kj, kret, khalt, hat, hk, hs, hnext, hjump, hret, hhalt => by
      simp only [stmtOps, codeAt_cons] at hat
      obtain ⟨h0, h1, -⟩ := hat
      obtain ⟨k1, rfl, hset, hs1⟩ := step_op hL h0 rfl hs
      exact ⟨hset, jumpAt_of_run hL h1 hs1 (fun _ _ _ => trivial)
        (fun k2 d f hk2 hs2 => hhalt k2 (by omega) d f hs2)⟩

/-- A run through a block's instructions has its meaning. -/
theorem PStmt.semList_of_run (hL : Loaded prog Γ code) {n : ℕ}
    (hC : ∀ f, FunSpecLtReached prog Γ.L n (Γ.ent f) (Γ.Pre f) (Γ.Post f)) : ∀ (b : List PStmt) (pos k : ℕ) (next : Prop) (kj : E → E → Prop)
    (kret : Prop) (khalt : E → E → Prop), CodeAt code pos (blockOps b pos) → k ≤ n →
    SafeAt prog Γ fp k pos → NextOK prog Γ fp k (pos + blockSize b) next → JumpOK prog Γ k kj →
    RetOK prog Γ fp k kret → JumpOK prog Γ k khalt → PStmt.SemList Γ fp b pos next kj kret khalt
  | [], pos, k, next, kj, kret, khalt, _, _, hs, hnext, _, _, _ => hnext k (Nat.le_refl k) hs
  | s :: ss, pos, k, next, kj, kret, khalt, hat, hk, hs, hnext, hjump, hret, hhalt => by
      rw [blockOps, codeAt_append, stmtOps_length] at hat
      refine PStmt.sem_of_run hL hC s pos k _ kj kret khalt hat.1 hk hs (fun k' hk' hs' => ?_) hjump hret
        hhalt
      exact PStmt.semList_of_run hL hC ss (pos + stmtSize s) k' next kj kret khalt hat.2 (by omega) hs'
        ((hnext.mono hk').cast (by sz)) (hjump.mono hk') (hret.mono hk')
        (hhalt.mono hk')

/-- A run entering the stages of a chain by a jump has the meaning of the arm it enters. -/
theorem PStmt.stagesJump_of_run (hL : Loaded prog Γ code) {n : ℕ}
    (hC : ∀ f, FunSpecLtReached prog Γ.L n (Γ.ent f) (Γ.Pre f) (Γ.Post f)) : ∀ (ss : List (List (List PStmt))) (pos k : ℕ) (next kret : Prop)
    (khalt : E → E → Prop), CodeAt code pos (stagesOps ss pos) → k ≤ n →
    NextOK prog Γ fp k (pos + stagesSize ss) next → RetOK prog Γ fp k kret → JumpOK prog Γ k khalt →
    ∀ d f, SafeReached prog Γ.L k ⟨d.limb 0, f.limb 0⟩ →
      PStmt.StagesJump Γ fp ss pos next kret khalt d f
  | [], pos, k, next, kret, khalt, _, _, hnext, _, _, d, f, hs => by
      rintro rfl rfl
      exact hnext k (Nat.le_refl k) (by simpa [Site.tgt, SafeAt, stagesSize] using hs)
  | s :: ss, pos, k, next, kret, khalt, hat, hk, hnext, hret, hhalt, d, f, hs => by
      rw [stagesOps, codeAt_append, armsOps_length] at hat
      have hlater : ∀ k' ≤ k, ∀ d f, SafeReached prog Γ.L k' ⟨d.limb 0, f.limb 0⟩ →
          PStmt.StagesJump Γ fp ss (pos + armsSize s) next kret khalt d f :=
        fun k' hk' d f hs' => PStmt.stagesJump_of_run hL hC ss (pos + armsSize s) k' next kret khalt
          hat.2 (by omega) ((hnext.mono hk').cast (by sz)) (hret.mono hk')
          (hhalt.mono hk') d f hs'
      exact ⟨PStmt.armsJump_of_run hL hC s pos k _ kret khalt hat.1 hk hlater hret hhalt d f hs,
        hlater k (Nat.le_refl k) d f hs⟩

/-- A run entering the arms of a stage by a jump has the meaning of the arm it enters. -/
theorem PStmt.armsJump_of_run (hL : Loaded prog Γ code) {n : ℕ}
    (hC : ∀ f, FunSpecLtReached prog Γ.L n (Γ.ent f) (Γ.Pre f) (Γ.Post f)) : ∀ (as : List (List PStmt)) (pos k : ℕ) (kj : E → E → Prop)
    (kret : Prop) (khalt : E → E → Prop), CodeAt code pos (armsOps as pos) → k ≤ n →
    (∀ k' ≤ k, ∀ d f, SafeReached prog Γ.L k' ⟨d.limb 0, f.limb 0⟩ → kj d f) →
    RetOK prog Γ fp k kret → JumpOK prog Γ k khalt →
    ∀ d f, SafeReached prog Γ.L k ⟨d.limb 0, f.limb 0⟩ →
      PStmt.ArmsJump Γ fp as pos kj kret khalt d f
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | a :: as, pos, k, kj, kret, khalt, hat, hk, hkj, hret, hhalt, d, f, hs => by
      rw [armsOps, codeAt_append, blockOps_length] at hat
      refine ⟨?_, PStmt.armsJump_of_run hL hC as (pos + blockSize a) k kj kret khalt hat.2 hk hkj hret
        hhalt d f hs⟩
      rintro rfl rfl
      refine PStmt.semList_of_run hL hC a pos k _ kj kret khalt hat.1 hk
        (by simpa [Site.tgt, SafeAt] using hs) (fun k' hk' hs' => ?_)
        (fun k' hk' d f h => hkj k' (by omega) d f h) hret hhalt
      exact hkj k' hk' _ _ (by simpa [Site.tgt, SafeAt] using hs')
end

end
end LeanVM.Guest.Backend
