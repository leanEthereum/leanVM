import Rv64Verifier.Sym.Sound
import Rv64Verifier.Sym.Norm
import Rv64Verifier.Sym.SimpAttr

/-!
# User-facing API

Ported from sig.golf's `SigGolfCandidate.Rv`.

* `BlockSpec code entry k P Q`, `BlockSpec.of_symRun`, `BlockSpec.mono`, `BlockSpec.seq`
* `Expect`, `Result.meets` and `BlockSpec.of_expect`: a block's specification checked by one
  `decide +kernel` of `(symRun ...).any (·.meets cfg x)`, so the kernel runs the executor once
  and nobody has to write its result down
* `Steps.iterate`: the loop-invariant lemma for loops whose body is a block
* `Layout` and `codeAt_layout`: place many segments of one image at once
* `readWordsSym` and `Result.readWords_toState`: reflective reads of the final memory
* the `rv_simp` simp set and the `rv_obligs` tactic
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

/-! ## Block specifications -/

/-- From every state at `entry` satisfying `P`, the machine performs exactly `k` steps and
reaches a state `t` with `Q s t`. -/
def BlockSpec (code : Code) (entry : Word) (k : Nat) (P : MachineState → Prop)
    (Q : MachineState → MachineState → Prop) : Prop :=
  ∀ s, s.pc = entry → P s → ∃ t, Steps code k s t ∧ Q s t

theorem BlockSpec.of_symRun {cfg : Config} {code : Code} {words : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg words pc fuel = some r)
    (hcode : CodeAt code pc words) {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop}
    (hobl : ∀ s, P s → r.obligs s) (hQ : ∀ s c, P s → Q s (r.toState s c)) :
    BlockSpec code pc r.steps P Q := by
  intro s hpc hP
  obtain ⟨c, h⟩ := symRun_sound hrun hcode s hpc (hobl s hP)
  exact ⟨_, h, hQ s c hP⟩

theorem BlockSpec.mono {code : Code} {entry : Word} {k : Nat} {P P' : MachineState → Prop}
    {Q Q' : MachineState → MachineState → Prop} (h : BlockSpec code entry k P Q)
    (hP : ∀ s, P' s → P s) (hQ : ∀ s t, P' s → Q s t → Q' s t) :
    BlockSpec code entry k P' Q' := by
  intro s hpc hs
  obtain ⟨t, h1, h2⟩ := h s hpc (hP s hs)
  exact ⟨t, h1, hQ s t hs h2⟩

/-- Two blocks in sequence. -/
theorem BlockSpec.seq {code : Code} {e₁ e₂ : Word} {k₁ k₂ : Nat} {P₁ P₂ : MachineState → Prop}
    {Q₁ Q₂ : MachineState → MachineState → Prop} (h₁ : BlockSpec code e₁ k₁ P₁ Q₁)
    (h₂ : BlockSpec code e₂ k₂ P₂ Q₂) (hmid : ∀ s t, P₁ s → Q₁ s t → t.pc = e₂ ∧ P₂ t) :
    BlockSpec code e₁ (k₁ + k₂) P₁ (fun s u => ∃ t, Q₁ s t ∧ Q₂ t u) := by
  intro s hpc hs
  obtain ⟨t, ht, hQ₁⟩ := h₁ s hpc hs
  obtain ⟨hpc₂, hP₂⟩ := hmid s t hs hQ₁
  obtain ⟨u, hu, hQ₂⟩ := h₂ t hpc₂ hP₂
  exact ⟨u, Steps.trans ht hu, t, hQ₁, hQ₂⟩

/-! ## Checked expectations -/

/-- What a block is expected to do, checked against the executor's result by `Result.meets`. -/
structure Expect where
  steps : Nat
  /-- the final pc -/
  pc : E
  /-- final register values -/
  regs : List (Reg × E)
  /-- doubleword reads of the final memory -/
  mem : List (Addr × E)
  /-- every doubleword the block writes has one of these addresses -/
  writes : List Addr
  /-- every side condition, of the run and of the reads, is one of these -/
  obl : List Oblig

/-- The final state `t` meets `x`, relative to the initial state `s`. -/
def Expect.Holds (x : Expect) (s t : MachineState) : Prop :=
  t.pc = x.pc.eval s ∧ (∀ p ∈ x.regs, t.getReg p.1 = p.2.eval s) ∧
    (∀ p ∈ x.mem, t.getMem (p.1.eval s) = p.2.eval s) ∧
    ∀ a, (∀ k ∈ x.writes, a ≠ k.eval s) → t.getMem a = s.getMem a

def Result.meets (cfg : Config) (r : Result) (x : Expect) : Bool :=
  r.steps == x.steps && E.acEq r.pc x.pc &&
    x.regs.all (fun p => E.acEq (r.st.regs.get p.1) p.2) &&
    x.mem.all (fun p => match readMem cfg p.1 r.st.mem with
      | some (e, os) => E.acEq e p.2 && os.all (fun o => x.obl.any (Oblig.beq o))
      | none => false) &&
    r.st.mem.all (fun w => x.writes.any (Addr.beq w.1)) &&
    r.st.obl.all (fun o => x.obl.any (Oblig.beq o))

theorem Oblig.holds_of_any {s : MachineState} {l : List Oblig} (hl : Oblig.all s l) {o : Oblig}
    (h : l.any (Oblig.beq o) = true) : o.holds s := by
  obtain ⟨o', ho', hb⟩ := List.any_eq_true.mp h
  rw [Oblig.beq_eq hb]
  exact (Oblig.all_iff s l).mp hl o' ho'

theorem Result.meets_holds {cfg : Config} {r : Result} {x : Expect} (h : r.meets cfg x = true)
    (s : MachineState) (hobl : Oblig.all s x.obl) (c : Word → Option Instr) :
    r.steps = x.steps ∧ r.obligs s ∧ x.Holds s (r.toState s c) := by
  simp only [Result.meets, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hsteps, hpc⟩, hregs⟩, hmem⟩, hwrites⟩, hobls⟩ := h
  refine ⟨hsteps, (Oblig.all_iff s _).mpr fun o ho => Oblig.holds_of_any hobl (hobls o ho),
    ?_, ?_, ?_, ?_⟩
  · exact E.acEq_eval s hpc
  · intro p hp
    rw [Result.toState_getReg]
    exact E.acEq_eval s (hregs p hp)
  · intro p hp
    have hp' := hmem p hp
    split at hp'
    · rename_i e os hr
      simp only [Bool.and_eq_true, List.all_eq_true] at hp'
      rw [Result.toState_getMem, readMem_sound hr s fun o ho => Oblig.holds_of_any hobl (hp'.2 o ho)]
      exact E.acEq_eval s hp'.1
    · cases hp'
  · intro a ha
    apply Result.toState_getMem_frame
    intro w hw
    obtain ⟨k, hk, hb⟩ := List.any_eq_true.mp (hwrites w hw)
    rw [Addr.beq_eq hb]
    exact ha k hk

/-- A block's specification from one kernel check: `hrun` is
`(symRun cfg words pc fuel).any (·.meets cfg x) = true`, proved by `decide +kernel`. -/
theorem BlockSpec.of_expect {cfg : Config} {code : Code} {words : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {x : Expect} (hrun : (symRun cfg words pc fuel).any (·.meets cfg x) = true)
    (hcode : CodeAt code pc words) {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop}
    (hobl : ∀ s, P s → Oblig.all s x.obl) (hQ : ∀ s t, P s → x.Holds s t → Q s t) :
    BlockSpec code pc x.steps P Q := by
  cases hr : symRun cfg words pc fuel with
  | none => rw [hr] at hrun; cases hrun
  | some r =>
    rw [hr] at hrun
    have hm : r.meets cfg x = true := hrun
    intro s hpc hP
    obtain ⟨hsteps, hobls, -⟩ := Result.meets_holds hm s (hobl s hP) s.code
    obtain ⟨c, h⟩ := symRun_sound hr hcode s hpc hobls
    obtain ⟨-, -, hx⟩ := Result.meets_holds hm s (hobl s hP) c
    exact ⟨_, hsteps ▸ h, hQ s _ hP hx⟩

/-! ## Loops -/

/-- Loop-invariant lemma: if from `Inv (i+1)` one body execution (`k` steps) reaches `Inv i`,
then from `Inv n` the machine reaches `Inv 0` in `n * k` steps. -/
theorem Steps.iterate {code : Code} {k : Nat} (Inv : Nat → MachineState → Prop)
    (body : ∀ i s, Inv (i + 1) s → ∃ t, Steps code k s t ∧ Inv i t) :
    ∀ n s, Inv n s → ∃ t, Steps code (n * k) s t ∧ Inv 0 t := by
  intro n
  induction n with
  | zero => intro s h; exact ⟨s, by simpa using Steps.refl code s, h⟩
  | succ n ih =>
    intro s h
    obtain ⟨t, h1, h2⟩ := body n s h
    obtain ⟨u, h3, h4⟩ := ih t h2
    exact ⟨u, Steps.of_eq (Steps.trans h1 h3) (by rw [Nat.succ_mul, Nat.add_comm]), h4⟩

/-! ## Code layout -/

/-- A list of `(instruction offset, segment)` pairs. -/
abbrev Layout := List (Nat × List (BitVec 32))

/-- Offsets are consecutive, starting from `n`. Check once with `decide +kernel`. -/
def layoutOk : Nat → Layout → Bool
  | _, [] => true
  | n, (o, seg) :: rest => (o == n) && layoutOk (n + seg.length) rest

/-- The code of a layout. -/
def layoutCode (L : Layout) : List (BitVec 32) := (L.map Prod.snd).flatten

theorem layout_split : ∀ (L : Layout) (n i o : Nat) (seg : List (BitVec 32)),
    layoutOk n L = true → L[i]? = some (o, seg) →
    ∃ pre post, layoutCode L = pre ++ seg ++ post ∧ n + pre.length = o := by
  intro L
  induction L with
  | nil => intro n i o seg _ h; simp at h
  | cons p L ih =>
    intro n i o seg hok hi
    obtain ⟨o', seg'⟩ := p
    simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hok
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact ⟨[], layoutCode L, by simp [layoutCode], by simp [hok.1]⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨pre, post, h1, h2⟩ := ih _ i o seg hok.2 hi
      refine ⟨seg' ++ pre, post, ?_, ?_⟩
      · simp only [layoutCode, List.map_cons, List.flatten_cons] at h1 ⊢
        rw [h1]; simp
      · simp only [List.length_append]; omega

/-- Segment placement from a layout table. -/
theorem codeAt_layout {code : Code} {L : Layout} (hcode : code.words = layoutCode L)
    (hok : layoutOk 0 L = true) {i o : Nat} {seg : List (BitVec 32)}
    (hi : L[i]? = some (o, seg)) (h4 : code.base.toNat % 4 = 0)
    (hrange : code.base.toNat + 4 * (o + seg.length) < 2 ^ 64) :
    CodeAt code (BitVec.ofNat 64 (code.base.toNat + 4 * o)) seg := by
  obtain ⟨pre, post, h1, h2⟩ := layout_split L 0 i o seg hok hi
  have hpc : (BitVec.ofNat 64 (code.base.toNat + 4 * o)).toNat = code.base.toNat + 4 * o := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine CodeAt.of_append (hcode.trans h1) _ ?_ ?_ ?_ <;> rw [hpc] <;> omega

/-! ## Reading final memory -/

/-- Symbolically read `n` consecutive doublewords starting at `k` from a symbolic memory. -/
def readWordsSym (cfg : Config) (mem : SymMem) (k : Addr) : Nat → Option (List E × List Oblig)
  | 0 => some ([], [])
  | n + 1 =>
    match readMem cfg k mem, readWordsSym cfg mem ⟨k.base, k.off + 8⟩ n with
    | some (e, os), some (es, os') => some (e :: es, os ++ os')
    | _, _ => none

theorem Addr.eval_add8 (s : MachineState) (k : Addr) :
    (⟨k.base, k.off + 8⟩ : Addr).eval s = k.eval s + 8 := by
  rcases k with ⟨_ | b, off⟩
  · rfl
  · simp [Addr.eval, BitVec.add_assoc]

theorem readWordsSym_sound {cfg : Config} {mem : SymMem} (s : MachineState) (t : MachineState)
    (ht : ∀ a, t.getMem a = memEval s mem a) :
    ∀ (n : Nat) (k : Addr) (es : List E) (os : List Oblig),
      readWordsSym cfg mem k n = some (es, os) → (∀ o ∈ os, o.holds s) →
      t.readWords (k.eval s) n = es.map (E.eval s) := by
  intro n
  induction n with
  | zero => intro k es os h _; simp [readWordsSym] at h; rw [h.1]; rfl
  | succ n ih =>
    intro k es os h hos
    simp only [readWordsSym] at h
    split at h
    · rename_i e os1 es' os2 h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [MachineState.readWords_succ, ht, readMem_sound h1 s (fun o ho => hos o
        (List.mem_append_left _ ho)), ← Addr.eval_add8,
        ih _ es' os2 h2 (fun o ho => hos o (List.mem_append_right _ ho))]
      rfl
    · cases h

/-- Reflective `readWords` of a block's final state. -/
theorem Result.readWords_toState (r : Result) (s : MachineState) (c : Word → Option Instr)
    {cfg : Config} {k : Addr} {n : Nat} {es : List E} {os : List Oblig}
    (h : readWordsSym cfg r.st.mem k n = some (es, os)) (hos : Oblig.all s os) :
    (r.toState s c).readWords (k.eval s) n = es.map (E.eval s) :=
  readWordsSym_sound s (r.toState s c) (fun _ => rfl) n k es os h ((Oblig.all_iff s _).mp hos)

/-! ## Deduplicating side conditions -/

/-- Remove duplicate side conditions (`ne` conditions are not deduplicated during execution). -/
def Oblig.dedup : List Oblig → List Oblig
  | [] => []
  | o :: os => if os.any (Oblig.beq o) then Oblig.dedup os else o :: Oblig.dedup os

theorem Oblig.mem_dedup : ∀ {l : List Oblig} {o : Oblig}, o ∈ l → o ∈ Oblig.dedup l := by
  intro l
  induction l with
  | nil => intro o h; cases h
  | cons x xs ih =>
    intro o h
    simp only [Oblig.dedup]
    split
    · rename_i hany
      rcases List.mem_cons.mp h with rfl | h
      · obtain ⟨y, hy, hb⟩ := List.any_eq_true.mp hany
        rw [Oblig.beq_eq hb]; exact ih hy
      · exact ih h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- Prove the side conditions of a block from a deduplicated list. -/
theorem Result.obligs_of_dedup (r : Result) (s : MachineState) {l : List Oblig}
    (hl : Oblig.dedup r.st.obl = l) (h : Oblig.all s l) : r.obligs s := by
  subst hl
  rw [Result.obligs, Oblig.all_iff]
  intro o ho
  exact (Oblig.all_iff s _).mp h o (Oblig.mem_dedup ho)

/-! ## Readability simp set -/

theorem add_ofNat_big (x : Word) (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    x + BitVec.ofNat 64 n = x - BitVec.ofNat 64 (2 ^ 64 - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - n < 2 ^ 64)]
  omega

attribute [rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.pc Result.st Result.steps Result.stop SymState.regs SymState.mem SymState.obl
  BitVec.ofNat_eq_ofNat

open Lean Meta Simp in
/-- `x + c` with a "negative" 64-bit literal `c ≥ 2^63` becomes `x - (2^64 - c)`. -/
simproc [rv_simp] addNegLit ((_ : BitVec 64) + BitVec.ofNat 64 _) := fun e => do
  let_expr HAdd.hAdd _ _ _ _ x c := e | return .continue
  let_expr BitVec.ofNat w n := c | return .continue
  let some wv := (← instantiateMVars w).nat? | return .continue
  unless wv == 64 do return .continue
  let some nv := (← instantiateMVars n).nat? | return .continue
  unless 2 ^ 63 ≤ nv ∧ nv < 2 ^ 64 do return .continue
  let m := 2 ^ 64 - nv
  let rhs ← mkAppM ``HSub.hSub #[x, mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit m)]
  let h1 ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit (2 ^ 63), n])
  let h2 ← mkDecideProof (← mkAppM ``LT.lt #[n, mkNatLit (2 ^ 64)])
  let pf := mkApp4 (mkConst ``add_ofNat_big) x n h1 h2
  -- `add_ofNat_big` states the rhs with `2 ^ 64 - n`; it is defeq to the literal `m`
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  return .done { expr := rhs, proof? := some pf }

/-- `validAccess` as arithmetic on `toNat`. -/
theorem validAccess_eight (a : Word) :
    validAccess 8 a = true ↔ ((0x20 ≤ a.toNat ∧ a.toNat ≤ 0x78000000) ∨
      (0xa0000000 ≤ a.toNat ∧ a.toNat ≤ 0xc0000000)) ∧ a.toNat % 8 = 0 := by
  simp only [validAccess, isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

/-- `rv_obligs [h₁, …]`: unfold the side conditions (`Result.obligs`, `Oblig.all …`) and the
doubleword validity checks to arithmetic on `toNat`, rewrite with the given hypotheses, and close
every conjunct with `omega`. -/
macro "rv_obligs" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| (simp only [rv_simp, validAccess_eight, ne_eq, BitVec.toNat_eq,
      BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, $ts',*] <;>
    (try and_intros) <;> (try trivial) <;> omega))

end Rv64Verifier.Sym
