import Rv64Verifier.Sym.Read
import Rv64Verifier.Repr

/-!
# What every function proof uses

* Byte ranges as intervals of `toNat` (`Within`, `Apart`), so that `omega` decides them, and
  riscv-zkvm's `ValidMemRange` read as one (`ValidMemRange.bounds`, `.access`, `.sub`).
* The stack below `sp` (`stackLo`, `StackOk`).
* Memory frames (`MemFrame`): `t`'s memory is `s`'s outside a range; they compose along a run.
* Reading a generated block's `Expect`: a register (`Expect.Holds.reg_eq`), a written doubleword
  (`Expect.Holds.mem_eq`), registers it keeps (`Expect.keeps`), its frame (`Expect.Holds.memFrame`).
* `E` values from their limbs (`limbs_add`, `limbs_one`, `eAt_eq_of_limbs`, `eAt_congr`).
* Calls that never return (`FunSpec.call_dead`), the callee-saved registers (`Preserves.reg`,
  `preserves_of`), branches (`ite_bne_of_eq`, `ite_bne_of_ne`).
* Tactics: `rv_eval` (a block's expressions as `BitVec` arithmetic), `rv_norm`, `addr_omega` (an
  address goal from listed facts), `valid_access` (a side condition `validAccess 8 x`).
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64 LeanVM.Parameters CompPoly.Extension

/-! ## Byte ranges -/

/-- `x` is one of the `n` bytes from `a`. -/
def Within (x a : Word) (n : Nat) : Prop := a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n

/-- The `n` bytes from `a` and the `m` bytes from `b` do not overlap. -/
def Apart (a : Word) (n : Nat) (b : Word) (m : Nat) : Prop :=
  n = 0 ∨ m = 0 ∨ a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat

theorem validAccess_of_dword {a : Word} (h : isValidDwordAccess a = true) :
    Sym.validAccess 8 a = true :=
  h

/-- A nonempty valid range lies in the machine's memory, aligned. -/
theorem ValidMemRange.bounds {a : Word} {n : Nat} (h : ValidMemRange a n) (hn : 0 < n) :
    0x20 ≤ a.toNat ∧ a.toNat % 8 = 0 ∧ a.toNat + 8 * n ≤ 0xc0000008 := by
  have h0 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h 0 hn))
  simp only [Nat.mul_zero, BitVec.add_zero] at h0
  refine ⟨by omega, h0.2, Classical.byContradiction fun hc ↦ ?_⟩
  have hi := (Sym.validAccess_eight _).mp
    (validAccess_of_dword (h ((0xc0000008 - a.toNat) / 8) (by omega)))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at hi
  omega

/-- Every aligned doubleword of a valid range is a valid access. -/
theorem ValidMemRange.access {a : Word} {n : Nat} (h : ValidMemRange a n) {x : Word}
    (h1 : a.toNat ≤ x.toNat) (h2 : x.toNat < a.toNat + 8 * n) (h3 : x.toNat % 8 = a.toNat % 8) :
    Sym.validAccess 8 x = true := by
  have hx : x = a + BitVec.ofNat 64 (8 * ((x.toNat - a.toNat) / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := x.isLt
    omega
  rw [hx]
  exact h _ (by omega)

/-- A valid range's aligned subrange is valid. -/
theorem ValidMemRange.sub {a b : Word} {n m : Nat} (h : ValidMemRange a n)
    (h1 : a.toNat ≤ b.toNat) (h2 : b.toNat + 8 * m ≤ a.toNat + 8 * n)
    (h3 : b.toNat % 8 = a.toNat % 8) :
    ValidMemRange b m := by
  intro i hi
  have hb := ValidMemRange.bounds h (by omega)
  refine ValidMemRange.access h ?_ ?_ ?_ <;> rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

/-- `x + n` without overflow, for `omega`: give it these rather than the sums' wrapping. -/
theorem toNat_add_ofNat {x : Word} {n : Nat} (h : x.toNat + n < 2 ^ 64) :
    (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Words apart by `<` on `toNat`: `omega` proves a `<` between sums quickly, a `≠` slowly. -/
theorem ne_of_toNat_lt {x y : Word} (h : x.toNat < y.toNat) : x ≠ y :=
  fun hxy ↦ by rw [hxy] at h; exact Nat.lt_irrefl _ h

/-! ## The stack -/

/-- The lowest of the `n` bytes below `sp`. -/
def stackLo (s : MachineState) (n : Nat) : Word := s.getReg .x2 - BitVec.ofNat 64 n

/-- The `n` bytes below `sp` are valid memory, and `sp` is 16-aligned. -/
structure StackOk (s : MachineState) (n : Nat) : Prop where
  valid : ValidMemRange (stackLo s n) (n / 8)
  aligned : (s.getReg .x2).toNat % 16 = 0

/-- `sp` as a number, for `omega`. -/
theorem StackOk.bounds {s : MachineState} {n : Nat} (h : StackOk s n) (hn : 8 ≤ n)
    (h8 : n % 8 = 0) :
    0x20 + n ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s n).toNat = (s.getReg .x2).toNat - n := by
  have hb := ValidMemRange.bounds h.valid (by omega)
  have ha := h.aligned
  simp only [stackLo, BitVec.toNat_sub, BitVec.toNat_ofNat] at hb ⊢
  have := (s.getReg .x2).isLt
  omega

/-! ## Memory frames -/

/-- `t`'s memory is `s`'s outside the `n` bytes from `lo`. -/
def MemFrame (s t : MachineState) (lo : Word) (n : Nat) : Prop :=
  ∀ a, ¬ Within a lo n → t.getMem a = s.getMem a

theorem MemFrame.refl (s : MachineState) (lo : Word) (n : Nat) : MemFrame s s lo n :=
  fun _ _ ↦ rfl

/-- A frame within a larger range is a frame of it. -/
theorem MemFrame.mono {s t : MachineState} {lo lo' : Word} {n n' : Nat} (h : MemFrame s t lo n)
    (hsub : ∀ a, Within a lo n → Within a lo' n') : MemFrame s t lo' n' :=
  fun a ha ↦ h a fun h' ↦ ha (hsub a h')

/-- Two frames in sequence, the second within the first's range. -/
theorem MemFrame.trans {s t u : MachineState} {lo lo' : Word} {n n' : Nat}
    (h₁ : MemFrame s t lo n) (h₂ : MemFrame t u lo' n')
    (hsub : ∀ a, Within a lo' n' → Within a lo n) : MemFrame s u lo n :=
  fun a ha ↦ (h₂ a fun h' ↦ ha (hsub a h')).trans (h₁ a ha)

/-- A frame of two ranges, both within a third, is a frame of the third. -/
theorem MemFrame.of_two {s t : MachineState} {lo₁ lo₂ lo : Word} {n₁ n₂ n : Nat}
    (h : ∀ a, ¬ Within a lo₁ n₁ → ¬ Within a lo₂ n₂ → t.getMem a = s.getMem a)
    (h₁ : ∀ a, Within a lo₁ n₁ → Within a lo n)
    (h₂ : ∀ a, Within a lo₂ n₂ → Within a lo n) :
    MemFrame s t lo n :=
  fun a ha ↦ h a (fun h' ↦ ha (h₁ a h')) (fun h' ↦ ha (h₂ a h'))

/-- An `E` outside the frame's range is unchanged. -/
theorem MemFrame.eAt {s t : MachineState} {lo : Word} {n : Nat} (h : MemFrame s t lo n) {p : Word}
    (hp : Apart p 24 lo n) (hw : p.toNat + 24 ≤ 2 ^ 64) : eAt t p = eAt s p := by
  have h8 : (p + 8).toNat = p.toNat + 8 := by bv_omega
  have h16 : (p + 16).toNat = p.toNat + 16 := by bv_omega
  simp only [Apart] at hp
  unfold Rv64Verifier.eAt
  rw [h p (by simp only [Within]; omega), h (p + 8) (by simp only [Within]; omega),
    h (p + 16) (by simp only [Within]; omega)]

/-! ## Reading a block's expectation -/

namespace Sym

theorem Expect.Holds.reg_eq {x : Expect} {s t : MachineState} (h : x.Holds s t) (r : Reg) {v : Word}
    (hr : (x.regs.find? fun p ↦ Reg.beqN p.1 r).isSome = true) (hv : (x.reg r).eval s = v) :
    t.getReg r = v :=
  (h.reg r hr).trans hv

theorem Expect.Holds.mem_eq {x : Expect} {s t : MachineState} (h : x.Holds s t) (i : Nat)
    (hi : i < x.mem.length) {a v : Word} (ha : (x.mem[i]).1.eval s = a)
    (hv : (x.mem[i]).2.eval s = v) : t.getMem a = v :=
  ha ▸ hv ▸ h.memAt i hi

theorem Expect.Holds.pc_eq {x : Expect} {s t : MachineState} (h : x.Holds s t) {v : Word}
    (hv : x.pc.eval s = v) : t.pc = v :=
  h.pc.trans hv

/-- `x` lists every register of `rs` and leaves it unchanged; decide it with `rfl`. -/
def Expect.keeps (x : Expect) (rs : List Reg) : Bool :=
  rs.all fun r ↦ (x.regs.find? fun p ↦ Reg.beqN p.1 r).isSome && E.beq (x.reg r) (.reg r)

theorem Expect.Holds.keeps {x : Expect} {s t : MachineState} (h : x.Holds s t) {rs : List Reg}
    (hk : x.keeps rs = true) : ∀ r ∈ rs, t.getReg r = s.getReg r := by
  intro r hr
  have hk' := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp hk r hr)
  rw [h.reg r hk'.1, E.beq_eq hk'.2]
  rfl

/-- A block whose writes all lie in a range leaves memory outside it unchanged. -/
theorem Expect.Holds.memFrame {x : Expect} {s t : MachineState} (h : x.Holds s t) {lo : Word}
    {n : Nat} (hw : ∀ k ∈ x.writes, Within (k.eval s) lo n) : MemFrame s t lo n :=
  fun a ha ↦ h.frame a fun k hk heq ↦ ha (heq ▸ hw k hk)

/-- `Expect.reg x r` of a concrete block: the expression it lists, by unfolding. -/
dsimproc_decl reduceReg (Expect.reg _ _) := fun e ↦ do
  return .done (← Lean.Meta.withTransparency .default <| Lean.Meta.whnf e)

theorem shiftLeft_eq_mul (x : Word) (n : Nat) : x <<< n = x * BitVec.ofNat 64 (2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mul_mod_mod]

/-- `x + a - b` with constants `b ≤ a`, folded. -/
theorem add_ofNat_sub_ofNat (x : Word) (a b : Nat) (h : b ≤ a) :
    x + BitVec.ofNat 64 a - BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `rv_eval [h, ...]`: a block's register, memory, pc, write or side-condition expressions as
`BitVec` arithmetic of the initial state (shifts by constants as products, a list's `∀` as a
conjunction), with the given rewrites. -/
macro "rv_eval" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? :
    tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [reduceReg, rv_simp, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
    Nat.reduceLeDiff, Nat.reduceSub, BitVec.reduceAdd, BitVec.reduceSub,
    shiftLeft_eq_mul, add_ofNat_sub_ofNat, List.getElem_cons_succ, List.getElem_cons_zero,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, $ts',*] $[$loc]?)

/-- `rv_norm h₁ …`: the hypotheses' literals in `rv_eval`'s form (`BitVec.ofNat`), so that
`rv_eval [h₁, …]` can rewrite with them. -/
macro "rv_norm " hs:(ppSpace colGt ident)+ : tactic =>
  `(tactic| try simp only [BitVec.ofNat_eq_ofNat] at $hs*)

end Sym

/-- `addr_omega [f₁, …]`: an address goal from the listed facts alone, the rest of the context
cleared: ranges as `toNat` intervals, then `bv_omega`. Every sum of words costs `omega` a
division, so give it the bounds that rule out wrapping, and state `≠` as `<` (`ne_of_toNat_lt`)
and a difference of addresses through each address's `toNat`: those are fast, a `≠` or a `Nat`
subtraction of wrapping sums is not. -/
macro "addr_omega" " [" ts:term,* "]" : tactic => do
  let ts := ts.getElems
  let hs := (Array.range ts.size).map fun i ↦ Lean.mkIdent (.mkSimple s!"addr_fact{i}")
  let mut tac ← `(tactic| ((clear * - $hs*) <;>
    (try simp only [Within, Apart, stackLo] at *) <;> bv_omega))
  for (h, t) in (hs.zip ts).reverse do
    tac ← `(tactic| (have $h:ident := $t; $tac))
  return tac

/-- `valid_access h [f₁, …]`: a doubleword access inside the valid range `h`, its bounds by
`addr_omega [f₁, …]`. -/
macro "valid_access " h:term:max " [" ts:term,* "]" : tactic =>
  `(tactic| (refine ValidMemRange.access $h ?_ ?_ ?_ <;> addr_omega [$ts,*]))

/-! ## `E` from its limbs -/

theorem coeffNat_add (x y : E) (i : Nat) :
    Ext.coeffNat (x + y) i = Ext.coeffNat x i + Ext.coeffNat y i := by
  unfold Ext.coeffNat
  split
  · exact Ext.coeff_add x y _
  · simp

theorem limbs_add (x y : E) : Model.limbs (x + y) =
    ((Model.limbs x).1 ^^^ (Model.limbs y).1, (Model.limbs x).2.1 ^^^ (Model.limbs y).2.1,
      (Model.limbs x).2.2 ^^^ (Model.limbs y).2.2) := by
  simp only [Model.limbs, coeffNat_add, Model.toBitVec_add]

theorem limbs_one : Model.limbs (1 : E) = (1, 0, 0) := by
  decide +kernel

theorem eAt_eq_of_limbs {t : MachineState} {a : Word} {x : E}
    (h : (t.getMem a, t.getMem (a + 8), t.getMem (a + 16)) = Model.limbs x) : eAt t a = x :=
  eq_of_limbs (by rw [limbs_eAt, h])

/-- Two `E`s whose limbs agree are equal. -/
theorem eAt_congr {s t : MachineState} {a b : Word} (h0 : t.getMem a = s.getMem b)
    (h1 : t.getMem (a + 8) = s.getMem (b + 8)) (h2 : t.getMem (a + 16) = s.getMem (b + 16)) :
    eAt t a = eAt s b := by
  simp only [eAt, h0, h1, h2]

/-! ## Calls and the frame -/

/-- A call to a function that never returns reaches a dead end. -/
theorem FunSpec.call_dead {code : Code} {entry : Word} {pre : MachineState → Prop}
    (h : FunSpec code entry pre fun _ _ ↦ False) {c c' : MachineState} (hjump : Reaches code c c')
    (hpc : c'.pc = entry) (hpre : pre c') : ∃ t, Reaches code c t ∧ Dead code t := by
  obtain ⟨t, ht, ⟨-, -, hf⟩ | hd⟩ := h.call hjump hpc hpre
  · exact hf.elim
  · exact ⟨t, ht, hd⟩

theorem Preserves.reg {s t : MachineState} (h : Preserves s t) (r : Reg)
    (hr : r ∈ calleeSaved := by decide) : t.getReg r = s.getReg r :=
  h r hr

/-- `Preserves` from each callee-saved register. -/
theorem preserves_of {s t : MachineState} (h2 : t.getReg .x2 = s.getReg .x2)
    (h8 : t.getReg .x8 = s.getReg .x8) (h9 : t.getReg .x9 = s.getReg .x9)
    (h18 : t.getReg .x18 = s.getReg .x18) (h19 : t.getReg .x19 = s.getReg .x19)
    (hrest : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
      t.getReg r = s.getReg r) :
    Preserves s t := by
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr | hr | hr | hr | hr | hr | hr | hr <;>
    first | assumption | exact hrest _ (by simp [hr])

/-- A branch on `a != b` whose operands are equal falls through. -/
theorem ite_bne_of_eq {a b x y : Word} (h : a = b) : (if (a != b) = true then x else y) = y := by
  simp [h]

/-- A branch on `a != b` whose operands differ is taken. -/
theorem ite_bne_of_ne {a b x y : Word} (h : a ≠ b) : (if (a != b) = true then x else y) = x := by
  simp [h]

theorem returnAddress_eq (s : MachineState) :
    returnAddress s = s.getReg .x1 &&& 0xfffffffffffffffe#64 := rfl

end Rv64Verifier
