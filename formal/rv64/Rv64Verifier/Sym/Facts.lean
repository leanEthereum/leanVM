import Rv64Verifier.Sym.Read
import Rv64Verifier.Sym.AddrAttr

/-!
# Facts about blocks, in one normal form

What the generated blocks' lemmas (`scripts/Gen.lean`) and the function proofs share:

* Byte ranges as intervals of `toNat` (`Within`, `Apart`) and memory frames (`MemFrame`: `t`'s
  memory is `s`'s outside a range), composed along a run.
* Reading a block's `Expect`: a register (`Expect.Holds.reg_eq`), a written doubleword
  (`Expect.Holds.mem_eq`), the pc (`Expect.Holds.pc_eq`), registers it keeps (`Expect.keeps`),
  its frame (`Expect.Holds.memFrame`).
* The normal form of words: numerals are `OfNat` literals (`104`, as one writes them, never
  `104#64`), and a register or load plus a constant is `b + k` or `b - k` with `0 < k < 2^63`.
  `rv_eval [..]` puts a block's expressions, and anything else, in it: `Expect.reg` unfolded
  (`reduceReg`), `E.eval` and the executor's operations unfolded, constants folded
  (`wordAddLit` ..), offsets merged (`wordAssocAdd`, `wordAssocSub`), shifts by constants as
  products. Hypotheses written by hand in this form rewrite the generated lemmas' terms directly.
* `addr_omega [h₁, ..]`: a goal about addresses (`Within`, `Apart`, `=`, `≠`, `<` of words or of
  their `toNat`) from the listed facts alone: each `toNat` of a sum, difference, product by a
  constant or `BitVec.ofNat` that the facts show does not wrap becomes linear (`x.toNat + k`),
  and `omega` decides the rest, with no `% 2^64` left to split on. A failure lists the linear
  facts it had: the missing one is usually a bound that rules out wrapping.
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64

/-! ## Byte ranges and memory frames -/

/-- `x` is one of the `n` bytes from `a`. -/
@[rv_addr] def Within (x a : Word) (n : Nat) : Prop := a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n

/-- The `n` bytes from `a` and the `m` bytes from `b` do not overlap. -/
@[rv_addr] def Apart (a : Word) (n : Nat) (b : Word) (m : Nat) : Prop :=
  n = 0 ∨ m = 0 ∨ a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat

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
    (h₂ : ∀ a, Within a lo₂ n₂ → Within a lo n) : MemFrame s t lo n :=
  fun a ha ↦ h a (fun h' ↦ ha (h₁ a h')) (fun h' ↦ ha (h₂ a h'))

/-- A step that writes no memory is a frame of every range. -/
theorem MemFrame.of_same {s t : MachineState} (h : ∀ a, t.getMem a = s.getMem a) (lo : Word)
    (n : Nat) : MemFrame s t lo n :=
  fun a _ ↦ h a

/-! ## Reading a block's expectation -/

namespace Sym

theorem Expect.Holds.reg_eq {x : Expect} {s t : MachineState} (h : x.Holds s t) (r : Reg)
    {v : Word} (hr : (x.regs.find? fun p ↦ Reg.beqN p.1 r).isSome = true)
    (hv : (x.reg r).eval s = v) : t.getReg r = v :=
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

/-- A block that writes nothing leaves memory unchanged. -/
theorem Expect.Holds.mem_same {x : Expect} {s t : MachineState} (h : x.Holds s t)
    (hw : x.writes = []) (a : Word) : t.getMem a = s.getMem a :=
  h.frame a fun k hk ↦ by rw [hw] at hk; cases hk

theorem bnot_of_false {b : Bool} (h : b = false) : (!b) = true := by simp [h]

theorem false_of_bnot {b : Bool} (h : (!b) = true) : b = false := by simpa using h

/-! ## The normal form of words -/

open Lean Meta Simp

/-- `Expect.reg x r` of a concrete block: the expression it lists, by unfolding. -/
dsimproc_decl reduceReg (Expect.reg _ _) := fun e ↦ do
  return .done (← withTransparency .default <| whnf e)

/-- A concrete block's `pc`, `mem`, `writes` or `obl`: the term it lists, by unfolding the block
and nothing else (its other fields can be large). -/
def reduceField (e : Expr) : SimpM DStep := do
  return .done (← withTransparency .default <| whnf e)

dsimproc_decl reducePc (Expect.pc _) := reduceField
dsimproc_decl reduceMem (Expect.mem _) := reduceField
dsimproc_decl reduceWrites (Expect.writes _) := reduceField
dsimproc_decl reduceObl (Expect.obl _) := reduceField

/-- The value of a numeral of `Word`, as `OfNat` or `BitVec.ofNat` writes it. -/
def wordLit? (e : Expr) : MetaM (Option Nat) := do
  let some ⟨n, v⟩ ← getBitVecValue? e | return none
  return if n == 64 then some v.toNat else none

/-- `BitVec.ofNat 64 n` of a numeral `n`: the `OfNat` literal. -/
dsimproc_decl wordOfNat (BitVec.ofNat _ _) := fun e ↦ do
  let some v ← wordLit? e | return .continue
  return .done (← mkNumeral (← inferType e) v)

/-- A binary operation of two numerals, folded. -/
def foldBin (f : Nat → Nat → Nat) (e : Expr) : SimpM DStep := do
  let args := e.getAppArgs
  if args.size < 2 then return .continue
  let a := args[args.size - 2]!
  let b := args[args.size - 1]!
  let some x ← wordLit? a | return .continue
  let some y ← wordLit? b | return .continue
  return .done (← mkNumeral (← inferType e) (f x y % 2 ^ 64))

dsimproc_decl wordAddLit ((_ : BitVec 64) + _) := foldBin (· + ·)
dsimproc_decl wordSubLit ((_ : BitVec 64) - _) := foldBin fun x y ↦ x + (2 ^ 64 - y)
dsimproc_decl wordMulLit ((_ : BitVec 64) * _) := foldBin (· * ·)
dsimproc_decl wordXorLit ((_ : BitVec 64) ^^^ _) := foldBin (· ^^^ ·)
dsimproc_decl wordAndLit ((_ : BitVec 64) &&& _) := foldBin (· &&& ·)
dsimproc_decl wordOrLit ((_ : BitVec 64) ||| _) := foldBin (· ||| ·)

/-- `toNat` of a numeral. -/
dsimproc_decl wordToNatLit (BitVec.toNat (_ : BitVec 64)) := fun e ↦ do
  let some x ← wordLit? e.appArg! | return .continue
  return .done (mkNatLit x)

theorem add_add_lit (b d c : Word) : b + d + c = b + (d + c) := BitVec.add_assoc b d c

theorem sub_add_lit (b d c : Word) : b - d + c = b + (c - d) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-d)]

theorem add_sub_lit (b d c : Word) : b + d - c = b + (d - c) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem sub_sub_lit (b d c : Word) : b - d - c = b - (d + c) := by
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]

theorem add_neg_lit (b k : Word) : b + k = b - (0 - k) := by
  bv_omega

theorem sub_neg_lit (b k : Word) : b - k = b + (0 - k) := by
  bv_omega

theorem add_zero_lit (b : Word) : b + 0 = b := BitVec.add_zero b
theorem zero_xor_lit (b : Word) : 0 ^^^ b = b := BitVec.zero_xor
theorem xor_zero_lit (b : Word) : b ^^^ 0 = b := BitVec.xor_zero
theorem sub_zero_lit (b : Word) : b - 0 = b := BitVec.sub_zero b

/-- The step of `wordAssocAdd`/`wordAssocSub` for `a ⊕ c`, `c` a numeral: merge with an offset
of `a`, or bring a "negative" offset to the other sign, or drop a zero. -/
def assocStep (isAdd : Bool) (a c : Expr) : SimpM Step := do
  let some v ← wordLit? c | return .continue
  if (← wordLit? a).isSome then return .continue
  let lit? (d : Expr) : SimpM Bool := return (← wordLit? d).isSome
  let pf? : Option Expr ← do
    match_expr a with
    | HAdd.hAdd _ _ _ _ b d =>
      if ← lit? d then
        pure (some (mkApp3 (mkConst (if isAdd then ``add_add_lit else ``add_sub_lit)) b d c))
      else pure none
    | HSub.hSub _ _ _ _ b d =>
      if ← lit? d then
        pure (some (mkApp3 (mkConst (if isAdd then ``sub_add_lit else ``sub_sub_lit)) b d c))
      else pure none
    | _ => pure none
  let pf? := pf?.orElse fun _ ↦
    if v == 0 then some (mkApp (mkConst (if isAdd then ``add_zero_lit else ``sub_zero_lit)) a)
    else if 2 ^ 63 ≤ v then
      some (mkApp2 (mkConst (if isAdd then ``add_neg_lit else ``sub_neg_lit)) a c)
    else none
  let some pf := pf? | return .continue
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

simproc_decl wordAssocAdd ((_ : BitVec 64) + _) := fun e ↦ do
  let_expr HAdd.hAdd _ _ _ _ a c := e | return .continue
  assocStep true a c

simproc_decl wordAssocSub ((_ : BitVec 64) - _) := fun e ↦ do
  let_expr HSub.hSub _ _ _ _ a c := e | return .continue
  assocStep false a c

theorem shiftLeft_eq_mul (x : Word) (n : Nat) : x <<< n = x * BitVec.ofNat 64 (2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mul_mod_mod]

/-- `rv_eval [h, ..] (at h')?`: a concrete block's register, memory, pc, write or side-condition
expressions as `BitVec` arithmetic of the initial state, in the normal form, with the given
rewrites. -/
macro "rv_eval" " [" ts:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [reduceReg, reducePc, reduceMem, reduceWrites, reduceObl, E.eval,
    BinOp.eval, UnOp.eval, CmpOp.eval, LoadKind.fromWord,
    StoreKind.merge, Addr.eval, Oblig.all, Oblig.holds, wordOfNat, wordAddLit, wordSubLit,
    wordMulLit, wordXorLit, wordAndLit, wordOrLit, wordToNatLit, wordAssocAdd, wordAssocSub,
    zero_xor_lit, xor_zero_lit,
    Nat.reduceMod, Nat.reducePow, shiftLeft_eq_mul, List.getElem_cons_succ,
    List.getElem_cons_zero, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, $ts',*] $[$loc]?)

end Sym

/-! ## `addr_omega` -/

theorem ne_of_toNat_lt {x y : Word} (h : x.toNat < y.toNat) : x ≠ y :=
  fun hxy ↦ by rw [hxy] at h; exact Nat.lt_irrefl _ h

theorem toNat_add_ofNat {x : Word} {n : Nat} (h : x.toNat + n < 2 ^ 64) :
    (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

namespace AddrOmega

theorem add_lt (x y : Word) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem sub_le (x y : Word) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]; omega

theorem mul_lit (x y : Word) (v : Nat) (hv : y.toNat = v) (h : x.toNat * v < 2 ^ 64) :
    (x * y).toNat = x.toNat * v := by
  rw [BitVec.toNat_mul, hv]; exact Nat.mod_eq_of_lt h

theorem ofNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem lt (x : Word) : x.toNat < 2 ^ 64 := x.isLt

open Lean Meta Elab Tactic

/-- `p` by `omega` from `facts`, if it can. -/
def prove? (facts : List Expr) (p : Expr) : MetaM (Option Expr) := do
  let m ← mkFreshExprSyntheticOpaqueMVar p
  try
    let some g ← m.mvarId!.falseOrByContra | return some (← instantiateMVars m)
    g.withContext do
      let some neg := (← getLCtx).lastDecl | throwError "addr_omega: no hypothesis"
      Omega.omega (facts ++ [neg.toExpr]) g
    return some (← instantiateMVars m)
  catch _ => return none

structure State where
  /-- words whose `toNat` is linear in the facts, or a numeral -/
  done : Std.HashSet Expr := {}
  /-- words seen, linear or not -/
  seen : Std.HashSet Expr := {}
  facts : Array Expr := #[]

/-- Add the linear fact about `e.toNat`, its value from its parts when the facts show it does not
wrap; parts first. Returns whether it did. -/
partial def linearize (e : Expr) : StateT State MetaM Bool := do
  if (← get).done.contains e then return true
  modify fun st ↦ { st with seen := st.seen.insert e }
  let fact (pf : Expr) : StateT State MetaM Unit :=
    modify fun st ↦ { st with facts := st.facts.push pf, done := st.done.insert e }
  let tryLemma (pf : Expr) : StateT State MetaM Bool := do
    let ty ← inferType pf
    let .forallE _ side _ _ := ty | return false
    match ← prove? (← get).facts.toList side with
    | some h => fact (mkApp pf h); return true
    | none => return false
  if let some v ← Sym.wordLit? e then
    let ty ← mkEq (← mkAppM ``BitVec.toNat #[e]) (mkNatLit v)
    fact (← mkExpectedTypeHint (← mkEqRefl (mkNatLit v)) ty)
    return true
  match_expr e with
  | HAdd.hAdd _ _ _ _ x y => do
    discard <| linearize x; discard <| linearize y
    tryLemma (mkApp2 (mkConst ``add_lt) x y)
  | HSub.hSub _ _ _ _ x y => do
    discard <| linearize x; discard <| linearize y
    tryLemma (mkApp2 (mkConst ``sub_le) x y)
  | HMul.hMul _ _ _ _ x y => do
    discard <| linearize x
    match ← Sym.wordLit? y with
    | some v =>
      let hv ← mkExpectedTypeHint (← mkEqRefl (mkNatLit v))
        (← mkEq (← mkAppM ``BitVec.toNat #[y]) (mkNatLit v))
      tryLemma (mkApp4 (mkConst ``mul_lit) x y (mkNatLit v) hv)
    | none => return false
  | BitVec.ofNat _ n => tryLemma (mkApp (mkConst ``ofNat_lt) n)
  | _ => return false

/-- The 64-bit words whose `toNat` occurs in `e`. -/
partial def toNatArgs (e : Expr) : Array Expr :=
  let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
    if e.isAppOfArity ``BitVec.toNat 2 && e.appFn!.appArg!.nat? == some 64 then
      acc.push e.appArg!
    else match e with
      | .app f a => go a (go f acc)
      | .forallE _ d b _ => go b (go d acc)
      | .lam _ d b _ => go b (go d acc)
      | .mdata _ b => go b acc
      | _ => acc
  go e #[]

/-- Linearize every word until nothing more is linear (a fact about one word can be what shows
another does not wrap), bound the rest by `2^64`, and run `omega`. -/
def run (g : MVarId) (hyps : Array Expr) : MetaM Unit := g.withContext do
  let mut words : Array Expr := #[]
  for h in hyps do
    words := words ++ toNatArgs (← instantiateMVars (← inferType h))
  let mut st : State := { facts := hyps }
  repeat
    let n := st.facts.size
    let ((), st') ← (words.forM fun w ↦ discard (linearize w)).run st
    st := st'
    if st.facts.size == n then break
  let mut facts := st.facts
  for w in st.seen do
    unless st.done.contains w do facts := facts.push (mkApp (mkConst ``lt) w)
  try Omega.omega facts.toList g
  catch ex =>
    throwError "addr_omega failed from:{indentD (MessageData.joinSep
      ((← facts.mapM inferType).toList.map toMessageData) Format.line)}\n{ex.toMessageData}"

end AddrOmega

open Lean Elab Tactic in
/-- `addr_omega [h₁, ..]`: an address goal from the listed facts alone (see the module doc). -/
elab "addr_omega" " [" ts:term,* "]" : tactic => do
  let names := (List.range ts.getElems.size).map fun i ↦ Name.mkSimple s!"addr_fact{i}"
  for (n, t) in names.zip ts.getElems.toList do
    evalTactic (← `(tactic| have $(mkIdent n):ident := $t))
  evalTactic (← `(tactic| refine Classical.byContradiction fun $(mkIdent `addr_neg) ↦ ?_))
  let locs := (names ++ [`addr_neg]).toArray.map mkIdent
  evalTactic (← `(tactic| try simp only [rv_addr, BitVec.toNat_eq, ne_eq, Classical.not_not,
    not_true_eq_false] at $locs*))
  if (← getGoals).isEmpty then return
  liftMetaFinishingTactic fun g ↦ g.withContext do
    let mut hyps := #[]
    for n in names ++ [`addr_neg] do
      if let some d := (← getLCtx).findFromUserName? n then hyps := hyps.push d.toExpr
    AddrOmega.run g hyps

end Rv64Verifier
