/-
  Rv64mc.Tactic.Sym

  `rv_sym`: symbolic execution of a RISC-V Lprog function body (`rvIsa`) that states each next state itself, for
  any template `hp : p[fn]? = some fd` whose body is a literal.

  Unlike `lsym` (machine-checked's `Lprog/Tactic.lean`), no `simp` runs over the goal or its hypotheses. The body
  is read once; each instruction is one rule of `Rv64mc.Tactic.Steps` applied by name, with the next state given,
  and every equation in its proof is an instance of a lemma or a closed fact the kernel decides by evaluation, never
  a reduction the kernel has to find (one through a value can unfold it without end):

  * a register file is an `rf` of its 32 values (`Rv64mc.Tactic.RegFile`), read and written by `rf_get_<r>` and
    `rf_set_<r>`. What a fact says of a register file the executor did not make (the entry's, or the one a callee
    returns: `regs .x2 = top`, `r' .x10 = …`) is written into its `rf` (`absorbFacts`);
  * a value is computed from its expression (`eval_*`, `bin_*`), addresses kept as a base plus a literal offset
    (`t + c`, by `add_assoc` and `add_zero`) and operations on literals folded by `decide`;
  * a load is read through the memory: a store at the same address gives its value, one at another offset of the
    same base is passed (`Addr.add_ne_add`, the offsets compared by the kernel), and a callee's memory is passed
    at an address its frame keeps (a hypothesis `∀ a, lo ≤ a → m'.getMem a = m.getMem a`), where the base's bounds
    in the context and the offsets decide `lo ≤ a` (`Addr.add_le_add`);
  * a call or tail call through a contract (`using`) resolves its target by the link facts given (`with`), closes
    the callee's precondition where it can (`closeSide`), and goes on after the return with the callee's
    postcondition split into hypotheses `hret<k>_<j>`;
  * a branch on a comparison gives two goals, each with the comparison's outcome as a proposition `hc`;
  * under `Holds` (`Core/Holds.lean`), a goal or contract is unfolded to the contract it is, and `closeSide` closes
    the frame (`Env.Frame`, built store by store and call by call: `Tactic/Frame.lean`), `env.Static`, `NEXT`'s
    bound and a callee's stack room from the function's own stack bound; a callee's frame without `out` becomes a
    frame hypothesis (`keep<k>_1`) that loads read through. A `need` that is a parameter is bounded by the
    hypotheses `k + need' ≤ need` (`stackLit`, `room_hyp`);
  * a load at `d.hi + d.lo + 8 k` reads word `k` of a constant table where a hypothesis `DataRef.Words env d ws`
    gives it (`dataRead`, `Core/ReprLemmas.lean`).

  It stops at a program counter in `stop`, at the target of a backward jump (a loop's head, for a loop lemma), at a
  call without a contract, and where the function returns, which `finish` closes by the contract's continuation,
  leaving the postcondition to `closeSide`.

  ## Main results

  * `rv_sym hp stop [pcs] with [facts] using [contracts]`: step a goal `SafeN … ⟨⟨fn, pc, …⟩ :: …⟩`
  * `rv_auto hp …`: a contract `rvIsa.Contract p c fn Pre Post`, from the entry
  * `rv_intro h`, `rv_close`: a loop invariant's facts into the register file; the side goals' closer
-/

import Lean
import Rv64mc.Tactic.Steps
import Rv64mc.Tactic.Addr
import Rv64mc.Tactic.Frame
import Rv64mc.Core.ReprLemmas

namespace Rv64mc.Tactic.Sym

open Lean Meta Elab Tactic
open RiscvZkvm.Rv64 Lprog Lprog.RiscV

initialize registerTraceClass `rv_sym

/-! ## Terms -/

/-- `c` applied to its arguments by binder name, with no unification: every binder up to the last given. -/
def appN (c : Name) (args : List (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo c
  let mut ty := info.type
  let mut xs : Array Expr := #[]
  while ty.isForall && xs.size < args.length do
    let .forallE n _ b _ := ty | unreachable!
    match args.lookup n with
    | some a => xs := xs.push a; ty := b.instantiate1 a
    | none => throwError "rv_sym: {c} needs its argument {n}"
  return mkAppN (mkConst c) xs

/-- A 64-bit literal's value. -/
def lit? (e : Expr) : MetaM (Option Nat) := do
  match ← getBitVecValue? e with
  | some ⟨64, v⟩ => return some v.toNat
  | _ => return none

def mkLit (v : Nat) : Expr := toExpr (BitVec.ofNat 64 v)

def word : Expr := mkApp (mkConst ``BitVec) (mkRawNatLit 64)

/-- The register a constructor names. -/
def regName? (e : Expr) : Option Name :=
  match e.consumeMData with
  | .const n _ => if n.getPrefix == ``RiscvZkvm.Rv64.Reg then some n else none
  | _ => none

/-- The index of the register a constructor names. -/
def regIdx? (e : Expr) : Option Nat :=
  match regName? e with
  | some (.str _ s) => (s.drop 1).toString.toNat?
  | _ => none

/-- The binders `a0`..`a31` of the `rf` lemmas, given. -/
def rfArgs (args : Array Expr) : List (Name × Expr) :=
  (List.range 32).map fun i => (Name.mkSimple s!"a{i}", args[i]!)

/-- `updReg R r v` as the register file the executor keeps: an `rf` with `r` written, and a proof of the equation
    (`rf_set_<r>`); any other `R` stays as it is. -/
def writeReg (R r v : Expr) : MetaM (Expr × Expr) := do
  let R := R.consumeMData
  let upd := mkApp5 (mkConst ``Lprog.updReg) (mkConst ``RiscvZkvm.Rv64.Reg)
    (mkConst ``RiscvZkvm.Rv64.instDecidableEqReg) R r v
  if R.isAppOfArity ``Rv64mc.Tactic.rf 32 then
    if let some k := regIdx? r then
      let args := R.getAppArgs
      return (mkAppN (mkConst ``Rv64mc.Tactic.rf) (args.set! k v),
        ← appN (Name.mkStr `Rv64mc.Tactic s!"rf_set_x{k}") ((`w, v) :: rfArgs args))
  return (upd, ← mkEqRefl upd)

/-- A signed 64-bit literal as an integer. -/
def toInt64 (v : Nat) : Int := if v < 2 ^ 63 then v else (v : Int) - 2 ^ 64

/-- `p` then `q`, where `q` may be absent (by reduction). -/
def transOpt (p : Expr) (q : Option Expr) : MetaM Expr :=
  match q with
  | some q => mkEqTrans p q
  | none => pure p

/-- The proof given, or reflexivity where the equation is by reduction. -/
def orRefl (p : Option Expr) (v : Expr) : MetaM Expr :=
  match p with
  | some p => pure p
  | none => mkEqRefl v

/-! ## Registers -/

/-- The value of register `r` in the register file `R`, and a proof of `R r = v` by `upd_same` and `upd_ne`. -/
partial def readP (R r : Expr) : MetaM (Expr × Expr) := do
  let R := R.consumeMData
  if R.isAppOfArity ``Rv64mc.Tactic.rf 32 then
    if let some k := regIdx? r then
      let args := R.getAppArgs
      return (args[k]!, ← appN (Name.mkStr `Rv64mc.Tactic s!"rf_get_x{k}") (rfArgs args))
  if R.isAppOfArity ``Lprog.updReg 5 then
    let args := R.getAppArgs
    let (R', r', v) := (args[2]!, args[3]!, args[4]!)
    if regName? r' == regName? r then
      return (v, ← appN ``Rv64mc.Tactic.upd_same [(`R, R'), (`r, r), (`v, v)])
    let (w, p) ← readP R' r
    let p1 ← appN ``Rv64mc.Tactic.upd_ne [(`R, R'), (`r, r'), (`r', r), (`v, v),
      (`h, ← mkEqRefl (mkConst ``Bool.false))]
    return (w, ← mkEqTrans p1 p)
  return (mkApp R r, ← mkEqRefl (mkApp R r))

/-- A read of a register through a chain of writes, as a simproc visiting terms before their arguments; `Isa.sp`
    and `Isa.link` named. A register file or a memory not applied to an address or a register is left as it is,
    its values unvisited: they are what the executor wrote, already in normal form. -/
def readStep (e : Expr) : SimpM Simp.Step := do
  if e.isAppOfArity ``Lprog.Isa.sp 1 || e.isAppOfArity ``Lprog.Isa.link 1 then
    let e' ← whnfR e
    if (regName? e').isSome then return .done { expr := e' }
  if e.isAppOf ``Rv64mc.Tactic.rf || e.isAppOf ``Lprog.updReg || e.isAppOf ``MachineState.setMem then
    if let .app f a := e then
      let f' := f.consumeMData
      if (f'.isAppOfArity ``Lprog.updReg 5 || f'.isAppOfArity ``Rv64mc.Tactic.rf 32) && (regName? a).isSome then
        let (v, p) ← readP f a
        return .done { expr := v, proof? := some p }
    return .done { expr := e }
  return .continue

/-- `e` with every read of a register through a chain of writes reduced, and a proof of `e = e'` where it changed. -/
def normReads (e : Expr) : MetaM (Expr × Option Expr) := do
  let e ← instantiateMVars e
  let ctx ← Simp.mkContext (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Simp.main e ctx (methods := { pre := readStep })
  return (r.expr, r.proof?)

/-! ## Values: a base and a literal offset -/

/-- A value as a base and a literal offset: a literal has no base, `t + c` is `(t, c)`, anything else is `(e, 0)`. -/
def affine (e : Expr) : MetaM (Option Expr × Nat) := do
  if let some v ← lit? e then return (none, v)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if let some c ← lit? e.appArg! then
      -- `t + 0` is not the base `t` by reduction: it stays an atom
      if c != 0 then return (some e.appFn!.appArg!, c)
  return (some e, 0)

def mkAdd (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a, b]

/-- A closed equation the kernel decides by evaluation (`decide`). Literal arithmetic is never left to the kernel's
    unifier, which can unfold a large literal one successor at a time. -/
def litEq (lhs rhs : Expr) : MetaM Expr := do mkDecideProof (← mkEq lhs rhs)

/-- `fun x => body x` over a variable of type `ty`. -/
def lam (ty : Expr) (body : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `x ty fun x => do mkLambdaFVars #[x] (← body x)

/-- The base plus the offset, and a proof that `a + b` is it where it is not by reduction. -/
partial def addV (a b : Expr) : MetaM (Expr × Option Expr) := do
  let (ba, ca) ← affine a
  let (bb, cb) ← affine b
  match ba, bb with
  | none, none =>
    let v := mkLit ((ca + cb) % 2 ^ 64)
    return (v, some (← litEq (← mkAdd a b) v))
  | some t, none =>
    if ca == 0 then
      if cb == 0 then return (t, some (← mkAppM ``BitVec.add_zero #[t]))
      return (← mkAdd t b, none)
    let c := (ca + cb) % 2 ^ 64
    let c1 := a.appArg!
    let pa ← mkAppM ``BitVec.add_assoc #[t, c1, b]
    let pc ← mkCongrArg (← lam word (mkAdd t ·)) (← litEq (← mkAdd c1 b) (mkLit c))
    let p ← mkEqTrans pa pc
    if c == 0 then return (t, some (← mkEqTrans p (← mkAppM ``BitVec.add_zero #[t])))
    return (← mkAdd t (mkLit c), some p)
  | none, some _ =>
    -- `c + b`, as `b + c`
    let pc ← mkAppM ``BitVec.add_comm #[a, b]
    let (v, pv) ← addV b a
    return (v, some (← transOpt pc pv))
  | some _, some _ => return (← mkAdd a b, none)

/-- The literal result of a binary operation on literals, if it is one of those folded. -/
def foldBin (op : Name) (x y : Nat) : Option Nat :=
  let m := 2 ^ 64
  match op with
  | ``BinOp.add => some ((x + y) % m)
  | ``BinOp.sub => some ((x + (m - y)) % m)
  | ``BinOp.mul => some ((x * y) % m)
  | ``BinOp.and => some (x &&& y)
  | ``BinOp.or => some (x ||| y)
  | ``BinOp.xor => some (x ^^^ y)
  | ``BinOp.shl => some ((x <<< y) % m)
  | ``BinOp.lshr => some (x >>> y)
  | _ => none

/-- `BinOp.eval op a b` as the operation it is, and a proof where that is not by reduction. -/
def binV (op : Expr) (a b : Expr) : MetaM (Expr × Option Expr) := do
  let some opn := op.consumeMData.constName? | return (mkApp3 (mkConst ``BinOp.eval) op a b, none)
  if let (some x, some y) := (← lit? a, ← lit? b) then
    if let some v := foldBin opn x y then
      let v := mkLit v
      return (v, some (← litEq (mkApp3 (mkConst ``BinOp.eval) op a b) v))
  let byName (n : Name) : MetaM Expr := appN n [(`x, a), (`y, b)]
  match opn with
  | ``BinOp.add =>
    let p0 ← byName ``Rv64mc.Tactic.bin_add
    let (v, pv) ← addV a b
    return (v, some (← transOpt p0 pv))
  | ``BinOp.sub =>
    let p0 ← byName ``Rv64mc.Tactic.bin_sub
    if let some y ← lit? b then
      let nb := mkLit ((2 ^ 64 - y) % 2 ^ 64)
      let ps ← mkAppM ``BitVec.sub_eq_add_neg #[a, b]
      let pn ← mkCongrArg (← lam word (mkAdd a ·)) (← litEq (← mkAppM ``Neg.neg #[b]) nb)
      let (v, pv) ← addV a nb
      return (v, some (← transOpt (← mkEqTrans p0 (← mkEqTrans ps pn)) pv))
    return (← mkAppM ``HSub.hSub #[a, b], some p0)
  | ``BinOp.mul => return (← mkAppM ``HMul.hMul #[a, b], some (← byName ``Rv64mc.Tactic.bin_mul))
  | ``BinOp.and => return (← mkAppM ``HAnd.hAnd #[a, b], some (← byName ``Rv64mc.Tactic.bin_and))
  | ``BinOp.or => return (← mkAppM ``HOr.hOr #[a, b], some (← byName ``Rv64mc.Tactic.bin_or))
  | ``BinOp.xor => return (← mkAppM ``HXor.hXor #[a, b], some (← byName ``Rv64mc.Tactic.bin_xor))
  | ``BinOp.shl | ``BinOp.lshr =>
    let (f, lem) := if opn == ``BinOp.shl then (``HShiftLeft.hShiftLeft, ``Rv64mc.Tactic.bin_shl)
      else (``HShiftRight.hShiftRight, ``Rv64mc.Tactic.bin_lshr)
    let p0 ← byName lem
    match ← lit? b with
    | some y =>
      let k := mkNatLit (y % 2 ^ 64)
      let bn ← mkAppM ``BitVec.toNat #[b]
      let p ← mkCongrArg (← lam (mkConst ``Nat) fun k => mkAppM f #[a, k]) (← litEq bn k)
      return (← mkAppM f #[a, k], some (← mkEqTrans p0 p))
    | none => return (← mkAppM f #[a, ← mkAppM ``BitVec.toNat #[b]], some p0)
  | _ => return (mkApp3 (mkConst ``BinOp.eval) op a b, none)

/-- The value of an expression over a register file, and a proof of `e.eval R = v`, every step by name. -/
partial def evalE (R e : Expr) : MetaM (Expr × Expr) := do
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Lprog.Expr.reg, #[_, r] =>
    let p0 ← appN ``Rv64mc.Tactic.eval_reg [(`R, R), (`r, r)]
    if (regName? r).isNone then return (mkApp R r, p0)
    let (v, p) ← readP R r
    return (v, ← mkEqTrans p0 p)
  | some ``Lprog.Expr.imm, #[_, v] => return (v, ← appN ``Rv64mc.Tactic.eval_imm [(`R, R), (`v, v)])
  | some ``Lprog.Expr.bin, #[_, op, a, b] =>
    let (va, pa) ← evalE R a
    let (vb, pb) ← evalE R b
    let p0 ← appN ``Rv64mc.Tactic.eval_bin [(`R, R), (`op, op), (`a, a), (`b, b)]
    let p1 ← mkCongr (← mkCongrArg (mkApp (mkConst ``BinOp.eval) op) pa) pb
    let (v, pv) ← binV op va vb
    return (v, ← transOpt (← mkEqTrans p0 p1) pv)
  | some ``Lprog.Expr.un, #[_, op, a] =>
    let (va, pa) ← evalE R a
    let p0 ← appN ``Rv64mc.Tactic.eval_un [(`R, R), (`op, op), (`a, a)]
    return (mkApp2 (mkConst ``UnOp.eval) op va, ← mkEqTrans p0 (← mkCongrArg (mkApp (mkConst ``UnOp.eval) op) pa))
  | _, _ =>
    let v ← mkAppM ``Lprog.Expr.eval #[R, e]
    return (v, ← mkEqRefl v)

/-! ## Facts in the context -/

/-- A natural number the term reduces to (a literal, or a sum of literals and constants defined as such). -/
def natVal? (e : Expr) : MetaM (Option Nat) := do
  if let some n ← evalNat e then return some n
  evalNat (← whnf e)

/-- A hypothesis `k + X ≤ need` or `k ≤ need`, `k` a numeral, for a `need` that is a parameter: the largest `k`, its
    proof, and `X` if any. -/
def needHyps (need : Expr) : MetaM (Array (Nat × Expr × Option Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    unless ty.isAppOfArity ``LE.le 4 && ty.appArg! == need do continue
    let a := ty.appFn!.appArg!
    if a.isAppOfArity ``HAdd.hAdd 6 then
      if let some k ← natVal? a.appFn!.appArg! then out := out.push (k, d.toExpr, some a.appArg!)
    else if let some k ← natVal? a then out := out.push (k, d.toExpr, none)
  return out

/-- `S + k ≤ t.toNat` with `k` a numeral, from the stack bound `h : S + need ≤ t.toNat`: `need`'s value if it has
    one, else the most a hypothesis on `need` gives. -/
def stackLit (h S t need : Expr) : MetaM (Option (Expr × Nat)) := do
  let goal (v : Nat) : MetaM Expr := do
    mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[S, mkNatLit v], ← mkAppM ``BitVec.toNat #[t]]
  if let some v ← natVal? need then return some (← mkExpectedTypeHint h (← goal v), v)
  let mut best : Option (Expr × Nat) := none
  for (k, hn, x?) in ← needHyps need do
    if best.any (k ≤ ·.2) then continue
    let p ← match x? with
      | some _ => mkAppM ``Rv64mc.Tactic.stack_lit #[h, hn]
      | none => mkAppM ``Rv64mc.Tactic.stack_lit0 #[h, hn]
    best := some (← mkExpectedTypeHint p (← goal k), k)
  return best

/-- The bounds `L ≤ t.toNat` and `t.toNat ≤ H` the context gives a base `t`, `L` and `H` numerals: from `L ≤ t` and
    `t ≤ H` on words, or from a stack bound `S + need ≤ t.toNat` (`Holds.pre`), the upper one `2^64 - 1` if no
    hypothesis gives one. -/
def bounds (t : Expr) : MetaM (Option (Expr × Nat × Expr × Nat)) := do
  let mut lo : Option (Expr × Nat) := none
  let mut hi : Option (Expr × Nat) := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty := ty.consumeMData
    if ty.isAppOfArity ``LE.le 4 then
      let a := ty.appFn!.appArg!
      let b := ty.appArg!
      if b == t then
        if let some v ← lit? a then
          if lo.all (·.2 < v) then
            lo := some (← mkExpectedTypeHint d.toExpr (← mkAppM ``LE.le #[mkNatLit v, ← mkAppM ``BitVec.toNat #[t]]), v)
      if a == t then
        if let some v ← lit? b then
          if hi.all (v < ·.2) then
            hi := some (← mkExpectedTypeHint d.toExpr (← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[t], mkNatLit v]), v)
      -- `S + need ≤ t.toNat`
      if b.isAppOfArity ``BitVec.toNat 2 && b.appArg! == t && a.isAppOfArity ``HAdd.hAdd 6 then
        if let some (hk, v) ← stackLit d.toExpr a.appFn!.appArg! t a.appArg! then
          if lo.all (·.2 < v) then
            let p ← mkAppM ``Rv64mc.Tactic.lo_of_room #[hk]
            lo := some (← mkExpectedTypeHint p (← mkAppM ``LE.le #[mkNatLit v, b]), v)
  let hi' ← match hi with
    | some x => pure x
    | none => pure (← mkAppM ``Rv64mc.Tactic.toNat_le_max #[t], 18446744073709551615)
  match lo with
  | some (hl, l) => return some (hl, l, hi'.1, hi'.2)
  | none => return none

/-- A hypothesis `t ≤ x`, or `t = x` read as one. -/
def leHyp (t x : Expr) : MetaM (Option Expr) := do
  if t == x then return some (← mkAppM ``BitVec.le_refl #[x])
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``LE.le 4 && ty.appFn!.appArg! == t && ty.appArg! == x then return some d.toExpr
  return none

/-- A proof of `a ≠ b` from the offsets of one base, or a hypothesis. -/
def neProof (a b : Expr) : MetaM (Option Expr) := do
  let (ba, ca) ← affine a
  let (bb, cb) ← affine b
  if ba.isSome && ba == bb && ca != cb then
    let t := ba.get!
    let tru := mkConst ``Bool.true
    if ca == 0 then
      return some (← appN ``Rv64mc.Tactic.ne_add [(`t, t), (`c, mkLit cb), (`h, ← mkEqRefl tru)])
    if cb == 0 then
      return some (← appN ``Rv64mc.Tactic.add_ne [(`t, t), (`c, mkLit ca), (`h, ← mkEqRefl tru)])
    return some (← appN ``Rv64mc.Tactic.add_ne_add
      [(`t, t), (`c1, mkLit ca), (`c2, mkLit cb), (`h, ← mkEqRefl tru)])
  -- one side below a base, the other at or above it by a hypothesis `t ≤ x`
  for (x, y, sym) in [(a, b, false), (b, a, true)] do
    let (by_, cy) ← affine y
    let some t := by_ | continue
    if cy == 0 then continue
    let some hx ← leHyp t x | continue
    let some (hl, l, _, _) ← bounds t | continue
    unless toInt64 cy < 0 && 0 ≤ (l : Int) + toInt64 cy do continue
    let p ← appN ``Rv64mc.Tactic.ne_add_of_le [(`t, t), (`a, x), (`c, mkLit cy),
      (`L, mkNatLit l), (`hL, hl), (`ha, hx), (`h, ← mkEqRefl (mkConst ``Bool.true))]
    return some (← if sym then mkAppM ``Ne.symm #[p] else pure p)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``Ne 3 then
      let x := ty.appFn!.appArg!
      let y := ty.appArg!
      if x == a && y == b then return some d.toExpr
      if x == b && y == a then return some (← mkAppM ``Ne.symm #[d.toExpr])
  return none

/-- A proof of `lo ≤ a` for offsets of one bounded base. -/
def leProof (lo a : Expr) : MetaM (Option Expr) := do
  -- numbers other than words': only the same
  unless (← whnfR (← inferType a)).isAppOf ``BitVec do
    if lo == a && (← whnfR (← inferType a)).isConstOf ``Nat then return some (← mkAppM ``Nat.le_refl #[a])
    return none
  if lo == a then return some (← mkAppM ``BitVec.le_refl #[a])
  let (bl, cl) ← affine lo
  let (ba, ca) ← affine a
  if bl.isNone then
    -- a literal below an offset of a bounded base
    let some t := ba | return none
    let some (hl, l, hh, h) ← bounds t | return none
    unless 0 ≤ (l : Int) + toInt64 ca ∧ (h : Int) + toInt64 ca < 2 ^ 64 ∧ (cl : Int) ≤ l + toInt64 ca do
      return none
    return some (← appN ``Rv64mc.Tactic.lit_le_add [(`t, t), (`c, mkLit ca), (`k, mkRawNatLit cl),
      (`L, mkNatLit l), (`H, mkNatLit h), (`hL, hl), (`hH, hh),
      (`h, ← mkEqRefl (mkConst ``Bool.true))])
  if ba.isNone then
    let some t := bl | return none
    let some (hl, l, hh, h) ← bounds t | return none
    unless 0 ≤ (l : Int) + toInt64 cl ∧ (h : Int) + toInt64 cl ≤ ca do return none
    return some (← appN ``Rv64mc.Tactic.add_le_lit [(`t, t), (`c, mkLit cl), (`k, mkRawNatLit ca),
      (`L, mkNatLit l), (`H, mkNatLit h), (`hL, hl), (`hH, hh),
      (`h, ← mkEqRefl (mkConst ``Bool.true))])
  let some t := bl | return none
  unless bl == ba do
    -- below a base that a hypothesis puts at or below `a`
    let some ha ← leHyp t a | return none
    if cl == 0 then return some ha
    let some (hl, l, _, _) ← bounds t | return none
    unless toInt64 cl < 0 && 0 ≤ (l : Int) + toInt64 cl do return none
    return some (← appN ``Rv64mc.Tactic.add_le_of_le [(`t, t), (`a, a), (`c, mkLit cl),
      (`L, mkNatLit l), (`hL, hl), (`ha, ha), (`h, ← mkEqRefl (mkConst ``Bool.true))])
  let some (hl, l, hh, h) ← bounds t | return none
  let ok := 0 ≤ (l : Int) + toInt64 cl ∧ (h : Int) + toInt64 ca < 2 ^ 64 ∧ toInt64 cl ≤ toInt64 ca
  unless ok do return none
  let lN := mkNatLit l
  let hN := mkNatLit h
  let tru ← mkEqRefl (mkConst ``Bool.true)
  let common := [(`t, t), (`L, lN), (`H, hN), (`hL, hl), (`hH, hh), (`h, tru)]
  if cl == 0 then return some (← appN ``Rv64mc.Tactic.le_add ((`c, mkLit ca) :: common))
  if ca == 0 then return some (← appN ``Rv64mc.Tactic.add_le ((`c, mkLit cl) :: common))
  return some (← appN ``Rv64mc.Tactic.add_le_add ((`c1, mkLit cl) :: (`c2, mkLit ca) :: common))

/-- A proof of `a < b` for offsets of one bounded base. -/
def ltProof (a b : Expr) : MetaM (Option Expr) := do
  let (ba, ca) ← affine a
  let (bb, cb) ← affine b
  let some t := ba | return none
  unless ba == bb do return none
  let some (hl, l, hh, h) ← bounds t | return none
  unless 0 ≤ (l : Int) + toInt64 ca ∧ (h : Int) + toInt64 cb < 2 ^ 64 ∧ toInt64 ca < toInt64 cb do return none
  let common := [(`t, t), (`L, mkNatLit l), (`H, mkNatLit h),
    (`hL, hl), (`hH, hh), (`h, ← mkEqRefl (mkConst ``Bool.true))]
  if cb == 0 then return some (← appN ``Rv64mc.Tactic.add_lt ((`c, mkLit ca) :: common))
  if ca == 0 then return none
  return some (← appN ``Rv64mc.Tactic.add_lt_add ((`c1, mkLit ca) :: (`c2, mkLit cb) :: common))

/-- A hypothesis `∀ a, lo ≤ a → M.getMem a = N.getMem a`: what a callee's frame keeps of memory `M`. -/
def frames (M : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    let .forallE _ _ body _ := ty | continue
    let .forallE _ hle eq _ := body | continue
    unless hle.isAppOfArity ``LE.le 4 && eq.isAppOfArity ``Eq 3 do continue
    let lo := hle.appFn!.appArg!
    let lhs := eq.appFn!.appArg!
    let rhs := eq.appArg!
    unless lhs.isAppOfArity ``MachineState.getMem 2 && rhs.isAppOfArity ``MachineState.getMem 2 do continue
    unless lhs.appFn!.appArg! == M do continue
    if lo.hasLooseBVars then continue
    out := out.push (d.toExpr, lo, rhs.appFn!.appArg!)
  return out

/-- The doubleword `M` holds at `x`, read through its stores and its callees' frames, and a proof of
    `M.getMem x = v` where it is not `M.getMem x` itself. -/
partial def readMem (M x : Expr) : MetaM (Expr × Option Expr) := do
  let M := M.consumeMData
  if M.isAppOfArity ``MachineState.setMem 3 then
    let N := M.appFn!.appFn!.appArg!
    let y := M.appFn!.appArg!
    let w := M.appArg!
    let (bx, cx) ← affine x
    let (by_, cy) ← affine y
    if x == y || (bx == by_ && cx == cy) then
      return (w, some (← mkAppOptM ``MachineState.getMem_setMem_eq #[N, y, w]))
    if let some hne ← neProof x y then
      let p1 ← mkAppOptM ``MachineState.getMem_setMem_ne #[N, y, x, w, hne]
      let (v, p2) ← readMem N x
      return (v, some (← transOpt p1 p2))
    return (← mkAppM ``MachineState.getMem #[M, x], none)
  for (F, lo, N) in ← frames M do
    if let some hle ← leProof lo x then
      let p1 := mkApp2 F x hle
      let (v, p2) ← readMem N x
      return (v, some (← transOpt p1 p2))
  return (← mkAppM ``MachineState.getMem #[M, x], none)

/-! ## Goals -/

/-- A goal `SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, R, M⟩`, its parts. -/
structure At where
  head : Expr
  pre : Array Expr
  stMk : Expr
  cons : Expr
  frMk : Expr
  fnE : Expr
  pc : Nat
  rv : Expr
  top : Expr
  rest : Expr
  R : Expr
  M : Expr

def parseAt (t : Expr) : MetaM (Option At) := do
  let t := (← instantiateMVars t).consumeMData
  unless t.isAppOfArity ``Lprog.Isa.SafeN 8 do return none
  let args := t.getAppArgs
  let s ← whnfR (args[7]!)
  unless s.isAppOfArity ``Lprog.State.mk 4 do return none
  let st ← whnfR (s.getAppArgs[1]!)
  unless st.isAppOfArity ``List.cons 3 do return none
  let fr ← whnfR (st.getAppArgs[1]!)
  unless fr.isAppOfArity ``Lprog.Frame.mk 4 do return none
  let some pc ← evalNat (fr.getAppArgs[1]!) | return none
  return some ⟨t.getAppFn, args.extract 0 7, mkApp s.getAppFn (s.getAppArgs[0]!),
    mkApp st.getAppFn (st.getAppArgs[0]!), fr.getAppFn, fr.getAppArgs[0]!, pc, fr.getAppArgs[2]!,
    fr.getAppArgs[3]!, st.getAppArgs[2]!, s.getAppArgs[2]!, s.getAppArgs[3]!⟩

/-- The goal at another program counter, register file and memory. -/
def At.goal (a : At) (pc : Nat) (R M : Expr) : Expr :=
  mkAppN a.head (a.pre.push (mkApp3 a.stMk
    (mkApp2 a.cons (mkApp4 a.frMk a.fnE (mkNatLit pc) a.rv a.top) a.rest) R M))

/-- The arguments every rule of `Steps` takes first. -/
def At.common (a : At) (fd : Expr) : List (Name × Expr) :=
  [(`p, (a.pre[1]!)), (`E, (a.pre[2]!)), (`c, (a.pre[3]!)), (`G, (a.pre[4]!)), (`n, (a.pre[5]!)), (`Q, (a.pre[6]!)),
    (`rest, a.rest), (`regs, a.R), (`m, a.M), (`fd, fd), (`fn, a.fnE), (`pc, mkNatLit a.pc), (`rv, a.rv),
    (`top, a.top)]

/-- A new goal of type `t` in the context of `g`. -/
def newGoal (g : MVarId) (t : Expr) : MetaM Expr :=
  g.withContext do mkFreshExprSyntheticOpaqueMVar t (← g.getTag)

/-! ## Splitting facts -/

def keep : List Name := [``Ne, ``Not, ``Iff, ``Lprog.Isa.Contract, ``Lprog.Isa.SafeN, ``LE.le, ``LT.lt, ``Eq,
  ``Rv64mc.Env.Frame, ``Rv64mc.Env.Static, ``Rv64mc.Env.MayWrite, ``Rv64mc.Env.next, ``Rv64mc.Holds,
  -- `Core/Repr.lean`'s representation predicates, which a proof uses whole (`EListAt.keep`, `Frame.keeps_live`)
  `Rv64mc.Env.Live, `Rv64mc.Env.Fresh, `Rv64mc.Keeps, `Rv64mc.InRange, `Rv64mc.WordsAt, `Rv64mc.EAt,
  `Rv64mc.EListAt, `Rv64mc.BytesAt, `Rv64mc.DigestAt, `Rv64mc.VecAt]

/-- A Prop-valued definition at the head of `t`, unfolded. -/
def unfoldHead? (t : Expr) : MetaM (Option Expr) := do
  let some n := t.getAppFn.constName? | return none
  if keep.contains n then return none
  let some (.defnInfo _) := (← getEnv).find? n | return none
  let some t' ← unfoldDefinition? t | return none
  return some (t'.headBeta)

/-- The conjuncts of a fact, its definitions unfolded, each with its proof. -/
partial def splitFact (pf ty : Expr) : MetaM (Array (Expr × Expr)) := do
  let ty := (← instantiateMVars ty).consumeMData.headBeta
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    return (← splitFact (mkApp3 (mkConst ``And.left) a b pf) a) ++
      (← splitFact (mkApp3 (mkConst ``And.right) a b pf) b)
  if ty.isConstOf ``True then return #[]
  if let some ty' ← unfoldHead? ty then return ← splitFact pf ty'
  let (ty', p) ← normReads ty
  match p with
  | some p => return #[(← mkEqMP p pf, ty')]
  | none => return #[(pf, ty')]

/-- The facts added to the context, under names `base_k`. -/
def addFacts (g : MVarId) (base : Name) (facts : Array (Expr × Expr)) : MetaM (MVarId × Array FVarId) := do
  let hs := facts.mapIdx fun k (pf, ty) =>
    ({ userName := base.appendIndexAfter (k + 1), type := ty, value := pf } : Hypothesis)
  let (fvs, g) ← g.assertHypotheses hs
  return (g, fvs)

/-- The goal's register file, if the executor did not make it, as the `rf` of its values with the facts `R r = v`
    written into their places (`rf_eta`, `regs_eq`). -/
def absorbFacts (g : MVarId) (facts : Array Expr) : MetaM MVarId := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``Lprog.Isa.SafeN 8 do return g
  let args := t.getAppArgs
  let s ← whnfR (args[7]!)
  unless s.isAppOfArity ``Lprog.State.mk 4 do return g
  let st := s.getAppArgs[1]!
  let R0 := (s.getAppArgs[2]!).consumeMData
  let M := s.getAppArgs[3]!
  if R0.isAppOfArity ``Rv64mc.Tactic.rf 32 then return g
  -- `R0 = rf (R0 .x0) … (R0 .x31)`, then each fact `R0 r = v` written into its place
  let regs := (List.range 32).toArray.map fun i => mkConst (Name.mkStr `RiscvZkvm.Rv64.Reg s!"x{i}")
  let mut vals := regs.map (mkApp R0)
  let mut eqs : Array (Option Expr) := regs.map fun _ => none
  for h in facts do
    let ty := (← instantiateMVars (← inferType h)).consumeMData
    unless ty.isAppOfArity ``Eq 3 do continue
    let lhs := ty.appFn!.appArg!.consumeMData
    let .app f r := lhs | continue
    unless f == R0 do continue
    let some k := regIdx? r | continue
    if eqs[k]!.isSome then continue
    let (v, pv) ← normReads ty.appArg!
    vals := vals.set! k v
    eqs := eqs.set! k (some (← transOpt h pv))
  let p0 ← mkAppM ``Rv64mc.Tactic.rf_eta #[R0]
  let mut fn := mkConst ``Rv64mc.Tactic.rf
  let mut pf : Option Expr := none
  for k in [0:32] do
    let a := mkApp R0 (regs[k]!)
    match eqs[k]!, pf with
    | none, none => fn := mkApp fn a
    | none, some p => pf := some (← mkCongrFun p a); fn := mkApp fn a
    | some e, none => pf := some (← mkCongrArg fn e); fn := mkApp fn (vals[k]!)
    | some e, some p => pf := some (← mkCongr p e); fn := mkApp fn (vals[k]!)
  let R' := mkAppN (mkConst ``Rv64mc.Tactic.rf) vals
  let e ← transOpt p0 pf
  let goalT := mkAppN t.getAppFn ((args.extract 0 7).push (mkApp3 (mkApp s.getAppFn (s.getAppArgs[0]!)) st R' M))
  let g' ← newGoal g goalT
  g.assign (← appN ``Rv64mc.Tactic.regs_eq [(`p, (args[1]!)), (`E, (args[2]!)), (`c, (args[3]!)), (`G, (args[4]!)),
    (`n, (args[5]!)), (`Q, (args[6]!)), (`m, M), (`st, st), (`R, R0), (`R', R'), (`e, e), (`k, g')])
  return g'.mvarId!

/-! ## `Holds`: the memory frame, the static data, `NEXT`, the stack -/

/-- `out` is the empty set of words (`fun _ => False`, as a contract's default `Out` gives it). -/
def isF (out : Expr) : MetaM Bool := do
  match (← whnfR out).headBeta with
  | .lam _ _ b _ => return b.isConstOf ``False
  | _ => return false

/-- The function's own stack bound, `env.stackLimit.toNat + need ≤ top.toNat` (`Holds.pre`): its proof, `S`,
    `top`, `need` and `need`'s value. -/
def rawStack : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``LE.le 4 then
      let a := ty.appFn!.appArg!
      let b := ty.appArg!
      if b.isAppOfArity ``BitVec.toNat 2 && a.isAppOfArity ``HAdd.hAdd 6 then
        let S := a.appFn!.appArg!
        if S.isAppOfArity ``BitVec.toNat 2 && S.appArg!.isAppOf ``Rv64mc.Env.stackLimit then
          return some (d.toExpr, S, b.appArg!, a.appArg!)
  return none

/-- The function's own stack bound as `S + k ≤ top.toNat`, `k` a numeral (`stackLit`): its proof, `S`, `top`, `k` and
    its value. -/
def ownStack : MetaM (Option (Expr × Expr × Expr × Expr × Nat)) := do
  let some (h, S, t, need) ← rawStack | return none
  let some (hk, k) ← stackLit h S t need | return none
  return some (hk, S, t, mkNatLit k, k)

/-- A hypothesis whose type is `t`, up to reducible unfolding. -/
def hypOf (t : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← withReducible (isDefEq (← instantiateMVars d.type) t) then return some d.toExpr
  return none

/-- A proof of `S + need ≤ (t + c).toNat` style facts about a slot `x` of the stack below `top`, from the stack
    bound: `S ≤ x.toNat` and `x.toNat < top.toNat`, or `x.toNat ≤ top.toNat` (`le`). -/
def slotFacts (x : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some (h, S, top, need, nv) ← ownStack | return none
  let (bx, cx) ← affine x
  unless bx == some top && toInt64 cx < 0 && 0 ≤ (nv : Int) + toInt64 cx do return none
  let args := [(`S, S), (`need, need), (`t, top), (`c, mkLit cx), (`h, h), (`hc, ← mkEqRefl (mkConst ``Bool.true))]
  return some (← appN ``Rv64mc.Tactic.slot_ge args, ← appN ``Rv64mc.Tactic.slot_lt args,
    ← appN ``Rv64mc.Tactic.slot_le args)

/-- `env.Frame top F m0 X`, for `X` the memory the function made from `m0`: its stores into its stack, its callees'
    frames (`Env.Frame … F N X` in the context). -/
partial def frameWalk (env top m0 X : Expr) : MetaM (Option Expr) := do
  let X := X.consumeMData
  if X == m0 then
    let nx ← mkAppM ``Rv64mc.Env.next #[env, m0]
    let hnxT ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[nx], ← mkAppM ``BitVec.toNat #[← mkAppM ``Rv64mc.Env.heapEnd #[env]]]
    let some hnx ← hypOf hnxT | return none
    return some (← appN ``Rv64mc.Tactic.frame_refl [(`env, env), (`top, top), (`m, m0), (`h, hnx)])
  if X.isAppOfArity ``MachineState.setMem 3 then
    let N := X.appFn!.appFn!.appArg!
    let a := X.appFn!.appArg!
    let v := X.appArg!
    let some h1 ← frameWalk env top m0 N | return none
    let some (hlo, hhi, _) ← slotFacts a | return none
    return some (← appN ``Rv64mc.Tactic.frame_store [(`env, env), (`top, top), (`a, a), (`v, v), (`m, m0), (`N, N),
      (`h1, h1), (`hlo, hlo), (`hhi, hhi)])
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    unless ty.isAppOfArity ``Rv64mc.Env.Frame 5 do continue
    let args := ty.getAppArgs
    unless args[4]! == X && (← isF (args[2]!)) do continue
    let top' := args[1]!
    let N := args[3]!
    let ht ← if top' == top then mkAppM ``Nat.le_refl #[← mkAppM ``BitVec.toNat #[top]] else do
      let some (_, _, hle) ← slotFacts top' | continue
      pure hle
    let some h1 ← frameWalk env top m0 N | continue
    return some (← appN ``Rv64mc.Tactic.frame_call [(`env, env), (`top, top), (`top', top'), (`m, m0), (`N, N),
      (`X, X), (`h1, h1), (`h2, d.toExpr), (`ht, ht)])
  return none

/-- The entry's memory: the one `env.Static` and `NEXT`'s bound are assumed of (`Holds.pre`). -/
def entryMem (env : Expr) : MetaM (Option (Expr × Expr)) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``Rv64mc.Env.Static 2 && ty.appFn!.appArg! == env then
      let m0 := ty.appArg!
      let nx ← mkAppM ``Rv64mc.Env.next #[env, m0]
      let hnxT ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[nx],
        ← mkAppM ``BitVec.toNat #[← mkAppM ``Rv64mc.Env.heapEnd #[env]]]
      if (← hypOf hnxT).isSome then return some (m0, d.toExpr)
  return none

/-- A callee's room `S + need' ≤ (top + c).toNat` for a `need'` that is a parameter: from the stack bound
    `S + need ≤ top.toNat` and a hypothesis `k + need' ≤ need` with `-c ≤ k` (`room_hyp`), or `need' ≤ need` and `c = 0`. -/
def roomParam (a b : Expr) : MetaM (Option Expr) := do
  let some (h, S, top, need) ← rawStack | return none
  unless a.appFn!.appArg! == S do return none
  let need' := a.appArg!
  let (bx, cx) ← affine b.appArg!
  unless bx == some top do return none
  for (k, hn, x?) in ← needHyps need do
    match x? with
    | some x =>
      if x == need' && toInt64 cx ≤ 0 && -toInt64 cx ≤ k then
        if cx == 0 then
          return some (← mkAppM ``Rv64mc.Tactic.room_hyp0 #[h, ← mkAppM ``Nat.le_trans
            #[← mkAppM ``Nat.le_add_left #[need', mkNatLit k], hn]])
        return some (← appN ``Rv64mc.Tactic.room_hyp [(`S, S), (`need, need), (`need', need'), (`k, (← inferType hn).appFn!.appArg!.appFn!.appArg!),
          (`t, top), (`c, mkLit cx), (`h, h), (`hn, hn), (`hc, ← mkEqRefl (mkConst ``Bool.true))])
    | none => pure ()
  return none

/-- A goal of `Holds`'s: the frame of the function's memory, the static data or `NEXT`'s bound in a memory it made,
    a callee's stack room. -/
def holdsGoal (ty : Expr) : MetaM (Option Expr) := do
  if ty.isAppOfArity ``Rv64mc.Env.Frame 5 then
    let args := ty.getAppArgs
    let some h ← frameWalk (args[0]!) (args[1]!) (args[3]!) (args[4]!) | return none
    return some (← appN ``Rv64mc.Tactic.frame_weaken [(`env, args[0]!), (`top, args[1]!), (`out, args[2]!),
      (`m, args[3]!), (`X, args[4]!), (`h, h)])
  let viaFrame (env X : Expr) : MetaM (Option (Expr × Expr)) := do
    let some (m0, hst) ← entryMem env | return none
    let some (_, _, top, _, _) ← ownStack | return none
    let some h ← frameWalk env top m0 X | return none
    return some (h, hst)
  if ty.isAppOfArity ``Rv64mc.Env.Static 2 then
    let some (h, hst) ← viaFrame ty.appFn!.appArg! ty.appArg! | return none
    return some (← mkAppM ``Rv64mc.Tactic.static_of_frame #[hst, h])
  if ty.isAppOfArity ``LE.le 4 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    -- `(env.next X).toNat ≤ env.heapEnd.toNat`
    if a.isAppOfArity ``BitVec.toNat 2 && a.appArg!.isAppOfArity ``Rv64mc.Env.next 2 &&
        b.isAppOfArity ``BitVec.toNat 2 && b.appArg!.isAppOf ``Rv64mc.Env.heapEnd then
      let nx := a.appArg!
      let some (h, _) ← viaFrame nx.appFn!.appArg! nx.appArg! | return none
      return some (← mkAppM ``Rv64mc.Tactic.frame_next #[h])
    -- `env.stackLimit.toNat + need' ≤ (top + c).toNat`: a callee's room
    if b.isAppOfArity ``BitVec.toNat 2 && a.isAppOfArity ``HAdd.hAdd 6 then
      let some need' ← natVal? a.appArg! | return ← roomParam a b
      let some (h, S, top, need, nv) ← ownStack | return none
      unless a.appFn!.appArg! == S do return none
      let (bx, cx) ← affine b.appArg!
      unless bx == some top do return none
      let tru ← mkEqRefl (mkConst ``Bool.true)
      if cx == 0 then
        unless need' ≤ nv do return none
        return some (← appN ``Rv64mc.Tactic.room0 [(`S, S), (`need, need), (`need', a.appArg!), (`t, top), (`h, h),
          (`hc, tru)])
      unless toInt64 cx ≤ 0 && (need' : Int) - toInt64 cx ≤ nv do return none
      return some (← appN ``Rv64mc.Tactic.room [(`S, S), (`need, need), (`need', a.appArg!), (`t, top),
        (`c, mkLit cx), (`h, h), (`hc, tru)])
  return none

/-- The elements of a literal list (through definitions), if it is one. -/
partial def listElems (l : Expr) : MetaM (Option (Array Expr)) := do
  let l ← whnf l
  if l.isAppOfArity ``List.nil 1 then return some #[]
  if l.isAppOfArity ``List.cons 3 then
    let some rest ← listElems l.appArg! | return none
    return some (#[l.appFn!.appArg!] ++ rest)
  return none

/-- A load from a constant table: `x` is `d.hi + d.lo + 8 k` for a data reference `d` whose words a hypothesis
    `DataRef.Words env d ws` gives, in a memory where `env.Static` holds (`holdsGoal`). -/
def dataRead (M x : Expr) : MetaM (Option (Expr × Expr)) := do
  let (bx, cx) ← affine x
  let some b := bx | return none
  unless b.isAppOfArity ``HAdd.hAdd 6 do return none
  let hi := b.appFn!.appArg!
  let lo := b.appArg!
  unless hi.isAppOfArity ``Rv64mc.DataRef.hi 1 && lo.isAppOfArity ``Rv64mc.DataRef.lo 1 && hi.appArg! == lo.appArg! do
    return none
  unless cx % 8 == 0 do return none
  let k := cx / 8
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    unless ty.isAppOfArity ``Rv64mc.DataRef.Words 3 && ty.getAppArgs[1]! == hi.appArg! do continue
    let env := ty.getAppArgs[0]!
    let ws := ty.getAppArgs[2]!
    let some elems ← listElems ws | continue
    unless k < elems.size do continue
    let some hs ← holdsGoal (← mkAppM ``Rv64mc.Env.Static #[env, M]) | continue
    let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, ← mkAppM ``List.length #[ws]])
    let p ← if k == 0 then mkAppM ``Rv64mc.DataRef.Words.get0 #[d.toExpr, hs, hk]
      else mkAppM ``Rv64mc.DataRef.Words.get #[d.toExpr, hs, mkNatLit k, hk]
    let v := elems[k]!
    return some (v, ← mkExpectedTypeHint p (← mkEq (← mkAppM ``MachineState.getMem #[M, x]) v))
  return none

/-! ## Side goals -/

/-- A proof of `X.getMem a = Y.getMem a` for an address `a` at or above `lo` (`ha : lo ≤ a`): every store into `X`
    since `Y` is below `lo`, and every callee's frame keeps what is at or above `lo`. -/
partial def memKeep (X Y a lo ha : Expr) : MetaM (Option Expr) := do
  let X := X.consumeMData
  if X == Y || (← withReducible (isDefEq X Y)) then return some (← mkEqRefl (← mkAppM ``MachineState.getMem #[X, a]))
  if X.isAppOfArity ``MachineState.setMem 3 then
    let N := X.appFn!.appFn!.appArg!
    let y := X.appFn!.appArg!
    let w := X.appArg!
    let some hlt ← ltProof y lo | return none
    let hne ← mkAppM ``Rv64mc.Tactic.ne_of_lt_le #[hlt, ha]
    let p1 ← mkAppOptM ``MachineState.getMem_setMem_ne #[N, y, a, w, hne]
    let some p2 ← memKeep N Y a lo ha | return none
    return some (← mkEqTrans p1 p2)
  for (F, lo', N) in ← frames X do
    let hle ← if lo' == lo then pure (some ha) else do
      let some h ← leProof lo' lo | pure none
      pure (some (← mkAppM ``BitVec.le_trans #[h, ha]))
    let some hle := hle | continue
    let some p2 ← memKeep N Y a lo ha | continue
    return some (← mkEqTrans (mkApp2 F a hle) p2)
  return none

/-- Close what is closed by reduction, by an address fact, or by a hypothesis; split conjunctions, unfold
    definitions; leave the rest, its reads reduced. -/
partial def closeSide (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    let ga ← newGoal g a
    let gb ← newGoal g b
    g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
    return (← closeSide ga.mvarId!) ++ (← closeSide gb.mvarId!)
  if let some pf ← holdsGoal ty then
    g.assign pf
    return []
  if let some ty' ← unfoldHead? ty then
    let g' ← g.replaceTargetDefEq ty'
    return ← closeSide g'
  let (ty, p) ← normReads ty
  if let some pf ← holdsGoal ty then
    let g ← match p with
      | some p => g.replaceTargetEq ty p
      | none => pure g
    g.assign pf
    return []
  let g ← match p with
    | some p => g.replaceTargetEq ty p
    | none => pure g
  if let .forallE _ _ (.forallE _ hle eq _) _ := ty then
    if hle.isAppOfArity ``LE.le 4 && eq.isAppOfArity ``Eq 3 then
      let saved ← saveState
      let (fvs, g') ← g.introN 2 [`a, `ha]
      let done ← g'.withContext do
        let a := mkFVar (fvs[0]!)
        let ty' := (← instantiateMVars (← g'.getType)).consumeMData
        let lo := (← instantiateMVars (← inferType (mkFVar (fvs[1]!)))).consumeMData.appFn!.appArg!
        let lhs := ty'.appFn!.appArg!
        let rhs := ty'.appArg!
        if lhs.isAppOfArity ``MachineState.getMem 2 && rhs.isAppOfArity ``MachineState.getMem 2 then
          if let some pf ← memKeep lhs.appFn!.appArg! rhs.appFn!.appArg! a lo (mkFVar (fvs[1]!)) then
            g'.assign pf; return true
        return false
      if done then return []
      saved.restore
  if ty.isAppOfArity ``Eq 3 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    let (ba, ca) ← affine a
    let (bb, cb) ← affine b
    if a == b || (ba == bb && ca == cb) || (← withReducible (isDefEq a b)) then
    g.assign (← mkEqRefl a)
    return []
  if ty.isAppOfArity ``LE.le 4 then
    if let some p ← leProof ty.appFn!.appArg! ty.appArg! then
    g.assign p
    return []
  if ty.isAppOfArity ``Ne 3 then
    if let some p ← neProof ty.appFn!.appArg! ty.appArg! then
    g.assign p
    return []
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).consumeMData == ty then
    g.assign d.toExpr
    return []
  return [g]

/-- A branch's hypothesis `hc` under a name of its own: the earlier ones are `hc_1`, `hc_2`, … in the order they were
    added, the latest `hc`. -/
def nameApart (g : MVarId) : MetaM MVarId := g.withContext do
  let lctx ← getLCtx
  let same := lctx.foldl (init := #[]) fun acc d =>
    if !d.isImplementationDetail && d.userName == `hc then acc.push d.fvarId else acc
  if same.size ≤ 1 then return g
  let mut k := lctx.foldl (init := 0) fun k d =>
    match d.userName with
    | .str .anonymous s => if !d.isImplementationDetail && s.startsWith "hc_" then k + 1 else k
    | _ => k
  let mut g := g
  for fv in same.pop do
    k := k + 1
    g ← g.rename fv (Name.mkSimple s!"hc_{k}")
  return g

/-! ## The executor -/

structure Cfg where
  hp : Expr
  fd : Expr
  body : Array Expr
  /-- The body's suffixes as literal lists, each the tail of the one before, and `fd.body = suffixes[0]`. -/
  suffixes : Array Expr
  hbody : Expr
  specs : Array (Expr × Expr)
  facts : Array (Expr × Expr)
  stops : List Nat
  /-- The targets of backward jumps: a path stops at one, for a loop's lemma, rather than going round. -/
  heads : List Nat

/-- The instructions of the body of `fd`, a literal. -/
partial def bodyOf (fd : Expr) : MetaM (Array Expr) := do
  let b ← whnf (← mkAppM ``Lprog.Lfundef.body #[fd])
  let rec go (l : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let l ← whnf l
    if l.isAppOfArity ``List.cons 3 then go l.appArg! (acc.push l.appFn!.appArg!)
    else return acc
  go b #[]

/-- `fd.body.drop pc = suffixes[pc]`, from the body's literal: the kernel walks the literal `pc` steps, once. -/
def dropAt (cfg : Cfg) (pc : Nat) : MetaM Expr := do
  appN ``Rv64mc.Tactic.drop_at [(`α, ← inferType (cfg.body[0]!)), (`l, ← mkAppM ``Lprog.Lfundef.body #[cfg.fd]),
    (`full, cfg.suffixes[0]!), (`rest, cfg.suffixes[pc]!), (`h, cfg.hbody), (`n, mkNatLit pc),
    (`h', ← mkEqRefl (cfg.suffixes[pc]!))]

/-- The index the label `l` is at. -/
def labelIdx? (body : Array Expr) (l : Nat) : MetaM (Option Nat) := do
  for h : k in [0:body.size] do
    let i := body[k]
    if i.isAppOfArity ``Lprog.LinstrR.Llabel 4 then
      if (← evalNat i.appArg!) == some l then return some k
  return none

/-- A fact among those given whose type is `lhs = ?` with `lhs` the given term, its right side and proof. -/
def factEq (cfg : Cfg) (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  for (pf, ty) in cfg.facts do
    let ty := ty.consumeMData
    if ty.isAppOfArity ``Eq 3 then
      if ← withReducible (isDefEq ty.appFn!.appArg! lhs) then return some (ty.appArg!, pf)
  return none

/-- The proof that a call target reaches function `f`: the address of `f` and, for an indirect call, the value of
    its expression, both from the facts given. -/
def calleeProof (cfg : Cfg) (R tgt f : Expr) : MetaM (Option Expr) := do
  let tgt := tgt.consumeMData
  -- `(p[f]?).map (·.addr) = some entry`
  let mut addr : Option (Expr × Expr) := none
  for (pf, ty) in cfg.facts do
    let ty := ty.consumeMData
    if ty.isAppOfArity ``Eq 3 then
      let lhs := ty.appFn!.appArg!
      if lhs.isAppOfArity ``Option.map 4 then
        let g := lhs.appArg!
        if g.isAppOf ``GetElem?.getElem? && (← withReducible (isDefEq g.appArg! f)) then
          let rhs := ty.appArg!
          if rhs.isAppOfArity ``Option.some 2 then addr := some (rhs.appArg!, pf)
  let some (entry, ha) := addr | return none
  if tgt.isAppOfArity ``Lprog.Target.direct 2 then
    return some (← mkAppOptM ``Rv64mc.Tactic.callee_direct #[none, R, f, entry, ha])
  unless tgt.isAppOfArity ``Lprog.Target.indirect 3 do return none
  let e := tgt.appFn!.appArg!
  let (v, pv) ← evalE R e
  let some (entry', hs) ← factEq cfg v | return none
  unless ← withReducible (isDefEq entry entry') do return none
  let he ← mkEqTrans pv hs
  return some (← mkAppOptM ``Rv64mc.Tactic.callee_indirect #[none, R, e, f, entry, ha, he])

/-- The callee a target names, if it names one: the single candidate of an indirect call, or a direct call's. -/
def targetIdx (tgt : Expr) : MetaM (Option Expr) := do
  let tgt := tgt.consumeMData
  if tgt.isAppOfArity ``Lprog.Target.direct 2 then return some tgt.appArg!
  if tgt.isAppOfArity ``Lprog.Target.indirect 3 then
    let l ← whnfR tgt.appArg!
    if l.isAppOfArity ``List.cons 3 then
      let t ← whnfR l.appArg!
      if t.isAppOfArity ``List.nil 1 then return some l.appFn!.appArg!
  return none

/-- A definition of a contract (`Holds`, a `NoReturn`) unfolded to the contract it is. -/
partial def toContract (ty : Expr) : MetaM Expr := do
  let ty := ty.consumeMData.headBeta
  if ty.isAppOf ``Lprog.Isa.Contract then return ty
  match ← unfoldDefinition? ty with
  | some ty' => toContract ty'
  | none => return ty

/-- A contract among those given for function `f`. -/
def specFor (cfg : Cfg) (f : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  for (pf, ty) in cfg.specs do
    -- a contract for every function, or for each value of a parameter: its arguments by unification
    let (xs, _, ty) ← forallMetaTelescope ty
    let ty ← toContract (← instantiateMVars ty)
    if ty.isAppOfArity ``Lprog.Isa.Contract 7 then
      let args := ty.getAppArgs
      if ← withReducible (isDefEq (args[4]!) f) then
        let pf ← instantiateMVars (mkAppN pf xs)
        if pf.hasExprMVar then continue
        return some (pf, ← instantiateMVars (args[5]!), ← instantiateMVars (args[6]!))
  return none

/-- After a call: `r'`, `m'` and the postcondition introduced, split into hypotheses `hret_k`, and what it says of
    `r'` written into the register file. -/
def afterCall (g : MVarId) (k : Nat) : MetaM (Option MVarId) := do
  let (fvs, g) ← g.introN 3 [Name.mkSimple s!"r{k}", Name.mkSimple s!"m{k}", Name.mkSimple s!"post{k}"]
  g.withContext do
    let post := mkFVar (fvs[2]!)
    let facts ← splitFact post (← inferType post)
    let (g, hs) ← addFacts g (Name.mkSimple s!"hret{k}") facts
    for (h, (_, ty)) in hs.zip facts do
      if ty.isConstOf ``False then
        g.withContext do g.assign (← mkFalseElim (← g.getType) (mkFVar h))
        return none
    let g ← g.tryClear (fvs[2]!)
    let g ← g.withContext do
      let mut above := #[]
      for h in hs do
        let ty := (← instantiateMVars (← h.getType)).consumeMData
        unless ty.isAppOfArity ``Rv64mc.Env.Frame 5 do continue
        let args := ty.getAppArgs
        unless ← isF (args[2]!) do continue
        let some (hb, S, top, need, _) ← ownStack | continue
        let hlim ← if args[1]! == top then
            mkAppM ``Nat.le_trans #[← mkAppM ``Nat.le_add_right #[S, need], hb]
          else do
            let some (hlo, _, _) ← slotFacts (args[1]!) | continue
            pure hlo
        let pf ← appN ``Rv64mc.Tactic.frame_above [(`env, args[0]!), (`top, args[1]!), (`M, args[3]!),
          (`X, args[4]!), (`h, mkFVar h), (`hlim, hlim)]
        above := above.push (pf, ← inferType pf)
      if above.isEmpty then return g
      let (g, _) ← addFacts g (Name.mkSimple s!"keep{k}") above
      return g
    some <$> absorbFacts g (hs.map mkFVar)

/-- The goal that the function has returned to its caller: closed by the contract's continuation in the context
    (`∀ r' m', Post … → SafeN p c G n Q ⟨rest, r', m'⟩`), leaving the postcondition. -/
def finish (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``Lprog.Isa.SafeN 8 do return none
  let s ← whnfR ty.appArg!
  unless s.isAppOfArity ``Lprog.State.mk 4 do return none
  let R := (s.getAppArgs[2]!)
  let M := (s.getAppArgs[3]!)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dt := (← instantiateMVars d.type).consumeMData
    let .forallE _ _ (.forallE _ _ (.forallE _ hpost body _) _) _ := dt | continue
    let body := body.consumeMData
    unless body.isAppOfArity ``Lprog.Isa.SafeN 8 do continue
    let s' := body.appArg!
    unless s'.isAppOfArity ``Lprog.State.mk 4 do continue
    let inst := body.instantiateRev #[R, M, mkConst ``True.intro]
    unless ← withReducible (isDefEq inst ty) do continue
    let postT := hpost.instantiateRev #[R, M]
    let gp ← newGoal g postT
    g.assign (mkApp3 d.toExpr R M gp)
    return some gp.mvarId!
  return none

/-- One goal stepped as far as the rules go: the goals left. -/
partial def run (cfg : Cfg) (g0 : MVarId) : MetaM (List MVarId) := do
  let mut todo : List (MVarId × List Nat × Option Expr) := [(g0, [], none)]
  let mut left : Array MVarId := #[]
  let mut calls := 0
  let mut steps := 0
  while !todo.isEmpty do
    let (g, seen, hd?) := todo.head!
    todo := todo.tail!
    let at? ← g.withContext do parseAt (← g.getType)
    let some a := at?
      | let gp? ← finish g
        if let some gp := gp? then left := left ++ (← closeSide gp) else left := left.push g
        continue
    if ((cfg.stops.contains a.pc || cfg.heads.contains a.pc) && g != g0) || seen.contains a.pc then
      trace[rv_sym] "left at {a.pc}: a stop or a loop's head"
      left := left.push g; continue
    let seen := a.pc :: seen
    let some ins := cfg.body[a.pc]? | left := left.push g; continue
    let ins := ins.consumeMData
    let common := a.common cfg.fd
    let α ← inferType ins
    let hd ← match hd? with
      | some hd => pure hd
      | none => dropAt cfg a.pc
    let l ← mkAppM ``Lprog.Lfundef.body #[cfg.fd]
    let common3 := [(`α, α), (`l, l), (`rest, cfg.suffixes[a.pc + 1]!), (`n, mkNatLit a.pc), (`a, ins), (`h, hd)]
    let hi ← appN ``Rv64mc.Tactic.drop_get common3
    let hdNext ← appN ``Rv64mc.Tactic.drop_next common3
    let base := common ++ [(`hf, cfg.hp), (`hi, hi)]
    let k := calls + 1
    if ins.isAppOf ``Lprog.LinstrR.Lcall || ins.isAppOf ``Lprog.LinstrR.Ltail then calls := k
    let step ← g.withContext do
      let args := ins.getAppArgs
      match ins.getAppFn.constName? with
      | some ``Lprog.LinstrR.Llabel =>
        let h ← newGoal g (a.goal (a.pc + 1) a.R a.M)
        g.assign (← appN ``Rv64mc.Tactic.step_label (base ++ [(`kd, (args[2]!)), (`l, (args[3]!)), (`h, h)]))
        pure (some [h.mvarId!])
      | some ``Lprog.LinstrR.Lgoto =>
        let some l ← evalNat (args[2]!) | pure none
        let some j ← labelIdx? cfg.body l | pure none
        let h ← newGoal g (a.goal j a.R a.M)
        g.assign (← appN ``Rv64mc.Tactic.step_goto (base ++ [(`l, (args[2]!)), (`j, mkNatLit j),
          (`hl, ← mkEqRefl (← mkAppM ``Option.some #[mkNatLit j])), (`h, h)]))
        pure (some [h.mvarId!])
      | some ``Lprog.LinstrR.Lopn =>
        let op := (args[2]!).consumeMData
        let oargs := op.getAppArgs
        match op.getAppFn.constName? with
        | some ``Lprog.Op.set =>
          let (v, hv) ← evalE a.R (oargs[2]!)
          let (R', hR) ← writeReg a.R (oargs[1]!) v
          let h ← newGoal g (a.goal (a.pc + 1) R' a.M)
          g.assign (← appN ``Rv64mc.Tactic.step_set (base ++ [(`rd, (oargs[1]!)), (`e, (oargs[2]!)), (`v, v),
            (`R', R'), (`hv, hv), (`hR, hR), (`h, h)]))
          pure (some [h.mvarId!])
        | some ``Lprog.Op.load =>
          let w := (oargs[2]!).consumeMData
          let s := (oargs[3]!).consumeMData
          let (x, ha) ← evalE a.R (oargs[4]!)
          if w.isConstOf ``Lprog.Width.b8 && s.isConstOf ``Bool.false then
            let (v, pv) ← match ← dataRead a.M x with
              | some (v, p) => pure (v, some p)
              | none => readMem a.M x
            let hv ← orRefl pv v
            let (R', hR) ← writeReg a.R (oargs[1]!) v
            let h ← newGoal g (a.goal (a.pc + 1) R' a.M)
            g.assign (← appN ``Rv64mc.Tactic.step_ld (base ++ [(`rd, (oargs[1]!)), (`a, (oargs[4]!)), (`x, x),
              (`v, v), (`R', R'), (`ha, ha), (`hv, hv), (`hR, hR), (`h, h)]))
            pure (some [h.mvarId!])
          else
            let lv ← whnfCore (← unfoldDefinition (mkApp3 (mkConst ``Rv64mc.Tactic.loadVal) w a.M x))
            let val := if s.isConstOf ``Bool.true then mkApp2 (mkConst ``UnOp.eval) (mkApp (mkConst ``UnOp.sext) w) lv
              else lv
            let ite ← mkAppM ``ite #[← mkEq s (mkConst ``Bool.true), mkApp2 (mkConst ``UnOp.eval)
              (mkApp (mkConst ``UnOp.sext) w) (mkApp3 (mkConst ``Rv64mc.Tactic.loadVal) w a.M x),
              mkApp3 (mkConst ``Rv64mc.Tactic.loadVal) w a.M x]
            -- the choice on a literal and the accessor by its width are reductions of constructors only
            let hv ← mkExpectedTypeHint (← mkEqRefl val) (← mkEq ite val)
            let (R', hR) ← writeReg a.R (oargs[1]!) val
            let h ← newGoal g (a.goal (a.pc + 1) R' a.M)
            g.assign (← appN ``Rv64mc.Tactic.step_loadw (base ++ [(`rd, (oargs[1]!)), (`w, w), (`s, s),
              (`a, (oargs[4]!)), (`x, x), (`v, val), (`R', R'), (`ha, ha), (`hv, hv), (`hR, hR), (`h, h)]))
            pure (some [h.mvarId!])
        | some ``Lprog.Op.store =>
          let w := (oargs[1]!).consumeMData
          let (x, ha) ← evalE a.R (oargs[2]!)
          let (v, hv) ← evalE a.R (oargs[3]!)
          if w.isConstOf ``Lprog.Width.b8 then
            let h ← newGoal g (a.goal (a.pc + 1) a.R (← mkAppM ``MachineState.setMem #[a.M, x, v]))
            g.assign (← appN ``Rv64mc.Tactic.step_sd (base ++ [(`a, (oargs[2]!)), (`e, (oargs[3]!)), (`x, x),
              (`v, v), (`ha, ha), (`hv, hv), (`h, h)]))
            pure (some [h.mvarId!])
          else
            let m' ← whnfCore (← unfoldDefinition (mkApp4 (mkConst ``Rv64mc.Tactic.storeMem) w a.M x v))
            let h ← newGoal g (a.goal (a.pc + 1) a.R m')
            g.assign (← appN ``Rv64mc.Tactic.step_storew (base ++ [(`w, w), (`a, (oargs[2]!)), (`e, (oargs[3]!)),
              (`x, x), (`v, v), (`ha, ha), (`hv, hv), (`h, h)]))
            pure (some [h.mvarId!])
        | some ``Lprog.Op.skip =>
          let h ← newGoal g (a.goal (a.pc + 1) a.R a.M)
          g.assign (← appN ``Rv64mc.Tactic.step_skip (base ++ [(`h, h)]))
          pure (some [h.mvarId!])
        | _ => pure none
      | some ``Lprog.LinstrR.Lcond =>
        let cnd := (args[2]!).consumeMData
        unless cnd.isAppOfArity ``Lprog.LOperand.cmp 4 do return none
        let some l ← evalNat (args[3]!) | return none
        let some j ← labelIdx? cfg.body l | return none
        let cargs := cnd.getAppArgs
        let opnd (o : Expr) : MetaM (Option Expr) := do
          let o := o.consumeMData
          if o.isAppOfArity ``Lprog.LOperand.reg 2 then return some (← readP a.R o.appArg!).1
          if o.isAppOfArity ``Lprog.LOperand.imm 2 then
            let some i ← getIntValue? o.appArg! | return none
            return some (mkLit (i % 2 ^ 64).toNat)
          return none
        let opndProof (o v : Expr) : MetaM Expr := do
          let lhs ← mkAppM ``Lprog.operandVal #[a.R, o]
          let rhs ← mkAppM ``Option.some #[v]
          if o.consumeMData.isAppOf ``Lprog.LOperand.imm then litEq lhs rhs else
            let r := o.consumeMData.appArg!
            let p0 ← appN ``Rv64mc.Tactic.opnd_reg [(`R, a.R), (`r, r)]
            mkEqTrans p0 (← mkCongrArg (← mkAppOptM ``Option.some #[word]) (← readP a.R r).2)
        let some x ← opnd (cargs[2]!) | return none
        let some y ← opnd (cargs[3]!) | return none
        let opS := (cargs[1]!)
        let .lit (.strVal opStr) := opS.consumeMData | return none
        let props : Option (Expr × Expr) ← match opStr with
          | "eq" => pure (some (← mkEq x y, mkNot (← mkEq x y)))
          | "ne" => pure (some (mkNot (← mkEq x y), ← mkEq x y))
          | "ltu" => pure (some (← mkAppM ``LT.lt #[x, y], ← mkAppM ``LE.le #[y, x]))
          | "geu" => pure (some (← mkAppM ``LE.le #[y, x], ← mkAppM ``LT.lt #[x, y]))
          | "lt" => do
            let s ← mkAppM ``BitVec.slt #[x, y]
            pure (some (← mkEq s (mkConst ``Bool.true), ← mkEq s (mkConst ``Bool.false)))
          | "ge" => do
            let s ← mkAppM ``BitVec.slt #[x, y]
            pure (some (← mkEq s (mkConst ``Bool.false), ← mkEq s (mkConst ``Bool.true)))
          | _ => pure none
        let some (pt, pn) := props | return none
        let gt ← newGoal g (← mkArrow pt (a.goal j a.R a.M))
        let gn ← newGoal g (← mkArrow pn (a.goal (a.pc + 1) a.R a.M))
        let tru := mkConst ``Bool.true
        g.assign (← appN ``Rv64mc.Tactic.step_cmp (base ++ [(`op, opS), (`a, (cargs[2]!)), (`b, (cargs[3]!)),
          (`l, (args[3]!)), (`j, mkNatLit j), (`x, x), (`y, y),
          (`hl, ← mkEqRefl (← mkAppM ``Option.some #[mkNatLit j])),
          (`ha, ← opndProof (cargs[2]!) x), (`hb, ← opndProof (cargs[3]!) y),
          (`hs, ← mkEqRefl tru), (`ht, gt), (`hn, gn)]))
        let (_, gt') ← gt.mvarId!.intro `hc
        let (_, gn') ← gn.mvarId!.intro `hc
        pure (some [← nameApart gt', ← nameApart gn'])
      | some ``Lprog.LinstrR.Lcall =>
        let ret := (args[2]!)
        let tgt := (args[3]!)
        let some f ← targetIdx tgt
          | trace[rv_sym] "at {a.pc}: the call's target names no single function"; return none
        let some (hcon, Pre, Post) ← specFor cfg f
          | trace[rv_sym] "at {a.pc}: no contract for function {f}"; return none
        let some hc ← calleeProof cfg a.R tgt f
          | trace[rv_sym] "at {a.pc}: the facts given do not show that the call reaches {f}"; return none
        let sp := mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x2)
        let R1 := mkApp5 (mkConst ``Lprog.updReg) (mkConst ``RiscvZkvm.Rv64.Reg)
          (mkConst ``RiscvZkvm.Rv64.instDecidableEqReg) a.R (mkConst ``RiscvZkvm.Rv64.Reg.x1) ret
        let hpre ← newGoal g (mkApp4 Pre ret sp R1 a.M).headBeta
        let kT ← withLocalDeclD `r' (← mkArrow (mkConst ``RiscvZkvm.Rv64.Reg) word) fun r' =>
          withLocalDeclD `m' (mkConst ``MachineState) fun m' => do
            mkForallFVars #[r', m'] (← mkArrow (mkAppN Post #[ret, sp, R1, a.M, r', m']).headBeta
              (a.goal (a.pc + 1) r' m'))
        let hk ← newGoal g kT
        g.assign (← appN ``Rv64mc.Tactic.step_call (base ++ [(`ret, ret), (`tgt, tgt), (`f, f), (`Pre, Pre),
          (`Post, Post), (`hcon, hcon), (`hc, hc), (`hpre, hpre), (`hk, hk)]))
        let side ← closeSide hpre.mvarId!
        let g' ← afterCall hk.mvarId! k
        pure (some (side ++ g'.toList))
      | some ``Lprog.LinstrR.Ltail =>
        let tgt := args[2]!
        let some f ← targetIdx tgt
          | trace[rv_sym] "at {a.pc}: the tail call's target names no single function"; return none
        let some (hcon, Pre, Post) ← specFor cfg f
          | trace[rv_sym] "at {a.pc}: no contract for function {f}"; return none
        let some hc ← calleeProof cfg a.R tgt f
          | trace[rv_sym] "at {a.pc}: the facts given do not show that the tail call reaches {f}"; return none
        let hsp ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x2)) a.top)
        let hpre ← newGoal g (mkApp4 Pre a.rv a.top a.R a.M).headBeta
        let kT ← withLocalDeclD `r' (← mkArrow (mkConst ``RiscvZkvm.Rv64.Reg) word) fun r' =>
          withLocalDeclD `m' (mkConst ``MachineState) fun m' => do
            mkForallFVars #[r', m'] (← mkArrow (mkAppN Post #[a.rv, a.top, a.R, a.M, r', m']).headBeta
              (mkAppN a.head (a.pre.push (mkApp3 a.stMk a.rest r' m'))))
        let hk ← newGoal g kT
        g.assign (← appN ``Rv64mc.Tactic.step_tail (base ++ [(`tgt, tgt), (`f, f), (`Pre, Pre), (`Post, Post),
          (`hcon, hcon), (`hc, hc), (`hsp, hsp), (`hpre, hpre),
          (`hk, hk)]))
        let side := (← closeSide hsp.mvarId!) ++ (← closeSide hpre.mvarId!)
        let g' ← afterCall hk.mvarId! k
        pure (some (side ++ g'.toList))
      | some ``Lprog.LinstrR.Lret =>
        let h ← newGoal g (mkAppN a.head (a.pre.push (mkApp3 a.stMk a.rest a.R a.M)))
        let hra ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x1)) a.rv)
        let hsp ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x2)) a.top)
        g.assign (← appN ``Rv64mc.Tactic.step_ret (base ++ [(`hra, hra), (`hsp, hsp), (`h, h)]))
        let side := (← closeSide hra.mvarId!) ++ (← closeSide hsp.mvarId!)
        pure (some (side ++ [h.mvarId!]))
      | _ => pure none
    match step with
    | none =>
      trace[rv_sym] "left at {a.pc}: no rule applies to {ins}"
      left := left.push g
    | some gs =>
      -- side goals (not a `SafeN` at a frame) go to `left` through `run`'s check, after the path's own
      steps := steps + 1
      -- the next instruction's suffix where the step falls through, found again after a jump
      let next ← gs.mapM fun g' => do
        let pc' ← g'.withContext do return (← parseAt (← g'.getType)).map (·.pc)
        return (g', seen, if pc' == some (a.pc + 1) then some hdNext else none)
      todo := next ++ todo
  trace[rv_sym] "{steps} instructions stepped, {left.size} goals left"
  return left.toList

/-! ## The tactics -/

/-- A fact given to the tactic, with its conjunctions and the fields of a structure of facts (a template's
    `Link.WF`) as facts of their own. -/
partial def expandFact (h : Expr) : MetaM (Array (Expr × Expr)) := do
  let ty := (← whnfR (← instantiateMVars (← inferType h))).consumeMData
  if ty.isAppOfArity ``And 2 then
    return (← expandFact (← mkAppM ``And.left #[h])) ++ (← expandFact (← mkAppM ``And.right #[h]))
  if let some n := ty.getAppFn.constName? then
    if isStructure (← getEnv) n && n != ``Eq then
      let mut out := #[]
      for fld in getStructureFields (← getEnv) n do
        out := out ++ (← expandFact (← mkProjection h fld))
      return out
  return #[(h, ty)]

/-- The configuration from the tactic's arguments. -/
def mkCfg (hp : Expr) (stops : List Nat) (facts specs : Array Expr) : MetaM Cfg := do
  let hpT := (← instantiateMVars (← inferType hp)).consumeMData
  unless hpT.isAppOfArity ``Eq 3 && hpT.appArg!.isAppOfArity ``Option.some 2 do
    throwError "rv_sym: {hp} is not `p[fn]? = some fd`"
  let fd := hpT.appArg!.appArg!
  let body ← bodyOf fd
  if body.isEmpty then throwError "rv_sym: the body of {fd} is empty"
  let α ← inferType (body[0]!)
  let mut suffixes := #[mkApp (mkConst ``List.nil [0]) α]
  for i in body.reverse do
    suffixes := suffixes.push (mkApp3 (mkConst ``List.cons [0]) α i suffixes.back!)
  suffixes := suffixes.reverse
  let hbody ← mkExpectedTypeHint (← mkEqRefl (suffixes[0]!)) (← mkEq (← mkAppM ``Lprog.Lfundef.body #[fd]) (suffixes[0]!))
  let facts ← facts.foldlM (init := #[]) fun acc h => return acc ++ (← expandFact h)
  let specs ← specs.mapM fun h => return (h, ← instantiateMVars (← inferType h))
  let mut heads := []
  for h : k in [0:body.size] do
    let i := body[k].consumeMData
    let l? := if i.isAppOfArity ``Lprog.LinstrR.Lgoto 3 then some i.appArg!
      else if i.isAppOfArity ``Lprog.LinstrR.Lcond 4 then some i.appArg! else none
    if let some l := l? then
      if let some l ← evalNat l then
        if let some j ← labelIdx? body l then
          if j ≤ k then heads := j :: heads
  return { hp, fd, body, suffixes, hbody, facts, specs, stops, heads }

syntax rvSymArgs := (" stop " "[" num,* "]")? (" with " "[" term,* "]")? (" using " "[" term,* "]")?

def elabArgs (hp : Syntax) (args : Syntax) : TacticM Cfg := do
  let stops := if args[0].isNone then [] else args[0][2].getSepArgs.toList.filterMap (·.isNatLit?)
  let facts ← if args[1].isNone then pure #[] else args[1][2].getSepArgs.mapM fun t => elabTerm t none
  let specs ← if args[2].isNone then pure #[] else args[2][2].getSepArgs.mapM fun t => elabTerm t none
  mkCfg (← elabTerm hp none) stops facts specs

/-- **`rv_sym hp stop [pcs] with [facts] using [contracts]`**: step the goal `SafeN … ⟨⟨fn, pc, …⟩ :: …⟩` through the
    body of the template `hp : p[fn]? = some fd` names. -/
syntax (name := rvSym) "rv_sym " term rvSymArgs : tactic

@[tactic rvSym] def evalRvSym : Tactic := fun stx => do
  let cfg ← elabArgs stx[1] stx[2]
  let g ← getMainGoal
  let left ← run cfg g
  replaceMainGoal left

/-- The precondition's facts as hypotheses `hpre_k`, and what they say of the entry's registers written into the
    register file. -/
def openContract (g : MVarId) : MetaM MVarId := do
  let g ← g.replaceTargetDefEq (← toContract (← instantiateMVars (← g.getType)))
  let (fvs, g) ← g.introN 10 [`G, `n, `Q, `ret, `top, `rest, `regs, `m, `hpre, `hk]
  g.withContext do
    let pre := mkFVar (fvs[8]!)
    let facts ← splitFact pre (← inferType pre)
    let (g, hs) ← addFacts g `hpre facts
    let g ← g.tryClear (fvs[8]!)
    absorbFacts g (hs.map mkFVar)

/-- **`rv_auto hp stop [pcs] with [facts] using [contracts]`**: a goal `rvIsa.Contract p c fn Pre Post` for the
    template `hp : p[fn]? = some fd`, stepped from the entry: the precondition split into hypotheses, every call
    through its contract, and what the postcondition says of the stack pointer, the saved registers and the memory
    above the frame closed. What is left is the postcondition's functional part, any callee precondition that is
    not closed by reduction or a hypothesis, and the goals at `stop`s and loop heads. -/
syntax (name := rvAuto) "rv_auto " term rvSymArgs : tactic

@[tactic rvAuto] def evalRvAuto : Tactic := fun stx => do
  let cfg ← elabArgs stx[1] stx[2]
  let g ← openContract (← getMainGoal)
  let left ← run cfg g
  replaceMainGoal left

/-- **`rv_intro h`**: the hypothesis `h` split into its conjuncts (`h_k`, its definitions unfolded), and what they say
    of the goal's register file written into it, as at a contract's entry: for a loop's invariant. -/
syntax (name := rvIntro) "rv_intro " ident : tactic

@[tactic rvIntro] def evalRvIntro : Tactic := fun stx => do
  let g ← getMainGoal
  let g ← g.withContext do
    let h ← getFVarId stx[1]
    let facts ← splitFact (mkFVar h) (← h.getType)
    let (g, hs) ← addFacts g (← h.getUserName) facts
    let g ← g.tryClear h
    absorbFacts g (hs.map mkFVar)
  replaceMainGoal [g]

/-- **`rv_close`**: on every goal, what `rv_auto` closes of a side goal: conjunctions split, definitions unfolded,
    equations by reduction or offsets, address bounds, memory a frame keeps, hypotheses. -/
syntax (name := rvClose) "rv_close" : tactic

@[tactic rvClose] def evalRvClose : Tactic := fun _ => do
  let gs ← getGoals
  let mut left := #[]
  for g in gs do
    if ← g.isAssigned then continue
    left := left ++ (← closeSide g)
  setGoals left.toList

/-- **`rv_sweep hp …`**, a measure of coverage and cost: `rv_auto`, and besides it the body stepped from each loop
    head with nothing known of the state (`∀ … regs m, SafeN … ⟨⟨fn, head, …⟩ :: …, regs, m⟩`), each a hypothesis of
    the goal whose proof the kernel checks with the rest. Every goal any run leaves is the tactic's. -/
syntax (name := rvSweep) "rv_sweep " term rvSymArgs : tactic

@[tactic rvSweep] def evalRvSweep : Tactic := fun stx => do
  let cfg ← elabArgs stx[1] stx[2]
  let g ← getMainGoal
  let gt := (← instantiateMVars (← g.getType)).consumeMData
  let gt ← toContract gt
  unless gt.isAppOfArity ``Lprog.Isa.Contract 7 do throwError "rv_sweep: the goal is not a contract"
  let ga := gt.getAppArgs
  let mut g := g
  let mut left : List MVarId := []
  for h in cfg.heads.eraseDups do
    let auxT ← g.withContext do
      let stTy := mkApp (mkConst ``Lprog.State) (ga[0]!)
      let pTy ← mkArrow stTy (mkSort 0)
      let restTy ← mkAppM ``List #[mkConst ``Lprog.Frame]
      let regsTy ← mkArrow (mkConst ``RiscvZkvm.Rv64.Reg) word
      withLocalDeclD `G pTy fun G =>
      withLocalDeclD `n (mkConst ``Nat) fun n =>
      withLocalDeclD `Q pTy fun Q =>
      withLocalDeclD `ret word fun ret =>
      withLocalDeclD `top word fun top =>
      withLocalDeclD `rest restTy fun rest =>
      withLocalDeclD `regs regsTy fun regs =>
      withLocalDeclD `m (mkConst ``MachineState) fun m => do
        let fr ← mkAppM ``Lprog.Frame.mk #[ga[4]!, mkNatLit h, ret, top]
        let st ← mkAppOptM ``Lprog.State.mk #[ga[0]!, ← mkAppM ``List.cons #[fr, rest], regs, m]
        let body := mkAppN (mkConst ``Lprog.Isa.SafeN) #[ga[0]!, ga[1]!, ga[2]!, ga[3]!, G, n, Q, st]
        mkForallFVars #[G, n, Q, ret, top, rest, regs, m] body
    let aux ← g.withContext do mkFreshExprSyntheticOpaqueMVar auxT
    let (_, ga') ← aux.mvarId!.introN 8
    left := left ++ (← run cfg ga')
    let g' ← g.assert (Name.mkSimple s!"head{h}") auxT aux
    let (_, g'') ← g'.intro1
    g := g''
  let g0 ← openContract g
  left := left ++ (← run cfg g0)
  replaceMainGoal left

end Rv64mc.Tactic.Sym
