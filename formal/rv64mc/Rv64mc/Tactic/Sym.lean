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

  It stops at a program counter in `stop`, at the target of a backward jump (a loop's head, for a loop lemma) unless
  `through` names it (`through *`: every one), where a path comes back to a program counter it has passed, at a
  call without a contract, and where the function returns, which `finish` closes by the contract's continuation,
  leaving the postcondition to `closeSide`.

  With `set_option rv_sym.heap true` (`heapOn`), comparisons of addresses that offsets do not decide go to `omega`
  over the context's facts about numbers (`arithProve`), `NEXT` is read through stores (`nextNorm`), frames take
  stores into what the function allocated and into `out`, and callees with an `out` (`Tactic/Heap.lean`), a
  representation predicate of an earlier memory is carried by its `<P>.keep` lemma (`transport`) or built in place
  field by field, and a branch on literals steps only the branch taken. Off, the goals left are those left before.

  ## Main results

  * `rv_sym hp stop [pcs] through [heads] with [facts] using [contracts]`: step a goal `SafeN … ⟨⟨fn, pc, …⟩ :: …⟩`
  * `rv_auto hp …`: a contract `rvIsa.Contract p c fn Pre Post`, from the entry
  * `rv_intro h`, `rv_close`: a loop invariant's facts into the register file; the side goals' closer
  * `rv_mem`: the goal's reads of registers, `NEXT` and memory resolved
-/

import Lean
import Rv64mc.Tactic.Steps
import Rv64mc.Tactic.Addr
import Rv64mc.Tactic.Frame
import Rv64mc.Tactic.Heap
import Rv64mc.Core.ReprLemmas
import Rv64mc.Core.ReprBytes

namespace Rv64mc.Tactic.Sym

open Lean Meta Elab Tactic
open RiscvZkvm.Rv64 Lprog Lprog.RiscV

initialize registerTraceClass `rv_sym

register_option rv_sym.heap : Bool := {
  defValue := false
  descr := "rv_sym: reason about the heap and `out` (by omega), NEXT through stores, literal branches"
}

/-- `rv_sym.heap`: comparisons of addresses by `omega`, `NEXT` read through stores, frames with stores into what the
    function allocated and into `out` and callees with an `out`, what such a callee keeps, branches on literals
    folded, literal forms in the facts given. Off, `rv_sym` leaves the goals it left before them. -/
def heapOn : MetaM Bool := return rv_sym.heap.get (← getOptions)

/-- The facts about numbers `omega` proved in this run of the tactic, by proposition: one reused where the local
    hypotheses it names are all in scope. -/
initialize arithCache : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}

register_option rv_sym.bind : Nat := {
  defValue := 0
  descr := "rv_sym: a callee's result deeper than this stays its own variable (0: every result is written in)"
}

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
  if e.isAppOf ``Rv64mc.Tactic.rf || e.isAppOf ``Lprog.updReg || e.isAppOf ``MachineState.setMem ||
      e.isAppOf ``MachineState.setByte then
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
  evalNat (← withTransparency .default (whnf e))

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

/-! ## Linear facts over the words' numbers, by `omega`

  Where offsets of one base do not decide a comparison of addresses (a slot against a block the function
  allocated, `sret` against the stack, a store's address against `NEXT`), `omega` does, from the context's facts
  about numbers (`arithFacts`: comparisons, words' comparisons and equations as their numbers', the bounds of a
  frame on `NEXT`, definitions such as `InRange`, `Owned`, `Live` unfolded, the environment's layout) that share an
  atom with the goal, and for each word `b + c` its number (`slot_eq` for a slot, `toNat_add_lit` else). -/

/-- Definitions that say nothing about numbers, or too much, never unfolded for `omega`. -/
def noArith : List Name := [``Lprog.Isa.Contract, ``Lprog.Isa.SafeN, ``Rv64mc.Holds, ``Rv64mc.Env.Static,
  ``Rv64mc.Env.MayWrite, ``Rv64mc.Env.Frame, ``Rv64mc.DataRef.Words, ``MachineState.getMem, ``Rv64mc.Env.next]

def isWordTy (T : Expr) : MetaM Bool := do
  let T ← whnfR T
  if T.isAppOfArity ``BitVec 1 then return (← evalNat T.appArg!) == some 64
  return false

/-- `e` with every constant of type `Nat` defined as a numeral replaced by it (a layout's sizes). -/
def litConsts (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if let .const n _ := x then
      if let some (.defnInfo _) := (← getEnv).find? n then
        if (← whnfR (← inferType x)).isConstOf ``Nat then
          if let some v ← natVal? x then return .done (mkNatLit v)
    -- a closed number other than arithmetic `omega` reads (`[].length`)
    if x.isApp && !x.hasFVar && !x.hasMVar && !x.hasLooseBVars then
      let some c := x.getAppFn.constName? | return .continue
      unless [``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``OfNat.ofNat,
          ``BitVec.toNat].contains c do
        if (← whnfR (← inferType x)).isConstOf ``Nat then
          if let some v ← natVal? x then return .done (mkNatLit v)
    return .continue)

/-- `ty` as a fact `omega` reads, up to unfolding: comparisons of numbers (of words as their numbers') under `∧`,
    `∨`, `¬`, `↔`. -/
partial def arithProp (ty : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  let ty := (← instantiateMVars ty).consumeMData.headBeta
  let n := ty.getAppNumArgs
  match ty.getAppFn.constName? with
  | some ``And | some ``Or | some ``Iff =>
    unless n == 2 do return none
    let some a ← arithProp ty.appFn!.appArg! fuel | return none
    let some b ← arithProp ty.appArg! fuel | return none
    return some (mkApp2 ty.appFn!.appFn! a b)
  | some ``Not =>
    unless n == 1 do return none
    let some a ← arithProp ty.appArg! fuel | return none
    return some (mkNot a)
  | some ``True | some ``False => return some ty
  | some ``LE.le | some ``LT.lt =>
    unless n == 4 do return none
    let T := ty.getArg! 0
    if (← whnfR T).isConstOf ``Nat then return some (← litConsts ty)
    unless ← isWordTy T do return none
    let x ← mkAppM ``BitVec.toNat #[ty.appFn!.appArg!]
    let y ← mkAppM ``BitVec.toNat #[ty.appArg!]
    return some (← mkAppM (if ty.isAppOf ``LE.le then ``LE.le else ``LT.lt) #[x, y])
  | some ``Eq | some ``Ne =>
    unless n == 3 do return none
    if (← whnfR (ty.getArg! 0)).isConstOf ``Nat then return some (← litConsts ty)
    return none
  | some c =>
    if noArith.contains c || fuel == 0 then return none
    let some ty' ← unfoldDefinition? ty | return none
    arithProp ty' (fuel - 1)
  | none => return none

/-- The facts about numbers a hypothesis `pf : ty` gives: its conjuncts', a frame's bounds on `NEXT`, a word
    equation's numbers. -/
partial def arithFacts (pf ty : Expr) (fuel : Nat := 8) : MetaM (Array (Expr × Expr)) := do
  let ty := (← instantiateMVars ty).consumeMData.headBeta
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    return (← arithFacts (mkApp3 (mkConst ``And.left) a b pf) a fuel) ++
      (← arithFacts (mkApp3 (mkConst ``And.right) a b pf) b fuel)
  if ty.isAppOfArity ``Rv64mc.Env.Frame 5 then
    let some ty' ← unfoldDefinition? ty | return #[]
    let ty' := ty'.headBeta
    unless ty'.isAppOfArity ``And 2 do return #[]
    let a := ty'.appFn!.appArg!
    let bc := ty'.appArg!
    unless bc.isAppOfArity ``And 2 do return #[]
    let b := bc.appFn!.appArg!
    let c := bc.appArg!
    return #[(mkApp3 (mkConst ``And.left) a bc pf, a),
      (mkApp3 (mkConst ``And.left) b c (mkApp3 (mkConst ``And.right) a bc pf), b)]
  if ty.isAppOfArity ``Eq 3 then
    if ← isWordTy (ty.getArg! 0) then
      let p ← mkAppM ``Rv64mc.Tactic.toNat_congr #[pf]
      return #[(p, ← inferType p)]
  if let some ty' ← arithProp ty fuel then return #[(← mkExpectedTypeHint pf ty', ty')]
  if let some c := ty.getAppFn.constName? then
    if !noArith.contains c && fuel > 0 then
      if let some ty' ← unfoldDefinition? ty then return ← arithFacts pf ty' (fuel - 1)
      -- a structure of facts (`VecAt`): its fields'
      if isStructure (← getEnv) c then
        let mut out := #[]
        for fld in getStructureFields (← getEnv) c do
          let some p ← (try some <$> mkProjection pf fld catch _ => pure none) | continue
          out := out ++ (← arithFacts p (← inferType p) (fuel - 1))
        return out
  return #[]

/-- The 64-bit words whose numbers `e` mentions. -/
partial def natAtoms (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  match e with
  | .app f a =>
    if e.isAppOfArity ``BitVec.toNat 2 && !a.hasLooseBVars then
      if (← evalNat e.appFn!.appArg!) == some 64 then
        return if acc.contains a then acc else acc.push a
    natAtoms a (← natAtoms f acc)
  | .mdata _ b => natAtoms b acc
  | _ => return acc

/-- The terms `(l.map f).length` of `e`. -/
partial def lengthMaps (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``List.length 2 && (e.appArg!).isAppOfArity ``List.map 4 && !e.hasLooseBVars then
    if acc.contains e then acc else acc.push e
  else match e with
    | .app f a => lengthMaps a (lengthMaps f acc)
    | .mdata _ b => lengthMaps b acc
    | _ => acc

/-- A register read through a register file the executor made (`normReads`), only where there is one. -/
def normRegs (pf ty : Expr) : MetaM (Expr × Expr) := do
  unless (ty.find? fun e => e.isAppOf ``Rv64mc.Tactic.rf || e.isAppOf ``Lprog.updReg).isSome do return (pf, ty)
  let (ty', p) ← normReads ty
  match p with
  | some p => return (← mkEqMP p pf, ty')
  | none => return (pf, ty')

/-- `pf : goal` as an auxiliary theorem, where it can be one. -/
def auxOr (goal pf : Expr) : MetaM Expr := do
  try mkAuxTheorem goal pf (zetaDelta := true)
  catch _ => pure pf

/-- `goal`, a proposition about numbers, by `omega` from `facts`; the proof is an auxiliary theorem. -/
def omegaOn (facts : Array Expr) (goal : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  -- `omega` may also run out of recursion depth or heartbeats: a failure like any other
  tryCatchRuntimeEx (do
    let g ← mkFreshExprSyntheticOpaqueMVar goal
    let some g' ← g.mvarId!.falseOrByContra | return none
    g'.withContext do
      let last := (← getLCtx).lastDecl
      let negated := if goal.consumeMData.isConstOf ``False then [] else
        match last with
        | some d => [d.toExpr]
        | none => []
      Lean.Elab.Tactic.Omega.omega (facts.toList ++ negated) g'
    let pf ← instantiateMVars g
    if pf.hasExprMVar then
      saved.restore
      return none
    return some (← auxOr goal pf))
    fun _ => do
      saved.restore
      return none

mutual

/-- `env.next X = env.next B` for the memory `B` that `X` stores into, through stores apart from `NEXT`. -/
partial def nextNorm (env X : Expr) : MetaM (Expr × Option Expr) := do
  let X := X.consumeMData
  if X.isAppOfArity ``MachineState.setByte 3 then
    let N := X.appFn!.appFn!.appArg!
    let a := X.appFn!.appArg!
    let some hne ← neNext env (← mkAppM ``alignToDword #[a]) | return (X, none)
    let p1 ← mkAppOptM ``Rv64mc.next_setByte #[env, N, a, X.appArg!, hne]
    let (B, p2) ← nextNorm env N
    return (B, some (← transOpt p1 p2))
  unless X.isAppOfArity ``MachineState.setMem 3 do return (X, none)
  let N := X.appFn!.appFn!.appArg!
  let a := X.appFn!.appArg!
  let v := X.appArg!
  let some hne ← neNext env a
    | trace[rv_sym] "nextNorm stops at {a}"; return (X, none)
  let p1 ← appN ``Rv64mc.Tactic.next_setMem [(`env, env), (`N, N), (`a, a), (`v, v), (`h, hne)]
  let (B, p2) ← nextNorm env N
  return (B, some (← transOpt p1 p2))

/-- `a ≠ env.nextAddr`: a slot of the stack, or by `omega`. -/
partial def neNext (env a : Expr) : MetaM (Option Expr) := do
  if let some (hlo, _, _) ← slotFacts a then
    return some (← appN ``Rv64mc.Tactic.next_ne_of_stack [(`env, env), (`a, a), (`h, hlo)])
  arithProve (← mkAppM ``Ne #[a, ← mkAppM ``Rv64mc.Env.nextAddr #[env]]) true

/-- **A proposition about numbers or words' numbers by `omega`**, from the facts of the context that share an atom
    with it, each word `b + c` among their atoms given its number. `nested`: no `NEXT` read through stores. -/
partial def arithProve (goal : Expr) (nested : Bool := false) : MetaM (Option Expr) := do
  unless ← heapOn do return none
  -- gathering the facts unfolds definitions and evaluates closed numbers: out of recursion depth or heartbeats there,
  -- no proof, as `omega` failing
  let goal ← instantiateMVars goal
  if let some p := (← arithCache.get).get? goal then
    let lctx ← getLCtx
    if (collectFVars {} p).fvarIds.all lctx.contains then return some p
  let saved ← saveState
  let r ← tryCatchRuntimeEx (arithProveCore goal nested) fun _ => do
    saved.restore
    return none
  if let some p := r then arithCache.modify (·.insert goal p)
  return r

partial def arithProveCore (goal : Expr) (nested : Bool) : MetaM (Option Expr) := do
  let goal := (← instantiateMVars goal).consumeMData
  if goal.hasExprMVar then return none
  if goal.isAppOfArity ``Ne 3 then
    if ← isWordTy (goal.getArg! 0) then
      let g' ← mkAppM ``Ne #[← mkAppM ``BitVec.toNat #[goal.appFn!.appArg!], ← mkAppM ``BitVec.toNat #[goal.appArg!]]
      let some p ← arithProveCore g' nested | return none
      return some (← mkAppM ``Rv64mc.Tactic.ne_of_toNat #[p])
  if goal.isAppOfArity ``Eq 3 then
    if ← isWordTy (goal.getArg! 0) then
      let g' ← mkEq (← mkAppM ``BitVec.toNat #[goal.appFn!.appArg!]) (← mkAppM ``BitVec.toNat #[goal.appArg!])
      let some p ← arithProveCore g' nested | return none
      return some (← mkAppM ``BitVec.eq_of_toNat_eq #[p])
  let some g1 ← arithProp goal | return none
  let hasRegs := (g1.find? fun e => e.isAppOf ``Rv64mc.Tactic.rf || e.isAppOf ``Lprog.updReg).isSome
  let (g2, pe) ← if hasRegs then normReads g1 else pure (g1, none)
  let mut facts : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.consumeMData.isConstOf ``Rv64mc.Env then
      let p ← mkAppM ``Rv64mc.Env.layout #[d.toExpr]
      facts := facts ++ (← arithFacts p (← inferType p))
      continue
    unless ← isProp ty do continue
    for (p, t) in ← arithFacts d.toExpr ty do
      facts := facts.push (← normRegs p t)
  -- each word's number (`extra`, by the word), and its key: a base, `NEXT` of the memory stored into
  let mut extra : Array (Expr × Expr) := #[]
  let mut canon : Array (Expr × Expr) := #[]
  let mut seen : Array Expr := #[]
  let mut todo := (← natAtoms g2 #[]).toList
  for (_, t) in facts do
    todo := todo ++ (← natAtoms t #[]).toList
  while !todo.isEmpty do
    let w := todo.head!
    todo := todo.tail!
    if seen.contains w then continue
    seen := seen.push w
    extra := extra.push (w, ← mkAppM ``BitVec.isLt #[w])
    if w.isAppOfArity ``alignToDword 1 then
      extra := extra.push (w, ← mkAppM ``Rv64mc.toNat_alignToDword' #[w.appArg!])
      todo := w.appArg! :: todo
      continue
    let (bw, cw) ← affine w
    let some b := bw
      | extra := extra.push (w, ← mkDecideProof (← mkEq (← mkAppM ``BitVec.toNat #[w]) (mkNatLit cw)))
        continue
    if cw != 0 then
      let c := w.appArg!
      let slot ← match ← ownStack with
        | some (h, S, top, need, nv) =>
          let k := 2 ^ 64 - cw
          if b == top && 0 < k && k ≤ nv then
            pure (some (← appN ``Rv64mc.Tactic.slot_eq [(`S, S), (`need, need), (`k, mkNatLit k), (`t, top),
              (`c, c), (`h, h), (`hc, ← mkEqRefl (mkConst ``Bool.true))]))
          else pure none
        | none => pure none
      match slot with
      | some p => extra := extra.push (w, p)
      | none =>
        if cw < 2 ^ 63 then
          let hc ← mkDecideProof (← mkEq (← mkAppM ``BitVec.toNat #[c]) (mkNatLit cw))
          extra := extra.push (w, ← appN ``Rv64mc.Tactic.toNat_add_lit [(`b, b), (`c, c), (`n, mkNatLit cw), (`h, hc)])
        else
          let k := 2 ^ 64 - cw
          let hc ← mkDecideProof (← mkEq (← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[c], mkNatLit k])
            (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]))
          extra := extra.push (w, ← appN ``Rv64mc.Tactic.toNat_add_negk [(`b, b), (`c, c), (`k, mkNatLit k), (`h, hc)])
      canon := canon.push (w, b)
      todo := b :: todo
    else if !nested && w.isAppOfArity ``Rv64mc.Env.next 2 then
      let env := w.appFn!.appArg!
      let (B, p?) ← nextNorm env w.appArg!
      if let some p := p? then
        extra := extra.push (w, ← mkAppM ``Rv64mc.Tactic.toNat_congr #[p])
        let nb ← mkAppM ``Rv64mc.Env.next #[env, B]
        canon := canon.push (w, nb)
        todo := nb :: todo
  let key (w : Expr) : Expr := ((canon.find? (·.1 == w)).map (·.2)).getD w
  let keysOf (t : Expr) : MetaM (Array Expr) := do
    let mut ks := (← natAtoms t #[]).map key
    for fv in (collectFVars {} t).fvarIds do
      if (← whnfR (← fv.getType)).isConstOf ``Nat then ks := ks.push (mkFVar fv)
    return ks
  -- the facts that share a key with the goal, closed under sharing
  let mut keys ← keysOf g2
  let factKeys ← facts.mapM fun (_, t) => keysOf t
  -- a goal without atoms (`False`): every fact
  let mut used := facts.map fun _ => keys.isEmpty
  let mut changed := true
  while changed do
    changed := false
    for i in [0:facts.size] do
      if used[i]! then continue
      let ks := factKeys[i]!
      if ks.any keys.contains then
        used := used.set! i true
        changed := true
        for k in ks do
          unless keys.contains k do keys := keys.push k
  let mut chosen : Array Expr := #[]
  for i in [0:facts.size] do
    if used[i]! then chosen := chosen.push facts[i]!.1
  for (w, p) in extra do
    if keys.isEmpty || keys.contains (key w) || keys.contains w then chosen := chosen.push p
  -- `(l.map f).length = l.length`
  let mut lens : Array Expr := #[]
  for t in #[g2] ++ facts.map (·.2) do
    lens := lengthMaps t lens
  for e in lens do
    let mp := e.appArg!
    chosen := chosen.push (← mkAppOptM ``List.length_map #[none, none, some mp.appArg!, some mp.appFn!.appArg!])
  let some p ← omegaOn chosen g2 | return none
  let p ← match pe with
    | some e => mkEqMPR e p
    | none => pure p
  return some (← mkExpectedTypeHint p goal)

end

/-- `NEXT` read through stores apart from it, as a simproc. -/
def nextStep (e : Expr) : SimpM Simp.Step := do
  if e.isAppOfArity ``Rv64mc.Env.next 2 && (e.appArg!.consumeMData.isAppOfArity ``MachineState.setMem 3 ||
      e.appArg!.consumeMData.isAppOfArity ``MachineState.setByte 3) then
    let (B, p?) ← withTransparency .default (nextNorm e.appFn!.appArg! e.appArg!)
    if let some p := p? then
      return .done { expr := mkApp2 e.appFn!.appFn! e.appFn!.appArg! B, proof? := some p }
  return .continue

/-- `ty` with `NEXT` read through the stores apart from it (`nextNorm`), and a proof of `ty = ty'` where it changed. -/
def nextTy (ty : Expr) : MetaM (Expr × Option Expr) := do
  let ty ← instantiateMVars ty
  let has := ty.find? fun e => e.isAppOfArity ``Rv64mc.Env.next 2 &&
    (e.appArg!.consumeMData.isAppOf ``MachineState.setMem || e.appArg!.consumeMData.isAppOf ``MachineState.setByte)
  if has.isNone then return (ty, none)
  let ctx ← Simp.mkContext (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Simp.main ty ctx (methods := { pre := nextStep })
  return (r.expr, r.proof?)

/-- A fact `pf : ty` with `NEXT` read through stores (`nextTy`). -/
def normNext (pf ty : Expr) : MetaM (Expr × Expr) := do
  let (ty', p) ← nextTy ty
  match p with
  | some p => return (← mkEqMP p pf, ty')
  | none => return (pf, ty)



/-- `InRange a n (a + j)` for a literal `j < n`, from a hypothesis `a.toNat + n < 2^64` (`inRange_add`), no `omega`. -/
def inRangeFast (ty : Expr) : MetaM (Option Expr) := do
  let ty := (← instantiateMVars ty).consumeMData
  unless ty.isAppOfArity ``Rv64mc.InRange 3 do return none
  let a := ty.getArg! 0
  let n := ty.getArg! 1
  let (bb, j) ← affine (ty.getArg! 2)
  unless bb == some a && j != 0 && j < 2 ^ 32 do return none
  let some nv ← natVal? n | return none
  unless j < nv do return none
  let some hw ← hypOf (← mkAppM ``LT.lt #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[a], n],
    ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]]) | return none
  let hj ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit j, n])
  let some p ← observing? (mkAppM ``Rv64mc.inRange_add #[hj, hw]) | return none
  return some (← mkExpectedTypeHint p ty)

/-- `a ≠ b` from a hypothesis `∀ xs, P₁ → … → l ≠ r` whose conclusion matches (either way round), its premises by
    `omega`: a precondition's apartness of two regions (`∀ b, InRange q n b → ∀ k < 25, alignToDword b ≠ s + 8 k`). An
    offset `s + 8 k` of the hypothesis matches a literal offset of the goal. -/
def neByHyp (a b : Expr) : MetaM (Option Expr) := do
  unless ← heapOn do return none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    unless ty.isForall do continue
    let saved ← saveState
    let r ← tryCatchRuntimeEx (try
        let (xs, _, concl) ← forallMetaTelescope ty
        let concl := concl.consumeMData
        unless concl.isAppOfArity ``Ne 3 do throwError "no"
        let l := concl.appFn!.appArg!
        let rr := concl.appArg!
        -- an offset `s + BitVec.ofNat 64 (8 * ?k)` against a literal offset: `?k` from the literal
        let offK (pat t : Expr) : MetaM Unit := do
          unless pat.isAppOfArity ``HAdd.hAdd 6 do return
          let off := pat.appArg!
          unless off.isAppOfArity ``BitVec.ofNat 2 do return
          let n := off.appArg!
          let k ← if n.isApp && n.appFn!.isApp then natVal? n.appFn!.appArg! else pure none
          unless n.isAppOfArity ``HMul.hMul 6 && k == some 8 do return
          let km := n.appArg!
          unless km.isMVar do return
          let (_, c) ← affine t
          if c % 8 == 0 then km.mvarId!.assign (mkNatLit (c / 8))
        let mut sym := false
        let mut ok := false
        let mut zero := false
        for (x, y, sw) in [(a, b, false), (b, a, true)] do
          let s1 ← saveState
          offK rr y
          if (← withReducible (isDefEq l x)) && (← withReducible (isDefEq rr y)) then
            ok := true; sym := sw; break
          s1.restore
          -- `y` without an offset against `s + 8 k`: `k` zero
          if rr.isAppOfArity ``HAdd.hAdd 6 && (← affine y).2 == 0 then
            let y0 ← mkAdd y (mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit 64)
              (← mkAppM ``HMul.hMul #[mkNatLit 8, mkNatLit 0]))
            if (← withReducible (isDefEq l x)) && (← withReducible (isDefEq rr y0)) then
              ok := true; sym := sw; zero := true; break
            s1.restore
        unless ok do throwError "no"
        for x in xs do
          if ← x.mvarId!.isAssigned then continue
          let xt ← instantiateMVars (← inferType x)
          unless ← isProp xt do throwError "no"
          let some p ← (do
              if !xt.hasFVar && !xt.hasMVar then
                if let some true ← observing? (do
                    return (← withTransparency .default (whnf (← mkDecide xt))).isConstOf ``Bool.true) then
                  return some (← mkDecideProof xt)
              if let some p ← inRangeFast xt then return some p
              arithProve xt) | throwError "no"
          x.mvarId!.assign p
        let pf ← instantiateMVars (mkAppN d.toExpr xs)
        if pf.hasExprMVar then throwError "no"
        let pf ← if zero then mkAppM ``Rv64mc.Tactic.ne_add0 #[pf] else pure pf
        if sym then pure (some (← mkAppM ``Ne.symm #[pf])) else pure (some pf)
      catch _ => pure none) fun _ => pure none
    match r with
    | some pf => return some pf
    | none => saved.restore
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
  if let some p ← neByHyp a b then return some p
  arithProve (← mkAppM ``Ne #[a, b])

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

/-- A hypothesis `∀ a, P₁ a → … → Pₖ a → M.getMem a = N.getMem a` (what a callee's frame keeps, `keep<k>_j`) whose
    premises hold at `x`, by offsets (`leProof`) or by `omega` (`arithProve`) away from the function's own stack:
    `M.getMem x = N.getMem x`, and `N`. -/
def keepAt (M x : Expr) : MetaM (Option (Expr × Expr)) := do
  let (bx, _) ← affine x
  let own := match ← ownStack with
    | some (_, _, top, _, _) => bx == some top
    | none => false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    let .forallE _ dom body _ := ty | continue
    unless ← isWordTy dom do continue
    let mut t := body.instantiate1 x
    let mut prems := #[]
    while t.isForall do
      let .forallE _ P b _ := t | break
      if b.hasLooseBVars then break
      prems := prems.push P
      t := b
    let concl := t.consumeMData
    unless concl.isAppOfArity ``Eq 3 && !prems.isEmpty do continue
    let lhs := concl.appFn!.appArg!
    let rhs := concl.appArg!
    unless lhs.isAppOfArity ``MachineState.getMem 2 && rhs.isAppOfArity ``MachineState.getMem 2 do continue
    unless lhs.appFn!.appArg! == M do continue
    let mut pfs := #[]
    for P in prems do
      let P := (← instantiateMVars P).consumeMData
      let le := P.isAppOfArity ``LE.le 4
      let mut p? ← if le then leProof P.appFn!.appArg! P.appArg! else pure none
      if p?.isNone && (!own || !le) then p? ← arithProve P
      let some p := p? | break
      pfs := pfs.push p
    unless pfs.size == prems.size do continue
    return some (mkAppN d.toExpr (#[x] ++ pfs), rhs.appFn!.appArg!)
  return none

/-- `y ≠ alignToDword x` for a slot `y` of the function's stack and `x = a + j` in a region off it: a hypothesis
    `a + n ≤ NEXT ∨ t ≤ a` (an `Owned`'s first part, or an `Owned` itself) with `t` the stack top, `a + n < 2^64`,
    `j < n`, the stack top 16-aligned (`ne_slot_of_region`), no `omega`. -/
def regionNeSlot (y x hlo hhi : Expr) (dword : Bool := false) : MetaM (Option Expr) := do
  let (bx, j) ← affine x
  let some a := bx | return none
  unless j != 0 && j < 2 ^ 32 do return none
  let some (_, _, top, _) ← rawStack | return none
  if a == top then return none
  let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
  let some h16 ← hypOf (← mkEq (← mkAppM ``HMod.hMod #[← num top, mkNatLit 16]) (mkNatLit 0)) | return none
  let _ := h16
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let mut ty := (← instantiateMVars d.type).consumeMData
    -- `a + n ≤ (env.next m).toNat ∨ t.toNat ≤ a.toNat`, or `env.Owned m t a n`
    let mut ho := d.toExpr
    let mut hw? : Option Expr := none
    if ty.isAppOfArity ``Rv64mc.Env.Owned 5 then
      if let some ty' ← unfoldDefinition? ty then
        let ty' := ty'.headBeta
        if ty'.isAppOfArity ``And 2 then
          ho := mkApp3 (mkConst ``And.left) ty'.appFn!.appArg! ty'.appArg! d.toExpr
          hw? := some (mkApp3 (mkConst ``And.right) ty'.appFn!.appArg! ty'.appArg! d.toExpr)
          ty := ty'.appFn!.appArg!
    unless ty.isAppOfArity ``Or 2 do continue
    let l := ty.appFn!.appArg!
    let r := ty.appArg!
    unless l.isAppOfArity ``LE.le 4 && r.isAppOfArity ``LE.le 4 do continue
    let la := l.appFn!.appArg!
    unless la.isAppOfArity ``HAdd.hAdd 6 do continue
    let la1 := la.appFn!.appArg!
    unless la1.isAppOfArity ``BitVec.toNat 2 && la1.appArg! == a && r.appArg!.isAppOfArity ``BitVec.toNat 2 &&
      r.appArg!.appArg! == a do continue
    let n := la.appArg!
    let nx := l.appArg!
    unless nx.isAppOfArity ``BitVec.toNat 2 && nx.appArg!.isAppOfArity ``Rv64mc.Env.next 2 do continue
    let env := nx.appArg!.appFn!.appArg!
    let t := r.appFn!.appArg!.appArg!
    let some hnx ← hypOf (← mkAppM ``LE.le #[nx, ← num (← mkAppM ``Rv64mc.Env.heapEnd #[env])]) | continue
    let ht ← if t == top then mkEqRefl (← num top) else do
      let some h ← hypOf (← mkEq t top) | continue
      mkAppM ``Rv64mc.Tactic.toNat_congr #[h]
    let some hw ← (match hw? with
      | some h => pure (some h)
      | none => do hypOf (← mkAppM ``LT.lt #[← mkAppM ``HAdd.hAdd #[← num a, n],
          ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]])) | continue
    let jn ← mkAppM ``LT.lt #[mkNatLit j, n]
    let ok ← observing? do
      let r ← withTransparency .default (whnf (← mkDecide jn))
      return r.isConstOf ``Bool.true
    unless ok == some true do continue
    let hj ← mkDecideProof jn
    if dword then
      let some p ← observing? (mkAppM ``Rv64mc.ne_slot_of_region' #[ho, hnx, ht, hj, hw, hlo, hhi]) | continue
      return some (← mkExpectedTypeHint p (← mkAppM ``Ne #[y, x]))
    let some p ← observing? (mkAppM ``Rv64mc.ne_slot_of_region #[ho, hnx, ht, h16, hj, hw, hlo, hhi]) | continue
    return some (← mkExpectedTypeHint p (← mkAppM ``Ne #[y, ← mkAppM ``alignToDword #[x]]))
  return none

/-- A slot `y` of the function's stack: `S ≤ y.toNat` and `y.toNat < top.toNat`, from the stack bound, or once by
    `omega` (cached) where `need` is a parameter. -/
def slotBounds (y : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some (hlo, hhi, _) ← slotFacts y then return some (hlo, hhi)
  let some (_, S, top, _) ← rawStack | return none
  unless (← affine y).1 == some top do return none
  let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
  let some hlo ← arithProve (← mkAppM ``LE.le #[S, ← num y]) | return none
  let some hhi ← arithProve (← mkAppM ``LT.lt #[← num y, ← num top]) | return none
  return some (hlo, hhi)

/-- The doubleword `M` holds at `x`, read through its stores and its callees' frames, and a proof of
    `M.getMem x = v` where it is not `M.getMem x` itself. -/
partial def readMem (M x : Expr) (off : Option (Option Expr) := none) : MetaM (Expr × Option Expr) := do
  let M := M.consumeMData
  if M.isAppOfArity ``MachineState.setMem 3 then
    let N := M.appFn!.appFn!.appArg!
    let y := M.appFn!.appArg!
    let w := M.appArg!
    let (bx, cx) ← affine x
    let (by_, cy) ← affine y
    if x == y || (bx == by_ && cx == cy) then
      return (w, some (← mkAppOptM ``MachineState.getMem_setMem_eq #[N, y, w]))
    -- a slot against a doubleword of a region off the stack (`ne_slot_of_region'`), either way round
    if ← heapOn then
      if let some (hlo, hhi) ← slotBounds y then
        if let some hne ← regionNeSlot y x hlo hhi (dword := true) then
          let p1 ← mkAppOptM ``MachineState.getMem_setMem_ne #[N, y, x, w, ← mkAppM ``Ne.symm #[hne]]
          let (v, p2) ← readMem N x off
          return (v, some (← transOpt p1 p2))
      else if let some (hlo, hhi) ← slotBounds x then
        if let some hne ← regionNeSlot x y hlo hhi (dword := true) then
          let p1 ← mkAppOptM ``MachineState.getMem_setMem_ne #[N, y, x, w, hne]
          let (v, p2) ← readMem N x off
          return (v, some (← transOpt p1 p2))
    -- a store into the stack, `x` off it: shown once for the whole run of stores (`ne_of_off_stack`)
    if ← heapOn then
      if let some (hlo, hhi, _) ← slotFacts y then
        let own ← match ← ownStack with
          | some (_, _, top, _, _) => pure (bx == some top)
          | none => pure true
        unless own do
          let off ← match off with
            | some o => pure o
            | none => do
              let some (_, S, top, _, _) ← ownStack | pure none
              arithProve (← mkAppM ``Or #[← mkAppM ``LT.lt #[← mkAppM ``BitVec.toNat #[x], S],
                ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[top], ← mkAppM ``BitVec.toNat #[x]]])
          if let some hoff := off then
            let hne ← mkAppM ``Rv64mc.Tactic.ne_of_off_stack #[hoff, hlo, hhi]
            let p1 ← mkAppOptM ``MachineState.getMem_setMem_ne #[N, y, x, w, hne]
            let (v, p2) ← readMem N x (some off)
            return (v, some (← transOpt p1 p2))
    if let some hne ← neProof x y then
      let p1 ← mkAppOptM ``MachineState.getMem_setMem_ne #[N, y, x, w, hne]
      let (v, p2) ← readMem N x off
      return (v, some (← transOpt p1 p2))
    return (← mkAppM ``MachineState.getMem #[M, x], none)
  if M.isAppOfArity ``MachineState.setByte 3 then
    let N := M.appFn!.appFn!.appArg!
    let y := M.appFn!.appArg!
    let c := M.appArg!
    let ay ← mkAppM ``alignToDword #[y]
    if let some hne ← neProof x ay then
      let p1 ← mkAppOptM ``Rv64mc.getMem_setByte_ne #[N, y, x, c, hne]
      let (v, p2) ← readMem N x
      return (v, some (← transOpt p1 p2))
    if let some heq ← arithProve (← mkEq ay x) then
      let p1 ← mkAppOptM ``Rv64mc.getMem_setByte_eq #[N, y, x, c, heq]
      let (v, p2) ← readMem N x
      let off ← mkAppM ``byteOffset #[y]
      let p2' ← match p2 with
        | some p => some <$> mkCongrArg (← lam word fun u => mkAppM ``replaceByte #[u, off, c]) p
        | none => pure none
      return (← mkAppM ``replaceByte #[v, off, c], some (← transOpt p1 p2'))
    return (← mkAppM ``MachineState.getMem #[M, x], none)
  if let some (p1, N) ← keepAt M x then
    let (v, p2) ← readMem N x
    return (v, some (← transOpt p1 p2))
  return (← mkAppM ``MachineState.getMem #[M, x], none)

/-- The byte `M` holds at `x`, read through doubleword stores apart from its doubleword, byte stores to other bytes
    and callees' frames that keep its doubleword, and a proof of `M.getByte x = v` where it is not `M.getByte x`. -/
partial def readByte (M x : Expr) : MetaM (Expr × Option Expr) := do
  let M := M.consumeMData
  if M.isAppOfArity ``MachineState.setMem 3 then
    let N := M.appFn!.appFn!.appArg!
    let y := M.appFn!.appArg!
    let w := M.appArg!
    let ax ← mkAppM ``alignToDword #[x]
    let fast ← match ← slotBounds y with
      | some (hlo, hhi) => regionNeSlot y x hlo hhi
      | none => pure none
    if let some hne ← (match fast with | some p => pure (some p) | none => neProof y ax) then
      let p1 ← mkAppOptM ``Rv64mc.getByte_setMem_ne #[N, x, y, w, hne]
      let (v, p2) ← readByte N x
      return (v, some (← transOpt p1 p2))
    return (← mkAppM ``MachineState.getByte #[M, x], none)
  if M.isAppOfArity ``MachineState.setByte 3 then
    let N := M.appFn!.appFn!.appArg!
    let y := M.appFn!.appArg!
    let c := M.appArg!
    let (bx, cx) ← affine x
    let (by_, cy) ← affine y
    if x == y || (bx == by_ && cx == cy) then
      return (c, some (← mkAppOptM ``Rv64mc.getByte_setByte_eq #[N, y, c]))
    if let some hne ← neProof x y then
      let p1 ← mkAppOptM ``Rv64mc.getByte_setByte_ne #[N, y, x, c, hne]
      let (v, p2) ← readByte N x
      return (v, some (← transOpt p1 p2))
    return (← mkAppM ``MachineState.getByte #[M, x], none)
  if let some (p1, N) ← keepAt M (← mkAppM ``alignToDword #[x]) then
    let p1 ← mkAppOptM ``Rv64mc.getByte_congr #[N, M, x, p1]
    let (v, p2) ← readByte N x
    return (v, some (← transOpt p1 p2))
  return (← mkAppM ``MachineState.getByte #[M, x], none)

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
def absorbFacts (g : MVarId) (facts : Array Expr) (bind : Nat := 0) : MetaM MVarId := g.withContext do
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
    -- a deep value stays the callee's register, its equation a hypothesis (`rv_sym.bind`)
    if bind != 0 && k != 2 && v.approxDepth.toNat > bind then continue
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

/-- `env.MayWrite top out m0 X a` for a word `a` of a callee's `out` (`ha`, in the context): in the stack below
    `top`, allocated since `m0`, or in `out`, by `omega`. -/
def mayWrite (env top out m0 X a : Expr) : MetaM (Option Expr) := do
  let args := [(`env, env), (`top, top), (`out, out), (`m, m0), (`X, X), (`a, a)]
  let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
  let stk ← mkAppM ``And #[← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.stackLimit #[env]), ← num a],
    ← mkAppM ``LT.lt #[← num a, ← num top]]
  if let some h ← arithProve stk then return some (← appN ``Rv64mc.Tactic.mw_stack (args ++ [(`h, h)]))
  let frs ← mkAppM ``And #[← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.next #[env, m0]), ← num a],
    ← mkAppM ``LT.lt #[← num a, ← num (← mkAppM ``Rv64mc.Env.next #[env, X])]]
  if let some h ← arithProve frs then return some (← appN ``Rv64mc.Tactic.mw_fresh (args ++ [(`h, h)]))
  unless ← isF out do
    if let some h ← arithProve (mkApp out a).headBeta then
      return some (← appN ``Rv64mc.Tactic.mw_out (args ++ [(`h, h)]))
  return none

/-- `env.Frame top out m0 X`, for `X` the memory the function made from `m0`: its stores into its stack, into what
    it allocated and into `out`, and its callees' frames (`Env.Frame … N X` in the context), each callee's `out`
    among what the function may write (`mayWrite`). -/
partial def frameWalk (env top out m0 X : Expr) : MetaM (Option Expr) := do
  let X := X.consumeMData
  let base := [(`env, env), (`top, top), (`out, out), (`m, m0)]
  if X == m0 then
    let nx ← mkAppM ``Rv64mc.Env.next #[env, m0]
    let hnxT ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[nx], ← mkAppM ``BitVec.toNat #[← mkAppM ``Rv64mc.Env.heapEnd #[env]]]
    let some hnx ← hypOf hnxT | return none
    return some (← appN ``Rv64mc.Env.Frame.refl (base ++ [(`h, hnx)]))
  if X.isAppOfArity ``MachineState.setMem 3 then
    let N := X.appFn!.appFn!.appArg!
    let a := X.appFn!.appArg!
    let v := X.appArg!
    let some h1 ← frameWalk env top out m0 N | return none
    let st := base ++ [(`a, a), (`v, v), (`N, N), (`h1, h1)]
    if let some (hlo, hhi, _) ← slotFacts a then
      return some (← appN ``Rv64mc.Tactic.frame_slot (st ++ [(`hlo, hlo), (`hhi, hhi)]))
    unless ← isF out do
      if let some hb ← arithProve (mkApp out a).headBeta then
        if let some hn ← neNext env a then
          return some (← appN ``Rv64mc.Tactic.frame_out (st ++ [(`hb, hb), (`hn, hn)]))
    let (B, hn?) ← nextNorm env N
    let hn ← match hn? with
      | some p => pure p
      | none => mkEqRefl (← mkAppM ``Rv64mc.Env.next #[env, N])
    let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
    let some hlo ← arithProve (← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.next #[env, m0]), ← num a])
      | return none
    let some hhi ← arithProve (← mkAppM ``LT.lt #[← num a, ← num (← mkAppM ``Rv64mc.Env.next #[env, B])]) | return none
    return some (← appN ``Rv64mc.Tactic.frame_fresh (st ++ [(`B, B), (`hn, hn), (`hlo, hlo), (`hhi, hhi)]))
  if X.isAppOfArity ``MachineState.setByte 3 then
    -- a byte store, into the doubleword at its aligned address
    let N := X.appFn!.appFn!.appArg!
    let a := X.appFn!.appArg!
    let c := X.appArg!
    let some h1 ← frameWalk env top out m0 N | return none
    let ay ← mkAppM ``alignToDword #[a]
    let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
    let st := base ++ [(`a, a), (`c, c), (`N, N), (`h1, h1)]
    if let some hlo ← arithProve (← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.stackLimit #[env]), ← num ay]) then
      if let some hhi ← arithProve (← mkAppM ``LT.lt #[← num ay, ← num top]) then
        return some (← appN ``Rv64mc.frame_byte (st ++ [(`hlo, hlo), (`hhi, hhi)]))
    unless ← isF out do
      if let some hb ← arithProve (mkApp out ay).headBeta then
        if let some hn ← neNext env ay then
          return some (← appN ``Rv64mc.frame_byte_out (st ++ [(`hb, hb), (`hn, hn)]))
    let (B, hn?) ← nextNorm env N
    let hn ← match hn? with
      | some p => pure p
      | none => mkEqRefl (← mkAppM ``Rv64mc.Env.next #[env, N])
    let some hlo ← arithProve (← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.next #[env, m0]), ← num ay])
      | return none
    let some hhi ← arithProve (← mkAppM ``LT.lt #[← num ay, ← num (← mkAppM ``Rv64mc.Env.next #[env, B])])
      | return none
    return some (← appN ``Rv64mc.frame_byte_fresh (st ++ [(`B, B), (`hn, hn), (`hlo, hlo), (`hhi, hhi)]))
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    unless ty.isAppOfArity ``Rv64mc.Env.Frame 5 do continue
    let args := ty.getAppArgs
    unless args[4]! == X do continue
    let top' := args[1]!
    let out' := args[2]!
    let N := args[3]!
    let ht ← if top' == top then mkAppM ``Nat.le_refl #[← mkAppM ``BitVec.toNat #[top]] else do
      let some (_, _, hle) ← slotFacts top' | continue
      pure hle
    let some h1 ← frameWalk env top out m0 N | continue
    let call := base ++ [(`top', top'), (`N, N), (`X, X), (`h1, h1), (`h2, d.toExpr), (`ht, ht)]
    if ← isF out' then return some (← appN ``Rv64mc.Tactic.frame_callF call)
    -- each word of the callee's `out` is the function's to write
    let hout? ← withLocalDeclD `a word fun a => do
      withLocalDeclD `ha (mkApp out' a).headBeta fun ha => do
        let some h ← mayWrite env top out m0 X a | return none
        return some (← mkLambdaFVars #[a, ha] h)
    let some hout := hout? | continue
    return some (← appN ``Rv64mc.Tactic.frame_trans (call ++ [(`out', out'), (`hout, hout)]))
  return none

/-- `env.Static X` for `X` the memory the function made: a hypothesis, or a store apart from the static data into a
    memory where it holds. -/
partial def staticWalk (env X : Expr) : MetaM (Option Expr) := do
  let X := X.consumeMData
  if let some h ← hypOf (← mkAppM ``Rv64mc.Env.Static #[env, X]) then return some h
  if X.isAppOfArity ``MachineState.setByte 3 then
    let N := X.appFn!.appFn!.appArg!
    let a := X.appFn!.appArg!
    let some hs ← staticWalk env N | return none
    let ay ← mkAppM ``alignToDword #[a]
    let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
    let apart ← mkAppM ``Or #[← mkAppM ``LT.lt #[← num ay, ← num (← mkAppM ``Rv64mc.Env.staticLo #[env])],
      ← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.staticHi #[env]), ← num ay]]
    let some h ← arithProve apart | return none
    return some (← appN ``Rv64mc.static_byte [(`env, env), (`N, N), (`a, a), (`c, X.appArg!), (`hs, hs), (`h, h)])
  unless X.isAppOfArity ``MachineState.setMem 3 do return none
  let N := X.appFn!.appFn!.appArg!
  let a := X.appFn!.appArg!
  let v := X.appArg!
  let some hs ← staticWalk env N | return none
  let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
  let apart ← mkAppM ``Or #[← mkAppM ``LT.lt #[← num a, ← num (← mkAppM ``Rv64mc.Env.staticLo #[env])],
    ← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.staticHi #[env]), ← num a]]
  let some h ← arithProve apart | return none
  return some (← appN ``Rv64mc.Tactic.static_store [(`env, env), (`N, N), (`a, a), (`v, v), (`hs, hs), (`h, h)])


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
  -- `need' ≤ need`, the callee's stack top the function's
  if cx == 0 && (← heapOn) then
    if let some hn ← hypOf (← mkAppM ``LE.le #[need', need]) then
      return some (← mkAppM ``Rv64mc.Tactic.room_hyp0 #[h, hn])
  return none

/-- A goal of `Holds`'s: the frame of the function's memory, the static data or `NEXT`'s bound in a memory it made,
    a callee's stack room. -/
def holdsGoal (ty : Expr) : MetaM (Option Expr) := do
  if ty.isAppOfArity ``Rv64mc.Env.Frame 5 then
    let args := ty.getAppArgs
    return ← frameWalk (args[0]!) (args[1]!) (args[2]!) (args[3]!) (args[4]!)
  let viaFrame (env X : Expr) : MetaM (Option (Expr × Expr)) := do
    let some (m0, hst) ← entryMem env | return none
    let some (_, _, top, _, _) ← ownStack | return none
    let some h ← frameWalk env top (mkConst ``Rv64mc.Tactic.F) m0 X | return none
    return some (h, hst)
  if ty.isAppOfArity ``Rv64mc.Env.Static 2 then
    let some (h, hst) ← viaFrame ty.appFn!.appArg! ty.appArg!
      | if ← heapOn then return ← staticWalk ty.appFn!.appArg! ty.appArg! else return none
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

/-- A narrow load (`w` not `b8`, sign-extended if `s`) from a constant table, `x` at `d.hi + d.lo + c`, where
    hypotheses `DataRef.Words env d ws` and `DataRef.Aligned d n` give the table and its alignment: the value, a
    literal, and a proof of `(if s then sext (loadVal w M x) else loadVal w M x) = v` (`DataRef.Words.load`, the rest
    by evaluation). -/
def dataLoad (M x w s : Expr) : MetaM (Option (Expr × Expr)) := do
  let some size := (match w.constName? with
    | some ``Lprog.Width.b1 => some 1
    | some ``Lprog.Width.b2 => some 2
    | some ``Lprog.Width.b4 => some 4
    | _ => none : Option Nat) | return none
  let some sgn := (if s.isConstOf ``Bool.true then some true else if s.isConstOf ``Bool.false then some false
    else none) | return none
  let (bx, cx) ← affine x
  let some b := bx | return none
  unless b.isAppOfArity ``HAdd.hAdd 6 do return none
  let hi := b.appFn!.appArg!
  let lo := b.appArg!
  unless hi.isAppOfArity ``Rv64mc.DataRef.hi 1 && lo.isAppOfArity ``Rv64mc.DataRef.lo 1 && hi.appArg! == lo.appArg! do
    return none
  let dref := hi.appArg!
  let k := cx / 8
  let o := cx % 8
  let mut words : Option (Expr × Expr × Array Expr) := none
  let mut aligned : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``Rv64mc.DataRef.Words 3 && ty.getAppArgs[1]! == dref then
      if let some elems ← listElems ty.getAppArgs[2]! then words := some (d.toExpr, ty.getAppArgs[0]!, elems)
    if ty.isAppOfArity ``Rv64mc.DataRef.Aligned 2 && ty.getAppArgs[0]! == dref then aligned := some d.toExpr
  let some (hw, env, elems) := words | return none
  let some hal := aligned | return none
  unless k < elems.size do return none
  let some wk ← lit? elems[k]! | return none
  -- the bytes read, and their sign extension
  let bits := 8 * size
  let raw := (wk >>> (8 * (o / size * size))) % 2 ^ bits
  let val := if sgn && raw ≥ 2 ^ (bits - 1) then raw + (2 ^ 64 - 2 ^ bits) else raw
  let some hs ← holdsGoal (← mkAppM ``Rv64mc.Env.Static #[env, M]) | return none
  let ws ← inferType hw
  unless ws.isApp do return none
  let hv ← mkDecideProof (← mkEq (← mkAppM ``GetElem?.getElem? #[ws.appArg!, mkNatLit k]) (← mkAppM ``Option.some #[elems[k]!]))
  let hc ← mkDecideProof (← mkEq (mkNatLit cx) (mkNatLit (8 * k + o)))
  let ho ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit o, mkNatLit 8])
  let hW ← mkDecideProof (mkNot (← mkEq w (mkConst ``Lprog.Width.b8)))
  -- `loadVal w M x = dwLoad w wk o`, at `x` written `d.hi + d.lo + BitVec.ofNat 64 cx`
  let p1 ← mkAppOptM ``Rv64mc.DataRef.Words.load #[env, dref, ws.appArg!, M, w, hw, hs, hal, mkNatLit k, mkNatLit o,
    mkNatLit cx, elems[k]!, hv, hc, ho, hW]
  let lv ← mkAppM ``Rv64mc.Tactic.loadVal #[w, M, x]
  let p1 ← if cx == 0 then do
      -- `x` is the base itself: `b = b + 0`
      let e0 ← mkEqSymm (← mkAppM ``BitVec.add_zero #[b])
      mkEqTrans (← mkCongrArg (← lam word fun t => mkAppM ``Rv64mc.Tactic.loadVal #[w, M, t]) e0) p1
    else pure p1
  let p1 ← mkExpectedTypeHint p1 (← mkEq lv (← mkAppM ``Rv64mc.dwLoad #[w, elems[k]!, mkNatLit o]))
  let f ← lam word fun t => do
    mkAppM ``ite #[← mkEq s (mkConst ``Bool.true), mkApp2 (mkConst ``UnOp.eval) (mkApp (mkConst ``UnOp.sext) w) t, t]
  let pf ← mkCongrArg f p1
  let rhs := (mkApp f (← mkAppM ``Rv64mc.dwLoad #[w, elems[k]!, mkNatLit o])).headBeta
  let q ← mkDecideProof (← mkEq rhs (mkLit val))
  let p ← mkEqTrans pf q
  let ite ← mkAppM ``ite #[← mkEq s (mkConst ``Bool.true), mkApp2 (mkConst ``UnOp.eval) (mkApp (mkConst ``UnOp.sext) w) lv, lv]
  return some (mkLit val, ← mkExpectedTypeHint p (← mkEq ite (mkLit val)))

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

/-- An address `(t + c₁) + c₂` as `t + c` (`addV`), sizes of layouts as numerals, and a proof where it changed. -/
partial def normAddr (x : Expr) : MetaM (Expr × Option Expr) := do
  let x ← litConsts x
  if x.isAppOfArity ``HAdd.hAdd 6 then
    let q := x.appArg!
    if (← lit? q).isSome then
      let (p, pp) ← normAddr x.appFn!.appArg!
      let (v, pv) ← addV p q
      let p1 ← match pp with
        | some e => some <$> mkCongrArg (← lam word (mkAdd · q)) e
        | none => pure none
      match p1, pv with
      | none, none => return (v, none)
      | some a, none => return (v, some a)
      | none, some b => return (v, some b)
      | some a, some b => return (v, some (← mkEqTrans a b))
  return (x, none)

/-- A read of memory, `M.getMem x`, through `M`'s stores and its callees' frames (`readMem`), its address normalized;
    a word-valued accessor of memory (`vecPtr m a`) unfolded first. -/
def memStep (e : Expr) : SimpM Simp.Step := do
  -- a memory is left as it is: its stored values are what the executor wrote
  if e.isAppOf ``MachineState.setMem || e.isAppOf ``MachineState.setByte then return .done { expr := e }
  if e.isAppOfArity ``MachineState.getMem 2 then
    let M := e.appFn!.appArg!
    let x := e.appArg!
    let (x', px) ← normAddr x
    let (v, pv) ← readMem M x'
    let getM := mkApp (mkConst ``MachineState.getMem) M
    let p1 ← match px with
      | some p => some <$> mkCongrArg getM p
      | none => pure none
    let p ← match p1, pv with
      | none, none => pure none
      | some a, none => pure (some a)
      | none, some b => pure (some b)
      | some a, some b => some <$> mkEqTrans a b
    return .done { expr := v, proof? := p }
  if let some c := e.getAppFn.constName? then
    if c != ``MachineState.setMem && c != ``Rv64mc.Env.next && e.getAppArgs.any (fun a => a.isFVar || a.isApp) then
      if let some (.defnInfo _) := (← getEnv).find? c then
        if ← isWordTy (← inferType e) then
          let mut mem := false
          for a in e.getAppArgs do
            if (← whnfR (← inferType a)).isConstOf ``MachineState then mem := true
          if mem then
            if let some e' ← withTransparency .default (unfoldDefinition? e) then return .visit { expr := e'.headBeta }
  if e.isAppOf ``Rv64mc.Tactic.rf || e.isAppOf ``Lprog.updReg then return .done { expr := e }
  return .continue

/-- `ty` with its reads of memory resolved where they can be (`memStep`), and a proof where it changed. -/
def memTy (ty : Expr) : MetaM (Expr × Option Expr) := do
  let ty ← instantiateMVars ty
  if (ty.find? fun e => e.isAppOfArity ``MachineState.getMem 2).isNone then
    -- an accessor (`vecPtr m a`) may still read memory
    if (ty.find? fun e => e.isFVar).isNone then return (ty, none)
  let ctx ← Simp.mkContext (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Simp.main ty ctx (methods := { pre := memStep })
  return (r.expr, r.proof?)

/-- A closed comparison of numbers or words, by evaluation. -/
def decideClosed (ty : Expr) : MetaM (Option Expr) := do
  if ty.hasFVar || ty.hasMVar then return none
  unless ty.isAppOfArity ``Eq 3 || ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``Ne 3 do
    return none
  try
    let d ← mkDecide ty
    let r ← withTransparency .default (whnf d)
    unless r.isConstOf ``Bool.true do return none
    return some (← mkDecideProof ty)
  catch _ => return none
/-- `X.getMem b = Y.getMem b` for `X` a memory the function made from `Y`: through `X`'s stores apart from `b`
    (`neProof`) and its callees' frames (`keepAt`), what the context says of `b` deciding each. -/
partial def memWalk (X Y b : Expr) : MetaM (Option Expr) := do
  let X := X.consumeMData
  if X == Y then return some (← mkEqRefl (← mkAppM ``MachineState.getMem #[X, b]))
  if X.isAppOfArity ``MachineState.setMem 3 then
    let N := X.appFn!.appFn!.appArg!
    let y := X.appFn!.appArg!
    let w := X.appArg!
    let some hne ← neProof b y | return none
    let p1 ← mkAppOptM ``MachineState.getMem_setMem_ne #[N, y, b, w, hne]
    let some p2 ← memWalk N Y b | return none
    return some (← mkEqTrans p1 p2)
  let some (p1, N) ← keepAt X b | return none
  let some p2 ← memWalk N Y b | return none
  return some (← mkEqTrans p1 p2)

/-- A proposition that unfolds to `∀ b, … → X.getMem b = Y.getMem b` (`Keeps`, a family's `HeapKept`): its binders
    introduced and `memWalk`. -/
partial def memEqForall (ty : Expr) (fuel : Nat := 4) : MetaM (Option Expr) := do
  let ty := (← whnfR (← instantiateMVars ty)).consumeMData
  unless ty.isForall do
    if fuel == 0 then return none
    let some ty' ← withTransparency .default (unfoldDefinition? ty) | return none
    return ← memEqForall ty' (fuel - 1)
  forallTelescopeReducing ty fun xs concl => do
    let concl := concl.consumeMData
    unless concl.isAppOfArity ``Eq 3 && xs.size ≥ 1 do return none
    let lhs := concl.appFn!.appArg!
    let rhs := concl.appArg!
    unless lhs.isAppOfArity ``MachineState.getMem 2 && rhs.isAppOfArity ``MachineState.getMem 2 do return none
    let b := lhs.appArg!
    unless rhs.appArg! == b do return none
    let some p ← memWalk lhs.appFn!.appArg! rhs.appFn!.appArg! b | return none
    return some (← mkLambdaFVars xs p)

/-- **A representation predicate carried to a later memory**: the goal `T`, a predicate of memory `M`, from the
    hypothesis `h : S`, the same predicate of an earlier memory, by its lemma `<P>.keep` (`WordsAt.keep`,
    `VecAt.keep`, a family's own): the lemma's premises that its hypothesis does not give are a memory kept
    (`memEqForall`), a fact about numbers (`arithProve`), or the same carried for a part (`Elems m p xs → Elems m' p
    xs`, recursively). -/
partial def transport (T h : Expr) (fuel : Nat := 3) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let T := (← instantiateMVars T).consumeMData
  let some c := T.getAppFn.constName? | return none
  let S ← instantiateMVars (← inferType h)
  -- a definition without a lemma of its own: the one it unfolds to (`UsizesAt` to `WordsAt`)
  unless (← getEnv).contains (c ++ `keep) || (← getEnv).contains (c ++ `keep') do
    let some T' ← withTransparency .default (unfoldDefinition? T) | return none
    let some S' ← withTransparency .default (unfoldDefinition? S) | return none
    let some p ← transport T'.headBeta (← mkExpectedTypeHint h S'.headBeta) (fuel - 1) | return none
    return some (← mkExpectedTypeHint p T)
  for lem in [c ++ `keep, c ++ `keep'] do
    unless (← getEnv).contains lem do continue
    let saved ← saveState
    let ok ← try
        let lc ← mkConstWithFreshMVarLevels lem
        let (xs, _, concl) ← forallMetaTelescopeReducing (← inferType lc)
        unless ← isDefEq concl T do throwError "its conclusion is not the goal"
        -- the hypothesis
        let mut given := false
        for x in xs do
          if given then break
          let xt ← instantiateMVars (← inferType x)
          if (← isProp xt) && !(← x.mvarId!.isAssigned) then
            if ← isDefEq xt S then
              x.mvarId!.assign h
              given := true
        unless given do throwError "no premise is the hypothesis"
        for x in xs do
          if ← x.mvarId!.isAssigned then continue
          let xt ← instantiateMVars (← inferType x)
          unless ← isProp xt do throwError "an argument is not given: {xt}"
          if xt.hasExprMVar then throwError "a premise is not determined: {xt}"
          if let some p ← memEqForall xt then
            x.mvarId!.assign p
            continue
          if let some p ← arithProve xt then
            x.mvarId!.assign p
            continue
          -- a part carried: `A m … → A m' …`
          let some p ← (forallTelescopeReducing xt fun ys concl' => do
              unless ys.size == 1 do return none
              let some q ← transport concl' ys[0]! (fuel - 1) | return none
              return some (← mkLambdaFVars ys q))
            | throwError "a premise is not closed: {xt}"
          x.mvarId!.assign p
        let pf ← instantiateMVars (mkAppN lc xs)
        if pf.hasExprMVar then throwError "the proof is not determined"
        pure (some pf)
      catch e =>
        trace[rv_sym] "transport by {lem}: {e.toMessageData}"
        pure none
    match ok with
    | some pf => return some pf
    | none => saved.restore
  return none

/-- A hypothesis of the goal's predicate at another memory, the other arguments the same, carried to the goal's
    (`transport`). -/
def transportGoal (T : Expr) : MetaM (Option Expr) := do
  let T := (← instantiateMVars T).consumeMData
  let some c := T.getAppFn.constName? | return none
  unless (← getEnv).contains (c ++ `keep) || (← getEnv).contains (c ++ `keep') do return none
  let args := T.getAppArgs
  let mut memPos := #[]
  for k in [0:args.size] do
    if (← whnfR (← inferType args[k]!)).isConstOf ``MachineState then memPos := memPos.push k
  if memPos.isEmpty then return none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dt := (← instantiateMVars d.type).consumeMData
    unless dt.getAppFn.constName? == some c && dt.getAppNumArgs == args.size do continue
    let dargs := dt.getAppArgs
    let mut same := true
    for k in [0:args.size] do
      unless memPos.contains k || dargs[k]! == args[k]! do same := false
    unless same do continue
    if let some p ← transport T d.toExpr then return some p
  return none

/-- `a` and `b` equal by reducible unfolding, within a budget: two large terms that differ are given up on rather
    than unfolded for minutes. -/
def cheapDefEq (a b : Expr) : MetaM Bool := do
  let saved ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) <|
      withReducible (isDefEq a b))
    fun _ => do
      saved.restore
      return false

/-- `(top + c).toNat % 16 = 0` for `c` a multiple of 16 below the function's stack top, from `top.toNat % 16 = 0`
    (`align_off`): a callee's stack top aligned where the caller's is. -/
def alignGoal (ty : Expr) : MetaM (Option Expr) := do
  unless ty.isAppOfArity ``Eq 3 do return none
  let lhs := ty.appFn!.appArg!
  -- both sides evaluated before the shape is tested: `natVal?` can run out of recursion depth (on
  -- `(x <<< 4 + q + 18446744073709551600#64).toNat`), and `closeSideSafe` then leaves the whole goal, which
  -- `FromElemT.tail` closes by hand
  let lv ← if lhs.isApp then natVal? lhs.appArg! else pure none
  let rv ← natVal? ty.appArg!
  unless lhs.isAppOfArity ``HMod.hMod 6 && lv == some 16 && rv == some 0 do return none
  let n := lhs.appFn!.appArg!
  unless n.isAppOfArity ``BitVec.toNat 2 do return none
  let some (_, _, top, _) ← rawStack | return none
  let (bx, cx) ← affine n.appArg!
  unless bx == some top && cx != 0 do return none
  let k := 2 ^ 64 - cx
  unless k % 16 == 0 do return none
  let some ht ← hypOf (← mkEq (← mkAppM ``HMod.hMod #[← mkAppM ``BitVec.toNat #[top], mkNatLit 16]) (mkNatLit 0))
    | return none
  let c := n.appArg!.appArg!
  let hc ← mkDecideProof (← mkEq (← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[c], mkNatLit k]) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]))
  let h16 ← mkDecideProof (← mkEq (← mkAppM ``HMod.hMod #[mkNatLit k, mkNatLit 16]) (mkNatLit 0))
  return some (← mkAppM ``Rv64mc.Tactic.align_off #[ht, hc, h16])

/-- Close what is closed by reduction, by an address fact, or by a hypothesis; split conjunctions, unfold
    definitions; leave the rest, its reads reduced. -/
partial def closeSide (g : MVarId) (split : Bool := false) : MetaM (List MVarId) := g.withContext do
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
    -- `split` (a callee's precondition): each conjunct on its own, one out of recursion depth or heartbeats left and
    -- the others closed; else the whole goal is left as it was (`closeSideSafe`)
    unless split do return (← closeSide ga.mvarId!) ++ (← closeSide gb.mvarId!)
    let part (h : Expr) : MetaM (List MVarId) := do
      let saved ← saveState
      tryCatchRuntimeEx (closeSide h.mvarId! true) fun _ => do
        saved.restore
        return [h.mvarId!]
    return (← part ga) ++ (← part gb)
  if let some pf ← holdsGoal ty then
    g.assign pf
    return []
  if let some ty' ← unfoldHead? ty then
    let g' ← g.replaceTargetDefEq ty'
    return ← closeSide g' split
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
  let (ty, pn) ← if ← heapOn then nextTy ty else pure (ty, none)
  let g ← match pn with
    | some p => g.replaceTargetEq ty p
    | none => pure g
  let (ty, pm) ← if ← heapOn then memTy ty else pure (ty, none)
  let g ← match pm with
    | some p => g.replaceTargetEq ty p
    | none => pure g
  if ← heapOn then
    if let some p ← decideClosed ty then
      g.assign p
      return []
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
    -- an invariant's value left to fill (`?v`): what the executor computed
    if b.isMVar && !a.hasMVar then
      if (← heapOn) && !(← b.mvarId!.isAssigned) then
        b.mvarId!.assign a
        g.assign (← mkEqRefl a)
        return []
    let (ba, ca) ← affine a
    let (bb, cb) ← affine b
    if a == b || (ba == bb && ca == cb) || (← cheapDefEq a b) then
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
  -- a callee's stack top 16-aligned: the function's own, less a multiple of 16
  if let some p ← alignGoal ty then
    g.assign p
    return []
  if let some p ← arithProve ty then
    g.assign p
    return []
  if ← heapOn then
    -- a representation predicate of an earlier memory, carried
    if let some p ← transportGoal ty then
      g.assign p
      return []
    -- a representation predicate built in place: every field, or its definition's every part, closed
    if let some c := ty.getAppFn.constName? then
      if keep.contains c && !noArith.contains c then
        let saved ← saveState
        let parts? ← try
            if isStructure (← getEnv) c then pure (some (← g.constructor))
            else match ← unfoldDefinition? ty with
              | some ty' => pure (some [← g.replaceTargetDefEq ty'.headBeta])
              | none => pure none
          catch _ => pure none
        if let some parts := parts? then
          let mut rest := []
          for p in parts do
            unless ← p.isAssigned do rest := rest ++ (← closeSide p)
          if rest.isEmpty then return []
        saved.restore
    -- a `∀` whose premises contradict the context, or whose conclusion closes
    if ty.isForall then
      let saved ← saveState
      let (_, g') ← g.intros
      let ok ← g'.withContext do
        match ← arithProve (mkConst ``False) with
        | some p =>
          g'.assign (← mkFalseElim (← g'.getType) p)
          pure true
        | none => pure false
      if ok then return []
      if (← closeSide g').isEmpty then return []
      saved.restore
    -- a hypothesis of the same predicate, up to unfolding
    if let some c := ty.getAppFn.constName? then
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let dt := (← instantiateMVars d.type).consumeMData
        if dt.getAppFn.constName? == some c then
          let saved ← saveState
          let same ← try withTransparency .default (isDefEq dt ty) catch _ => pure false
          if same then
            g.assign d.toExpr
            return []
          saved.restore
  return [g]

/-- `closeSide`, out of recursion depth or heartbeats leaving the goal as it was. -/
def closeSideSafe (g : MVarId) (split : Bool := false) : MetaM (List MVarId) := do
  let saved ← saveState
  tryCatchRuntimeEx (closeSide g split) fun _ => do
    saved.restore
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

/-- `e` with every 64-bit literal in the form the executor writes (`mkLit`). -/
def litForms (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if let some v ← lit? x then return .done (mkLit v)
    return .continue)

/-- A fact among those given whose type is `lhs = ?` with `lhs` the given term, its right side and proof. -/
def factEq (cfg : Cfg) (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  let lhs ← if ← heapOn then litForms lhs else pure lhs
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
        let same ← if g.isApp then withReducible (isDefEq g.appArg! f) else pure false
        if g.isAppOf ``GetElem?.getElem? && same then
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
    let facts ← if ← heapOn then facts.mapM fun (p, t) => normNext p t else pure facts
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
        let noOut ← isF (args[2]!)
        let fr := [(`env, args[0]!), (`top, args[1]!), (`M, args[3]!), (`X, args[4]!), (`h, mkFVar h)]
        let some (hb, S, top, need, _) ← ownStack | continue
        let hlim ← if args[1]! == top then
            mkAppM ``Nat.le_trans #[← mkAppM ``Nat.le_add_right #[S, need], hb]
          else do
            let some (hlo, _, _) ← slotFacts (args[1]!) | continue
            pure hlo
        unless noOut || (← heapOn) do continue
        let pf ← if noOut then appN ``Rv64mc.Tactic.frame_above (fr ++ [(`hlim, hlim)])
          else appN ``Rv64mc.Tactic.frame_above_out (fr ++ [(`out, args[2]!), (`hlim, hlim)])
        above := above.push (pf, ← inferType pf)
        -- the heap below `NEXT` at the call
        unless ← heapOn do continue
        let nx ← mkAppM ``Rv64mc.Env.next #[args[0]!, args[3]!]
        let hnxT ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[nx],
          ← mkAppM ``BitVec.toNat #[← mkAppM ``Rv64mc.Env.heapEnd #[args[0]!]]]
        let hnx ← match ← hypOf hnxT with
          | some h => pure (some h)
          | none => match ← holdsGoal hnxT with
            | some h => pure (some h)
            | none => arithProve hnxT
        let some hnx := hnx | continue
        let pf ← if noOut then appN ``Rv64mc.Tactic.frame_keep (fr ++ [(`hlim, hlim), (`hnx, hnx)])
          else appN ``Rv64mc.Tactic.frame_keep_out (fr ++ [(`out, args[2]!), (`hlim, hlim), (`hnx, hnx)])
        above := above.push (pf, ← inferType pf)
      if above.isEmpty then return g
      let (g, _) ← addFacts g (Name.mkSimple s!"keep{k}") above
      return g
    some <$> absorbFacts g (hs.map mkFVar) (rv_sym.bind.get (← getOptions))

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
        if let some gp := gp? then left := left ++ (← closeSideSafe gp) else left := left.push g
        continue
    if ((cfg.stops.contains a.pc || cfg.heads.contains a.pc) && g != g0) || seen.contains a.pc then
      let why := if seen.contains a.pc then "a program counter it has passed" else if cfg.stops.contains a.pc then
        "a stop" else "a loop's head"
      trace[rv_sym] "left at {a.pc}: {why}"
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
          else if let some (val, hv) ← (if ← heapOn then dataLoad a.M x w s else pure none) then
            let (R', hR) ← writeReg a.R (oargs[1]!) val
            let h ← newGoal g (a.goal (a.pc + 1) R' a.M)
            g.assign (← appN ``Rv64mc.Tactic.step_loadw (base ++ [(`rd, (oargs[1]!)), (`w, w), (`s, s),
              (`a, (oargs[4]!)), (`x, x), (`v, val), (`R', R'), (`ha, ha), (`hv, hv), (`hR, hR), (`h, h)]))
            pure (some [h.mvarId!])
          else if let some (bv, pb) ← (do
              unless (← heapOn) && w.isConstOf ``Lprog.Width.b1 do return none
              let (bv, pb?) ← readByte a.M x
              let some pb := pb? | return none
              return some (bv, pb)) then
            -- a byte read through the stores (`readByte`)
            let ext (t : Expr) : Expr := mkApp3 (mkConst ``BitVec.zeroExtend) (mkRawNatLit 8) (mkRawNatLit 64) t
            let lv := ext bv
            let lvM := mkApp3 (mkConst ``Rv64mc.Tactic.loadVal) w a.M x
            let p1 ← mkExpectedTypeHint (← mkCongrArg (← lam (mkApp (mkConst ``BitVec) (mkRawNatLit 8)) (pure ∘ ext)) pb)
              (← mkEq lvM lv)
            let f ← lam word fun t => do
              mkAppM ``ite #[← mkEq s (mkConst ``Bool.true), mkApp2 (mkConst ``UnOp.eval) (mkApp (mkConst ``UnOp.sext) w) t, t]
            let val := if s.isConstOf ``Bool.true then mkApp2 (mkConst ``UnOp.eval) (mkApp (mkConst ``UnOp.sext) w) lv
              else lv
            let ite ← mkAppM ``ite #[← mkEq s (mkConst ``Bool.true), mkApp2 (mkConst ``UnOp.eval)
              (mkApp (mkConst ``UnOp.sext) w) lvM, lvM]
            let hv ← mkExpectedTypeHint (← mkCongrArg f p1) (← mkEq ite val)
            let (R', hR) ← writeReg a.R (oargs[1]!) val
            let h ← newGoal g (a.goal (a.pc + 1) R' a.M)
            g.assign (← appN ``Rv64mc.Tactic.step_loadw (base ++ [(`rd, (oargs[1]!)), (`w, w), (`s, s),
              (`a, (oargs[4]!)), (`x, x), (`v, val), (`R', R'), (`ha, ha), (`hv, hv), (`hR, hR), (`h, h)]))
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
        let (hct, gt') ← gt.mvarId!.intro `hc
        let (hcn, gn') ← gn.mvarId!.intro `hc
        -- a comparison of literals: the branch not taken closed by its hypothesis' refutation
        if let (true, some xv, some yv) := (← heapOn, ← lit? x, ← lit? y) then
          let taken := match opStr with
            | "eq" => xv == yv
            | "ne" => xv != yv
            | "ltu" => decide (xv < yv)
            | "geu" => decide (yv ≤ xv)
            | "lt" => decide (toInt64 xv < toInt64 yv)
            | _ => decide (toInt64 yv ≤ toInt64 xv)
          let (dead, hc, P, live) := if taken then (gn', hcn, pn, gt') else (gt', hct, pt, gn')
          dead.withContext do
            dead.assign (← mkAbsurd (← dead.getType) (mkFVar hc) (← mkDecideProof (mkNot P)))
          pure (some [← nameApart live])
        else
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
        let side ← closeSideSafe hpre.mvarId! (split := true)
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
        let side := (← closeSideSafe hsp.mvarId!) ++ (← closeSideSafe hpre.mvarId! (split := true))
        let g' ← afterCall hk.mvarId! k
        pure (some (side ++ g'.toList))
      | some ``Lprog.LinstrR.Lret =>
        let h ← newGoal g (mkAppN a.head (a.pre.push (mkApp3 a.stMk a.rest a.R a.M)))
        let hra ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x1)) a.rv)
        let hsp ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x2)) a.top)
        g.assign (← appN ``Rv64mc.Tactic.step_ret (base ++ [(`hra, hra), (`hsp, hsp), (`h, h)]))
        let side := (← closeSideSafe hra.mvarId!) ++ (← closeSideSafe hsp.mvarId!)
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
  let facts ← facts.mapM fun (pf, ty) => do
    let ty' ← if ← heapOn then litForms ty else pure ty
    return (← mkExpectedTypeHint pf ty', ty')
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

syntax rvThrough := "*" <|> ("[" num,* "]")
syntax rvSymArgs := (" stop " "[" num,* "]")? (" through " rvThrough)? (" with " "[" term,* "]")?
  (" using " "[" term,* "]")?

/-- The loop heads `through` passes: every one (`*`, as `none`) or those listed. -/
def throughHeads (t : Syntax) : MetaM (Option (List Nat)) :=
  match t with
  | `(rvThrough| *) => return none
  | `(rvThrough| [$ks,*]) => return some (ks.getElems.toList.map (·.getNat))
  | _ => throwError "rv_sym: `through` takes `*` or a list of program counters"

/-- The arguments, elaborated in the main goal's context (after `rv_auto` has opened the contract: its `regs`, `m`,
    `top`, `ret` and `hpre_k` in scope). -/
def elabArgs (hp : Syntax) (args : Syntax) : TacticM Cfg := withMainContext do
  let stops := if args[0].isNone then [] else args[0][2].getSepArgs.toList.filterMap (·.isNatLit?)
  let through ← if args[1].isNone then pure (some []) else throughHeads args[1][1]
  let facts ← if args[2].isNone then pure #[] else args[2][2].getSepArgs.mapM fun t => elabTerm t none
  let specs ← if args[3].isNone then pure #[] else args[3][2].getSepArgs.mapM fun t => elabTerm t none
  let cfg ← mkCfg (← elabTerm hp none) stops facts specs
  match through with
  | none => return { cfg with heads := [] }
  | some ks => return { cfg with heads := cfg.heads.filter (!ks.contains ·) }

/-- **`rv_sym hp stop [pcs] through [heads] with [facts] using [contracts]`**: step the goal
    `SafeN … ⟨⟨fn, pc, …⟩ :: …⟩` through the body of the template `hp : p[fn]? = some fd` names, not stopping at the
    loop heads in `through` (`through *`: at none). -/
syntax (name := rvSym) "rv_sym " term rvSymArgs : tactic

@[tactic rvSym] def evalRvSym : Tactic := fun stx => do
  arithCache.set {}
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

/-- **`rv_auto hp stop [pcs] through [heads] with [facts] using [contracts]`**: a goal `rvIsa.Contract p c fn Pre Post` for the
    template `hp : p[fn]? = some fd`, stepped from the entry: the precondition split into hypotheses, every call
    through its contract, and what the postcondition says of the stack pointer, the saved registers and the memory
    above the frame closed. What is left is the postcondition's functional part, any callee precondition that is
    not closed by reduction or a hypothesis, and the goals at `stop`s and loop heads. -/
syntax (name := rvAuto) "rv_auto " term rvSymArgs : tactic

@[tactic rvAuto] def evalRvAuto : Tactic := fun stx => do
  arithCache.set {}
  let g ← openContract (← getMainGoal)
  replaceMainGoal [g]
  let cfg ← elabArgs stx[1] stx[2]
  -- with `rv_sym.heap`, the facts given that are not equations (a region's `WordsAt`, `Live`, `InRange`) are
  -- hypotheses `hwith_k` the closers read
  let g ← if ← heapOn then g.withContext do
      let fs := cfg.facts.filter fun (_, ty) => !ty.consumeMData.isAppOf ``Eq
      if fs.isEmpty then pure g else pure (← addFacts g `hwith fs).1
    else pure g
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
    left := left ++ (← closeSideSafe g)
  setGoals left.toList

/-- **`rv_mem`**: the goal's reads of registers, of `NEXT` and of memory resolved, as the executor reads them: through
    the register file, the stores and the callees' frames (`rv_sym.heap` on). -/
syntax (name := rvMem) "rv_mem" : tactic

@[tactic rvMem] def evalRvMem : Tactic := fun _ => withOptions (rv_sym.heap.set · true) do
  let g ← getMainGoal
  let g ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let (ty, p) ← normReads ty
    let g ← match p with
      | some p => g.replaceTargetEq ty p
      | none => pure g
    let (ty, p) ← nextTy ty
    let g ← match p with
      | some p => g.replaceTargetEq ty p
      | none => pure g
    let (ty, p) ← memTy ty
    match p with
      | some p => g.replaceTargetEq ty p
      | none => pure g
  replaceMainGoal [g]

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
