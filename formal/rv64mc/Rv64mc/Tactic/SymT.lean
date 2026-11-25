/-
  Rv64mc.Tactic.SymT

  `rv_symT`: `rv_sym` (`Rv64mc.Tactic.Sym`) for a total goal `rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, …⟩ :: …⟩`, the
  judgement `HoldsT` (`Core/HoldsT.lean`) asks of a function's body. The same executor over `StepsT.lean`'s rules:
  every value, read and memory is computed as `rv_sym` computes it, by `Sym.lean`'s functions, and the goals it
  leaves are `rv_sym`'s, with these besides, each closed where it can be and left as a goal where it cannot:

  * at a load or store, its address in a window (`inWindow x w = true`, as `inWindow_iff`'s bounds) and aligned for
    its width (`x.toNat % w = 0`), by `omega` over the context (`arithProve`, run with `rv_sym.heap` on whatever
    the option says elsewhere): the stack bound and `Windows`' fields, the layout, the pointer's bounds in `Pre`;
    for a store, no code at it (`noCodeAt_of_windows`), from the entry's `Windows` and the code map kept along the
    stores and calls since (`codeWalk`);
  * at a call or tail call through a total contract (`using`, a `HoldsT` or a definition unfolding to one, such
    as `Aborts`): `Windows` at the callee's stack top in the current memory (`windowsGoal`: the entry's, by
    `Windows.after` and `Windows.callee`, `NEXT` not lowered by `omega`), and `Q` at the callee's stopping states,
    by the caller's own stopping hypothesis (`hstop`, as `rv_autoT` names it) where the caller's stopping set
    contains the callee's (`closeStop`); a callee's postcondition gives the code map kept, which the walk uses;
  * at a return, the code map kept (`HoldsT.post`).

  It stops where `rv_sym` stops: at a program counter in `stop`, at a loop's head (for `Total.loop`), at a call
  without a contract, and where the function returns, which the contract's continuation closes.

  ## Main results

  * `rv_symT hp stop [pcs] with [facts] using [contracts]`: step a goal `Total … ⟨⟨fn, pc, …⟩ :: …⟩`
  * `rv_autoT hp …`: a total contract (`HoldsT`, `Isa.TContract`), from the entry
  * `rv_introT h`: a loop invariant's facts into the register file
  * `rv_closeT`: the side goals' closer
-/

import Rv64mc.Tactic.Sym
import Rv64mc.Tactic.StepsT
import Rv64mc.Core.HoldsT

namespace Rv64mc.Tactic.SymT

open Lean Meta Elab Tactic
open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Tactic.Sym

/-! ## Goals -/

/-- A goal `Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, R, M⟩`, its parts; `pre` the six arguments before the
    state. -/
def parseAtT (t : Expr) : MetaM (Option At) := do
  let t := (← instantiateMVars t).consumeMData
  unless t.isAppOfArity ``Lprog.Isa.Total 7 do return none
  let args := t.getAppArgs
  unless (args[4]!).consumeMData.isAppOfArity ``Rv64mc.WinOk 1 do return none
  let s ← whnfR (args[6]!)
  unless s.isAppOfArity ``Lprog.State.mk 4 do return none
  let st ← whnfR (s.getAppArgs[1]!)
  unless st.isAppOfArity ``List.cons 3 do return none
  let fr ← whnfR (st.getAppArgs[1]!)
  unless fr.isAppOfArity ``Lprog.Frame.mk 4 do return none
  let some pc ← evalNat (fr.getAppArgs[1]!) | return none
  return some ⟨t.getAppFn, args.extract 0 6, mkApp s.getAppFn (s.getAppArgs[0]!),
    mkApp st.getAppFn (st.getAppArgs[0]!), fr.getAppFn, fr.getAppArgs[0]!, pc, fr.getAppArgs[2]!,
    fr.getAppArgs[3]!, st.getAppArgs[2]!, s.getAppArgs[2]!, s.getAppArgs[3]!⟩

/-- The arguments every rule of `StepsT` takes first. -/
def commonT (a : At) (fd : Expr) : List (Name × Expr) :=
  [(`p, (a.pre[1]!)), (`E, (a.pre[2]!)), (`c, (a.pre[3]!)), (`Q, (a.pre[5]!)), (`rest, a.rest), (`regs, a.R),
    (`m, a.M), (`fd, fd), (`fn, a.fnE), (`pc, mkNatLit a.pc), (`rv, a.rv), (`top, a.top)]

/-- The goal's register file, if the executor did not make it, as the `rf` of its values with the facts `R r = v`
    written into their places: `absorbFacts` for a total goal. -/
def absorbFactsT (g : MVarId) (facts : Array Expr) (bind : Nat := 0) : MetaM MVarId := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``Lprog.Isa.Total 7 do return g
  let args := t.getAppArgs
  let s ← whnfR (args[6]!)
  unless s.isAppOfArity ``Lprog.State.mk 4 do return g
  let st := s.getAppArgs[1]!
  let R0 := (s.getAppArgs[2]!).consumeMData
  let M := s.getAppArgs[3]!
  if R0.isAppOfArity ``Rv64mc.Tactic.rf 32 then return g
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
  let goalT := mkAppN t.getAppFn ((args.extract 0 6).push (mkApp3 (mkApp s.getAppFn (s.getAppArgs[0]!)) st R' M))
  let g' ← newGoal g goalT
  g.assign (← appN ``Rv64mc.Tactic.regsT_eq [(`p, (args[1]!)), (`E, (args[2]!)), (`c, (args[3]!)), (`Q, (args[5]!)),
    (`m, M), (`st, st), (`R, R0), (`R', R'), (`e, e), (`k, g')])
  return g'.mvarId!

/-! ## Side goals: windows, alignment, code -/

/-- `x` with `omega` over the context, whatever `rv_sym.heap` says. -/
def withArith {α : Type} (x : MetaM α) : MetaM α := withOptions (rv_sym.heap.set · true) x

/-- `M.code = T.code`, through stores (`code_setMem`, …) and callees' postconditions (`m'.code = M.code` in the
    context). `seen` holds the memories already walked, so that a cycle of such facts ends. -/
partial def codeWalk (M T : Expr) (seen : List Expr := []) : MetaM (Option Expr) := do
  let M := M.consumeMData
  if M == T then return some (← mkEqRefl (← mkAppM ``MachineState.code #[M]))
  if seen.contains M then return none
  let seen := M :: seen
  let stores := [(``MachineState.setMem, ``MachineState.code_setMem),
    (``MachineState.setByte, ``MachineState.code_setByte),
    (``MachineState.setHalfword, ``MachineState.code_setHalfword),
    (``MachineState.setWord32, ``MachineState.code_setWord32)]
  if let some (_, c) := stores.find? (M.isAppOfArity ·.1 3) then
    let N := M.appFn!.appFn!.appArg!
    let some p ← codeWalk N T seen | return none
    let p1 ← mkAppOptM c #[N, M.appFn!.appArg!, M.appArg!]
    return some (← mkEqTrans p1 p)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    unless ty.isAppOfArity ``Eq 3 do continue
    let l := ty.appFn!.appArg!.consumeMData
    let r := ty.appArg!.consumeMData
    unless l.isAppOfArity ``MachineState.code 1 && r.isAppOfArity ``MachineState.code 1 && l.appArg! == M do continue
    if r.appArg! == M then continue
    let some p ← codeWalk r.appArg! T seen | continue
    return some (← mkEqTrans d.toExpr p)
  return none

/-- The hypotheses `Windows env top0 m0` of the context. -/
def windowsHyps : MetaM (Array (Expr × Expr × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``Rv64mc.Windows 3 then
      let a := ty.getAppArgs
      out := out.push (d.toExpr, a[0]!, a[1]!, a[2]!)
  return out

/-- A goal of type `ty`: `prove`'s proof, or a new goal left. -/
def sideGoal (g : MVarId) (ty : Expr) (prove : MetaM (Option Expr)) : MetaM (Expr × List MVarId) := do
  if let some p ← g.withContext prove then return (p, [])
  let h ← newGoal g ty
  return (h, [h.mvarId!])

/-- `inWindow x n = true` by `omega`, as `inWindow_iff`'s bounds. -/
def winProof (x : Expr) (n : Nat) : MetaM (Option Expr) := do
  let xn ← mkAppM ``BitVec.toNat #[x]
  let xe ← mkAppM ``HAdd.hAdd #[xn, mkNatLit n]
  let le (a b : Expr) : MetaM Expr := mkAppM ``LE.le #[a, b]
  let lo ← mkAppM ``And #[← le (mkNatLit 0x10000000) xn, ← le xe (mkNatLit 0x78000000)]
  let hi ← mkAppM ``And #[← le (mkNatLit 0xa0000000) xn, ← le xe (mkNatLit 0xc0000000)]
  let some p ← withArith (arithProve (← mkAppM ``Or #[lo, hi])) | return none
  return some (← mkAppM ``Iff.mpr #[← mkAppOptM ``Rv64mc.inWindow_iff #[x, mkNatLit n], p])

/-- `x.toNat % n = 0`: by `Nat.mod_one` for `n = 1`, else by `omega`. -/
def alignProof (x : Expr) (n : Nat) : MetaM (Option Expr) := do
  let xn ← mkAppM ``BitVec.toNat #[x]
  if n == 1 then return some (← mkAppM ``Nat.mod_one #[xn])
  withArith (arithProve (← mkEq (← mkAppM ``HMod.hMod #[xn, mkNatLit n]) (mkNatLit 0)))

/-- `noCodeAt M x n = true` from a `Windows` of a memory whose code map `M` keeps, and `hx : inWindow x n = true`. -/
def noCodeProof (M : Expr) (n : Nat) (hx : Expr) : MetaM (Option Expr) := do
  for (hw, _, _, m0) in ← windowsHyps do
    let some hc ← codeWalk M m0 | continue
    let hn ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit n])
    return some (← mkAppM ``Rv64mc.Tactic.noCodeAt_of_windows #[hw, hc, hx, hn])
  return none

/-- `Windows env t M`: an entry's `Windows` with the code map kept (`codeWalk`), `NEXT` not lowered and the stack top
    no higher, the last two by `omega` or left as goals. -/
def windowsGoal (g : MVarId) (ty : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  let a := ty.getAppArgs
  let (env, t, M) := (a[0]!, a[1]!, a[2]!)
  for (hw, env0, top0, m0) in ← windowsHyps do
    unless env0 == env do continue
    let some hc ← codeWalk M m0 | continue
    let mut left := []
    let mut h := hw
    unless M.consumeMData == m0 do
      let num (e : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[e]
      let hnT ← mkAppM ``LE.le #[← num (← mkAppM ``Rv64mc.Env.next #[env, m0]),
        ← num (← mkAppM ``Rv64mc.Env.next #[env, M])]
      let (hn, l) ← sideGoal g hnT (withArith (arithProve hnT))
      left := left ++ l
      h ← mkAppM ``Rv64mc.Windows.after #[h, hc, hn]
    unless t == top0 do
      let hleT ← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[t], ← mkAppM ``BitVec.toNat #[top0]]
      let (hle, l) ← sideGoal g hleT (withArith (arithProve hleT))
      left := left ++ l
      h ← mkAppM ``Rv64mc.Windows.callee #[h, hle]
    g.assign h
    return some left
  return none

mutual

/-- `Q` at a callee's stopping state, `∀ fr st r' m', Stop … → accept … → Q ⟨fr :: st, r', m'⟩`: by a hypothesis of
    that shape for the caller's own stopping set (`hstop`), whose stopping condition is closed from the callee's
    (`hs`, split into `hs_k`) where it can be, and left as a goal where it cannot. -/
partial def closeStop (g : MVarId) : MetaM (List MVarId) := do
  let saved ← saveState
  let (fvs, g1) ← g.introN 6 [`fr, `st, `r', `m', `hs, `ha]
  let r ← g1.withContext do
    let hs := mkFVar (fvs[4]!)
    let ha := mkFVar (fvs[5]!)
    let hsT ← instantiateMVars (← inferType hs)
    if (← whnfR hsT).isConstOf ``False then
      g1.assign (← mkFalseElim (← g1.getType) hs)
      return some []
    let goal ← instantiateMVars (← g1.getType)
    for d in ← getLCtx do
      if d.isImplementationDetail || fvs.contains d.fvarId then continue
      let dt ← instantiateMVars d.type
      unless dt.isForall do continue
      let s1 ← saveState
      let (xs, _, concl) ← forallMetaTelescopeReducing dt (some 6)
      if xs.size != 6 then s1.restore; continue
      unless ← withReducible (isDefEq concl goal) do s1.restore; continue
      unless ← withReducible (isDefEq (← inferType (xs[5]!)) (← inferType ha)) do s1.restore; continue
      (xs[5]!).mvarId!.assign ha
      let sT ← Core.betaReduce (← instantiateMVars (← inferType (xs[4]!)))
      let gs ← newGoal g1 sT
      (xs[4]!).mvarId!.assign gs
      g1.assign (← instantiateMVars (mkAppN d.toExpr xs))
      -- the callee's stopping condition, split, then the caller's from it
      let facts ← splitFact hs (← Core.betaReduce hsT)
      let (gs', _) ← addFacts gs.mvarId! `hs facts
      if ← gs'.withContext do
          let t ← instantiateMVars (← gs'.getType)
          let some h ← hypOf t | return false
          gs'.assign h
          return true then
        return some []
      return some (← closeSideT gs')
    return none
  match r with
  | some l => return l
  | none => saved.restore; return [g]

/-- `closeSide` for a total goal's side goals: `HoldsT`'s pre- and postconditions unfolded, `Windows` (`windowsGoal`),
    the code map kept (`codeWalk`), a window (`winProof`), a callee's stopping states (`closeStop`); the rest
    `closeSide`'s. -/
partial def closeSideT (g : MVarId) (split : Bool := false) : MetaM (List MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    let ga ← newGoal g a
    let gb ← newGoal g b
    g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
    return (← closeSideTSafe ga.mvarId! split) ++ (← closeSideTSafe gb.mvarId! split)
  if ty.isAppOf ``Rv64mc.HoldsT.pre || ty.isAppOf ``Rv64mc.HoldsT.post then
    let some ty' ← unfoldDefinition? ty | return [g]
    return ← closeSideT (← g.replaceTargetDefEq ty'.headBeta) split
  if ty.isAppOfArity ``Rv64mc.Windows 3 then return (← windowsGoal g ty).getD [g]
  if ty.isAppOfArity ``Eq 3 then
    let l := ty.appFn!.appArg!.consumeMData
    let r := ty.appArg!.consumeMData
    if l.isAppOfArity ``MachineState.code 1 && r.isAppOfArity ``MachineState.code 1 then
      if let some p ← codeWalk l.appArg! r.appArg! then
        g.assign p
        return []
      return [g]
    if l.isAppOfArity ``Rv64mc.inWindow 2 && r.isConstOf ``Bool.true then
      if let some n ← natVal? l.appArg! then
        if let some p ← winProof l.appFn!.appArg! n then
          g.assign p
          return []
  if let .forallE _ _ (.forallE _ _ (.forallE _ _ (.forallE _ _ (.forallE _ _ (.forallE _ acc _ _) _) _) _) _) _ := ty then
    if acc.isAppOf ``Lprog.Isa.accept then return ← closeStop g
  closeSideSafe g split

/-- `closeSideT`, out of recursion depth or heartbeats leaving the goal as it was. -/
partial def closeSideTSafe (g : MVarId) (split : Bool := false) : MetaM (List MVarId) := do
  let saved ← saveState
  tryCatchRuntimeEx (closeSideT g split) fun _ => do
    saved.restore
    return [g]

end

/-! ## Calls and returns -/

/-- A definition of a total contract (`HoldsT`, `Aborts`, a function's `…SpecT`) unfolded to the `Isa.TContract` it
    is. -/
partial def toTContract (ty : Expr) : MetaM Expr := do
  let ty := ty.consumeMData.headBeta
  if ty.isAppOf ``Lprog.Isa.TContract then return ty
  match ← unfoldDefinition? ty with
  | some ty' => toTContract ty'
  | none => return ty

/-- A total contract among those given for function `f`: its proof, `Pre`, `Post` and `Stop`. -/
def specForT (cfg : Cfg) (f : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  for (pf, ty) in cfg.specs do
    let (xs, _, ty) ← forallMetaTelescope ty
    let ty ← toTContract (← instantiateMVars ty)
    if ty.isAppOfArity ``Lprog.Isa.TContract 9 then
      let args := ty.getAppArgs
      if ← withReducible (isDefEq (args[5]!) f) then
        let pf ← instantiateMVars (mkAppN pf xs)
        if pf.hasExprMVar then continue
        return some (pf, ← instantiateMVars (args[6]!), ← instantiateMVars (args[7]!), ← instantiateMVars (args[8]!))
  return none

/-- After a call: `afterCall`'s hypotheses (`r<k>`, `m<k>`, `hret<k>_j`, `keep<k>_j`), and what they say of `r<k>`
    written into the register file. -/
def afterCallT (g : MVarId) (k : Nat) : MetaM (Option MVarId) := do
  let some g ← afterCall g k | return none
  g.withContext do
    let pre := s!"hret{k}_"
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let .str .anonymous s := d.userName then
        if s.startsWith pre then hs := hs.push d.toExpr
    some <$> absorbFactsT g hs (rv_sym.bind.get (← getOptions))

/-- The goal that the function has returned to its caller: closed by the contract's continuation in the context
    (`∀ r' m', Post … → Total p c G Q ⟨rest, r', m'⟩`), leaving the postcondition. -/
def finishT (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``Lprog.Isa.Total 7 do return none
  let s ← whnfR ty.appArg!
  unless s.isAppOfArity ``Lprog.State.mk 4 do return none
  let R := (s.getAppArgs[2]!)
  let M := (s.getAppArgs[3]!)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dt := (← instantiateMVars d.type).consumeMData
    let .forallE _ _ (.forallE _ _ (.forallE _ hpost body _) _) _ := dt | continue
    let body := body.consumeMData
    unless body.isAppOfArity ``Lprog.Isa.Total 7 do continue
    let s' := body.appArg!
    unless s'.isAppOfArity ``Lprog.State.mk 4 do continue
    let inst := body.instantiateRev #[R, M, mkConst ``True.intro]
    unless ← withReducible (isDefEq inst ty) do continue
    let postT := hpost.instantiateRev #[R, M]
    let gp ← newGoal g postT
    g.assign (mkApp3 d.toExpr R M gp)
    return some gp.mvarId!
  return none

/-- The type of the binder after the arguments given of a rule. -/
def nextBinder (c : Name) (args : List (Name × Expr)) : MetaM Expr := do
  let t ← whnfR (← inferType (← appN c args))
  let .forallE _ d _ _ := t | throwError "rv_symT: {c} takes no more arguments"
  Core.betaReduce (← instantiateMVars d)

/-! ## The executor -/

/-- A load's or store's address facts: in a window and aligned for its `n` bytes, and, for a store into `M`, over
    no code. -/
def accessFacts (g : MVarId) (x : Expr) (n : Nat) (store? : Option Expr) :
    MetaM (List (Name × Expr) × List MVarId) := do
  let xn ← mkAppM ``BitVec.toNat #[x]
  let (hw, l1) ← sideGoal g (← mkEq (← mkAppM ``Rv64mc.inWindow #[x, mkNatLit n]) (mkConst ``Bool.true))
    (winProof x n)
  let (hal, l2) ← sideGoal g (← mkEq (← mkAppM ``HMod.hMod #[xn, mkNatLit n]) (mkNatLit 0)) (alignProof x n)
  let some M := store? | return ([(`hw, hw), (`hal, hal)], l1 ++ l2)
  let ncT ← mkEq (← mkAppM ``RiscvZkvm.Rv64.noCodeAt #[M, x, mkNatLit n]) (mkConst ``Bool.true)
  let (hnc, l3) ← sideGoal g ncT (noCodeProof M n hw)
  return ([(`hw, hw), (`hal, hal), (`hnc, hnc)], l1 ++ l2 ++ l3)

/-- The width's bytes. -/
def widthBytes (w : Expr) : Option Nat :=
  if w.isConstOf ``Lprog.Width.b1 then some 1 else if w.isConstOf ``Lprog.Width.b2 then some 2
  else if w.isConstOf ``Lprog.Width.b4 then some 4 else if w.isConstOf ``Lprog.Width.b8 then some 8 else none

/-- One goal stepped as far as the rules go: the goals left. -/
partial def runT (cfg : Cfg) (g0 : MVarId) : MetaM (List MVarId) := do
  let mut todo : List (MVarId × List Nat × Option Expr) := [(g0, [], none)]
  let mut left : Array MVarId := #[]
  let mut calls := 0
  let mut steps := 0
  while !todo.isEmpty do
    let (g, seen, hd?) := todo.head!
    todo := todo.tail!
    let at? ← g.withContext do parseAtT (← g.getType)
    let some a := at?
      | let gp? ← finishT g
        if let some gp := gp? then left := left ++ (← closeSideTSafe gp) else left := left.push g
        continue
    if ((cfg.stops.contains a.pc || cfg.heads.contains a.pc) && g != g0) || seen.contains a.pc then
      trace[rv_sym] "left at {a.pc}: a stop or a loop's head"
      left := left.push g; continue
    let seen := a.pc :: seen
    let some ins := cfg.body[a.pc]? | left := left.push g; continue
    let ins := ins.consumeMData
    let common := commonT a cfg.fd
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
      -- a rule whose one continuation is the next instruction's goal at `R'` and `M'`, after the side goals
      let fall (c : Name) (R' M' : Expr) (xs : List (Name × Expr)) (side : List MVarId) :
          MetaM (Option (List MVarId)) := do
        let h ← newGoal g (a.goal (a.pc + 1) R' M')
        g.assign (← appN c (base ++ xs ++ [(`h, h)]))
        return some (side ++ [h.mvarId!])
      -- a call or tail call through a total contract: the side goals, `hstop`, then after the return
      let viaContract (c : Name) (pre : List (Name × Expr)) (side : MetaM (List MVarId)) :
          MetaM (Option (List MVarId)) := do
        let hstop ← newGoal g (← nextBinder c pre)
        let hk ← newGoal g (← nextBinder c (pre ++ [(`hstop, hstop)]))
        g.assign (← appN c (pre ++ [(`hstop, hstop), (`hk, hk)]))
        let side := (← side) ++ (← closeSideTSafe hstop.mvarId!)
        return some (side ++ (← afterCallT hk.mvarId! k).toList)
      match ins.getAppFn.constName? with
      | some ``Lprog.LinstrR.Llabel =>
        fall ``Rv64mc.Tactic.stepT_label a.R a.M [(`kd, (args[2]!)), (`l, (args[3]!))] []
      | some ``Lprog.LinstrR.Lgoto =>
        let some l ← evalNat (args[2]!) | pure none
        let some j ← labelIdx? cfg.body l | pure none
        let h ← newGoal g (a.goal j a.R a.M)
        g.assign (← appN ``Rv64mc.Tactic.stepT_goto (base ++ [(`l, (args[2]!)), (`j, mkNatLit j),
          (`hl, ← mkEqRefl (← mkAppM ``Option.some #[mkNatLit j])), (`h, h)]))
        pure (some [h.mvarId!])
      | some ``Lprog.LinstrR.Lopn =>
        let op := (args[2]!).consumeMData
        let oargs := op.getAppArgs
        match op.getAppFn.constName? with
        | some ``Lprog.Op.set =>
          let (v, hv) ← evalE a.R (oargs[2]!)
          let (R', hR) ← writeReg a.R (oargs[1]!) v
          fall ``Rv64mc.Tactic.stepT_set R' a.M [(`rd, (oargs[1]!)), (`e, (oargs[2]!)), (`v, v), (`R', R'),
            (`hv, hv), (`hR, hR)] []
        | some ``Lprog.Op.load =>
          let w := (oargs[2]!).consumeMData
          let s := (oargs[3]!).consumeMData
          let some nb := widthBytes w | pure none
          let (x, ha) ← evalE a.R (oargs[4]!)
          let (acc, side) ← accessFacts g x nb none
          let load (c : Name) (v hv : Expr) (xs : List (Name × Expr)) : MetaM (Option (List MVarId)) := do
            let (R', hR) ← writeReg a.R (oargs[1]!) v
            fall c R' a.M (xs ++ [(`rd, (oargs[1]!)), (`a, (oargs[4]!)), (`x, x), (`v, v), (`R', R'), (`ha, ha),
              (`hv, hv), (`hR, hR)] ++ acc) side
          if w.isConstOf ``Lprog.Width.b8 && s.isConstOf ``Bool.false then
            let (v, pv) ← match ← dataRead a.M x with
              | some (v, p) => pure (v, some p)
              | none => readMem a.M x
            load ``Rv64mc.Tactic.stepT_ld v (← orRefl pv v) []
          else
            -- the value `if s then sext lv else lv` of a read `lv` of `loadVal w M x`, and its proof
            let sext (t : Expr) : Expr := mkApp2 (mkConst ``UnOp.eval) (mkApp (mkConst ``UnOp.sext) w) t
            let pick (t : Expr) : Expr := if s.isConstOf ``Bool.true then sext t else t
            let choose (t : Expr) : MetaM Expr := do mkAppM ``ite #[← mkEq s (mkConst ``Bool.true), sext t, t]
            let lvM := mkApp3 (mkConst ``Rv64mc.Tactic.loadVal) w a.M x
            let (val, hv) ← do
              if let some r ← (if ← heapOn then dataLoad a.M x w s else pure none) then pure r
              else if let some (bv, pb) ← (do
                  unless (← heapOn) && w.isConstOf ``Lprog.Width.b1 do return none
                  let (bv, pb?) ← readByte a.M x
                  let some pb := pb? | return none
                  return some (bv, pb)) then
                let ext (t : Expr) : Expr := mkApp3 (mkConst ``BitVec.zeroExtend) (mkRawNatLit 8) (mkRawNatLit 64) t
                let lv := ext bv
                let p1 ← mkExpectedTypeHint
                  (← mkCongrArg (← lam (mkApp (mkConst ``BitVec) (mkRawNatLit 8)) (pure ∘ ext)) pb) (← mkEq lvM lv)
                pure (pick lv, ← mkExpectedTypeHint (← mkCongrArg (← lam word choose) p1)
                  (← mkEq (← choose lvM) (pick lv)))
              else
                let lv ← whnfCore (← unfoldDefinition lvM)
                pure (pick lv, ← mkExpectedTypeHint (← mkEqRefl (pick lv)) (← mkEq (← choose lvM) (pick lv)))
            load ``Rv64mc.Tactic.stepT_loadw val hv [(`w, w), (`s, s)]
        | some ``Lprog.Op.store =>
          let w := (oargs[1]!).consumeMData
          let some nb := widthBytes w | pure none
          let (x, ha) ← evalE a.R (oargs[2]!)
          let (v, hv) ← evalE a.R (oargs[3]!)
          let (acc, side) ← accessFacts g x nb (some a.M)
          let xs := [(`a, (oargs[2]!)), (`e, (oargs[3]!)), (`x, x), (`v, v), (`ha, ha), (`hv, hv)] ++ acc
          if w.isConstOf ``Lprog.Width.b8 then
            fall ``Rv64mc.Tactic.stepT_sd a.R (← mkAppM ``MachineState.setMem #[a.M, x, v]) xs side
          else
            let m' ← whnfCore (← unfoldDefinition (mkApp4 (mkConst ``Rv64mc.Tactic.storeMem) w a.M x v))
            fall ``Rv64mc.Tactic.stepT_storew a.R m' ((`w, w) :: xs) side
        | some ``Lprog.Op.skip => fall ``Rv64mc.Tactic.stepT_skip a.R a.M [] []
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
            return some (Sym.mkLit (i % 2 ^ 64).toNat)
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
        g.assign (← appN ``Rv64mc.Tactic.stepT_cmp (base ++ [(`op, opS), (`a, (cargs[2]!)), (`b, (cargs[3]!)),
          (`l, (args[3]!)), (`j, mkNatLit j), (`x, x), (`y, y),
          (`hl, ← mkEqRefl (← mkAppM ``Option.some #[mkNatLit j])),
          (`ha, ← opndProof (cargs[2]!) x), (`hb, ← opndProof (cargs[3]!) y),
          (`hs, ← mkEqRefl tru), (`ht, gt), (`hn, gn)]))
        let (hct, gt') ← gt.mvarId!.intro `hc
        let (hcn, gn') ← gn.mvarId!.intro `hc
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
          pure (some [← Sym.nameApart live])
        else
        pure (some [← Sym.nameApart gt', ← Sym.nameApart gn'])
      | some ``Lprog.LinstrR.Lcall =>
        let ret := (args[2]!)
        let tgt := (args[3]!)
        let some f ← targetIdx tgt
          | trace[rv_sym] "at {a.pc}: the call's target names no single function"; return none
        let some (hcon, Pre, Post, Stop) ← specForT cfg f
          | trace[rv_sym] "at {a.pc}: no total contract for function {f}"; return none
        let some hc ← calleeProof cfg a.R tgt f
          | trace[rv_sym] "at {a.pc}: the facts given do not show that the call reaches {f}"; return none
        let sp := mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x2)
        let R1 := mkApp5 (mkConst ``Lprog.updReg) (mkConst ``RiscvZkvm.Rv64.Reg)
          (mkConst ``RiscvZkvm.Rv64.instDecidableEqReg) a.R (mkConst ``RiscvZkvm.Rv64.Reg.x1) ret
        let hpre ← newGoal g (mkApp4 Pre ret sp R1 a.M).headBeta
        let pre := base ++ [(`ret, ret), (`tgt, tgt), (`f, f), (`Pre, Pre), (`Post, Post), (`Stop, Stop),
          (`hcon, hcon), (`hc, hc), (`hpre, hpre)]
        viaContract ``Rv64mc.Tactic.stepT_call pre (closeSideTSafe hpre.mvarId! (split := true))
      | some ``Lprog.LinstrR.Ltail =>
        let tgt := args[2]!
        let some f ← targetIdx tgt
          | trace[rv_sym] "at {a.pc}: the tail call's target names no single function"; return none
        let some (hcon, Pre, Post, Stop) ← specForT cfg f
          | trace[rv_sym] "at {a.pc}: no total contract for function {f}"; return none
        let some hc ← calleeProof cfg a.R tgt f
          | trace[rv_sym] "at {a.pc}: the facts given do not show that the tail call reaches {f}"; return none
        let hsp ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x2)) a.top)
        let hpre ← newGoal g (mkApp4 Pre a.rv a.top a.R a.M).headBeta
        let pre := base ++ [(`tgt, tgt), (`f, f), (`Pre, Pre), (`Post, Post), (`Stop, Stop), (`hcon, hcon),
          (`hc, hc), (`hsp, hsp), (`hpre, hpre)]
        viaContract ``Rv64mc.Tactic.stepT_tail pre
          (do return (← closeSideTSafe hsp.mvarId!) ++ (← closeSideTSafe hpre.mvarId! (split := true)))
      | some ``Lprog.LinstrR.Lret =>
        let h ← newGoal g (mkAppN a.head (a.pre.push (mkApp3 a.stMk a.rest a.R a.M)))
        let hra ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x1)) a.rv)
        let hsp ← newGoal g (← mkEq (mkApp a.R (mkConst ``RiscvZkvm.Rv64.Reg.x2)) a.top)
        g.assign (← appN ``Rv64mc.Tactic.stepT_ret (base ++ [(`hra, hra), (`hsp, hsp), (`h, h)]))
        let side := (← closeSideSafe hra.mvarId!) ++ (← closeSideSafe hsp.mvarId!)
        pure (some (side ++ [h.mvarId!]))
      | _ => pure none
    match step with
    | none =>
      trace[rv_sym] "left at {a.pc}: no rule applies to {ins}"
      left := left.push g
    | some gs =>
      steps := steps + 1
      let next ← gs.mapM fun g' => do
        let pc' ← g'.withContext do return (← parseAtT (← g'.getType)).map (·.pc)
        return (g', seen, if pc' == some (a.pc + 1) then some hdNext else none)
      todo := next ++ todo
  trace[rv_sym] "{steps} instructions stepped, {left.size} goals left"
  return left.toList

/-! ## The tactics -/

/-- **`rv_symT hp stop [pcs] with [facts] using [contracts]`**: step the total goal `Total … ⟨⟨fn, pc, …⟩ :: …⟩`
    through the body of the template `hp : p[fn]? = some fd` names, calls through the total contracts given. -/
syntax (name := rvSymT) "rv_symT " term rvSymArgs : tactic

@[tactic rvSymT] def evalRvSymT : Tactic := fun stx => do
  arithCache.set {}
  let cfg ← elabArgs stx[1] stx[2]
  let g ← getMainGoal
  let left ← runT cfg g
  replaceMainGoal left

/-- The precondition's facts as hypotheses `hpre_k`, the stopping hypothesis `hstop` (its stopping set applied) and
    the continuation `hk`, and what the facts say of the entry's registers written into the register file. -/
def openContractT (g : MVarId) : MetaM MVarId := do
  let ty ← toTContract (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Lprog.Isa.TContract 9 do throwError "rv_autoT: the goal is not a total contract"
  let g ← g.replaceTargetDefEq ty
  let (fvs, g) ← g.introN 9 [`Q, `ret, `top, `rest, `regs, `m, `hpre, `hstop, `hk]
  let g ← g.withContext do
    g.replaceLocalDeclDefEq (fvs[7]!) (← Core.betaReduce (← instantiateMVars (← (fvs[7]!).getType)))
  g.withContext do
    let pre := mkFVar (fvs[6]!)
    let facts ← splitFact pre (← inferType pre)
    let (g, hs) ← addFacts g `hpre facts
    let g ← g.tryClear (fvs[6]!)
    absorbFactsT g (hs.map mkFVar)

/-- **`rv_autoT hp stop [pcs] with [facts] using [contracts]`**: a total contract (`HoldsT`, or a definition unfolding
    to `rvIsa.TContract p c (WinOk p) fn Pre Post Stop`) for the template `hp : p[fn]? = some fd`, stepped from the
    entry as `rv_auto` steps a partial one. What is left is `rv_auto`'s, and the side goals `rv_symT` does not close:
    an address's window or alignment, a callee's `Windows`, `Q` at a callee's stopping state not in the function's. -/
syntax (name := rvAutoT) "rv_autoT " term rvSymArgs : tactic

@[tactic rvAutoT] def evalRvAutoT : Tactic := fun stx => do
  arithCache.set {}
  let g ← openContractT (← getMainGoal)
  replaceMainGoal [g]
  let cfg ← elabArgs stx[1] stx[2]
  let g ← if ← heapOn then g.withContext do
      let fs := cfg.facts.filter fun (_, ty) => !ty.consumeMData.isAppOf ``Eq
      if fs.isEmpty then pure g else pure (← addFacts g `hwith fs).1
    else pure g
  let left ← runT cfg g
  replaceMainGoal left

/-- **`rv_introT h`**: `rv_intro` for a total goal. -/
syntax (name := rvIntroT) "rv_introT " ident : tactic

@[tactic rvIntroT] def evalRvIntroT : Tactic := fun stx => do
  let g ← getMainGoal
  let g ← g.withContext do
    let h ← getFVarId stx[1]
    let facts ← splitFact (mkFVar h) (← h.getType)
    let (g, hs) ← addFacts g (← h.getUserName) facts
    let g ← g.tryClear h
    absorbFactsT g (hs.map mkFVar)
  replaceMainGoal [g]

/-- **`rv_closeT`**: on every goal, what `rv_autoT` closes of a side goal. -/
syntax (name := rvCloseT) "rv_closeT" : tactic

@[tactic rvCloseT] def evalRvCloseT : Tactic := fun _ => do
  let gs ← getGoals
  let mut left := #[]
  for g in gs do
    if ← g.isAssigned then continue
    left := left ++ (← closeSideTSafe g)
  setGoals left.toList

end Rv64mc.Tactic.SymT
