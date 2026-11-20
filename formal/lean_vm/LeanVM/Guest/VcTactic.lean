/-
  LeanVM.Guest.VcTactic

  `vc`: a concrete core function's relation rewritten to its forward condition, computed and
  proved one statement at a time.
-/

module

public import LeanVM.Guest.Vc
public meta import Lean.Elab.Tactic.Simp

/-!
# The `vc` tactic

`vc [rules]` rewrites the first `Fn.Sem C rd f args rets` of the goal, `f` a concrete function
(`fn% «name»`), to the condition `Fn.sem_iff_wp` gives, computed: no valuation, an existential
word for each value read before it is defined (named `x{k}` after `V.n k`), every other read
replaced by its word, and `rules` applied.

It walks the body once, a statement at a time, the environment of defined values kept as a table.
For each statement:

1. its equation (`wp_atom`, `wp_ite`, ...) at an environment `ρ₀` and a continuation `k₀` that are
   free variables, and every block it contains (a branch, an arm) another free variable `ℓ`;
2. the reads unfolded on that equation's right side by the table: a defined value's word, or an
   existential that defines it; the atom's relation on the words read (`Atom.rel`) reduced. The
   kernel checks this step by definitional unfolding, which only reduces the IR (`getv`, lookups
   in the table `Defs`, `Atom.vars`, `Atom.rel`'s match), never a word, since the words are the
   table's own terms on both sides;
3. `simp only` with the elimination lemmas (`exists_eq_left`, ...) and `rules` on that small term,
   so a value defined by an equation (a constant, a sum, a product, a copy, a permutation's cells
   by a rule) is substituted; the table's words are held abstract meanwhile, so neither they nor
   the rest of the body are visited;
4. at each occurrence of `k₀ ρ'` or `ℓ ρ'` in the result, `ρ'` read as the definitions added and
   rewritten to an `Env.ofDefs` table (`Env.upd_ofDefs`), in which the kernel looks a value up in
   a step per bit of its index, the rest of the block (or the branch) computed the same way, then
   put back by congruence.

So no `simp` call and no recursion the elaborator bounds (`maxRecDepth`) grows with the body: each
statement costs one small `simp` and lemma applications. The metaprogram itself recurses a level
per statement, and abstracting each existential over the rest of the condition and its proof
costs time in the size of that rest. A sequence of branches duplicates what follows them, once
per branch, as the condition itself does. The kernel checks the whole proof; the tactic does not
type-check it itself, so `lake-build.py --dev` keeps the kernel on in every module that uses it.
-/

public meta section

namespace LeanVM.Guest.Core.VcTactic

open Lean Meta Elab Tactic LeanVM.Parameters

/-! ## Values and the table of definitions -/

/-- A value: its path, and its tag and index as numerals. -/
structure Key where
  path : Expr
  tag : Nat
  idx : Nat
  deriving BEq, Hashable

/-- The words of the values defined so far. -/
abbrev Vals := Std.HashMap Key Expr

/-- A numeral a term reduces to. -/
def natOf (e : Expr) : MetaM Nat := do
  match ← (evalNat (← whnfD e)).run with
  | some n => return n
  | none => throwError "vc: not a numeral{indentExpr e}"

def keyOf (v : Expr) : MetaM Key := do
  let w ← whnfD v
  unless w.isAppOfArity ``V.mk 3 do throwError "vc: not a value{indentExpr v}"
  let a := w.getAppArgs
  return ⟨← instantiateMVars a[0]!, ← natOf a[1]!, ← natOf a[2]!⟩

/-- The name of a value's existential: `x{k}` for `V.n k`. -/
def binderName (v : Expr) : MetaM Name := return .mkSimple s!"x{(← keyOf v).idx}"

/-- The elements of a list literal, its tails reduced one at a time. -/
partial def toList (e : Expr) : MetaM (List Expr) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then return e.appFn!.appArg! :: (← toList e.appArg!)
  throwError "vc: not a list literal{indentExpr e}"

def eTy : Expr := mkConst ``E
def envTy : Expr := mkConst ``Env
def propTy : Expr := mkSort Level.zero
def contTy : Expr := mkForall `ρ .default envTy propTy
def listTy : Expr := mkApp (mkConst ``List [Level.zero]) eTy

def ofDefs (t : Expr) : Expr := mkApp (mkConst ``Env.ofDefs) t

/-- `e` with every head redex reduced. -/
partial def headBetaAll (e : Expr) : Expr :=
  if e.getAppFn.isLambda then headBetaAll e.headBeta else e

/-- `Atom.rel rd a ws`, its match reduced to the atom's case. -/
def reduceRel (e : Expr) : MetaM Expr := do
  let some e' ← unfoldDefinition? e | throwError "vc: cannot unfold{indentExpr e}"
  match ← reduceMatcher? e'.headBeta with
  | .reduced r => return r.headBeta
  | _ => throwError "vc: cannot reduce{indentExpr e}"

/-! ## The computation -/

/-- What every statement's condition shares: the call relation, the reader, the return
condition, and the rewriting of each statement's condition. -/
structure Ctx where
  C : Expr
  rd : Expr
  kret : Expr
  simpCtx : Simp.Context
  simprocs : Simp.SimprocsArray

abbrev M := ReaderT Ctx MetaM

def Ctx.wp (ctx : Ctx) (s ρ Q : Expr) : Expr :=
  mkApp6 (mkConst ``Stmt.wp) ctx.C ctx.rd ctx.kret s ρ Q

def Ctx.wpList (ctx : Ctx) (ss ρ Q : Expr) : Expr :=
  mkApp6 (mkConst ``Stmt.wpList) ctx.C ctx.rd ctx.kret ss ρ Q

/-- The rest of a condition: its value, and its condition at the table and environment given
(a proposition `P` and a proof of `value ρ ↔ P`). -/
structure Rest where
  value : Expr
  run : Vals → Expr → M (Expr × Expr)

instance : Inhabited Rest := ⟨⟨default, fun _ _ => throwError "vc: no rest"⟩⟩

/-- The term `e` (reads, relations, the blocks `blocks` as `wpList` and the continuation as an
application of `k₀`) with its reads unfolded by `vals`, each block `blocks[i]` replaced by its
free variable `ℓs[i]`. -/
partial def unfoldReads (blocks : Array Expr) (ℓs : Array Expr) (vals : Vals) (e : Expr) :
    MetaM Expr := do
  let e := headBetaAll e
  let go := unfoldReads blocks ℓs
  match e.getAppFnArgs with
  | (``getv, #[ρ, v, Q]) =>
    let key ← keyOf v
    match vals[key]? with
    | some w => go vals (Q.beta #[ρ, w])
    | none =>
      withLocalDeclD (← binderName v) eTy fun y => do
        let body ← go (vals.insert key y) (Q.beta #[mkApp3 (mkConst ``Env.upd) ρ v y, y])
        return mkApp2 (mkConst ``Exists [Level.one]) eTy (← mkLambdaFVars #[y] body)
  | (``getvs, #[ρ, vs, Q]) =>
    match ← toList vs with
    | [] => go vals (Q.beta #[ρ, mkApp (mkConst ``List.nil [Level.zero]) eTy])
    | v :: rest =>
      -- `getvs ρ (v :: vs) Q = getv ρ v fun ρ x => getvs ρ vs fun ρ xs => Q ρ (x :: xs)`
      let restE ← mkListLit (mkConst ``V) rest
      let inner := mkLambda `ρ .default envTy <| mkLambda `x .default eTy <|
        mkApp3 (mkConst ``getvs) (.bvar 1) restE <|
          mkLambda `ρ .default envTy <| mkLambda `xs .default listTy <|
            mkApp2 Q (.bvar 1) (mkApp3 (mkConst ``List.cons [Level.zero]) eTy (.bvar 2) (.bvar 0))
      go vals (mkApp3 (mkConst ``getv) ρ v inner)
  | (``Atom.rel, #[_, _, _]) => reduceRel e
  | (``armsDisj, #[xv, j, ps]) =>
    let ps ← whnfD ps
    if ps.isAppOfArity ``List.nil 1 then return mkConst ``False
    unless ps.isAppOfArity ``List.cons 3 do throwError "vc: arms not a list{indentExpr ps}"
    let ty ← instantiateForall (← inferType (mkConst ``armsDisj_cons))
      #[xv, j, ps.appFn!.appArg!, ps.appArg!]
    go vals ty.appArg!
  | (``Stmt.wpList, #[_, _, _, z, ρ, _]) =>
    match blocks.findIdx? (· == z) with
    | some i => return mkApp ℓs[i]! ρ
    | none => throwError "vc: unexpected block{indentExpr z}"
  | (``And, #[a, b]) | (``Or, #[a, b]) =>
    return mkApp2 e.appFn!.appFn! (← go vals a) (← go vals b)
  | (``Exists, #[α, .lam n d b bi]) =>
    withLocalDecl n bi d fun x => do
      return mkApp2 e.getAppFn α (← mkLambdaFVars #[x] (← go vals (b.instantiate1 x)))
  | _ =>
    match e with
    | .forallE n d b bi =>
      withLocalDecl n bi (← go vals d) fun x => do mkForallFVars #[x] (← go vals (b.instantiate1 x))
    | _ => return e

/-- The value an environment `Env.upd … v #i …` defines as the loose variable `#i`. -/
partial def envDefOf? (ρ : Expr) (i : Nat) : Option Expr :=
  if ρ.isAppOfArity ``Env.upd 3 then
    if ρ.appArg! == .bvar i then some ρ.appFn!.appArg! else envDefOf? ρ.appFn!.appFn!.appArg! i
  else none

/-- The value the loose variable `#i` defines in an environment of a rest under the connectives of
`e` (`∧`, `∨`, `→`, `∃`, `∀`), the words in between not visited. -/
partial def defOf? (e : Expr) (i : Nat) : Option Expr :=
  match e with
  | .app (.fvar _) ρ => envDefOf? ρ i
  | .forallE _ _ b _ => defOf? b (i + 1)
  | _ =>
    match e.getAppFnArgs with
    | (``And, #[a, b]) | (``Or, #[a, b]) => defOf? a i <|> defOf? b i
    | (``Exists, #[_, .lam _ _ b _]) => defOf? b (i + 1)
    | _ => none

/-- Each existential's variable named after the value it defines (a rewrite may rename it). -/
partial def fixNames (e : Expr) : MetaM Expr := do
  match e with
  | .forallE n d b bi => return .forallE n d (← fixNames b) bi
  | _ =>
    match e.getAppFnArgs with
    | (``And, #[a, b]) | (``Or, #[a, b]) =>
      return mkApp2 e.appFn!.appFn! (← fixNames a) (← fixNames b)
    | (``Exists, #[α, .lam n d b bi]) =>
      let n ← match defOf? b 0 with
        | some v => binderName v
        | none => pure n
      return mkApp2 e.appFn!.appFn! α (.lam n d (← fixNames b) bi)
    | _ => return e

/-- `Defs.insert t v x k n` evaluated, `t` a literal table: the kernel then reads a value in a
table already built, rather than replaying the insertions that built it. -/
partial def insertDefs (t v x : Expr) (k n : Nat) : Expr :=
  let (h, z, o) := match t.getAppFnArgs with
    | (``Defs.node, #[h, z, o]) => (h, z, o)
    | _ => (mkApp (mkConst ``List.nil [Level.zero]) entryTy, mkConst ``Defs.nil, mkConst ``Defs.nil)
  if n == 0 || k == 0 then
    mkApp3 (mkConst ``Defs.node) (mkApp3 (mkConst ``List.cons [Level.zero]) entryTy
      (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``V) eTy v x) h) z o
  else if k % 2 == 0 then mkApp3 (mkConst ``Defs.node) h (insertDefs z v x (k / 2) (n - 1)) o
  else mkApp3 (mkConst ``Defs.node) h z (insertDefs o v x (k / 2) (n - 1))
where entryTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``V) eTy

/-- The definitions an environment adds to `ρ₀`, innermost first. -/
partial def envDefs (ρ₀ : Expr) (e : Expr) (acc : List (Expr × Expr) := []) :
    MetaM (List (Expr × Expr)) := do
  if e == ρ₀ then return acc
  match e.getAppFnArgs with
  | (``Env.upd, #[r, v, x]) => envDefs ρ₀ r ((v, x) :: acc)
  | _ => throwError "vc: unexpected environment{indentExpr e}"

def iffTrans (a b c h₁ h₂ : Expr) : Expr := mkApp5 (mkConst ``Iff.trans) a b c h₁ h₂

def iffRfl (a : Expr) : Expr := mkApp (mkConst ``Iff.rfl) a

/-- `a ↔ P` from `h : a = b` and `hP : b ↔ P`. -/
def eqIff (a b P h hP : Expr) : Expr := iffTrans a b P (mkApp3 (mkConst ``Iff.of_eq) a b h) hP

/-- The condition of `e`, a statement's rewritten condition whose free variables `fvars`
(environment, continuation, blocks, words) stand for `values`, and among them `leaves` (the
continuation and the blocks) for `rests`: congruence down to each occurrence `ℓ ρ'` of a leaf,
where the rest is computed. Returns `P` and a proof of `e[fvars := values] ↔ P`. -/
partial def assemble (ρ₀ ρ : Expr) (fvars values leaves : Array Expr) (rests : Array Rest)
    (vals : Vals) (e : Expr) : M (Expr × Expr) := do
  let inst (t : Expr) : Expr := t.replaceFVars fvars values
  let go := assemble ρ₀ ρ fvars values leaves rests vals
  -- under a binder: its type, the body before and after as functions, and their equivalence
  let under (n : Name) (bi : BinderInfo) (d b : Expr) : M (Level × Expr × Expr × Expr × Expr) := do
    let d := inst d
    withLocalDecl n bi d fun x => do
      let (pb, hb) ← go (b.instantiate1 x)
      return (← getLevel d, d, ← mkLambdaFVars #[x] (inst (b.instantiate1 x)),
        ← mkLambdaFVars #[x] pb, ← mkLambdaFVars #[x] hb)
  if !e.hasAnyFVar (leaves.map (·.fvarId!)).contains then
    let ei := inst e
    return (ei, iffRfl ei)
  if let .app (.fvar f) arg := e then
    if let some i := leaves.findIdx? (· == .fvar f) then
      -- `arg[ρ₀ := ρ] = Env.ofDefs T`, `ρ = Env.ofDefs T₀`, a definition at a time
      let mut vals' := vals
      let mut env := ρ
      let mut T := ρ.appArg!
      let mut h := mkApp2 (mkConst ``Eq.refl [Level.one]) envTy ρ
      for (v, x) in ← envDefs ρ₀ arg do
        let x := inst x
        let k ← keyOf v
        vals' := vals'.insert k x
        let upd (r : Expr) := mkApp3 (mkConst ``Env.upd) r v x
        let T' := insertDefs T v x k.idx 64
        let hc := mkAppN (mkConst ``congrArg [Level.one, Level.one])
          #[envTy, envTy, env, ofDefs T, .lam `r envTy (upd (.bvar 0)) .default, h]
        h := mkAppN (mkConst ``Eq.trans [Level.one])
          #[envTy, upd env, upd (ofDefs T), ofDefs T', hc, mkApp3 (mkConst ``Env.upd_ofDefs) T v x]
        env := upd env
        T := T'
      let (P, hP) ← rests[i]!.run vals' (ofDefs T)
      if env == ρ then return (P, hP)
      let value := rests[i]!.value
      let hv := mkAppN (mkConst ``congrArg [Level.one, Level.one])
        #[envTy, propTy, env, ofDefs T, value, h]
      return (P, eqIff (value.beta #[env]) (value.beta #[ofDefs T]) P hv hP)
  match e.getAppFnArgs with
  | (``And, #[a, b]) | (``Or, #[a, b]) =>
    let (pa, ha) ← go a
    let (pb, hb) ← go b
    let congr := if e.isAppOf ``And then ``and_congr else ``or_congr
    return (mkApp2 e.appFn!.appFn! pa pb, mkAppN (mkConst congr) #[inst a, pa, inst b, pb, ha, hb])
  | (``Exists, #[_, .lam n d b bi]) =>
    let (u, d, p, q, h) ← under n bi d b
    return (mkApp2 (mkConst ``Exists [u]) d q, mkAppN (mkConst ``exists_congr [u]) #[d, p, q, h])
  | _ =>
    match e with
    | .forallE n d b bi =>
      if b.hasLooseBVars then
        let (u, d, p, q, h) ← under n bi d b
        return (.forallE n d q.bindingBody! bi, mkAppN (mkConst ``forall_congr' [u]) #[d, p, q, h])
      else
        let (pd, hd) ← go d
        let (pb, hb) ← go b
        return (.forallE n pd pb bi, mkAppN (mkConst ``imp_congr) #[inst d, inst b, pd, pb, hd, hb])
    | _ => throwError "vc: a block or the rest of the body under{indentExpr e}"

/-- The table's words in `e` that are not variables, outermost first. -/
partial def wordsIn (table : Std.HashSet Expr) (e : Expr)
    (acc : Array Expr × Std.HashSet Expr := (#[], {})) : Array Expr × Std.HashSet Expr :=
  if table.contains e then if acc.2.contains e then acc else (acc.1.push e, acc.2.insert e)
  else match e with
    | .app f a => wordsIn table a (wordsIn table f acc)
    | .lam _ d b _ | .forallE _ d b _ => wordsIn table b (wordsIn table d acc)
    | .mdata _ b => wordsIn table b acc
    | _ => acc

/-- The condition of `rhs`, a term in the free environment `ρ₀` and continuation `k₀` whose blocks
are `blocks`: its reads unfolded by `vals`, rewritten, and every block and the continuation
computed. `ρ₀`, `k₀` and the blocks stand for `ρ`, `cont.value` and `blockRests`' values.
Returns `P` and a proof of `rhs[ρ₀ := ρ, k₀ := cont.value] ↔ P`. -/
def condOf (ρ₀ k₀ : Expr) (ρ : Expr) (cont : Rest) (blocks : Array Expr)
    (blockRests : Array Rest) (vals : Vals) (rhs : Expr) : M (Expr × Expr) := do
  let ctx ← read
  withLocalDecls (blocks.map fun _ => (`ℓ, .default, fun _ => pure contTy)) fun ℓs => do
    let raw ← unfoldReads blocks ℓs vals rhs
    -- the table's words held abstract, so that nothing below visits them
    let table : Std.HashSet Expr := vals.fold (init := {}) fun s _ w =>
      if w.isFVar then s else s.insert w
    let ws := (wordsIn table raw).1
    withLocalDecls (ws.map fun _ => (`w, .default, fun _ => pure eTy)) fun wfs => do
      let m : Std.HashMap Expr Expr := (ws.zip wfs).foldl (init := {}) fun m (w, f) => m.insert w f
      let rawG := raw.replace m.get?
      let (r, _) ← Meta.simp rawG ctx.simpCtx ctx.simprocs
      let sgG ← fixNames r.expr
      let fvars := #[ρ₀, k₀] ++ ℓs ++ wfs
      let values := #[ρ, cont.value] ++ blockRests.map (·.value) ++ ws
      let (P, hP) ← assemble ρ₀ ρ fvars values (#[k₀] ++ ℓs) (#[cont] ++ blockRests) vals sgG
      let rhsI := rhs.replaceFVars #[ρ₀, k₀] #[ρ, cont.value]
      let rawI := rawG.replaceFVars fvars values
      let sgI := sgG.replaceFVars fvars values
      -- the reads: by definitional unfolding of the IR
      let h₁ ← mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [Level.one]) propTy rawI)
        (mkApp3 (mkConst ``Eq [Level.one]) propTy rhsI rawI)
      let h₂ := (← r.getProof).replaceFVars fvars values
      let h := mkApp6 (mkConst ``Eq.trans [Level.one]) propTy rhsI rawI sgI h₁ h₂
      return (P, eqIff rhsI sgI P h hP)

mutual
/-- The rest `ss` then `Q`: `fun ρ => Stmt.wpList C rd kret ss ρ Q.value`, computed by `vcBlock`. -/
partial def blockRest (ctx : Ctx) (ss : Expr) (Q : Rest) : Rest :=
  ⟨mkLambda `ρ .default envTy (ctx.wpList ss (.bvar 0) Q.value), fun vals ρ => vcBlock ss vals ρ Q⟩

/-- The condition of statement `s` at the table `vals` and environment `ρ`, `K` the rest of its
block: `P` and a proof of `Stmt.wp C rd kret s ρ K.value ↔ P`. -/
partial def vcStmt (s : Expr) (vals : Vals) (ρ : Expr) (K : Rest) : M (Expr × Expr) := do
  let ctx ← read
  let s' ← whnfD s
  let (eqn, args, blocks) ← match s'.getAppFnArgs with
    | (``Stmt.atom, #[a]) => pure (``wp_atom, #[a], #[])
    | (``Stmt.ite, #[c, z, n]) => pure (``wp_ite, #[c, z, n], #[z, n])
    | (``Stmt.match_, #[x, arms]) => pure (``wp_match, #[x, arms], (← toList arms).toArray)
    | (``Stmt.call, #[f, as, rs]) => pure (``wp_call, #[f, as, rs], #[])
    | (``Stmt.callIf, #[c, f, as]) => pure (``wp_callIf, #[c, f, as], #[])
    | (``Stmt.dispatch, #[x, fs, as, rs]) => pure (``wp_dispatch, #[x, fs, as, rs], #[])
    | (``Stmt.ret, #[vs]) => pure (``wp_ret, #[vs], #[])
    | _ => throwError "vc: not a statement{indentExpr s'}"
  let base := #[ctx.C, ctx.rd, ctx.kret]
  withLocalDeclD `ρ envTy fun ρ₀ => withLocalDeclD `k contTy fun k₀ => do
    let ty ← instantiateForall (← inferType (mkConst eqn)) (base ++ #[ρ₀, k₀] ++ args)
    let rhs := ty.appArg!
    let (P, hP) ← condOf ρ₀ k₀ ρ K blocks (blocks.map (blockRest ctx · K)) vals rhs
    return (P, eqIff (ctx.wp s ρ K.value) (rhs.replaceFVars #[ρ₀, k₀] #[ρ, K.value]) P
      (mkAppN (mkConst eqn) (base ++ #[ρ, K.value] ++ args)) hP)

/-- The condition of block `ss` at `vals` and `ρ`, `Q` what follows it: `P` and a proof of
`Stmt.wpList C rd kret ss ρ Q.value ↔ P`. -/
partial def vcBlock (ss : Expr) (vals : Vals) (ρ : Expr) (Q : Rest) : M (Expr × Expr) := do
  let ctx ← read
  let base := #[ctx.C, ctx.rd, ctx.kret, ρ, Q.value]
  let lhs := ctx.wpList ss ρ Q.value
  let ss' ← whnfD ss
  if ss'.isAppOfArity ``List.nil 1 then
    let (P, hP) ← Q.run vals ρ
    return (P, eqIff lhs (Q.value.beta #[ρ]) P (mkAppN (mkConst ``wpList_nil) base) hP)
  unless ss'.isAppOfArity ``List.cons 3 do throwError "vc: not a block{indentExpr ss'}"
  let s := ss'.appFn!.appArg!
  let rest := ss'.appArg!
  let K := blockRest ctx rest Q
  let (P, hP) ← vcStmt s vals ρ K
  return (P, eqIff lhs (ctx.wp s ρ K.value) P
    (mkAppN (mkConst ``wpList_cons) (base ++ #[s, rest])) hP)
end

/-- The condition of `Fn.Sem C rd f args rets`, `h₀ : ty` its `Fn.sem_iff_wp`: `P` and a proof of
`Fn.Sem C rd f args rets ↔ P`. -/
def vcSem (f h₀ ty : Expr) : M (Expr × Expr) := do
  let ctx ← read
  let body := mkApp (mkConst ``Fn.body) f
  let nothing : Rest := ⟨mkLambda `ρ .default envTy (mkConst ``False),
    fun _ _ => pure (mkConst ``False, iffRfl (mkConst ``False))⟩
  withLocalDeclD `ρ envTy fun ρ₀ => withLocalDeclD `k contTy fun k₀ => do
    let rhsG := ty.appArg!.replace fun e => if e == mkConst ``Env.empty then some ρ₀ else none
    let (P, hP) ← condOf ρ₀ k₀ (ofDefs (mkConst ``Defs.nil)) nothing #[body]
      #[blockRest ctx body nothing] {} rhsG
    return (P, iffTrans ty.appFn!.appArg! ty.appArg! P h₀ hP)

/-! ## The tactic -/

/-- `vc [rules]`: the first `Fn.Sem C rd f args rets` of the goal, `f` a concrete function, is
rewritten to its forward condition (`Fn.sem_iff_wp`), computed one statement at a time: each read
of a defined value is its word, each other read an existential `x{k}`, each value an equation
defines substituted, and each statement's condition rewritten by `rules`. -/
syntax (name := vcTac) "vc"
  (" [" withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "]")? : tactic

@[tactic vcTac] def evalVc : Tactic := fun stx => withMainContext do
  let rules := match stx with
    | `(tactic| vc [$rs,*]) => rs.getElems
    | _ => #[]
  let simpStx ← `(tactic| simp only [exists_eq_left, exists_eq_left', exists_eq_right,
    exists_eq_right', exists_and_left, exists_and_right, exists_eq_right_right, and_true,
    true_and, and_assoc, false_and, and_false, exists_false, false_implies, implies_true,
    true_implies, not_false_eq_true, or_false, List.cons.injEq, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, reduceCtorEq,
    Nat.reduceAdd, keccak_cells_one, keccak_cells_two, keccak_cells_all, $rules,*])
  let { ctx, simprocs, .. } ← mkSimpContext simpStx (eraseLocal := false)
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some sem := target.find? fun e => e.isAppOfArity ``Fn.Sem 5 && !e.hasLooseBVars
    | throwError "vc: no `Fn.Sem` in the goal"
  let a := sem.getAppArgs
  let h₀ := mkAppN (mkConst ``Fn.sem_iff_wp) a
  let ty ← inferType h₀
  let some wl := ty.find? (·.isAppOfArity ``Stmt.wpList 6) | throwError "vc: `Fn.sem_iff_wp`"
  let (P, h) ← (vcSem a[2]! h₀ ty).run
    { C := a[0]!, rd := a[1]!, kret := wl.getAppArgs[2]!, simpCtx := ctx, simprocs }
  let motive ← kabstract target sem
  let eq := mkApp6 (mkConst ``congrArg [Level.one, Level.one]) propTy propTy
    sem P (.lam `X propTy motive .default) (mkApp3 (mkConst ``propext) sem P h)
  replaceMainGoal [← goal.replaceTargetEq (motive.instantiate1 P) eq]

end LeanVM.Guest.Core.VcTactic
