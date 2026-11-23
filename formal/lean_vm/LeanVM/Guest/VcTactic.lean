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
per statement. A sequence of branches duplicates what follows them, once per branch, as the
condition itself does.

The body is computed in chunks of `vc.chunkSize` statements on each path. Where a chunk ends, the
rest of its block is a cut: each word of the table that is neither closed nor a variable is
generalized to a variable, and the rest's condition is computed over these as a chunk of its own.
Its proof is an auxiliary theorem over the chunk's variables `xs`, its condition an auxiliary
definition `R` of them, whose body applies its own cuts' definitions, and a second auxiliary theorem
states `lhs ↔ R xs`. In the enclosing chunk, metavariables applied to the words stand for `R` and
that theorem: the chunk's proof is abstracted over them and applied to the declarations, and its
condition has the reduced conditions substituted.
The kernel checks each chunk and each cut's definition once. When the cut generalizes, a chunk's
terms hold no word built before it, so neither the metaprogram nor the kernel visits the body before
a chunk while computing or checking it, and a deep word (a chain of permutations) is compared only
where the condition meets the composed proof. The words are tracked as terms of the body as well
(`Vals.terms`), so each statement is rewritten as without chunks and the condition is the same;
where generalizing would tell apart two terms that are one word of the body, `vc` computes again
without generalizing (`trace.vc` says so).

By default a `KECCAK`'s written cells are substituted (`keccak_cells_one`, `keccak_cells_two`,
`keccak_cells_all`), so a chain of permutations is a deep word. A body that chains many
thirteen-cell `KECCAK`s takes `vc [-keccak_cells_all, keccak_cells_all_fn]` instead: each such
`KECCAK` is one equation between its written cells, kept as existential words, and the permuted
state of the cells it reads, so no word nests one thirteen-cell permutation in another.

The auxiliary declarations bind a cut's variables, the goal's let-variables with their values, so a
let-variable may stand anywhere in the goal (the function, a statement, an argument, `rets`, a
word's type) and a rule may rely on its value. They are added with the kernel check done at once,
so that a failure fails the tactic and leaves the goal. The tactic does not type-check its proof
itself, so `lake-build.py --dev` keeps the kernel on in every module that uses it.
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

/-- The words of the values defined so far; the variables standing for words since a cut, with
their words in the body; and the words that are not variables, as terms of the body. -/
structure Vals where
  words : Std.HashMap Key Expr := {}
  body : Std.HashMap FVarId Expr := {}
  terms : Std.HashSet Expr := {}

/-- `e` as a term of the body: each variable standing for a word replaced by the word. -/
def Vals.inBody (vals : Vals) (e : Expr) : Expr :=
  if vals.body.isEmpty then e else
    e.replace fun t => if !t.hasFVar then some t else if let .fvar f := t then vals.body[f]?
      else none

/-- `vals` with the word `w` of value `k`, and `w` as a term of the body if it is not a variable. -/
def Vals.insert (vals : Vals) (k : Key) (w : Expr) : Vals :=
  let b := vals.inBody w
  { vals with words := vals.words.insert k w,
              terms := if b.isFVar then vals.terms else vals.terms.insert b }

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

/-- Thrown where the variables of a cut tell apart two terms that are one word of the body. -/
initialize vcSplitId : InternalExceptionId ← registerInternalExceptionId `vc.split

initialize registerTraceClass `vc

register_option vc.chunkSize : Nat := {
  defValue := 32
  descr := "the statements `vc` computes on a path in a chunk before it cuts the rest (at least 1)"
}

/-- A cut: the metavariables standing in its chunk for the rest's condition `R` and for its proof
`hR`; their values in the proof, auxiliary declarations; and `R`'s value in the condition, its
definition reduced. -/
structure Cut where
  R : Expr
  hR : Expr
  Rval : Expr
  hRval : Expr
  Pval : Expr

/-- What every statement's condition shares: the call relation, the reader, the return
condition, and the rewriting of each statement's condition; the chunk size, whether cuts
generalize words, and the statements the current chunk has computed on the current path. -/
structure Ctx where
  C : Expr
  rd : Expr
  kret : Expr
  simpCtx : Simp.Context
  simprocs : Simp.SimprocsArray
  chunkSize : Nat
  generalize : Bool
  depth : Nat := 0

/-- The computation: its state is the current chunk's cuts. -/
abbrev M := ReaderT Ctx (StateRefT (Array Cut) MetaM)

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
    match vals.words[key]? with
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

/-- The terms of `e` that are words of the table and not variables in the body, outermost first;
`none` if two of them are one term of the body. -/
partial def wordsIn (vals : Vals) (e : Expr)
    (acc : Array Expr × Std.HashMap Expr Expr := (#[], {})) :
    Option (Array Expr × Std.HashMap Expr Expr) :=
  let w := vals.inBody e
  if vals.terms.contains w then
    match acc.2[w]? with
    | some e' => if e' == e then some acc else none
    | none => some (acc.1.push e, acc.2.insert w e)
  else match e with
    | .app f a => wordsIn vals f acc >>= (wordsIn vals a ·)
    | .lam _ d b _ | .forallE _ d b _ => wordsIn vals d acc >>= (wordsIn vals b ·)
    | .letE _ t v b _ => wordsIn vals t acc >>= (wordsIn vals v ·) >>= (wordsIn vals b ·)
    | .mdata _ b | .proj _ _ b => wordsIn vals b acc
    | _ => some acc

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
    let some (ws, _) := wordsIn vals raw | throw (.internal vcSplitId)
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

/-- A condition computed as a chunk: `P`, its cuts' conditions substituted; `raw`, their
definitions applied instead; its proof `H : ty`, `ty = ∀ R₁ hR₁ …, lhs ↔ P'` with `P'` the
condition in its cuts' metavariables; and their values in the proof. -/
structure Chunk where
  P : Expr
  raw : Expr
  H : Expr
  ty : Expr
  vals : Array Expr

/-- `x`, a condition of `lhs`, computed as a chunk. -/
def chunk (lhs : Expr) (x : M (Expr × Expr)) : M Chunk := do
  let outer ← modifyGet (·, #[])
  let (P, h) ← withReader ({ · with depth := 0 }) x
  let cs ← modifyGet (·, outer)
  let vs := cs.flatMap fun c => #[c.R, c.hR]
  let H ← mkLambdaFVars vs h
  let P ← instantiateMVars P
  let ty ← mkForallFVars vs (mkApp2 (mkConst ``Iff) lhs P)
  let vals := cs.flatMap fun c => #[c.Rval, c.hRval]
  let raw := (← instantiateForall ty vals).appArg!
  for c in cs do c.R.mvarId!.assign c.Pval
  return ⟨← instantiateMVars P, raw, H, ty, vals⟩

/-- The variables of `es`, of their types and of let-variables' values, in the order of the
context. -/
def varsOf (es : Array Expr) : MetaM (Array Expr) := do
  let mut s : CollectFVars.State := {}
  for e in es do s := collectFVars s (← instantiateMVars e)
  let mut i := 0
  while h : i < s.fvarIds.size do
    let d ← s.fvarIds[i].getDecl
    s := collectFVars s (← instantiateMVars d.type)
    if let some v := d.value? then s := collectFVars s (← instantiateMVars v)
    i := i + 1
  return (← sortFVarIds s.fvarIds).map mkFVar

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
  if ctx.depth ≥ ctx.chunkSize then return ← cut ss vals ρ Q
  let s := ss'.appFn!.appArg!
  let rest := ss'.appArg!
  let K := blockRest ctx rest Q
  let (P, hP) ← withReader ({ · with depth := ctx.depth + 1 }) (vcStmt s vals ρ K)
  return (P, eqIff lhs (ctx.wp s ρ K.value) P
    (mkAppN (mkConst ``wpList_cons) (base ++ #[s, rest])) hP)

/-- The cut of block `ss` at `vals` and `ρ`, `Q` what follows it: each word of the table that is
neither closed nor a variable generalized to a variable `y` (if `ctx.generalize`), the block's
condition computed as a chunk, proved by an auxiliary theorem over the chunk's variables `xs` and
defined by an auxiliary definition of them; in the current chunk, `R as` and
`hR as : lhs ↔ R as`, `as` the words of `xs`. -/
partial def cut (ss : Expr) (vals : Vals) (ρ : Expr) (Q : Rest) : M (Expr × Expr) := do
  let ctx ← read
  let ws := if !ctx.generalize then #[] else Prod.fst <|
    vals.words.fold (init := (#[], ({} : Std.HashSet Expr))) fun acc _ w =>
      if !w.hasFVar || w.isFVar || acc.2.contains w then acc else (acc.1.push w, acc.2.insert w)
  withLocalDecls (ws.map fun _ => (`y, .default, fun _ => pure eTy)) fun ys => do
    let (ofWord, body) := (ws.zip ys).foldl (init := (({} : Std.HashMap Expr Expr), vals.body))
      fun (m, b) (w, y) => (m.insert w y, b.insert y.fvarId! (vals.inBody w))
    let toY (e : Expr) := e.replace fun t => if !t.hasFVar then some t else ofWord[t]?
    let vals' := { vals with words := vals.words.map fun _ w => toY w, body }
    let ρ' := toY ρ
    let lhs := ctx.wpList ss ρ' Q.value
    let { P, raw, H, ty, vals := vs } ← chunk lhs (vcBlock ss vals' ρ' Q)
    -- the declarations are closed over `xs`, let-variables bound with their values; `zs` the others
    let xs ← varsOf #[ty, H]
    let zs ← xs.filterM fun x => return !(← x.fvarId!.isLetVar)
    let Rty ← mkForallFVars xs propTy
    let iffR (R : Expr) := mkApp2 (mkConst ``Iff) lhs (mkAppN R zs)
    -- checked by the kernel at once, so that a failure fails the tactic and leaves the goal
    let (Rval, hRval) ← try withOptions (Elab.async.set · false) do
        -- the proof over `R`, so that identical chunks (a rest after branches) share one theorem
        let thm ← mkAuxTheorem (← mkForallFVars xs ty) (← mkLambdaFVars xs H) (zetaDelta := true)
          (kind? := `_vc)
        let Rval ← mkAuxDefinition (← mkAuxDeclName `_vc_cond) Rty (← mkLambdaFVars xs raw)
          (zetaDelta := true) (compile := false)
        return (Rval, ← mkAuxTheorem (← mkForallFVars xs (iffR Rval))
          (← mkLambdaFVars xs (mkAppN thm (zs ++ vs))) (zetaDelta := true) (kind? := `_vc))
      catch e => throwError "vc: the kernel rejects a cut{indentD e.toMessageData}"
    let R ← mkFreshExprMVarAt {} {} Rty .syntheticOpaque
    let hR ← mkFreshExprMVarAt {} {} (← mkForallFVars xs (iffR R)) .syntheticOpaque
    modify (·.push ⟨R, hR, Rval, hRval, ← mkLambdaFVars zs P⟩)
    let as := zs.map (·.replaceFVars ys ws)
    return (mkAppN R as, mkAppN hR as)
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
  let chunkSize := max 1 (vc.chunkSize.get (← getOptions))
  let run (generalize : Bool) : MetaM _ :=
    (chunk sem (vcSem a[2]! h₀ ty)).run
      { C := a[0]!, rd := a[1]!, kret := wl.getAppArgs[2]!, simpCtx := ctx, simprocs, chunkSize,
        generalize } |>.run' #[]
  let s ← Meta.saveState
  -- cuts generalize their words unless that tells apart two terms of the body
  let { P, H, vals := vs, .. } ← try run true catch e => do
    let .internal id _ := e | throw e
    unless id == vcSplitId do throw e
    s.restore
    trace[vc] "cuts tell apart two terms of one word: computing without generalizing"
    run false
  let h := mkAppN H vs
  let motive ← kabstract target sem
  let eq := mkApp6 (mkConst ``congrArg [Level.one, Level.one]) propTy propTy
    sem P (.lam `X propTy motive .default) (mkApp3 (mkConst ``propext) sem P h)
  replaceMainGoal [← goal.replaceTargetEq (motive.instantiate1 P) eq]

end LeanVM.Guest.Core.VcTactic
