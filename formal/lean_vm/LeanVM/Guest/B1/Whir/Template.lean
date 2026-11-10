/-
  LeanVM.Guest.B1.Whir.Template

  The core IR of `open_stacked` and of its loop helpers, generated from a candidate's
  configuration as the expansion numbers it: the head, the levels, the tail rounds, the point,
  the induced bases, the residual chains and the out-of-domain weights.
-/

module

public import LeanVM.Guest.B1.Whir.Config
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Whir.Interface

/-!
# The template of `open_stacked` (TRIAGE G #42)

`osBody c` is the body of `open_stacked__L{c.m}` (`lean_ethereum.py`, `open_stacked`) at the
configuration `c = osCfg m`, value by value as the expansion numbers it: every block takes the
first free value `k` and returns the next, the running sponge cells, the cursor (a base value and
a word offset), the waiting scalars, the quadratic and the claim in `OsSt`. The body depends on the
size alone: where a rate changes a level's shape it dispatches on the rate's selector, value `0`
(`.dispatch`), into a helper specialized on that rate's row (`level_positions`, `level_queries`,
`level_residual`, and `opening_fold_round` at a level some rate grinds the folds of), the names
taken from every rate's levels (`OsCfg.lvAt`). The inline Fiat-Shamir helpers are B1-a's
templates (`fsPackT`, `fsNextT`, `challengeT`, `keccakA`, `B1/Fs/Templates.lean`).

`Whir/Data*.lean` check every size's body equal to this by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-! ## Small blocks -/

/-- `g^e` as a word, its limbs written out for the kernel (`gpowK`, `Guest/Word.lean`). -/
def gw (e : ℕ) : E := E.ofLimbs (gpowK e) 0 0

/-- A value's name. -/
abbrev nv (k : ℕ) : V := .n k

/-- `HeapBuf(g^e)` at `k`: its size `k`, its pointer `k + 1`. -/
def osHeap (e k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (gw e)), .atom (.hint (.allocDyn (.n (k + 1)) (.n k)))]

/-- The pointer `base·g^off`, materialized from `k` when the offset is not zero: the statements,
the pointer's value and the next free value. -/
def osMat (base off k : ℕ) : List Stmt × ℕ × ℕ :=
  if off = 0 then ([], base, k)
  else ([.atom (.const (.n k) (gw off)), .atom (.mul (.n (k + 1)) (.n base) (.n k))],
    k + 1, k + 2)

/-- A shifted pointer the body materialized (`Mat`, `Guest/Expand.lean`): `out = base·g^exp`,
made as `src·g^dist`. -/
structure OsMat where
  base : ℕ
  exp : ℕ
  out : ℕ
  src : ℕ
  dist : ℕ
  deriving Repr, Inhabited, DecidableEq

/-- The source and distance of a first materialization of `base·g^off`: from the materialization
`base·g^e` the plan names (`e < off`), when there is one, else from `base`. -/
def osMatSrc (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off : ℕ) : ℕ × ℕ :=
  match plan.find? (fun p ↦ p.1 == base && p.2.1 == off) with
  | some (_, _, e) =>
    match mats.find? (fun m ↦ m.base == base && m.exp == e) with
    | some m => if e < off then (m.out, off - e) else (base, off)
    | none => (base, off)
  | none => (base, off)

/-- The pointer `base·g^off` as the compiler materializes it (`materialize`), from `k`, the
materializations so far `mats`: none when the offset is zero; a second materialization repeats the
first's product; a first is from the base or, as the plan says, from an earlier one. The
statements, the pointer's value and the next free value. -/
def osMatP (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) : List Stmt × ℕ × ℕ :=
  if off = 0 then ([], base, k)
  else
    let sd : ℕ × ℕ := match mats.find? (fun m ↦ m.base == base && m.exp == off) with
      | some m => (m.src, m.dist)
      | none => osMatSrc plan mats base off
    ([.atom (.const (.n k) (gw sd.2)), .atom (.mul (.n (k + 1)) (.n sd.1) (.n k))], k + 1, k + 2)

/-- The materializations after `osMatP plan mats base off k`. -/
def osMatsAfter (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) : List OsMat :=
  if off = 0 then mats
  else match mats.find? (fun m ↦ m.base == base && m.exp == off) with
    | some _ => mats
    | none =>
      let sd := osMatSrc plan mats base off
      mats ++ [⟨base, off, k + 1, sd.1, sd.2⟩]

/-- Values `k .. k + n - 1`. -/
def osRun (k n : ℕ) : List V := (List.range n).map fun j ↦ .n (k + j)

/-- `x^e` by the compiler's square-and-multiply from `acc = x` over the digits after the leading
one, from `k`: the statements and the result. -/
def osPowSteps (x : ℕ) : List Bool → ℕ → ℕ → List Stmt × ℕ
  | [], acc, _ => ([], acc)
  | d :: ds, acc, k =>
    if d then
      let r := osPowSteps x ds (k + 1) (k + 2)
      (.atom (.mul (.n k) (.n acc) (.n acc)) :: .atom (.mul (.n (k + 1)) (.n k) (.n x)) :: r.1, r.2)
    else
      let r := osPowSteps x ds k (k + 1)
      (.atom (.mul (.n k) (.n acc) (.n acc)) :: r.1, r.2)

/-- The binary digits of `e` after its leading one, most significant first. -/
def osPowDigits (e : ℕ) : List Bool := (Nat.bits e).reverse.tail

/-- The values `osPowSteps` takes for `e`'s digits. -/
def osPowLen (e : ℕ) : ℕ := (osPowDigits e).length + ((osPowDigits e).filter id).length

/-- The `mul_range` loop's tail (`x·g ≠ N`: call the loop at `x·g`), from `k`, for a helper of
`n` parameters, the first the counter and the second the bound. -/
def osLoopTail (name : String) (n k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (word 2 0 0)), .atom (.mul (.n (k + 1)) (.n 0) (.n k)),
    .atom (.add (.n (k + 2)) (.n (k + 1)) (.n 1)), .atom (.const (.n (k + 3)) (word 2 0 0)),
    .atom (.mul (.n (k + 4)) (.n 0) (.n (k + 3))),
    .callIf (.n (k + 2)) name (.n (k + 4) :: (List.range (n - 1)).map fun i ↦ .n (i + 1)),
    .ret []]

/-- A loop's entry `for x in mul_range(1, g^n)`, from `k`: the guard `1 + g^n` at `k + 2`, the
loop called at `[1, g^n] ++ args`. -/
def osLoopCall (name : String) (n : ℕ) (args : List ℕ) (k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (word 1 0 0)), .atom (.const (.n (k + 1)) (gw n)),
    .atom (.add (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.const (.n (k + 3)) (word 1 0 0)),
    .atom (.const (.n (k + 4)) (gw n)),
    .callIf (.n (k + 2)) name (.n (k + 3) :: .n (k + 4) :: args.map V.n)]

/-- The zero run of the sponge's padding (`keccak_pad_run`), allocated at its first use: the
statements, its first cell (`1`; the next four are `0`) and the next free value. -/
def osPad (pad : Option ℕ) (k : ℕ) : List Stmt × ℕ × ℕ :=
  match pad with
  | some p => ([], p, k)
  | none => ([.atom (.const (.n k) (word 1 0 0)), .atom (.const (.n (k + 1)) (word 0 0 0)),
      .atom (.const (.n (k + 2)) (word 0 0 0)), .atom (.const (.n (k + 3)) (word 0 0 0)),
      .atom (.const (.n (k + 4)) (word 0 0 0))], k, k + 5)

/-- A squeeze with nothing waiting (`squeeze(sp, no_rate, 0)`) on the five capacity values `cap`,
the zero run at `p`, from `k`: the permutation's outputs `k .. k + 12`, the challenge `k + 19`. -/
def osSqueeze0 (p : ℕ) (cap : List ℕ) (k : ℕ) : List Stmt :=
  keccakA (([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4] ++ cap).map V.n)
      (osRun k 13) :: challengeT (.n k) (.n (k + 1)) (k + 13)

/-- `residual_query(chain, row_d, vanish, n_cols)` (G:1414-1422) inline, the position at `pos`,
the row's `d` words at `bd·g^row`, from `k`: the product `Π_t (d_t + chain_t)`, the chain from
the position by `chain ← chain·(chain + v)` over the vanishing values from `vo`. The statements,
the product's value and the next free value. -/
def osResQ (pos bd row vo : ℕ) : ℕ → ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ
  | 0, _, pe, k => ([], pe, k)
  | n + 1, t, pe, k =>
    let ch := if t = 1 then pos else k - 4
    let r := osResQ pos bd row vo n (t + 1) (k + 5) (k + 6)
    ([.atom (.const (.n k) (word (vanishVal (vo + t - 1)) 0 0)), .atom (.add (.n (k + 1)) (.n ch) (.n k)),
      .atom (.mul (.n (k + 2)) (.n ch) (.n (k + 1))), .atom (.load (.n (k + 3)) (.n bd) (row + t)),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))),
      .atom (.mul (.n (k + 5)) (.n pe) (.n (k + 4)))] ++ r.1, r.2)

/-- The whole inline `residual_query` from `k` over `ncols` coordinates: `d_0 + pos` at `k + 1`,
then the steps. -/
def osResQuery (pos bd row vo ncols k : ℕ) : List Stmt × ℕ × ℕ :=
  let r := osResQ pos bd row vo (ncols - 1) 1 (k + 1) (k + 2)
  ([.atom (.load (.n k) (.n bd) row), .atom (.add (.n (k + 1)) (.n k) (.n pos))] ++ r.1, r.2)

/-! ## The running state -/

/-- The values the body carries between its blocks. -/
structure OsSt where
  /-- The next free value. -/
  k : ℕ
  /-- The sponge's five capacity cells. -/
  fs : List ℕ
  /-- The two scalars waiting in the sponge. -/
  w0 : ℕ
  w1 : ℕ
  /-- The cursor: a base value and a word offset. -/
  cb : ℕ
  co : ℕ
  /-- The running quadratic's coefficients and the running claim. -/
  c : ℕ
  b : ℕ
  a : ℕ
  t : ℕ
  /-- The zero run, once allocated. -/
  pad : Option ℕ
  /-- The shifted pointers materialized so far (of the fixed buffers). -/
  mats : List OsMat
  deriving Repr, Inhabited

/-- The rate's selector `g^r`, the body's first argument, which the dispatches read. -/
abbrev osRate : ℕ := 0

/-- The fixed buffers' pointers, allocated by the head: `final_msg`, `level_roots`,
`fold_challenges`, `level_betas`, `level_mus`, `query_positions`, `query_win_ptrs`, `win_tabs`,
`ood_z`, `ood`. -/
abbrev osFmsg : ℕ := 14
abbrev osRoots : ℕ := 16
abbrev osFch : ℕ := 18
abbrev osBetas : ℕ := 20
abbrev osMus : ℕ := 22
abbrev osQpos : ℕ := 24
abbrev osQbp : ℕ := 26
abbrev osWin : ℕ := 28
abbrev osOodz : ℕ := 158
abbrev osOod : ℕ := 160

/-- The window table: `win_tabs[g^n] = n`, `n < 128`, the constant `n` at `29 + n`. -/
def osWinTabs : List Stmt :=
  ((List.range 128).map fun i ↦
    [.atom (.const (.n (29 + i)) (word i 0 0)), .atom (.load (.n (29 + i)) (.n osWin) i)]).flatten

/-! ## The head and the levels -/

/-- The head: the first quadratic read (`c` at `10`, `a` at `11`, `b = target + a` at `12`), the
fixed buffers, the commitment's root into `level_roots`. The arguments are the rate's selector
`0`, the sponge `1 .. 5`, the target `6`, the root `7, 8` and the cursor `9`. -/
def osHead (c : OsCfg) : List Stmt × OsSt :=
  let n := c.levels.length
  ([.atom (.load (.n 10) (.n 9) 0), .atom (.load (.n 11) (.n 9) 1), .atom (.add (.n 12) (.n 6) (.n 11))] ++
    osHeap c.yrLen 13 ++ osHeap (2 * n) 15 ++
    [.atom (.load (.n 7) (.n osRoots) 0), .atom (.load (.n 8) (.n osRoots) 1)] ++
    osHeap c.nFolds 17 ++ osHeap n 19 ++ osHeap n 21 ++ osHeap (n * ligPosCap) 23 ++
    osHeap (n * ligPosCap) 25 ++ osHeap 128 27 ++ osWinTabs ++ osHeap (n * ligColsCap) 157 ++
    osHeap (n * oodSlots) 159,
   ⟨161, [1, 2, 3, 4, 5], 10, 11, 9, 2, 10, 12, 11, 6, none, []⟩)

/-- The call of one sumcheck round on its arguments and returns: `opening_fold` itself, or, at a
level some rate grinds the folds of, the rate's `opening_fold_round` specialization. -/
def osFoldCall (fr : Option (List String)) (args rets : List V) : Stmt :=
  match fr with
  | none => .call "opening_fold" args rets
  | some names => .dispatch (.n osRate) names args rets

/-- One sumcheck round (`opening_fold`), its challenge stored at `p·g^off`: the cursor
materialized, the call, the store, `b = claim + a`. -/
def osFold (fr : Option (List String)) (p off : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let m := osMat s.cb s.co s.k
  let r := m.2.2
  (m.1 ++ [osFoldCall fr ((s.fs ++ [s.w0, s.w1, m.2.1, s.c, s.b, s.a]).map V.n) (osRun r 10),
    .atom (.load (.n (r + 9)) (.n p) off), .atom (.add (.n (r + 10)) (.n (r + 6)) (.n (r + 8)))],
   { s with k := r + 11, fs := [r, r + 1, r + 2, r + 3, r + 4], cb := r + 5, co := 0, t := r + 6,
            c := r + 7, a := r + 8, w0 := r + 7, w1 := r + 8, b := r + 10 })

/-- `n` rounds, the challenges stored from `p·g^off`. -/
def osFolds (fr : Option (List String)) (p : ℕ) : ℕ → ℕ → OsSt → List Stmt × OsSt
  | _, 0, s => ([], s)
  | off, n + 1, s =>
    let r := osFold fr p off s
    let t := osFolds fr p (off + 1) n r.2
    (r.1 ++ t.1, t.2)

/-- The rounds keep the materialized pointers. -/
theorem osFolds_mats (fr : Option (List String)) (p : ℕ) :
    ∀ (n off : ℕ) (st : OsSt), (osFolds fr p off n st).2.mats = st.mats
  | 0, _, _ => rfl
  | n + 1, off, st => osFolds_mats fr p n (off + 1) (osFold fr p off st).2

/-- The name of `opening_fold_round`'s specialization at `b` bits. -/
def osFoldRoundName (b : ℕ) : String := "opening_fold_round__L" ++ natStr b

/-- A level's fold call: `opening_fold`, or, when some rate grinds its folds, the dispatch on the
rate into `opening_fold_round` at each rate's bits. -/
def osFoldNames (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Option (List String) :=
  if lv.grindAny = 0 then none else some ((c.lvAt lvl).map fun l ↦ osFoldRoundName l.foldGrind)

/-- The final level's message (`opening_final_message`, G:1501): the call, the sponge after the
nonce's permutation; its first cell (the grinding word) and the nonce. -/
def osFinal (c : OsCfg) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let m := osMat s.cb s.co s.k
  let r := m.2.2
  (m.1 ++ [.call ("opening_final_message__L" ++ natStr c.yrLen)
      ((s.fs ++ [s.w0, s.w1, m.2.1, osFmsg]).map V.n) (osRun r 8)],
   { s with k := r + 8, fs := [r + 1, r + 2, r + 3, r + 4, r + 5], cb := r + 6, co := 0 }, r)

/-- A level's next commitment (G:1494-1538): the capacity copied (`fs_cap`), the waiting scalars
packed, the root's two halves read, checked canonical and stored, the out-of-domain point
(`opening_ood_point`), its value and intro message read and stored in `ood`, the nonce read and
absorbed with them (`fs_absorb_nonce`): the permutation's first cell (the grinding word) and its
capacity. -/
def osCommit (plan : List (ℕ × ℕ × ℕ)) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let k := s.k
  let sb := (lvl + 1) * oodSlots
  let oz := osMatP plan s.mats osOodz ((lvl + 1) * ligColsCap) (k + 45)
  ((s.fs.zipIdx.map fun (f, i) ↦ .atom (.copy (.n (k + i)) (.n f))) ++
    fsPackT (.n s.w0) (k + 5) 1 ++ fsPackT (.n s.w1) (k + 14) 1 ++
    fsNextT (.n s.cb) s.co (k + 23) ++ fsNextT (.n s.cb) (s.co + 1) (k + 33) ++
    [.call "assert_canonical" [.n (k + 23)] [.n (k + 43)],
      .call "assert_canonical" [.n (k + 33)] [.n (k + 44)],
      .atom (.load (.n (k + 23)) (.n osRoots) (2 * lvl + 2)),
      .atom (.load (.n (k + 33)) (.n osRoots) (2 * lvl + 3)),
      ] ++ oz.1 ++ [
      .call ("opening_ood_point__L" ++ natStr lv.logCols)
        ((s.fs ++ [k + 11, k + 13, k + 20, k + 22, k + 30, k + 32, k + 40, k + 42, k + 46]).map V.n)
        (osRun (k + 47) 5)] ++
    fsNextT (.n s.cb) (s.co + 2) (k + 52) ++ fsNextT (.n s.cb) (s.co + 3) (k + 62) ++
    fsNextT (.n s.cb) (s.co + 4) (k + 72) ++
    [.atom (.load (.n (k + 52)) (.n osOod) (sb + 1)), .atom (.load (.n (k + 62)) (.n osOod) (sb + 2)),
      .atom (.load (.n (k + 72)) (.n osOod) (sb + 3)), .atom (.load (.n (k + 82)) (.n s.cb) (s.co + 5))] ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (k + 83 + i)) (.n (k + 47 + i)))) ++
    fsPackT (.n (k + 82)) (k + 88) 4 ++
    [keccakA ([k + 59, k + 61, k + 69, k + 71, k + 79, k + 81, k + 94, k + 96, k + 83, k + 84, k + 85,
      k + 86, k + 87].map V.n) (osRun (k + 97) 13)],
   { s with k := k + 110, fs := [k + 105, k + 106, k + 107, k + 108, k + 109], co := s.co + 6,
            mats := osMatsAfter plan s.mats osOodz ((lvl + 1) * ligColsCap) (k + 45) }, k + 97)

/-- The name of `level_positions`' specialization at a level's row. -/
def osPositionsName (lv : OsLv) : String :=
  "level_positions__L" ++ natStr lv.squeezes ++ "_L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth

/-- The query positions: the level's slots of `query_positions` and `query_win_ptrs`
materialized, the dispatch on the rate into `level_positions` (the squeezes, decoded), its
capacity copied, and the batching challenge `lam` squeezed from it (at the returned `k - 1`);
its capacity becomes the sponge's. -/
def osPositions (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let P := c.plan
  let qp := osMatP P s.mats osQpos lv.posOff k
  let m1 := osMatsAfter P s.mats osQpos lv.posOff k
  let wp := osMatP P m1 osQbp lv.posOff qp.2.2
  let m2 := osMatsAfter P m1 osQbp lv.posOff qp.2.2
  let j := wp.2.2
  let pd := osPad s.pad (j + 10)
  let e := pd.2.2
  (qp.1 ++ wp.1 ++
    [.dispatch (.n osRate) ((c.lvAt lvl).map osPositionsName)
      ((s.fs ++ [qp.2.1, wp.2.1, osWin]).map V.n) (osRun j 5)] ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (j + 5 + i)) (.n (j + i)))) ++
    pd.1 ++ osSqueeze0 pd.2.1 [j + 5, j + 6, j + 7, j + 8, j + 9] e,
   { s with k := e + 20, fs := [e + 8, e + 9, e + 10, e + 11, e + 12], pad := some pd.2.1, mats := m2 })

/-- `level_mus[g^lvl] = 1 / lam`, from `k`: `1` at `k` and the constraint `1 = μ·lam` with `μ`
at `k + 1`, stored. The statements and the next free value. -/
def osMu (lvl lam k : ℕ) : List Stmt × ℕ :=
  ([.atom (.const (.n k) (word 1 0 0)), .atom (.mul (.n k) (.n (k + 1)) (.n lam)),
    .atom (.load (.n (k + 1)) (.n osMus) lvl)], k + 2)

/-- The name of `level_queries`' specialization at a level's row. -/
def osQueriesName (lvl : ℕ) (lv : OsLv) : String :=
  let base := if lvl = 0 then 1 else 0
  "level_queries__L" ++ natStr lv.queries ++ "_L" ++ natStr base ++ "_L" ++
    natStr lv.interleave ++ "_L" ++ natStr lv.leafCells ++ "_L" ++ natStr lv.depth ++ "_L" ++
    natStr lv.capDepth

/-- The level's queries, from `k`, after `level_mus`: the row weights, the dispatch on the rate
into `level_queries` (the level's cap checked up to its root, stored in `level_roots`, the queries'
sum and `lam^n`), the intro message's two words and its linear coefficient. The statements, the
next free value, and the values of the sum, `lam^n` and `c0`, `c1`, `c2`. -/
def osQueries (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam : ℕ) (s : OsSt) :
    List Stmt × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let k := s.k
  let P := c.plan
  let m0 := s.mats
  let fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  let bp := osMatP P m1 osQbp lv.posOff fp.2.2
  let r := bp.2.2
  (osHeap c.maxIl k ++ fp.1 ++
    [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [.n fp.2.1, .n (k + 1)] []] ++
    bp.1 ++
    [.dispatch (.n osRate) ((c.lvAt lvl).map (osQueriesName lvl)) [.n lam, .n bp.2.1, .n (k + 1)]
        (osRun r 4),
      .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1)),
      .atom (.load (.n (r + 4)) (.n s.cb) s.co), .atom (.load (.n (r + 5)) (.n s.cb) (s.co + 1)),
      .atom (.add (.n (r + 6)) (.n (r + 2)) (.n (r + 5)))],
   r + 7, r + 2, r + 3, r + 4, r + 6, r + 5)

/-- The materializations after a level's queries (`osQueries`): the fold challenges' and the
window pointers' (repeating the positions' first). -/
def osQueriesMats (c : OsCfg) (lv : OsLv) (s : OsSt) : List OsMat :=
  let k := s.k
  let P := c.plan
  let m0 := s.mats
  let fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  osMatsAfter P m1 osQbp lv.posOff fp.2.2

/-- A level's out-of-domain claim glued with the scalar `lam` (G:1621-1631), from `k`: its value
and intro reread from `ood`, the scalar stored, the running sums updated; the next scalar
`lam²` at `k + 12`. -/
def osOodGlue (lvl lam : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let sb := (lvl + 1) * oodSlots
  ([.atom (.load (.n k) (.n osOod) (sb + 1)), .atom (.load (.n (k + 1)) (.n osOod) (sb + 3)),
    .atom (.load (.n lam) (.n osOod) sb), .atom (.load (.n (k + 2)) (.n osOod) (sb + 2)),
    .atom (.mul (.n (k + 3)) (.n lam) (.n (k + 2))), .atom (.add (.n (k + 4)) (.n s.c) (.n (k + 3))),
    .atom (.add (.n (k + 5)) (.n k) (.n (k + 1))), .atom (.mul (.n (k + 6)) (.n lam) (.n (k + 5))),
    .atom (.add (.n (k + 7)) (.n s.b) (.n (k + 6))), .atom (.mul (.n (k + 8)) (.n lam) (.n (k + 1))),
    .atom (.add (.n (k + 9)) (.n s.a) (.n (k + 8))), .atom (.mul (.n (k + 10)) (.n lam) (.n k)),
    .atom (.add (.n (k + 11)) (.n s.t) (.n (k + 10))), .atom (.mul (.n (k + 12)) (.n lam) (.n lam))],
   { s with k := k + 13, c := k + 4, b := k + 7, a := k + 9, t := k + 11 })

/-- The level's batch glued with the scalar `beta` (G:1633-1637), from `k`: the intro `c0, c1, c2`
and the queries' sum `v`. -/
def osGlue (beta v c0 c1 c2 : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  ([.atom (.mul (.n k) (.n beta) (.n c0)), .atom (.add (.n (k + 1)) (.n s.c) (.n k)),
    .atom (.mul (.n (k + 2)) (.n beta) (.n c1)), .atom (.add (.n (k + 3)) (.n s.b) (.n (k + 2))),
    .atom (.mul (.n (k + 4)) (.n beta) (.n c2)), .atom (.add (.n (k + 5)) (.n s.a) (.n (k + 4))),
    .atom (.mul (.n (k + 6)) (.n beta) (.n v)), .atom (.add (.n (k + 7)) (.n s.t) (.n (k + 6)))],
   { s with k := k + 8, c := k + 1, b := k + 3, a := k + 5, t := k + 7 })

/-- One level. -/
def osLevel (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let f := osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds s
  let m := if lvl = c.yrLevel then osFinal c f.2 else osCommit c.plan lvl lv f.2
  let gr : List Stmt := [.call ("grind_check__L" ++ natStr lv.grind) [.n m.2.2] []]
  let sq := osPositions c lvl lv m.2.1
  let lam := sq.2.k - 1
  let mu := osMu lvl lam sq.2.k
  let q := osQueries c lvl lv lam { sq.2 with k := mu.2 }
  let lamN := q.2.2.2.1
  let s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.2.1, w1 := q.2.2.2.2.2.2,
                               co := sq.2.co + 2, mats := osQueriesMats c lv { sq.2 with k := mu.2 } }
  let o := if lvl = c.yrLevel then (([] : List Stmt), s1, lam) else
    let g := osOodGlue lvl lam s1
    (g.1, g.2, s1.k + 12)
  let beta := o.2.2
  let bk := o.2.1.k
  let gl := osGlue beta q.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2 { o.2.1 with k := bk + 1 }
  (f.1 ++ m.1 ++ gr ++ sq.1 ++ mu.1 ++ q.1 ++ o.1 ++
    [.atom (.mul (.n bk) (.n beta) (.n lamN)), .atom (.load (.n bk) (.n osBetas) lvl)] ++ gl.1,
   gl.2)

/-- The levels `lvl ..`. -/
def osLevels (c : OsCfg) : ℕ → List OsLv → OsSt → List Stmt × OsSt
  | _, [], s => ([], s)
  | lvl, lv :: rest, s =>
    let r := osLevel c lvl lv s
    let t := osLevels c (lvl + 1) rest r.2
    (r.1 ++ t.1, t.2)

/-! ## The tail and the rest -/

/-- The tail rounds (G:1648-1666) into `tail_challenges` (`HeapBuf(g^5)` at `k + 1`): `yrLog - 1`
rounds, the closing squeeze on the two waiting scalars, its challenge stored, the final claim, the
unused entries zeroed. The statements, the state (its claim `t`) and the buffer. -/
def osTail (c : OsCfg) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let tch := s.k + 1
  let f := osFolds none tch 0 (c.yrLog - 1) { s with k := s.k + 2 }
  let j := f.2.k
  let p := (f.2.pad.getD 0)
  (osHeap yrLogCap s.k ++ f.1 ++
    (f.2.fs.zipIdx.map fun (x, i) ↦ .atom (.copy (.n (j + i)) (.n x))) ++
    fsPackT (.n f.2.w0) (j + 5) 1 ++ fsPackT (.n f.2.w1) (j + 14) 1 ++
    keccakA ([j + 11, j + 13, j + 20, j + 22, p + 1, p + 2, p + 3, p + 4, j, j + 1, j + 2, j + 3,
      j + 4].map V.n) (osRun (j + 23) 13) ::
    challengeT (.n (j + 23)) (.n (j + 24)) (j + 36) ++
    [.atom (.load (.n (j + 42)) (.n tch) (c.yrLog - 1)),
      .atom (.mul (.n (j + 43)) (.n (j + 42)) (.n f.2.b)), .atom (.add (.n (j + 44)) (.n f.2.c) (.n (j + 43))),
      .atom (.mul (.n (j + 45)) (.n (j + 42)) (.n (j + 42))),
      .atom (.mul (.n (j + 46)) (.n (j + 45)) (.n f.2.a)),
      .atom (.add (.n (j + 47)) (.n (j + 44)) (.n (j + 46)))] ++
    ((List.range (yrLogCap - c.yrLog)).map fun i ↦
      [.atom (.const (.n (j + 48 + i)) (word 0 0 0)),
        .atom (.load (.n (j + 48 + i)) (.n tch) (c.yrLog + i))]).flatten,
   { f.2 with k := j + 48 + (yrLogCap - c.yrLog), t := j + 47 }, tch)

/-- The source of entry `i` of the rotated point (G:1672-1686): the fold challenges past the lane
folds, the tail challenges, the lane folds; then zeros. -/
def osPtSrc (c : OsCfg) (tch i : ℕ) : Option (ℕ × ℕ) :=
  let lane := (c.levels.headD default).folds
  if i < c.nFolds - lane then some (osFch, lane + i)
  else if i < c.nFolds - lane + c.yrLog then some (tch, i - (c.nFolds - lane))
  else if i < c.nFolds + c.yrLog then some (osFch, i - (c.nFolds - lane) - c.yrLog)
  else none

/-- Entry `i` of the point at `pt` and of `point1` at `pt1`, from `k`; the next free value. -/
def osPtBlk (pt pt1 i k : ℕ) : Option (ℕ × ℕ) → List Stmt × ℕ
  | some (b, o) =>
    ([.atom (.load (.n k) (.n b) o), .atom (.load (.n k) (.n pt) i),
      .atom (.const (.n (k + 1)) (word 1 0 0)), .atom (.load (.n (k + 2)) (.n b) o),
      .atom (.add (.n (k + 3)) (.n (k + 1)) (.n (k + 2))), .atom (.load (.n (k + 3)) (.n pt1) i)], k + 4)
  | none =>
    ([.atom (.const (.n k) (word 0 0 0)), .atom (.load (.n k) (.n pt) i),
      .atom (.const (.n (k + 1)) (word 1 0 0)), .atom (.load (.n (k + 1)) (.n pt1) i)], k + 2)

/-- The entries `i ..` of the point, from `k`. -/
def osPtBlks (c : OsCfg) (pt pt1 tch : ℕ) : ℕ → ℕ → ℕ → List Stmt × ℕ
  | _, 0, k => ([], k)
  | i, n + 1, k =>
    let r := osPtBlk pt pt1 i k (osPtSrc c tch i)
    let t := osPtBlks c pt pt1 tch (i + 1) n r.2
    (r.1 ++ t.1, t.2)

/-- One coordinate of a level's basis row (G:1705-1711): the challenge at `src`, its coefficient
`b = c·inv` (`c` itself when `inv = 1`), `d = (1 + c)/b` stored at `basis_d[slot]`, the scale
times `b`; from `k`, the scale `sc`. The statements, the new scale and the next free value. -/
def osBasisBlk (bd slot : ℕ) (src : ℕ × ℕ) (inv sc k : ℕ) : List Stmt × ℕ × ℕ :=
  if inv = 1 then
    ([.atom (.load (.n k) (.n src.1) src.2), .atom (.const (.n (k + 1)) (word 1 0 0)),
      .atom (.add (.n (k + 2)) (.n (k + 1)) (.n k)), .atom (.mul (.n (k + 2)) (.n (k + 3)) (.n k)),
      .atom (.load (.n (k + 3)) (.n bd) slot), .atom (.mul (.n (k + 4)) (.n sc) (.n k))], k + 4, k + 5)
  else
    ([.atom (.load (.n k) (.n src.1) src.2), .atom (.const (.n (k + 1)) (word inv 0 0)),
      .atom (.mul (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.const (.n (k + 3)) (word 1 0 0)),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n k)), .atom (.mul (.n (k + 4)) (.n (k + 5)) (.n (k + 2))),
      .atom (.load (.n (k + 5)) (.n bd) slot), .atom (.mul (.n (k + 6)) (.n sc) (.n (k + 2)))], k + 6, k + 7)

/-- A level's basis coordinates `(slot, source, inverse)`: the fold challenges after its folds,
then the tail challenges. -/
def osBasisCoords (c : OsCfg) (tch lvl : ℕ) (lv : OsLv) : List (ℕ × (ℕ × ℕ) × ℕ) :=
  (List.range (lv.prefixLen + c.yrLog)).map fun t ↦
    (lvl * ligColsCap + t,
      (if t < lv.prefixLen then (osFch, lv.resFoldOff + t) else (tch, t - lv.prefixLen)),
      vanishInv (lv.vanish + t))

/-- The coordinates of a basis row from the scale `sc` and `k`: the statements, the final scale and
the next free value. -/
def osBasisRow (bd : ℕ) : List (ℕ × (ℕ × ℕ) × ℕ) → ℕ → ℕ → List Stmt × ℕ × ℕ
  | [], sc, k => ([], sc, k)
  | (slot, src, inv) :: rest, sc, k =>
    let r := osBasisBlk bd slot src inv sc k
    let t := osBasisRow bd rest r.2.1 r.2.2
    (r.1 ++ t.1, t.2)

/-- Every level's basis row and its scale (G:1699-1718), from `k`. -/
def osBases (c : OsCfg) (tch bd ls : ℕ) : ℕ → List OsLv → ℕ → List Stmt × ℕ
  | _, [], k => ([], k)
  | lvl, lv :: rest, k =>
    let r := osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1)
    let t := osBases c tch bd ls (lvl + 1) rest r.2.2
    (.atom (.load (.n k) (.n osBetas) lvl) :: r.1 ++ [.atom (.load (.n r.2.1) (.n ls) lvl)] ++ t.1, t.2)

/-- One step of a residual chain, from `k`: the position loaded at `pp·g^j`, its
`residual_query` (`osResQuery`) over the row at `bd·g^row`, then `h ← (h + eq)·μ`. The
statements, the new `h` and the next free value. -/
def osResStep (pp bd row vo ncols mu : ℕ) (j h k : ℕ) : List Stmt × ℕ × ℕ :=
  let e := osResQuery k bd row vo ncols (k + 1)
  ([.atom (.load (.n k) (.n pp) j)] ++ e.1 ++
    [.atom (.add (.n e.2.2) (.n h) (.n e.2.1)), .atom (.mul (.n (e.2.2 + 1)) (.n e.2.2) (.n mu))],
   e.2.2 + 1, e.2.2 + 2)

/-- The steps at the position offsets `js`, from the chain value `h` and `k`. -/
def osResSteps (pp bd row vo ncols mu : ℕ) : List ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ
  | [], h, k => ([], h, k)
  | j :: js, h, k =>
    let r := osResStep pp bd row vo ncols mu j h k
    let t := osResSteps pp bd row vo ncols mu js r.2.1 r.2.2
    (r.1 ++ t.1, t.2)

/-- `RES_BATCH`: the queries a residual batch takes. -/
abbrev resBatch : ℕ := 8

/-- The name of `level_residual`'s specialization at a level's row. -/
def osResidualName (lv : OsLv) : String :=
  "level_residual__L" ++ natStr lv.queries ++ "_L" ++ natStr lv.logCols

/-- Level `lvl`'s residual chain, from `k` and the materializations `mats`: the level's slots of
`query_positions` and its row of `basis_d` materialized, `μ` read from `level_mus`, the dispatch on
the rate into `level_residual`, `inner[lvl + 1] = inner[lvl] + scale·h`. The statements, the
materializations after it and the next free value. -/
def osResidual (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) :
    List Stmt × List OsMat × ℕ :=
  let P := c.plan
  let qp := osMatP P mats osQpos lv.posOff k
  let m1 := osMatsAfter P mats osQpos lv.posOff k
  let bp := osMatP P m1 bd (lvl * ligColsCap) qp.2.2
  let m2 := osMatsAfter P m1 bd (lvl * ligColsCap) qp.2.2
  let j := bp.2.2
  (qp.1 ++ bp.1 ++
    [.atom (.load (.n j) (.n osMus) lvl),
      .dispatch (.n osRate) ((c.lvAt lvl).map osResidualName) [.n qp.2.1, .n bp.2.1, .n j] [.n (j + 1)],
      .atom (.load (.n (j + 2)) (.n ich) lvl), .atom (.load (.n (j + 3)) (.n ls) lvl),
      .atom (.mul (.n (j + 4)) (.n (j + 3)) (.n (j + 1))), .atom (.add (.n (j + 5)) (.n (j + 2)) (.n (j + 4))),
      .atom (.load (.n (j + 5)) (.n ich) (lvl + 1))], m2, j + 6)

/-- Every level's residual sum, from `k`. -/
def osResiduals (c : OsCfg) (ich bd ls : ℕ) : ℕ → List OsLv → List OsMat → ℕ → List Stmt × ℕ
  | _, [], _, k => ([], k)
  | lvl, lv :: rest, mats, k =>
    let r := osResidual c ich bd ls lvl lv mats k
    let t := osResiduals c ich bd ls (lvl + 1) rest r.2.1 r.2.2
    (r.1 ++ t.1, t.2)

/-- The factors of an out-of-domain weight (G:1750-1755) over the coordinates `(z slot, source)`,
from the scalar `sc` at `k`: each `sc ← sc·(1 + z + c)`. The statements, the weight and the next
free value. -/
def osOodFacs (sc : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → List Stmt × ℕ × ℕ
  | [], k => ([], sc, k)
  | (zo, src) :: rest, k =>
    let r := osOodFacs (k + 5) rest (k + 6)
    ([.atom (.const (.n k) (word 1 0 0)), .atom (.load (.n (k + 1)) (.n osOodz) zo),
      .atom (.add (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.load (.n (k + 3)) (.n src.1) src.2),
      .atom (.add (.n (k + 4)) (.n (k + 2)) (.n (k + 3))), .atom (.mul (.n (k + 5)) (.n sc) (.n (k + 4)))] ++
      r.1, r.2)

/-- The out-of-domain weight of the commitment level `ol` reads, its sample `0` (G:1747-1756),
after `prevCols` message coordinates, from `k`: the scalar, then the factors. -/
def osOodWeight (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (k : ℕ) : List Stmt × ℕ × ℕ :=
  let zf := prevCols - c.yrLog
  let r := osOodFacs k ((List.range (zf + c.yrLog)).map fun t ↦
    (ol * ligColsCap + t, if t < zf then (osFch, lv.foldsOff + t) else (tch, t - zf))) (k + 1)
  (.atom (.load (.n k) (.n osOod) (ol * oodSlots)) :: r.1, r.2)

/-- The out-of-domain weights of the levels `ol ..` (each with one sample), summed into `acc`, from
`k`: the statements, the sum and the next free value. -/
def osOodWeights (c : OsCfg) (tch : ℕ) :
    ℕ → ℕ → List OsLv → Option ℕ → ℕ → List Stmt × Option ℕ × ℕ
  | _, _, [], acc, k => ([], acc, k)
  | prevCols, ol, lv :: rest, acc, k =>
    let w := osOodWeight c tch prevCols ol lv k
    let a : List Stmt × Option ℕ × ℕ := match acc with
      | none => ([], some w.2.1, w.2.2)
      | some x => ([.atom (.add (.n w.2.2) (.n x) (.n w.2.1))], some w.2.2, w.2.2 + 1)
    let t := osOodWeights c tch lv.logCols (ol + 1) rest a.2.1 a.2.2
    (w.1 ++ a.1 ++ t.1, t.2)

/-- The body after the tail (G:1667-1757), from the tail's state `st` and `tail_challenges` at
`tch`: the residual's value, the point, the basis rows, the residual sums, the out-of-domain
weights, the returns. -/
def osFinish (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt :=
  let n := c.levels.length
  let yat := st.k
  let pt := yat + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bd := pts.2 + 1
  let ls := pts.2 + 3
  let bs := osBases c tch bd ls 0 c.levels (pts.2 + 4)
  let ich := bs.2 + 1
  let rs := osResiduals c ich bd ls 0 c.levels st.mats (bs.2 + 3)
  let od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2
  let k := od.2.2
  [.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n yat],
    .atom (.hint (.alloc (.n pt) pointCap)), .atom (.hint (.alloc (.n (pt + 1)) pointCap))] ++
    pts.1 ++ osHeap (n * ligColsCap) pts.2 ++ osHeap n (pts.2 + 2) ++ bs.1 ++
    osHeap (n + 1) bs.2 ++
    [.atom (.const (.n (bs.2 + 2)) (word 0 0 0)), .atom (.load (.n (bs.2 + 2)) (.n ich) 0)] ++
    rs.1 ++ od.1 ++
    [.atom (.copy (.n k) (.n st.t)), .atom (.copy (.n (k + 1)) (.n pt)),
      .atom (.copy (.n (k + 2)) (.n (pt + 1))), .atom (.load (.n (k + 3)) (.n ich) n),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (od.2.1.getD 0))), .atom (.copy (.n (k + 5)) (.n yat)),
      .ret [.n k, .n (k + 1), .n (k + 2), .n (k + 4), .n (k + 5)]]

/-- **The body of `open_stacked` at a configuration.** -/
def osBody (c : OsCfg) : List Stmt :=
  let h := osHead c
  let lv := osLevels c 0 c.levels h.2
  let tl := osTail c lv.2
  h.1 ++ lv.1 ++ tl.1 ++ osFinish c tl.2.1 tl.2.2

end
end LeanVM.Guest.B1.Whir
