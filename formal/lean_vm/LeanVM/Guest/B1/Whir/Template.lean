/-
  LeanVM.Guest.B1.Whir.Template

  The core IR of `open_stacked`, generated from a size's configuration as the expansion numbers
  it: the levels (fold rounds, the next commitment or the final lane, the query positions' dispatch,
  `λ`, the high part, the queries' dispatch, the glue), the closing rounds, the point, the induced
  bases, the residual chains' dispatches and the out-of-domain weights.
-/

module

public import LeanVM.Guest.B1.Whir.Config
public import LeanVM.Guest.B1.Whir.Split
public import LeanVM.Guest.Word
public import LeanVM.Guest.Renumber

/-!
# The template of `open_stacked` (TRIAGE G #42)

`osBody c` is the body of `open_stacked__L{c.m}` (`lean_ethereum.py`, `open_stacked`, G below) at
the configuration `c = osCfg m`, value by value as the expansion numbers it: every block takes the
state `OsSt` (the first free value `k`, the sponge's capacity cells, the cursor as a base value and
a word offset, the running claim, the shifted pointers materialized so far) and returns the next,
with the values later blocks read (`OsSt`'s transient fields). The body depends on the size alone:
where a rate changes a level's shape it dispatches on the rate's selector, value `0` (`.dispatch`),
into a helper specialized on that rate's row (`level_positions`, `level_queries`,
`level_residual`, their templates in `Whir/HelperT.lean`), the names taken from every rate's levels
(`OsCfg.lvAt`). The inline helpers are expanded in place: `fs_next`, `fs_pack`, `fs_absorb_nonce`,
`fs_cap`, `residual_query` and `novel_eval`.

`Whir/Data*.lean` check every size's body equal to this by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Protocol

@[expose] public section

/-! ## Small blocks -/

/-- `g^e` as a word. -/
def gw (e : ℕ) : E := E.ofLimbs (gpowK e) 0

/-- A constant. -/
abbrev osCst (k : ℕ) (c : E) : Stmt := .atom (.const (.n k) c)

/-- `d = mem[p·g^off]`. -/
abbrev osLd (d p off : ℕ) : Stmt := .atom (.load (.n d) (.n p) off)

/-- `d = a·b`. -/
abbrev osMul (d a b : ℕ) : Stmt := .atom (.mul (.n d) (.n a) (.n b))

/-- `d = a + b`. -/
abbrev osAdd (d a b : ℕ) : Stmt := .atom (.add (.n d) (.n a) (.n b))

/-- `d = s`. -/
abbrev osCp (d s : ℕ) : Stmt := .atom (.copy (.n d) (.n s))

/-- Values `k .. k + n - 1`. -/
def osRun (k n : ℕ) : List V := (List.range n).map fun j ↦ .n (k + j)

/-- One `KECCAK` in the even layouts reading the cells `ins`, writing `out .. out + 12`. -/
def osKeccak (ins : List ℕ) (out : ℕ) : Stmt := .atom (.keccak (ins.map V.n) (osRun out 13) false false)

/-- `HeapBuf(g^e)` at `k`: its size `k`, its pointer `k + 1`. -/
def osHeap (e k : ℕ) : List Stmt :=
  [osCst k (gw e), .atom (.hint (.allocDyn (.n (k + 1)) (.n k)))]

/-! ## Products in `K` of the vanishing tables -/

/-- The carry-less product of two 64-bit words, before reduction. -/
def clmulN (a b : ℕ) : ℕ :=
  (List.range 64).foldl (fun r i ↦ if b.testBit i then r ^^^ (a <<< i) else r) 0

/-- Reduction modulo `x^64 + x^4 + x^3 + x + 1`, from the top bit `126` down. -/
def redN (r : ℕ) : ℕ :=
  (List.range 63).foldl (fun r j ↦
    if r.testBit (126 - j) then r ^^^ ((2 ^ 64 + 27) <<< (62 - j)) else r) r

/-- A product in `K` of two words given by their bits. -/
def kmulN (a b : ℕ) : ℕ := redN (clmulN a b)

/-- The normalizer of a high-part coefficient: the product of the vanishing
inverses `vanishInv (v + i)` over the set bits `i < bits` of `c`, from `init`. -/
def hsScale (v bits c init : ℕ) : ℕ :=
  (List.range bits).foldl (fun sc i ↦ if c.testBit i then kmulN sc (vanishInv (v + i)) else sc) init

/-! ## Materialized pointers -/

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

/-- The pointer `base·g^off` as the compiler materializes it, from `k`, the materializations so
far `mats`: none when the offset is zero; a second materialization repeats the first's product; a
first is from the base or, as the plan says, from an earlier one. The statements, the pointer's
value and the next free value. -/
def osMatP (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) : List Stmt × ℕ × ℕ :=
  if off = 0 then ([], base, k)
  else
    let sd : ℕ × ℕ := match mats.find? (fun m ↦ m.base == base && m.exp == off) with
      | some m => (m.src, m.dist)
      | none => osMatSrc plan mats base off
    ([osCst k (gw sd.2), osMul (k + 1) sd.1 k], k + 1, k + 2)

/-- The materializations after `osMatP plan mats base off k`. -/
def osMatsAfter (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) : List OsMat :=
  if off = 0 then mats
  else match mats.find? (fun m ↦ m.base == base && m.exp == off) with
    | some _ => mats
    | none =>
      let sd := osMatSrc plan mats base off
      mats ++ [⟨base, off, k + 1, sd.1, sd.2⟩]

/-- The pointer `base·g^off` of a value that is not one of the fixed buffers (the cursor, a loop's
parameter): materialized from `base` itself. -/
def osMat (base off k : ℕ) : List Stmt × ℕ × ℕ :=
  if off = 0 then ([], base, k) else ([osCst k (gw off), osMul (k + 1) base k], k + 1, k + 2)

/-! ## Powers and loops -/

/-- `x^e` by the compiler's square-and-multiply from `acc = x` over the digits after the leading
one, from `k`: the statements and the result. -/
def osPowSteps (x : ℕ) : List Bool → ℕ → ℕ → List Stmt × ℕ
  | [], acc, _ => ([], acc)
  | d :: ds, acc, k =>
    if d then
      let r := osPowSteps x ds (k + 1) (k + 2)
      (osMul k acc acc :: osMul (k + 1) k x :: r.1, r.2)
    else
      let r := osPowSteps x ds k (k + 1)
      (osMul k acc acc :: r.1, r.2)

/-- The binary digits of `e` after its leading one, most significant first. -/
def osPowDigits (e : ℕ) : List Bool := (Nat.bits e).reverse.tail

/-- The values `osPowSteps` takes for `e`'s digits. -/
def osPowLen (e : ℕ) : ℕ := (osPowDigits e).length + ((osPowDigits e).filter id).length

/-- The `mul_range` loop's tail (`x·g ≠ N`: call the loop at `x·g`), from `k`, for a helper of
`n` parameters, the first the counter and the second the bound. -/
def osLoopTail (name : String) (n k : ℕ) : List Stmt :=
  [osCst k (gw 1), osMul (k + 1) 0 k, osAdd (k + 2) (k + 1) 1, osCst (k + 3) (gw 1),
    osMul (k + 4) 0 (k + 3), .callIf (.n (k + 2)) name (.n (k + 4) :: (List.range (n - 1)).map fun i ↦ .n (i + 1)),
    .ret []]

/-- A loop's entry `for x in mul_range(g^e0, g^n)`, from `k`: the guard `g^e0 + g^n` at `k + 2`,
the loop called at `[g^e0, g^n] ++ args`. -/
def osLoopCall (name : String) (e0 n : ℕ) (args : List ℕ) (k : ℕ) : List Stmt :=
  [osCst k (gw e0), osCst (k + 1) (gw n), osAdd (k + 2) k (k + 1), osCst (k + 3) (gw e0),
    osCst (k + 4) (gw n), .callIf (.n (k + 2)) name (.n (k + 3) :: .n (k + 4) :: args.map V.n)]

/-- The zero run the sponge's padding reads, allocated at its first use: the statements, its first
cell (`1`; the next four are `0`) and the next free value. -/
def osPad (pad : Option ℕ) (k : ℕ) : List Stmt × ℕ × ℕ :=
  match pad with
  | some p => ([], p, k)
  | none => ([osCst k (word 1 0), osCst (k + 1) (word 0 0), osCst (k + 2) (word 0 0),
      osCst (k + 3) (word 0 0), osCst (k + 4) (word 0 0)], k, k + 5)

/-! ## `residual_query` and `novel_eval` inline -/

/-- One level of `novel_eval`'s fold: `out[m] = in[2m] + w·in[2m + 1]`, the last
copied when the count is odd; at level `0` the inputs are loaded from `hp·g^(ho + ·)`. The
statements, the outputs and the next free value. -/
def osNovelLevel (hp ho : ℕ) (ins : Option (List ℕ)) (nIn w : ℕ) : ℕ → ℕ → List Stmt × List ℕ × ℕ
  | 0, k => ([], [], k)
  | f + 1, k =>
    let m := (nIn + 1) / 2 - (f + 1)
    let two := 2 * m + 1 < nIn
    let lo : List Stmt × ℕ × ℕ := match ins with
      | none => ([osLd k hp (ho + 2 * m)], k, k + 1)
      | some vs => ([], vs.getD (2 * m) 0, k)
    let hi : List Stmt × ℕ × ℕ := if two then
        match ins with
        | none => ([osLd lo.2.2 hp (ho + 2 * m + 1)], lo.2.2, lo.2.2 + 1)
        | some vs => ([], vs.getD (2 * m + 1) 0, lo.2.2)
      else ([], 0, lo.2.2)
    let j := hi.2.2
    let o : List Stmt × ℕ × ℕ :=
      if two then ([osMul j w hi.2.1, osAdd (j + 1) lo.2.1 j], j + 1, j + 2)
      else ([osCp j lo.2.1], j, j + 1)
    let r := osNovelLevel hp ho ins nIn w f o.2.2
    (lo.1 ++ hi.1 ++ o.1 ++ r.1, o.2.1 :: r.2.1, r.2.2)

/-- `novel_eval(hs, ws, n, nbits)` on the coefficients at `hp·g^ho` and the values
`ws`: the levels `i .. nbits - 1`, the current values `ins` (`none` before level `0`). The
statements, the result and the next free value. -/
def osNovelLevels (hp ho n nbits : ℕ) (ws : List ℕ) : ℕ → ℕ → Option (List ℕ) → ℕ → List Stmt × ℕ × ℕ
  | 0, _, ins, k => ([], ((ins.getD []).headD 0), k)
  | f + 1, i, ins, k =>
    let nIn := (n + 2 ^ i - 1) / 2 ^ i
    let l := osNovelLevel hp ho ins nIn (ws.getD i 0) ((nIn + 1) / 2) k
    let r := osNovelLevels hp ho n nbits ws f (i + 1) (some l.2.1) l.2.2
    (l.1 ++ r.1, r.2)

/-- `novel_eval` from `k`: one load when `nbits = 0`, else the levels. -/
def osNovelEval (hp ho n nbits : ℕ) (ws : List ℕ) (k : ℕ) : List Stmt × ℕ × ℕ :=
  if nbits = 0 then ([osLd k hp ho], k, k + 1) else osNovelLevels hp ho n nbits ws nbits 0 none k

/-- The chain of `residual_query` from coordinate `t`: `chain ← chain·(chain + v)`
over the vanishing values from `vo`, the first `HIGH_BITS_CAP - 1` kept as `ws`, the product
`pe·(d_t + chain_t)` over the row at `bd·g^ro` but at the last. The statements, the final chain,
the product, the `ws` and the next free value. -/
def osResChain (bd ro vo ncols : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ → List Stmt × ℕ × ℕ × List ℕ × ℕ
  | 0, _, ch, pe, ws, k => ([], ch, pe, ws, k)
  | f + 1, t, ch, pe, ws, k =>
    let ws' := if t < 3 then ws ++ [k + 2] else ws
    let up := [osCst k (word (vanishVal (vo + t - 1)) 0), osAdd (k + 1) ch k, osMul (k + 2) ch (k + 1)]
    if t = ncols then
      let r := osResChain bd ro vo ncols f (t + 1) (k + 2) pe ws' (k + 3)
      (up ++ r.1, r.2)
    else
      let r := osResChain bd ro vo ncols f (t + 1) (k + 2) (k + 5) ws' (k + 6)
      (up ++ [osLd (k + 3) bd (ro + t), osAdd (k + 4) (k + 3) (k + 2), osMul (k + 5) pe (k + 4)] ++ r.1,
        r.2)

/-- `residual_query(pos, row_d, hs, …)` inline from `k`: `ws[0]` the position's
copy, the product's first factor, the chain, then the high part's share `chain·novel_eval(hs, ws)`
(the coefficients at `hp·g^ho`). The statements, the product, the share and the next free
value. -/
def osResQuery (pos bd ro hp ho vo ncols nhs hbits k : ℕ) : List Stmt × ℕ × ℕ × ℕ :=
  let c := osResChain bd ro vo ncols ncols 1 pos (k + 2) [k] (k + 3)
  let ne := osNovelEval hp ho nhs hbits c.2.2.2.1 c.2.2.2.2
  ([osCp k pos, osLd (k + 1) bd ro, osAdd (k + 2) (k + 1) pos] ++ c.1 ++ ne.1 ++
      [osMul ne.2.2 c.2.1 ne.2.1],
    c.2.2.1, ne.2.2, ne.2.2 + 1)

/-- One query of a residual chain, its position loaded from `pp·g^j`:
`h ← (h + eq)·μ`, `hh ← (hh + high)·μ`. The statements, the new `h`, `hh` and the next free
value. -/
def osResStep (pp bd ro hp ho vo ncols nhs hbits mu j h hh k : ℕ) : List Stmt × ℕ × ℕ × ℕ :=
  let q := osResQuery k bd ro hp ho vo ncols nhs hbits (k + 1)
  let e := q.2.2.2
  (osLd k pp j :: q.1 ++
      [osAdd e h q.2.1, osMul (e + 1) e mu, osAdd (e + 2) hh q.2.2.1, osMul (e + 3) (e + 2) mu],
    e + 1, e + 3, e + 4)

/-- The steps at the position offsets `js`. -/
def osResSteps (pp bd ro hp ho vo ncols nhs hbits mu : ℕ) :
    List ℕ → ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ × ℕ
  | [], h, hh, k => ([], h, hh, k)
  | j :: js, h, hh, k =>
    let r := osResStep pp bd ro hp ho vo ncols nhs hbits mu j h hh k
    let t := osResSteps pp bd ro hp ho vo ncols nhs hbits mu js r.2.1 r.2.2.1 r.2.2.2
    (r.1 ++ t.1, t.2)

/-! ## The running state -/

/-- The values the body carries between its blocks, and the values a block leaves for later
ones. -/
structure OsSt where
  /-- The next free value. -/
  k : ℕ
  /-- The sponge's five capacity cells. -/
  fs : List ℕ
  /-- The cursor: a base value and a word offset. -/
  cb : ℕ
  co : ℕ
  /-- The running claim. -/
  claim : ℕ
  /-- The zero run, once allocated. -/
  pad : Option ℕ
  /-- The shifted pointers materialized so far (of the fixed buffers). -/
  mats : List OsMat
  /-- The last permutation's first two cells: the first query word, and the proof of work. -/
  word0 : ℕ := 0
  pow0 : ℕ := 0
  /-- A non-final level's sent words (`sent`) and its out-of-domain values. -/
  sent : ℕ := 0
  ys : List ℕ := []
  /-- A non-final level's `λ` and `1/λ`. -/
  lam : ℕ := 0
  lamInv : ℕ := 0
  /-- The final level's high-part buffer. -/
  hs : ℕ := 0
  /-- The level's queries' returned value. -/
  batched : ℕ := 0
  /-- `λ^n`, the level's queries' last returned value. -/
  lamPow : ℕ := 0
  deriving Repr, Inhabited

/-- The rate's selector `g^r`, the body's first argument, which the dispatches read. -/
abbrev osRate : ℕ := 0

/-- The fixed buffers' pointers, allocated by the head. -/
abbrev osFmsg : ℕ := 12
abbrev osRoots : ℕ := 14
abbrev osFch : ℕ := 16
abbrev osCoefs : ℕ := 18
abbrev osBetas : ℕ := 20
abbrev osMus : ℕ := 22
abbrev osHs : ℕ := 24
abbrev osOodz : ℕ := 26
abbrev osOodSc : ℕ := 28
abbrev osQpos : ℕ := 30
abbrev osQbp : ℕ := 32

/-- The parameter `tabs`. -/
abbrev osTabs : ℕ := 10

/-- A fixed buffer's pointer `base·g^off`, materialized as the plan says (`osMatP`), the state's
`k` and materializations moved on. -/
def osMatS (plan : List (ℕ × ℕ × ℕ)) (base off : ℕ) (s : OsSt) : List Stmt × ℕ × OsSt :=
  let r := osMatP plan s.mats base off s.k
  (r.1, r.2.1, { s with k := r.2.2, mats := osMatsAfter plan s.mats base off s.k })

/-- The cursor, materialized at its offset. -/
def osCurS (s : OsSt) : List Stmt × ℕ × OsSt :=
  let r := osMat s.cb s.co s.k
  (r.1, r.2.1, { s with k := r.2.2 })

/-! ## The head and the levels -/

/-- The head: the fixed buffers, the commitment's root into `level_roots`. The arguments are the
rate's selector `0`, the sponge `1 .. 5`, the target `6`, the root `7, 8`, the cursor `9` and the
window table `10`. -/
def osHead (c : OsCfg) : List Stmt × OsSt :=
  let n := c.levels.length
  let lastFolds := (c.levels.getD c.yrLevel default).folds
  (osHeap (c.yrLen + lastFolds) 11 ++ osHeap (2 * n) 13 ++ [osLd 7 osRoots 0, osLd 8 osRoots 1] ++
    osHeap c.nFolds 15 ++ osHeap (2 * c.nFolds) 17 ++ osHeap n 19 ++ osHeap n 21 ++
    osHeap (n * hsStride) 23 ++ osHeap (n * ligColsCap) 25 ++ osHeap n 27 ++
    osHeap (n * ligPosCap) 29 ++ osHeap (n * ligPosCap) 31,
   { k := 33, fs := [1, 2, 3, 4, 5], cb := 9, co := 0, claim := 6, pad := none, mats := [] })

/-- One fold round (`opening_round`): the cursor, the round's `α` slot and its
`α, β` slots materialized, the call. -/
def osRound (P : List (ℕ × ℕ × ℕ)) (i : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let cu := osCurS s
  let fp := osMatS P osFch i cu.2.2
  let cp := osMatS P osCoefs (2 * i) fp.2.2
  let r := cp.2.2.k
  (cu.1 ++ fp.1 ++ cp.1 ++
      [.call "opening_round" ((s.fs ++ [cu.2.1, s.claim, osTabs, fp.2.1, cp.2.1]).map V.n) (osRun r 7)],
   { cp.2.2 with k := r + 7, fs := [r, r + 1, r + 2, r + 3, r + 4], cb := r + 5, co := 0,
                 claim := r + 6 })

/-- The rounds `i .. i + n - 1`. -/
def osRounds (P : List (ℕ × ℕ × ℕ)) : ℕ → ℕ → OsSt → List Stmt × OsSt
  | _, 0, s => ([], s)
  | i, n + 1, s =>
    let r := osRound P i s
    let t := osRounds P (i + 1) n r.2
    (r.1 ++ t.1, t.2)

/-- The final level's message: the final lane and the query nonce, `opening_message`
into `final_msg`. -/
def osFinalMsg (c : OsCfg) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let cu := osCurS s
  let r := cu.2.2.k
  (cu.1 ++ [.call ("opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1")
      ((s.fs ++ [cu.2.1, osFmsg]).map V.n) (osRun r 8)],
   { cu.2.2 with k := r + 8, fs := [r + 2, r + 3, r + 4, r + 5, r + 6], cb := r + 7, co := 0,
                 word0 := r, pow0 := r + 1 })

/-- `OOD_GRIND_BITS`, every later level's too. -/
abbrev levelOodGrind : ℕ := 15

/-- A non-final level's next commitment: `sent` (the next root and the high part)
and the OOD nonce by `opening_message`, its grind, the root into `level_roots`, the OOD point
(`squeeze_point_from`, its first coordinate the nonce's permutation's), its value and the query
nonce absorbed (`fs_next`, `fs_absorb_nonce`), the padding allocated at its first use. -/
def osCommit (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let sent := k + 1
  let cu := osCurS { s with k := k + 2 }
  let r := cu.2.2.k
  let s1 : OsSt := { cu.2.2 with k := r + 10 }
  let o0 := osMatS c.plan osOodz ((lvl + 1) * ligColsCap) s1
  let q := o0.2.2.k
  let b := q + 10
  let cb := r + 7
  let pd := osPad o0.2.2.pad (b + 6)
  let p := pd.2.1
  let j := pd.2.2
  (osHeap (2 + lv.folds) k ++ cu.1 ++
    [.call ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1") ((s.fs ++ [cu.2.1, sent]).map V.n)
      (osRun r 8),
      .call ("grind_check__L" ++ natStr levelOodGrind) [.n (r + 1), .n osTabs] [],
      osLd (r + 8) sent 0, osLd (r + 8) osRoots (2 * lvl + 2),
      osLd (r + 9) sent 1, osLd (r + 9) osRoots (2 * lvl + 3)] ++ o0.1 ++
    [.call ("squeeze_point_from__L" ++ natStr lv.logCols)
      ([r + 2, r + 3, r + 4, r + 5, r + 6, r, o0.2.1].map V.n) (osRun q 5)] ++
    ((List.range 5).map fun i ↦ osCp (q + 5 + i) (q + i)) ++
    [osLd b cb 0, osCp (b + 1) b, osCst (b + 2) (word 0 1),
      osLd (b + 3) cb 1, osCp (b + 4) (b + 3), osCst (b + 5) (word 0 4)] ++ pd.1 ++
    [osKeccak [b + 1, b + 2, b + 4, b + 5, p + 1, p + 2, p + 3, p + 4, q + 5, q + 6, q + 7, q + 8,
      q + 9] j],
   { o0.2.2 with k := j + 13, fs := [j + 8, j + 9, j + 10, j + 11, j + 12], cb := cb, co := 2,
                 pad := some p, word0 := j, pow0 := j + 1, sent := sent, ys := [b] })

/-- `QUERY_GRIND_BITS`. -/
abbrev queryGrind : ℕ := 17

/-- The name of `level_positions`' specialization at a level's row. -/
def osPositionsName (lv : OsLv) : String :=
  "level_positions__L" ++ natStr lv.squeezes ++ "_L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth

/-- The query positions: the level's slots of `query_positions` and `query_win_ptrs`
materialized, the dispatch on the rate into `level_positions` (the first word decoded, the other
squeezes, decoded), its returned capacity the sponge's. -/
def osPositions (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let qp := osMatS c.plan osQpos lv.posOff s
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  let j := wp.2.2.k
  (qp.1 ++ wp.1 ++
    [.dispatch (.n osRate) ((c.lvAt lvl).map osPositionsName)
      ((s.word0 :: s.fs ++ [qp.2.1, wp.2.1, osTabs]).map V.n) (osRun j 5)],
   { wp.2.2 with k := j + 5, fs := [j, j + 1, j + 2, j + 3, j + 4] })

/-- A non-final level's batching challenge: the sponge's capacity copied (`fs_cap`), the query
message's last squeeze (`squeeze`, the padding's cells), `λ` (`challenge_from_state`'s copy) and
`1/λ`. -/
def osLam (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let pd := osPad s.pad (k + 5)
  let p := pd.2.1
  let j := pd.2.2
  ((s.fs.zipIdx.map fun (f, i) ↦ osCp (k + i) f) ++ pd.1 ++
    [osKeccak ([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4] ++ [k, k + 1, k + 2, k + 3, k + 4]) j,
      osCp (j + 13) j, osCst (j + 14) (word 1 0), osMul (j + 14) (j + 15) (j + 13)],
   { s with k := j + 16, fs := [j + 8, j + 9, j + 10, j + 11, j + 12], pad := some p,
            lam := j + 13, lamInv := j + 15 })

/-- A high-part coefficient scaled: loaded from `src·g^i`, times its normalizer
`sc` (no product when it is `1`), stored at `dst·g^o`. -/
def osHsCoef (src i sc dst o k : ℕ) : List Stmt × ℕ :=
  if sc = 1 then ([osLd k src i, osLd k dst o], k + 1)
  else ([osLd k src i, osCst (k + 1) (word sc 0), osMul (k + 2) k (k + 1), osLd (k + 2) dst o], k + 3)

/-- The coefficients `i ..` of a high part. -/
def osHsCoefs (src dst : ℕ) (sc : ℕ → ℕ) (si di : ℕ) : ℕ → ℕ → ℕ → List Stmt × ℕ
  | 0, _, k => ([], k)
  | n + 1, i, k =>
    let r := osHsCoef src (si + i) (sc i) dst (di + i) k
    let t := osHsCoefs src dst sc si di n (i + 1) r.2
    (r.1 ++ t.1, t.2)

/-- A non-final level's high part, normalized, into `level_hs`. -/
def osHsMid (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let r := osHsCoefs s.sent osHs
    (fun c ↦ hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 2 (lvl * hsStride)
    lv.folds 0 s.k
  (r.1, { s with k := r.2 })

/-- The final level's lane, normalized, into a fresh `hs`. -/
def osHsFinal (c : OsCfg) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let n := c.yrLen + lv.folds
  let hs := s.k + 1
  let r := osHsCoefs osFmsg hs (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 n 0 (s.k + 2)
  (osHeap n s.k ++ r.1, { s with k := r.2, hs := hs })

/-- The name of `level_queries`' specialization at a level's row: the queries, the base (`1` at
level `0`), the folds, the leaf's cells, the tree and cap depths, and at the final level the
message log, the lane's length and index bits and `1` (else zeros). -/
def osQueriesName (c : OsCfg) (lvl : ℕ) (lv : OsLv) : String :=
  let base := if lvl = 0 then 1 else 0
  let fin := lvl = c.yrLevel
  "level_queries__L" ++ natStr lv.queries ++ "_L" ++ natStr base ++ "_L" ++
    natStr lv.folds ++ "_L" ++ natStr lv.leafCells ++ "_L" ++ natStr lv.depth ++ "_L" ++
    natStr lv.capDepth ++ "_L" ++ natStr (if fin then lv.logCols else 0) ++ "_L" ++
    natStr (if fin then c.yrLen + lv.folds else 0) ++ "_L" ++ natStr (if fin then c.yrLog + 1 else 0) ++
    "_L" ++ natStr (if fin then 1 else 0)

/-- The level's queries: `λ` and `1/λ` (`0, 0` at the final level), the round coefficients, the
high part, the positions and windows, the dispatch on the rate into `level_queries` (the cap
checked up to its root, the queries' sum, `λ^n`), the root into `level_roots`. -/
def osQueries (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let fin := lvl = c.yrLevel
  let li : List Stmt × ℕ × ℕ × OsSt :=
    if fin then ([osCst s.k (word 0 0), osCst (s.k + 1) (word 0 0)], s.k, s.k + 1, { s with k := s.k + 2 })
    else ([], s.lam, s.lamInv, s)
  let cf := osMatS c.plan osCoefs (2 * lv.foldsOff) li.2.2.2
  let hp : List Stmt × ℕ × OsSt :=
    if fin then ([], s.hs, cf.2.2) else osMatS c.plan osHs (lvl * hsStride) cf.2.2
  let qp := osMatS c.plan osQpos lv.posOff hp.2.2
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  let r := wp.2.2.k
  (li.1 ++ cf.1 ++ hp.1 ++ qp.1 ++ wp.1 ++
    [.dispatch (.n osRate) ((c.lvAt lvl).map (osQueriesName c lvl))
        ([li.2.1, li.2.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1].map V.n) (osRun r 4),
      osLd r osRoots (2 * lvl), osLd (r + 1) osRoots (2 * lvl + 1)],
   { wp.2.2 with k := r + 4, batched := r + 2, lamPow := r + 3 })

/-- A non-final level's claims glued: the out-of-domain claim with `λ` (stored in
`ood_scalars`), the query batch with `λ^2·λ^n` (stored in `level_scales`), `1/λ` into
`level_lam_invs`. -/
def osGlue (lvl : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let lam := s.lam
  let y0 := s.ys.getD 0 0
  ([osLd lam osOodSc (lvl + 1), osMul k lam y0, osAdd (k + 1) s.claim k, osMul (k + 2) lam lam,
    osMul (k + 3) (k + 2) s.lamPow, osMul (k + 4) (k + 3) s.batched, osAdd (k + 5) (k + 1) (k + 4),
    osLd (k + 3) osBetas lvl, osLd s.lamInv osMus lvl],
   { s with k := k + 6, claim := k + 5 })

/-- One level. -/
def osLevel (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let fin := lvl = c.yrLevel
  let f := osRounds c.plan lv.foldsOff lv.folds s
  let m := if fin then osFinalMsg c lv f.2 else osCommit c lvl lv f.2
  let gr : List Stmt := [.call ("grind_check__L" ++ natStr queryGrind) [.n m.2.pow0, .n osTabs] []]
  let sq := osPositions c lvl lv m.2
  let la := if fin then (([] : List Stmt), sq.2) else osLam sq.2
  let h := if fin then osHsFinal c lv la.2 else osHsMid lvl lv la.2
  let q := osQueries c lvl lv h.2
  let g := if fin then (([] : List Stmt), q.2) else osGlue lvl q.2
  (f.1 ++ m.1 ++ gr ++ sq.1 ++ la.1 ++ h.1 ++ q.1 ++ g.1, g.2)

/-- The levels `lvl ..`. -/
def osLevels (c : OsCfg) : ℕ → List OsLv → OsSt → List Stmt × OsSt
  | _, [], s => ([], s)
  | lvl, lv :: rest, s =>
    let r := osLevel c lvl lv s
    let t := osLevels c (lvl + 1) rest r.2
    (r.1 ++ t.1, t.2)

/-! ## The closing rounds and the rest -/

/-- One closing round (`opening_tail_round`), its challenge stored at `tch·g^j`. -/
def osTailRound (tch j : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let cu := osCurS s
  let r := cu.2.2.k
  (cu.1 ++ [.call "opening_tail_round" ((s.fs ++ [cu.2.1, s.claim, osTabs]).map V.n) (osRun r 8),
      osLd (r + 7) tch j],
   { cu.2.2 with k := r + 8, fs := [r, r + 1, r + 2, r + 3, r + 4], cb := r + 5, co := 0,
                 claim := r + 6 })

/-- The closing rounds `j ..`. -/
def osTailRounds (tch : ℕ) : ℕ → ℕ → OsSt → List Stmt × OsSt
  | _, 0, s => ([], s)
  | j, n + 1, s =>
    let r := osTailRound tch j s
    let t := osTailRounds tch (j + 1) n r.2
    (r.1 ++ t.1, t.2)

/-- The closing rounds into `tail_challenges` (`HeapBuf(g^5)` at `k + 1`), the
unused entries zeroed. The statements, the state and the buffer. -/
def osTail (c : OsCfg) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let tch := s.k + 1
  let f := osTailRounds tch 0 c.yrLog { s with k := s.k + 2 }
  let j := f.2.k
  (osHeap yrLogCap s.k ++ f.1 ++
    ((List.range (yrLogCap - c.yrLog)).map fun i ↦
      [osCst (j + i) (word 0 0), osLd (j + i) tch (c.yrLog + i)]).flatten,
   { f.2 with k := j + (yrLogCap - c.yrLog) }, tch)

/-- The source of entry `i` of the rotated point: the fold challenges past the lane
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
    ([osLd k b o, osLd k pt i, osCst (k + 1) (word 1 0), osLd (k + 2) b o, osAdd (k + 3) (k + 1) (k + 2),
      osLd (k + 3) pt1 i], k + 4)
  | none => ([osCst k (word 0 0), osLd k pt i, osCst (k + 1) (word 1 0), osLd (k + 1) pt1 i], k + 2)

/-- The entries `i ..` of the point, from `k`. -/
def osPtBlks (c : OsCfg) (pt pt1 tch : ℕ) : ℕ → ℕ → ℕ → List Stmt × ℕ
  | _, 0, k => ([], k)
  | i, n + 1, k =>
    let r := osPtBlk pt pt1 i k (osPtSrc c tch i)
    let t := osPtBlks c pt pt1 tch (i + 1) n r.2
    (r.1 ++ t.1, t.2)

/-- One coordinate of a level's basis row: the challenge at `src`, its coefficient
`b = c·inv` (`c` itself when `inv = 1`), `d = (1 + c)/b` stored at `basis_d[slot]`, the scale
times `b`, the product of the challenges times `c` (`c` itself at the first); from `k`. The
statements, the new scale, the new product and the next free value. -/
def osBasisBlk (bd slot : ℕ) (src : ℕ × ℕ) (inv sc : ℕ) (after : Option ℕ) (k : ℕ) :
    List Stmt × ℕ × ℕ × ℕ :=
  let b : List Stmt × ℕ × ℕ :=
    if inv = 1 then ([], k, k + 1) else ([osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1)], k + 2, k + 3)
  let j := b.2.2
  let a : List Stmt × ℕ × ℕ := match after with
    | none => ([], k, j + 4)
    | some x => ([osMul (j + 4) x k], j + 4, j + 5)
  (osLd k src.1 src.2 :: b.1 ++
      [osCst j (word 1 0), osAdd (j + 1) j k, osMul (j + 1) (j + 2) b.2.1, osLd (j + 2) bd slot,
        osMul (j + 3) sc b.2.1] ++ a.1,
    j + 3, a.2.1, a.2.2)

/-- A level's basis coordinates `(slot, source, inverse)`: the fold challenges after its folds,
then the tail challenges. -/
def osBasisCoords (c : OsCfg) (tch lvl : ℕ) (lv : OsLv) : List (ℕ × (ℕ × ℕ) × ℕ) :=
  (List.range (lv.prefixLen + c.yrLog)).map fun t ↦
    (lvl * ligColsCap + t,
      (if t < lv.prefixLen then (osFch, lv.resFoldOff + t) else (tch, t - lv.prefixLen)),
      vanishInv (lv.vanish + t))

/-- The coordinates of a basis row from the scale `sc`, the product `after` and `k`. -/
def osBasisRow (bd : ℕ) : List (ℕ × (ℕ × ℕ) × ℕ) → ℕ → Option ℕ → ℕ → List Stmt × ℕ × ℕ × ℕ
  | [], sc, after, k => ([], sc, after.getD 0, k)
  | (slot, src, inv) :: rest, sc, after, k =>
    let r := osBasisBlk bd slot src inv sc after k
    let t := osBasisRow bd rest r.2.1 (some r.2.2.1) r.2.2.2
    (r.1 ++ t.1, t.2)

/-- The non-final levels' basis rows, scales and products, from `k`. -/
def osBases (c : OsCfg) (tch bd ls la : ℕ) : ℕ → List OsLv → ℕ → List Stmt × ℕ
  | _, [], k => ([], k)
  | lvl, lv :: rest, k =>
    let r := osBasisRow bd (osBasisCoords c tch lvl lv) k none (k + 1)
    let t := osBases c tch bd ls la (lvl + 1) rest r.2.2.2
    (osLd k osBetas lvl :: r.1 ++ [osLd r.2.1 ls lvl, osLd r.2.2.1 la lvl] ++ t.1, t.2)

/-- `RES_BATCH`: the queries a residual loop iteration takes. -/
abbrev resBatch : ℕ := 8

/-- The name of `level_residual`'s specialization at a level's row: the queries, the message
columns, the high part's length and index bits. -/
def osResidualName (lv : OsLv) : String :=
  "level_residual__L" ++ natStr lv.queries ++ "_L" ++ natStr lv.logCols ++ "_L" ++ natStr lv.folds ++
    "_L" ++ natStr lv.highBits

/-- Non-final level `lvl`'s residual chains, from `k` and the materializations `mats`: the level's
slots of `query_positions`, its row of `basis_d` and its high part materialized, `λ⁻¹` read from
`level_lam_invs`, the dispatch on the rate into `level_residual`, the level's sums into `inner_chain`.
The statements, the materializations after it and the next free value. -/
def osResidual (c : OsCfg) (ich bd ls la lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) :
    List Stmt × List OsMat × ℕ :=
  let P := c.plan
  let qp := osMatP P mats osQpos lv.posOff k
  let m1 := osMatsAfter P mats osQpos lv.posOff k
  let bp := osMatP P m1 bd (lvl * ligColsCap) qp.2.2
  let m2 := osMatsAfter P m1 bd (lvl * ligColsCap) qp.2.2
  let hp := osMatP P m2 osHs (lvl * hsStride) bp.2.2
  let m3 := osMatsAfter P m2 osHs (lvl * hsStride) bp.2.2
  let j := hp.2.2
  let a := j + 3
  (qp.1 ++ bp.1 ++ hp.1 ++
    [osLd j osMus lvl,
      .dispatch (.n osRate) ((c.lvAt lvl).map osResidualName) [.n qp.2.1, .n bp.2.1, .n hp.2.1, .n j]
        (osRun (j + 1) 2),
      osLd a ich (2 * lvl), osLd (a + 1) ls lvl, osMul (a + 2) (a + 1) (j + 1), osAdd (a + 3) a (a + 2),
      osLd (a + 3) ich (2 * lvl + 2), osLd (a + 4) ich (2 * lvl + 1), osLd (a + 5) osBetas lvl,
      osLd (a + 6) la lvl, osMul (a + 7) (a + 5) (a + 6), osMul (a + 8) (a + 7) (j + 2),
      osAdd (a + 9) (a + 4) (a + 8), osLd (a + 9) ich (2 * lvl + 3)], m3, a + 10)

/-- The non-final levels' residual chains, from `k`. -/
def osResiduals (c : OsCfg) (ich bd ls la : ℕ) : ℕ → List OsLv → List OsMat → ℕ → List Stmt × ℕ
  | _, [], _, k => ([], k)
  | lvl, lv :: rest, mats, k =>
    let r := osResidual c ich bd ls la lvl lv mats k
    let t := osResiduals c ich bd ls la (lvl + 1) rest r.2.1 r.2.2
    (r.1 ++ t.1, t.2)

/-- The factors of an out-of-domain weight over the coordinates `(z slot, source)`,
from the scalar `sc` at `k`: each `sc ← sc·(1 + z + c)`. The statements, the weight and the next
free value. -/
def osOodFacs (sc : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → List Stmt × ℕ × ℕ
  | [], k => ([], sc, k)
  | (zo, src) :: rest, k =>
    let r := osOodFacs (k + 5) rest (k + 6)
    ([osCst k (word 1 0), osLd (k + 1) osOodz zo, osAdd (k + 2) k (k + 1), osLd (k + 3) src.1 src.2,
      osAdd (k + 4) (k + 2) (k + 3), osMul (k + 5) sc (k + 4)] ++ r.1, r.2)

/-- The out-of-domain claim of the commitment level `ol - 1` reads, after
`prevCols` message coordinates, from `k`: its scalar, then the factors. -/
def osOodWeight (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (k : ℕ) : List Stmt × ℕ × ℕ :=
  let zf := prevCols - c.yrLog
  let row := ol * ligColsCap
  let r := osOodFacs k ((List.range (zf + c.yrLog)).map fun t ↦
    (row + t, if t < zf then (osFch, lv.foldsOff + t) else (tch, t - zf))) (k + 1)
  (osLd k osOodSc ol :: r.1, r.2)

/-- Add a weight to the running sum, the first one alone. -/
def osAcc (acc : Option ℕ) (w k : ℕ) : List Stmt × Option ℕ × ℕ :=
  match acc with
  | none => ([], some w, k)
  | some x => ([osAdd k x w], some k, k + 1)

/-- The out-of-domain weights of the levels `ol ..` (one each), summed into `acc`, from `k`: the
statements, the sum and the next free value. -/
def osOodWeights (c : OsCfg) (tch : ℕ) :
    ℕ → ℕ → List OsLv → Option ℕ → ℕ → List Stmt × Option ℕ × ℕ
  | _, _, [], acc, k => ([], acc, k)
  | prevCols, ol, lv :: rest, acc, k =>
    let w0 := osOodWeight c tch prevCols ol lv k
    let a0 := osAcc acc w0.2.1 w0.2.2
    let t := osOodWeights c tch lv.logCols (ol + 1) rest a0.2.1 a0.2.2
    (w0.1 ++ a0.1 ++ t.1, t.2)

/-- The body after the closing rounds, from their state `st` and `tail_challenges`
at `tch`: the final lane's low part at the tail challenges, the point, the basis rows, the
residual sums, the out-of-domain weights, the returns. -/
def osFinish (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt :=
  let n := c.levels.length
  let mid := c.levels.take c.yrLevel
  let yat := st.k
  let pt := yat + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bd := pts.2 + 1
  let ls := pts.2 + 3
  let la := pts.2 + 5
  let bs := osBases c tch bd ls la 0 mid (pts.2 + 6)
  let ich := bs.2 + 1
  let rs := osResiduals c ich bd ls la 0 mid st.mats (bs.2 + 3)
  let od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2
  let k := od.2.2
  [.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n yat],
    .atom (.hint (.alloc (.n pt) pointCap)), .atom (.hint (.alloc (.n (pt + 1)) pointCap))] ++
    pts.1 ++ osHeap (n * ligColsCap) pts.2 ++ osHeap n (pts.2 + 2) ++ osHeap n (pts.2 + 4) ++ bs.1 ++
    osHeap (2 * n) bs.2 ++ [osCst (bs.2 + 2) (word 0 0), osLd (bs.2 + 2) ich 0, osLd st.claim ich 1] ++
    rs.1 ++ od.1 ++
    [osLd k ich (2 * c.yrLevel + 1), osCp (k + 1) pt, osCp (k + 2) (pt + 1), osLd (k + 3) ich (2 * c.yrLevel),
      osAdd (k + 4) (k + 3) (od.2.1.getD 0), osCp (k + 5) yat,
      .ret [.n k, .n (k + 1), .n (k + 2), .n (k + 4), .n (k + 5)]]

/-- **The body of `open_stacked` at a configuration.** -/
def osBody (c : OsCfg) : List Stmt :=
  let h := osHead c
  let lv := osLevels c 0 c.levels h.2
  let tl := osTail c lv.2
  h.1 ++ lv.1 ++ tl.1 ++ osFinish c tl.2.1 tl.2.2

/-! ## The loop helpers' templates at a level's row

`sqLoopBody` (one squeeze and its `decode_query_windows` an iteration, the positions at the
level's offset) is `level_positions`' loop at offset `0` (`lpLoopBody`, `Whir/HelperT.lean`);
`resLoopBody` (eight queries' induced products and high shares chained by `μ = 1/λ` an
iteration) is the shape of `level_residual`'s batches' loop. -/

/-- The squeeze loop's body, at `x, N, sqz, qpos, qwp, tabs` (values `0 .. 5`):
the row `sqz·x^5`, its capacity loaded, one squeeze, the next capacity stored, the decoded
positions and windows at `g^posOff·x^(128/depth)`, then the loop's tail. -/
def sqLoopBody (lv : OsLv) (name : String) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (128 / lv.depth)) 0 34
  let p1 := osMat 3 lv.posOff (34 + osPowLen (128 / lv.depth))
  let p2 := osMat 4 lv.posOff (p1.2.2 + 1)
  let e := p2.2.2 + 1
  [osMul 6 0 0, osMul 7 6 6, osMul 8 7 0, osMul 9 2 8] ++
    ((List.range 5).map fun i ↦ osLd (10 + i) 9 i) ++
    [osCst 15 (word 1 0), osCst 16 (word 0 0), osCst 17 (word 0 0), osCst 18 (word 0 0),
      osCst 19 (word 0 0), osKeccak [16, 16, 16, 16, 16, 17, 18, 19, 10, 11, 12, 13, 14] 20, osCp 33 20] ++
    ((List.range 5).map fun i ↦ osLd (28 + i) 9 (5 + i)) ++
    pw.1 ++ p1.1 ++ [osMul p1.2.2 p1.2.1 pw.2] ++ p2.1 ++ [osMul p2.2.2 p2.2.1 pw.2] ++
    [.call ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
      [.n 33, .n p1.2.2, .n p2.2.2, .n 5] []] ++
    osLoopTail name 6 e

/-- The residual loop's body, at `xr, N, qpos, basis_d, level_hs, chain, μ` (values
`0 .. 6`): the batch's positions at `qpos·g^posOff·xr^8`, `h, hh = chain[xr]`, eight steps,
`chain[xr·g] = h, hh`, then the loop's tail. -/
def resLoopBody (lvl : ℕ) (lv : OsLv) (name : String) : List Stmt :=
  let pp := osMat 2 lv.posOff 7
  let x := pp.2.2
  let st := osResSteps (x + 3) 3 (lvl * ligColsCap) 4 (lvl * hsStride) lv.vanish lv.logCols lv.folds
    lv.highBits 6 (List.range resBatch) (x + 6) (x + 7) (x + 8)
  pp.1 ++ [osMul x 0 0, osMul (x + 1) x x, osMul (x + 2) (x + 1) (x + 1), osMul (x + 3) pp.2.1 (x + 2),
    osMul (x + 4) 5 0, osMul (x + 5) (x + 4) 0, osLd (x + 6) (x + 5) 0, osLd (x + 7) (x + 5) 1] ++ st.1 ++
    [osLd st.2.1 (x + 5) 2, osLd st.2.2.1 (x + 5) 3] ++
    osLoopTail name 7 st.2.2.2

end
end LeanVM.Guest.B1.Whir
