/-
  LeanVM.Guest.B1.Sig.Template

  The bodies of the signature verifiers' core functions as functions of their constants:
  `verify_lean_xmss`, `verify_sig_lean_sphincs` and the 256 `sp_forest_key` specializations,
  written once from the guest's structure (`lean_ethereum.py`, G:2278-2658) with the values numbered
  as the renumbered expansion numbers them.
-/

module

public import LeanVM.Guest.Renumber

/-!
# The signature verifiers as templates

A template writes out the statements of one guest construct with its values `V.n k` numbered from
a base `b`, in order of first occurrence, as `Fn.renumber` numbers them. `XmssData` and `SphincsData`
prove the data equal to the templates by kernel evaluation, so every later proof reasons about the
templates, once for every instance of a construct.

* `cStep`, `cSteps`, `cWalk`: a WOTS+C chain step, the steps of a chain, a chain's walk
  (`chain_step`, `walk`, G:2307-2331), for leanXMSS (`lx`, the address precomputed, the chain index
  after the value) and leanSPHINCS (the address computed per step, a zero cell after the value);
* `cArm`, `cArms`, `cGroup`: one arm of a digit group's dispatch, its arms, the whole group (the
  digit hint, its bound, the range check and the `match`; `walk_group`, G:2334-2342);
* `hashValues` (G:2345-2360), `merkle` (G:2363-2382), `shifts` (G:2289-2295);
* `spFoldArm`, `spArms` (`sp_fold` with `sp_subtree_arm` or `sp_tree_arm`, G:2481-2516);
* `xBody`, `sBody`, `fkBody`: the three function bodies.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## Words and statement shapes -/

/-- The IV's two cells, as the compiler writes them. -/
def iv0 : E := word 13503953895743350343 11912009169889063794 0
def iv1 : E := word 11170449402626986623 6620516960021240235 0

/-- The metadata cell of a compile-time counter and flag (`hash_flock::metadata`). -/
def mdw (c : Nat) (fin : Bool) : E := word c (if fin then 2 ^ 32 - 1 else 0) 0

/-- An address's type field, `tag · 2^56`. -/
def tw (tag : Nat) : Nat := tag * 2 ^ 56
def hiMul : Nat := 2 ^ 32
def stepMul : Nat := 2 ^ 61
def lxTop : Nat := 2 ^ 55

def cst (b : Nat) (c : E) : Stmt := .atom (.const (.n b) c)
def ivs (b : Nat) : List Stmt := [cst b iv0, cst (b + 1) iv1]
def hintW (s : String) (vs : List V) : Stmt := .atom (.hint (.witness s (.stack vs)))
def b2s (m0 m1 m2 m3 c0 c1 o0 o1 md : V) : Stmt := .atom (.blake2s m0 m1 m2 m3 c0 c1 o0 o1 md)
def addS (d a b : V) : Stmt := .atom (.add d a b)
def mulS (d a b : V) : Stmt := .atom (.mul d a b)

/-- The range check `log x < k` with its bound at `b`, from `b + 1` (`x` hinted before). -/
def rangeS (x : V) (k b : Nat) : List Stmt :=
  [cst b (word (2 ^ (k - 1)) 0 0), .atom (.rangeCheck x (.n (b + 1)) (.n (b + 2)) (.n (b + 3)) (.n b))]

/-! ## WOTS+C chains -/

/-- What a chain step reads beside its value: the public parameter and the step metadata; the
step addresses (leanXMSS) or the index the address is computed from (leanSPHINCS). -/
structure Wots where
  pp : V
  md : V
  lx : Bool
  adr : Nat → V
  idx : V

/-- The fresh values of a step before its outputs. -/
def stepSize (lx : Bool) : Nat := if lx then 3 else 5

/-- The step of chain `i` leaving position `s`, from base `b` (`chain_step`, G:2307). -/
def cStep (w : Wots) (i s b : Nat) (v o0 o1 : V) : List Stmt :=
  if w.lx then
    [cst b (word i 0 0), cst (b + 1) iv0, cst (b + 2) iv1,
      b2s w.pp (w.adr s) v (.n b) (.n (b + 1)) (.n (b + 2)) o0 o1 w.md]
  else
    [cst b (word (tw 1 + i * hiMul + s * stepMul) 0 0), addS (.n (b + 1)) w.idx (.n b),
      cst (b + 2) (word 0 0 0), cst (b + 3) iv0, cst (b + 4) iv1,
      b2s w.pp (.n (b + 1)) v (.n (b + 2)) (.n (b + 3)) (.n (b + 4)) o0 o1 w.md]

/-- `m + 1` steps of chain `i` from position `s`, the last into `t0, t1`. -/
def cSteps (w : Wots) (i : Nat) (t0 t1 : V) : Nat → Nat → Nat → V → List Stmt
  | 0, s, b, v => cStep w i s b v t0 t1
  | m + 1, s, b, v =>
      cStep w i s b v (.n (b + stepSize w.lx)) (.n (b + stepSize w.lx + 1)) ++
        cSteps w i t0 t1 m (s + 1) (b + stepSize w.lx + 2) (.n (b + stepSize w.lx))

/-- Chain `i` walked from digit `d` into `t0, t1` (`walk`, G:2318). -/
def cWalk (w : Wots) (i d b : Nat) (t0 t1 : V) : List Stmt :=
  if d = 3 then [hintW "chain_starts" [t0]]
  else hintW "chain_starts" [.n b] :: cSteps w i t0 t1 (2 - d) d (b + 1) (.n b)

/-- The fresh values of a walk, its outputs not counted. -/
def walkSize (lx : Bool) (d : Nat) : Nat :=
  if d = 3 then 0 else 1 + (stepSize lx + 2) * (2 - d) + stepSize lx

/-- The walks of chains `first + r`, `r ..< r + m`, at the base-4 digits of `k`, from `b`; with
`fresh`, each walk's tips are the two values after it. -/
def cWalks (w : Wots) (tips : Nat → V × V) (first k : Nat) (fresh : Bool) :
    Nat → Nat → Nat → List Stmt × Nat
  | 0, _, b => ([], b)
  | m + 1, r, b =>
      let d := k / 4 ^ r % 4
      let rest := cWalks w tips first k fresh m (r + 1) (b + walkSize w.lx d + (if fresh then 2 else 0))
      (cWalk w (first + r) d b (tips r).1 (tips r).2 ++ rest.1, rest.2)

/-- The digit sum of `k`'s `n` low base-4 digits. -/
def digitSum (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => k / 4 ^ n % 4 + digitSum k n

/-- A 128-bit literal (`lit_field`). -/
def lit (c : Nat) : E := word (c % 2 ^ 64) (c / 2 ^ 64 % 2 ^ 64) 0

/-- Arm `k` of a group's dispatch from base `b`: the walks, then the product and the encoding
folded in. `fold` for the first group, whose running values are the constants `1` and `0`;
`fresh` for the first arm, which allocates the shared outputs. -/
def cArm (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
    (first n k : Nat) (fold fresh : Bool) (b : Nat) : List Stmt × Nat :=
  let ws := cWalks w tips first k fresh n 0 (if fold then b + 1 else b)
  let b1 := ws.2 + (if fresh then 2 else 0)
  let enc0 := if fold then V.n b else encIn
  let pre := if fold then [cst b (word 0 0 0)] else []
  let prod := if fold then Stmt.atom (.copy prodOut (power (digitSum k n)))
    else mulS prodOut prodIn (power (digitSum k n))
  if k = 0 then (pre ++ ws.1 ++ [prod, .atom (.copy encOut enc0)], b1)
  else (pre ++ ws.1 ++ [prod, cst b1 (lit (k * 4 ^ first)), addS encOut enc0 (.n b1)], b1 + 1)

/-- Arms `k ..< k + m`. -/
def cArms (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
    (first n : Nat) (fold : Bool) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, k, b =>
      let a := cArm w tips power prodIn encIn prodOut encOut first n k fold (k == 0) b
      let rest := cArms w tips power prodIn encIn prodOut encOut first n fold m (k + 1) a.2
      (a.1 :: rest.1, rest.2)

/-- Where the first arm of a group from base `b` puts the shared outputs: its chains' tips, then
the product and the encoding. -/
def groupStart (fold : Bool) (b : Nat) : Nat := b + 5 + (if fold then 1 else 0)
def chainStride (lx : Bool) : Nat := walkSize lx 0 + 2
def groupTips (lx fold : Bool) (b : Nat) : Nat → V × V := fun r =>
  (.n (groupStart fold b + chainStride lx * r + walkSize lx 0),
    .n (groupStart fold b + chainStride lx * r + walkSize lx 0 + 1))
def groupProd (lx fold : Bool) (n b : Nat) : V := .n (groupStart fold b + chainStride lx * n)
def groupEnc (lx fold : Bool) (n b : Nat) : V := .n (groupStart fold b + chainStride lx * n + 1)

/-- A digit group from base `b`: the digit hint, its range check and the dispatch over the
`4^n` digit values (G:2421-2429). -/
def cGroup (w : Wots) (power : Nat → V) (prodIn encIn : V) (first n : Nat) (fold : Bool)
    (b : Nat) : List Stmt × Nat :=
  let arms := cArms w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5)
  (hintW "digits" [.n b] :: rangeS (.n b) (4 ^ n) (b + 1) ++ [.match_ (.n b) arms.1], arms.2)

/-- Groups `p ..< p + m` of three digits, from base `b`, after the running product and encoding:
the statements, the next base, the tips of their chains, the final product and encoding. -/
def cGroups (w : Wots) (power : Nat → V) :
    Nat → Nat → V → V → Nat → List Stmt × Nat × List (V × V) × V × V
  | 0, _, prod, enc, b => ([], b, [], prod, enc)
  | m + 1, p, prod, enc, b =>
      let fold := p == 0
      let g := cGroup w power prod enc (3 * p) 3 fold b
      let rest := cGroups w power m (p + 1) (groupProd w.lx fold 3 b) (groupEnc w.lx fold 3 b) g.2
      (g.1 ++ rest.1, rest.2.1, (List.range 3).map (groupTips w.lx fold b) ++ rest.2.2.1,
        rest.2.2.2)

/-- The whole codeword of `v = 3·G + 1` chains from base `b`: `G` groups and the last chain's,
then the two assertions against the target sum `g^T` and the digest cell `d0`. The statements,
the next base and the chains' tips. -/
def cCodeword (w : Wots) (power : Nat → V) (G : Nat) (target : E) (d0 : V) (b : Nat) :
    List Stmt × Nat × List (V × V) :=
  let gs := cGroups w power G 0 (.n 0) (.n 0) b
  let last := cGroup w power gs.2.2.2.1 gs.2.2.2.2 (3 * G) 1 false gs.2.1
  let c := last.2
  (gs.1 ++ last.1 ++ [cst c target, .atom (.assertEq (groupProd w.lx false 1 gs.2.1) (.n c)),
    .atom (.assertEq (groupEnc w.lx false 1 gs.2.1) d0)], c + 1,
    gs.2.2.1 ++ [groupTips w.lx false gs.2.1 0])

/-! ## Hashing values, Merkle paths, bits -/

/-- `Th(P, A, values)` over `n` values from base `b` (`hash_values`, G:2345): the statements and
the output. -/
def hashValues (pp a : V) (val : Nat → V) (n b : Nat) : List Stmt × V :=
  let q := (n + 1) / 4 - 1
  let first := ivs b ++ [cst (b + 2) (mdw 64 false),
    b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]
  let mid := (List.range q).flatMap fun j => let c := b + 5 + 3 * j;
    [cst c (mdw (64 * (j + 2)) false),
      b2s (val (4 * j + 2)) (val (4 * j + 3)) (val (4 * j + 4)) (val (4 * j + 5))
        (.n (c - 2)) (.n (c - 1)) (.n (c + 1)) (.n (c + 2)) (.n c)]
  let c := b + 5 + 3 * q
  if n % 4 = 0 then
    (first ++ mid ++ [cst c (word 0 0 0), cst (c + 1) (word 0 0 0), cst (c + 2) (mdw (16 * (n + 2)) true),
      b2s (val (n - 2)) (val (n - 1)) (.n c) (.n (c + 1)) (.n (c - 2)) (.n (c - 1)) (.n (c + 3))
        (.n (c + 4)) (.n (c + 2))], .n (c + 3))
  else
    (first ++ mid ++ [cst c (mdw (16 * (n + 2)) true),
      b2s (val (n - 4)) (val (n - 3)) (val (n - 2)) (val (n - 1)) (.n (c - 2)) (.n (c - 1))
        (.n (c + 1)) (.n (c + 2)) (.n c)], .n (c + 1))

/-- The fresh values of `hashValues`. -/
def hashValuesSize (n : Nat) : Nat := 5 + 3 * ((n + 1) / 4 - 1) + (if n % 4 = 0 then 5 else 3)

/-- `merkle_path` from `cur`, levels `l ..< l + m`, from base `b` (G:2363): the level's bit,
the node index added to its address unless `isEnd`, the address constant. -/
def merkle (pp : V) (bit node : Nat → V) (addr : Nat → Nat) (isEnd : Nat → Bool) :
    Nat → Nat → V → Nat → List Stmt × V × Nat
  | 0, _, cur, b => ([], cur, b)
  | m + 1, l, cur, b =>
      let a := if isEnd l then b + 4 else b + 5
      let rest := merkle pp bit node addr isEnd m (l + 1) (.n (a + 4)) (a + 6)
      ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bit l) (.n (b + 3)),
        cst (b + 4) (word (addr l) 0 0)] ++
        (if isEnd l then [] else [addS (.n (b + 5)) (.n (b + 4)) (node (l + 1))]) ++
        ivs (a + 1) ++ [cst (a + 3) (mdw 64 true),
          b2s pp (.n a) (.n b) (.n (b + 1)) (.n (a + 1)) (.n (a + 2)) (.n (a + 4)) (.n (a + 5))
            (.n (a + 3))] ++ rest.1, rest.2)

/-- `shifts` (G:2289): out `l` at `outBase + 3·(n - 1 - l)`, over the bits at `bitBase`. -/
def shifts (bitBase n outBase : Nat) : List Stmt :=
  .atom (.copy (.n outBase) (.n (bitBase + n - 1))) ::
  (List.range (n - 1)).flatMap fun r' => let r := r' + 1;
    [cst (outBase + 3 * r - 2) (word 2 0 0),
      mulS (.n (outBase + 3 * r - 1)) (.n (outBase + 3 * r - 2)) (.n (outBase + 3 * r - 3)),
      addS (.n (outBase + 3 * r)) (.n (bitBase + n - 1 - r)) (.n (outBase + 3 * r - 1))]

/-- Bits pinned Boolean: `x = x · x` for each. -/
def booleans (base n : Nat) : List Stmt := (List.range n).map fun j => mulS (.n (base + j)) (.n (base + j)) (.n (base + j))

/-- The powers `g^s`, `s < 10`, from base `b`. -/
def powers (b : Nat) : List Stmt := (List.range 10).map fun s => cst (b + s) (word (2 ^ s) 0 0)

/-! ## leanXMSS -/

/-- The prologue: `pp`, the step metadata, the leaf index's bits pinned Boolean, the node
indices `n(128 - 3l)` (`shifts`), the powers `n(129 + s)`. -/
def xPrologue : List Stmt :=
  [.atom (.load (.n 1) (.n 0) 1), cst 2 (mdw 64 true),
    hintW "leaf_index_bits" ((List.range 32).map fun j => .n (3 + j))] ++
  booleans 3 32 ++ shifts 3 32 35 ++ powers 129

/-- The bottom layer's message digest from base `b`: `D = Th(P, A_msg, M | R)`, two blocks. -/
def xDigest0 (b : Nat) : List Stmt :=
  [hintW "randomizer" [.n b], cst (b + 1) (word (tw 12) 0 0), addS (.n (b + 2)) (.n 128) (.n (b + 1)),
    .atom (.load (.n (b + 3)) (.n 0) 2), .atom (.load (.n (b + 4)) (.n 0) 3)] ++ ivs (b + 5) ++
  [cst (b + 7) (mdw 64 false),
    b2s (.n 1) (.n (b + 2)) (.n (b + 3)) (.n (b + 4)) (.n (b + 5)) (.n (b + 6)) (.n (b + 8))
      (.n (b + 9)) (.n (b + 7)),
    cst (b + 10) (word 0 0 0), cst (b + 11) (word 0 0 0), cst (b + 12) (word 0 0 0),
    cst (b + 13) (mdw 80 true),
    b2s (.n b) (.n (b + 10)) (.n (b + 11)) (.n (b + 12)) (.n (b + 8)) (.n (b + 9)) (.n (b + 14))
      (.n (b + 15)) (.n (b + 13))]

/-- The top layer's index and message digest from base `b`, over the bottom root `root`. -/
def xDigest1 (b : Nat) (root : V) : List Stmt :=
  [cst b (word lxTop 0 0), addS (.n (b + 1)) (.n 80) (.n b), hintW "randomizer" [.n (b + 2)],
    cst (b + 3) (word (tw 12) 0 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))] ++ ivs (b + 5) ++
  [cst (b + 7) (mdw 64 true),
    b2s (.n 1) (.n (b + 4)) root (.n (b + 2)) (.n (b + 5)) (.n (b + 6)) (.n (b + 8)) (.n (b + 9))
      (.n (b + 7))]

/-- The three step addresses from base `b`, at `n(b + 2s + 1)`. -/
def xStepAddrs (idx : V) (b : Nat) : List Stmt :=
  (List.range 3).flatMap fun s =>
    [cst (b + 2 * s) (word (tw 1 + s * stepMul) 0 0), addS (.n (b + 2 * s + 1)) idx (.n (b + 2 * s))]

/-- `g^106`. -/
def xTarget : E := word 118747255799808 0 0

/-- Layer `layer` from base `b`, over the bottom root `root` at the top: its statements, the
next base and its root. -/
def xLayer (layer b : Nat) (root : V) : List Stmt × Nat × V :=
  let idx := if layer = 0 then V.n 128 else V.n (b + 1)
  let a := if layer = 0 then b + 16 else b + 10
  let w : Wots := ⟨.n 1, .n 2, true, fun s => .n (a + 2 * s + 1), idx⟩
  let cw := cCodeword w (fun s => .n (129 + s)) 19 xTarget
    (if layer = 0 then V.n (b + 14) else V.n (b + 8)) (a + 6)
  let c := cw.2.1
  let leaf := hashValues (.n 1) (.n (c + 1)) (fun i => (cw.2.2.getD i (.n 0, .n 0)).1) 58 (c + 2)
  let mk := merkle (.n 1) (fun l => .n (3 + 16 * layer + l))
    (fun l => .n (128 - 3 * (16 * layer + l)))
    (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32)
    16 0 leaf.2 (c + 2 + hashValuesSize 58)
  ((if layer = 0 then xDigest0 b else xDigest1 b root) ++ xStepAddrs idx a ++ cw.1 ++
    [cst c (word (tw 2) 0 0), addS (.n (c + 1)) idx (.n c)] ++ leaf.1 ++ mk.1, mk.2.2, mk.2.1)

/-- The body of `verify_lean_xmss`. -/
def xBody : List Stmt :=
  let l0 := xLayer 0 139 (.n 0)
  let l1 := xLayer 1 l0.2.1 l0.2.2
  xPrologue ++ l0.1 ++ l1.1 ++
    [.atom (.load (.n l1.2.1) (.n 0) 0), .atom (.assertEq l1.2.2 (.n l1.2.1)), .ret []]

/-! ## leanSPHINCS -/

/-- The 256 forest-key specializations, `sp_forest_key__L{t}`. -/
def fkNames : List String := [
  "sp_forest_key__L0", "sp_forest_key__L1", "sp_forest_key__L2", "sp_forest_key__L3",
  "sp_forest_key__L4", "sp_forest_key__L5", "sp_forest_key__L6", "sp_forest_key__L7",
  "sp_forest_key__L8", "sp_forest_key__L9", "sp_forest_key__L10", "sp_forest_key__L11",
  "sp_forest_key__L12", "sp_forest_key__L13", "sp_forest_key__L14", "sp_forest_key__L15",
  "sp_forest_key__L16", "sp_forest_key__L17", "sp_forest_key__L18", "sp_forest_key__L19",
  "sp_forest_key__L20", "sp_forest_key__L21", "sp_forest_key__L22", "sp_forest_key__L23",
  "sp_forest_key__L24", "sp_forest_key__L25", "sp_forest_key__L26", "sp_forest_key__L27",
  "sp_forest_key__L28", "sp_forest_key__L29", "sp_forest_key__L30", "sp_forest_key__L31",
  "sp_forest_key__L32", "sp_forest_key__L33", "sp_forest_key__L34", "sp_forest_key__L35",
  "sp_forest_key__L36", "sp_forest_key__L37", "sp_forest_key__L38", "sp_forest_key__L39",
  "sp_forest_key__L40", "sp_forest_key__L41", "sp_forest_key__L42", "sp_forest_key__L43",
  "sp_forest_key__L44", "sp_forest_key__L45", "sp_forest_key__L46", "sp_forest_key__L47",
  "sp_forest_key__L48", "sp_forest_key__L49", "sp_forest_key__L50", "sp_forest_key__L51",
  "sp_forest_key__L52", "sp_forest_key__L53", "sp_forest_key__L54", "sp_forest_key__L55",
  "sp_forest_key__L56", "sp_forest_key__L57", "sp_forest_key__L58", "sp_forest_key__L59",
  "sp_forest_key__L60", "sp_forest_key__L61", "sp_forest_key__L62", "sp_forest_key__L63",
  "sp_forest_key__L64", "sp_forest_key__L65", "sp_forest_key__L66", "sp_forest_key__L67",
  "sp_forest_key__L68", "sp_forest_key__L69", "sp_forest_key__L70", "sp_forest_key__L71",
  "sp_forest_key__L72", "sp_forest_key__L73", "sp_forest_key__L74", "sp_forest_key__L75",
  "sp_forest_key__L76", "sp_forest_key__L77", "sp_forest_key__L78", "sp_forest_key__L79",
  "sp_forest_key__L80", "sp_forest_key__L81", "sp_forest_key__L82", "sp_forest_key__L83",
  "sp_forest_key__L84", "sp_forest_key__L85", "sp_forest_key__L86", "sp_forest_key__L87",
  "sp_forest_key__L88", "sp_forest_key__L89", "sp_forest_key__L90", "sp_forest_key__L91",
  "sp_forest_key__L92", "sp_forest_key__L93", "sp_forest_key__L94", "sp_forest_key__L95",
  "sp_forest_key__L96", "sp_forest_key__L97", "sp_forest_key__L98", "sp_forest_key__L99",
  "sp_forest_key__L100", "sp_forest_key__L101", "sp_forest_key__L102", "sp_forest_key__L103",
  "sp_forest_key__L104", "sp_forest_key__L105", "sp_forest_key__L106", "sp_forest_key__L107",
  "sp_forest_key__L108", "sp_forest_key__L109", "sp_forest_key__L110", "sp_forest_key__L111",
  "sp_forest_key__L112", "sp_forest_key__L113", "sp_forest_key__L114", "sp_forest_key__L115",
  "sp_forest_key__L116", "sp_forest_key__L117", "sp_forest_key__L118", "sp_forest_key__L119",
  "sp_forest_key__L120", "sp_forest_key__L121", "sp_forest_key__L122", "sp_forest_key__L123",
  "sp_forest_key__L124", "sp_forest_key__L125", "sp_forest_key__L126", "sp_forest_key__L127",
  "sp_forest_key__L128", "sp_forest_key__L129", "sp_forest_key__L130", "sp_forest_key__L131",
  "sp_forest_key__L132", "sp_forest_key__L133", "sp_forest_key__L134", "sp_forest_key__L135",
  "sp_forest_key__L136", "sp_forest_key__L137", "sp_forest_key__L138", "sp_forest_key__L139",
  "sp_forest_key__L140", "sp_forest_key__L141", "sp_forest_key__L142", "sp_forest_key__L143",
  "sp_forest_key__L144", "sp_forest_key__L145", "sp_forest_key__L146", "sp_forest_key__L147",
  "sp_forest_key__L148", "sp_forest_key__L149", "sp_forest_key__L150", "sp_forest_key__L151",
  "sp_forest_key__L152", "sp_forest_key__L153", "sp_forest_key__L154", "sp_forest_key__L155",
  "sp_forest_key__L156", "sp_forest_key__L157", "sp_forest_key__L158", "sp_forest_key__L159",
  "sp_forest_key__L160", "sp_forest_key__L161", "sp_forest_key__L162", "sp_forest_key__L163",
  "sp_forest_key__L164", "sp_forest_key__L165", "sp_forest_key__L166", "sp_forest_key__L167",
  "sp_forest_key__L168", "sp_forest_key__L169", "sp_forest_key__L170", "sp_forest_key__L171",
  "sp_forest_key__L172", "sp_forest_key__L173", "sp_forest_key__L174", "sp_forest_key__L175",
  "sp_forest_key__L176", "sp_forest_key__L177", "sp_forest_key__L178", "sp_forest_key__L179",
  "sp_forest_key__L180", "sp_forest_key__L181", "sp_forest_key__L182", "sp_forest_key__L183",
  "sp_forest_key__L184", "sp_forest_key__L185", "sp_forest_key__L186", "sp_forest_key__L187",
  "sp_forest_key__L188", "sp_forest_key__L189", "sp_forest_key__L190", "sp_forest_key__L191",
  "sp_forest_key__L192", "sp_forest_key__L193", "sp_forest_key__L194", "sp_forest_key__L195",
  "sp_forest_key__L196", "sp_forest_key__L197", "sp_forest_key__L198", "sp_forest_key__L199",
  "sp_forest_key__L200", "sp_forest_key__L201", "sp_forest_key__L202", "sp_forest_key__L203",
  "sp_forest_key__L204", "sp_forest_key__L205", "sp_forest_key__L206", "sp_forest_key__L207",
  "sp_forest_key__L208", "sp_forest_key__L209", "sp_forest_key__L210", "sp_forest_key__L211",
  "sp_forest_key__L212", "sp_forest_key__L213", "sp_forest_key__L214", "sp_forest_key__L215",
  "sp_forest_key__L216", "sp_forest_key__L217", "sp_forest_key__L218", "sp_forest_key__L219",
  "sp_forest_key__L220", "sp_forest_key__L221", "sp_forest_key__L222", "sp_forest_key__L223",
  "sp_forest_key__L224", "sp_forest_key__L225", "sp_forest_key__L226", "sp_forest_key__L227",
  "sp_forest_key__L228", "sp_forest_key__L229", "sp_forest_key__L230", "sp_forest_key__L231",
  "sp_forest_key__L232", "sp_forest_key__L233", "sp_forest_key__L234", "sp_forest_key__L235",
  "sp_forest_key__L236", "sp_forest_key__L237", "sp_forest_key__L238", "sp_forest_key__L239",
  "sp_forest_key__L240", "sp_forest_key__L241", "sp_forest_key__L242", "sp_forest_key__L243",
  "sp_forest_key__L244", "sp_forest_key__L245", "sp_forest_key__L246", "sp_forest_key__L247",
  "sp_forest_key__L248", "sp_forest_key__L249", "sp_forest_key__L250", "sp_forest_key__L251",
  "sp_forest_key__L252", "sp_forest_key__L253", "sp_forest_key__L254", "sp_forest_key__L255"]

/-- The deficits of the forest codewords, six per table entry (`SP_CODEWORDS`): `lut`'s. -/
def spCode (t i : Nat) : Nat :=
  let codes : List Nat := [9, 21, 29, 45, 101, 105, 129, 145, 225, 501, 505, 525, 629, 645, 725, 1125,
   2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501, 12505, 12525, 12625, 13125, 13, 17,
   53, 65, 77, 85, 253, 265, 325, 377, 385, 425, 1253, 1265, 1325, 1625, 1877, 1885,
   1925, 2125, 6253, 6265, 6325, 6625, 8125, 9377, 9385, 9425, 9625, 10625, 33, 41, 81, 133,
   141, 153, 165, 201, 205, 381, 401, 405, 633, 641, 653, 665, 701, 705, 753, 765,
   825, 1001, 1005, 1025, 1881, 1901, 1905, 2001, 2005, 2025, 3133, 3141, 3153, 3165, 3201, 3205,
   3253, 3265, 3325, 3501, 3505, 3525, 3753, 3765, 3825, 4125, 5001, 5005, 5025, 5125, 9381, 9401,
   9405, 9501, 9505, 9525, 10001, 10005, 10025, 10125, 37, 57, 61, 137, 177, 185, 257, 261,
   277, 285, 301, 305, 637, 677, 685, 877, 885, 925, 1257, 1261, 1277, 1285, 1301, 1305,
   1377, 1385, 1425, 1501, 1505, 1525, 3137, 3177, 3185, 3377, 3385, 3425, 4377, 4385, 4425, 4625,
   6257, 6261, 6277, 6285, 6301, 6305, 6377, 6385, 6425, 6501, 6505, 6525, 6877, 6885, 6925, 7125,
   7501, 7505, 7525, 7625, 157, 161, 181, 281, 657, 661, 681, 757, 761, 777, 785, 801,
   805, 881, 901, 905, 1281, 1381, 1401, 1405, 3157, 3161, 3181, 3257, 3261, 3277, 3285, 3301,
   3305, 3381, 3401, 3405, 3757, 3761, 9, 21, 29, 45, 101, 105, 129, 145, 225, 501,
   505, 525, 629, 645, 725, 1125, 2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501,
   12505, 12525, 12625, 13125, 13, 17, 53, 65, 77, 85, 253, 265, 325, 377, 385, 425]
  codes.getD t 0 / 5 ^ (5 - i) % 5

/-- One forest chain `i` walked its deficit `d` up to the top from base `b`, its tip at
`n(b + fkChainSize d - 2)` (`sp_forest_key`, G:2464-2475). -/
def fkChain (i d b : Nat) : List Stmt :=
  hintW "sp_forest_values" [.n b] :: (List.range d).flatMap fun j =>
    let c := b + 1 + 8 * j
    [cst c (word (tw 15 + i * 2 ^ 43 + (4 - d + j) * stepMul) 0 0), addS (.n (c + 1)) (.n 0) (.n c),
      cst (c + 2) (word 0 0 0)] ++ ivs (c + 3) ++ [cst (c + 5) (mdw 48 true),
      b2s (.n 1) (.n (c + 1)) (if j = 0 then .n b else .n (c - 2)) (.n (c + 2)) (.n (c + 3))
        (.n (c + 4)) (.n (c + 6)) (.n (c + 7)) (.n (c + 5))]

def fkChainSize (d : Nat) : Nat := 1 + 8 * d

/-- The tip of a forest chain from base `b`. -/
def fkTip (d b : Nat) : Nat := if d = 0 then b else b + fkChainSize d - 2

/-- The chains `i ..< i + m` of forest key `t` from base `b`: the statements, the next base and
the tips. -/
def fkChains (t : Nat) : Nat → Nat → Nat → List Stmt × Nat × List Nat
  | 0, _, b => ([], b, [])
  | m + 1, i, b =>
      let rest := fkChains t m (i + 1) (b + fkChainSize (spCode t i))
      (fkChain i (spCode t i) b ++ rest.1, rest.2.1, fkTip (spCode t i) b :: rest.2.2)

/-- The body of `sp_forest_key__L{t}`: `at` is `n0`, `pp` is `n1`. -/
def fkBody (t : Nat) : List Stmt :=
  let ch := fkChains t 6 0 2
  let B := ch.2.1
  let tip : Nat → V := fun i => .n (ch.2.2.getD i 0)
  ch.1 ++ [cst B (word (tw 16) 0 0), addS (.n (B + 1)) (.n 0) (.n B)] ++ ivs (B + 2) ++
    [cst (B + 4) (mdw 64 false),
      b2s (.n 1) (.n (B + 1)) (tip 0) (tip 1) (.n (B + 2)) (.n (B + 3)) (.n (B + 5)) (.n (B + 6))
        (.n (B + 4)),
      cst (B + 7) (mdw 128 true),
      b2s (tip 2) (tip 3) (tip 4) (tip 5) (.n (B + 5)) (.n (B + 6)) (.n (B + 8)) (.n (B + 9))
        (.n (B + 7)),
      .atom (.copy (.n (B + 10)) (.n (B + 8))), cst (B + 11) (word t 0 0),
      .ret [.n (B + 10), .n (B + 11)]]

/-- The function of forest key `t`. -/
def fkFn (t : Nat) : Fn := ⟨fkNames.getD t "", [.n 0, .n 1], fkBody t⟩

/-- One level of `sp_fold` (G:2481) from base `b`: the hinted sibling, the node's address, the
pair in the order of the index's bit, into `o0, o1`. -/
def spLevel (pp md adr : V) (addr : Nat) (bit : Bool) (cur : V) (b : Nat) (o0 o1 : V) : List Stmt :=
  [hintW "sp_forest_nodes" [.n b], cst (b + 1) (word addr 0 0), addS (.n (b + 2)) adr (.n (b + 1))] ++
    ivs (b + 3) ++
    [if bit then b2s pp (.n (b + 2)) (.n b) cur (.n (b + 3)) (.n (b + 4)) o0 o1 md
      else b2s pp (.n (b + 2)) cur (.n b) (.n (b + 3)) (.n (b + 4)) o0 o1 md]

/-- What a fold's tree is: its height, its address type and its address multipliers. -/
structure Fold where
  height : Nat
  tag : Nat
  levelMul : Nat
  nodeMul : Nat

/-- The address of level `l`'s node above leaf `index`. -/
def Fold.addr (F : Fold) (index l : Nat) : Nat :=
  tw F.tag + (l + 1) * F.levelMul + index / 2 ^ (l + 1) * F.nodeMul

/-- Levels `l ..< l + m` of a fold, inline, from base `b`: the statements and the node reached. -/
def spLevels (pp md adr : V) (F : Fold) (index : Nat) : Nat → Nat → V → Nat → List Stmt × V
  | 0, _, cur, _ => ([], cur)
  | m + 1, l, cur, b =>
      let rest := spLevels pp md adr F index m (l + 1) (.n (b + 5)) (b + 7)
      (spLevel pp md adr (F.addr index l) (index.testBit l) cur b (.n (b + 5)) (.n (b + 6)) ++ rest.1,
        rest.2)

/-- One arm of a fold's dispatch, leaf `index`, from base `b` (`sp_subtree_arm`, `sp_tree_arm`,
G:2503-2516): the levels below the top, the top level into the outputs `out (2h)`, `out (2h+1)`,
the other top node hinted into `out (2 - 2h)`, then the arm's two constants, `r1` into `ret1` and
`r2` into `ret2`. -/
def spArm (pp md adr node : V) (F : Fold) (out : Nat → V) (ret1 ret2 : V) (r1 r2 : E)
    (index b : Nat) : List Stmt :=
  let lv := spLevels pp md adr F index (F.height - 2) 0 node b
  let c := b + 7 * (F.height - 2)
  let h := index / 2 ^ (F.height - 1)
  lv.1 ++ spLevel pp md adr (F.addr index (F.height - 2)) (index.testBit (F.height - 2)) lv.2 c
      (out (2 * h)) (out (2 * h + 1)) ++
    [hintW "sp_forest_nodes" [out (2 - 2 * h)], .atom (.const ret1 r1), .atom (.const ret2 r2)]

/-- The fresh values of arm `index`: the first allocates three outputs and `ret2`, the first of
the upper half the fourth output. -/
def spArmSize (F : Fold) (index : Nat) : Nat :=
  7 * (F.height - 2) + 5 + (if index = 0 then 4 else if index = 2 ^ (F.height - 1) then 1 else 0)

/-- Arms `a ..< a + m` from base `b`. -/
def spArms (pp md adr node : V) (F : Fold) (out : Nat → V) (ret1 ret2 : V) (r1 r2 : Nat → E) :
    Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, a, b =>
      let rest := spArms pp md adr node F out ret1 ret2 r1 r2 m (a + 1) (b + spArmSize F a)
      (spArm pp md adr node F out ret1 ret2 (r1 a) (r2 a) a b :: rest.1, rest.2)

/-- A fold's dispatch from base `b`: where its arms put the outputs and `ret2`. -/
def spOut (F : Fold) (b : Nat) : Nat → V := fun k =>
  if k < 3 then .n (b + 7 * (F.height - 2) + 5 + k)
  else .n (b + 7 * (F.height - 2) + 9 + (2 ^ (F.height - 1) - 1) * (7 * (F.height - 2) + 5) +
    7 * (F.height - 2) + 5)
def spRet2 (F : Fold) (b : Nat) : V := .n (b + 7 * (F.height - 2) + 8)

def subFoldT : Fold := ⟨3, 17, 256 * hiMul, 1024 * hiMul⟩
def topFoldT : Fold := ⟨4, 19, 8 * hiMul, 64 * hiMul⟩

/-- `g^255`, the bound of a codeword index. -/
def g255 : E := word 9223372036854810629 0 0

/-- Sub-tree `j` of coordinate `c` from base `b`, at `subAt`: the key and codeword hints, the
forest key's dispatch, the fold's dispatch, the bound's update. The statements, the next base,
the codeword's cell, the fold's outputs and the new bound. -/
def sSub (c j : Nat) (subAt : V) (bound : V) (b : Nat) : List Stmt × Nat × V × (Nat → V) × V :=
  let arms := spArms (.n 1) (.n 3) subAt (.n (b + 12)) subFoldT (spOut subFoldT (b + 14)) (.n (b + 1))
    (spRet2 subFoldT (b + 14)) (fun a => word (a * 2 ^ 40) 0 0)
    (fun a => lit (a * 2 ^ (58 + 3 * (2 * c + j)))) 8 0 (b + 14)
  ([hintW "sp_keys" [.n b, .n (b + 1)]] ++ rangeS (.n b) 8 (b + 2) ++ [hintW "sp_words" [.n (b + 6)],
    cst (b + 7) g255, .atom (.rangeCheck (.n (b + 6)) (.n (b + 8)) (.n (b + 9)) (.n (b + 10)) (.n (b + 7))),
    addS (.n (b + 11)) subAt (.n (b + 1)),
    .dispatch (.n (b + 6)) fkNames [.n (b + 11), .n 1] [.n (b + 12), .n (b + 13)],
    .match_ (.n b) arms.1, addS (.n arms.2) bound (spRet2 subFoldT (b + 14))], arms.2 + 1,
    .n (b + 13), spOut subFoldT (b + 14), .n arms.2)

/-- Coordinate `c` of the forest from base `b`: the statements, the next base, the two codeword
cells, the two top nodes and the new bound. -/
def sCoord (c : Nat) (bound : V) (b : Nat) : List Stmt × Nat × (V × V) × (V × V) × V :=
  let pre : List Stmt := if c = 0 then [] else [cst b (word (c * hiMul) 0 0), addS (.n (b + 1)) (.n 142) (.n b)]
  let treeAt := if c = 0 then V.n 142 else V.n (b + 1)
  let b0 := if c = 0 then b else b + 2
  let leafAt := V.n (b0 + 6)
  let s0 := sSub c 0 leafAt bound (b0 + 7)
  let b1 := s0.2.1
  let s1 := sSub c 1 (.n (b1 + 1)) s0.2.2.2.2 (b1 + 2)
  let f := s1.2.1
  let sub0 := s0.2.2.2.1
  let sub1 := s1.2.2.2.1
  let arms := spArms (.n 1) (.n 3) treeAt (.n (f + 10)) topFoldT (spOut topFoldT (f + 12)) (.n (b0 + 1))
    (spRet2 topFoldT (f + 12)) (fun s => word (s * 2 ^ 35) 0 0) (fun s => lit (s * 2 ^ (26 + 4 * c)))
    16 0 (f + 12)
  (pre ++ [hintW "sp_leaves" [.n b0, .n (b0 + 1)]] ++ rangeS (.n b0) 16 (b0 + 2) ++
    [addS leafAt treeAt (.n (b0 + 1))] ++ s0.1 ++ [cst b1 (word (2 ^ 39) 0 0), addS (.n (b1 + 1)) leafAt (.n b1)] ++
    s1.1 ++ [cst f (word (tw 18) 0 0), addS (.n (f + 1)) leafAt (.n f)] ++ ivs (f + 2) ++
    [cst (f + 4) (mdw 64 false),
      b2s (.n 1) (.n (f + 1)) (sub0 0) (sub0 2) (.n (f + 2)) (.n (f + 3)) (.n (f + 5)) (.n (f + 6)) (.n (f + 4)),
      cst (f + 7) (word 0 0 0), cst (f + 8) (word 0 0 0), cst (f + 9) (mdw 96 true),
      b2s (sub1 0) (sub1 2) (.n (f + 7)) (.n (f + 8)) (.n (f + 5)) (.n (f + 6)) (.n (f + 10)) (.n (f + 11)) (.n (f + 9)),
      .match_ (.n b0) arms.1, addS (.n arms.2) s1.2.2.2.2 (spRet2 topFoldT (f + 12))], arms.2 + 1,
    (s0.2.2.1, s1.2.2.1), (spOut topFoldT (f + 12) 0, spOut topFoldT (f + 12) 2), .n arms.2)

/-- Coordinates `c ..< c + m` from base `b`. -/
def sCoords : Nat → Nat → V → Nat → List Stmt × Nat × List (V × V) × List (V × V) × V
  | 0, _, bound, b => ([], b, [], [], bound)
  | m + 1, c, bound, b =>
      let x := sCoord c bound b
      let rest := sCoords m (c + 1) x.2.2.2.2 x.2.1
      (x.1 ++ rest.1, rest.2.1, x.2.2.1 :: rest.2.2.1, x.2.2.2.1 :: rest.2.2.2.1, rest.2.2.2.2)

/-- The prologue: `pp`, the two metadata cells, the message digest, its index bits and unused
bits pinned Boolean, the node indices `n(142 - 3l)`, the unused bits' value, the bound's start. -/
def sPrologue : List Stmt :=
  [.atom (.load (.n 1) (.n 0) 1), cst 2 (mdw 48 true), cst 3 (mdw 64 true), cst 4 (word (tw 12) 0 0),
    .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3)] ++ ivs 7 ++
  [cst 9 (mdw 64 false), b2s (.n 1) (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 10) (.n 11) (.n 9),
    hintW "sp_rand" [.n 12], cst 13 (word 0 0 0), cst 14 (word 0 0 0), cst 15 (word 0 0 0),
    cst 16 (mdw 80 true), b2s (.n 12) (.n 13) (.n 14) (.n 15) (.n 10) (.n 11) (.n 17) (.n 18) (.n 16),
    .atom (.hint (.bits (.n 18) 0 26 (.stack ((List.range 26).map fun j => .n (19 + j)))))] ++
  booleans 19 26 ++
  [.atom (.hint (.bits (.n 18) 106 22 (.stack ((List.range 22).map fun j => .n (45 + j)))))] ++
  booleans 45 22 ++ shifts 19 26 67 ++ shifts 45 22 143 ++
  [cst 207 (word 0 (2 ^ 42) 0), mulS (.n 208) (.n 206) (.n 207), addS (.n 209) (.n 142) (.n 208)]

/-- The codeword lanes from base `b` over the sixteen codeword cells, then the digest's
assertions (G:2582-2589). -/
def sLanes (wd : Nat → V) (bound : V) (b : Nat) : List Stmt :=
  let lane0 : Nat → V := fun k => if k = 0 then wd 7 else .n (b + 6 * (k - 1) + 2)
  let lane1 : Nat → V := fun k => if k = 0 then wd 15 else .n (b + 6 * (k - 1) + 5)
  let c := b + 42
  ((List.range 7).flatMap fun k' => let k := k' + 1; let e := b + 6 * k';
    [cst e (word 256 0 0), mulS (.n (e + 1)) (lane0 k') (.n e), addS (.n (e + 2)) (wd (7 - k)) (.n (e + 1)),
      cst (e + 3) (word 256 0 0), mulS (.n (e + 4)) (lane1 k') (.n (e + 3)),
      addS (.n (e + 5)) (wd (15 - k)) (.n (e + 4))]) ++
  [cst c (word 0 1 0), mulS (.n (c + 1)) (lane1 7) (.n c), addS (.n (c + 2)) (lane0 7) (.n (c + 1)),
    .atom (.assertEq (.n (c + 2)) (.n 17)), .atom (.assertEq bound (.n 18))]

/-- The counter from base `b`: its hint, its 32 bits pinned Boolean and recombined, the
encoding hash over the forest key `fk` (G:2595-2605). -/
def sCounter (fk : V) (b : Nat) : List Stmt :=
  let e := b + 126
  [hintW "sp_counter" [.n b], .atom (.hint (.bits (.n b) 0 32 (.stack ((List.range 32).map fun j => .n (b + 1 + j)))))] ++
  [mulS (.n (b + 1)) (.n (b + 1)) (.n (b + 1))] ++
  (List.range 31).flatMap (fun i' => let i := i' + 1; let c := b + 33 + 3 * i';
    [mulS (.n (b + 1 + i)) (.n (b + 1 + i)) (.n (b + 1 + i)), cst c (word 2 0 0),
      mulS (.n (c + 1)) (.n c) (if i' = 0 then .n (b + 32) else .n (c - 1)),
      addS (.n (c + 2)) (.n (b + 32 - i)) (.n (c + 1))]) ++
  [.atom (.assertEq (.n (b + 125)) (.n b)), cst e (word (tw 4) 0 0), addS (.n (e + 1)) (.n 142) (.n e)] ++
  ivs (e + 2) ++ [cst (e + 4) (mdw 52 true),
    b2s (.n 1) (.n (e + 1)) fk (.n b) (.n (e + 2)) (.n (e + 3)) (.n (e + 5)) (.n (e + 6)) (.n (e + 4))]

/-- `g^120`. -/
def sTarget : E := word 1945555039024054272 0 0

/-- The body of `verify_sig_lean_sphincs`. -/
def sBody : List Stmt :=
  let cs := sCoords 8 0 (.n 209) 210
  let b := cs.2.1
  let wd : Nat → V := fun k => ((cs.2.2.1.getD (k / 2) (.n 0, .n 0)) |> fun p => if k % 2 = 0 then p.1 else p.2)
  let top : Nat → V := fun k => ((cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)) |> fun p => if k % 2 = 0 then p.1 else p.2)
  let f := b + 45
  let fkh := hashValues (.n 1) (.n (f + 1)) top 16 (f + 2)
  let ctr := f + 2 + hashValuesSize 16
  let e := ctr + 126
  let w : Wots := ⟨.n 1, .n 2, false, fun _ => .n 0, .n 142⟩
  let cw := cCodeword w (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  let c := cw.2.1
  let leaf := hashValues (.n 1) (.n (c + 1)) (fun i => (cw.2.2.getD i (.n 0, .n 0)).1) 64 (c + 2)
  let mk := merkle (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l))
    (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) 26 0 leaf.2 (c + 2 + hashValuesSize 64)
  sPrologue ++ cs.1 ++ sLanes wd cs.2.2.2.2 b ++ [cst f (word (tw 20) 0 0), addS (.n (f + 1)) (.n 142) (.n f)] ++
    fkh.1 ++ sCounter fkh.2 ctr ++ powers (e + 7) ++ cw.1 ++
    [cst c (word (tw 2) 0 0), addS (.n (c + 1)) (.n 142) (.n c)] ++ leaf.1 ++ mk.1 ++
    [.atom (.load (.n mk.2.2) (.n 0) 0), .atom (.assertEq mk.2.1 (.n mk.2.2)), .ret []]

end
end LeanVM.Guest.B1.Sig
