/-
  LeanVM.Guest.B1.Whir.StackedT

  The expansion of `open_stacked` and of its loop helpers, generated from a candidate's
  configuration: the level loop, the tail rounds, the rotated point, the induced bases, the
  residual chains and the out-of-domain weights.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesT

/-!
# The templates of `open_stacked` (TRIAGE #36)

`open_stacked(m, fs0, fs1, target, root0, root1, cursor)` (G:1047-1317) has 28 specializations,
one per candidate `m = (μ - 22) + 7·(r - 1)`, each reading its row of the `LIG_*` tables at
compile time. `OsCfg` is that row as the compiler folds it (`OsLvl` per level), with the names of
the specialized callees and loop helpers; `osBody cfg` is the body, generated as the compiler
numbers it, value by value: each block takes the first free value `k` and returns the next, with
the running Fiat-Shamir state, cursor, quadratic and claim in `OsSt`. The loop helpers are
`sqLoopBody` (one squeeze and its `decode_query_bits` per iteration, G:1147-1157) and
`resLoopBody` (one query's induced basis product, G:1283-1294).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Configurations -/

/-- One level's row of the `LIG_*` tables, and its specialized callees. -/
structure OsLvl where
  folds : ℕ
  foldsOff : ℕ
  queries : ℕ
  depth : ℕ
  posOff : ℕ
  capDepth : ℕ
  capOff : ℕ
  grindBits : ℕ
  squeezes : ℕ
  /-- `LIG_LOG_MSG_COLS`: the message log after the level's folds. -/
  logCols : ℕ
  /-- `LIG_OOD_SAMPLES` of the next level: the samples of the commitment this level reads. -/
  oodNext : ℕ
  /-- `LIG_OOD_SAMPLES` of this level. -/
  oodHere : ℕ
  prefixLen : ℕ
  resFoldOff : ℕ
  /-- `LIG_VANISH_INVS[vanish + t]`, `t < prefixLen + yrLog`. -/
  invs : List ℕ
  /-- `LIG_VANISH_VALS[vanish + t]`, `t < logCols - 1`. -/
  vals : List ℕ
  rowWeights : String
  verifyCap : String
  queriesFn : String
  decode : String
  sqLoop : String
  resLoop : String
  deriving Repr, Inhabited

/-- A candidate's configuration. -/
structure OsCfg where
  levels : List OsLvl
  yrLevel : ℕ
  yrLog : ℕ
  yrLen : ℕ
  nFolds : ℕ
  maxQ : ℕ
  capLen : ℕ
  posLen : ℕ
  maxSq : ℕ
  maxIl : ℕ
  finalMsg : String
  foldFinal : String
  deriving Repr, Inhabited

/-- The word of `g^e`, as the compiler folds it. -/
def osGw (e : ℕ) : E := kw (gpowK e)

/-! ## Blocks -/

/-- The running state between blocks: the next free value, the Fiat-Shamir state's cells, the
cursor (a base value and a word offset), the quadratic's coefficients and the running claim. -/
structure OsSt where
  k : ℕ
  f0 : ℕ
  f1 : ℕ
  cb : ℕ
  co : ℕ
  c : ℕ
  b : ℕ
  a : ℕ
  t : ℕ

/-- A pointer `base·g^off`, materialized when the offset is not zero: the statements, the
pointer's value and the next free value. -/
def osMat (base off k : ℕ) : List Stmt × ℕ × ℕ :=
  if off = 0 then ([], base, k)
  else ([.atom (.const (.n k) (osGw off)), .atom (.mul (.n (k + 1)) (.n base) (.n k))], k + 1, k + 2)

/-- A fresh `HeapBuf(g^e)` at `k`: its size, then its pointer at `k + 1`. -/
def osHeap (e k : ℕ) : List Stmt := [.atom (.const (.n k) (osGw e)), .atom (.hint (.allocDyn (.n (k + 1)) (.n k)))]

/-- `fs_next` (G:510) at the state: the word at `k`, the new state at `k + 13`, `k + 14`. -/
def osFsNext (s : OsSt) : List Stmt × OsSt :=
  (fsNextT (.n s.f0) (.n s.f1) (.n s.cb) s.co s.k, { s with k := s.k + 15, f0 := s.k + 13, f1 := s.k + 14, co := s.co + 1 })

/-- One sumcheck round (`opening_fold`, G:945), its challenge stored at `fch[fo]`. -/
def osFold (s : OsSt) (fch fo : ℕ) : List Stmt × OsSt :=
  let m := osMat s.cb s.co s.k
  let r := m.2.2
  (m.1 ++ [.call "opening_fold" [.n s.f0, .n s.f1, .n m.2.1, .n s.c, .n s.b, .n s.a]
      ((List.range 7).map fun j => .n (r + j)),
    .atom (.copy (.n (r + 7)) (.n r)), .atom (.copy (.n (r + 8)) (.n (r + 1))),
    .atom (.load (.n (r + 6)) (.n fch) fo), .atom (.add (.n (r + 9)) (.n (r + 3)) (.n (r + 5)))],
   { k := r + 10, f0 := r + 7, f1 := r + 8, cb := r + 2, co := 0, c := r + 4, b := r + 9, a := r + 5,
     t := r + 3 })

/-- `n` rounds, the challenges stored from `fch[fo]`. -/
def osFolds (fch : ℕ) : ℕ → ℕ → OsSt → List Stmt × OsSt
  | _, 0, s => ([], s)
  | fo, n + 1, s =>
    let r := osFold s fch fo
    let rest := osFolds fch (fo + 1) n r.2
    (r.1 ++ rest.1, rest.2)

/-- The final level's message (`opening_final_message`, G:969) into `final_msg`. -/
def osFinal (name : String) (fmsg : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let m := osMat s.cb s.co s.k
  let r := m.2.2
  (m.1 ++ [.call name [.n s.f0, .n s.f1, .n m.2.1, .n fmsg] [.n r, .n (r + 1), .n (r + 2)],
    .atom (.copy (.n (r + 3)) (.n r)), .atom (.copy (.n (r + 4)) (.n (r + 1)))],
   { s with k := r + 5, f0 := r + 3, f1 := r + 4, cb := r + 2, co := 0 })

/-- An out-of-domain sample (G:1125-1135): its point squeezed into `ood_z`, its value and its
intro message read and stored in `ood`. -/
def osOodSample (oz so logCols oodz ood : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let pre : List Stmt := [.atom (.const (.n k) (osGw oz)), .atom (.mul (.n (k + 1)) (.n oodz) (.n k)),
    .atom (.const (.n (k + 2)) (osGw logCols)),
    .call "opening_ood_point" [.n s.f0, .n s.f1, .n (k + 1), .n (k + 2)] [.n (k + 3), .n (k + 4)],
    .atom (.copy (.n (k + 5)) (.n (k + 3))), .atom (.copy (.n (k + 6)) (.n (k + 4)))]
  let s1 : OsSt := { s with k := k + 7, f0 := k + 5, f1 := k + 6 }
  let y := osFsNext s1
  let c0 := osFsNext y.2
  let c2 := osFsNext c0.2
  (pre ++ y.1 ++ c0.1 ++ c2.1 ++
    [.atom (.load (.n s1.k) (.n ood) (so + 1)), .atom (.load (.n y.2.k) (.n ood) (so + 2)),
      .atom (.load (.n c0.2.k) (.n ood) (so + 3))], c2.2)

/-- The out-of-domain samples `os ..` of the commitment level `lvl` reads. -/
def osOods (lvl logCols oodz ood : ℕ) : ℕ → ℕ → OsSt → List Stmt × OsSt
  | _, 0, st => ([], st)
  | os, n + 1, st =>
    let r := osOodSample (((lvl + 1) + os) * 22) ((lvl + 1) * 4 + os * 4) logCols oodz ood st
    let rest := osOods lvl logCols oodz ood (os + 1) n r.2
    (r.1 ++ rest.1, rest.2)

/-- The next commitment of a level that is not the last (G:1113-1135): its two root halves read,
checked canonical and stored, then its out-of-domain samples. -/
def osCommit (lvl logCols oodNext roots oodz ood : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let ra := osFsNext s
  let rb := osFsNext ra.2
  let k := rb.2.k
  let chk : List Stmt := [.call "assert_canonical" [.n s.k] [.n k],
    .call "assert_canonical" [.n ra.2.k] [.n (k + 1)],
    .atom (.load (.n s.k) (.n roots) (2 * lvl + 2)), .atom (.load (.n ra.2.k) (.n roots) (2 * lvl + 3))]
  let o := osOods lvl logCols oodz ood 0 oodNext { rb.2 with k := k + 2 }
  (ra.1 ++ rb.1 ++ chk ++ o.1, o.2)

/-- The query nonce (G:1136-1142): the raw word at the cursor, its proof of work, its absorb. -/
def osGrind (bits : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let chk : List Stmt :=
    if bits = 0 then [.atom (.const (.n (k + 1)) (word 0 0 0)), .atom (.assertEq (.n k) (.n (k + 1)))]
    else [.atom (.const (.n (k + 1)) (osGw bits)),
      .call "grind_check" [.n s.f0, .n s.f1, .n k, .n (k + 1)] []]
  ([.atom (.load (.n k) (.n s.cb) s.co)] ++ chk ++ fsCompressT (.n s.f0) (.n s.f1) (.n k) (k + 2) 4,
   { s with k := k + 16, f0 := k + 14, f1 := k + 15, co := s.co + 1 })

/-- The query positions (G:1144-1166): the squeeze run `sqz` from the state, the loop of
`squeezes` squeezes decoding the positions, its last state, and the batching challenge `lam` at
the returned `OsSt.k - 1`. -/
def osSqueezes (maxSq nsq qpos qbp : ℕ) (loop : String) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let pre : List Stmt := osHeap (2 * (maxSq + 1)) k ++
    [.atom (.load (.n s.f0) (.n (k + 1)) 0), .atom (.load (.n s.f1) (.n (k + 1)) 1),
      .atom (.const (.n (k + 2)) (word 1 0 0)), .atom (.const (.n (k + 3)) (osGw nsq)),
      .atom (.add (.n (k + 4)) (.n (k + 2)) (.n (k + 3))), .atom (.const (.n (k + 5)) (word 1 0 0)),
      .atom (.const (.n (k + 6)) (osGw nsq)),
      .callIf (.n (k + 4)) loop [.n (k + 5), .n (k + 6), .n (k + 1), .n qpos, .n qbp],
      .atom (.const (.n (k + 7)) (osGw (2 * nsq))), .atom (.mul (.n (k + 8)) (.n (k + 1)) (.n (k + 7))),
      .atom (.load (.n (k + 9)) (.n (k + 8)) 0), .atom (.load (.n (k + 10)) (.n (k + 8)) 1)]
  (pre ++ squeezeT (.n (k + 9)) (.n (k + 10)) (k + 11),
   { s with k := k + 25, f0 := k + 16, f1 := k + 17 })

/-- The query weights `qw[base + i] = lam^i`, `i < nq` (G:1167-1170), from `k`: one value per `i`,
the last power `lam^nq` unused. -/
def osLamPows (lam qw base k : ℕ) : ℕ → List Stmt
  | 0 => []
  | nq + 1 =>
    [.atom (.const (.n k) (word 1 0 0)), .atom (.load (.n k) (.n qw) base)] ++
      (if nq = 0 then [] else
        [.atom (.load (.n lam) (.n qw) (base + 1)), .atom (.mul (.n (k + 1)) (.n lam) (.n lam))] ++
        ((List.range (nq - 1)).map fun i =>
          [.atom (.load (.n (k + 1 + i)) (.n qw) (base + 2 + i)),
            .atom (.mul (.n (k + 2 + i)) (.n (k + 1 + i)) (.n lam))]).flatten)

/-- The fixed buffers' pointers, allocated by the body's head: the cap run, its flags, the final
message, the level roots, the fold challenges, the level scalars, the query weights, the query
positions and bit runs, the out-of-domain points and claims. -/
def osCaps : ℕ := 40
def osFlags : ℕ := 42
def osFmsg : ℕ := 44
def osRoots : ℕ := 46
def osFch : ℕ := 48
def osBetas : ℕ := 50
def osQw : ℕ := 52
def osQpos : ℕ := 54
def osQbp : ℕ := 56
def osOodz : ℕ := 58
def osOod : ℕ := 60

/-- The level's queries (G:1176-1193): the row weights, the cap's root, the queries' sum, the
intro message. Returns the statements, the state after the intro's reads, and the values of the
query sum and of the intro's three coefficients `c0`, `c1`, `c2`. -/
def osQueries (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) : List Stmt × OsSt × ℕ × ℕ × ℕ × ℕ :=
  let k := s.k
  let rw := osHeap cfg.maxIl k
  let p := osMat osFch lv.foldsOff (k + 2)
  let cp := osMat osCaps (4 * lv.capOff) p.2.2
  let fp := osMat osFlags lv.capOff cp.2.2
  let r := fp.2.2
  let cap : List Stmt := [.call lv.verifyCap [.n cp.2.1, .n fp.2.1] [.n r, .n (r + 1)],
    .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))]
  let cp2 := osMat osCaps (4 * lv.capOff) (r + 2)
  let fp2 := osMat osFlags lv.capOff cp2.2.2
  let qp := osMat osQw (lvl * cfg.maxQ) fp2.2.2
  let bp := osMat osQbp lv.posOff qp.2.2
  let g := bp.2.2
  let qs : List Stmt := [.atom (.const (.n g) (osGw lv.queries)),
    .call lv.queriesFn [.n cp2.2.1, .n fp2.2.1, .n qp.2.1, .n bp.2.1, .n (k + 1), .n g] [.n (g + 1)]]
  let s1 : OsSt := { s with k := g + 2 }
  let i0 := osFsNext s1
  let i2 := osFsNext i0.2
  (rw ++ p.1 ++ [.call lv.rowWeights [.n p.2.1, .n (k + 1)] []] ++ cp.1 ++ fp.1 ++ cap ++ cp2.1 ++
    fp2.1 ++ qp.1 ++ bp.1 ++ qs ++ i0.1 ++ i2.1 ++ [.atom (.add (.n i2.2.k) (.n (g + 1)) (.n i0.2.k))],
   { i2.2 with k := i2.2.k + 1 }, g + 1, s1.k, i2.2.k, i0.2.k)

/-- The running quadratic and claim plus `sc` times a claim's value `v` and intro `c0, c1, c2`,
from `k` (G:1203-1206, G:1210-1213). -/
def osGlue (sc v c0 c1 c2 : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  ([.atom (.mul (.n k) (.n sc) (.n c0)), .atom (.add (.n (k + 1)) (.n s.c) (.n k)),
    .atom (.mul (.n (k + 2)) (.n sc) (.n c1)), .atom (.add (.n (k + 3)) (.n s.b) (.n (k + 2))),
    .atom (.mul (.n (k + 4)) (.n sc) (.n c2)), .atom (.add (.n (k + 5)) (.n s.a) (.n (k + 4))),
    .atom (.mul (.n (k + 6)) (.n sc) (.n v)), .atom (.add (.n (k + 7)) (.n s.t) (.n (k + 6)))],
   { s with k := k + 8, c := k + 1, b := k + 3, a := k + 5, t := k + 7 })

/-- An out-of-domain claim glued with the scalar `sc` (G:1199-1207): its value and intro reread
from `ood`, the scalar stored, the running sums updated; the next scalar `sc·lam` at the returned
`OsSt.k - 1`. -/
def osOodGlue (so sc lam : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let pre : List Stmt := [.atom (.load (.n k) (.n osOod) (so + 1)), .atom (.load (.n (k + 1)) (.n osOod) (so + 3)),
    .atom (.load (.n sc) (.n osOod) so), .atom (.load (.n (k + 2)) (.n osOod) (so + 2)),
    .atom (.mul (.n (k + 3)) (.n sc) (.n (k + 2))), .atom (.add (.n (k + 4)) (.n s.c) (.n (k + 3))),
    .atom (.add (.n (k + 5)) (.n k) (.n (k + 1))), .atom (.mul (.n (k + 6)) (.n sc) (.n (k + 5))),
    .atom (.add (.n (k + 7)) (.n s.b) (.n (k + 6))), .atom (.mul (.n (k + 8)) (.n sc) (.n (k + 1))),
    .atom (.add (.n (k + 9)) (.n s.a) (.n (k + 8))), .atom (.mul (.n (k + 10)) (.n sc) (.n k)),
    .atom (.add (.n (k + 11)) (.n s.t) (.n (k + 10))), .atom (.mul (.n (k + 12)) (.n sc) (.n lam))]
  (pre, { s with k := k + 13, c := k + 4, b := k + 7, a := k + 9, t := k + 11 })

/-- The out-of-domain claims `os ..` of level `lvl`, from the scalar `sc`; the last scalar. -/
def osOodGlues (lvl lam : ℕ) : ℕ → ℕ → ℕ → OsSt → List Stmt × OsSt × ℕ
  | _, 0, sc, st => ([], st, sc)
  | os, n + 1, sc, st =>
    let r := osOodGlue ((lvl + 1) * 4 + os * 4) sc lam st
    let rest := osOodGlues lvl lam (os + 1) n (r.2.k - 1) r.2
    (r.1 ++ rest.1, rest.2)

/-- One level of the opening (G:1096-1213). -/
def osLevel (cfg : OsCfg) (lvl : ℕ) (lv : OsLvl) (s : OsSt) : List Stmt × OsSt :=
  let f := osFolds osFch lv.foldsOff lv.folds s
  let m := if lvl = cfg.yrLevel then osFinal cfg.finalMsg osFmsg f.2
    else osCommit lvl lv.logCols lv.oodNext osRoots osOodz osOod f.2
  let gr := osGrind lv.grindBits m.2
  let sq := osSqueezes cfg.maxSq lv.squeezes osQpos osQbp lv.sqLoop gr.2
  let lam := sq.2.k - 1
  let lp := osLamPows lam osQw (lvl * cfg.maxQ) sq.2.k lv.queries
  let q := osQueries cfg lv lvl { sq.2 with k := sq.2.k + lv.queries }
  let o := if lvl = cfg.yrLevel then (([] : List Stmt), q.2.1, lam)
    else osOodGlues lvl lam 0 lv.oodNext lam q.2.1
  let beta := o.2.2
  let gl := osGlue beta q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 o.2.1
  (f.1 ++ m.1 ++ gr.1 ++ sq.1 ++ lp ++ q.1 ++ o.1 ++ [.atom (.load (.n beta) (.n osBetas) lvl)] ++ gl.1,
   gl.2)

/-- The levels `lvl ..`. -/
def osLevels (cfg : OsCfg) : ℕ → List OsLvl → OsSt → List Stmt × OsSt
  | _, [], s => ([], s)
  | lvl, lv :: rest, s =>
    let r := osLevel cfg lvl lv s
    let t := osLevels cfg (lvl + 1) rest r.2
    (r.1 ++ t.1, t.2)


/-! ## The tail, the point, the bases, the residual chains, the out-of-domain weights -/

/-- The tail rounds (G:1216-1228) into `tail_challenges` (`HeapBuf(g^5)` at `k + 1`): `yrLog - 1`
rounds, the closing squeeze (its challenge `last`), the final claim at `t`, the unused entries
zeroed. Returns the statements, the state, the buffer and `last`. -/
def osTail (yrLog : ℕ) (s : OsSt) : List Stmt × OsSt × ℕ × ℕ :=
  let tch := s.k + 1
  let f := osFolds tch 0 (yrLog - 1) { s with k := s.k + 2 }
  let b := f.2.k
  let m := b + 14
  (osHeap 5 s.k ++ f.1 ++ squeezeT (.n f.2.f0) (.n f.2.f1) b ++
    [.atom (.load (.n (b + 13)) (.n tch) (yrLog - 1)),
      .atom (.mul (.n m) (.n (b + 13)) (.n f.2.b)), .atom (.add (.n (m + 1)) (.n f.2.c) (.n m)),
      .atom (.mul (.n (m + 2)) (.n (b + 13)) (.n (b + 13))),
      .atom (.mul (.n (m + 3)) (.n (m + 2)) (.n f.2.a)),
      .atom (.add (.n (m + 4)) (.n (m + 1)) (.n (m + 3)))] ++
    ((List.range (5 - yrLog)).map fun j =>
      [.atom (.const (.n (m + 5 + j)) (word 0 0 0)),
        .atom (.load (.n (m + 5 + j)) (.n tch) (yrLog + j))]).flatten,
   { f.2 with k := m + 5 + (5 - yrLog), f0 := b + 5, f1 := b + 6, t := m + 4 }, tch, b + 13)

/-- The source of entry `i` of the rotated point (G:1240-1247): the fold challenges past the lane
folds, the tail challenges, the lane folds, then zeros. -/
def osPtSrc (nFolds lane yrLog tch i : ℕ) : Option (ℕ × ℕ) :=
  if i < nFolds - lane then some (osFch, lane + i)
  else if i < nFolds - lane + yrLog then some (tch, i - (nFolds - lane))
  else if i < nFolds + yrLog then some (osFch, i - (nFolds - lane) - yrLog)
  else none

/-- Entry `i` of the point at `pt`, its value `v`. -/
def osPtBlk (pt v i : ℕ) : Option (ℕ × ℕ) → List Stmt
  | some (b, o) => [.atom (.load (.n v) (.n b) o), .atom (.load (.n v) (.n pt) i)]
  | none => [.atom (.const (.n v) (word 0 0 0)), .atom (.load (.n v) (.n pt) i)]

/-- The point (`HeapBuf(42)` at `k`), entry `i` through the value `k + 1 + i`. -/
def osPoint (nFolds lane yrLog tch k : ℕ) : List Stmt :=
  .atom (.hint (.alloc (.n k) 42)) ::
    ((List.range 42).map fun i => osPtBlk k (k + 1 + i) i (osPtSrc nFolds lane yrLog tch i)).flatten

/-- One coordinate of a level's basis row (G:1262-1269): the challenge at `src`, `1 + c` stored in
`basis_a`, `c·inv` in `basis_b` (`c` itself when `inv = 1`), from `k`; the next free value. -/
def osBasisBlk (ba bb slot : ℕ) (src : ℕ × ℕ) (inv k : ℕ) : List Stmt × ℕ :=
  let pre : List Stmt := [.atom (.load (.n k) (.n src.1) src.2),
    .atom (.const (.n (k + 1)) (word 1 0 0)), .atom (.add (.n (k + 2)) (.n (k + 1)) (.n k)),
    .atom (.load (.n (k + 2)) (.n ba) slot)]
  if inv = 1 then (pre ++ [.atom (.load (.n k) (.n bb) slot)], k + 3)
  else (pre ++ [.atom (.const (.n (k + 3)) (word inv 0 0)), .atom (.mul (.n (k + 4)) (.n k) (.n (k + 3))),
    .atom (.load (.n (k + 4)) (.n bb) slot)], k + 5)

/-- The coordinates `(slot, source, inverse)` of a basis row, from `k`. -/
def osBasisRow (ba bb : ℕ) : List (ℕ × (ℕ × ℕ) × ℕ) → ℕ → List Stmt × ℕ
  | [], k => ([], k)
  | (slot, src, inv) :: rest, k =>
    let r := osBasisBlk ba bb slot src inv k
    let t := osBasisRow ba bb rest r.2
    (r.1 ++ t.1, t.2)

/-- Level `lvl`'s basis coordinates: the fold challenges after its folds, then the tail. -/
def osBasisCoords (yrLog tch lvl : ℕ) (lv : OsLvl) : List (ℕ × (ℕ × ℕ) × ℕ) :=
  (List.range (lv.prefixLen + yrLog)).map fun t =>
    (lvl * 22 + t, (if t < lv.prefixLen then (osFch, lv.resFoldOff + t) else (tch, t - lv.prefixLen)),
      lv.invs.getD t 0)

/-- Every level's basis row, from `k`. -/
def osBases (yrLog tch ba bb : ℕ) : ℕ → List OsLvl → ℕ → List Stmt × ℕ
  | _, [], k => ([], k)
  | lvl, lv :: rest, k =>
    let r := osBasisRow ba bb (osBasisCoords yrLog tch lvl lv) k
    let t := osBases yrLog tch ba bb (lvl + 1) rest r.2
    (r.1 ++ t.1, t.2)

/-- Level `lvl`'s residual chain (G:1276-1296), from `k`: the chain's buffer, the loop over its
queries, `inner[lvl + 1] = inner[lvl] + beta·chain[n]`. -/
def osResidual (maxQ ich ba bb lvl : ℕ) (lv : OsLvl) (k : ℕ) : List Stmt :=
  osHeap (maxQ + 1) k ++
    [.atom (.const (.n (k + 2)) (word 0 0 0)), .atom (.load (.n (k + 2)) (.n (k + 1)) 0),
      .atom (.const (.n (k + 3)) (word 1 0 0)), .atom (.const (.n (k + 4)) (osGw lv.queries)),
      .atom (.add (.n (k + 5)) (.n (k + 3)) (.n (k + 4))), .atom (.const (.n (k + 6)) (word 1 0 0)),
      .atom (.const (.n (k + 7)) (osGw lv.queries)),
      .callIf (.n (k + 5)) lv.resLoop
        [.n (k + 6), .n (k + 7), .n osQpos, .n ba, .n bb, .n (k + 1), .n osQw],
      .atom (.load (.n (k + 8)) (.n ich) lvl), .atom (.load (.n (k + 9)) (.n osBetas) lvl),
      .atom (.load (.n (k + 10)) (.n (k + 1)) lv.queries),
      .atom (.mul (.n (k + 11)) (.n (k + 9)) (.n (k + 10))),
      .atom (.add (.n (k + 12)) (.n (k + 8)) (.n (k + 11))),
      .atom (.load (.n (k + 12)) (.n ich) (lvl + 1))]

/-- Every level's residual chain, level `lvl` from `k + 13·lvl`. -/
def osResiduals (maxQ ich ba bb k : ℕ) (lvs : List OsLvl) : List Stmt :=
  (lvs.zipIdx.map fun (lv, lvl) => osResidual maxQ ich ba bb lvl lv (k + 13 * lvl)).flatten

/-- One factor `sc·(1 + z + c)` of an out-of-domain weight, from `k` (G:1306-1309). -/
def osOodFac (sc zo : ℕ) (src : ℕ × ℕ) (k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (word 1 0 0)), .atom (.load (.n (k + 1)) (.n osOodz) zo),
    .atom (.add (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.load (.n (k + 3)) (.n src.1) src.2),
    .atom (.add (.n (k + 4)) (.n (k + 2)) (.n (k + 3))), .atom (.mul (.n (k + 5)) (.n sc) (.n (k + 4)))]

/-- The factors of an out-of-domain weight over `(z offset, source)`, from the scalar `sc` at `k`;
each factor's product is its last value. -/
def osOodFacs (sc k : ℕ) (coords : List (ℕ × ℕ × ℕ)) : List Stmt :=
  (coords.zipIdx.map fun ((zo, src), j) =>
    osOodFac (if j = 0 then sc else k + 6 * j - 1) zo src (k + 6 * j)).flatten

/-- The out-of-domain weight of level `ol`'s sample `os` (G:1302-1310), from `k`: the scalar,
then its factors; the weight is the last value. -/
def osOodWeight (yrLog tch zf ris ol os k : ℕ) : List Stmt :=
  .atom (.load (.n k) (.n osOod) (ol * 4 + os * 4)) ::
    osOodFacs k (k + 1) ((List.range (zf + yrLog)).map fun t =>
      ((ol + os) * 22 + t, if t < zf then (osFch, ris + t) else (tch, t - zf)))

/-- The out-of-domain weights of the levels `ol ..` (each after the first), summed into `acc`,
from `k`: the statements, the sum and the next free value. -/
def osOodWeights (yrLog tch : ℕ) (prevCols : ℕ) :
    ℕ → List OsLvl → Option ℕ → ℕ → List Stmt × Option ℕ × ℕ
  | _, [], acc, k => ([], acc, k)
  | ol, lv :: rest, acc, k =>
    let zf := prevCols - yrLog
    let r := (List.range lv.oodHere).foldl (fun (st : List Stmt × Option ℕ × ℕ) os =>
      let w := osOodWeight yrLog tch zf lv.foldsOff ol os st.2.2
      let last := st.2.2 + 6 * (zf + yrLog)
      match st.2.1 with
      | none => (st.1 ++ w, some last, last + 1)
      | some a => (st.1 ++ w ++ [.atom (.add (.n (last + 1)) (.n a) (.n last))], some (last + 1), last + 2))
      ([], acc, k)
    let t := osOodWeights yrLog tch lv.logCols (ol + 1) rest r.2.1 r.2.2
    (r.1 ++ t.1, t.2)

/-! ## The loop helpers -/

/-- Square-and-multiply of the value `x` by the binary digits `ds` (most significant first, after
the leading one), from the accumulator `acc` and `k`: the statements and the result. -/
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

/-- The pointer `base·g^posOff·q` from `k`: the statements, its value and the next free value. -/
def sqPtr (posOff q base k : ℕ) : List Stmt × ℕ × ℕ :=
  if posOff = 0 then ([.atom (.mul (.n k) (.n base) (.n q))], k, k + 1)
  else ([.atom (.const (.n k) (osGw posOff)), .atom (.mul (.n (k + 1)) (.n base) (.n k)),
    .atom (.mul (.n (k + 2)) (.n (k + 1)) (.n q))], k + 2, k + 3)

/-- The squeeze loop's body (G:1147-1157), at `x, N, sqz, qpos, qbp` (values `0 .. 4`): the row
`sqz·x²`, one squeeze, the next state stored, the decoded positions and bit runs at
`g^posOff·x^(192/depth)`, then the loop's tail. -/
def sqLoopBody (depth posOff : ℕ) (decode loop : String) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (192 / depth)) 0 27
  let q := pw.2
  let k := 27 + (osPowDigits (192 / depth)).length + ((osPowDigits (192 / depth)).filter id).length
  let p1 := sqPtr posOff q 3 k
  let p2 := sqPtr posOff q 4 p1.2.2
  let e := p2.2.2
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 2) (.n 5)),
    .atom (.load (.n 7) (.n 6) 0), .atom (.load (.n 8) (.n 6) 1),
    .atom (.copy (.n 9) (.n 7)), .atom (.copy (.n 10) (.n 8))] ++ squeezeT (.n 9) (.n 10) 11 ++
    [.atom (.copy (.n 25) (.n 16)), .atom (.copy (.n 26) (.n 17)),
      .atom (.load (.n 25) (.n 6) 2), .atom (.load (.n 26) (.n 6) 3)] ++ pw.1 ++ p1.1 ++ p2.1 ++
    [.call decode [.n 24, .n p1.2.1, .n p2.2.1] [],
      .atom (.const (.n e) (word 2 0 0)), .atom (.mul (.n (e + 1)) (.n 0) (.n e)),
      .atom (.add (.n (e + 2)) (.n (e + 1)) (.n 1)), .atom (.const (.n (e + 3)) (word 2 0 0)),
      .atom (.mul (.n (e + 4)) (.n 0) (.n (e + 3))),
      .callIf (.n (e + 2)) loop [.n (e + 4), .n 1, .n 2, .n 3, .n 4], .ret []]

/-- Coordinate `t ≥ 1` of the residual loop (G:1288-1292), from `k = 13 + 8(t - 1)`: the chain's
next value, the coordinate's factor, the running product. -/
def resStep (row : ℕ) (val : ℕ) (t : ℕ) : List Stmt :=
  let k := 13 + 8 * (t - 1)
  let ch := if t = 1 then 8 else k - 6
  let pe := if t = 1 then 12 else k - 1
  [.atom (.const (.n k) (word val 0 0)), .atom (.add (.n (k + 1)) (.n ch) (.n k)),
    .atom (.mul (.n (k + 2)) (.n ch) (.n (k + 1))), .atom (.load (.n (k + 3)) (.n 3) (row + t)),
    .atom (.load (.n (k + 4)) (.n 4) (row + t)), .atom (.mul (.n (k + 5)) (.n (k + 4)) (.n (k + 2))),
    .atom (.add (.n (k + 6)) (.n (k + 3)) (.n (k + 5))), .atom (.mul (.n (k + 7)) (.n pe) (.n (k + 6)))]

/-- The residual loop's body (G:1283-1294), at `x, N, qpos, basis_a, basis_b, chain, qw` (values
`0 .. 6`): the query's position, its basis product over the `cols` coordinates (`vals` the
vanishing values), `chain[x·g] = chain[x] + qw[lvl·maxQ·x]·product`, then the loop's tail. -/
def resLoopBody (posOff row cols qo : ℕ) (vals : List ℕ) (loop : String) : List Stmt :=
  let e := 13 + 8 * (cols - 1)
  let pe := if cols = 1 then 12 else e - 1
  [.atom (.mul (.n 7) (.n 2) (.n 0)), .atom (.load (.n 8) (.n 7) posOff),
    .atom (.load (.n 9) (.n 3) row), .atom (.load (.n 10) (.n 4) row),
    .atom (.mul (.n 11) (.n 10) (.n 8)), .atom (.add (.n 12) (.n 9) (.n 11))] ++
    ((List.range (cols - 1)).map fun t => resStep row (vals.getD t 0) (t + 1)).flatten ++
    [.atom (.mul (.n e) (.n 5) (.n 0)), .atom (.load (.n (e + 1)) (.n e) 0),
      .atom (.mul (.n (e + 2)) (.n 6) (.n 0)), .atom (.load (.n (e + 3)) (.n (e + 2)) qo),
      .atom (.mul (.n (e + 4)) (.n (e + 3)) (.n pe)), .atom (.add (.n (e + 5)) (.n (e + 1)) (.n (e + 4))),
      .atom (.mul (.n (e + 6)) (.n 5) (.n 0)), .atom (.load (.n (e + 5)) (.n (e + 6)) 1),
      .atom (.const (.n (e + 7)) (word 2 0 0)), .atom (.mul (.n (e + 8)) (.n 0) (.n (e + 7))),
      .atom (.add (.n (e + 9)) (.n (e + 8)) (.n 1)), .atom (.const (.n (e + 10)) (word 2 0 0)),
      .atom (.mul (.n (e + 11)) (.n 0) (.n (e + 10))),
      .callIf (.n (e + 9)) loop [.n (e + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []]

/-- Level `lv`'s squeeze loop body. -/
def sqLoopOf (lv : OsLvl) : List Stmt := sqLoopBody lv.depth lv.posOff lv.decode lv.sqLoop

/-- Level `lvl`'s residual loop body. -/
def resLoopOf (cfg : OsCfg) (lvl : ℕ) (lv : OsLvl) : List Stmt :=
  resLoopBody lv.posOff (lvl * 22) lv.logCols (lvl * cfg.maxQ) lv.vals lv.resLoop

/-! ## The body -/

/-- The head (G:1062-1094): the state copied, the first quadratic read, the fixed buffers. -/
def osHead (cfg : OsCfg) : List Stmt × OsSt :=
  let s0 : OsSt := ⟨8, 6, 7, 5, 0, 0, 0, 0, 2⟩
  let c := osFsNext s0
  let a := osFsNext c.2
  let n := cfg.levels.length
  ([.atom (.copy (.n 6) (.n 0)), .atom (.copy (.n 7) (.n 1))] ++ c.1 ++ a.1 ++
    [.atom (.add (.n 38) (.n 2) (.n 23))] ++
    osHeap (4 * cfg.capLen) 39 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n osCaps) 0 (4 * cfg.capLen))))] ++
    osHeap cfg.capLen 41 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n osFlags) 0 cfg.capLen)))] ++
    osHeap cfg.yrLen 43 ++ osHeap (2 * n) 45 ++
    [.atom (.load (.n 3) (.n osRoots) 0), .atom (.load (.n 4) (.n osRoots) 1)] ++
    osHeap cfg.nFolds 47 ++ osHeap n 49 ++ osHeap (n * cfg.maxQ) 51 ++ osHeap cfg.posLen 53 ++
    osHeap cfg.posLen 55 ++ osHeap (n * 22) 57 ++ osHeap (n * 4) 59,
   ⟨61, a.2.f0, a.2.f1, 5, 2, 8, 38, 23, 2⟩)

/-- The body after the tail rounds (G:1229-1317), from the tail's state `st` (its next free
value, its final claim) and `tail_challenges` at `tch`: the residual's value, the point, the basis
rows, the residual chains, the out-of-domain weights, the returns. -/
def osFinish (cfg : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt :=
  let yat := st.k
  let pt := yat + 1
  let lane := (cfg.levels.headD default).folds
  let ba := pt + 44
  let bb := pt + 46
  let bs := osBases cfg.yrLog tch ba bb 0 cfg.levels (pt + 47)
  let ich := bs.2 + 1
  let n := cfg.levels.length
  let rk := bs.2 + 3 + 13 * n
  let od := osOodWeights cfg.yrLog tch ((cfg.levels.headD default).logCols) 1 cfg.levels.tail none rk
  let k := od.2.2
  let tot := (match od.2.1 with | none => ([], k + 2) | some a => ([.atom (.add (.n (k + 3)) (.n (k + 2)) (.n a))], k + 3) : List Stmt × ℕ)
  [.call cfg.foldFinal [.n osFmsg, .n tch] [.n yat]] ++
    osPoint cfg.nFolds lane cfg.yrLog tch pt ++ osHeap (n * 22) (pt + 43) ++ osHeap (n * 22) (pt + 45) ++
    bs.1 ++ osHeap (n + 1) bs.2 ++
    [.atom (.const (.n (bs.2 + 2)) (word 0 0 0)), .atom (.load (.n (bs.2 + 2)) (.n ich) 0)] ++
    osResiduals cfg.maxQ ich ba bb (bs.2 + 3) cfg.levels ++ od.1 ++
    [.atom (.copy (.n k) (.n st.t)), .atom (.copy (.n (k + 1)) (.n pt)),
      .atom (.load (.n (k + 2)) (.n ich) n)] ++ tot.1 ++
    [.atom (.copy (.n (tot.2 + 1)) (.n yat)), .ret [.n k, .n (k + 1), .n tot.2, .n (tot.2 + 1)]]

/-- The body of `open_stacked` at a configuration. -/
def osBody (cfg : OsCfg) : List Stmt :=
  let h := osHead cfg
  let lv := osLevels cfg 0 cfg.levels h.2
  let tl := osTail cfg.yrLog lv.2
  h.1 ++ lv.1 ++ tl.1 ++ osFinish cfg tl.2.1 tl.2.2.1

end
end LeanVM.Guest.B1
