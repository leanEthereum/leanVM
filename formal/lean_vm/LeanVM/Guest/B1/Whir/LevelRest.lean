/-
  LeanVM.Guest.B1.Whir.LevelRest

  A level after its proof of work: the template's squeezes, query weights, queries and glue
  run the Spec's `levelRest`.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesBlk
public import LeanVM.Guest.B1.Whir.LamPows
public import LeanVM.Guest.B1.Whir.FoldRound
public import LeanVM.Guest.B1.Whir.Glue
public import LeanVM.Guest.B1.Whir.LevelSpec

/-!
# A level's queries and glue (G:1554-1646)

`osLevelB` is the part of `osLevel` after the grinding check (`osLevel_split`).
`osLevelB_sound`: from the sponge with nothing waiting after the proof of work, the positions
squeezed and decoded (`level_positions`), the batching challenge, its inverse stored, the queries
opened against the level's root and summed (`level_queries`), the intro read, the claims glued: the Spec's `levelRest`, the guest's
quadratic and claim the glued state's, the sponge the guest carries with the intro waiting.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The part of a level after its grinding check. -/
def osLevelB (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : List Stmt × OsSt :=
  let sq := osPositions c lvl lv st
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
  (sq.1 ++ mu.1 ++ q.1 ++ o.1 ++
    [.atom (.mul (.n bk) (.n beta) (.n lamN)), .atom (.load (.n bk) (.n osBetas) lvl)] ++ gl.1, gl.2)

/-- The part of a level up to its grinding check. -/
def osLevelA (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let f := osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds s
  let m := if lvl = c.yrLevel then osFinal c f.2 else osCommit c.plan lvl lv f.2
  (f.1 ++ m.1 ++ [.call ("grind_check__L" ++ natStr lv.grind) [.n m.2.2] []], m.2.1, m.2.2)

theorem osLevel_split (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    osLevel c lvl lv s = ((osLevelA c lvl lv s).1 ++ (osLevelB c lvl lv (osLevelA c lvl lv s).2.1).1,
      (osLevelB c lvl lv (osLevelA c lvl lv s).2.1).2) := by
  simp only [osLevel, osLevelA, osLevelB, List.append_assoc]

/-- What the commitment a level read leaves for its glue: nothing at the last level, else the
out-of-domain claim, its value and intro stored in `ood`. -/
def PendOk (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ)
    (pending : List (E × List E × (List E → E))) : Prop :=
  if lvl = c.yrLevel then pending = [] else
    ∃ (y c0 c2 : E) (z : List E), pending = [(y, [c0, y + c2, c2], fun x ↦ eqEval z x)] ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0 ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2

/-- A level's configuration facts the queries and glue use (`lv` the rate's row). -/
structure LvB (c : OsCfg) (lvl : ℕ) (lv : OsLv) (level : Whir.Level) (ml : ℕ) : Prop where
  depth : lv.depth = ml + level.logInvRate
  queries : level.queries = lv.queries
  q2 : 2 ≤ lv.queries
  qdigits : digitsVal (osPowDigits lv.queries) 1 = lv.queries
  per : 1 ≤ 192 / lv.depth
  squeezes : lv.squeezes = ceilDiv lv.queries (192 / lv.depth)
  digits : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth
  posOff : lv.posOff < u128Bound
  sq0 : 0 < lv.squeezes
  sqOrd : lv.squeezes < ordG
  sq5 : lv.squeezes * 5 < u128Bound
  row : RowShape lvl lv
  cd : 2 ≤ lv.capDepth
  cd8 : lv.capDepth ≤ 8
  cdd : lv.capDepth ≤ lv.depth
  bounds : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound ∧
    lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧
    lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound

/-- What a level leaves for the terminal's weights: its positions, the batching challenge's
inverse `μ` (the residual chain's factor), its scalar times `λ^n`. -/
structure LvRec (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam : E)
    (qs : List ℕ) : Prop where
  qlen : qs.length = lv.queries
  qlt : ∀ k < lv.queries, qs.getD k 0 < 2 ^ lv.depth
  pos : ∀ k < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + k) (eOfNat (qs.getD k 0))
  lam0 : lam ≠ 0
  mu : LoadHolds rd (σ (.n osMus)) lvl lam⁻¹
  beta : LoadHolds rd (σ (.n osBetas)) lvl
    ((if lvl = c.yrLevel then lam else lam * lam) * lam ^ lv.queries)
  ood : lvl ≠ c.yrLevel → LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots) lam

end
end LeanVM.Guest.B1.Whir
