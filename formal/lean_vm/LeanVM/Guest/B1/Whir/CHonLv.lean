/-
  LeanVM.Guest.B1.Whir.CHonLv

  A level of the honest run in the guest's terms: its query grind's permutation, its squeezes,
  `λ`, its record, the guest's data of the level.
-/

module

public import LeanVM.Guest.B1.Whir.CHon
public import LeanVM.Guest.B1.Whir.CLevel
public import LeanVM.Guest.B1.Whir.FinishSound

/-!
# A level, in the guest's terms

On a level `L : LvAt` of the honest run (`Whir/CHon`): the capacity after its folds `cap1`, its
query grind's permutation `qS`, the sponge after its positions' squeezes `F3`, its samples `word j`
and the squeezes' capacities `capSq j`, `λ` (`0` at the final level), its phase, its record
(`OsRec`, S1a-3's), its non-final (`nw`) or final (`fw`) reads; the guest's data of the level
(`midW`, `finWD`) and its claim at the level's start, the Spec's less the deficit (`gcl`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace LvAt

variable (L : LvAt) (logN : ℕ)

/-- The capacity after the level's folds. -/
def cap1 : List E := roundsCap L.level.fold L.cap L.rw

/-- The non-final level's reads (dummy at the final one). -/
def nw : NextW := match L.d with
  | .next _ W => W
  | .fin _ _ => ⟨0, 0, [], 0, 0, 0, []⟩

/-- The final level's reads (dummy at a non-final one). -/
def fw : FinW := match L.d with
  | .fin _ W => W
  | .next _ _ => ⟨[], 0, [], []⟩

/-- The query grind's permutation. -/
def qS : KeccakState := match L.d with
  | .next _ W => W.qS L.F (L.mu logN)
  | .fin _ W => W.qS L.F

/-- The sponge after the positions' squeezes. -/
def F3 : Fs := match L.d with
  | .next _ W => W.F3 L.F (L.mu logN) (L.dp logN) L.level.queries
  | .fin _ W => W.F3 L.F (L.dp logN) L.level.queries

/-- Sample `j` of the positions. -/
def word (j : ℕ) : E := sqSample (challengeOf (L.qS logN)) (capOf (L.qS logN)) j

/-- The capacity before sample `j ≥ 1`. -/
def capSq (j : ℕ) : List E := sqCap (capOf (L.qS logN)) (j - 1)

/-- `λ`, `0` at the final level. -/
def lam : E := match L.d with
  | .next _ W => W.lam L.F (L.mu logN) (L.dp logN) L.level.queries
  | .fin _ _ => 0

/-- The level's phase of openings. -/
def phase : List Opening := match L.d with
  | .next _ W => W.phase
  | .fin _ W => W.phase

/-- The level's record (a default one at the final level). -/
def osRec : OsRec := match L.d with
  | .next _ W => W.osRec logN L.level L.s1 L.F
  | .fin _ _ => default

/-- **The guest's data of a non-final level**, given the cap's root cells, the batch and the
pointers of `sent` and the squeeze run. -/
def midW (r0 r1 batched pS pZ : E) : MidW :=
  ⟨L.rw, L.nw.x0, L.nw.x1, L.nw.high, L.nw.n1, L.nw.y0, L.nw.nn, r0, r1, batched, pS, pZ⟩

/-- **The guest's data of the final level**, given the cap's root cells, the batch and the
pointers of the squeeze run and the normalized lane. -/
def finWD (r0 r1 batched pZ pH : E) : FinWD :=
  ⟨L.rw, L.fw.fold, L.fw.nn, r0, r1, batched, pZ, pH⟩

/-- **The guest's claim at the level's start**: the Spec's plus the deficit of the records
`recs` before it. -/
def gcl (recs : List OsRec) : E := L.s.claim + recsDeficit recs L.s.alphas

end LvAt

/-- The records of the levels before `i`. -/
def lvsRecs (logN : ℕ) (Ls : List LvAt) (i : ℕ) : List OsRec := (Ls.take i).map (·.osRec logN)

end
end LeanVM.Guest.B1.Whir
