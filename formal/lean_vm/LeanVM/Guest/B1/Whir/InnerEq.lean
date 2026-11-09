/-
  LeanVM.Guest.B1.Whir.InnerEq

  The guest's glued weight is the Spec's: `Σ` over the glued claims of their scalar times their
  weight at the terminal point.
-/

module

public import LeanVM.Guest.B1.Whir.Finish
public import LeanVM.Guest.B1.Whir.InnerSpec
public import LeanVM.Guest.B1.Whir.Level

/-!
# The glued weight (V:1826-1828)

The Spec sums `scalar·weightAt(point)` over the glued claims, each level gluing its
out-of-domain claim (`λ·eqEval z`, not at the last level) and its query claim
(`β·inducedWeight`, `β = λ²` or `λ` at the last level) (`contrib_eq`). The guest computes
`Σ_lvl scale_lvl·sum_lvl` with the scale `β·Π_t x_t·inv_t` and the residual sums
(`level_term`, by `induced_factor`), and the out-of-domain weights apart (`oodSum_levels`):
`inner_eq`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

instance : Inhabited OsRec := ⟨⟨0, [], none, 0, 0⟩⟩

/-! ## The Spec's sum, by record -/

/-- A glued claim's weight at the terminal. -/
def claimW (F T : List E) (cl : GluedClaim) : E := cl.scalar * cl.weightAt (F.drop cl.foldStart ++ T)

/-- A record's claims' weights. -/
def contrib (F T : List E) (r : OsRec) : E := ((recClaims r).map (claimW F T)).sum

theorem foldl_claims (F T : List E) : ∀ (L : List GluedClaim) (a : E),
    L.foldl (fun w cl ↦ w + cl.scalar * cl.weightAt (F.drop cl.foldStart ++ T)) a =
      a + (L.map (claimW F T)).sum
  | [], a => by simp
  | cl :: L, a => by
    rw [List.foldl_cons, foldl_claims F T L]
    simp only [List.map_cons, List.sum_cons, claimW]
    ring

theorem specInner_eq (F T : List E) (rs : List OsRec) :
    (rs.flatMap recClaims).foldl (fun w cl ↦ w + cl.scalar * cl.weightAt (F.drop cl.foldStart ++ T))
      0 = ∑ i ∈ Finset.range rs.length, contrib F T (rs.getD i default) := by
  rw [foldl_claims, zero_add]
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, contrib]
    ring

/-- A record's out-of-domain claim's weight. -/
def oodPart (F T : List E) (r : OsRec) : E :=
  match r.z with
  | some z => r.lam * eqEval z (F.drop r.F ++ T)
  | none => 0

/-- A record's query claim's scalar. -/
def betaR (r : OsRec) : E :=
  match r.z with
  | some _ => r.lam * r.lam
  | none => r.lam

theorem contrib_eq (F T : List E) (r : OsRec) :
    contrib F T r = oodPart F T r +
      betaR r * inducedWeight r.ml r.qs (powers r.lam r.qs.length) (F.drop r.F ++ T) := by
  obtain ⟨lam, qs, z, Fo, ml⟩ := r
  cases z <;> simp [contrib, recClaims, oodPart, betaR, claimW]

/-! ## The guest's level term -/

/-- **A level's scale times its residual sum** is its query claim's weight. -/
theorem level_term {lv : OsLv} {X : ℕ → E} {x : List E} {qs : List ℕ} {lam b : E} {len : ℕ}
    (hlen : len = lv.logCols) (hx : x.length = lv.logCols)
    (hX : ∀ t < lv.logCols, X t = x.getD t 0)
    (hval : ∀ t < lv.logCols,
      word (vanishVal (lv.vanish + t)) 0 0 = (subspaceRoots lv.logCols).getD t 0)
    (hinv : ∀ t < lv.logCols, word (vanishInv (lv.vanish + t)) 0 0 = (invsOf lv.logCols).getD t 0)
    (hne : ∀ t < lv.logCols, X t * invW lv t ≠ 0) :
    (b * ∏ t ∈ Finset.range len, (X t * invW lv t)) *
        ∑ j ∈ Finset.range qs.length, lam ^ j * lvRes lv (dOf lv X) (eOfNat (qs.getD j 0)) =
      b * inducedWeight lv.logCols qs (powers lam qs.length) x := by
  rw [inducedWeight_eq, hx, hlen, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hp : ∏ t ∈ Finset.range lv.logCols, (1 + x.getD t 0 * (1 + chainF (subspaceRoots lv.logCols)
      0 (eOfNat (qs.getD j 0)) t * (invsOf lv.logCols).getD t 0)) =
      ∏ t ∈ Finset.range lv.logCols, (1 + X t * (1 + chainF (subspaceRoots lv.logCols)
        0 (eOfNat (qs.getD j 0)) t * (invsOf lv.logCols).getD t 0)) :=
    Finset.prod_congr rfl fun t ht ↦ by rw [hX t (Finset.mem_range.mp ht)]
  rw [hp, induced_factor (eOfNat (qs.getD j 0)) hval hinv hne]
  have hd : (fun t ↦ (1 + X t) / (X t * word (vanishInv (lv.vanish + t)) 0 0)) = dOf lv X := rfl
  rw [hd]
  simp only [lvRes, invW]
  ring

/-! ## The out-of-domain weights -/

theorem oodSum_levels (c : OsCfg) (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) :
    ∀ (L : List OsLv) (ol : ℕ),
      oodSum c Λ Z Y (L.headD default).logCols ol L.tail =
        ∑ i ∈ Finset.range (L.length - 1), Λ (ol + i) *
          ∏ t ∈ Finset.range ((L.getD i default).logCols - c.yrLog + c.yrLog),
            (1 + Z (ol + i) t + Y (ol + i) t)
  | [], _ => by simp [oodSum]
  | [_], _ => by simp [oodSum]
  | a :: b :: L, ol => by
    have ih := oodSum_levels c Λ Z Y (b :: L) (ol + 1)
    simp only [List.headD_cons, List.tail_cons] at ih ⊢
    rw [oodSum, ih]
    simp only [List.length_cons, Nat.add_sub_cancel, Finset.sum_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) rfl
    rw [show ol + 1 + i = ol + (i + 1) by ring]

/-! ## The guest's choices -/

/-- Level `i`'s coordinates: the fold challenges after its folds, then the tail. -/
def Xof (rs : List OsRec) (F T : List E) (i t : ℕ) : E :=
  (F.drop (rs.getD i default).F ++ T).getD t 0

/-- Level `i`'s batching scalar in `level_betas`. -/
def βof (c : OsCfg) (rs : List OsRec) (i : ℕ) : E :=
  if i = c.yrLevel then (rs.getD i default).lam else (rs.getD i default).lam * (rs.getD i default).lam

def Pof (rs : List OsRec) (i j : ℕ) : E := eOfNat ((rs.getD i default).qs.getD j 0)

def Wof (rs : List OsRec) (i j : ℕ) : E := (rs.getD i default).lam ^ j

def Λof (rs : List OsRec) (ol : ℕ) : E := (rs.getD (ol - 1) default).lam

def Zof (rs : List OsRec) (ol t : ℕ) : E := (((rs.getD (ol - 1) default).z).getD []).getD t 0

def Yof (rs : List OsRec) (F T : List E) (ol t : ℕ) : E := Xof rs F T (ol - 1) t

/-- What the identity needs of a level. -/
structure LvFin (c : OsCfg) (rs : List OsRec) (F T : List E) (i : ℕ) : Prop where
  fle : (rs.getD i default).F ≤ F.length
  ml : F.length - (rs.getD i default).F + T.length = (c.levels.getD i default).logCols
  rml : (rs.getD i default).ml = (c.levels.getD i default).logCols
  qs : (rs.getD i default).qs.length = (c.levels.getD i default).queries
  pre : (c.levels.getD i default).prefixLen + c.yrLog = (c.levels.getD i default).logCols
  val : ∀ t < (c.levels.getD i default).logCols,
    word (vanishVal ((c.levels.getD i default).vanish + t)) 0 0 =
      (subspaceRoots (c.levels.getD i default).logCols).getD t 0
  inv : ∀ t < (c.levels.getD i default).logCols,
    word (vanishInv ((c.levels.getD i default).vanish + t)) 0 0 =
      (invsOf (c.levels.getD i default).logCols).getD t 0
  ne : ∀ t < (c.levels.getD i default).logCols,
    Xof rs F T i t * invW (c.levels.getD i default) t ≠ 0
  zfin : i = c.yrLevel → (rs.getD i default).z = none
  z : i ≠ c.yrLevel → ∃ z, (rs.getD i default).z = some z ∧
    z.length = (c.levels.getD i default).logCols

theorem xof_length {c : OsCfg} {rs : List OsRec} {F T : List E} {i : ℕ} (h : LvFin c rs F T i) :
    (F.drop (rs.getD i default).F ++ T).length = (c.levels.getD i default).logCols := by
  rw [List.length_append, List.length_drop, h.ml]

/-- **The guest's glued weight is the Spec's.** -/
theorem inner_eq {c : OsCfg} {rs : List OsRec} {F T : List E} (hn : rs.length = c.levels.length)
    (hn1 : 1 ≤ c.levels.length) (hyr : c.yrLevel = c.levels.length - 1)
    (hT : T.length = c.yrLog) (hlv : ∀ i < c.levels.length, LvFin c rs F T i) :
    (rs.flatMap recClaims).foldl (fun w cl ↦ w + cl.scalar * cl.weightAt (F.drop cl.foldStart ++ T))
      0 = finInner c (βof c rs) (Xof rs F T) (Pof rs) (Wof rs) (Λof rs) (Zof rs) (Yof rs F T) := by
  rw [specInner_eq, hn]
  simp only [contrib_eq, Finset.sum_add_distrib, finInner]
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the query claims
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have h := hlv i (Finset.mem_range.mp hi)
    have hb : βof c rs i = betaR (rs.getD i default) := by
      unfold βof betaR
      by_cases hy : i = c.yrLevel
      · rw [h.zfin hy]; simp [hy]
      · obtain ⟨z, hz, -⟩ := h.z hy
        rw [hz]; simp [hy]
    rw [hb, h.rml, ← h.qs]
    simp only [Wof, Pof]
    refine Eq.symm ?_
    exact level_term (lv := c.levels.getD i default) (X := Xof rs F T i)
      (x := F.drop (rs.getD i default).F ++ T) (qs := (rs.getD i default).qs)
      (lam := (rs.getD i default).lam) (b := betaR (rs.getD i default)) h.pre (xof_length h)
      (fun t _ ↦ rfl) h.val h.inv h.ne
  · -- the out-of-domain claims
    rw [oodSum_levels]
    obtain ⟨m, hm⟩ : ∃ m, c.levels.length = m + 1 := ⟨c.levels.length - 1, by omega⟩
    rw [hm, Finset.sum_range_succ, Nat.add_sub_cancel]
    have hlast : oodPart F T (rs.getD m default) = 0 := by
      have h := hlv m (by omega)
      rw [oodPart, h.zfin (by omega)]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    have h := hlv i (by omega)
    obtain ⟨z, hz, hzl⟩ := h.z (by omega)
    have hcols : (c.levels.getD i default).logCols - c.yrLog + c.yrLog =
        (c.levels.getD i default).logCols := by
      have := h.ml; omega
    simp only [Λof, Zof, Yof, Nat.add_sub_cancel_left, hcols, oodPart, hz, Option.getD_some]
    rw [eqEval_eq, hzl, xof_length h, min_self]
    simp only [Xof]

end
end LeanVM.Guest.B1.Whir
