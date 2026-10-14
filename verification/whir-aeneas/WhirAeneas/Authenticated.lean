import WhirAeneas.Compose

/-! The model's `AuthenticatedRows` for the script's opening. The native verifier reads a next
oracle only as a presence marker, so `Script.prf` carries an empty one; `withOracles` puts each
level's committed oracle table in its place. `nativeVerify` cannot tell the two apart, and when
every opened row is the committed table's row at its query, the opening with the tables
satisfies `AuthenticatedRows` against the first committed table. -/
namespace WhirAeneas.Replay
open Whir Whir.Concrete Whir.WHIRNativeArithmetic

/-- The opening with level `i`'s next oracle, when present, replaced by `tables (i + 1)`. -/
def withOracles (P : Protocol.Opening) (tables : Nat → Protocol.Oracle) : Protocol.Opening :=
  { P with levels := P.levels.mapIdx fun i lp =>
      { lp with nextOracle := lp.nextOracle.map fun _ => tables (i + 1) } }

theorem withOracles_level (P : Protocol.Opening) (tables : Nat → Protocol.Oracle) (i : Nat) :
    (withOracles P tables).levels[i]! =
      { P.levels[i]! with nextOracle := P.levels[i]!.nextOracle.map fun _ => tables (i + 1) } := by
  by_cases hi : i < P.levels.size
  · simp [withOracles, getElem!_pos, hi]
  · simp [withOracles, getElem!_def, hi]
    rfl

theorem verifyLevel_withOracles (c : Protocol.Config) (ch : Protocol.Challenges) (P : Protocol.Opening)
    (tables : Nat → Protocol.Oracle) (i : Nat) (st : State) :
    verifyLevel c ch (withOracles P tables) i st = verifyLevel c ch P i st := by
  simp only [verifyLevel, withOracles_level, Option.isSome_map]
  rfl

theorem nativeVerify_withOracles (c : Protocol.Config) (ch : Protocol.Challenges) (lanes : Nat)
    (x : Concrete.E) (callerAt : Array Concrete.E → Concrete.E) (P : Protocol.Opening)
    (tables : Nat → Protocol.Oracle) :
    nativeVerify c ch lanes x callerAt (withOracles P tables) = nativeVerify c ch lanes x callerAt P := by
  have hv : verifyLevel c ch (withOracles P tables) = verifyLevel c ch P := by
    funext i st; exact verifyLevel_withOracles c ch P tables i st
  have hs : (withOracles P tables).levels.size = P.levels.size := by simp [withOracles]
  have hc : ∀ st, closeTail ch (withOracles P tables) st = closeTail ch P st := fun _ => rfl
  simp only [nativeVerify, hv, hs, hc]
  rfl

section Rows
variable {V R K Q E : Type} (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)

/-- An opened row as the model reads it: at level 0 each word is a base element, later each
three words are one extension element. -/
def encRow (base : Bool) (w : List K) : Array Concrete.E :=
  if base then (w.map fun k => Concrete.E.ofK (encodeK k)).toArray else (eRow encodeK ofLimbs w).toArray

theorem prf_rows (base : Bool) (l : SLevel E Q R K) :
    (l.prf encode encodeK ofLimbs base).rows = (l.rows.map (encRow encodeK ofLimbs base)).toArray := by
  cases base <;> simp [SLevel.prf, encRow]

/-- `AuthenticatedRows` for the script's opening with the committed tables in place of the
presence markers, against the first table, when every opened row is its query's table row. -/
theorem authenticated_withOracles (c : Protocol.Config) (s : Script E Q R K) (lanes : Nat)
    (hS : ScriptShape index c s lanes) (tables : Nat → Protocol.Oracle)
    (hopen : ∀ j (hj : j < s.levels.length) i (hi : i < s.levels[j].rows.length),
      encRow encodeK ofLimbs (j == 0) s.levels[j].rows[i] =
        (tables j)[index (s.levels[j].queries[i]'(by rw [← hS.rows j hj]; exact hi))]!) :
    AuthenticatedRows c (s.chal encode) (withOracles (s.prf encode encodeK ofLimbs) tables) (tables 0) := by
  intro i hi qs hqs j hj
  have hil : i < s.levels.length := by rw [hS.len]; exact hi
  have hq := hS.queries i hil
  rw [chal_get encode s i hil] at hqs
  simp only [SLevel.chal] at hqs
  rw [hqs] at hq
  simp only [Option.map_some, Option.some.injEq] at hq
  have hjq : j < s.levels[i].queries.length := by
    have := congrArg List.length hq; simp at this; omega
  have hjr : j < s.levels[i].rows.length := by rw [hS.rows i hil]; exact hjq
  have hqj : qs[j]! = index s.levels[i].queries[j] := by
    have := congrArg (·[j]?) hq
    simp only [Array.getElem?_toList, List.getElem?_map, List.getElem?_eq_getElem hjq, Option.map_some] at this
    rw [getElem!_pos qs j hj]
    rw [Array.getElem?_eq_getElem hj] at this
    exact Option.some.inj this
  rw [withOracles_level, prf_get encode encodeK ofLimbs s i hil]
  simp only
  rw [prf_rows, hqj]
  have hrow : (s.levels[i].rows.map (encRow encodeK ofLimbs (i == 0))).toArray[j]! =
      encRow encodeK ofLimbs (i == 0) s.levels[i].rows[j] := by
    rw [getElem!_pos _ j (by simp; exact hjr)]; simp
  rw [hrow, hopen i hil j hjr]
  congr 1
  unfold oracleBefore
  by_cases hi0 : i = 0
  · subst hi0; simp
  · rw [if_neg hi0, withOracles_level, prf_get encode encodeK ofLimbs s (i - 1) (by omega)]
    obtain ⟨r, hr⟩ := hS.head (i - 1) (by omega)
    have hr' : s.levels[i - 1].head = .inl r := hr
    simp [SLevel.prf, hr', show i - 1 + 1 = i by omega]

end Rows

end WhirAeneas.Replay
