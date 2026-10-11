import Whir.PCSBCSMerkleRootCache
import Whir.CausalGame
import Whir.WHIRCallerGeometry

/-! The semantic oracle is the frozen suffix in its original wire lane order.
Initial base rows use the existing liftRoot. Extension rows decode consecutive
three-word E images without serializing and reparsing a temporary byte array. -/
set_option autoImplicit false
namespace Whir.PCSBCSFrozenOracleRows
open Concrete Protocol CausalGame

/-- Malformed extension images reject rather than dropping their last limbs. -/
def extensionRow (words : Array K) : Option (Array E) :=
  if words.size % 3 = 0 then
    some (Array.ofFn fun i : Fin (words.size / 3) =>
      ⟨words[3*i.val]!,words[3*i.val+1]!,words[3*i.val+2]!⟩)
  else none

def extensionOracle (raw : Array (Array K)) : Option Oracle :=
  raw.mapM extensionRow

/-- The source phase determines the representation; the proof does not choose
whether the same bytes are read as base or extension elements. -/
def frozenOracle (phase : Nat) (frozen : PCSBCSMerkleRootCache.Frozen) : Option Oracle :=
  if phase = 0 then some (liftRoot frozen.raw) else extensionOracle frozen.raw

/-- A query reply contains ONLY rows in derived-query order, not the full tree.
Checked lookup rejects out-of-range positions in the same traversal. -/
def queryRows (oracle : Oracle) (queries : Array Nat) : Option Oracle :=
  queries.mapM (fun q => oracle[q]?)

theorem queryRows_spec (oracle rows : Oracle) (queries : Array Nat)
    (selected : queryRows oracle queries = some rows) :
    rows.size = queries.size ∧
      ∀ i : Fin queries.size, rows[i.val]! = oracle[queries[i]]! := by
  unfold queryRows at selected
  rw [Array.mapM_eq_mapM_toList] at selected
  cases traversed : queries.toList.mapM (fun q => oracle[q]?) with
  | none => simp [traversed] at selected
  | some ys =>
    simp only [traversed,Functor.map,Option.map,Option.some.injEq] at selected
    subst rows
    have related := WHIRCallerGeometry.option_mapM_rel (fun q => oracle[q]?)
      queries.toList ys traversed
    have length : ys.length = queries.size := by simpa using related.length_eq.symm
    constructor
    · simpa
    · intro i
      have outputBound : i.val < ys.length := by simp [length,i.isLt]
      have matched : oracle[queries[i]]? = some ys[i.val] := by
        simpa using related.get (i := i.val) (by simp [i.isLt]) outputBound
      obtain ⟨inside,same⟩ := Array.getElem?_eq_some_iff.mp matched
      rw [getElem!_pos oracle (queries[i]) inside]
      simpa [getElem!_pos,outputBound] using same.symm

theorem extensionRow_size (words : Array K) (row : Array E)
    (decoded : extensionRow words = some row) :
    words.size % 3 = 0 ∧ row.size = words.size / 3 := by
  unfold extensionRow at decoded
  split at decoded
  next valid =>
    have same := Option.some.inj decoded
    subst row
    exact ⟨valid,by simp⟩
  next => contradiction

theorem extensionRow_limb (words : Array K) (row : Array E)
    (decoded : extensionRow words = some row) (i : Fin row.size) :
    row[i].c0 = words[3*i.val]! ∧ row[i].c1 = words[3*i.val+1]! ∧
      row[i].c2 = words[3*i.val+2]! := by
  unfold extensionRow at decoded
  split at decoded
  next valid =>
    cases Option.some.inj decoded
    simp
  next => contradiction

#print axioms extensionRow_size
#print axioms extensionRow_limb
end Whir.PCSBCSFrozenOracleRows

#print axioms Whir.PCSBCSFrozenOracleRows.queryRows_spec
