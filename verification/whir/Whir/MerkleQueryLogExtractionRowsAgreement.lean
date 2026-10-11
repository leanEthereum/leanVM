import Whir.MerkleQueryLogExtractionRows

/-! The emitted table is in ascending physical leaf-index order. This is a
checked agreement with the existing ideal full Snapshot table, not a different
address enumeration convention. -/
namespace Whir.MerkleQueryLogExtraction
open Concrete FiatShamirGame MerkleTransport MerkleTransport.Commitments

private theorem address_top (index h : Nat) (below : List Bool) :
    addressAbove index (h+1) below =
      right (index / 2^h) :: addressAbove index h below := by
  induction h generalizing index below with
  | zero => simp [addressAbove]
  | succ h ih =>
    rw [addressAbove,ih]
    simp only [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm]
    rfl

private theorem address_mod (index h : Nat) (below : List Bool) :
    addressAbove (index % 2^h) h below = addressAbove index h below := by
  induction h generalizing index below with
  | zero => rfl
  | succ h ih =>
    rw [addressAbove,addressAbove]
    have parity : right (index % 2^(h+1)) = right index := by
      simp only [right,MerkleLevels.right,pow_succ,Nat.mul_comm (2^h) 2,
        Nat.mod_mul_right_mod]
    rw [parity]
    rw [pow_succ,Nat.mod_mul_left_div_self,ih]

private theorem normalize_default (width : Nat) :
    normalize width (List.replicate width 0) = Array.replicate width 0 := by
  simp [normalize]

/-- Optional indexing avoids invented rows outside the full fixed tree. -/
theorem rowsSpec_get (width height : Nat) (tree : Tree) (index : Nat)
    (inside : index < 2^height) :
    (rowsSpec width height tree)[index]? =
      some (normalize width (tree.row (List.replicate width 0) (addressAbove index height []))) := by
  induction height generalizing tree index with
  | zero =>
    have eq : index = 0 := by simpa using inside
    subst index
    cases tree <;> simp [rowsSpec,Tree.row,Tree.get,addressAbove,normalize_default]
  | succ h ih =>
    have pos : 0 < 2^h := by positivity
    have full : index < 2^h*2 := by simpa [pow_succ] using inside
    rw [address_top]
    cases tree with
    | absent => simp [rowsSpec,Tree.row,Tree.get,inside,normalize_default]
    | leaf row => simp [rowsSpec,Tree.row,Tree.get,inside,normalize_default]
    | branch l r =>
      by_cases lower : index < 2^h
      · have hd : index / 2^h = 0 := Nat.div_eq_of_lt lower
        simp only [rowsSpec,Tree.row,Tree.get,hd,right,MerkleLevels.right,
          Nat.reduceMod,Nat.reduceBEq]
        rw [List.getElem?_append_left (by simpa [rowsSpec_length] using lower)]
        exact ih l index lower
      · have upper : index-2^h < 2^h := by omega
        have hd : index / 2^h = 1 :=
          Nat.div_eq_of_lt_le (by simpa using Nat.le_of_not_gt lower)
            (by simpa [Nat.mul_comm] using full)
        have hm : index % 2^h = index-2^h := by
          rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt lower),Nat.mod_eq_of_lt upper]
        have ha : addressAbove index h [] = addressAbove (index-2^h) h [] := by
          rw [← hm]
          exact (address_mod index h []).symm
        simp only [rowsSpec,Tree.row,Tree.get,hd,right,MerkleLevels.right,
          Nat.reduceMod,Nat.reduceBEq,↓reduceIte]
        rw [List.getElem?_append_right (by simpa [rowsSpec_length] using Nat.le_of_not_gt lower)]
        rw [rowsSpec_length,ha]
        exact ih r (index-2^h) upper

theorem fullRows_get (width height : Nat) (tree : Tree) (index : Nat)
    (inside : index < 2^height) :
    (fullRows width height tree)[index]? =
      some (normalize width (tree.row (List.replicate width 0) (addressAbove index height []))) := by
  rw [← Array.getElem?_toList,fullRows_spec]
  exact rowsSpec_get width height tree index inside

/-- A zero-default Snapshot agrees at EVERY index, including absent paths and
malformed-width paths. No availability assumption is present. -/
theorem fullRows_eq_snapshot (codec : Codec) (hash : Primitive) (records : Records)
    (auth : Authentic hash records)
    (clean : ¬ MerkleBinding.Collision (hashing hash) (recordDomain records))
    (root : Digest32) (height width : Nat) :
    fullRows width height (extract codec (build records) height root) =
      baseOracle hash ⟨recordDomain records,List.replicate width 0⟩ root height (2^height) width := by
  apply Array.ext
  · simp [fullRows_size,baseOracle_size]
  · intro index left right
    have inside : index < 2^height := by simpa only [fullRows_size] using left
    have hg := fullRows_get width height (extract codec (build records) height root) index inside
    have he := extract_eq_ideal codec hash records auth clean root (List.replicate width 0)
      (addressAbove index height [])
    rw [addressAbove_length] at he
    simp only [List.length_nil,Nat.add_zero] at he
    have hn : normalize width
        ((extract codec (build records) height root).row (List.replicate width 0)
          (addressAbove index height [])) =
        (baseRow hash ⟨recordDomain records,List.replicate width 0⟩ root height index width).toArray := by
      rw [he]
      unfold normalize baseRow row oracle
      split <;> simp_all
    rw [hn] at hg
    have hl := Option.some.inj ((Array.getElem?_eq_getElem left).symm.trans hg)
    simpa only [baseOracle,Array.getElem_ofFn] using hl

private theorem baseRow_empty_default (hash : Primitive) (table : Finset (List Byte))
    (root : Digest32) (height index width : Nat) :
    baseRow hash ⟨table,List.replicate width 0⟩ root height index width =
      baseRow hash ⟨table,[]⟩ root height index width := by
  classical
  by_cases recorded : ∃ path : MerkleBinding.Opening (List K) Digest32
      (addressAbove index height []),
      path.inputs (hashing hash) ⊆ table ∧ path.digest (hashing hash) = root
  · simp only [baseRow,row,oracle,MerkleBinding.idealRow,dite_eq_left recorded]
  · cases width <;> simp [baseRow,row,oracle,MerkleBinding.idealRow,recorded]

/-- The existing registry's empty book-default convention gives the same
shape-normalized full table, including absent leaves. -/
theorem fullRows_eq_empty_snapshot (codec : Codec) (hash : Primitive) (records : Records)
    (auth : Authentic hash records)
    (clean : ¬ MerkleBinding.Collision (hashing hash) (recordDomain records))
    (root : Digest32) (height width : Nat) :
    fullRows width height (extract codec (build records) height root) =
      baseOracle hash ⟨recordDomain records,[]⟩ root height (2^height) width := by
  rw [fullRows_eq_snapshot codec hash records auth clean root height width]
  simp only [baseOracle,baseRow_empty_default]

end Whir.MerkleQueryLogExtraction
