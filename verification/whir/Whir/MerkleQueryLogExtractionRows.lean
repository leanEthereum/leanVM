import Whir.MerkleQueryLogExtractionCodec

/-! Full fixed-height row materialization. The extractor traverses the tree
once and uses a single mutable array accumulator. Shape defaults remain marked
by the extracted tree's absence/width branch; they are not witness fallbacks.
Initial Merkle/decoder rows are RAW. Coefficient/fold order is separate. -/
namespace Whir.MerkleQueryLogExtraction
open Concrete FiatShamirGame MerkleTransport

def normalize (width : Nat) (row : List K) : Array K :=
  if row.length = width then row.toArray else Array.replicate width 0

theorem normalize_size (width : Nat) (row : List K) : (normalize width row).size = width := by
  simp only [normalize]
  split <;> simp_all

def fill (default : Array K) : Nat → Array (Array K) → Array (Array K)
  | 0, out => out
  | n+1, out => fill default n (out.push default)

theorem fill_list (default : Array K) (n : Nat) (out : Array (Array K)) :
    (fill default n out).toList = out.toList ++ List.replicate n default := by
  induction n generalizing out with
  | zero => simp [fill]
  | succ n ih =>
    simp only [fill,ih,Array.toList_push,List.append_assoc,List.replicate_succ,
      List.singleton_append]

/-- Specification only. The executable accumulator does not construct or
concatenate this list. -/
def rowsSpec (width : Nat) : Nat → Tree → List (Array K)
  | 0, .leaf row => [normalize width row]
  | h+1, .branch l r => rowsSpec width h l ++ rowsSpec width h r
  | h, _ => List.replicate (2^h) (Array.replicate width 0)

def emit (width : Nat) (default : Array K) : Nat → Tree → Array (Array K) → Array (Array K)
  | 0, .leaf row, out => out.push (if row.length = width then row.toArray else default)
  | h+1, .branch l r, out => emit width default h r (emit width default h l out)
  | h, _, out => fill default (2^h) out

def fullRows (width height : Nat) (tree : Tree) : Array (Array K) :=
  emit width (Array.replicate width 0) height tree #[]

/-- Production full-row extraction fuses preimage descent and emission.
No intermediate tree or per-row root-to-leaf path is allocated. -/
def extractRows (codec : Codec) (index : Index) (width : Nat) (default : Array K) :
    Nat → Digest32 → Array (Array K) → Array (Array K)
  | 0, root, out => match index[key root]? with
    | none => out.push default
    | some bytes => match codec.leaf bytes with
      | none => out.push default
      | some row => out.push (if row.length = width then row.toArray else default)
  | h+1, root, out => match index[key root]? with
    | none => fill default (2^(h+1)) out
    | some bytes => match codec.pair bytes with
      | none => fill default (2^(h+1)) out
      | some (l,r) => extractRows codec index width default h r
        (extractRows codec index width default h l out)

theorem extractRows_eq_emit (codec : Codec) (index : Index) (width : Nat) (default : Array K)
    (height : Nat) (root : Digest32) (out : Array (Array K)) :
    extractRows codec index width default height root out =
      emit width default height (extract codec index height root) out := by
  induction height generalizing root out with
  | zero =>
    cases hi : index[key root]? with
    | none => simp [extractRows,extract,hi,emit,fill]
    | some bytes =>
      cases hl : codec.leaf bytes <;> simp [extractRows,extract,hi,hl,emit,fill]
  | succ h ih =>
    cases hi : index[key root]? with
    | none => simp [extractRows,extract,hi,emit]
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp [extractRows,extract,hi,hp,emit]
      | some pair =>
        rcases pair with ⟨l,r⟩
        simp only [extractRows,extract,hi,hp,emit,ih]

theorem emit_spec (width height : Nat) (tree : Tree) (out : Array (Array K)) :
    (emit width (Array.replicate width 0) height tree out).toList =
      out.toList ++ rowsSpec width height tree := by
  induction height generalizing tree out with
  | zero => cases tree <;> simp [emit,rowsSpec,fill_list,normalize]
  | succ h ih =>
    cases tree <;> simp only [emit,rowsSpec,fill_list,ih,List.append_assoc]

theorem fullRows_spec (width height : Nat) (tree : Tree) :
    (fullRows width height tree).toList = rowsSpec width height tree := by
  simpa [fullRows] using emit_spec width height tree #[]

theorem rowsSpec_length (width height : Nat) (tree : Tree) :
    (rowsSpec width height tree).length = 2^height := by
  induction height generalizing tree with
  | zero => cases tree <;> simp [rowsSpec]
  | succ h ih => cases tree <;> simp [rowsSpec,ih,pow_succ,Nat.mul_two]

theorem fullRows_size (width height : Nat) (tree : Tree) :
    (fullRows width height tree).size = 2^height := by
  have length := congrArg List.length (fullRows_spec width height tree)
  simpa only [Array.length_toList,rowsSpec_length] using length

theorem rowsSpec_width (width height : Nat) (tree : Tree) :
    ∀ row ∈ rowsSpec width height tree, row.size = width := by
  induction height generalizing tree with
  | zero => cases tree <;> simp [rowsSpec,normalize_size]
  | succ h ih =>
    cases tree with
    | absent => simp [rowsSpec]
    | leaf row => simp [rowsSpec]
    | branch l r =>
      intro row hm
      rcases List.mem_append.mp hm with hl | hr
      · exact ih l row hl
      · exact ih r row hr

theorem fullRows_width (width height : Nat) (tree : Tree) :
    ∀ row ∈ (fullRows width height tree).toList, row.size = width := by
  rw [fullRows_spec]
  exact rowsSpec_width width height tree

/-- Coefficient-ascending order, NOT the decoder input. The decoder accepts
raw occupied leaves and its receivedLane/fullRow apply the reversal internally. -/
def root0CoefficientOrder (raw : Array (Array K)) : Array (Array K) := raw.map Array.reverse

theorem root0CoefficientOrder_size (raw : Array (Array K)) :
    (root0CoefficientOrder raw).size = raw.size := by simp [root0CoefficientOrder]

theorem root0CoefficientOrder_width (occupied : Nat) (raw : Array (Array K))
    (shape : ∀ row ∈ raw.toList, row.size = occupied) :
    ∀ row ∈ (root0CoefficientOrder raw).toList, row.size = occupied := by
  intro row hm
  simp only [root0CoefficientOrder,Array.toList_map,List.mem_map] at hm
  obtain ⟨source,hs,rfl⟩ := hm
  simpa using shape source hs

theorem root0CoefficientOrder_raw (raw : Array (Array K)) (index : Nat) (bound : index < raw.size) :
    (root0CoefficientOrder raw)[index]'(by simpa [root0CoefficientOrder_size] using bound) =
      raw[index].reverse := by
  simp [root0CoefficientOrder]

theorem root0CoefficientOrder_involutive (raw : Array (Array K)) :
    root0CoefficientOrder (root0CoefficientOrder raw) = raw := by
  simp [root0CoefficientOrder,Array.map_map,Function.comp_def]

/-- Separate first-fold boundary, NOT the compact decoder input: reverse
occupied raw lanes then append virtual zero lanes. Never use this operation on
an already-normalized logical Snapshot. -/
def root0Consumer (occupied padded : Nat) (raw : Array (Array K)) : Array (Array K) :=
  raw.map fun row => row.reverse ++ Array.replicate (padded-occupied) 0

theorem root0Consumer_size (occupied padded : Nat) (raw : Array (Array K)) :
    (root0Consumer occupied padded raw).size = raw.size := by simp [root0Consumer]

theorem root0Consumer_width (occupied padded : Nat) (fits : occupied ≤ padded)
    (raw : Array (Array K)) (shape : ∀ row ∈ raw.toList, row.size = occupied) :
    ∀ row ∈ (root0Consumer occupied padded raw).toList, row.size = padded := by
  intro row hm
  simp only [root0Consumer,Array.toList_map,List.mem_map] at hm
  obtain ⟨source,hs,rfl⟩ := hm
  simp only [Array.size_append,Array.size_reverse,Array.size_replicate,shape source hs]
  omega

theorem root0Consumer_raw (occupied padded : Nat) (raw : Array (Array K))
    (index : Nat) (bound : index < raw.size) :
    (root0Consumer occupied padded raw)[index]'(by simpa [root0Consumer_size] using bound) =
      raw[index].reverse ++ Array.replicate (padded-occupied) 0 := by
  simp [root0Consumer]

end Whir.MerkleQueryLogExtraction
