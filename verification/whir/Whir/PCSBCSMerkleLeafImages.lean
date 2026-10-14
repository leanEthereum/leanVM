import Whir.PCSBCSMerkleQueryLog

/-! Full hashed images and compact source suffixes are different objects.
Missing/malformed images have explicit unavailable status, even though the
book default keeps both numerical tables rectangular. Invalid zero padding
is a local source rejection, never a cryptographic collision. -/
namespace Whir.PCSBCSMerkleLeafImages
open Concrete FiatShamirGame MerkleTransport MerkleTransport.Commitments
open MerkleBinding
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PublicMerkleLog

/-- Allocation-free leading-zero check. -/
def zeroPrefix : Nat → List K → Bool
  | 0, _ => true
  | _+1, [] => false
  | n+1, x::xs => (x == 0) && zeroPrefix n xs

theorem zeroPrefix_replicate (n : Nat) (row : List K) :
    zeroPrefix n (List.replicate n 0 ++ row) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeroPrefix,List.replicate_succ,ih]

structure ImageCell where
  image : Array K
  compact : Array K
  available : Bool
  paddingValid : Bool

/-- Numerical defaults are not marked available or padding-authenticated. -/
def defaultCell (leafWords occupied : Nat) : ImageCell :=
  ⟨Array.replicate leafWords 0,Array.replicate (leafWords-(leafWords-occupied)) 0,false,false⟩

def leafCell (leafWords occupied : Nat) (row : List K)
    (default : ImageCell := defaultCell leafWords occupied) : ImageCell :=
  if row.length = leafWords then
    ⟨row.toArray,(row.drop (leafWords-occupied)).toArray,true,
      decide (occupied ≤ leafWords) && zeroPrefix (leafWords-occupied) row⟩
  else default

theorem leafCell_image (leafWords occupied : Nat) (row : List K) :
    (leafCell leafWords occupied row).image = MerkleQueryLogExtraction.normalize leafWords row := by
  simp only [leafCell,MerkleQueryLogExtraction.normalize]
  split <;> rfl

theorem leafCell_compact (leafWords occupied : Nat) (row : List K) :
    (leafCell leafWords occupied row).compact =
      ((leafCell leafWords occupied row).image.toList.drop (leafWords-occupied)).toArray := by
  simp only [leafCell]
  split
  next => simp
  next => simp [defaultCell,List.drop_replicate]

theorem leafCell_admitted (leafWords occupied : Nat) (row : List K)
    (width : row.length = occupied) (fits : occupied ≤ leafWords) :
    (leafCell leafWords occupied (leafImage 0 leafWords row)).available = true ∧
    (leafCell leafWords occupied (leafImage 0 leafWords row)).paddingValid = true ∧
    (leafCell leafWords occupied (leafImage 0 leafWords row)).compact = row.toArray := by
  have full := leafImage_length (0 : K) leafWords row (width ▸ fits)
  simp only [leafCell,full,↓reduceIte]
  simp [leafImage,width,fits,zeroPrefix_replicate]

def fillCells (default : ImageCell) : Nat → Array ImageCell → Array ImageCell
  | 0, out => out
  | n+1, out => fillCells default n (out.push default)

theorem fillCells_list (default : ImageCell) (n : Nat) (out : Array ImageCell) :
    (fillCells default n out).toList = out.toList ++ List.replicate n default := by
  induction n generalizing out with
  | zero => simp [fillCells]
  | succ n ih => simp only [fillCells,ih,Array.toList_push,List.append_assoc,
      List.replicate_succ,List.singleton_append]

def cellsSpec (leafWords occupied : Nat) : Nat → Tree → List ImageCell
  | 0, .leaf row => [leafCell leafWords occupied row]
  | h+1, .branch l r => cellsSpec leafWords occupied h l ++ cellsSpec leafWords occupied h r
  | h, _ => List.replicate (2^h) (defaultCell leafWords occupied)

def emitCells (leafWords occupied : Nat) : Nat → Tree → Array ImageCell → Array ImageCell
  | 0, .leaf row, out => out.push (leafCell leafWords occupied row)
  | h+1, .branch l r, out => emitCells leafWords occupied h r (emitCells leafWords occupied h l out)
  | h, _, out => fillCells (defaultCell leafWords occupied) (2^h) out

/-- One preindex and one fused hash-tree descent. No per-row log/path scans. -/
def extractCells (codec : Codec) (index : Index) (leafWords occupied : Nat) (default : ImageCell) :
    Nat → Digest32 → Array ImageCell → Array ImageCell
  | 0, root, out => match index[key root]? with
    | none => out.push default
    | some bytes => match codec.leaf bytes with
      | none => out.push default
      | some row => out.push (leafCell leafWords occupied row default)
  | h+1, root, out => match index[key root]? with
    | none => fillCells default (2^(h+1)) out
    | some bytes => match codec.pair bytes with
      | none => fillCells default (2^(h+1)) out
      | some (l,r) => extractCells codec index leafWords occupied default h r
          (extractCells codec index leafWords occupied default h l out)

theorem extractCells_eq_emit (codec : Codec) (index : Index) (leafWords occupied height : Nat)
    (root : Digest32) (out : Array ImageCell) :
    extractCells codec index leafWords occupied (defaultCell leafWords occupied) height root out =
      emitCells leafWords occupied height (extract codec index height root) out := by
  induction height generalizing root out with
  | zero =>
    cases hi : index[key root]? with
    | none => simp [extractCells,extract,hi,emitCells,fillCells]
    | some bytes => cases hl : codec.leaf bytes <;>
        simp [extractCells,extract,hi,hl,emitCells,fillCells]
  | succ h ih =>
    cases hi : index[key root]? with
    | none => simp [extractCells,extract,hi,emitCells]
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp [extractCells,extract,hi,hp,emitCells]
      | some pair => rcases pair with ⟨l,r⟩; simp only [extractCells,extract,hi,hp,emitCells,ih]

theorem emitCells_spec (leafWords occupied height : Nat) (tree : Tree) (out : Array ImageCell) :
    (emitCells leafWords occupied height tree out).toList =
      out.toList ++ cellsSpec leafWords occupied height tree := by
  induction height generalizing tree out with
  | zero => cases tree <;> simp [emitCells,cellsSpec,fillCells_list]
  | succ h ih => cases tree <;> simp only [emitCells,cellsSpec,fillCells_list,ih,List.append_assoc]

theorem cellsSpec_length (leafWords occupied height : Nat) (tree : Tree) :
    (cellsSpec leafWords occupied height tree).length = 2^height := by
  induction height generalizing tree with
  | zero => cases tree <;> simp [cellsSpec]
  | succ h ih => cases tree <;> simp [cellsSpec,ih,pow_succ,Nat.mul_two]

def sourceCells (log : PublicLog) (root : Digest32) (height leafWords occupied : Nat) : Array ImageCell :=
  extractCells canonicalCodec (build (records log)) leafWords occupied
    (defaultCell leafWords occupied) height root #[]

def imageTable (cells : Array ImageCell) : Array (Array K) := cells.map ImageCell.image
def compactTable (cells : Array ImageCell) : Array (Array K) := cells.map ImageCell.compact

theorem sourceCells_spec (log : PublicLog) (root : Digest32) (height leafWords occupied : Nat) :
    (sourceCells log root height leafWords occupied).toList =
      cellsSpec leafWords occupied height (fromPublic log root height) := by
  simp only [sourceCells,extractCells_eq_emit,emitCells_spec,List.nil_append,fromPublic]

theorem sourceCells_size (log : PublicLog) (root : Digest32) (height leafWords occupied : Nat) :
    (sourceCells log root height leafWords occupied).size = 2^height := by
  have h := congrArg List.length (sourceCells_spec log root height leafWords occupied)
  simpa only [Array.length_toList,cellsSpec_length] using h

theorem cellsSpec_images (leafWords occupied height : Nat) (tree : Tree) :
    (cellsSpec leafWords occupied height tree).map ImageCell.image = rowsSpec leafWords height tree := by
  induction height generalizing tree with
  | zero =>
    cases tree with
    | absent => simp [cellsSpec,rowsSpec,defaultCell]
    | branch l r => simp [cellsSpec,rowsSpec,defaultCell]
    | leaf row => simp only [cellsSpec,rowsSpec,List.map_cons,List.map_nil,leafCell_image]
  | succ h ih => cases tree <;> simp [cellsSpec,rowsSpec,defaultCell,ih]

theorem imageTable_eq_full (log : PublicLog) (root : Digest32) (height leafWords occupied : Nat) :
    imageTable (sourceCells log root height leafWords occupied) = rawRoot0 log root height leafWords := by
  apply Array.toList_inj.mp
  simp only [imageTable,Array.toList_map,sourceCells_spec,cellsSpec_images,
    rawRoot0_eq_fullRows,fullRows_spec]

theorem cell_compact_drop (leafWords occupied height : Nat) (tree : Tree) :
    ∀ cell ∈ cellsSpec leafWords occupied height tree,
      cell.compact = (cell.image.toList.drop (leafWords-occupied)).toArray := by
  induction height generalizing tree with
  | zero =>
    cases tree with
    | absent => simp [cellsSpec,defaultCell,List.drop_replicate]
    | branch l r => simp [cellsSpec,defaultCell,List.drop_replicate]
    | leaf row =>
      intro cell member
      simp only [cellsSpec,List.mem_singleton] at member
      subst cell
      exact leafCell_compact leafWords occupied row
  | succ h ih =>
    cases tree with
    | absent => simp [cellsSpec,defaultCell,List.drop_replicate]
    | leaf row => simp [cellsSpec,defaultCell,List.drop_replicate]
    | branch l r =>
      intro cell member
      rcases List.mem_append.mp member with hl | hr
      · exact ih l cell hl
      · exact ih r cell hr

theorem compactTable_eq_drop (log : PublicLog) (root : Digest32) (height leafWords occupied : Nat) :
    compactTable (sourceCells log root height leafWords occupied) =
      (rawRoot0 log root height leafWords).map
        (fun image => (image.toList.drop (leafWords-occupied)).toArray) := by
  rw [← imageTable_eq_full log root height leafWords occupied]
  apply Array.toList_inj.mp
  simp only [compactTable,imageTable,Array.toList_map,List.map_map,sourceCells_spec]
  apply List.map_congr_left
  intro cell member
  exact cell_compact_drop leafWords occupied height (fromPublic log root height) cell member

theorem compactTable_shape (log : PublicLog) (root : Digest32)
    (height leafWords occupied : Nat) (fits : occupied ≤ leafWords) :
    (compactTable (sourceCells log root height leafWords occupied)).size = 2^height ∧
    ∀ row ∈ (compactTable (sourceCells log root height leafWords occupied)).toList,
      row.size = occupied := by
  rw [compactTable_eq_drop]
  have shape := rawRoot0_shape log root height leafWords
  refine ⟨by simpa using shape.1,?_⟩
  intro row member
  simp only [Array.toList_map,List.mem_map] at member
  obtain ⟨image,inside,rfl⟩ := member
  have width := shape.2 image inside
  simp only [List.size_toArray,List.length_drop,Array.length_toList,width]
  omega

private theorem address_top (index h : Nat) (below : List Bool) :
    addressAbove index (h+1) below = right (index/2^h) :: addressAbove index h below := by
  induction h generalizing index below with
  | zero => simp [addressAbove]
  | succ h ih => rw [addressAbove,ih]; simp only [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm]; rfl

private theorem address_mod (index h : Nat) (below : List Bool) :
    addressAbove (index%2^h) h below = addressAbove index h below := by
  induction h generalizing index below with
  | zero => rfl
  | succ h ih =>
    rw [addressAbove,addressAbove]
    have parity : right (index%2^(h+1)) = right index := by
      simp only [right,MerkleLevels.right,pow_succ,Nat.mul_comm (2^h) 2,Nat.mod_mul_right_mod]
    rw [parity,pow_succ,Nat.mod_mul_left_div_self,ih]

def cellAt (leafWords occupied : Nat) (tree : Tree) (address : List Bool) : ImageCell :=
  match tree.get address with
  | none => defaultCell leafWords occupied
  | some row => leafCell leafWords occupied row

theorem cellsSpec_get (leafWords occupied height : Nat) (tree : Tree) (index : Nat)
    (inside : index < 2^height) :
    (cellsSpec leafWords occupied height tree)[index]? =
      some (cellAt leafWords occupied tree (addressAbove index height [])) := by
  induction height generalizing tree index with
  | zero =>
    have eq : index = 0 := by simpa using inside
    subst index
    cases tree <;> simp [cellsSpec,cellAt,Tree.get,addressAbove]
  | succ h ih =>
    have full : index < 2^h*2 := by simpa [pow_succ] using inside
    rw [address_top]
    cases tree with
    | absent => simp [cellsSpec,cellAt,Tree.get,inside]
    | leaf row => simp [cellsSpec,cellAt,Tree.get,inside]
    | branch l r =>
      by_cases lower : index < 2^h
      · have hd : index/2^h = 0 := Nat.div_eq_of_lt lower
        simp only [cellsSpec,cellAt,Tree.get,hd,right,MerkleLevels.right,Nat.reduceMod,Nat.reduceBEq]
        rw [List.getElem?_append_left (by simpa [cellsSpec_length] using lower)]
        exact ih l index lower
      · have upper : index-2^h < 2^h := by omega
        have hd : index/2^h = 1 := Nat.div_eq_of_lt_le (by simpa using Nat.le_of_not_gt lower)
          (by simpa [Nat.mul_comm] using full)
        have hm : index%2^h = index-2^h := by
          rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt lower),Nat.mod_eq_of_lt upper]
        have ha : addressAbove index h [] = addressAbove (index-2^h) h [] := by
          rw [← hm]; exact (address_mod index h []).symm
        simp only [cellsSpec,cellAt,Tree.get,hd,right,MerkleLevels.right,Nat.reduceMod,Nat.reduceBEq,↓reduceIte]
        rw [List.getElem?_append_right (by simpa [cellsSpec_length] using Nat.le_of_not_gt lower)]
        rw [cellsSpec_length,ha]
        exact ih r (index-2^h) upper

theorem sourceCells_get (log : PublicLog) (root : Digest32) (height leafWords occupied index : Nat)
    (inside : index < 2^height) :
    (sourceCells log root height leafWords occupied)[index]? =
      some (cellAt leafWords occupied (fromPublic log root height) (addressAbove index height [])) := by
  rw [← Array.getElem?_toList,sourceCells_spec]
  exact cellsSpec_get leafWords occupied height _ index inside

end Whir.PCSBCSMerkleLeafImages
