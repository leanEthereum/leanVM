import Whir.PublicMerkleBinding
import Std.Data.ExtHashMap.Lemmas

/-! Deterministic extraction from exposed input/answer records. The runtime
never evaluates a hash oracle. Depth is retained even when leaf and pair bytes
coincide. Absence and malformed preimages are data, not witness defaults. -/
namespace Whir.MerkleQueryLogExtraction
open Concrete FiatShamirGame MerkleBinding MerkleTransport
open MerkleTransport.Commitments

abbrev Key := List Byte
abbrev Index := Std.ExtHashMap Key (List Byte)
def key (d : Digest32) : Key := List.ofFn d

theorem key_injective : Function.Injective key := List.ofFn_injective

/-- Final index retains the earliest record for each output. Each record is
indexed once; tree descent does not scan the records. -/
def build : Records → Index
  | [] => ∅
  | (bytes,d) :: rest => (build rest).insert (key d) bytes

/-- Online registration does not replace an already cached preimage. -/
def register (index : Index) (bytes : List Byte) (d : Digest32) : Index :=
  index.insertIfNew (key d) bytes

theorem register_preserves (index : Index) (bytes old : List Byte) (d target : Digest32)
    (known : index[key target]? = some old) :
    (register index bytes d)[key target]? = some old := by
  rw [register, Std.ExtHashMap.getElem?_insertIfNew]
  split
  next h =>
    have eq : key d = key target := by simpa using h.1
    have mem : key d ∈ index := by
      rw [eq, Std.ExtHashMap.mem_iff_isSome_getElem?, known]; rfl
    exact (h.2 mem).elim
  next => exact known

def inverseLookup (d : Digest32) : Records → Option (List Byte)
  | [] => none
  | (bytes,e) :: rest => if key e = key d then some bytes else inverseLookup d rest

theorem build_lookup (records : Records) (d : Digest32) :
    (build records)[key d]? = inverseLookup d records := by
  induction records with
  | nil => simp [build, inverseLookup]
  | cons e rest ih =>
    rcases e with ⟨bytes,e⟩
    simp [build, inverseLookup, Std.ExtHashMap.getElem?_insert, ih]

theorem inverseLookup_mem {records : Records} {d : Digest32} {bytes : List Byte}
    (hit : inverseLookup d records = some bytes) : (bytes,d) ∈ records := by
  induction records with
  | nil => simp [inverseLookup] at hit
  | cons e rest ih =>
    rcases e with ⟨bs,e⟩
    simp only [inverseLookup] at hit
    split at hit
    next eq =>
      have ed := key_injective eq
      cases ed
      cases Option.some.inj hit
      exact List.mem_cons_self
    next => exact List.mem_cons_of_mem _ (ih hit)

theorem build_mem {records : Records} {d : Digest32} {bytes : List Byte}
    (hit : (build records)[key d]? = some bytes) : (bytes,d) ∈ records :=
  inverseLookup_mem (by simpa only [build_lookup] using hit)

theorem build_complete {records : Records} {d : Digest32} {bytes : List Byte}
    (member : (bytes,d) ∈ records) : ∃ selected, (build records)[key d]? = some selected := by
  rw [build_lookup]
  induction records with
  | nil => cases member
  | cons e rest ih =>
    rcases e with ⟨bs,e⟩
    by_cases eq : key e = key d
    · exact ⟨bs, by simp [inverseLookup,eq]⟩
    · have mem : (bytes,d) ∈ rest := by
        rcases List.mem_cons.mp member with he | he
        · cases he; exact (eq rfl).elim
        · exact he
      obtain ⟨selected,hs⟩ := ih mem
      exact ⟨selected,by simp [inverseLookup,eq,hs]⟩

/-- Codec obligations, not cryptographic assumptions. A decoder must reject
malformed byte strings and be a left inverse on every canonical preimage. -/
structure Codec where
  leaf : List Byte → Option (List K)
  pair : List Byte → Option (Digest32 × Digest32)
  leaf_sound : ∀ bytes row, leaf bytes = some row → ByteCodec.wordsBytes row = bytes
  leaf_complete : ∀ row, leaf (ByteCodec.wordsBytes row) = some row
  pair_sound : ∀ bytes p, pair bytes = some p → List.ofFn (ByteCodec.pairBytes p) = bytes
  pair_complete : ∀ p, pair (List.ofFn (ByteCodec.pairBytes p)) = some p

/-- A subtree may be absent without making other occupied rows unavailable.
The leaf case is distinguished from the branch case by requested height. -/
inductive Tree where
  | absent
  | leaf (row : List K)
  | branch (left right : Tree)

def extract (codec : Codec) (index : Index) : Nat → Digest32 → Tree
  | 0, d => match index[key d]? with
    | none => .absent
    | some bytes => match codec.leaf bytes with
      | none => .absent
      | some row => .leaf row
  | height + 1, d => match index[key d]? with
    | none => .absent
    | some bytes => match codec.pair bytes with
      | none => .absent
      | some (l,r) => .branch (extract codec index height l) (extract codec index height r)

def Tree.get : Tree → List Bool → Option (List K)
  | .leaf row, [] => some row
  | .branch l r, b :: address => (if b then r else l).get address
  | _, _ => none

/-- Book default is applied only at the consumer boundary, and is visibly
marked by `get = none`. It is not an authenticated witness. -/
def Tree.row (tree : Tree) (fallback : List K) (address : List Bool) : List K :=
  (tree.get address).getD fallback

theorem domain_mem {records : Records} {bytes : List Byte} {d : Digest32}
    (hm : (bytes,d) ∈ records) : bytes ∈ recordDomain records :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨(bytes,d),hm,rfl⟩)

theorem selected_unique (hash : Primitive) (records : Records)
    (auth : Authentic hash records) (clean : ¬ Collision (hashing hash) (recordDomain records))
    {bytes : List Byte} {d : Digest32} (hm : (bytes,d) ∈ records) :
    (build records)[key d]? = some bytes := by
  obtain ⟨selected,hit⟩ := build_complete hm
  have hs := build_mem hit
  have eq : selected = bytes := by
    by_contra hn
    exact clean ⟨selected,domain_mem hs,bytes,domain_mem hm,hn,
      (auth _ _ hs).trans (auth _ _ hm).symm⟩
  simpa only [eq] using hit

/-- Extraction succeeds on a recorded authenticated path outside the literal
collision event. No log-completeness premise is used: this is about the exact
finite domain, and unrecorded opening inputs are charged separately. -/
theorem extract_complete (codec : Codec) (hash : Primitive) (records : Records)
    (auth : Authentic hash records) (clean : ¬ Collision (hashing hash) (recordDomain records))
    {address : List Bool} (path : Opening (List K) Digest32 address)
    (covered : path.inputs (hashing hash) ⊆ recordDomain records) :
    (extract codec (build records) address.length (path.digest (hashing hash))).get address =
      some path.row := by
  induction path with
  | leaf row =>
    have mem : ByteCodec.wordsBytes row ∈ recordDomain records :=
      covered (Finset.mem_singleton_self _)
    obtain ⟨d,hd⟩ := recordLookup_exists records _ mem
    have hm := recordLookup_mem _ _ _ hd
    have he := auth _ _ hm
    have hit := selected_unique hash records auth clean hm
    change hash (ByteCodec.wordsBytes row) = d at he
    change (extract codec (build records) 0 (hash (ByteCodec.wordsBytes row))).get [] = some row
    rw [he]
    simp only [extract,hit,codec.leaf_complete,Tree.get]
  | node b sibling child ih =>
    have cc : child.inputs (hashing hash) ⊆ recordDomain records :=
      fun x hx => covered (Finset.mem_insert_of_mem hx)
    let pair := if b then (sibling,child.digest (hashing hash)) else (child.digest (hashing hash),sibling)
    have cp : List.ofFn (ByteCodec.pairBytes pair) ∈ recordDomain records :=
      covered (Finset.mem_insert_self _ _)
    obtain ⟨d,hd⟩ := recordLookup_exists records _ cp
    have hm := recordLookup_mem _ _ _ hd
    have he := auth _ _ hm
    have hit := selected_unique hash records auth clean hm
    change hash (List.ofFn (ByteCodec.pairBytes pair)) = d at he
    have hc := ih cc
    change (extract codec (build records) (_ + 1)
      (hash (List.ofFn (ByteCodec.pairBytes pair)))).get (b :: _) = _
    rw [he]
    simp only [extract,hit,codec.pair_complete]
    cases b <;> exact hc

/-- Every successful extraction supplies a genuinely recorded authenticated
path. Failed parsing is never disguised as a witness. -/
theorem extract_sound (codec : Codec) (hash : Primitive) (records : Records)
    (auth : Authentic hash records) (address : List Bool) (d : Digest32) (row : List K)
    (hit : (extract codec (build records) address.length d).get address = some row) :
    ∃ path : Opening (List K) Digest32 address,
      path.row = row ∧ path.inputs (hashing hash) ⊆ recordDomain records ∧
      path.digest (hashing hash) = d := by
  induction address generalizing d with
  | nil =>
    cases hi : (build records)[key d]? with
    | none => simp [extract,hi,Tree.get] at hit
    | some bytes =>
      cases hl : codec.leaf bytes with
      | none => simp [extract,hi,hl,Tree.get] at hit
      | some selected =>
        have eq : selected = row := by simpa [extract,hi,hl,Tree.get] using hit
        subst selected
        have hb := codec.leaf_sound bytes row hl
        have hm := build_mem hi
        refine ⟨.leaf row,rfl,?_,?_⟩
        · simpa [Opening.inputs,hashing,hb] using domain_mem hm
        · simpa [Opening.digest,hashing,hb] using auth _ _ hm
  | cons b address ih =>
    cases hi : (build records)[key d]? with
    | none => simp [extract,hi,Tree.get] at hit
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp [extract,hi,hp,Tree.get] at hit
      | some pair =>
        rcases pair with ⟨l,r⟩
        have hb := codec.pair_sound bytes (l,r) hp
        have hm := build_mem hi
        cases b
        · obtain ⟨child,hrow,hcovered,hd⟩ := ih l (by simpa [extract,hi,hp,Tree.get] using hit)
          refine ⟨.node false r child,hrow,?_,?_⟩
          · simp only [Opening.inputs, Bool.false_eq_true, ↓reduceIte, hd]
            change insert (List.ofFn (ByteCodec.pairBytes (l,r)))
              (child.inputs (hashing hash)) ⊆ recordDomain records
            rw [hb]
            exact Finset.insert_subset (domain_mem hm) hcovered
          · simp only [Opening.digest, Bool.false_eq_true, ↓reduceIte, hd]
            change hash (List.ofFn (ByteCodec.pairBytes (l,r))) = d
            rw [hb]
            exact auth _ _ hm
        · obtain ⟨child,hrow,hcovered,hd⟩ := ih r (by simpa [extract,hi,hp,Tree.get] using hit)
          refine ⟨.node true l child,hrow,?_,?_⟩
          · simp only [Opening.inputs, ↓reduceIte, hd]
            change insert (List.ofFn (ByteCodec.pairBytes (l,r)))
              (child.inputs (hashing hash)) ⊆ recordDomain records
            rw [hb]
            exact Finset.insert_subset (domain_mem hm) hcovered
          · simp only [Opening.digest, ↓reduceIte, hd]
            change hash (List.ofFn (ByteCodec.pairBytes (l,r))) = d
            rw [hb]
            exact auth _ _ hm

theorem extract_eq_ideal (codec : Codec) (hash : Primitive) (records : Records)
    (auth : Authentic hash records) (clean : ¬ Collision (hashing hash) (recordDomain records))
    (root : Digest32) (fallback : List K) (address : List Bool) :
    (extract codec (build records) address.length root).row fallback address =
      idealRow (hashing hash) (recordDomain records) root fallback address := by
  classical
  by_cases hex : ∃ path : Opening (List K) Digest32 address,
      path.inputs (hashing hash) ⊆ recordDomain records ∧ path.digest (hashing hash) = root
  · have hit := extract_complete codec hash records auth clean hex.choose hex.choose_spec.1
    rw [hex.choose_spec.2] at hit
    simp only [Tree.row,hit,Option.getD_some,idealRow,dite_eq_left hex]
  · have absent : (extract codec (build records) address.length root).get address = none := by
      cases hit : (extract codec (build records) address.length root).get address with
      | none => rfl
      | some row =>
        obtain ⟨path,_,hc,hd⟩ := extract_sound codec hash records auth address root row hit
        exact (hex ⟨path,hc,hd⟩).elim
    simp only [Tree.row,absent,Option.getD_none,idealRow,dite_eq_right hex]

end Whir.MerkleQueryLogExtraction
