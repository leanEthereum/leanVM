module

public import Statement.LeanVm
public import LeanVM.Protocol.Extraction.Fast.Extract
public import LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The extractor's lookups, indexed

The statement's Merkle inversion reads the answered pairs through `preimage pairs d len`, a scan of
all pairs per node, and the pairs come from `answerPairs answers keys`, one call of `answers` per
key; in the random-permutation model `answers` is `lookupEvaluation P`, a scan of the paths `P`.
For `N` paths of up to `L` bytes that is `N²·L` for the pairs and `N` per node. Here:

* `firstAnswers P`: a sorted map (`SortedMap`) from each key to its first answer, so
  `answerPairs (lookupEvaluation P) keys = answerPairs ((firstAnswers P).get?) keys`
  (`answerPairs_firstAnswers`);
* `preimageIndex pairs`: a sorted map from `(digest, length)` to what the pairs with that digest and
  length answer (`Hits`: nothing, one byte string, or several), so
  `preimageIn (preimageIndex pairs) d len = preimage pairs d len` (`preimageIn_preimageIndex`);
* `extractWith mk lookup`: `extractFast` with the Merkle inversion reading the preimages through
  `lookup (mk width)`, an index built once from the leaves' width;
  `extractWith (fun _ ↦ pairs…) preimage = extractFast` (`extractWith_preimage`), and the result
  depends on the lookup only at the lengths `64` and `8·width` (`extractWith_congr`).
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash LeanVM.Extraction

public section

attribute [local instance] lexOrd

/-! ## First answers -/

/-- `m` with `v` at `k`, unless `m` has a value at `k`. -/
@[expose] def insertIfNew {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] (m : SortedMap α β) (k : α) (v : β) :
    SortedMap α β :=
  if m.contains k then m else m.insert k v

/-- The first answer of each key among the pairs `P`. -/
@[expose] def firstAnswers (P : List (Bytes × Digest)) : SortedMap Bytes Digest :=
  P.foldl (fun m p ↦ insertIfNew m p.1 p.2) .empty

private theorem foldl_insertIfNew (P : List (Bytes × Digest)) (m : SortedMap Bytes Digest)
    (x : Bytes) :
    (P.foldl (fun m p ↦ insertIfNew m p.1 p.2) m).get? x = (m.get? x).or (lookupEvaluation P x) := by
  induction P generalizing m with
  | nil => simp [lookupEvaluation]
  | cons p P ih =>
    rw [List.foldl_cons, ih, insertIfNew]
    by_cases hm : m.contains p.1 = true
    · simp only [hm, ↓reduceIte]
      by_cases hx : p.1 = x
      · subst hx
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hm
        simp [hv]
      · simp [hx, lookupEvaluation]
    · simp only [hm, Bool.false_eq_true, ↓reduceIte, SortedMap.get?_insert]
      by_cases hx : p.1 = x
      · subst hx
        have hn : m.get? p.1 = none := by simpa [SortedMap.contains] using hm
        simp [hn, lookupEvaluation]
      · simp [hx, lookupEvaluation]

theorem firstAnswers_get? (P : List (Bytes × Digest)) (x : Bytes) :
    (firstAnswers P).get? x = lookupEvaluation P x := by
  rw [firstAnswers, foldl_insertIfNew, SortedMap.get?_empty, Option.none_or]

theorem answerPairs_firstAnswers (P : List (Bytes × Digest)) (keys : List Bytes) :
    answerPairs (firstAnswers P).get? keys = answerPairs (lookupEvaluation P) keys := by
  rw [funext (firstAnswers_get? P)]

/-! ## The preimage index -/

/-- What the pairs with one digest and one length answer: no byte string, one, or several. -/
inductive Hits where
  | none
  | one (x : Bytes)
  | many
  deriving DecidableEq

/-- The answer of two sets of pairs together. -/
@[expose] def Hits.merge : Hits → Hits → Hits
  | .none, h => h
  | h, .none => h
  | .one x, .one y => if x = y then .one x else .many
  | _, _ => .many

/-- The byte string answered, if exactly one is. -/
@[expose] def Hits.toOption : Hits → Option Bytes
  | .one x => some x
  | _ => Option.none

theorem Hits.merge_assoc (a b c : Hits) : (a.merge b).merge c = a.merge (b.merge c) := by
  cases a <;> cases b <;> cases c <;> simp only [Hits.merge] <;> split_ifs <;> simp_all

@[simp] theorem Hits.many_merge (h : Hits) : Hits.many.merge h = .many := by cases h <;> rfl

@[simp] theorem Hits.none_merge (h : Hits) : Hits.none.merge h = h := rfl

@[simp] theorem Hits.merge_none (h : Hits) : h.merge .none = h := by cases h <;> rfl

@[simp] theorem Hits.one_merge_one (x y : Bytes) :
    (Hits.one x).merge (.one y) = if x = y then .one x else .many := rfl

/-- A pair's index key: its digest's words and its byte string's length. -/
@[expose] def hitKey (p : Bytes × Digest) : List UInt64 × ℕ := (p.2.toList, p.1.length)

/-- What the pairs answer at key `k`. -/
@[expose] def hitsOf : List (Bytes × Digest) → List UInt64 × ℕ → Hits
  | [], _ => .none
  | p :: l, k => (if hitKey p = k then Hits.one p.1 else Hits.none).merge (hitsOf l k)

/-- **The preimage index** of the pairs: at each key, what the pairs with that key answer. -/
@[expose] def preimageIndex (pairs : List (Bytes × Digest)) :
    SortedMap (List UInt64 × ℕ) Hits :=
  pairs.foldl (fun m p ↦ m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) .empty

/-- `preimage`, read off an index. -/
@[expose] def preimageIn (idx : SortedMap (List UInt64 × ℕ) Hits) (d : Digest) (len : ℕ) :
    Option Bytes :=
  (idx.getD (d.toList, len) .none).toOption

private theorem getD_foldl (l : List (Bytes × Digest)) (m : SortedMap (List UInt64 × ℕ) Hits)
    (k : List UInt64 × ℕ) :
    (l.foldl (fun m p ↦ m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m).getD
      k .none = (m.getD k .none).merge (hitsOf l k) := by
  induction l generalizing m with
  | nil => simp [hitsOf]
  | cons p l ih =>
    rw [List.foldl_cons, ih, SortedMap.getD_insert, hitsOf]
    by_cases hk : hitKey p = k
    · subst hk
      simp only [↓reduceIte, Hits.merge_assoc]
    · simp only [hk, ↓reduceIte]
      rfl

private theorem one_merge_hitsOf (l : List (Bytes × Digest)) (d : Digest) (len : ℕ) (x : Bytes) :
    (Hits.one x).merge (hitsOf l (d.toList, len)) =
      if l.all (fun p' ↦ !(decide (p'.2.toList = d.toList) && decide (p'.1.length = len)) ||
          decide (p'.1 = x)) then .one x else .many := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [hitsOf, ← Hits.merge_assoc, List.all_cons]
    by_cases hq : q.2.toList = d.toList ∧ q.1.length = len
    · have hk : hitKey q = (d.toList, len) := by simp [hitKey, hq]
      simp only [hk, ↓reduceIte, Hits.one_merge_one, hq, decide_true, Bool.and_self,
        Bool.not_true, Bool.false_or]
      by_cases hx : x = q.1
      · simp only [hx, ↓reduceIte, decide_true, Bool.true_and]
        rw [← hx, ih]
      · simp [hx, Ne.symm hx]
    · have hk : hitKey q ≠ (d.toList, len) := fun h ↦ hq (by simpa [hitKey] using h)
      have hb : (!(decide (q.2.toList = d.toList) && decide (q.1.length = len)) ||
          decide (q.1 = x)) = true := by
        by_cases h1 : q.2.toList = d.toList <;> simp_all
      simp only [hk, ↓reduceIte, Hits.merge_none, ih, hb, Bool.true_and]

theorem preimage_eq_hitsOf (pairs : List (Bytes × Digest)) (d : Digest) (len : ℕ) :
    preimage pairs d len = (hitsOf pairs (d.toList, len)).toOption := by
  induction pairs with
  | nil => rfl
  | cons p l ih =>
    rw [hitsOf]
    by_cases hp : hitKey p = (d.toList, len)
    · simp only [hitKey, Prod.mk.injEq] at hp
      simp only [preimage, List.find?_cons, hp, decide_true, Bool.and_self, List.all_cons,
        Bool.not_true, Bool.false_or, Bool.true_and, hitKey, ↓reduceIte]
      rw [one_merge_hitsOf]
      split <;> rfl
    · have hh : (decide (p.2.toList = d.toList) && decide (p.1.length = len)) = false := by
        by_cases h1 : p.2.toList = d.toList <;> simp_all [hitKey]
      simp only [hp, ↓reduceIte, Hits.none_merge, ← ih]
      simp only [preimage, List.find?_cons, hh, List.all_cons, Bool.not_false, Bool.true_or,
        Bool.true_and]

/-- **The index answers as `preimage` does.** -/
theorem preimageIn_preimageIndex (pairs : List (Bytes × Digest)) :
    preimageIn (preimageIndex pairs) = preimage pairs := by
  funext d len
  rw [preimageIn, preimageIndex, getD_foldl, SortedMap.getD_empty, preimage_eq_hitsOf]
  rfl

/-! ## The extractor with a preimage lookup -/

/-- `leafOf`, with the preimages from `pre`. -/
@[expose] def leafOfWith (pre : Digest → ℕ → Option Bytes) (w : ℕ) (d : Digest) : List K :=
  match pre d (8 * w) with
  | some x => bytesWords w x
  | none => List.replicate w 0

/-- `subtreeLeaves`, with the preimages from `pre`. -/
@[expose] def subtreeLeavesWith (pre : Digest → ℕ → Option Bytes) (w : ℕ) :
    ℕ → Digest → Array (List K)
  | 0, d => #[leafOfWith pre w d]
  | h + 1, d =>
    match pre d 64 with
    | some x =>
      subtreeLeavesWith pre w h (splitNode x).1 ++ subtreeLeavesWith pre w h (splitNode x).2
    | none => Array.replicate (2 ^ (h + 1)) (List.replicate w 0)

theorem subtreeLeavesWith_preimage (pairs : List (Bytes × Digest)) (w h : ℕ) (d : Digest) :
    subtreeLeavesWith (preimage pairs) w h d = subtreeLeaves pairs w h d := by
  induction h generalizing d with
  | zero => rfl
  | succ h ih =>
    simp only [subtreeLeavesWith, subtreeLeaves, ih]
    cases preimage pairs d 64 <;> rfl

theorem subtreeLeavesWith_congr {pre pre' : Digest → ℕ → Option Bytes} {w : ℕ}
    (h64 : ∀ d, pre d 64 = pre' d 64) (hw : ∀ d, pre d (8 * w) = pre' d (8 * w)) (h : ℕ)
    (d : Digest) : subtreeLeavesWith pre w h d = subtreeLeavesWith pre' w h d := by
  induction h generalizing d with
  | zero => simp only [subtreeLeavesWith, leafOfWith, hw]
  | succ h ih => simp only [subtreeLeavesWith, h64, ih]

/-- **The extractor with indexed preimages**: `extractFast` with the leaves read through
`lookup (mk width)`, the index `mk width` built once. -/
@[expose] def extractWith {α : Type} (prog : LeanIsaProgram) (input : PublicInput) (bytecode :
    List K)
    (mk : ℕ → α) (lookup : α → Digest → ℕ → Option Bytes) (π : Proof) :
    Option (Execution prog) := do
  let ((layout, logInverseRate), state) ← afterRoot bytecode π
  let (root, height, width) ← state.roots.head?
  let idx := mk width
  let leaves := subtreeLeavesWith (lookup idx) width height root
  let word := leafAt leaves height width
  let execution := candidateExecutionFast prog input layout
  (fastStacks layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksFast layout.stackLog logInverseRate word).findSome? execution

theorem extractWith_preimage (prog : LeanIsaProgram) (input : PublicInput) (bytecode : List K)
    (answers : Bytes → Option Digest) (keys : List Bytes) (π : Proof) :
    extractWith prog input bytecode (fun _ ↦ answerPairs answers keys) preimage π =
      extractFast prog input bytecode answers keys π := by
  simp only [extractWith, extractFast, committedLeaves, subtreeLeavesWith_preimage]

theorem extractWith_congr {α β : Type} (prog : LeanIsaProgram) (input : PublicInput) (bytecode :
    List K)
    (mk : ℕ → α) (lookup : α → Digest → ℕ → Option Bytes) (mk' : ℕ → β)
    (lookup' : β → Digest → ℕ → Option Bytes)
    (h : ∀ w d, ∀ len ∈ [64, 8 * w], lookup (mk w) d len = lookup' (mk' w) d len) (π : Proof) :
    extractWith prog input bytecode mk lookup π = extractWith prog input bytecode mk' lookup' π := by
  have hl : ∀ w height root, subtreeLeavesWith (lookup (mk w)) w height root =
      subtreeLeavesWith (lookup' (mk' w)) w height root := fun w height root ↦
    subtreeLeavesWith_congr (fun d ↦ h w d 64 (by simp)) (fun d ↦ h w d (8 * w) (by simp)) _ _
  simp only [extractWith, hl]

end

end LeanVM.Extraction.Fast
