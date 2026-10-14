import WhirAeneas.MerkleNative
import WhirAeneas.MerkleOpen

/-! The native rows read from the content of its hint: when the next hint holds the rows of the
distinct sorted queries as little-endian words, then whole 32-byte siblings, and the opening of
the queries accepts against the root (`HintOpens`), the generated native `open_rows` returns
each query's row and consumes the hint. Under injective leaf and pair hashes, an accepting hint
against a committed tree's root opens the committed rows. -/
namespace WhirAeneas.MerkleNative
open Aeneas Aeneas.Std ReplaySource WhirAeneas.Merkle

/-- The distinct queries, ascending. -/
def sortedOf (qs : List Nat) : List Nat := qs.toFinset.sort (· ≤ ·)

/-- The first `n` little-endian words of a hint. -/
def wordsOf (hint : List U8) (n : Nat) : List U64 := (List.range n).map fun t => wordAt hint (8 * t)

/-- Query `q`'s row: the one stored at `q`'s place among the distinct sorted queries' rows. -/
def rowAt (rows : List U64) (sorted : List Nat) (rw q : Nat) : List U64 := (rows.drop (sorted.idxOf q * rw)).take rw

/-- A rows event's hint over a tree of `2 ^ depth` leaves: the rows of the distinct sorted
queries as little-endian words, then whole 32-byte siblings `sibs`, such that the opening of the
queries accepts against `root`; `ws` is each query's row. The widths and depth fit a word. -/
structure HintOpens (leaf : List U64 → Digest) (node : Digest → Digest → Digest) (root : Digest)
    (depth : Nat) (qs : List Nat) (rw lw : Nat) (ws : List (List U64)) (hint : List U8) : Prop where
  pos : 0 < rw
  depth_lt : depth < 62
  cap : 128 * (qs.length + 1) * (lw + 1) < Usize.max
  bytes : 8 * ((sortedOf qs).length * rw) ≤ hint.length
  whole : (hint.length - 8 * ((sortedOf qs).length * rw)) % 32 = 0
  accepts : ∃ sibs : List Digest, sibs.map (·.val) =
      (List.range ((hint.length - 8 * ((sortedOf qs).length * rw)) / 32)).map
        (fun t => digestBytes hint (8 * ((sortedOf qs).length * rw) + 32 * t)) ∧
    ∃ I Ps, openSpec leaf node (wordsOf hint ((sortedOf qs).length * rw)) sibs root depth qs rw lw = some (I, Ps)
  rows : ws = qs.map (rowAt (wordsOf hint ((sortedOf qs).length * rw)) (sortedOf qs) rw)

theorem drop_app {β : Type} (A B : List β) (j : Nat) : (A ++ B).drop (A.length + j) = B.drop j := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.cons_append, List.length_cons, show A.length + 1 + j = (A.length + j) + 1 by omega,
      List.drop_succ_cons, ih]

theorem flatMap_chunk {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (L : List α), (∀ x ∈ L, (f x).length = k) → ∀ (i : Nat) (hi : i < L.length),
      ((L.flatMap f).drop (i * k)).take k = f L[i]
  | [], _, i, hi => by simp at hi
  | x :: L, h, i, hi => by
    have hx := h x (by simp)
    cases i with
    | zero => simp [List.flatMap_cons, ← hx]
    | succ i =>
      rw [List.flatMap_cons, show (i + 1) * k = (f x).length + i * k by rw [hx, Nat.succ_mul]; omega,
        drop_app]
      exact flatMap_chunk f k L (fun y hy => h y (by simp [hy])) i (by simpa using hi)

theorem flatMap_length {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (L : List α), (∀ x ∈ L, (f x).length = k) → (L.flatMap f).length = L.length * k
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatMap_cons, List.length_append, h x (by simp),
      flatMap_length f k L (fun y hy => h y (by simp [hy]))]
    simp [Nat.succ_mul]; omega

/-- What an accepting `openSpec` says about its arguments and images. -/
theorem openSpec_some (leaf : List U64 → Digest) (node : Digest → Digest → Digest) (rows : List U64)
    (sibs : List Digest) (root : Digest) (h : Nat) (qs : List Nat) (rw lw : Nat) (I Ps)
    (hs : openSpec leaf node rows sibs root h qs rw lw = some (I, Ps)) :
    qs ≠ [] ∧ rw ≤ lw ∧ (∀ q ∈ qs, q < 2 ^ h) ∧ rows.length = (sortedOf qs).length * rw ∧
      I = qs.flatMap (imageOf rows (sortedOf qs) rw lw) := by
  simp only [openSpec] at hs
  split_ifs at hs with hcond
  simp only [not_or, not_exists, not_and, not_le] at hcond
  obtain ⟨hq, hrl, hin, hlen⟩ := hcond
  refine ⟨hq, by omega, hin, by simpa [sortedOf] using hlen, ?_⟩
  cases hreb : rebuildSpec node sibs h (leavesOf leaf rows (qs.toFinset.sort (· ≤ ·)) rw lw) 0 with
  | none => rw [hreb] at hs; cases hs
  | some x =>
    obtain ⟨lvls, top, u⟩ := x
    rw [hreb] at hs
    dsimp only at hs
    split_ifs at hs
    exact expandSpec_images _ _ _ rw lw qs I Ps hs

theorem imageOf_length (rows : List U64) (S : List Nat) (rw lw q : Nat) (hrl : rw ≤ lw)
    (hq : q ∈ S) (hlen : rows.length = S.length * rw) : (imageOf rows S rw lw q).length = lw := by
  have hi : S.idxOf q < S.length := List.idxOf_lt_length_of_mem hq
  have : S.idxOf q * rw + rw ≤ rows.length := by rw [hlen, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  simp only [imageOf, List.length_append, List.length_replicate, List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by omega)]; omega

theorem rowsOf_images (o : merkle.Openings) (rows : List U64) (qs : List Nat) (rw : Nat)
    (hrl : rw ≤ o.leaf_words.val) (h0 : 0 < o.leaf_words.val) (hin : ∀ q ∈ qs, q ∈ sortedOf qs)
    (hlen : rows.length = (sortedOf qs).length * rw)
    (hI : o.images.val = qs.flatMap (imageOf rows (sortedOf qs) rw o.leaf_words.val)) :
    rowsOf o rw = qs.map (rowAt rows (sortedOf qs) rw) := by
  have hk : ∀ q ∈ qs, (imageOf rows (sortedOf qs) rw o.leaf_words.val q).length = o.leaf_words.val :=
    fun q hq => imageOf_length rows _ rw _ q hrl (hin q hq) hlen
  have hl : o.images.val.length = qs.length * o.leaf_words.val := by rw [hI]; exact flatMap_length _ _ qs hk
  unfold rowsOf
  rw [hl, Nat.mul_div_cancel _ h0]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [hI, flatMap_chunk _ _ qs hk i (by simpa using h1)]
  simp only [imageOf, rowAt]
  rw [List.drop_left' (by simp)]

/-- The native rows read: a hint that opens the event's rows is consumed and its rows returned. -/
theorem open_rows_ok (hword : UScalarTy.Usize.numBits = 64) {leaf : List U64 → Digest}
    {node : Digest → Digest → Digest} (hR : RowHash leaf) (hP : PairHash node) (vs : VS)
    (hp : vs.poison = none) (root : Digest) (depth : Usize) (queries : Slice Usize) (rw lw : Usize)
    (L : U32) (hint more : Slice U8) (hL : L.val = hint.val.length)
    (hb : vs.hints.rest.val = (core.num.U32.to_le_bytes L).val ++ hint.val ++ more.val) (ws : List (List U64))
    (hh : HintOpens leaf node root depth.val (queries.val.map (·.val)) rw.val lw.val ws hint.val) :
    ∃ rows : alloc.vec.Vec (alloc.vec.Vec U64), verifier.open_rows_native vs root depth queries rw lw =
        .ok (.Ok rows, ({ vs with hints := ⟨more⟩, hints_read := Std.Usize.wrapping_add vs.hints_read 1#usize } : VS)) ∧
      rows.val.map (fun r : alloc.vec.Vec U64 => r.val) = ws := by
  set qs := queries.val.map (·.val) with hqs
  obtain ⟨distinct, hd, ed⟩ := sorted_unique_eq hword queries
  have hdl : (alloc.vec.Vec.len distinct).val = (sortedOf qs).length := by
    have := congrArg List.length ed; simp [sortedOf] at this ⊢; exact this
  have h8 : 8 * ((alloc.vec.Vec.len distinct).val * rw.val) ≤ hint.val.length := by rw [hdl]; exact hh.bytes
  have h32 : (hint.val.length - 8 * ((alloc.vec.Vec.len distinct).val * rw.val)) % 32 = 0 := by
    rw [hdl]; exact hh.whole
  obtain ⟨p, hf, hrows, hsibs⟩ := from_hint_some hint (alloc.vec.Vec.len distinct) rw h8 h32
  obtain ⟨sibs, esibs, I, Ps, hspec⟩ := hh.accepts
  rw [hdl] at hrows hsibs
  have hsib : p.sibling_hashes.val = sibs :=
    (List.map_injective_iff.mpr (fun a b h => (Array.eq_iff a b).mpr h)) (by rw [hsibs, esibs])
  have hrows' : p.rows.val = wordsOf hint.val ((sortedOf qs).length * rw.val) := hrows
  obtain ⟨hqne, hrl, hin, hlen, hI⟩ := openSpec_some leaf node _ sibs root depth.val qs rw.val lw.val I Ps hspec
  have hdep : depth.val < 64 := by have := hh.depth_lt; omega
  have hnl := shl_one_val hword depth hdep
  obtain ⟨res, hopen, hout⟩ := open_eq hword hR hP p root (Std.Usize.wrapping_shl 1#usize depth) depth.val hnl
    hh.depth_lt queries rw lw hh.pos (by simpa [qs] using hh.cap)
  rw [hrows', hsib] at hout
  try rw [← hqs] at hout
  rw [hspec] at hout
  obtain ⟨o, rfl, hlw, -, himg, -⟩ := hout
  have hw : ∀ o', some o = some o' → 0 < o'.leaf_words.val ∧ rw.val ≤ o'.leaf_words.val := by
    intro o' he; cases he; rw [hlw]; exact ⟨by have := hh.pos; omega, hrl⟩
  have hr := open_rows_eq vs hp root depth queries rw lw L hint more hL hb distinct hd (some p) hf (some o) hopen hw
  obtain ⟨rows, hrun, erows⟩ := hr
  refine ⟨rows, hrun, ?_⟩
  rw [erows, hh.rows]
  have hlw' : o.leaf_words.val = lw.val := by rw [hlw]
  apply rowsOf_images o _ qs rw.val (by rw [hlw']; exact hrl) (by rw [hlw']; have := hh.pos; omega)
    (fun q hq => (mem_sort_iff _ q).mpr hq) hlen
  rw [himg, hI, hlw']

/-- Binding of a hint: under injective leaf and pair hashes, rows a hint opens against the root
of the committed tree `T` (leaf `i` hashing row `C i` after the zero prefix, each parent the pair
hash of its children) are the committed rows. -/
theorem hint_binding (leaf : List U64 → Digest) (node : Digest → Digest → Digest)
    (hleaf : ∀ a b, leaf a = leaf b → a = b) (hnode : ∀ a b c d, node a b = node c d → a = c ∧ b = d)
    (depth : Nat) (qs : List Nat) (rw lw : Nat) (ws : List (List U64)) (hint : List U8)
    (C : Nat → List U64) (T : Nat → Nat → Digest)
    (hT0 : ∀ i, T 0 i = leaf (List.replicate (lw - rw) primitives.field.gf2_64.F64.ZERO ++ C i))
    (hT : ∀ l i, T (l + 1) i = node (T l (2 * i)) (T l (2 * i + 1)))
    (hh : HintOpens leaf node (T depth 0) depth qs rw lw ws hint) :
    ws = qs.map C ∧ ∀ q ∈ qs, q < 2 ^ depth := by
  obtain ⟨sibs, -, I, Ps, hspec⟩ := hh.accepts
  have hb := openSpec_binding leaf node hleaf hnode _ sibs depth qs rw lw C T hT0 hT I Ps hspec
  obtain ⟨-, -, hin, -, -⟩ := openSpec_some leaf node _ sibs (T depth 0) depth qs rw lw I Ps hspec
  refine ⟨?_, hin⟩
  rw [hh.rows]
  apply List.map_congr_left
  intro q hq
  have := hb q hq
  simp only [imageOf] at this
  exact List.append_cancel_left this

end WhirAeneas.MerkleNative
