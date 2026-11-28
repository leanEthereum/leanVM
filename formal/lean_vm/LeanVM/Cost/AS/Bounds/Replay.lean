module

public import LeanVM.Cost.AS.Bounds.Tactic
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.AS.Forward
import all Statement.Field
import LeanVM.Cost.AS.Bounds.TraceShape

/-!
# Bounds: the agreement-set extractor's replay

* the first forward answers' map (keys of `25` words, values Keccak states): `searchFwd_cost`,
  `mergeNewerFwd_cost`, `carryFwd_amortized`, `getFwd_cost`;
* **`fwdIndex_cost`**: the index of `N ≤ 2^D` queries, `(fwdStepPrice D W + 14)·N + 9`;
  **`fwdF_cost`**: a lookup in a good map, `fwdLookupPrice D W`;
* `keccakIdx_cost`: Keccak-256 of `L` bytes through the index, `L/136 + 1` blocks of a lookup and
  `430004`, and `8·L + 85`; **`extractSeed_cost`**: the seed of a bytecode of `n` words
  (`extractLC`'s, its hash closure over the index built once);
* the sponge (`absorb_cost`, `squeeze_cost`, `absorbNonce_cost`, at most four scalars waiting:
  `SpOk`), its packed absorptions and draws (`observePacked_cost`, `samplesPacked_cost`: a
  permutation and `20000` per scalar, and one more);
* **`skelReplay_cost`**: the skeleton's replay (`skelReplayP.c327`), per operation two lookups,
  `34000` and `11` per root, and per packed scalar a lookup and `40000`.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Extraction.AS LeanVM.Cost.Extractor

public section

attribute [local instance] lexOrd

variable (P : MachineProgram)

/-! ## The first forward answers' map -/

/-- The map's key-value pairs. -/
abbrev FwdEntry := List UInt64 × LeanVM.Semantics.KeccakState

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- The binary search of a word list `k` (`searchIn.c306`). -/
theorem searchFwd_cost (hP : Includes P searchIn.c306.costDeps)
    (t : Array FwdEntry) (k : List UInt64) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c306.costIdx [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp : ∀ a b : List UInt64, machineCost P Auto.List.compareLex.c5.costIdx
      [.closure searchPreC.lam0.costIdx [], encodeValue a, encodeValue b] ≤ 26 * b.length + 7 := by
    intro a b
    have := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
      (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
      (fun a b ↦ by
        rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero,
          searchPreC.lam0.costEq P (by includes)]
        split_ifs <;> omega) a b
    omega
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchIn.c306.costIdx [encodeValue t, encodeValue k, encodeValue x.1,
      encodeValue x.2])
    (40 + 26 * k.length + 9 * W) (40 + 26 * k.length + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c306.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    limbs_bound hW
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c306.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    limbs_bound hW
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      dsimp only
      split_ifs <;> omega
    | some v =>
      have hc := hcmp v.1 k
      dsimp only
      generalize compare v.1 k = o2
      cases o2
      · right
        refine ⟨((lo + hi) / 2 + 1, hi), ⟨by omega, hhi⟩, by dsimp only; omega, ?_⟩
        dsimp only
        split_ifs <;> omega
      · left
        dsimp only
        split_ifs <;> omega
      · right
        refine ⟨(lo, (lo + hi) / 2), ⟨hlo, by omega⟩, by dsimp only; omega, ?_⟩
        dsimp only
        split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `mergeNewer` on word-list keys (`mergeNewer.c310`): at most `26·L + 33` per entry and `3`. -/
theorem mergeNewerFwd_cost (hP : Includes P mergeNewer.c310.costDeps) (L : ℕ) :
    ∀ (n : ℕ) (a b : List FwdEntry), a.length + b.length = n →
      (∀ e ∈ b, WordsKey L e.1) →
      machineCost P mergeNewer.c310.costIdx [encodeValue a, encodeValue b] ≤ (26 * L + 33) * n + 3 := by
  have hcmp := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero,
        searchPreC.lam0.costEq P (by includes)]
      split_ifs <;> omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hb
  cases a with
  | nil => rw [mergeNewer.c310.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c310.costEq_cons P hP]
    cases b with
    | nil => simp at hn ⊢; have : 1 ≤ n := (by omega); nlinarith
    | cons y b =>
      dsimp only
      have hy : y.1.length ≤ L := hb y (by simp)
      have hc := hcmp x.1 y.1
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp) hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl
        (fun e he ↦ hb e (by simp [he]))
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp)
        (fun e he ↦ hb e (by simp [he]))
      simp only [List.length_cons] at hn h1 h3
      have : (9 + 17) * y.1.length ≤ 26 * L := by omega
      generalize compare x.1 y.1 = o2
      subst hn
      cases o2 <;> dsimp only <;> nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Two levels merged (`Level.merge.c309`): at most `26·L + 37` per entry and `18`. -/
theorem levelMergeFwd_cost (hP : Includes P Level.merge.c309.costDeps) (L : ℕ)
    (l l' : Level (List UInt64) LeanVM.Semantics.KeccakState) (hQ : KeysIn (WordsKey L) [l, l'])
    (W : ℕ) (hw : limbCount l.weight ≤ W) (hw' : limbCount l'.weight ≤ W)
    (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P Level.merge.c309.costIdx [encodeValue l, encodeValue l'] ≤
      18 + W + (26 * L + 37) * (l.entries.size + l'.entries.size) := by
  rw [Level.merge.c309.costEq P hP]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) ≤ W :=
    max_le hws (max_le hw hw')
  have hm := mergeNewerFwd_cost P (by includes) L _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the first forward answers' map, amortized** (`carry.c308`). -/
theorem carryFwd_amortized (hP : Includes P carry.c308.costDeps) (L D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hm : smGood m)
    (hQ : KeysIn (WordsKey L) m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level (List UInt64) LeanVM.Semantics.KeccakState) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, WordsKey L e.1) :
    machineCost P carry.c308.costIdx [encodeValue l, encodeValue m.levels] +
        (26 * L + 37) * potential D (carry l m.levels) ≤
      (26 * L + 37) * potential D m.levels + (26 * L + 37) * D + (32 + 2 * W) * (m.levels.length + 1) := by
  refine insert_amortized (WordsKey L)
    (fun l ls ↦ machineCost P carry.c308.costIdx [encodeValue l, encodeValue ls])
    (32 + 2 * W) (26 * L + 37) D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c308.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c308.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeFwd_cost P (by includes) L l l' hQ2 W (hW _ (by omega)) (hW _ (by omega))
      (hW _ (by omega))
    rw [carry.c308.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the first forward answers' map (`SortedMap.get?.c304`): a binary search per level. -/
theorem getFwd_cost (hP : Includes P SortedMap.get?.c304.costDeps)
    (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (H W : ℕ)
    (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (k : List UInt64) :
    machineCost P SortedMap.get?.c304.costIdx [encodeValue m, encodeValue k] ≤
      m.levels.length * (20 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.closure SortedMap.get?.c304.lam0.costIdx [encodeValue k])
      [encodeValue l] ≤ 9 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.length_singleton, List.singleton_append,
      SortedMap.get?.c304.lam0.costEq P (by includes)]
    have := searchFwd_cost P (by includes) l.entries k H W hW (hm l hl)
      0 l.entries.size (by omega) (hm l hl)
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : (40 + 26 * k.length + 9 * W) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _
    (.closure SortedMap.get?.c304.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (SortedMap.get?.c304.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [SortedMap.get?.c304.costEq P hP]
  nlinarith

/-! ## The index -/

/-- The index's invariant with `r` insertions left: a good map of `25`-word keys, the insertions
staying within `2^D`. -/
@[expose] def FwdInv (D : ℕ) (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (r : ℕ) :
    Prop :=
  smGood m ∧ KeysIn (WordsKey 25) m.levels ∧ smWeightSum m + r ≤ 2 ^ D

/-- A lookup in a map of fewer than `2^D` insertions, amortized or not. -/
@[expose] def fwdGetPrice (D W : ℕ) : ℕ := D * (20 + (690 + 9 * W) * (D + 2)) + 9

/-- **One step of the index, amortized**: a lookup and an insertion of a `25`-word key. -/
@[expose] def fwdStepPrice (D W : ℕ) : ℕ :=
  fwdGetPrice D W + 687 * D + (32 + 2 * W) * (D + 1) + 130

theorem fwdGet_le (hP : Includes P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c304.costDeps)
    (D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hg : smGood m)
    (hN : smWeightSum m < 2 ^ D) (k : List UInt64) (hk : k.length = 25) :
    machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c304.costIdx
      [encodeValue m, encodeValue k] ≤ fwdGetPrice D W := by
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg hN
  have hget := getFwd_cost P hP m (2 ^ D) W hW (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) k
  rw [Nat.log2_two_pow, hk, show 40 + 26 * 25 + 9 * W = 690 + 9 * W by omega] at hget
  have := Nat.mul_le_mul_right (20 + (690 + 9 * W) * (D + 2)) hlev
  unfold fwdGetPrice
  omega

theorem fwdStep_amortized (hP : Includes P fwdStepC.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (r : ℕ) (hm : FwdInv D m (r + 1))
    (q : Common.PermutationQuery LeanVM.Semantics.KeccakState × LeanVM.Semantics.KeccakState) :
    FwdInv D (fwdStep m q) r ∧
      machineCost P fwdStepC.costIdx [encodeValue m, encodeValue q] +
          (26 * 25 + 37) * potential D (fwdStep m q).levels ≤
        (26 * 25 + 37) * potential D m.levels + fwdStepPrice D W := by
  obtain ⟨hg, hQ, hw⟩ := hm
  have hN : smWeightSum m < 2 ^ D := by omega
  obtain ⟨hlev, -⟩ := smGood_levels_le hg hN
  obtain ⟨q, y⟩ := q
  rw [fwdStepC.costEq P hP]
  cases q with
  | inverse z =>
    simp only [fwdStep]
    refine ⟨⟨hg, hQ, by omega⟩, ?_⟩
    unfold fwdStepPrice
    omega
  | forward x =>
    simp only [fwdStep, Vector.size_toArray]
    have hx : x.toList.length = 25 := by simp
    have hget := fwdGet_le P (by includes) D W hW m hg hN x.toList hx
    rw [Auto.LeanVM.Extraction.Fast.insertIfNew.c303.costEq P (by includes)]
    unfold fwdStepPrice
    by_cases hc : m.contains x.toList = true
    · simp only [insertIfNew, hc, ↓reduceIte]
      refine ⟨⟨hg, hQ, by omega⟩, ?_⟩
      generalize m.get? x.toList = o
      cases o <;> dsimp only <;> nlinarith
    · simp only [insertIfNew, hc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2⟩ := smGood_insert hg x.toList y
      refine ⟨⟨h1, keysIn_insert hQ (show WordsKey 25 x.toList from hx.le) y, by omega⟩, ?_⟩
      rw [Auto.LeanVM.Extraction.Fast.SortedMap.insert.c307.costEq P (by includes)]
      have hcarry := carryFwd_amortized P (by includes) 25 D W hW m hg hQ hN
        ⟨1, #[(x.toList, y)], by simp [Ascending]⟩ rfl rfl
        (fun e he ↦ by simp at he; rw [he]; exact hx.le)
      have hins : (m.insert x.toList y).levels =
          carry ⟨1, #[(x.toList, y)], by simp [Ascending]⟩ m.levels := rfl
      rw [hins]
      have hc1 := Nat.mul_le_mul_left (32 + 2 * W) (show m.levels.length + 1 ≤ D + 1 by omega)
      generalize m.get? x.toList = o
      cases o <;> dsimp only <;> nlinarith

theorem fwd_foldl_good :
    ∀ (qs : List (Common.PermutationQuery LeanVM.Semantics.KeccakState × LeanVM.Semantics.KeccakState))
      (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState), smGood m →
      smGood (qs.foldl fwdStep m) ∧ smWeightSum (qs.foldl fwdStep m) ≤ smWeightSum m + qs.length := by
  intro qs
  induction qs with
  | nil => intro m h; simpa using h
  | cons q qs ih =>
    intro m hg
    rw [List.foldl_cons]
    have step : smGood (fwdStep m q) ∧ smWeightSum (fwdStep m q) ≤ smWeightSum m + 1 := by
      obtain ⟨q, y⟩ := q
      cases q with
      | inverse z => exact ⟨hg, by simp only [fwdStep]; omega⟩
      | forward x =>
        simp only [fwdStep, insertIfNew]
        split_ifs
        · exact ⟨hg, by omega⟩
        · obtain ⟨h1, h2⟩ := smGood_insert hg x.toList y
          exact ⟨h1, by omega⟩
    obtain ⟨h1, h2⟩ := ih _ step.1
    simp only [List.length_cons]
    exact ⟨h1, by omega⟩

/-- **The index is a good map of at most its queries' insertions.** -/
theorem fwdIndex_good (qs : List (Common.PermutationQuery LeanVM.Semantics.KeccakState ×
    LeanVM.Semantics.KeccakState)) :
    smGood (fwdIndex qs) ∧ smWeightSum (fwdIndex qs) ≤ qs.length := by
  have := fwd_foldl_good qs SortedMap.empty smGood_empty
  rw [smWeightSum_empty, Nat.zero_add] at this
  exact this

/-- **The transcript's first forward answers, indexed** (`fwdIndexC`): at most
`(fwdStepPrice D W + 14)·N + 9` for `N ≤ 2^D` queries, `W` a bound of the limbs of the positions
and weights (up to `2·2^D`). -/
theorem fwdIndex_cost (hP : Includes P fwdIndexC.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (qs : List (Common.PermutationQuery LeanVM.Semantics.KeccakState × LeanVM.Semantics.KeccakState))
    (hn : qs.length ≤ 2 ^ D) :
    machineCost P fwdIndexC.costIdx [encodeValue qs] ≤ (fwdStepPrice D W + 14) * qs.length + 9 := by
  rw [fwdIndexC.costEq P hP]
  have := listFoldl_amortized P (by includes) _ (.closure fwdIndexC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (fwdIndexC.lam0.costSpec P (by includes) a b))
    (fwdStepPrice D W + 3) (fun m ↦ (26 * 25 + 37) * potential D m.levels) (FwdInv D)
    qs SortedMap.empty ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h,
      by simp [smWeightSum_empty]; omega⟩
    (fun acc r hacc q _ ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero,
        fwdIndexC.lam0.costEq P (by includes)]
      have := fwdStep_amortized P (by includes) D W hW acc r hacc q
      exact ⟨this.1, by omega⟩)
  have h0 : potential D (SortedMap.empty :
      SortedMap (List UInt64) LeanVM.Semantics.KeccakState).levels = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.zero_add] at this
  nlinarith

/-- A lookup through the index's function (`fwdFC`). -/
@[expose] def fwdLookupPrice (D W : ℕ) : ℕ := fwdGetPrice D W + 79

/-- **A lookup in a good map of fewer than `2^D` insertions** (`fwdFC`). -/
theorem fwdF_cost (hP : Includes P fwdFC.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (M : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hg : smGood M)
    (hN : smWeightSum M < 2 ^ D) (x : LeanVM.Semantics.KeccakState) :
    machineCost P fwdFC.costIdx [encodeValue M, encodeValue x] ≤ fwdLookupPrice D W := by
  rw [fwdFC.costEq P hP]
  have := fwdGet_le P (by includes) D W hW M hg hN x.toList (by simp)
  simp only [Vector.size_toArray]
  unfold fwdLookupPrice
  omega

/-! ## Keccak-256 through the index -/

open LeanVM.Protocol.KeccakHash in
open LeanVM.Cost.Auto.LeanVM.Protocol.KeccakHash in
/-- A lane of a block (`littleEndianLane.c320`), lane `i < 17`: at most `16778`. -/
theorem littleEndianLane_cost (hP : Includes P littleEndianLane.c320.costDeps) (bytes : List UInt8)
    (i : ℕ) (hi : i < 17) :
    machineCost P littleEndianLane.c320.costIdx [encodeValue bytes, encodeValue i] ≤ 16778 := by
  rw [littleEndianLane.c320.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) 8 [] (by norm_num)
  have h2 := listFoldl_le P (by includes) _
    (.closure littleEndianLane.c320.lam0.costIdx [encodeValue bytes, encodeValue i])
    (fun acc k ↦ RunsApp.of_spec (littleEndianLane.c320.lam0.costSpec P (by includes) bytes i acc k))
    2069 (fun _ ↦ True) (List.range 8) 0 trivial (fun acc _ k hk ↦ by
      refine ⟨trivial, ?_⟩
      have hk8 := List.mem_range.1 hk
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        littleEndianLane.c320.lam0.costEq P (by includes),
        limbs_of_lt (by omega : 8 * i < 2 ^ 64), limbs_of_lt (by omega : i < 2 ^ 64),
        limbs_of_lt (by omega : 8 * i + k < 2 ^ 64), limbs_of_lt (by omega : k < 2 ^ 64),
        limbs_of_lt (by omega : 8 * k < 2 ^ 64)]
      have := getD_cost_idx P (by includes) bytes (8 * i + k) 0 (by omega)
      simp only [List.length_cons, List.length_nil, max_self]
      omega)
  simp only [List.length_range] at h2
  omega

open LeanVM.Protocol.KeccakHash in
open LeanVM.Cost.Auto.LeanVM.Protocol.KeccakHash in
/-- **One block absorbed** (`absorbBlockWith.c318`): at most the permutation's price `B` and
`420300`. -/
theorem absorbBlockWith_cost (hP : Includes P absorbBlockWith.c318.costDeps)
    (π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (πVal : MachineValue)
    (hπ : ∀ a, RunsApp P πVal [encodeValue a] (encodeValue (π a))) (B : ℕ)
    (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P πVal [encodeValue a] ≤ B) (s : LeanVM.Semantics.KeccakState)
    (block : List UInt8) :
    machineCost P absorbBlockWith.c318.costIdx [πVal, encodeValue s, encodeValue block] ≤
      B + 420300 := by
  rw [absorbBlockWith.c318.costEq P hP π πVal hπ, ofFnFrom_length]
  have h1 := ofFnFrom_cost P (by includes) (n := 25) (by norm_num) _
    (.closure absorbBlockWith.c318.lam0.costIdx [encodeValue s, encodeValue block])
    (fun j ↦ RunsApp.of_spec (absorbBlockWith.c318.lam0.costSpec P (by includes) s block j)) 16792
    (fun j ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        absorbBlockWith.c318.lam0.costEq P (by includes),
        limbs_of_lt (by omega : (j : ℕ) < 2 ^ 64)]
      simp only [List.length_cons, List.length_nil]
      split_ifs with hj
      · have := littleEndianLane_cost P (by includes) block j hj
        omega
      · omega) 0 (Nat.zero_le _)
  have h2 := hB (Vector.ofFn fun i : Fin 25 ↦ if i.val < 17 then
    LeanVM.Semantics.Keccak.lane s i ^^^ littleEndianLane block i else LeanVM.Semantics.Keccak.lane s i)
  simp only [Nat.sub_zero] at h1
  omega

open LeanVM.Protocol.KeccakHash in
open LeanVM.Cost.Auto.LeanVM.Protocol.KeccakHash in
/-- **The absorption of `k` whole blocks and the padded last one** (`absorbWith.c317`), the data
below `136·(k + 1)` bytes: `B + 430000` per block. -/
theorem absorbWith_cost (hP : Includes P absorbWith.c317.costDeps)
    (π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (πVal : MachineValue)
    (hπ : ∀ a, RunsApp P πVal [encodeValue a] (encodeValue (π a))) (B : ℕ)
    (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P πVal [encodeValue a] ≤ B) :
    ∀ (k : ℕ) (s : LeanVM.Semantics.KeccakState) (data : List UInt8), k < 2 ^ 63 →
      data.length < 136 * (k + 1) →
      machineCost P absorbWith.c317.costIdx [πVal, encodeValue k, encodeValue s, encodeValue data] ≤
        (k + 1) * (B + 430000) := by
  intro k
  induction k with
  | zero =>
    intro s data _ hd
    rw [absorbWith.c317.costEq P hP π πVal hπ, limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64)]
    have h1 := padBlock_cost P (by includes) data (by omega)
    have h2 := absorbBlockWith_cost P (by includes) π πVal hπ B hB s (padBlock data)
    simp only [Nat.rec_zero]
    omega
  | succ k ih =>
    intro s data hk hd
    rw [absorbWith.c317.costEq P hP π πVal hπ]
    dsimp only
    rw [limbs_of_lt (by omega : k + 1 < 2 ^ 64)]
    have h1 := take_cost P (by includes) rate data (by rw [rate_eq]; norm_num)
    have h2 := absorbBlockWith_cost P (by includes) π πVal hπ B hB s (data.take rate)
    have h3 := bind_cost P (by includes) _
      (.closure 322 [encodeValue k, πVal, encodeValue data])
      (fun st ↦ RunsApp.of_spec (absorbWith.c317.lam0.costSpec P (by includes) k π πVal hπ data st))
      ((k + 1) * (B + 430000) + 2100) (fun st ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
          show (322 : ℕ) = absorbWith.c317.lam0.costIdx from rfl,
          absorbWith.c317.lam0.costEq P (by includes) k π πVal hπ]
        have := drop_cost P (by includes) rate data (by rw [rate_eq]; norm_num)
        have := ih st (data.drop rate) (by omega) (by simp only [List.length_drop, rate_eq]; omega)
        simp only [List.length_cons, List.length_nil, rate_eq] at *
        omega) (absorbBlockWith π s (data.take rate))
    have hr : rate = 136 := rate_eq
    have : (k + 1 + 1) * (B + 430000) = (k + 1) * (B + 430000) + B + 430000 := by ring
    omega

/-- The permutation through the index: its closure's price. -/
theorem hashLam_cost (hP : Includes P hashMC.lam0.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (M : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hg : smGood M)
    (hN : smWeightSum M < 2 ^ D) (x : LeanVM.Semantics.KeccakState) :
    appCost P (.closure hashMC.lam0.costIdx [encodeValue M]) [encodeValue x] ≤
      fwdLookupPrice D W + 4 := by
  rw [appCost_fn, List.singleton_append, hashMC.lam0.costEq P (by includes)]
  have := fwdF_cost P (by includes) D W hW M hg hN x
  simp only [List.length_singleton]
  omega

theorem length_toBytes (a : K) : a.toBytes.length = 8 := by
  simp [K.toBytes, LeanVM.Protocol.KeccakHash.wordBytes]

/-- Keccak-256 through a good index's closure (`keccak256With.c315` with `hashMC.lam0`), a message
of `L < 2^60` bytes. -/
theorem keccakIdx_cost (hP : Includes P Auto.LeanVM.Protocol.KeccakHash.keccak256With.c315.costDeps)
    (hL : Includes P hashMC.lam0.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (M : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hg : smGood M)
    (hN : smWeightSum M < 2 ^ D) (m : List UInt8) (hm : m.length < 2 ^ 60) :
    machineCost P Auto.LeanVM.Protocol.KeccakHash.keccak256With.c315.costIdx
      [.closure hashMC.lam0.costIdx [encodeValue M], encodeValue m] ≤
      (m.length / 136 + 1) * (fwdLookupPrice D W + 430004) + 8 * m.length + 85 := by
  rw [Auto.LeanVM.Protocol.KeccakHash.keccak256With.c315.costEq P hP
    (fwdF M) _ (fun x ↦ RunsApp.of_spec (hashMC.lam0.costSpec P hL M x)),
    limbs_of_lt (by omega : m.length < 2 ^ 64),
    limbs_of_lt (by rw [LeanVM.Cost.Bounds.rate_eq]; norm_num : LeanVM.Protocol.KeccakHash.rate < 2 ^ 64)]
  have hl := length_cost P (by includes) m (by omega)
  have ha := absorbWith_cost P (by includes) (fwdF M) _
    (fun x ↦ RunsApp.of_spec (hashMC.lam0.costSpec P hL M x)) _
    (hashLam_cost P hL D W hW M hg hN) (m.length / LeanVM.Protocol.KeccakHash.rate)
    (Vector.replicate 25 0) m (by rw [LeanVM.Cost.Bounds.rate_eq]; omega)
    (by rw [LeanVM.Cost.Bounds.rate_eq]; omega)
  have hb := bind_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.KeccakHash.keccak256With.c315.lam0.costIdx [])
    (fun st ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.keccak256With.c315.lam0.costSpec P
      (by includes) st)) 36 (fun st ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Protocol.KeccakHash.keccak256With.c315.lam0.costEq P (by includes)]
        rfl) (LeanVM.Protocol.KeccakHash.absorbWith (fwdF M)
          (m.length / LeanVM.Protocol.KeccakHash.rate) (Vector.replicate 25 0) m)
  rw [LeanVM.Cost.Bounds.rate_eq] at ha hb ⊢
  rw [show fwdLookupPrice D W + 4 + 430000 = fwdLookupPrice D W + 430004 by omega] at ha
  omega

/-- **The extractor's seed** (`seedWithHash.c484` as `extractLC` calls it: the IV hashed through a
closure over the index of the `N` queries, then one lookup), for `N < 2^D`. -/
theorem extractSeed_cost (hP : Includes P extractLC.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (qs : List (Common.PermutationQuery LeanVM.Semantics.KeccakState × LeanVM.Semantics.KeccakState))
    (hq : qs.length < 2 ^ D) (bytecode : List K) (hb : bytecode.length ≤ 2 ^ 34)
    (pd : LeanVM.Protocol.Digest) :
    machineCost P Auto.LeanVM.Protocol.Verifier.seedWithHash.c484.costIdx
      [.closure extractLC.lam1.costIdx [encodeValue (fwdIndex qs)],
        .closure hashMC.lam0.costIdx [encodeValue (fwdIndex qs)], encodeValue bytecode,
        encodeValue pd] ≤
      ((9 + 8 * bytecode.length) / 136 + 2) * (fwdLookupPrice D W + 430004) +
        520 * bytecode.length + 2000 := by
  obtain ⟨hg, hw⟩ := fwdIndex_good qs
  have hN : smWeightSum (fwdIndex qs) < 2 ^ D := by omega
  have hF : ∀ x, RunsApp P (.closure hashMC.lam0.costIdx [encodeValue (fwdIndex qs)]) [encodeValue x]
      (encodeValue (fwdF (fwdIndex qs) x)) := fun x ↦
    RunsApp.of_spec (hashMC.lam0.costSpec P (by includes) (fwdIndex qs) x)
  have hH : ∀ m, RunsApp P (.closure extractLC.lam1.costIdx [encodeValue (fwdIndex qs)]) [encodeValue m]
      (encodeValue (LeanVM.Protocol.KeccakHash.keccak256With (fwdF (fwdIndex qs)) m)) := fun m ↦
    RunsApp.of_spec (extractLC.lam1.costSpec P (by includes) (fwdIndex qs) m)
  have hlen : (LeanVM.Protocol.Verifier.versionTag ++
      bytecode.flatMap K.toBytes).length = 9 + 8 * bytecode.length := by
    rw [List.length_append, versionTag_eq, List.length_flatMap]
    simp [length_toBytes, List.sum_replicate, Nat.mul_comm]
  rw [Auto.LeanVM.Protocol.Verifier.seedWithHash.c484.costEq P (by includes) _ _ hH
    (fwdF (fwdIndex qs)) _ hF,
    Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c488.costEq P (by includes) _ _ hH]
  have h1 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c488.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c488.lam0.costSpec P
      (by includes) a)) 337 bytecode (fun a _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c488.lam0.costEq P (by includes)]
        have := LeanVM.Cost.Bounds.wordBytes_cost P (by includes) a.lane
        simp only [List.length_nil]
        omega)
  have h2 := flatten_map_cost P (by includes) 8 K.toBytes bytecode
    (fun a _ ↦ (length_toBytes a).le)
  have h3 := append_cost P (by includes) LeanVM.Protocol.Verifier.versionTag
    (bytecode.flatMap K.toBytes)
  have hv : LeanVM.Protocol.Verifier.versionTag.length = 9 := by rw [versionTag_eq]; rfl
  have h4 : appCost P (.closure extractLC.lam1.costIdx [encodeValue (fwdIndex qs)])
      [encodeValue (LeanVM.Protocol.Verifier.versionTag ++ bytecode.flatMap K.toBytes)] ≤
      ((9 + 8 * bytecode.length) / 136 + 1) * (fwdLookupPrice D W + 430004) +
        8 * (9 + 8 * bytecode.length) + 92 := by
    rw [appCost_fn, List.singleton_append, extractLC.lam1.costEq P (by includes)]
    have k1 := keccakIdx_cost P (by includes) (by includes) D W hW (fwdIndex qs) hg hN
      (LeanVM.Protocol.Verifier.versionTag ++ bytecode.flatMap K.toBytes) (by rw [hlen]; omega)
    rw [hlen] at k1
    simp only [List.length_singleton]
    omega
  have h5 := bind_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.Verifier.seedWithHash.c484.lam0.costIdx
      [.closure hashMC.lam0.costIdx [encodeValue (fwdIndex qs)], encodeValue pd])
    (fun iv ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.seedWithHash.c484.lam0.costSpec P
      (by includes) (fwdF (fwdIndex qs)) _ hF pd iv)) (fwdLookupPrice D W + 900) (fun iv ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          Auto.LeanVM.Protocol.Verifier.seedWithHash.c484.lam0.costEq P (by includes) _ _ hF,
          Auto.LeanVM.Protocol.Compile.seedInput.c486.costEq P (by includes), ofFnFrom_length]
        have := ofFnFrom_cost P (by includes) (n := 25) (by norm_num) _
          (.closure Auto.LeanVM.Protocol.Compile.seedInput.c486.lam0.costIdx
            [encodeValue iv, encodeValue pd])
          (fun j ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Compile.seedInput.c486.lam0.costSpec P
            (by includes) iv pd j)) 16 (fun j ↦ by
              rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
                Auto.LeanVM.Protocol.Compile.seedInput.c486.lam0.costEq P (by includes),
                limbs_of_lt (by omega : (j : ℕ) < 2 ^ 64)]
              simp only [List.length_cons, List.length_nil]
              split_ifs <;> omega) 0 (Nat.zero_le _)
        have := hashLam_cost P (by includes) D W hW (fwdIndex qs) hg hN
          (LeanVM.Protocol.Compile.seedInput iv pd)
        simp only [Nat.sub_zero, List.length_cons, List.length_nil] at *
        omega) (LeanVM.Protocol.Verifier.fiatShamirIvWithHash
          (LeanVM.Protocol.KeccakHash.keccak256With (fwdF (fwdIndex qs))) bytecode)
  have e1 : ((9 + 8 * bytecode.length) / 136 + 2) * (fwdLookupPrice D W + 430004) =
      ((9 + 8 * bytecode.length) / 136 + 1) * (fwdLookupPrice D W + 430004) +
        fwdLookupPrice D W + 430004 := by ring
  omega

/-- The public input's digest (`publicInputDigest.c491`). -/
theorem publicInputDigest_cost (hP : Includes P Auto.LeanVM.publicInputDigest.c491.costDeps)
    (input : LeanVM.Semantics.PublicInput) :
    machineCost P Auto.LeanVM.publicInputDigest.c491.costIdx [encodeValue input] ≤ 200 := by
  rw [Auto.LeanVM.publicInputDigest.c491.costEq P hP, Auto.Fin.ofNat.c102.costEq P (by includes),
    Auto.Fin.ofNat.c102.costEq P (by includes), Auto.Fin.ofNat.c102.costEq P (by includes),
    Auto.Fin.ofNat.c102.costEq P (by includes)]
  rw [limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (1 : ℕ) < 2 ^ 64),
    limbs_of_lt (by norm_num : (2 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (3 : ℕ) < 2 ^ 64)]
  omega

/-! ## The sponge -/

section Sponge

open LeanVM.Protocol.Compile
open LeanVM.Cost.Auto.LeanVM.Protocol.Compile

/-- A sponge the replay keeps: at most four scalars waiting, their tags word-sized. -/
@[expose] def SpOk (sp : Sponge) : Prop := sp.pending.length ≤ 4 ∧ ∀ p ∈ sp.pending, p.2 < 2 ^ 64

theorem duplex_some {π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState}
    {sp d : Sponge} (h : duplex π sp = some d) : d.pending = [] ∧ d.ground = sp.ground := by
  unfold duplex at h
  simp only [bind, pure] at h
  rcases hπ : π (duplexInput sp) with _ | st
  · rw [hπ] at h; cases h
  · rw [hπ] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem absorb_ok {π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState}
    {sp sp' : Sponge} {x : E} {tag : ℕ} (h : SpOk sp) (ht : tag < 2 ^ 64)
    (he : LeanVM.Protocol.Compile.absorb π sp x tag = some sp') : SpOk sp' := by
  unfold absorb at he
  simp only [bind, pure] at he
  split_ifs at he with hl
  · rcases hd : duplex π sp with _ | d
    · rw [hd] at he; cases he
    · rw [hd] at he
      cases he
      have := (duplex_some hd).1
      refine ⟨by simp [this], fun p hp ↦ ?_⟩
      simp only [this, List.nil_append, List.mem_singleton] at hp
      rw [hp]; exact ht
  · cases he
    refine ⟨by have := h.1; simp only [List.length_append, List.length_singleton]; unfold rateScalars at hl; omega,
      fun p hp ↦ ?_⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact h.2 p hp
    · rw [List.mem_singleton.1 hp]; exact ht

theorem squeeze_ok {π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState}
    {sp : Sponge} {c : E × Sponge} (h : SpOk sp) (he : squeeze π sp = some c) : SpOk c.2 := by
  unfold squeeze at he
  rcases hg : sp.ground with _ | g
  · rw [hg] at he
    simp only [bind, pure] at he
    rcases hd : duplex π sp with _ | d
    · rw [hd] at he; cases he
    · rw [hd] at he
      cases he
      have := (duplex_some hd).1
      exact ⟨by simp [this], by simp [this]⟩
  · rw [hg] at he
    simp only [pure] at he
    cases he
    exact h

theorem absorbNonce_ok {π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState}
    {sp : Sponge} {n : E} {c : UInt64 × Sponge} (he : absorbNonce π sp n = some c) :
    SpOk c.2 := by
  unfold absorbNonce at he
  simp only [bind, pure] at he
  rcases ha : LeanVM.Protocol.Compile.absorb π sp n dsPowNonce with _ | a
  · rw [ha] at he; cases he
  · rw [ha, Option.bind_some] at he
    rcases hd : duplex π a with _ | d
    · rw [hd] at he; cases he
    · rw [hd] at he
      cases he
      have := (duplex_some hd).1
      exact ⟨by simp [this], by simp [this]⟩

/-- The waiting scalars' lanes (`pendingLanes.c335`): at most `382`. -/
theorem pendingLanes_cost (hP : Includes P pendingLanes.c335.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P pendingLanes.c335.costIdx [encodeValue sp.pending] ≤ 382 := by
  rw [pendingLanes.c335.costEq P hP]
  have h1 := map_cost P (by includes) _ (.closure pendingLanes.c335.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (pendingLanes.c335.lam0.costSpec P (by includes) a)) 25 sp.pending
    (fun a ha ↦ by
      rw [appCost_fn, List.nil_append, pendingLanes.c335.lam0.costEq P (by includes)]
      obtain ⟨e, t⟩ := a
      have := h.2 _ ha
      dsimp only at this ⊢
      rw [limbs_of_lt this]
      simp)
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add h1 (flatten_cost P (by includes) 4 _ ?_)) _) ?_
  · intro l hl
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hl
    obtain ⟨e, t⟩ := a
    simp
  · have := h.1
    simp only [List.length_map]
    omega

/-- A permutation's input (`duplexInput.c333`): at most `16312`. -/
theorem duplexInput_cost (hP : Includes P duplexInput.c333.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P duplexInput.c333.costIdx [encodeValue sp] ≤ 16312 := by
  rw [duplexInput.c333.costEq P hP, ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := 25) (by norm_num) _
    (.closure duplexInput.c333.lam0.costIdx [encodeValue sp])
    (fun j ↦ RunsApp.of_spec (duplexInput.c333.lam0.costSpec P (by includes) sp j)) 635
    (fun j ↦ by
      rw [appCost_fn, List.singleton_append, duplexInput.c333.lam0.costEq P (by includes),
        limbs_of_lt (by omega : (j : ℕ) < 2 ^ 64)]
      simp only [List.length_singleton]
      split_ifs with hj
      · have := pendingLanes_cost P (by includes) sp h
        have := getD_cost_idx P (by includes) (pendingLanes sp.pending) j 0 (by omega)
        omega
      · omega) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at this
  omega

section Perm

variable (π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (πVal : MachineValue)
  (hπ : ∀ a, RunsApp P πVal [encodeValue a] (encodeValue (π a))) (B : ℕ)
  (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P πVal [encodeValue a] ≤ B)

include hπ hB in
/-- **A permutation** (`duplex.c331`): `B + 16340`. -/
theorem duplex_cost (hP : Includes P duplex.c331.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P duplex.c331.costIdx [πVal, encodeValue sp] ≤ B + 16340 := by
  rw [duplex.c331.costEq P hP π πVal hπ]
  have h1 := duplexInput_cost P (by includes) sp h
  have h2 := hB (duplexInput sp)
  have h3 := bind_cost P (by includes) _ (.closure duplex.c331.lam0.costIdx [encodeValue sp])
    (fun st ↦ RunsApp.of_spec (duplex.c331.lam0.costSpec P (by includes) sp st)) 11
    (fun st ↦ by
      rw [appCost_fn, List.singleton_append, duplex.c331.lam0.costEq P (by includes)]
      rfl) (π (duplexInput sp))
  omega

include hπ hB in
/-- **A scalar absorbed** (`absorb.c329`): `B + 16500`. -/
theorem absorb_cost (hP : Includes P absorb.c329.costDeps) (sp : Sponge) (x : E) (tag : ℕ)
    (h : SpOk sp) :
    machineCost P absorb.c329.costIdx [πVal, encodeValue sp, encodeValue x, encodeValue tag] ≤
      B + 16500 := by
  rw [absorb.c329.costEq P hP π πVal hπ, limbs_of_lt (by have := h.1; omega : sp.pending.length < 2 ^ 64),
    limbs_of_lt (by unfold rateScalars; norm_num : rateScalars < 2 ^ 64)]
  have h1 := length_cost P (by includes) sp.pending (by have := h.1; omega)
  have h0 := h.1
  have hr : rateScalars = 4 := rfl
  have hlam : ∀ (o : Option Sponge), (∀ a, o = some a → a.pending.length ≤ 4) →
      machineCost P Auto.Option.bind.c47.costIdx [encodeValue o,
        .closure absorb.c329.lam0.costIdx [encodeValue x, encodeValue tag]] ≤ 77 := by
    intro o ho
    have := bind_le P (by includes) _ (.closure absorb.c329.lam0.costIdx [encodeValue x, encodeValue tag])
      (fun a ↦ RunsApp.of_spec (absorb.c329.lam0.costSpec P (by includes) x tag a)) o 71
      (fun a ha ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          absorb.c329.lam0.costEq P (by includes)]
        have := append_cost P (by includes) a.pending [(x, tag)]
        have := ho a ha
        simp only [List.length_cons, List.length_nil]
        omega)
    omega
  split_ifs with hl
  · have h2 := duplex_cost P π πVal hπ B hB (by includes) sp h
    have h3 := hlam (duplex π sp) (fun a ha ↦ by rw [(duplex_some ha).1]; simp)
    omega
  · have h3 := hlam (pure sp) (fun a ha ↦ by cases ha; exact h.1)
    omega

include hπ hB in
/-- **A challenge squeezed** (`squeeze.c339`): `B + 16400`. -/
theorem squeeze_cost (hP : Includes P squeeze.c339.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P squeeze.c339.costIdx [πVal, encodeValue sp] ≤ B + 16400 := by
  rw [squeeze.c339.costEq P hP π πVal hπ]
  cases hg : sp.ground with
  | some g => dsimp only; omega
  | none =>
    dsimp only
    have h1 := duplex_cost P π πVal hπ B hB (by includes) sp h
    have h2 := bind_cost P (by includes) _ (.closure squeeze.c339.lam0.costIdx [])
      (fun d ↦ RunsApp.of_spec (squeeze.c339.lam0.costSpec P (by includes) d)) 20
      (fun d ↦ by
        rw [appCost_fn, List.nil_append, squeeze.c339.lam0.costEq P (by includes)]
        rfl) (duplex π sp)
    omega

include hπ hB in
/-- **A grinding nonce absorbed and permuted** (`absorbNonce.c361`): `2·B + 33000`. -/
theorem absorbNonce_cost (hP : Includes P absorbNonce.c361.costDeps) (sp : Sponge) (n : E)
    (h : SpOk sp) :
    machineCost P absorbNonce.c361.costIdx [πVal, encodeValue sp, encodeValue n] ≤
      2 * B + 33000 := by
  rw [absorbNonce.c361.costEq P hP π πVal hπ]
  have h1 := absorb_cost P π πVal hπ B hB (by includes) sp n dsPowNonce h
  have h2 := bind_le P (by includes) _ (.closure absorbNonce.c361.lam0.costIdx [πVal])
    (fun a ↦ RunsApp.of_spec (absorbNonce.c361.lam0.costSpec P (by includes) π πVal hπ a))
    (LeanVM.Protocol.Compile.absorb π sp n dsPowNonce) (B + 16400)
    (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, absorbNonce.c361.lam0.costEq P (by includes) π πVal hπ]
      have := duplex_cost P π πVal hπ B hB (by includes) a
        (absorb_ok h (by unfold dsPowNonce; norm_num) ha)
      have := bind_cost P (by includes) _ (.closure absorbNonce.c361.lam0.lam0.costIdx [])
        (fun d ↦ RunsApp.of_spec (absorbNonce.c361.lam0.lam0.costSpec P (by includes) d)) 34
        (fun d ↦ by
          rw [appCost_fn, List.nil_append, absorbNonce.c361.lam0.lam0.costEq P (by includes)]
          rfl) (duplex π a)
      simp only [List.length_singleton]
      omega)
  omega

end Perm

end Sponge

section Packed

open LeanVM.Protocol.Compile
open LeanVM.Cost.Auto.LeanVM.Protocol.Compile

/-! ### Packed absorptions and draws -/

/-- A packed permutation's input (`packedInput.c348`), at most eight scalars: at most `19000`. -/
theorem packedInput_cost (hP : Includes P packedInput.c348.costDeps) (st : LeanVM.Semantics.KeccakState)
    (chunk : List E) (hc : chunk.length ≤ 8) :
    machineCost P packedInput.c348.costIdx [encodeValue st, encodeValue chunk] ≤ 19000 := by
  rw [packedInput.c348.costEq P hP, ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := 25) (by norm_num) _
    (.closure packedInput.c348.lam0.costIdx [encodeValue st, encodeValue chunk])
    (fun j ↦ RunsApp.of_spec (packedInput.c348.lam0.costSpec P (by includes) st chunk j)) 730
    (fun j ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        packedInput.c348.lam0.costEq P (by includes), limbs_of_lt (by omega : (j : ℕ) < 2 ^ 64)]
      simp only [List.length_cons, List.length_nil]
      split_ifs with hj
      · have h1 := map_cost P (by includes) _ (.closure packedInput.c348.lam0.lam0.costIdx [])
          (fun x ↦ RunsApp.of_spec (packedInput.c348.lam0.lam0.costSpec P (by includes) x)) 11 chunk
          (fun x _ ↦ by
            rw [appCost_fn, List.nil_append, packedInput.c348.lam0.lam0.costEq P (by includes)]
            simp)
        have h2 := flatten_map_cost P (by includes) 2 (fun x : E ↦ [(x.limb 0).lane, (x.limb 1).lane])
          chunk (fun _ _ ↦ by simp)
        have h3 := getD_cost_idx P (by includes)
          (chunk.flatMap fun x : E ↦ [(x.limb 0).lane, (x.limb 1).lane]) j 0 (by omega)
        omega
      · omega) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at this
  omega

theorem digestOfScalars_cost (hP : Includes P Extractor.digestOfScalarsC.costDeps) (s : E × E) :
    machineCost P Extractor.digestOfScalarsC.costIdx [encodeValue s] ≤ 44 := by
  rw [Extractor.digestOfScalarsC.costEq P hP]; omega

theorem observePacked_ok {π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState}
    {sp sp' : Sponge} {vs : List E} (h : SpOk sp) (he : observePacked π sp vs = some sp') :
    SpOk sp' := by
  unfold observePacked at he
  simp only [bind, pure] at he
  split_ifs at he with hp
  · simp only [Option.bind_some] at he
    rcases ha : absorbPackedChunks π vs.length sp.state vs with _ | a
    · simp [ha] at he
    · simp only [ha, Option.bind_some, Option.some.injEq] at he
      subst he
      exact h
  · obtain ⟨d, hd, he⟩ := Option.bind_eq_some_iff.mp he
    rcases ha : absorbPackedChunks π vs.length d.state vs with _ | a
    · simp [ha] at he
    · simp only [ha, Option.bind_some, Option.some.injEq] at he
      subst he
      exact ⟨by simp [(duplex_some hd).1], by simp [(duplex_some hd).1]⟩

theorem squeezePackedChunks_ok
    {π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState} :
    ∀ (fuel : ℕ) (sp : Sponge) (m : ℕ) (c : List E × Sponge), SpOk sp →
      squeezePackedChunks π fuel sp m = some c → SpOk c.2
  | 0, sp, m, c, h, he => by
    simp only [squeezePackedChunks, pure] at he
    cases he
    exact h
  | k + 1, sp, 0, c, h, he => by
    simp only [squeezePackedChunks, pure] at he
    cases he
    exact h
  | k + 1, sp, j + 1, c, h, he => by
    simp only [squeezePackedChunks, bind, pure] at he
    obtain ⟨d, hd, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨r, hr, he⟩ := Option.bind_eq_some_iff.mp he
    have hd' : SpOk d := ⟨by simp [(duplex_some hd).1], by simp [(duplex_some hd).1]⟩
    have := squeezePackedChunks_ok k d _ r hd' hr
    obtain ⟨r1, r2⟩ := r
    cases he
    exact this

theorem samplesPacked_ok {π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState}
    {sp : Sponge} {n : ℕ} {c : List E × Sponge} (h : SpOk sp) (he : samplesPacked π sp n = some c) :
    SpOk c.2 := by
  unfold samplesPacked at he
  rcases n with _ | k
  · simp only [bind, pure] at he
    obtain ⟨⟨r1, r2⟩, hr, he⟩ := Option.bind_eq_some_iff.mp he
    cases he
    exact squeezePackedChunks_ok _ _ _ _ h hr
  · rcases hg : sp.ground with _ | g
    · simp only [hg, bind, pure] at he
      obtain ⟨⟨r1, r2⟩, hr, he⟩ := Option.bind_eq_some_iff.mp he
      cases he
      exact squeezePackedChunks_ok _ _ _ _ h hr
    · simp only [hg, bind, pure] at he
      obtain ⟨⟨r1, r2⟩, hr, he⟩ := Option.bind_eq_some_iff.mp he
      cases he
      exact squeezePackedChunks_ok _ { state := sp.state, pending := sp.pending } _ (r1, r2) h hr

section Perm2

variable (π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (πVal : MachineValue)
  (hπ : ∀ a, RunsApp P πVal [encodeValue a] (encodeValue (π a))) (B : ℕ)
  (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P πVal [encodeValue a] ≤ B)

include hπ hB in
/-- **Packed absorption's loop** (`absorbPackedChunks.c346`): a permutation and `20000` per
scalar at most. -/
theorem absorbPackedChunks_cost (hP : Includes P absorbPackedChunks.c346.costDeps) :
    ∀ (fuel : ℕ) (st : LeanVM.Semantics.KeccakState) (vs : List E), fuel < 2 ^ 64 →
      machineCost P absorbPackedChunks.c346.costIdx [πVal, encodeValue fuel, encodeValue st,
        encodeValue vs] ≤ vs.length * (B + 20000) + 15
  | 0, st, vs, _ => by
    rw [absorbPackedChunks.c346.costEq P hP π πVal hπ, limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64)]
    simp
  | k + 1, st, [], h => by
    rw [absorbPackedChunks.c346.costEq P hP π πVal hπ, limbs_of_lt h]
    simp
  | k + 1, st, x :: xs, h => by
    rw [absorbPackedChunks.c346.costEq P hP π πVal hπ, limbs_of_lt h]
    dsimp only
    have h1 := take_cost P (by includes) 8 (x :: xs) (by norm_num)
    have h2 := packedInput_cost P (by includes) st ((x :: xs).take 8) (by simp)
    have h3 := hB (packedInput st ((x :: xs).take 8))
    have h4 := bind_cost P (by includes) _
      (.closure 347 [encodeValue x, encodeValue xs, encodeValue k, πVal])
      (fun s ↦ RunsApp.of_spec (absorbPackedChunks.c346.lam0.costSpec P (by includes) x xs k π πVal hπ s))
      (xs.length * (B + 20000) + 160)
      (fun s ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
          List.nil_append, show (347 : ℕ) = absorbPackedChunks.c346.lam0.costIdx from rfl,
          absorbPackedChunks.c346.lam0.costEq P (by includes) x xs k π πVal hπ]
        have e1 := drop_cost P (by includes) 8 (x :: xs) (by norm_num)
        have e2 := absorbPackedChunks_cost hP k s ((x :: xs).drop 8) (by omega)
        have hl : ((x :: xs).drop 8).length ≤ xs.length := by
          simp only [List.length_drop, List.length_cons]; omega
        have e3 := Nat.mul_le_mul_right (B + 20000) hl
        simp only [List.length_cons, List.length_nil]
        omega)
      (π (packedInput st ((x :: xs).take 8)))
    have e : (xs.length + 1) * (B + 20000) = xs.length * (B + 20000) + B + 20000 := by ring
    simp only [List.length_cons]
    omega

include hπ hB in
/-- **A packed absorption** (`observePacked.c343`): a permutation and `20000` per scalar, and one
more. -/
theorem observePacked_cost (hP : Includes P observePacked.c343.costDeps) (sp : Sponge) (vs : List E)
    (h : SpOk sp) (hv : vs.length < 2 ^ 60) :
    machineCost P observePacked.c343.costIdx [πVal, encodeValue sp, encodeValue vs] ≤
      (vs.length + 1) * (B + 20010) := by
  have hlam : ∀ s : Sponge, appCost P (.closure observePacked.c343.lam0.costIdx [πVal, encodeValue vs])
      [encodeValue s] ≤ vs.length * (B + 20000) + 8 * vs.length + 60 := by
    intro s
    rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
      observePacked.c343.lam0.costEq P (by includes) π πVal hπ]
    have h1 := length_cost P (by includes) vs (by omega)
    have h2 := absorbPackedChunks_cost P π πVal hπ B hB (by includes) vs.length s.state vs (by omega)
    have h3 := bind_cost P (by includes) _ (.closure observePacked.c343.lam0.lam0.costIdx [encodeValue s])
      (fun st ↦ RunsApp.of_spec (observePacked.c343.lam0.lam0.costSpec P (by includes) s st)) 12
      (fun st ↦ by
        rw [appCost_fn, List.cons_append, List.nil_append,
          observePacked.c343.lam0.lam0.costEq P (by includes)]
        simp)
      (absorbPackedChunks π vs.length s.state vs)
    simp only [List.length_cons, List.length_nil]
    omega
  have hb : ∀ o : Option Sponge, machineCost P Auto.Option.bind.c47.costIdx
      [encodeValue o, .closure observePacked.c343.lam0.costIdx [πVal, encodeValue vs]] ≤
        vs.length * (B + 20000) + 8 * vs.length + 66 := fun o ↦
    bind_cost P (by includes) _ (.closure observePacked.c343.lam0.costIdx [πVal, encodeValue vs])
      (fun s ↦ RunsApp.of_spec (observePacked.c343.lam0.costSpec P (by includes) π πVal hπ vs s)) _
      hlam o
  rw [observePacked.c343.costEq P hP π πVal hπ]
  have hd := duplex_cost P π πVal hπ B hB (by includes) sp h
  have hb1 := hb (pure sp)
  have hb2 := hb (duplex π sp)
  have e : (vs.length + 1) * (B + 20010) = vs.length * (B + 20000) + 10 * vs.length + B + 20010 := by
    ring
  rcases hq : sp.pending with _ | ⟨p, ps⟩ <;>
    simp only [List.isEmpty_nil, List.isEmpty_cons, ↓reduceIte, Bool.false_eq_true] <;> omega

include hπ hB in
/-- **The packed draws' loop** (`squeezePackedChunks.c356`): a permutation and `20000` per
challenge at most. -/
theorem squeezePackedChunks_cost (hP : Includes P squeezePackedChunks.c356.costDeps) :
    ∀ (fuel : ℕ) (sp : Sponge) (m : ℕ), fuel < 2 ^ 60 → m < 2 ^ 60 → SpOk sp →
      machineCost P squeezePackedChunks.c356.costIdx [πVal, encodeValue fuel, encodeValue sp,
        encodeValue m] ≤ m * (B + 20000) + 20
  | 0, sp, m, _, hm, _ => by
    rw [squeezePackedChunks.c356.costEq P hP π πVal hπ, limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64)]
    simp
  | k + 1, sp, 0, hk, _, _ => by
    rw [squeezePackedChunks.c356.costEq P hP π πVal hπ, limbs_of_lt (by omega : k + 1 < 2 ^ 64),
      limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64)]
    simp
  | k + 1, sp, j + 1, hk, hj, h => by
    rw [squeezePackedChunks.c356.costEq P hP π πVal hπ, limbs_of_lt (by omega : k + 1 < 2 ^ 64),
      limbs_of_lt (by omega : j + 1 < 2 ^ 64)]
    dsimp only
    have h1 := duplex_cost P π πVal hπ B hB (by includes) sp h
    have h2 := bind_le P (by includes) _
      (.closure 359 [encodeValue j, encodeValue k, πVal])
      (fun s ↦ RunsApp.of_spec (squeezePackedChunks.c356.lam2.costSpec P (by includes) j k π πVal hπ s))
      (duplex π sp) (j * (B + 20000) + 1000)
      (fun s hs ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
          show (359 : ℕ) = squeezePackedChunks.c356.lam2.costIdx from rfl,
          squeezePackedChunks.c356.lam2.costEq P (by includes) j k π πVal hπ]
        have hs' : SpOk s := ⟨by simp [(duplex_some hs).1], by simp [(duplex_some hs).1]⟩
        have e1 := rangeLoop_cost P (by includes) (min 8 (j + 1)) [] (by omega)
        have e2 := map_cost P (by includes) _
          (.closure squeezePackedChunks.c356.lam0.costIdx [encodeValue s.state])
          (fun i ↦ RunsApp.of_spec (squeezePackedChunks.c356.lam0.costSpec P (by includes) s.state i)) 40
          (List.range (min 8 (j + 1))) (fun i hi ↦ by
            have : i < 8 := by simp only [List.mem_range] at hi; omega
            rw [appCost_fn, List.cons_append, List.nil_append,
              squeezePackedChunks.c356.lam0.costEq P (by includes),
              packedChallengeOf.c354.costEq P (by includes)]
            simp (disch := omega) only [limbs_of_lt, List.length_cons, List.length_nil, max_self]
            omega)
        have e3 := squeezePackedChunks_cost hP k s (j + 1 - min 8 (j + 1)) (by omega) (by omega) hs'
        have e4 := bind_cost P (by includes) _
          (.closure squeezePackedChunks.c356.lam1.costIdx
            [encodeValue ((List.range (min 8 (j + 1))).map (packedChallengeOf s.state)),
              encodeValue (min 8 (j + 1))])
          (fun c ↦ RunsApp.of_spec (squeezePackedChunks.c356.lam1.costSpec P (by includes) _ _ c)) 120
          (fun c ↦ by
            rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
              squeezePackedChunks.c356.lam1.costEq P (by includes)]
            obtain ⟨a, b⟩ := c
            have := append_cost P (by includes)
              ((List.range (min 8 (j + 1))).map (packedChallengeOf s.state)) a
            simp only [List.length_map, List.length_range, List.length_cons, List.length_nil] at this ⊢
            omega) (squeezePackedChunks π k s (j + 1 - min 8 (j + 1)))
        have e5 := Nat.mul_le_mul_right (B + 20000) (show j + 1 - min 8 (j + 1) ≤ j by omega)
        simp only [List.length_range, List.length_cons, List.length_nil] at *
        simp (disch := omega) only [limbs_of_lt, max_self]
        split_ifs <;> omega)
    have e : (j + 1) * (B + 20000) = j * (B + 20000) + B + 20000 := by ring
    omega

include hπ hB in
/-- **Packed draws** (`samplesPacked.c352`): a permutation and `20000` per challenge, and one
more. -/
theorem samplesPacked_cost (hP : Includes P samplesPacked.c352.costDeps) (sp : Sponge) (n : ℕ)
    (h : SpOk sp) (hn : n < 2 ^ 60) :
    machineCost P samplesPacked.c352.costIdx [πVal, encodeValue sp, encodeValue n] ≤
      (n + 1) * (B + 20000) := by
  have hbind : ∀ (fst : List E) (o : Option (List E × Sponge)), fst.length ≤ 7 →
      machineCost P Auto.Option.bind.c47.costIdx
        [encodeValue o, .closure samplesPacked.c352.lam1.costIdx [encodeValue fst]] ≤ 110 := by
    intro fst o hf
    have := bind_cost P (by includes) _ (.closure samplesPacked.c352.lam1.costIdx [encodeValue fst])
      (fun c ↦ RunsApp.of_spec (samplesPacked.c352.lam1.costSpec P (by includes) fst c)) 100
      (fun c ↦ by
        rw [appCost_fn, List.cons_append, List.nil_append, samplesPacked.c352.lam1.costEq P (by includes)]
        obtain ⟨a, b⟩ := c
        have := append_cost P (by includes) fst a
        simp only [List.length_cons, List.length_nil]
        omega) o
    omega
  have hsq := fun (sp' : Sponge) (m : ℕ) (hm : m ≤ n) (h' : SpOk sp') ↦
    squeezePackedChunks_cost P π πVal hπ B hB (by includes) m sp' m (by omega) (by omega) h'
  have e : (n + 1) * (B + 20000) = n * (B + 20000) + B + 20000 := by ring
  rw [samplesPacked.c352.costEq P hP π πVal hπ]
  rcases n with _ | k
  · simp only [Nat.rec_zero]
    have h1 := hsq sp 0 le_rfl h
    have h2 := hbind [] (squeezePackedChunks π 0 sp 0) (by simp)
    have h3 := length_cost P (by includes) ([] : List E) (by simp)
    simp (disch := omega) only [limbs_of_lt, List.length_nil, Nat.sub_zero, max_self] at *
    omega
  · have hk := Nat.mul_le_mul_right (B + 20000) (show k + 1 - 1 ≤ k + 1 by omega)
    rcases hg : sp.ground with _ | g
    · dsimp only
      have h1 := hsq sp (k + 1) le_rfl h
      have h2 := hbind [] (squeezePackedChunks π (k + 1) sp (k + 1)) (by simp)
      have h3 := length_cost P (by includes) ([] : List E) (by simp)
      simp (disch := omega) only [limbs_of_lt, List.length_nil, Nat.sub_zero, max_self] at *
      omega
    · dsimp only
      have hl : ((List.take k (List.range 6)).map
          (packedChallengeOf sp.state ∘ fun x ↦ x + 2)).length ≤ 6 := by simp
      have h0 := rangeLoop_cost P (by includes) 6 [] (by norm_num)
      have h0' := take_cost_length P (by includes) k (List.range 6) (by omega)
      have h0'' := map_cost P (by includes) _ (.closure samplesPacked.c352.lam0.costIdx [encodeValue sp])
        (fun i ↦ RunsApp.of_spec (samplesPacked.c352.lam0.costSpec P (by includes) sp i)) 30
        (List.take k (List.range 6)) (fun i hi ↦ by
          have : i < 6 := List.mem_range.1 (List.mem_of_mem_take hi)
          rw [appCost_fn, List.cons_append, List.nil_append, samplesPacked.c352.lam0.costEq P (by includes),
            packedChallengeOf.c354.costEq P (by includes)]
          simp (disch := omega) only [limbs_of_lt, List.length_cons, List.length_nil, max_self]
          omega)
      have hlt : (List.take k (List.range 6)).length ≤ 6 := by simp
      set fst := g :: (List.take k (List.range 6)).map (packedChallengeOf sp.state ∘ fun x ↦ x + 2)
        with hfst
      have hfl : fst.length ≤ 7 := by rw [hfst, List.length_cons]; omega
      have h1 := hsq { state := sp.state, pending := sp.pending } (k + 1 - fst.length) (by omega) h
      have h2 := hbind fst (squeezePackedChunks π (k + 1 - fst.length)
        { state := sp.state, pending := sp.pending } (k + 1 - fst.length)) hfl
      have h3 := length_cost P (by includes) fst (by omega)
      have hk2 := Nat.mul_le_mul_right (B + 20000) (show k + 1 - fst.length ≤ k + 1 by omega)
      simp (disch := omega) only [limbs_of_lt, List.length_range, max_self] at *
      omega

end Perm2

end Packed

/-! ## The skeleton's replay -/

section Replay

open LeanVM.Protocol.Compile
open LeanVM.Cost.Auto.LeanVM.Protocol.EndToEnd.Sound

variable (F : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (FVal : MachineValue)
  (hF : ∀ a, RunsApp P FVal [encodeValue a] (encodeValue (F a))) (B : ℕ)
  (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P FVal [encodeValue a] ≤ B)

include hF hB in
/-- **The skeleton's replay** (`skelReplayP.c327`), the permutation's closure at most `B`: per
operation at most two permutations, `34000`, and `11` per root read so far, and a
permutation and `40000` per packed scalar (`R` bounds the roots
and the operations). -/
theorem skelReplay_cost (hP : Includes P Auto.LeanVM.Extraction.AS.skelReplayP.c327.costDeps) (R : ℕ) :
    ∀ (sk : List LeanVM.Protocol.EndToEnd.Sound.Op) (s : VerifierProgramState),
      s.roots.length + sk.length ≤ R → packedSum sk < 2 ^ 60 → SpOk s.sponge →
      machineCost P Auto.LeanVM.Extraction.AS.skelReplayP.c327.costIdx [FVal, encodeValue sk, encodeValue s] ≤
        sk.length * (2 * B + 34000 + 11 * R) + packedSum sk * (B + 40000) + 9 := by
  intro sk
  induction sk with
  | nil => intro s _ _ _; rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.costEq P hP F FVal hF]; simp
  | cons op tail ih =>
    intro s hR hpk hs
    simp only [List.length_cons] at hR ⊢
    have hmul : (tail.length + 1) * (2 * B + 34000 + 11 * R) =
        tail.length * (2 * B + 34000 + 11 * R) + (2 * B + 34000 + 11 * R) := by ring
    have hmap : ∀ (s' : VerifierProgramState),
        machineCost P Auto.Option.map.c90.costIdx [.closure Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam3.costIdx [],
          encodeValue (LeanVM.Extraction.AS.skelReplayP F tail s')] ≤ 23 := by
      intro s'
      have := optionMap_cost P (by includes) _ (.closure Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam3.costIdx [])
        (fun r ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam3.costSpec P (by includes) r)) 15
        (LeanVM.Extraction.AS.skelReplayP F tail s')
        (fun r _ ↦ by rw [appCost_fn, List.nil_append, Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam3.costEq P (by includes)]; rfl)
      omega
    rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.costEq P hP F FVal hF]
    cases op with
    | read =>
      simp only [packedSum] at hpk ⊢
      rcases hst : s.stream with _ | ⟨x, xs⟩
      · dsimp only; omega
      · dsimp only
        rcases hg : s.sponge.ground with _ | g
        · dsimp only
          have h1 := absorb_cost P F FVal hF B hB (by includes) s.sponge x dsObserve hs
          have h2 := bind_le P (by includes) _ (.closure 328 [encodeValue x, encodeValue xs,
              encodeValue tail, FVal, encodeValue s])
            (fun sp ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam0.costSpec P (by includes) x xs tail F FVal
              hF s sp))
            (LeanVM.Protocol.Compile.absorb F s.sponge x dsObserve)
            (tail.length * (2 * B + 34000 + 11 * R) + packedSum tail * (B + 40000) + 9 + 60)
            (fun sp hsp ↦ by
              rw [appCost_fn, show (328 : ℕ) = Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam0.costIdx from rfl]
              simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam0.costEq P (by includes) x xs tail F FVal hF]
              have h3 := ih { sponge := sp, stream := xs, openings := s.openings, roots := s.roots }
                (by dsimp only; omega) hpk (absorb_ok hs (by unfold dsObserve; norm_num) hsp)
              have h4 := optionMap_cost P (by includes) _
                (.closure skelReplayPC.lam0.lam0.costIdx [encodeValue x])
                (fun r ↦ RunsApp.of_spec (skelReplayPC.lam0.lam0.costSpec P (by includes) x r)) 18
                (LeanVM.Extraction.AS.skelReplayP F tail
                  { sponge := sp, stream := xs, openings := s.openings, roots := s.roots })
                (fun r _ ↦ by
                  rw [appCost_fn, List.singleton_append, skelReplayPC.lam0.lam0.costEq P (by includes)]
                  rfl)
              omega)
          omega
        · dsimp only; omega
    | sample =>
      simp only [packedSum] at hpk ⊢
      have h1 := squeeze_cost P F FVal hF B hB (by includes) s.sponge hs
      have h2 := bind_le P (by includes) _ (.closure 338 [encodeValue tail, FVal, encodeValue s])
        (fun c ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam2.costSpec P (by includes) tail F FVal hF s c))
        (LeanVM.Protocol.Compile.squeeze F s.sponge)
        (tail.length * (2 * B + 34000 + 11 * R) + packedSum tail * (B + 40000) + 9 + 60)
        (fun c hc ↦ by
          rw [appCost_fn, show (338 : ℕ) = Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam2.costIdx from rfl]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam2.costEq P (by includes) tail F FVal hF]
          have h3 := ih { sponge := c.2, stream := s.stream, openings := s.openings, roots := s.roots }
            (by dsimp only; omega) hpk (squeeze_ok hs hc)
          have h4 := optionMap_cost P (by includes) _
            (.closure Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam1.costIdx [encodeValue c])
            (fun r ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam1.costSpec P (by includes) c r)) 19
            (LeanVM.Extraction.AS.skelReplayP F tail
              { sponge := c.2, stream := s.stream, openings := s.openings, roots := s.roots })
            (fun r _ ↦ by
              rw [appCost_fn, List.singleton_append, Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam1.costEq P (by includes)]
              rfl)
          omega)
      omega
    | readPacked n =>
      simp only [packedSum] at hpk ⊢
      have hlt : (s.stream.take n).length ≤ n := by simp
      have h1 := take_cost P (by includes) n s.stream (by omega)
      have h2 := length_cost P (by includes) (s.stream.take n) (by omega)
      have hl1 : limbCount (s.stream.take n).length = 1 := limbs_of_lt (by omega)
      have hl2 : limbCount n = 1 := limbs_of_lt (by omega)
      have h3 := observePacked_cost P F FVal hF B hB (by includes) s.sponge (s.stream.take n) hs
        (by omega)
      have h4 := bind_le P (by includes) _
        (.closure 342 [encodeValue n, encodeValue tail, FVal, encodeValue s])
        (fun sp ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam4.costSpec P (by includes) n tail F FVal hF s sp))
        (observePacked F s.sponge (s.stream.take n))
        (tail.length * (2 * B + 34000 + 11 * R) + packedSum tail * (B + 40000) + 9 + 15 * n + 60)
        (fun sp hsp ↦ by
          rw [appCost_fn, show (342 : ℕ) = Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam4.costIdx from rfl]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam4.costEq P (by includes) n tail F FVal hF]
          have := drop_cost P (by includes) n s.stream (by omega)
          have := ih
            { sponge := sp, stream := s.stream.drop n, openings := s.openings, roots := s.roots }
            (by dsimp only; omega) (by omega) (observePacked_ok hs hsp)
          have := hmap
            { sponge := sp, stream := s.stream.drop n, openings := s.openings, roots := s.roots }
          omega)
      have e1 : (n + packedSum tail) * (B + 40000) = n * (B + 40000) + packedSum tail * (B + 40000) := by
        ring
      have e2 : ((s.stream.take n).length + 1) * (B + 20010) =
          (s.stream.take n).length * (B + 20000) + 10 * (s.stream.take n).length + B + 20010 := by ring
      have e3 := Nat.mul_le_mul_right (B + 20000) hlt
      have e4 : n * (B + 40000) = n * (B + 20000) + 20000 * n := by ring
      rcases hg : s.sponge.ground with _ | g <;>
        simp only [Option.isNone_none, Option.isNone_some, true_and, Bool.false_eq_true, false_and,
          ↓reduceIte] <;> (try split_ifs) <;> omega
    | samplePacked n =>
      simp only [packedSum] at hpk ⊢
      have h3 := samplesPacked_cost P F FVal hF B hB (by includes) s.sponge n hs (by omega)
      have h4 := bind_le P (by includes) _ (.closure 351 [encodeValue tail, FVal, encodeValue s])
        (fun c ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam5.costSpec P (by includes) tail F FVal hF s c))
        (samplesPacked F s.sponge n)
        (tail.length * (2 * B + 34000 + 11 * R) + packedSum tail * (B + 40000) + 9 + 60)
        (fun c hc ↦ by
          rw [appCost_fn, show (351 : ℕ) = Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam5.costIdx from rfl]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam5.costEq P (by includes) tail F FVal hF]
          have := ih { sponge := c.2, stream := s.stream, openings := s.openings, roots := s.roots }
            (by dsimp only; omega) (by omega) (samplesPacked_ok hs hc)
          have := hmap { sponge := c.2, stream := s.stream, openings := s.openings, roots := s.roots }
          omega)
      have e1 : (n + packedSum tail) * (B + 40000) = n * (B + 40000) + packedSum tail * (B + 40000) := by
        ring
      have e2 : (n + 1) * (B + 20000) = n * (B + 20000) + B + 20000 := by ring
      have e4 : n * (B + 40000) = n * (B + 20000) + 20000 * n := by ring
      omega
    | grind bits =>
      simp only [packedSum] at hpk ⊢
      rcases hst : s.stream with _ | ⟨x, xs⟩
      · dsimp only; omega
      · dsimp only
        rcases hg : s.sponge.ground with _ | g
        · dsimp only
          have h1 := absorbNonce_cost P F FVal hF B hB (by includes) s.sponge x hs
          have h2 := bind_le P (by includes) _ (.closure 360 [encodeValue xs, encodeValue tail, FVal,
              encodeValue s])
            (fun c ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam6.costSpec P (by includes) xs tail F FVal hF
              s c))
            (LeanVM.Protocol.Compile.absorbNonce F s.sponge x)
            (tail.length * (2 * B + 34000 + 11 * R) + packedSum tail * (B + 40000) + 9 + 60)
            (fun c hc ↦ by
              rw [appCost_fn, show (360 : ℕ) = Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam6.costIdx from rfl]
              simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam6.costEq P (by includes) xs tail F FVal hF]
              have h3 := ih { sponge := c.2, stream := xs, openings := s.openings, roots := s.roots }
                (by dsimp only; omega) hpk (absorbNonce_ok hc)
              have h4 := hmap { sponge := c.2, stream := xs, openings := s.openings, roots := s.roots }
              omega)
          omega
        · dsimp only; omega
    | commit height width =>
      simp only [packedSum] at hpk ⊢
      rcases hst : s.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only
        rcases hg : s.sponge.ground with _ | g
        · dsimp only
          have h1 := absorb_cost P F FVal hF B hB (by includes) s.sponge x0 dsObserve hs
          have h2 := bind_le P (by includes) _ (.closure 365 [encodeValue x1, encodeValue xs,
              encodeValue x0, encodeValue height, encodeValue width, encodeValue tail, FVal,
              encodeValue s])
            (fun sp ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam8.costSpec P (by includes) x1 xs x0 height
              width tail F FVal hF s sp))
            (LeanVM.Protocol.Compile.absorb F s.sponge x0 dsObserve)
            (tail.length * (2 * B + 34000 + 11 * R) + packedSum tail * (B + 40000) + 9 + B + 16700 + 11 * s.roots.length)
            (fun sp0 hsp0 ↦ by
              rw [appCost_fn, show (365 : ℕ) = Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam8.costIdx from rfl]
              simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam8.costEq P (by includes) x1 xs x0 height width tail F FVal hF]
              have hok0 := absorb_ok hs (by unfold dsObserve; norm_num) hsp0
              have h3 := absorb_cost P F FVal hF B hB (by includes) sp0 x1 dsObserve hok0
              have h4 := bind_le P (by includes) _ (.closure Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam7.costIdx
                  [encodeValue x1, encodeValue xs, encodeValue x0, encodeValue height,
                    encodeValue width, encodeValue tail, FVal, encodeValue s])
                (fun sp ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam7.costSpec P (by includes) x1 xs x0
                  height width tail F FVal hF s sp))
                (LeanVM.Protocol.Compile.absorb F sp0 x1 dsObserve)
                (tail.length * (2 * B + 34000 + 11 * R) + packedSum tail * (B + 40000) + 9 + 130 + 11 * s.roots.length)
                (fun sp1 hsp1 ↦ by
                  rw [appCost_fn]
                  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
                  rw [Auto.LeanVM.Extraction.AS.skelReplayP.c327.lam7.costEq P (by includes) x1 xs x0 height width tail F FVal hF]
                  have h5 := digestOfScalars_cost P (by includes) (x0, x1)
                  have h6 := append_cost P (by includes) s.roots
                    [(LeanVM.Protocol.KeccakHash.digestFromHalves (x0, x1), height, width)]
                  have h7 := ih
                    { sponge := sp1, stream := xs, openings := s.openings,
                      roots := s.roots ++
                        [(LeanVM.Protocol.KeccakHash.digestFromHalves (x0, x1), height, width)] }
                    (by dsimp only; simp only [List.length_append, List.length_singleton]; omega)
                    hpk (absorb_ok hok0 (by unfold dsObserve; norm_num) hsp1)
                  have h8 := hmap
                    { sponge := sp1, stream := xs, openings := s.openings,
                      roots := s.roots ++
                        [(LeanVM.Protocol.KeccakHash.digestFromHalves (x0, x1), height, width)] }
                  omega)
              omega)
          have hr : 11 * s.roots.length ≤ 11 * R := by omega
          omega
        · dsimp only; omega
    | query =>
      simp only [packedSum] at hpk ⊢
      rcases ho : s.openings with _ | ⟨ph, os⟩
      · dsimp only; omega
      · dsimp only
        have h3 := ih { sponge := s.sponge, stream := s.stream, openings := os, roots := s.roots }
          (by dsimp only; omega) hpk hs
        have h4 := hmap { sponge := s.sponge, stream := s.stream, openings := os, roots := s.roots }
        omega

end Replay

end

end LeanVM.Cost.Bounds.AS
