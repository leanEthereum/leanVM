module

public import LeanVM.Cost.AS.Bounds.Newton
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.AS.Forward
import all Statement.Field
import LeanVM.Protocol.Extraction.AS.TraceShape
public meta import Lean.Elab.Tactic

/-!
# Bounds: the agreement-set extractor's replay

* the first forward answers' map (keys of `25` words, values Keccak states): `searchFwd_cost`,
  `mergeNewerFwd_cost`, `carryFwd_amortized`, `getFwd_cost`;
* **`fwdIndex_cost`**: the index of `N ≤ 2^D` queries, `(fwdStepPrice D W + 14)·N + 9`;
  **`fwdF_cost`**: a lookup in a good map,
  `fwdLookupPrice D W`;
* `keccakIdx_cost`: Keccak-256 of `L` bytes through the index, `L/136 + 1` blocks of a lookup and
  `430004`, and `8·L + 85`; **`extractSeed_cost`**: the seed of a bytecode of `n` words
  (`extractLC`'s, its hash closure over the index built once);
* the sponge (`absorb_cost`, `squeeze_cost`, `absorbNonce_cost`, at most four scalars waiting:
  `SpOk`) and **`skelReplay_cost`**: the skeleton's replay, per operation two lookups, `34000` and
  `11` per root;
* a tactic, `cost_calls [L₁, …]` / `len_facts [L₁, …]`, adding the bounds of a goal's list
  primitives and of named callees, and the lengths the lemmas bound;
* the skeletons' builders (`skSum_cost`, `skGkrLayers_cost`, `skBus_cost`, `skKeccak_cost`,
  `skTablePhaseL_cost`, `pushDepthL_cost`, `skLevels_cost` by `skLevelsPrice`, …), the ladders'
  facts at every admissible shape by the kernel (`ladder_facts`, `ladder_dec`), and at an
  admissible layout (`LayOk`) **`length_skBodyL`** (`≤ 40000`), **`skBodyL_cost`** (`≤ 10^9`);
* the decoders: `decLevelsP_cost` by `decLevelsPrice`, `decWhirCutP_cost`, **`decBodyL_cost`**
  (`≤ 1001400000`, whatever the events), **`decSizesL_cost`** (`80·n + 8·|bytecode| + 977124100`).
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
/-- The binary search of a word list `k` (`searchIn.c417`). -/
theorem searchFwd_cost (hP : Includes P searchIn.c417.costDeps)
    (t : Array FwdEntry) (k : List UInt64) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c417.costIdx [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] ≤
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
    (fun x ↦ machineCost P searchIn.c417.costIdx [encodeValue t, encodeValue k, encodeValue x.1,
      encodeValue x.2])
    (40 + 26 * k.length + 9 * W) (40 + 26 * k.length + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c417.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    limbs_bound hW
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c417.costEq P hP]
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
/-- `mergeNewer` on word-list keys (`mergeNewer.c421`): at most `26·L + 33` per entry and `3`. -/
theorem mergeNewerFwd_cost (hP : Includes P mergeNewer.c421.costDeps) (L : ℕ) :
    ∀ (n : ℕ) (a b : List FwdEntry), a.length + b.length = n →
      (∀ e ∈ b, WordsKey L e.1) →
      machineCost P mergeNewer.c421.costIdx [encodeValue a, encodeValue b] ≤ (26 * L + 33) * n + 3 := by
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
  | nil => rw [mergeNewer.c421.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c421.costEq_cons P hP]
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
/-- Two levels merged (`Level.merge.c420`): at most `26·L + 37` per entry and `18`. -/
theorem levelMergeFwd_cost (hP : Includes P Level.merge.c420.costDeps) (L : ℕ)
    (l l' : Level (List UInt64) LeanVM.Semantics.KeccakState) (hQ : KeysIn (WordsKey L) [l, l'])
    (W : ℕ) (hw : limbCount l.weight ≤ W) (hw' : limbCount l'.weight ≤ W)
    (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P Level.merge.c420.costIdx [encodeValue l, encodeValue l'] ≤
      18 + W + (26 * L + 37) * (l.entries.size + l'.entries.size) := by
  rw [Level.merge.c420.costEq P hP]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) ≤ W :=
    max_le hws (max_le hw hw')
  have hm := mergeNewerFwd_cost P (by includes) L _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the first forward answers' map, amortized** (`carry.c419`). -/
theorem carryFwd_amortized (hP : Includes P carry.c419.costDeps) (L D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hm : smGood m)
    (hQ : KeysIn (WordsKey L) m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level (List UInt64) LeanVM.Semantics.KeccakState) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, WordsKey L e.1) :
    machineCost P carry.c419.costIdx [encodeValue l, encodeValue m.levels] +
        (26 * L + 37) * potential D (carry l m.levels) ≤
      (26 * L + 37) * potential D m.levels + (26 * L + 37) * D + (32 + 2 * W) * (m.levels.length + 1) := by
  refine insert_amortized (WordsKey L)
    (fun l ls ↦ machineCost P carry.c419.costIdx [encodeValue l, encodeValue ls])
    (32 + 2 * W) (26 * L + 37) D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c419.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c419.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeFwd_cost P (by includes) L l l' hQ2 W (hW _ (by omega)) (hW _ (by omega))
      (hW _ (by omega))
    rw [carry.c419.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the first forward answers' map (`SortedMap.get?.c415`): a binary search per level. -/
theorem getFwd_cost (hP : Includes P SortedMap.get?.c415.costDeps)
    (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (H W : ℕ)
    (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (k : List UInt64) :
    machineCost P SortedMap.get?.c415.costIdx [encodeValue m, encodeValue k] ≤
      m.levels.length * (20 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.closure SortedMap.get?.c415.lam0.costIdx [encodeValue k])
      [encodeValue l] ≤ 9 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.length_singleton, List.singleton_append,
      SortedMap.get?.c415.lam0.costEq P (by includes)]
    have := searchFwd_cost P (by includes) l.entries k H W hW (hm l hl)
      0 l.entries.size (by omega) (hm l hl)
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : (40 + 26 * k.length + 9 * W) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _
    (.closure SortedMap.get?.c415.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (SortedMap.get?.c415.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [SortedMap.get?.c415.costEq P hP]
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

theorem fwdGet_le (hP : Includes P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c415.costDeps)
    (D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hg : smGood m)
    (hN : smWeightSum m < 2 ^ D) (k : List UInt64) (hk : k.length = 25) :
    machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c415.costIdx
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
    rw [Auto.LeanVM.Extraction.Fast.insertIfNew.c414.costEq P (by includes)]
    unfold fwdStepPrice
    by_cases hc : m.contains x.toList = true
    · simp only [insertIfNew, hc, ↓reduceIte]
      refine ⟨⟨hg, hQ, by omega⟩, ?_⟩
      generalize m.get? x.toList = o
      cases o <;> dsimp only <;> nlinarith
    · simp only [insertIfNew, hc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2⟩ := smGood_insert hg x.toList y
      refine ⟨⟨h1, keysIn_insert hQ (show WordsKey 25 x.toList from hx.le) y, by omega⟩, ?_⟩
      rw [Auto.LeanVM.Extraction.Fast.SortedMap.insert.c418.costEq P (by includes)]
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
/-- A lane of a block (`littleEndianLane.c431`), lane `i < 17`: at most `16778`. -/
theorem littleEndianLane_cost (hP : Includes P littleEndianLane.c431.costDeps) (bytes : List UInt8)
    (i : ℕ) (hi : i < 17) :
    machineCost P littleEndianLane.c431.costIdx [encodeValue bytes, encodeValue i] ≤ 16778 := by
  rw [littleEndianLane.c431.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) 8 [] (by norm_num)
  have h2 := listFoldl_le P (by includes) _
    (.closure littleEndianLane.c431.lam0.costIdx [encodeValue bytes, encodeValue i])
    (fun acc k ↦ RunsApp.of_spec (littleEndianLane.c431.lam0.costSpec P (by includes) bytes i acc k))
    2069 (fun _ ↦ True) (List.range 8) 0 trivial (fun acc _ k hk ↦ by
      refine ⟨trivial, ?_⟩
      have hk8 := List.mem_range.1 hk
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        littleEndianLane.c431.lam0.costEq P (by includes),
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
/-- **One block absorbed** (`absorbBlockWith.c429`): at most the permutation's price `B` and
`420300`. -/
theorem absorbBlockWith_cost (hP : Includes P absorbBlockWith.c429.costDeps)
    (π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (πVal : MachineValue)
    (hπ : ∀ a, RunsApp P πVal [encodeValue a] (encodeValue (π a))) (B : ℕ)
    (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P πVal [encodeValue a] ≤ B) (s : LeanVM.Semantics.KeccakState)
    (block : List UInt8) :
    machineCost P absorbBlockWith.c429.costIdx [πVal, encodeValue s, encodeValue block] ≤
      B + 420300 := by
  rw [absorbBlockWith.c429.costEq P hP π πVal hπ, ofFnFrom_length]
  have h1 := ofFnFrom_cost P (by includes) (n := 25) (by norm_num) _
    (.closure absorbBlockWith.c429.lam0.costIdx [encodeValue s, encodeValue block])
    (fun j ↦ RunsApp.of_spec (absorbBlockWith.c429.lam0.costSpec P (by includes) s block j)) 16792
    (fun j ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        absorbBlockWith.c429.lam0.costEq P (by includes),
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
/-- **The absorption of `k` whole blocks and the padded last one** (`absorbWith.c428`), the data
below `136·(k + 1)` bytes: `B + 430000` per block. -/
theorem absorbWith_cost (hP : Includes P absorbWith.c428.costDeps)
    (π : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (πVal : MachineValue)
    (hπ : ∀ a, RunsApp P πVal [encodeValue a] (encodeValue (π a))) (B : ℕ)
    (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P πVal [encodeValue a] ≤ B) :
    ∀ (k : ℕ) (s : LeanVM.Semantics.KeccakState) (data : List UInt8), k < 2 ^ 63 →
      data.length < 136 * (k + 1) →
      machineCost P absorbWith.c428.costIdx [πVal, encodeValue k, encodeValue s, encodeValue data] ≤
        (k + 1) * (B + 430000) := by
  intro k
  induction k with
  | zero =>
    intro s data _ hd
    rw [absorbWith.c428.costEq P hP π πVal hπ, limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64)]
    have h1 := padBlock_cost P (by includes) data (by omega)
    have h2 := absorbBlockWith_cost P (by includes) π πVal hπ B hB s (padBlock data)
    simp only [Nat.rec_zero]
    omega
  | succ k ih =>
    intro s data hk hd
    rw [absorbWith.c428.costEq P hP π πVal hπ]
    dsimp only
    rw [limbs_of_lt (by omega : k + 1 < 2 ^ 64)]
    have h1 := take_cost P (by includes) rate data (by rw [rate_eq]; norm_num)
    have h2 := absorbBlockWith_cost P (by includes) π πVal hπ B hB s (data.take rate)
    have h3 := bind_cost P (by includes) _ (.closure 433 [encodeValue k, πVal, encodeValue data])
      (fun st ↦ RunsApp.of_spec (absorbWith.c428.lam0.costSpec P (by includes) k π πVal hπ data st))
      ((k + 1) * (B + 430000) + 2100) (fun st ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
          show (433 : ℕ) = absorbWith.c428.lam0.costIdx from rfl,
          absorbWith.c428.lam0.costEq P (by includes) k π πVal hπ]
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

/-- Keccak-256 through a good index's closure (`keccak256With.c426` with `hashMC.lam0`), a message
of `L < 2^60` bytes. -/
theorem keccakIdx_cost (hP : Includes P Auto.LeanVM.Protocol.KeccakHash.keccak256With.c426.costDeps)
    (hL : Includes P hashMC.lam0.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (M : SortedMap (List UInt64) LeanVM.Semantics.KeccakState) (hg : smGood M)
    (hN : smWeightSum M < 2 ^ D) (m : List UInt8) (hm : m.length < 2 ^ 60) :
    machineCost P Auto.LeanVM.Protocol.KeccakHash.keccak256With.c426.costIdx
      [.closure hashMC.lam0.costIdx [encodeValue M], encodeValue m] ≤
      (m.length / 136 + 1) * (fwdLookupPrice D W + 430004) + 8 * m.length + 85 := by
  rw [Auto.LeanVM.Protocol.KeccakHash.keccak256With.c426.costEq P hP
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
    (.closure Auto.LeanVM.Protocol.KeccakHash.keccak256With.c426.lam0.costIdx [])
    (fun st ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.keccak256With.c426.lam0.costSpec P
      (by includes) st)) 36 (fun st ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Protocol.KeccakHash.keccak256With.c426.lam0.costEq P (by includes)]
        rfl) (LeanVM.Protocol.KeccakHash.absorbWith (fwdF M)
          (m.length / LeanVM.Protocol.KeccakHash.rate) (Vector.replicate 25 0) m)
  rw [LeanVM.Cost.Bounds.rate_eq] at ha hb ⊢
  rw [show fwdLookupPrice D W + 4 + 430000 = fwdLookupPrice D W + 430004 by omega] at ha
  omega

/-- **The extractor's seed** (`seedWithHash.c537` as `extractLC` calls it: the IV hashed through a
closure over the index of the `N` queries, then one lookup), for `N < 2^D`. -/
theorem extractSeed_cost (hP : Includes P extractLC.costDeps) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (qs : List (Common.PermutationQuery LeanVM.Semantics.KeccakState × LeanVM.Semantics.KeccakState))
    (hq : qs.length < 2 ^ D) (bytecode : List K) (hb : bytecode.length ≤ 2 ^ 34)
    (pd : LeanVM.Protocol.Digest) :
    machineCost P Auto.LeanVM.Protocol.Verifier.seedWithHash.c537.costIdx
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
  rw [Auto.LeanVM.Protocol.Verifier.seedWithHash.c537.costEq P (by includes) _ _ hH
    (fwdF (fwdIndex qs)) _ hF,
    Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c541.costEq P (by includes) _ _ hH]
  have h1 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c541.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c541.lam0.costSpec P
      (by includes) a)) 337 bytecode (fun a _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Protocol.Verifier.fiatShamirIvWithHash.c541.lam0.costEq P (by includes)]
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
    (.closure Auto.LeanVM.Protocol.Verifier.seedWithHash.c537.lam0.costIdx
      [.closure hashMC.lam0.costIdx [encodeValue (fwdIndex qs)], encodeValue pd])
    (fun iv ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.seedWithHash.c537.lam0.costSpec P
      (by includes) (fwdF (fwdIndex qs)) _ hF pd iv)) (fwdLookupPrice D W + 900) (fun iv ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          Auto.LeanVM.Protocol.Verifier.seedWithHash.c537.lam0.costEq P (by includes) _ _ hF,
          Auto.LeanVM.Protocol.Compile.seedInput.c539.costEq P (by includes), ofFnFrom_length]
        have := ofFnFrom_cost P (by includes) (n := 25) (by norm_num) _
          (.closure Auto.LeanVM.Protocol.Compile.seedInput.c539.lam0.costIdx
            [encodeValue iv, encodeValue pd])
          (fun j ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Compile.seedInput.c539.lam0.costSpec P
            (by includes) iv pd j)) 16 (fun j ↦ by
              rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
                Auto.LeanVM.Protocol.Compile.seedInput.c539.lam0.costEq P (by includes),
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

/-- The public input's digest (`publicInputDigest.c544`). -/
theorem publicInputDigest_cost (hP : Includes P Auto.LeanVM.publicInputDigest.c544.costDeps)
    (input : LeanVM.Semantics.PublicInput) :
    machineCost P Auto.LeanVM.publicInputDigest.c544.costIdx [encodeValue input] ≤ 200 := by
  rw [Auto.LeanVM.publicInputDigest.c544.costEq P hP, Auto.Fin.ofNat.c129.costEq P (by includes),
    Auto.Fin.ofNat.c129.costEq P (by includes), Auto.Fin.ofNat.c129.costEq P (by includes),
    Auto.Fin.ofNat.c129.costEq P (by includes)]
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

/-- The waiting scalars' lanes (`pendingLanes.c523`): at most `382`. -/
theorem pendingLanes_cost (hP : Includes P pendingLanes.c523.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P pendingLanes.c523.costIdx [encodeValue sp.pending] ≤ 382 := by
  rw [pendingLanes.c523.costEq P hP]
  have h1 := map_cost P (by includes) _ (.closure pendingLanes.c523.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (pendingLanes.c523.lam0.costSpec P (by includes) a)) 25 sp.pending
    (fun a ha ↦ by
      rw [appCost_fn, List.nil_append, pendingLanes.c523.lam0.costEq P (by includes)]
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

/-- A permutation's input (`duplexInput.c521`): at most `16312`. -/
theorem duplexInput_cost (hP : Includes P duplexInput.c521.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P duplexInput.c521.costIdx [encodeValue sp] ≤ 16312 := by
  rw [duplexInput.c521.costEq P hP, ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := 25) (by norm_num) _
    (.closure duplexInput.c521.lam0.costIdx [encodeValue sp])
    (fun j ↦ RunsApp.of_spec (duplexInput.c521.lam0.costSpec P (by includes) sp j)) 635
    (fun j ↦ by
      rw [appCost_fn, List.singleton_append, duplexInput.c521.lam0.costEq P (by includes),
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
/-- **A permutation** (`duplex.c519`): `B + 16340`. -/
theorem duplex_cost (hP : Includes P duplex.c519.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P duplex.c519.costIdx [πVal, encodeValue sp] ≤ B + 16340 := by
  rw [duplex.c519.costEq P hP π πVal hπ]
  have h1 := duplexInput_cost P (by includes) sp h
  have h2 := hB (duplexInput sp)
  have h3 := bind_cost P (by includes) _ (.closure duplex.c519.lam0.costIdx [encodeValue sp])
    (fun st ↦ RunsApp.of_spec (duplex.c519.lam0.costSpec P (by includes) sp st)) 11
    (fun st ↦ by
      rw [appCost_fn, List.singleton_append, duplex.c519.lam0.costEq P (by includes)]
      rfl) (π (duplexInput sp))
  omega

include hπ hB in
/-- **A scalar absorbed** (`absorb.c517`): `B + 16500`. -/
theorem absorb_cost (hP : Includes P absorb.c517.costDeps) (sp : Sponge) (x : E) (tag : ℕ)
    (h : SpOk sp) :
    machineCost P absorb.c517.costIdx [πVal, encodeValue sp, encodeValue x, encodeValue tag] ≤
      B + 16500 := by
  rw [absorb.c517.costEq P hP π πVal hπ, limbs_of_lt (by have := h.1; omega : sp.pending.length < 2 ^ 64),
    limbs_of_lt (by unfold rateScalars; norm_num : rateScalars < 2 ^ 64)]
  have h1 := length_cost P (by includes) sp.pending (by have := h.1; omega)
  have h0 := h.1
  have hr : rateScalars = 4 := rfl
  have hlam : ∀ (o : Option Sponge), (∀ a, o = some a → a.pending.length ≤ 4) →
      machineCost P Auto.Option.bind.c47.costIdx [encodeValue o,
        .closure absorb.c517.lam0.costIdx [encodeValue x, encodeValue tag]] ≤ 77 := by
    intro o ho
    have := bind_le P (by includes) _ (.closure absorb.c517.lam0.costIdx [encodeValue x, encodeValue tag])
      (fun a ↦ RunsApp.of_spec (absorb.c517.lam0.costSpec P (by includes) x tag a)) o 71
      (fun a ha ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          absorb.c517.lam0.costEq P (by includes)]
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
/-- **A challenge squeezed** (`squeeze.c527`): `B + 16400`. -/
theorem squeeze_cost (hP : Includes P squeeze.c527.costDeps) (sp : Sponge) (h : SpOk sp) :
    machineCost P squeeze.c527.costIdx [πVal, encodeValue sp] ≤ B + 16400 := by
  rw [squeeze.c527.costEq P hP π πVal hπ]
  cases hg : sp.ground with
  | some g => dsimp only; omega
  | none =>
    dsimp only
    have h1 := duplex_cost P π πVal hπ B hB (by includes) sp h
    have h2 := bind_cost P (by includes) _ (.closure squeeze.c527.lam0.costIdx [])
      (fun d ↦ RunsApp.of_spec (squeeze.c527.lam0.costSpec P (by includes) d)) 20
      (fun d ↦ by
        rw [appCost_fn, List.nil_append, squeeze.c527.lam0.costEq P (by includes)]
        rfl) (duplex π sp)
    omega

include hπ hB in
/-- **A grinding nonce absorbed and permuted** (`absorbNonce.c531`): `2·B + 33000`. -/
theorem absorbNonce_cost (hP : Includes P absorbNonce.c531.costDeps) (sp : Sponge) (n : E)
    (h : SpOk sp) :
    machineCost P absorbNonce.c531.costIdx [πVal, encodeValue sp, encodeValue n] ≤
      2 * B + 33000 := by
  rw [absorbNonce.c531.costEq P hP π πVal hπ]
  have h1 := absorb_cost P π πVal hπ B hB (by includes) sp n dsPowNonce h
  have h2 := bind_le P (by includes) _ (.closure absorbNonce.c531.lam0.costIdx [πVal])
    (fun a ↦ RunsApp.of_spec (absorbNonce.c531.lam0.costSpec P (by includes) π πVal hπ a))
    (LeanVM.Protocol.Compile.absorb π sp n dsPowNonce) (B + 16400)
    (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, absorbNonce.c531.lam0.costEq P (by includes) π πVal hπ]
      have := duplex_cost P π πVal hπ B hB (by includes) a
        (absorb_ok h (by unfold dsPowNonce; norm_num) ha)
      have := bind_cost P (by includes) _ (.closure absorbNonce.c531.lam0.lam0.costIdx [])
        (fun d ↦ RunsApp.of_spec (absorbNonce.c531.lam0.lam0.costSpec P (by includes) d)) 34
        (fun d ↦ by
          rw [appCost_fn, List.nil_append, absorbNonce.c531.lam0.lam0.costEq P (by includes)]
          rfl) (duplex π a)
      simp only [List.length_singleton]
      omega)
  omega

end Perm

end Sponge

/-! ## The skeleton's replay -/

section Replay

open LeanVM.Protocol.Compile
open LeanVM.Cost.Auto.LeanVM.Protocol.EndToEnd.Sound

variable (F : LeanVM.Semantics.KeccakState → Option LeanVM.Semantics.KeccakState) (FVal : MachineValue)
  (hF : ∀ a, RunsApp P FVal [encodeValue a] (encodeValue (F a))) (B : ℕ)
  (hB : ∀ a : LeanVM.Semantics.KeccakState, appCost P FVal [encodeValue a] ≤ B)

include hF hB in
/-- **The skeleton's replay** (`skelReplayP.c514`), the permutation's closure at most `B`: per
operation at most two permutations, `34000`, and `11` per root read so far (`R` bounds the roots
and the operations). -/
theorem skelReplay_cost (hP : Includes P skelReplayP.c514.costDeps) (R : ℕ) :
    ∀ (sk : List LeanVM.Protocol.EndToEnd.Sound.Op) (s : VerifierProgramState),
      s.roots.length + sk.length ≤ R → SpOk s.sponge →
      machineCost P skelReplayP.c514.costIdx [FVal, encodeValue sk, encodeValue s] ≤
        sk.length * (2 * B + 34000 + 11 * R) + 9 := by
  intro sk
  induction sk with
  | nil => intro s _ _; rw [skelReplayP.c514.costEq P hP F FVal hF]; simp
  | cons op tail ih =>
    intro s hR hs
    simp only [List.length_cons] at hR ⊢
    have hmul : (tail.length + 1) * (2 * B + 34000 + 11 * R) =
        tail.length * (2 * B + 34000 + 11 * R) + (2 * B + 34000 + 11 * R) := by ring
    have hmap : ∀ (s' : VerifierProgramState),
        machineCost P Auto.Option.map.c90.costIdx [.closure skelReplayP.c514.lam4.costIdx [],
          encodeValue (LeanVM.Protocol.EndToEnd.Sound.skelReplayP F tail s')] ≤ 23 := by
      intro s'
      have := optionMap_cost P (by includes) _ (.closure skelReplayP.c514.lam4.costIdx [])
        (fun r ↦ RunsApp.of_spec (skelReplayP.c514.lam4.costSpec P (by includes) r)) 15
        (LeanVM.Protocol.EndToEnd.Sound.skelReplayP F tail s')
        (fun r _ ↦ by rw [appCost_fn, List.nil_append, skelReplayP.c514.lam4.costEq P (by includes)]; rfl)
      omega
    rw [skelReplayP.c514.costEq P hP F FVal hF]
    cases op with
    | read =>
      dsimp only
      rcases hst : s.stream with _ | ⟨x, xs⟩
      · dsimp only; omega
      · dsimp only
        rcases hg : s.sponge.ground with _ | g
        · dsimp only
          have h1 := absorb_cost P F FVal hF B hB (by includes) s.sponge x dsObserve hs
          have h2 := bind_le P (by includes) _ (.closure 516 [encodeValue x, encodeValue xs,
              encodeValue tail, FVal, encodeValue s])
            (fun sp ↦ RunsApp.of_spec (skelReplayP.c514.lam1.costSpec P (by includes) x xs tail F FVal
              hF s sp))
            (LeanVM.Protocol.Compile.absorb F s.sponge x dsObserve)
            (tail.length * (2 * B + 34000 + 11 * R) + 9 + 60)
            (fun sp hsp ↦ by
              rw [appCost_fn, show (516 : ℕ) = skelReplayP.c514.lam1.costIdx from rfl]
              simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              rw [skelReplayP.c514.lam1.costEq P (by includes) x xs tail F FVal hF]
              have h3 := ih { sponge := sp, stream := xs, openings := s.openings, roots := s.roots }
                (by dsimp only; omega) (absorb_ok hs (by unfold dsObserve; norm_num) hsp)
              have h4 := optionMap_cost P (by includes) _
                (.closure skelReplayP.c514.lam0.costIdx [encodeValue x])
                (fun r ↦ RunsApp.of_spec (skelReplayP.c514.lam0.costSpec P (by includes) x r)) 18
                (LeanVM.Protocol.EndToEnd.Sound.skelReplayP F tail
                  { sponge := sp, stream := xs, openings := s.openings, roots := s.roots })
                (fun r _ ↦ by
                  rw [appCost_fn, List.singleton_append, skelReplayP.c514.lam0.costEq P (by includes)]
                  rfl)
              omega)
          omega
        · dsimp only; omega
    | sample =>
      dsimp only
      have h1 := squeeze_cost P F FVal hF B hB (by includes) s.sponge hs
      have h2 := bind_le P (by includes) _ (.closure 526 [encodeValue tail, FVal, encodeValue s])
        (fun c ↦ RunsApp.of_spec (skelReplayP.c514.lam3.costSpec P (by includes) tail F FVal hF s c))
        (LeanVM.Protocol.Compile.squeeze F s.sponge)
        (tail.length * (2 * B + 34000 + 11 * R) + 9 + 60)
        (fun c hc ↦ by
          rw [appCost_fn, show (526 : ℕ) = skelReplayP.c514.lam3.costIdx from rfl]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [skelReplayP.c514.lam3.costEq P (by includes) tail F FVal hF]
          have h3 := ih { sponge := c.2, stream := s.stream, openings := s.openings, roots := s.roots }
            (by dsimp only; omega) (squeeze_ok hs hc)
          have h4 := optionMap_cost P (by includes) _
            (.closure skelReplayP.c514.lam2.costIdx [encodeValue c])
            (fun r ↦ RunsApp.of_spec (skelReplayP.c514.lam2.costSpec P (by includes) c r)) 19
            (LeanVM.Protocol.EndToEnd.Sound.skelReplayP F tail
              { sponge := c.2, stream := s.stream, openings := s.openings, roots := s.roots })
            (fun r _ ↦ by
              rw [appCost_fn, List.singleton_append, skelReplayP.c514.lam2.costEq P (by includes)]
              rfl)
          omega)
      omega
    | grind bits =>
      dsimp only
      rcases hst : s.stream with _ | ⟨x, xs⟩
      · dsimp only; omega
      · dsimp only
        rcases hg : s.sponge.ground with _ | g
        · dsimp only
          have h1 := absorbNonce_cost P F FVal hF B hB (by includes) s.sponge x hs
          have h2 := bind_le P (by includes) _ (.closure 530 [encodeValue xs, encodeValue tail, FVal,
              encodeValue s])
            (fun c ↦ RunsApp.of_spec (skelReplayP.c514.lam5.costSpec P (by includes) xs tail F FVal hF
              s c))
            (LeanVM.Protocol.Compile.absorbNonce F s.sponge x)
            (tail.length * (2 * B + 34000 + 11 * R) + 9 + 60)
            (fun c hc ↦ by
              rw [appCost_fn, show (530 : ℕ) = skelReplayP.c514.lam5.costIdx from rfl]
              simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              rw [skelReplayP.c514.lam5.costEq P (by includes) xs tail F FVal hF]
              have h3 := ih { sponge := c.2, stream := xs, openings := s.openings, roots := s.roots }
                (by dsimp only; omega) (absorbNonce_ok hc)
              have h4 := hmap { sponge := c.2, stream := xs, openings := s.openings, roots := s.roots }
              omega)
          omega
        · dsimp only; omega
    | commit height width =>
      dsimp only
      rcases hst : s.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only
        rcases hg : s.sponge.ground with _ | g
        · dsimp only
          have h1 := absorb_cost P F FVal hF B hB (by includes) s.sponge x0 dsObserve hs
          have h2 := bind_le P (by includes) _ (.closure 535 [encodeValue x1, encodeValue xs,
              encodeValue x0, encodeValue height, encodeValue width, encodeValue tail, FVal,
              encodeValue s])
            (fun sp ↦ RunsApp.of_spec (skelReplayP.c514.lam7.costSpec P (by includes) x1 xs x0 height
              width tail F FVal hF s sp))
            (LeanVM.Protocol.Compile.absorb F s.sponge x0 dsObserve)
            (tail.length * (2 * B + 34000 + 11 * R) + 9 + B + 16700 + 11 * s.roots.length)
            (fun sp0 hsp0 ↦ by
              rw [appCost_fn, show (535 : ℕ) = skelReplayP.c514.lam7.costIdx from rfl]
              simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              rw [skelReplayP.c514.lam7.costEq P (by includes) x1 xs x0 height width tail F FVal hF]
              have hok0 := absorb_ok hs (by unfold dsObserve; norm_num) hsp0
              have h3 := absorb_cost P F FVal hF B hB (by includes) sp0 x1 dsObserve hok0
              have h4 := bind_le P (by includes) _ (.closure skelReplayP.c514.lam6.costIdx
                  [encodeValue x1, encodeValue xs, encodeValue x0, encodeValue height,
                    encodeValue width, encodeValue tail, FVal, encodeValue s])
                (fun sp ↦ RunsApp.of_spec (skelReplayP.c514.lam6.costSpec P (by includes) x1 xs x0
                  height width tail F FVal hF s sp))
                (LeanVM.Protocol.Compile.absorb F sp0 x1 dsObserve)
                (tail.length * (2 * B + 34000 + 11 * R) + 9 + 130 + 11 * s.roots.length)
                (fun sp1 hsp1 ↦ by
                  rw [appCost_fn]
                  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
                  rw [skelReplayP.c514.lam6.costEq P (by includes) x1 xs x0 height width tail F FVal hF]
                  have h5 := digestOfScalars_cost P (by includes) (x0, x1)
                  have h6 := append_cost P (by includes) s.roots
                    [(LeanVM.Protocol.KeccakHash.digestFromHalves (x0, x1), height, width)]
                  have h7 := ih
                    { sponge := sp1, stream := xs, openings := s.openings,
                      roots := s.roots ++
                        [(LeanVM.Protocol.KeccakHash.digestFromHalves (x0, x1), height, width)] }
                    (by dsimp only; simp only [List.length_append, List.length_singleton]; omega)
                    (absorb_ok hok0 (by unfold dsObserve; norm_num) hsp1)
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
      dsimp only
      rcases ho : s.openings with _ | ⟨ph, os⟩
      · dsimp only; omega
      · dsimp only
        have h3 := ih { sponge := s.sponge, stream := s.stream, openings := os, roots := s.roots }
          (by dsimp only; omega) hs
        have h4 := hmap { sponge := s.sponge, stream := s.stream, openings := os, roots := s.roots }
        omega

end Replay

/-! ## A tactic for the skeletons' prices -/

section Meta

open Lean Meta Elab Tactic

/-- The values of a literal list of encoded values `[encodeValue a, …]`. -/
meta partial def encArgsOf (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    let h := e.appFn!.appArg!
    if h.isAppOfArity ``LeanVM.Cost.MachineEncoding.encodeValue 3 then
      (encArgsOf e.appArg!).map (h.appArg! :: ·)
    else none
  else none

/-- The program and the values of every `machineCost P c [encodeValue a, …]` of `e`. -/
meta partial def callsOf (c : Name) (e : Expr) (acc : Array (Expr × List Expr) := #[]) :
    Array (Expr × List Expr) :=
  let acc :=
    if e.isAppOfArity ``LeanVM.Cost.machineCost 3 && !e.hasLooseBVars then
      let args := e.getAppArgs
      if args[1]!.isConstOf c then
        match encArgsOf args[2]! with
        | some xs => if acc.any (fun p ↦ p.2 == xs) then acc else acc.push (args[0]!, xs)
        | none => acc
      else acc
    else acc
  match e with
  | .app f a => callsOf c a (callsOf c f acc)
  | .lam _ t b _ | .forallE _ t b _ => callsOf c b (callsOf c t acc)
  | .letE _ t v b _ => callsOf c b (callsOf c v (callsOf c t acc))
  | .mdata _ b | .proj _ _ b => callsOf c b acc
  | _ => acc

/-- Add the hypothesis `stx` proves, if it elaborates. -/
meta def noteTerm (stx : Syntax) : TacticM Unit := do
  let g ← getMainGoal
  try
    let g' ← g.withContext do
      let pf ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm stx none
      let pf ← instantiateMVars pf
      if pf.hasExprMVar || pf.hasSyntheticSorry then return g
      let (_, g') ← g.note `hcost pf
      return g'
    replaceMainGoal [g']
  catch _ => replaceMainGoal [g]

/-- The `machineCost` index of a lemma's conclusion. -/
meta def lemmaIdx (n : Name) : MetaM (Option Name) := do
  let ci ← getConstInfo n
  forallTelescopeReducing ci.type fun _ body ↦ do
    match body.find? (fun x ↦ x.isAppOfArity ``LeanVM.Cost.machineCost 3) with
    | some m => return (m.getArg! 1).constName?
    | none => return none

/-- The function whose length a lemma bounds. -/
meta def lemmaLenFn (n : Name) : MetaM (Option Name) := do
  let ci ← getConstInfo n
  forallTelescopeReducing ci.type fun _ body ↦ do
    match body.find? (fun x ↦ x.isAppOfArity ``List.length 2) with
    | some m => return m.appArg!.getAppFn.constName?
    | none => return none

/-- The arguments of every `List.length (f a₁ … aₙ)` of `e`. -/
meta partial def lenArgsOf (f : Name) (e : Expr) (acc : Array (Array Expr) := #[]) :
    Array (Array Expr) :=
  let acc :=
    if e.isAppOfArity ``List.length 2 && !e.hasLooseBVars && e.appArg!.isAppOf f then
      let args := e.appArg!.getAppArgs
      if acc.any (· == args) then acc else acc.push args
    else acc
  match e with
  | .app fn a => lenArgsOf f a (lenArgsOf f fn acc)
  | .lam _ t b _ | .forallE _ t b _ => lenArgsOf f b (lenArgsOf f t acc)
  | .letE _ t v b _ => lenArgsOf f b (lenArgsOf f v (lenArgsOf f t acc))
  | .mdata _ b | .proj _ _ b => lenArgsOf f b acc
  | _ => acc

/-- `cost_calls [L₁, …]`: for every append, replicate and word-sized `limbCount` of the goal, its
bound as a hypothesis (`append_cost`, `replicate_cost`, `take_cost`, `drop_cost`, `length_cost`,
`limbs_of_lt`); for every call of a
lemma `Lᵢ`'s index on encoded values, `Lᵢ P (by includes) a₁ …` (side conditions by their
`autoParam`s). -/
elab "cost_calls" " [" ls:ident,* "]" : tactic => do
  let tgt ← withMainContext do instantiateMVars (← getMainTarget)
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.append.c50.costIdx tgt do
    if let [a, b] := xs then
      noteTerm (← `(append_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax b)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.replicate.c76.costIdx tgt do
    if let [n, a] := xs then
      noteTerm (← `(replicate_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax n) (by omega)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.take.c68.costIdx tgt do
    if let [n, a] := xs then
      noteTerm (← `(take_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax n)
        $(← Term.exprToSyntax a) (by omega)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.drop.c42.costIdx tgt do
    if let [n, a] := xs then
      noteTerm (← `(drop_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax n)
        $(← Term.exprToSyntax a) (by omega)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.length.c21.costIdx tgt do
    if let [a] := xs then
      noteTerm (← `(length_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax a)
        (by omega)))
  for t in limbsArgs tgt do
    noteTerm (← `(limbs_of_lt (by omega : $(← Term.exprToSyntax t) < 2 ^ 64)))
  for l in ls.getElems do
    let n ← realizeGlobalConstNoOverloadWithInfo l
    let some c ← lemmaIdx n | throwError "cost_calls: {n} prices no call"
    for (p, xs) in callsOf c tgt do
      let args ← xs.toArray.mapM fun x ↦ Term.exprToSyntax x
      noteTerm (← `($(mkIdent n) $(← Term.exprToSyntax p) (by includes) $args*))

/-- `len_facts [L₁, …]`: for every `List.length (f a₁ …)` of the goal and the hypotheses, `f` the
function a lemma `Lᵢ` bounds the length of, `Lᵢ a₁ …` as a hypothesis. -/
elab "len_facts" " [" ls:ident,* "]" : tactic => do
  evalTactic (← `(tactic| try simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.length_singleton] at *))
  let es ← withMainContext do
    let mut es := #[← instantiateMVars (← getMainTarget)]
    for d in ← getLCtx do
      unless d.isImplementationDetail do es := es.push (← instantiateMVars d.type)
    return es
  for l in ls.getElems do
    let n ← realizeGlobalConstNoOverloadWithInfo l
    let some f ← lemmaLenFn n | throwError "len_facts: {n} bounds no length"
    let mut seen : Array (Array Expr) := #[]
    for e in es do
      seen := lenArgsOf f e seen
    for args in seen do
      let args ← args.mapM fun x ↦ Term.exprToSyntax x
      noteTerm (← `($(mkIdent n) $args*))
  evalTactic (← `(tactic| try simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.length_singleton] at *))

end Meta

/-! ## The body's skeleton -/

section Skeleton

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Cost.Auto.LeanVM.Protocol.EndToEnd.Sound

/-- `grindingBits` (`grindingBits.c450`), a numerator below `2^128`: at most `1900`. -/
theorem grindingBits_cost (hP : Includes P Auto.LeanVM.Protocol.Compile.grindingBits.c450.costDeps)
    (n : ℕ) (hn : n < 2 ^ 128 := by omega) :
    machineCost P Auto.LeanVM.Protocol.Compile.grindingBits.c450.costIdx [encodeValue n] ≤ 1900 := by
  rw [Auto.LeanVM.Protocol.Compile.grindingBits.c450.costEq P hP]
  have hl1 : limbCount n ≤ 3 := limbs_le_wl (E := 128) (by omega)
  have hs : securityBits = 125 := rfl
  rw [hs, limbs_of_lt (by norm_num : (125 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : 128 - 125 < 2 ^ 64)]
  have hlog : Nat.log2 (n - 1) < 128 := by
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
    · rw [h0]; simp
    · exact (Nat.log2_lt (by omega)).2 (by omega)
  have hr := log2Rec_cost P (by includes) (n - 1) (by omega)
  split_ifs with h
  · simp only [limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : Nat.log2 (n - 1) + 1 < 2 ^ 64),
      limbs_of_lt (by omega : Nat.log2 (n - 1) < 2 ^ 64)]
    simp only [max_self]
    nlinarith

theorem grindingBits_le (n : ℕ) (hn : n < 2 ^ 128) : grindingBits n ≤ 128 := by
  unfold grindingBits
  split_ifs
  · omega
  · have hlog : Nat.log2 (n - 1) < 128 := by
      rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
      · rw [h0]; simp
      · exact (Nat.log2_lt (by omega)).2 (by omega)
    omega

/-- A grind's skeleton (`skGrind.c448`): at most `11`. -/
theorem skGrind_cost (hP : Includes P skGrind.c448.costDeps) (bits : ℕ) (hb : bits < 2 ^ 64 := by omega) :
    machineCost P skGrind.c448.costIdx [encodeValue bits] ≤ 11 := by
  rw [skGrind.c448.costEq P hP, limbs_of_lt hb]
  split_ifs <;> omega

theorem length_skGrind (bits : ℕ) :
    (LeanVM.Protocol.EndToEnd.Sound.skGrind bits).length ≤ 1 := by
  unfold LeanVM.Protocol.EndToEnd.Sound.skGrind; split_ifs <;> simp

theorem length_skRound (count : ℕ) (b : Bool) :
    (LeanVM.Protocol.EndToEnd.Sound.skRound count b).length ≤ count + 2 := by
  cases b <;> simp only [LeanVM.Protocol.EndToEnd.Sound.skRound, List.length_cons,
    List.length_append, List.length_replicate] <;>
    have := length_skGrind (grindingBits (count - 1)) <;>
    have := length_skGrind (grindingBits (count - 1 + 1)) <;> omega

/-- A sumcheck round's skeleton (`skRound.c455`): at most `30·count + 2000`. -/
theorem skRound_cost (hP : Includes P skRound.c455.costDeps) (count : ℕ) (b : Bool)
    (hc : count < 2 ^ 60 := by omega) :
    machineCost P skRound.c455.costIdx [encodeValue count, encodeValue b] ≤ 30 * count + 2000 := by
  rw [skRound.c455.costEq P hP]
  have g1 := grindingBits_cost P (by includes) (count - 1) (by omega)
  have g2 := grindingBits_cost P (by includes) (count - 1 + 1) (by omega)
  have s1 := skGrind_cost P (by includes) (grindingBits (count - 1))
    (by have := grindingBits_le (count - 1) (by omega); omega)
  have s2 := skGrind_cost P (by includes) (grindingBits (count - 1 + 1))
    (by have := grindingBits_le (count - 1 + 1) (by omega); omega)
  cases b <;> dsimp only <;> cost_calls [] <;>
    simp only [List.length_cons, List.length_replicate] at * <;> omega

theorem length_skSum (count : ℕ) (eqs : List Bool) :
    (LeanVM.Protocol.EndToEnd.Sound.skSum count eqs).length ≤ eqs.length * (count + 3) := by
  unfold LeanVM.Protocol.EndToEnd.Sound.skSum
  induction eqs with
  | nil => simp
  | cons b eqs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_append, List.length_singleton,
      List.length_cons]
    have := length_skRound count b
    nlinarith

/-- A sumcheck's skeleton (`skSum.c453`): at most `(52·count + 2100)·|eqs| + 12`. -/
theorem skSum_cost (hP : Includes P skSum.c453.costDeps) (count : ℕ) (eqs : List Bool)
    (hc : count < 2 ^ 60 := by omega) :
    machineCost P skSum.c453.costIdx [encodeValue count, encodeValue eqs] ≤
      (52 * count + 2100) * eqs.length + 12 := by
  rw [skSum.c453.costEq P hP]
  have h1 := map_cost P (by includes) _ (.closure skSum.c453.lam0.costIdx [encodeValue count])
    (fun b ↦ RunsApp.of_spec (skSum.c453.lam0.costSpec P (by includes) count b))
    (41 * count + 2040) eqs (fun b _ ↦ by
      rw [appCost_fn, List.singleton_append, skSum.c453.lam0.costEq P (by includes)]
      have := skRound_cost P (by includes) count b hc
      have := append_cost P (by includes) (LeanVM.Protocol.EndToEnd.Sound.skRound count b)
        [LeanVM.Protocol.EndToEnd.Sound.Op.sample]
      have := length_skRound count b
      simp only [List.length_singleton]
      omega)
  have h2 := flatten_cost P (by includes) (count + 3)
    (List.map (fun b ↦ LeanVM.Protocol.EndToEnd.Sound.skRound count b ++
      [LeanVM.Protocol.EndToEnd.Sound.Op.sample]) eqs) (fun l hl ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hl
        have := length_skRound count b
        simp only [List.length_append, List.length_singleton]
        omega)
  simp only [List.length_map] at h2
  nlinarith

end Skeleton

section Skeleton2

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Cost.Auto.LeanVM.Protocol.EndToEnd.Sound

/-- The protocol's constants the skeletons read. -/
theorem skConsts : busBits = 4 ∧ nTrees = 3 ∧ keccakDepth = 12 ∧ keccakSegments = 2 ∧
    keccakSegmentBits = 1 ∧ keccakLaneBits = 5 ∧ keccakLocalBits = 11 ∧ qkeccakSlotBits = 6 ∧
    kBits = 64 ∧ ringMapWidth = 8 ∧ embedBits = 24 ∧ productBits = 47 ∧ opKeccak = 5 ∧
    Whir.oodGrindingBits = 15 ∧ Whir.batchGrindingBits = 13 ∧ Whir.foldGrindingBits = 7 ∧
    Whir.queryGrindingBits = 17 ∧ securityBits = 125 := by
  decide +kernel

theorem length_skOod (s : ℕ) : (skOod s).length = s + 2 := by
  simp [skOod, LeanVM.Protocol.EndToEnd.Sound.skGrind, Whir.oodGrindingBits]

/-- The out-of-domain sample's skeleton (`skOod.c447`). -/
theorem skOod_cost (hP : Includes P skOod.c447.costDeps) (s : ℕ) (hs : s < 2 ^ 60 := by omega) :
    machineCost P skOod.c447.costIdx [encodeValue s] ≤ 26 * s + 60 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, c14, -⟩ := skConsts
  rw [skOod.c447.costEq P hP]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

theorem length_skRing : skRing.length = 17 := by decide

/-- Ring switching's skeleton (`skRing.c470`): at most `300`. -/
theorem skRing_cost (hP : Includes P skRing.c470.costDeps) :
    machineCost P skRing.c470.costIdx [] ≤ 300 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -, -, -, -, c15, -⟩ := skConsts
  rw [skRing.c470.costEq P hP]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

theorem length_skFoldRound : skFoldRound.length = 7 := by decide

/-- A fold round's skeleton (`skFoldRound.c474`): at most `200`. -/
theorem skFoldRound_cost (hP : Includes P skFoldRound.c474.costDeps) :
    machineCost P skFoldRound.c474.costIdx [] ≤ 200 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c16, -⟩ := skConsts
  rw [skFoldRound.c474.costEq P hP]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

theorem length_skFoldRounds : ∀ n, (skFoldRounds n).length = 7 * n
  | 0 => rfl
  | n + 1 => by
    rw [skFoldRounds, List.length_append, length_skFoldRound, length_skFoldRounds n]; ring

/-- `n` fold rounds' skeleton (`skFoldRounds.c473`): at most `300·n + 5`. -/
theorem skFoldRounds_cost (hP : Includes P skFoldRounds.c473.costDeps) :
    ∀ n : ℕ, n < 2 ^ 60 → machineCost P skFoldRounds.c473.costIdx [encodeValue n] ≤ 300 * n + 5
  | 0, _ => by rw [skFoldRounds.c473.costEq P hP]; simp
  | n + 1, hn => by
    rw [skFoldRounds.c473.costEq P hP]
    dsimp only
    have := skFoldRounds_cost hP n (by omega)
    have := skFoldRound_cost P (by includes)
    have := append_cost P (by includes) skFoldRound (skFoldRounds n)
    rw [length_skFoldRound] at this
    rw [limbs_of_lt (by omega : n + 1 < 2 ^ 64)]
    omega

theorem length_skBytecodeShare : skBytecodeShare.length ≤ 30 := by decide

/-- The bytecode's share's skeleton (`skBytecodeShare.c456`): at most `9400`. -/
theorem skBytecodeShare_cost (hP : Includes P skBytecodeShare.c456.costDeps) :
    machineCost P skBytecodeShare.c456.costIdx [] ≤ 9400 := by
  obtain ⟨c1, -⟩ := skConsts
  rw [skBytecodeShare.c456.costEq P hP]
  cost_calls [skSum_cost]
  len_facts [length_skSum]
  omega

/-- `productBits` (`productBits.c468`): `5`. -/
theorem productBits_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.productBits.c468.costDeps) :
    machineCost P Auto.LeanVM.Protocol.Verifier.productBits.c468.costIdx [] ≤ 5 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, c11, -⟩ := skConsts
  rw [Auto.LeanVM.Protocol.Verifier.productBits.c468.costEq P hP]
  cost_calls []
  omega

theorem length_skLayer (n : ℕ) : (skLayer n).length ≤ 6 * n + 140 := by
  have := length_skSum 3 (List.replicate n true)
  have := length_skSum 4 (List.replicate keccakLocalBits false)
  have := length_skGrind (grindingBits (productBits - 1))
  have := length_skGrind (grindingBits 2)
  obtain ⟨-, -, -, -, -, -, c7, -, -, -, -, c12, -⟩ := skConsts
  simp only [skLayer, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at *
  omega

/-- A Keccak layer's skeleton (`skLayer.c467`), at a point of `n` coordinates. -/
theorem skLayer_cost (hP : Includes P skLayer.c467.costDeps) (n : ℕ) (hn : n < 2 ^ 50 := by omega) :
    machineCost P skLayer.c467.costIdx [encodeValue n] ≤ 2600 * n + 40000 := by
  obtain ⟨-, -, -, -, -, -, c7, -, -, -, -, c12, -⟩ := skConsts
  have := grindingBits_le (productBits - 1) (by omega)
  have := grindingBits_le 2 (by omega)
  rw [skLayer.c467.costEq P hP]
  cost_calls [skGrind_cost, grindingBits_cost, skSum_cost, productBits_cost]
  len_facts [length_skGrind, length_skSum]
  omega

theorem bitLength_cost' (hP : Includes P bitLengthC.costDeps) (n : ℕ) (hn : n < 2 ^ 64 := by omega) :
    machineCost P bitLengthC.costIdx [encodeValue n] ≤ 771 := bitLength_cost P hP n hn

theorem foldl_max_le (M : ℕ) : ∀ (hs : List ℕ) (a : ℕ), a ≤ M → (∀ x ∈ hs, x ≤ M) →
    hs.foldl max a ≤ M
  | [], _, ha, _ => ha
  | x :: hs, a, ha, h => foldl_max_le M hs (max a x) (max_le ha (h x (by simp)))
      (fun y hy ↦ h y (by simp [hy]))

/-- The largest height (`List.foldl max` with `skTablePhaseL.c461.lam0`): `18·|hs| + 3`. -/
theorem foldlMax_cost (h1 : Includes P listFoldl.costDeps) (h2 : Includes P Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam0.costDeps)
    (hs : List ℕ) (h : ∀ x ∈ hs, x < 2 ^ 63) :
    machineCost P listFoldl.costIdx [.closure Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam0.costIdx [], encodeValue 0,
      encodeValue hs] ≤ 18 * hs.length + 3 := by
  have := listFoldl_le P h1 (fun a b : ℕ ↦ max a b) (.closure Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam0.costSpec P h2 a b)) 7
    (fun acc ↦ acc < 2 ^ 63) hs 0 (by norm_num)
    (fun acc hacc b hb ↦ ⟨by have := h b hb; omega, by
      rw [appCost_fn, List.nil_append, Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam0.costEq P h2,
        limbs_of_lt (by omega : acc < 2 ^ 64), limbs_of_lt (by have := h b hb; omega : b < 2 ^ 64)]
      simp⟩)
  omega

theorem getD_le_of (hs : List ℕ) (i M : ℕ) (h : ∀ x ∈ hs, x ≤ M) : hs.getD i 0 ≤ M := by
  rcases getD_mem_or hs i 0 with hm | hm
  · exact h _ hm
  · rw [hm]; omega

theorem kLen_le (hs : List ℕ) (M : ℕ) (h : ∀ x ∈ hs, x ≤ M) : kLen hs ≤ M := by
  unfold kLen
  exact (min_le_left _ _).trans (getD_le_of hs _ M h)

/-- The Keccak reduction's length (`kLen.c469`), heights of at most `30`: at most `400`. -/
theorem kLen_cost (hP : Includes P kLen.c469.costDeps) (hs : List ℕ) (hl : hs.length ≤ 6)
    (h : ∀ x ∈ hs, x ≤ 30) : machineCost P kLen.c469.costIdx [encodeValue hs] ≤ 400 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, c13, -⟩ := skConsts
  rw [kLen.c469.costEq P hP]
  have g := getD_cost_idx P (by includes) hs opKeccak 0 (by omega)
  have f := foldlMax_cost P (by includes) (by includes) hs (fun x hx ↦ by have := h x hx; omega)
  have h1 := getD_le_of hs opKeccak 30 h
  have h2 := foldl_max_le 30 hs 0 (by omega) h
  rw [limbs_of_lt (by omega : hs.getD opKeccak 0 < 2 ^ 64),
    limbs_of_lt (by omega : hs.foldl max 0 < 2 ^ 64)]
  split_ifs <;> omega

/-- The constant `tableWidthsL` (`tableWidthsL.c464`). -/
theorem tableWidthsL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.tableWidthsL.c464.costDeps) :
    machineCost P Auto.LeanVM.Extraction.AS.tableWidthsL.c464.costIdx [] ≤ 25 :=
  (Auto.LeanVM.Extraction.AS.tableWidthsL.c464.costEq P hP).le

/-- The constant `pushCountsL` (`pushCountsL.c460`). -/
theorem pushCountsL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.pushCountsL.c460.costDeps) :
    machineCost P Auto.LeanVM.Extraction.AS.pushCountsL.c460.costIdx [] ≤ 25 :=
  (Auto.LeanVM.Extraction.AS.pushCountsL.c460.costEq P hP).le

theorem length_skTablesL (k : ℕ) : (skTablesL k).length ≤ 153 := by
  rcases lt_or_ge k 6 with hk | hk
  · interval_cases k <;> decide +kernel
  · unfold skTablesL
    rw [List.take_of_length_le (by simp [tableWidthsL]; omega)]
    decide +kernel

theorem length_skTablePhaseL (hs : List ℕ) : (skTablePhaseL hs).length ≤ 7 * hs.foldl max 0 + 160 := by
  unfold skTablePhaseL
  have := length_skGrind (grindingBits (2 + nTrees - 1))
  have := length_skSum 4 (List.replicate (hs.foldl max 0) false)
  have := length_skTablesL (min hs.length 6)
  simp only [List.length_append, List.length_replicate, List.length_singleton] at *
  omega

/-- The table phase's skeleton (`skTablePhaseL.c461`), heights of at most `30`: at most `100000`. -/
theorem skTablePhaseL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.costDeps)
    (hs : List ℕ) (hl : hs.length ≤ 6) (h : ∀ x ∈ hs, x ≤ 30) :
    machineCost P Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.costIdx [encodeValue hs] ≤ 100000 := by
  obtain ⟨-, c2, -⟩ := skConsts
  have f := foldlMax_cost P (by includes) (by includes) hs (fun x hx ↦ by have := h x hx; omega)
  have hm := foldl_max_le 30 hs 0 (by omega) h
  have := grindingBits_le (2 + nTrees - 1) (by omega)
  have htk : (List.take (min hs.length 6) tableWidthsL).length ≤ 6 := by simp [tableWidthsL]
  have hw92 : ∀ w ∈ tableWidthsL, w ≤ 92 := by decide
  have hw : ∀ w ∈ List.take (min hs.length 6) tableWidthsL, w ≤ 92 := fun w hw ↦
    hw92 w (List.mem_of_mem_take hw)
  have hmap := map_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam1.costIdx [])
    (fun w ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam1.costSpec P
      (by includes) w)) 1388 _ (fun w hw' ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.lam1.costEq P (by includes)]
        have := replicate_cost P (by includes) Op.read w (by have := hw w hw'; omega)
        have := hw w hw'
        simp only [List.length_nil]
        omega)
  have hfl := flatten_cost P (by includes) 92
    (List.map (fun w ↦ List.replicate w Op.read) (List.take (min hs.length 6) tableWidthsL))
    (fun l hl' ↦ by
      obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hl'
      simpa using hw w hw')
  have := length_skTablesL (min hs.length 6)
  rw [Auto.LeanVM.Extraction.AS.skTablePhaseL.c461.costEq P hP]
  cost_calls [grindingBits_cost, skGrind_cost, skSum_cost, tableWidthsL_cost]
  len_facts [length_skGrind, length_skSum]
  simp only [List.length_map] at hfl
  have hmx : (1388 + 13) * (List.take (min hs.length 6) tableWidthsL).length ≤ 1401 * 6 :=
    Nat.mul_le_mul_left _ htk
  have hfx : (11 * 92 + 11) * (List.take (min hs.length 6) tableWidthsL).length ≤ 1023 * 6 :=
    Nat.mul_le_mul_left _ htk
  have hsx : (52 * 4 + 2100) * hs.foldl max 0 ≤ 2308 * 30 := Nat.mul_le_mul_left _ hm
  have hsl : hs.foldl max 0 * (4 + 3) ≤ 30 * 7 := Nat.mul_le_mul_right _ hm
  rw [ite_eq_left hl]
  omega

theorem pushSizes_facts (lm lb : ℕ) (hs : List ℕ) (hm : lm ≤ 40) (hb : lb ≤ 40)
    (h : ∀ x ∈ hs, x ≤ 30) :
    ([0, lm, lb] ++ (hs.zip pushCountsL).flatMap fun x ↦ List.replicate x.2 x.1).length ≤ 200 ∧
      ∀ x ∈ [0, lm, lb] ++ (hs.zip pushCountsL).flatMap (fun x ↦ List.replicate x.2 x.1), x ≤ 40 := by
  have hz : ∀ x ∈ hs.zip pushCountsL, x.1 ≤ 30 ∧ x.2 ≤ 28 := fun x hx ↦ by
    have h1 := h _ (List.of_mem_zip hx).1
    have h2 : ∀ c ∈ pushCountsL, c ≤ 28 := by decide
    exact ⟨h1, h2 _ (List.of_mem_zip hx).2⟩
  have hl : (hs.zip pushCountsL).length ≤ 6 := by simp [pushCountsL]
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [List.length_append, List.length_flatMap]
    have := List.sum_le_length_nsmul
      ((hs.zip pushCountsL).map fun x ↦ (List.replicate x.2 x.1).length) 28 (fun y hy ↦ by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        simpa using (hz x hx).2)
    rw [List.length_map, smul_eq_mul] at this
    simp only [List.length_cons, List.length_nil] at *
    omega
  · rcases List.mem_append.1 hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hx
      rw [List.eq_of_mem_replicate hxy]
      have := (hz y hy).1
      omega

theorem pushDepthL_le (lm lb : ℕ) (hs : List ℕ) (hm : lm ≤ 40) (hb : lb ≤ 40)
    (h : ∀ x ∈ hs, x ≤ 30) : pushDepthL lm lb hs ≤ 64 :=
  (stackOffsets_bounds _ (pushSizes_facts lm lb hs hm hb h).1 (pushSizes_facts lm lb hs hm hb h).2).2

/-- The push side's depth (`pushDepthL.c457`): at most `973730000`. -/
theorem pushDepthL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.pushDepthL.c457.costDeps)
    (lm lb : ℕ) (hs : List ℕ) (hm : lm ≤ 40) (hb : lb ≤ 40) (h : ∀ x ∈ hs, x ≤ 30) :
    machineCost P Auto.LeanVM.Extraction.AS.pushDepthL.c457.costIdx [encodeValue lm, encodeValue lb,
      encodeValue hs] ≤ 973730000 := by
  rw [Auto.LeanVM.Extraction.AS.pushDepthL.c457.costEq P hP]
  have hz : ∀ x ∈ hs.zip pushCountsL, x.1 ≤ 30 ∧ x.2 ≤ 28 := fun x hx ↦ by
    have h1 := h _ (List.of_mem_zip hx).1
    have h2 : ∀ c ∈ pushCountsL, c ≤ 28 := by decide
    exact ⟨h1, h2 _ (List.of_mem_zip hx).2⟩
  have hl : (hs.zip pushCountsL).length ≤ 6 := by simp [pushCountsL]
  have h1 := pushCountsL_cost P (by includes)
  have h2 := listZipWith_le P (by includes) (fun a b : ℕ ↦ (a, b))
    (.closure Auto.LeanVM.Extraction.AS.pushDepthL.c457.lam1.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.pushDepthL.c457.lam1.costSpec P
      (by includes) a b)) 5 hs pushCountsL (fun a _ b _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.AS.pushDepthL.c457.lam1.costEq P (by includes)]
        rfl)
  have h3 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.AS.pushDepthL.c457.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.pushDepthL.c457.lam0.costSpec P
      (by includes) x)) 430 (hs.zip pushCountsL) (fun x hx ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.AS.pushDepthL.c457.lam0.costEq P (by includes)]
        have := replicate_cost P (by includes) x.1 x.2 (by have := (hz x hx).2; omega)
        have := (hz x hx).2
        simp only [List.length_nil]
        omega)
  have h4 := flatten_cost P (by includes) 28
    (List.map (fun x ↦ List.replicate x.2 x.1) (hs.zip pushCountsL)) (fun l hl' ↦ by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl'
      simpa using (hz x hx).2)
  have h5 := append_cost P (by includes) [0, lm, lb]
    ((hs.zip pushCountsL).flatMap fun x ↦ List.replicate x.2 x.1)
  have h6 := stackOffsets_cost P (by includes) _ (pushSizes_facts lm lb hs hm hb h).1
    (pushSizes_facts lm lb hs hm hb h).2
  have hpl : pushCountsL.length = 6 := rfl
  simp only [List.length_map, List.length_cons, List.length_nil, List.length_zip, hpl] at *
  have : (5 + 19) * min hs.length 6 ≤ 24 * 6 := Nat.mul_le_mul_left _ (min_le_right _ _)
  have : (430 + 13) * min hs.length 6 ≤ 443 * 6 := Nat.mul_le_mul_left _ (min_le_right _ _)
  have : (11 * 28 + 11) * min hs.length 6 ≤ 319 * 6 := Nat.mul_le_mul_left _ (min_le_right _ _)
  omega

theorem length_skGkrStep (step : ℕ) (last : Bool) (L : ℕ) (hs : step ≤ 2) :
    (skGkrStep step last L).length ≤ 8 * L + 20 := by
  have h2 : 2 ^ step ≤ 4 := (Nat.pow_le_pow_right (by norm_num) hs).trans (by norm_num)
  have := length_skSum (2 ^ step + 1) (List.replicate L true)
  have := length_skGrind (grindingBits (nTrees - 1))
  have := length_skGrind (grindingBits (if last then 2 * step else step))
  simp only [skGkrStep, List.length_append, List.length_replicate, List.length_singleton] at *
  have : L * (2 ^ step + 1 + 3) ≤ L * 8 := Nat.mul_le_mul_left _ (by omega)
  omega

/-- A GKR step's skeleton (`skGkrStep.c452`), `step ≤ 2` levels from `L` coordinates. -/
theorem skGkrStep_cost (hP : Includes P skGkrStep.c452.costDeps) (step : ℕ) (last : Bool) (L : ℕ)
    (hs : step ≤ 2 := by omega) (hL : L < 2 ^ 50 := by omega) :
    machineCost P skGkrStep.c452.costIdx [encodeValue step, encodeValue last, encodeValue L] ≤
      3000 * L + 7000 := by
  obtain ⟨-, c2, -⟩ := skConsts
  have h2 : 2 ^ step ≤ 4 := (Nat.pow_le_pow_right (by norm_num) hs).trans (by norm_num)
  have := grindingBits_le (nTrees - 1) (by omega)
  have hsk := skSum_cost P (by includes) (2 ^ step + 1) (List.replicate L true) (by omega)
  have hsl := length_skSum (2 ^ step + 1) (List.replicate L true)
  have hm1 : (52 * (2 ^ step + 1) + 2100) * (List.replicate L true).length ≤ 2360 * L := by
    rw [List.length_replicate]; exact Nat.mul_le_mul_right _ (by omega)
  have hm2 : (List.replicate L true).length * (2 ^ step + 1 + 3) ≤ L * 8 := by
    rw [List.length_replicate]; exact Nat.mul_le_mul_left _ (by omega)
  rw [skGkrStep.c452.costEq P hP]
  simp only [Nat.one_shiftLeft]
  cases last
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at *
    have := grindingBits_le (2 * step) (by omega)
    have := grindingBits_le step (by omega)
    cost_calls [grindingBits_cost, skGrind_cost]
    len_facts [length_skGrind]
    omega

theorem natCasesOn_one {C : ℕ → Sort _} (z : C 0) (f : ∀ n, C (n + 1)) :
    (Nat.casesOn 1 z f : C 1) = f 0 := rfl

theorem natCasesOn_zero {C : ℕ → Sort _} (z : C 0) (f : ∀ n, C (n + 1)) :
    (Nat.casesOn 0 z f : C 0) = z := rfl

theorem length_skGkrLayers : ∀ n L, (skGkrLayers n L).length ≤ n * (8 * (L + n) + 20)
  | 0, _ => by simp [skGkrLayers]
  | 1, L => by
    have := length_skGkrStep 1 true L (by omega)
    simp only [skGkrLayers]; omega
  | k + 2, L => by
    simp only [skGkrLayers]
    split_ifs
    · have h1 := length_skGkrStep 1 false L (by omega)
      have h2 := length_skGkrLayers (k + 1) (1 + L)
      rw [List.length_append]
      rw [show 1 + L + (k + 1) = L + (k + 2) by omega] at h2
      have : (k + 2) * (8 * (L + (k + 2)) + 20) =
          (k + 1) * (8 * (L + (k + 2)) + 20) + (8 * (L + (k + 2)) + 20) := by ring
      omega
    · have h1 := length_skGkrStep 2 (decide (k = 0)) L (by omega)
      have h2 := length_skGkrLayers k (2 + L)
      rw [List.length_append]
      rw [show 2 + L + k = L + (k + 2) by omega] at h2
      have : (k + 2) * (8 * (L + (k + 2)) + 20) =
          k * (8 * (L + (k + 2)) + 20) + 2 * (8 * (L + (k + 2)) + 20) := by ring
      omega

/-- The GKR walk's skeleton (`skGkrLayers.c451`), `n` levels from `L` coordinates. -/
theorem skGkrLayers_cost (hP : Includes P skGkrLayers.c451.costDeps) :
    ∀ n L, L + n < 2 ^ 40 →
      machineCost P skGkrLayers.c451.costIdx [encodeValue n, encodeValue L] ≤
        n * (3200 * (L + n) + 7500) + 5
  | 0, L, _ => by
    rw [skGkrLayers.c451.costEq P hP]
    simp
  | 1, L, _ => by
    rw [skGkrLayers.c451.costEq P hP, natCasesOn_one, natCasesOn_zero]
    have := skGkrStep_cost P (by includes) 1 true L
    cost_calls []
    omega
  | k + 2, L, h => by
    rw [skGkrLayers.c451.costEq P hP]
    dsimp only
    rw [limbs_of_lt (by omega : k + 2 < 2 ^ 64), limbs_of_lt (by omega : k + 1 < 2 ^ 64),
      limbs_of_lt (by omega : k < 2 ^ 64), limbs_of_lt (by omega : k % 2 < 2 ^ 64)]
    split_ifs with hk
    · have h1 := skGkrStep_cost P (by includes) 1 false L
      have h2 := skGkrLayers_cost hP (k + 1) (1 + L) (by omega)
      have h3 := append_cost P (by includes) (skGkrStep 1 false L) (skGkrLayers (k + 1) (1 + L))
      have h4 := length_skGkrStep 1 false L (by omega)
      rw [show 1 + L + (k + 1) = L + (k + 2) by omega] at h2
      rw [limbs_of_lt (by omega : 1 + L < 2 ^ 64), limbs_of_lt (by omega : L < 2 ^ 64)]
      have : (k + 2) * (3200 * (L + (k + 2)) + 7500) =
          (k + 1) * (3200 * (L + (k + 2)) + 7500) + (3200 * (L + (k + 2)) + 7500) := by ring
      simp only [max_self]
      omega
    · have h1 := skGkrStep_cost P (by includes) 2 (decide (k = 0)) L
      have h2 := skGkrLayers_cost hP k (2 + L) (by omega)
      have h3 := append_cost P (by includes) (skGkrStep 2 (decide (k = 0)) L)
        (skGkrLayers k (2 + L))
      have h4 := length_skGkrStep 2 (decide (k = 0)) L (by omega)
      rw [show 2 + L + k = L + (k + 2) by omega] at h2
      rw [limbs_of_lt (by omega : 2 + L < 2 ^ 64), limbs_of_lt (by omega : L < 2 ^ 64)]
      have : (k + 2) * (3200 * (L + (k + 2)) + 7500) =
          k * (3200 * (L + (k + 2)) + 7500) + 2 * (3200 * (L + (k + 2)) + 7500) := by ring
      simp only [max_self]
      omega

theorem length_skBus (depth : ℕ) (hd : depth ≤ 64) : (skBus depth).length ≤ 35000 := by
  obtain ⟨c1, -⟩ := skConsts
  have := length_skGkrLayers depth 0
  have := length_skGrind (busGrindingBits depth)
  have := length_skBytecodeShare
  have hm : depth * (8 * (0 + depth) + 20) ≤ 64 * (8 * (0 + 64) + 20) :=
    Nat.mul_le_mul hd (by omega)
  have h16 : 2 ^ busBits = 16 := by rw [c1]; norm_num
  simp only [skBus, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at *
  omega

/-- The bus phase's skeleton (`skBus.c449`), a depth of at most `64`: at most `16000000`. -/
theorem skBus_cost (hP : Includes P skBus.c449.costDeps) (depth : ℕ) (hd : depth ≤ 64) :
    machineCost P skBus.c449.costIdx [encodeValue depth] ≤ 16000000 := by
  obtain ⟨c1, -⟩ := skConsts
  have h2 : 2 ^ depth ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hd
  have hl2 : limbCount (2 ^ depth) ≤ 2 := by
    have := limbs_le_wl h2
    unfold limbsBelowTwoPow at this
    omega
  have h16 : 2 ^ busBits = 16 := by rw [c1]; norm_num
  have hbg : busGrindingBits depth ≤ 128 := grindingBits_le _ (by omega)
  have hg := skGkrLayers_cost P (by includes) depth 0 (by omega)
  have hgl := length_skGkrLayers depth 0
  have hm : depth * (8 * (0 + depth) + 20) ≤ 64 * (8 * (0 + 64) + 20) :=
    Nat.mul_le_mul hd (by omega)
  have hm' : depth * (3200 * (0 + depth) + 7500) ≤ 64 * (3200 * (0 + 64) + 7500) :=
    Nat.mul_le_mul hd (by omega)
  rw [skBus.c449.costEq P hP]
  simp only [Nat.one_shiftLeft]
  cost_calls [grindingBits_cost, skGrind_cost, skBytecodeShare_cost]
  len_facts [length_skGrind, length_skBytecodeShare]
  omega

theorem length_skOpen : skOpen.length ≤ 36 := by
  have := length_skSum 3 (List.replicate qkeccakSlotBits false)
  obtain ⟨-, -, -, -, -, -, -, c8, -⟩ := skConsts
  simp only [skOpen, List.length_replicate] at *
  omega

theorem length_layers (L : ℕ) :
    ((List.range keccakDepth).flatMap fun _ ↦ skLayer (L - 4 + keccakSegmentBits)).length ≤
      12 * (6 * L + 146) := by
  obtain ⟨-, -, c3, -, c5, -⟩ := skConsts
  rw [List.length_flatMap, List.map_const', List.sum_replicate, List.length_range, c3, smul_eq_mul]
  have := length_skLayer (L - 4 + keccakSegmentBits)
  omega

theorem length_skKeccak (L : ℕ) : (skKeccak L).length ≤ 72 * L + 2000 := by
  obtain ⟨-, -, -, -, c5, c6, -, c8, c9, -⟩ := skConsts
  have := length_layers L
  have := length_skOpen
  have := length_skGrind (grindingBits (keccakSegmentBits + keccakLaneBits))
  have := length_skSum 3 (List.replicate 4 false)
  simp only [skKeccak, List.length_append, List.length_replicate, List.length_singleton] at *
  omega

/-- The Keccak reduction's skeleton (`skKeccak.c465`), at a point of `L` coordinates. -/
theorem skKeccak_cost (hP : Includes P skKeccak.c465.costDeps) (L : ℕ) (hL : L ≤ 2 ^ 30) :
    machineCost P skKeccak.c465.costIdx [encodeValue L] ≤ 40000 * L + 1000000 := by
  obtain ⟨-, -, c3, c4, c5, c6, -, c8, c9, -⟩ := skConsts
  have hlay := length_layers L
  have hop := length_skOpen
  have := grindingBits_le (keccakSegmentBits + keccakLaneBits) (by omega)
  have hr := rangeLoop_cost P (by includes) keccakDepth [] (by omega)
  have hmap := map_cost P (by includes) _ (.closure skKeccak.c465.lam0.costIdx [encodeValue L])
    (fun x ↦ RunsApp.of_spec (skKeccak.c465.lam0.costSpec P (by includes) L x))
    (2600 * L + 44000) (List.range keccakDepth) (fun x _ ↦ by
      rw [appCost_fn, List.singleton_append, skKeccak.c465.lam0.costEq P (by includes)]
      have := skLayer_cost P (by includes) (L - 4 + keccakSegmentBits)
      have := bitLength_cost' P (by includes) (keccakSegments - 1)
      rw [limbs_of_lt (by omega : L < 2 ^ 64), limbs_of_lt (by omega : keccakDepth < 2 ^ 64),
        limbs_of_lt (by omega : keccakSegments < 2 ^ 64),
        limbs_of_lt (by omega : L - 4 + keccakSegmentBits < 2 ^ 64),
        limbs_of_lt (by omega : L - 4 < 2 ^ 64), limbs_of_lt (by omega : keccakSegmentBits < 2 ^ 64)]
      simp only [List.length_singleton, max_self]
      omega)
  have hfl := flatten_cost P (by includes) (6 * L + 146)
    (List.map (fun _ ↦ skLayer (L - 4 + keccakSegmentBits)) (List.range keccakDepth))
    (fun l hl ↦ by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      have := length_skLayer (L - 4 + keccakSegmentBits)
      omega)
  have hlen : (List.range keccakDepth).length = 12 := by rw [List.length_range, c3]
  rw [List.length_map, hlen] at hfl
  rw [hlen] at hmap
  rw [skKeccak.c465.costEq P hP]
  cost_calls [grindingBits_cost, skGrind_cost, skSum_cost, bitLength_cost']
  len_facts [length_skGrind, length_skSum]
  omega

/-! ### The opening's skeleton -/

theorem sqSamples_le (depth : ℕ) : ∀ fuel rem, sqSamples depth fuel rem ≤ fuel
  | 0, _ => le_rfl
  | fuel + 1, rem => by
    unfold sqSamples
    split_ifs
    · omega
    · have := sqSamples_le depth fuel (rem - min (128 / depth) rem); omega

/-- The query samples' count (`sqSamples.c476`): at most `31·fuel + 10`. -/
theorem sqSamples_cost (hP : Includes P sqSamples.c476.costDeps) (depth : ℕ) (hd : depth < 2 ^ 64) :
    ∀ fuel rem, fuel < 2 ^ 60 → rem < 2 ^ 64 →
      machineCost P sqSamples.c476.costIdx [encodeValue depth, encodeValue fuel, encodeValue rem] ≤
        31 * fuel + 10
  | 0, rem, _, _ => by rw [sqSamples.c476.costEq P hP]; simp
  | fuel + 1, rem, hf, hr => by
    rw [sqSamples.c476.costEq P hP]
    dsimp only
    have hsub : rem - min (128 / depth) rem ≤ rem := Nat.sub_le _ _
    have := sqSamples_cost hP depth hd fuel (rem - min (128 / depth) rem) (by omega) (by omega)
    have := sqSamples_le depth fuel (rem - min (128 / depth) rem)
    have : 128 / depth ≤ 128 := Nat.div_le_self _ _
    have : min (128 / depth) rem ≤ 128 := (min_le_left _ _).trans this
    rw [limbs_of_lt (by omega : fuel + 1 < 2 ^ 64), limbs_of_lt hr, limbs_of_lt hd,
      limbs_of_lt (by omega : 128 / depth < 2 ^ 64),
      limbs_of_lt (by omega : min (128 / depth) rem < 2 ^ 64),
      limbs_of_lt (by omega : 1 + sqSamples depth fuel (rem - min (128 / depth) rem) < 2 ^ 64),
      limbs_of_lt (by omega : sqSamples depth fuel (rem - min (128 / depth) rem) < 2 ^ 64)]
    split_ifs <;> omega

/-- A level's commitment shape (`levelShape.c446`): at most `11`. -/
theorem levelShape_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.levelShape.c446.costDeps)
    (m : ℕ) (l : Whir.Level) (w : ℕ) (hm : m < 2 ^ 60 := by omega) (hf : l.fold < 2 ^ 60 := by omega)
    (hr : l.logInvRate < 2 ^ 60 := by omega) :
    machineCost P Auto.LeanVM.Protocol.Verifier.levelShape.c446.costIdx [encodeValue m, encodeValue l,
      encodeValue w] ≤ 11 := by
  rw [Auto.LeanVM.Protocol.Verifier.levelShape.c446.costEq P hP]
  cost_calls []
  omega

/-- A level's facts the skeleton's prices need. -/
@[expose] def LevelOk (l : Whir.Level) : Prop := l.fold < 50 ∧ l.logInvRate < 50 ∧ l.queries < 2 ^ 20

instance (l : Whir.Level) : Decidable (LevelOk l) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem length_skMidTail (logN A : ℕ) (l n : Whir.Level) :
    (skMidTail logN A l n).length ≤ l.fold + logN + l.queries + 8 := by
  have := sqSamples_le (logN - A + l.logInvRate) l.queries l.queries
  have := length_skGrind Whir.oodGrindingBits
  have := length_skGrind Whir.queryGrindingBits
  simp only [skMidTail, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at *
  omega

/-- A level's tail's skeleton (`skMidTail.c475`). -/
theorem skMidTail_cost (hP : Includes P skMidTail.c475.costDeps) (logN A : ℕ) (l n : Whir.Level)
    (hN : logN < 2 ^ 20) (hA : A < 2 ^ 60) (hl : LevelOk l) (hn : LevelOk n) :
    machineCost P skMidTail.c475.costIdx [encodeValue logN, encodeValue A, encodeValue l,
      encodeValue n] ≤ 150 * (l.fold + logN + l.queries) + 1000 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, c14, -, -, c17, -⟩ := skConsts
  obtain ⟨hl1, hl2, hl3⟩ := hl
  obtain ⟨hn1, hn2, hn3⟩ := hn
  have hsq := sqSamples_le (logN - A + l.logInvRate) l.queries l.queries
  have hs := sqSamples_cost P (by includes) (logN - A + l.logInvRate) (by omega) l.queries l.queries
    (by omega) (by omega)
  have h2 : 2 ^ n.fold < 2 ^ 50 := Nat.pow_lt_pow_right (by norm_num) hn1
  rw [skMidTail.c475.costEq P hP]
  simp only [Nat.one_shiftLeft]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

/-- A price of `skLevels` (`skLevels.c472`) from `A` folds made. -/
@[expose] def skLevelsPrice (logN : ℕ) : ℕ → List Whir.Level → ℕ
  | _, [] => 3
  | A, [l] => 377 * l.fold + 15 * (2 ^ (logN - (A + l.fold)) + l.fold) + 40
  | A, l :: n :: rest => 377 * l.fold + (150 * (l.fold + logN + l.queries) + 1000) +
      11 * (8 * l.fold + logN + l.queries + 8) + skLevelsPrice logN (A + l.fold) (n :: rest) + 50

/-- **The levels' skeleton** (`skLevels.c472`): at most `skLevelsPrice`. -/
theorem skLevels_cost (hP : Includes P skLevels.c472.costDeps) (logN : ℕ) (hN : logN < 50) :
    ∀ (levels : List Whir.Level) (A : ℕ), (∀ l ∈ levels, LevelOk l) →
      A + 50 * levels.length < 2 ^ 40 →
      machineCost P skLevels.c472.costIdx [encodeValue logN, encodeValue A, encodeValue levels] ≤
        skLevelsPrice logN A levels
  | [], A, _, _ => by rw [skLevels.c472.costEq_nil P hP]; rfl
  | [l], A, hl, hA => by
    obtain ⟨hl1, hl2, hl3⟩ := hl l (by simp)
    simp only [List.length_singleton] at hA
    have h2' : 2 ^ (logN - (A + l.fold)) < 2 ^ 50 :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [skLevels.c472.costEq_cons P hP]
    dsimp only
    simp only [Nat.one_shiftLeft]
    have := skFoldRounds_cost P (by includes) l.fold (by omega)
    cost_calls []
    have := length_skFoldRounds l.fold
    unfold skLevelsPrice
    omega
  | l :: n :: rest, A, hl, hA => by
    have hl' := hl l (by simp)
    have hn' := hl n (by simp)
    obtain ⟨hl1, hl2, hl3⟩ := hl'
    simp only [List.length_cons] at hA
    rw [skLevels.c472.costEq_cons P hP]
    dsimp only
    have h1 := skFoldRounds_cost P (by includes) l.fold (by omega)
    have h2 := skMidTail_cost P (by includes) logN (A + l.fold) l n (by omega) (by omega)
      ⟨hl1, hl2, hl3⟩ hn'
    have h3 := skLevels_cost hP logN hN (n :: rest) (A + l.fold)
      (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons]; omega)
    have h4 := length_skFoldRounds l.fold
    have h5 := length_skMidTail logN (A + l.fold) l n
    cost_calls []
    simp only [List.length_append] at *
    unfold skLevelsPrice
    omega

/-- The stack's commitment's skeleton (`skCommitStack.c445`): at most `3600`. -/
theorem skCommitStack_cost (hP : Includes P skCommitStack.c445.costDeps) (logN ρ : ℕ)
    (hN : logN < 2 ^ 60) (hρ : ρ < 2 ^ 60) :
    machineCost P skCommitStack.c445.costIdx [encodeValue logN, encodeValue ρ] ≤ 3600 := by
  rw [skCommitStack.c445.costEq P hP]
  have hl := ladder_cost P (by includes) logN ρ (by omega) (by omega)
  rcases h : Whir.ladder logN ρ with _ | lv
  · dsimp only; omega
  · rcases lv with _ | ⟨l, rest⟩
    · dsimp only; omega
    · dsimp only
      obtain ⟨h1, h2⟩ := ladder_head h
      have h6 : l.fold = 6 := h1
      simp only [Nat.one_shiftLeft]
      have := levelShape_cost P (by includes) logN l (2 ^ l.fold) (by omega) (by omega) (by omega)
      rw [h6]
      rw [h6] at this
      cost_calls []
      omega

theorem length_skCommitStack (logN ρ : ℕ) : (skCommitStack logN ρ).length ≤ 1 := by
  unfold skCommitStack
  split <;> simp

theorem ladder_some_bounds {μ ρ : ℕ} {lv : List Whir.Level} (h : Whir.ladder μ ρ = some lv) :
    μ < 31 ∧ ρ < 5 := by
  unfold Whir.ladder at h
  split_ifs at h with ha
  · obtain ⟨-, h2, -, h4⟩ := ha
    exact ⟨by unfold Whir.maxLogStack at h2; omega, by omega⟩

/-- The ladders' facts at every admissible shape, by the kernel. -/
theorem ladder_facts_all : ∀ μ < 31, ∀ ρ < 5, (Whir.ladder μ ρ).all (fun lv ↦
    decide ((∀ l ∈ lv, LevelOk l) ∧ lv.length ≤ 6 ∧ skLevelsPrice μ 0 lv ≤ 110000 ∧
      (skLevels μ 0 lv).length ≤ 410)) = true := by
  decide +kernel

theorem ladder_facts {μ ρ : ℕ} {lv : List Whir.Level} (h : Whir.ladder μ ρ = some lv) :
    (∀ l ∈ lv, LevelOk l) ∧ lv.length ≤ 6 ∧ skLevelsPrice μ 0 lv ≤ 110000 ∧
      (skLevels μ 0 lv).length ≤ 410 := by
  obtain ⟨h1, h2⟩ := ladder_some_bounds h
  have := ladder_facts_all μ h1 ρ h2
  rw [h] at this
  simpa using this

theorem length_skWhir (μ ρ : ℕ) : (skWhir μ ρ).length ≤ 410 := by
  unfold skWhir
  split
  · next lv h => exact (ladder_facts h).2.2.2
  · simp

/-- **The opening's skeleton** (`skWhir.c471`): at most `113600`. -/
theorem skWhir_cost (hP : Includes P skWhir.c471.costDeps) (μ ρ : ℕ) (hμ : μ < 2 ^ 64)
    (hρ : ρ < 2 ^ 64) :
    machineCost P skWhir.c471.costIdx [encodeValue μ, encodeValue ρ] ≤ 113600 := by
  rw [skWhir.c471.costEq P hP]
  have hl := ladder_cost P (by includes) μ ρ hμ hρ
  rcases h : Whir.ladder μ ρ with _ | lv
  · dsimp only; omega
  · dsimp only
    obtain ⟨h1, h2, h3, -⟩ := ladder_facts h
    have hb := ladder_some_bounds h
    have := skLevels_cost P (by includes) μ (by omega) lv 0 h1 (by omega)
    omega

/-! ### The body's skeleton -/

/-- An admissible lite layout: a stack of at most `2^30`, memory and bytecode of log-size at most
`30`, six tables of log-heights at most `30`. -/
@[expose] def LayOk (lay : LayoutLite) : Prop :=
  lay.stackLog ≤ 30 ∧ lay.logMemory ≤ 30 ∧ lay.logBytecode ≤ 30 ∧
    lay.tableLogHeights.length ≤ 6 ∧ ∀ h ∈ lay.tableLogHeights, h ≤ 30

/-- **The body's skeleton's length** at an admissible layout and rate: at most `40000`. -/
theorem length_skBodyL (lay : LayoutLite) (ρ : ℕ) (hl : LayOk lay) :
    (skBodyL lay ρ).length ≤ 40000 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hl
  have := length_skCommitStack lay.stackLog ρ
  have := length_skOod lay.stackLog
  have := length_skBus _ (pushDepthL_le lay.logMemory lay.logBytecode lay.tableLogHeights
    (by omega) (by omega) h5)
  have := length_skTablePhaseL lay.tableLogHeights
  have := foldl_max_le 30 lay.tableLogHeights 0 (by omega) h5
  have := length_skKeccak (kLen lay.tableLogHeights)
  have := kLen_le lay.tableLogHeights 30 h5
  have := length_skRing
  have := length_skWhir lay.stackLog ρ
  simp only [skBodyL, List.length_append, List.length_singleton] at *
  omega

theorem length_skBodyHeadL (lay : LayoutLite) (ρ : ℕ) (hl : LayOk lay) :
    (skBodyHeadL lay ρ).length ≤ 40000 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hl
  have := length_skCommitStack lay.stackLog ρ
  have := length_skOod lay.stackLog
  have := length_skBus _ (pushDepthL_le lay.logMemory lay.logBytecode lay.tableLogHeights
    (by omega) (by omega) h5)
  have := length_skTablePhaseL lay.tableLogHeights
  have := foldl_max_le 30 lay.tableLogHeights 0 (by omega) h5
  have := length_skKeccak (kLen lay.tableLogHeights)
  have := kLen_le lay.tableLogHeights 30 h5
  have := length_skRing
  simp only [skBodyHeadL, List.length_append, List.length_singleton] at *
  omega

/-- **The body's skeleton** (`skBodyLC`) at an admissible layout and rate: at most `10^9`. -/
theorem skBodyL_cost (hP : Includes P skBodyLC.costDeps) (lay : LayoutLite) (ρ : ℕ)
    (hl : LayOk lay) (hρ : ρ ≤ 4) :
    machineCost P skBodyLC.costIdx [encodeValue lay, encodeValue ρ] ≤ 1000000000 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hl
  have hd := pushDepthL_le lay.logMemory lay.logBytecode lay.tableLogHeights (by omega) (by omega) h5
  have hm := foldl_max_le 30 lay.tableLogHeights 0 (by omega) h5
  have hk := kLen_le lay.tableLogHeights 30 h5
  have c1 := skCommitStack_cost P (by includes) lay.stackLog ρ (by omega) (by omega)
  have c2 := skOod_cost P (by includes) lay.stackLog
  have c3 := pushDepthL_cost P (by includes) lay.logMemory lay.logBytecode lay.tableLogHeights
    (by omega) (by omega) h5
  have c4 := skBus_cost P (by includes) _ hd
  have c5 := skTablePhaseL_cost P (by includes) lay.tableLogHeights h4 h5
  have c6 := kLen_cost P (by includes) lay.tableLogHeights h4 h5
  have c7 := skKeccak_cost P (by includes) (kLen lay.tableLogHeights) (by omega)
  have c8 := skRing_cost P (by includes)
  have c9 := skWhir_cost P (by includes) lay.stackLog ρ (by omega) (by omega)
  have l1 := length_skCommitStack lay.stackLog ρ
  have l2 := length_skOod lay.stackLog
  have l3 := length_skBus _ hd
  have l4 := length_skTablePhaseL lay.tableLogHeights
  have l5 := length_skKeccak (kLen lay.tableLogHeights)
  have l6 := length_skRing
  have l7 := length_skWhir lay.stackLog ρ
  rw [skBodyLC.costEq P hP]
  cost_calls []
  simp only [List.length_append, List.length_singleton] at *
  omega

/-- The body's skeleton before the opening's trace (`skBodyHeadL.c494`): at most `10^9`. -/
theorem skBodyHeadL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.skBodyHeadL.c494.costDeps)
    (lay : LayoutLite) (ρ : ℕ) (hl : LayOk lay) (hρ : ρ ≤ 4) :
    machineCost P Auto.LeanVM.Extraction.AS.skBodyHeadL.c494.costIdx [encodeValue lay,
      encodeValue ρ] ≤ 1000000000 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hl
  have hd := pushDepthL_le lay.logMemory lay.logBytecode lay.tableLogHeights (by omega) (by omega) h5
  have hm := foldl_max_le 30 lay.tableLogHeights 0 (by omega) h5
  have hk := kLen_le lay.tableLogHeights 30 h5
  have c1 := skCommitStack_cost P (by includes) lay.stackLog ρ (by omega) (by omega)
  have c2 := skOod_cost P (by includes) lay.stackLog
  have c3 := pushDepthL_cost P (by includes) lay.logMemory lay.logBytecode lay.tableLogHeights
    (by omega) (by omega) h5
  have c4 := skBus_cost P (by includes) _ hd
  have c5 := skTablePhaseL_cost P (by includes) lay.tableLogHeights h4 h5
  have c6 := kLen_cost P (by includes) lay.tableLogHeights h4 h5
  have c7 := skKeccak_cost P (by includes) (kLen lay.tableLogHeights) (by omega)
  have c8 := skRing_cost P (by includes)
  have l1 := length_skCommitStack lay.stackLog ρ
  have l2 := length_skOod lay.stackLog
  have l3 := length_skBus _ hd
  have l4 := length_skTablePhaseL lay.tableLogHeights
  have l5 := length_skKeccak (kLen lay.tableLogHeights)
  have l6 := length_skRing
  rw [Auto.LeanVM.Extraction.AS.skBodyHeadL.c494.costEq P hP]
  cost_calls []
  simp only [List.length_append, List.length_singleton] at *
  omega

/-! ### The decoders -/

/-- `List.mapM` with `Option` (`mapM.loop.c441`): the closure's price and `43` per element, `11` per
element of the accumulator, `10`. -/
theorem mapMLoop_cost (hP : Includes P Auto.List.mapM.loop.c441.costDeps) {α β : Type}
    [MachineEncoding α] [MachineEncoding β] (f : α → Option β) (fVal : MachineValue)
    (hf : ∀ a, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : α, appCost P fVal [encodeValue a] ≤ B) :
    ∀ (xs : List α) (acc : List β),
      machineCost P Auto.List.mapM.loop.c441.costIdx [fVal, encodeValue xs, encodeValue acc] ≤
        (B + 43) * xs.length + 11 * acc.length + 10
  | [], acc => by
    rw [Auto.List.mapM.loop.c441.costEq_nil P hP f fVal hf]
    have := reverseAux_cost P (by includes) acc []
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
    omega
  | x :: xs, acc => by
    rw [Auto.List.mapM.loop.c441.costEq_cons P hP f fVal hf]
    have h1 := hB x
    have h2 := bind_cost P (by includes) _ (.closure 442 [encodeValue xs, fVal, encodeValue acc])
      (fun b ↦ RunsApp.of_spec (Auto.List.mapM.loop.c441.lam0.costSpec P (by includes) xs f fVal hf
        acc b)) ((B + 43) * xs.length + 11 * acc.length + 32) (fun b ↦ by
          rw [appCost_fn, show (442 : ℕ) = Auto.List.mapM.loop.c441.lam0.costIdx from rfl]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.List.mapM.loop.c441.lam0.costEq P (by includes) xs f fVal hf]
          have := mapMLoop_cost hP f fVal hf B hB xs (b :: acc)
          simp only [List.length_cons] at this
          omega) (f x)
    simp only [List.length_cons]
    have : (B + 43) * (xs.length + 1) = (B + 43) * xs.length + B + 43 := by ring
    omega

/-- The reads' values (`mapM` with `decSizesLC.lam1`): `45` per event, `10`. -/
theorem mapMReads_cost (hP : Includes P Auto.List.mapM.loop.c441.costDeps)
    (h1 : Includes P decSizesLC.lam1.costDeps) (xs : List EvP) :
    machineCost P Auto.List.mapM.loop.c441.costIdx [.closure decSizesLC.lam1.costIdx [],
      encodeValue xs, encodeValue ([] : List E)] ≤ 45 * xs.length + 10 := by
  have := mapMLoop_cost P hP (fun p : EvP ↦ p.1) (.closure decSizesLC.lam1.costIdx [])
    (fun p ↦ RunsApp.of_spec (decSizesLC.lam1.costSpec P h1 p)) 2 (fun p ↦ by
      rw [appCost_fn, List.nil_append, decSizesLC.lam1.costEq P h1]; rfl) xs []
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at this
  omega

theorem listCases_le {α : Type} (l : List α) (a b : ℕ) :
    (List.casesOn l a (fun _ _ ↦ b) : ℕ) ≤ max a b := by
  cases l <;> simp

theorem listRec_le {α : Type} (l : List α) (a b : ℕ) :
    (List.rec a (fun _ _ _ ↦ b) l : ℕ) ≤ max a b := by
  cases l <;> simp

/-- A fold round's challenges (`decRoundP.c486`): at most `200`. -/
theorem decRoundP_cost (hP : Includes P decRoundP.c486.costDeps) (h : List EvP) :
    machineCost P decRoundP.c486.costIdx [encodeValue h] ≤ 200 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c16, -⟩ := skConsts
  rw [decRoundP.c486.costEq P hP]
  have hg : (skGrind Whir.foldGrindingBits).length = 1 := by rw [c16]; rfl
  have b1 := bind_cost P (by includes) _ (.closure decRoundP.c486.lam0.lam1.costIdx [])
    (fun p ↦ RunsApp.of_spec (decRoundP.c486.lam0.lam1.costSpec P (by includes) p)) 2 (fun p ↦ by
      rw [appCost_fn, List.nil_append, decRoundP.c486.lam0.lam1.costEq P (by includes)]; rfl)
    (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h).head?
  have b2 := bind_cost P (by includes) _ (.closure decRoundP.c486.lam0.costIdx
      [encodeValue (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)])
    (fun a ↦ RunsApp.of_spec (decRoundP.c486.lam0.costSpec P (by includes) _ a)) 58 (fun a ↦ by
      rw [appCost_fn, List.singleton_append, decRoundP.c486.lam0.costEq P (by includes)]
      have := drop_cost P (by includes) 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)
        (by norm_num)
      have := bind_cost P (by includes) _ (.closure decRoundP.c486.lam0.lam1.costIdx [])
        (fun p ↦ RunsApp.of_spec (decRoundP.c486.lam0.lam1.costSpec P (by includes) p)) 2 (fun p ↦ by
          rw [appCost_fn, List.nil_append, decRoundP.c486.lam0.lam1.costEq P (by includes)]; rfl)
        (List.drop 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)).head?
      have := optionMap_cost P (by includes) _ (.closure decRoundP.c486.lam0.lam0.costIdx
          [encodeValue a])
        (fun b ↦ RunsApp.of_spec (decRoundP.c486.lam0.lam0.costSpec P (by includes) a b)) 6
        ((List.drop 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)).head?.bind
          fun p ↦ p.2) (fun b _ ↦ by
          rw [appCost_fn, List.singleton_append, decRoundP.c486.lam0.lam0.costEq P (by includes)]
          rfl)
      have := listRec_le (List.drop 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)) 1 5
      simp only [List.length_singleton]
      omega) ((List.drop (4 + (skGrind Whir.foldGrindingBits).length) h).head?.bind fun p ↦ p.2)
  have := skGrind_cost P (by includes) Whir.foldGrindingBits
  have := length_cost P (by includes) (skGrind Whir.foldGrindingBits) (by omega)
  have := drop_cost P (by includes) (4 + (skGrind Whir.foldGrindingBits).length) h (by omega)
  have := listCases_le (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h) 1 5
  rw [hg] at *
  rw [limbs_of_lt (by norm_num : 4 + 1 < 2 ^ 64), limbs_of_lt (by norm_num : 1 < 2 ^ 64)]
  omega

/-- The fold rounds' challenges (`decRoundsP.c483`): at most `(500·n + 1100)·n + 7`. -/
theorem decRoundsP_cost (hP : Includes P decRoundsP.c483.costDeps) :
    ∀ (n : ℕ) (h : List EvP), n < 2 ^ 30 →
      machineCost P decRoundsP.c483.costIdx [encodeValue n, encodeValue h] ≤ (500 * n + 1100) * n + 7
  | 0, h, _ => by rw [decRoundsP.c483.costEq P hP]; simp
  | k + 1, h, hk => by
    rw [decRoundsP.c483.costEq P hP]
    dsimp only
    have h1 := skFoldRound_cost P (by includes)
    have h2 := decRoundP_cost P (by includes) (List.take skFoldRound.length h)
    have h3 := bind_cost P (by includes) _ (.closure 485 [encodeValue k, encodeValue h])
      (fun r ↦ RunsApp.of_spec (decRoundsP.c483.lam1.costSpec P (by includes) k h r))
      ((500 * k + 1100) * k + 7 + 500 * k + 450) (fun r ↦ by
        rw [appCost_fn, show (485 : ℕ) = decRoundsP.c483.lam1.costIdx from rfl]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [decRoundsP.c483.lam1.costEq P (by includes)]
        have := skFoldRounds_cost P (by includes) k (by omega)
        have := skFoldRound_cost P (by includes)
        have := decRoundsP_cost hP k (List.take (skFoldRounds k).length (List.drop skFoldRound.length h))
          (by omega)
        have := optionMap_cost P (by includes) _ (.closure decRoundsP.c483.lam0.costIdx [encodeValue r])
          (fun rs ↦ RunsApp.of_spec (decRoundsP.c483.lam0.costSpec P (by includes) r rs)) 6
          (decRoundsP k (List.take (skFoldRounds k).length (List.drop skFoldRound.length h)))
          (fun rs _ ↦ by
            rw [appCost_fn, List.singleton_append, decRoundsP.c483.lam0.costEq P (by includes)]; rfl)
        have := length_skFoldRounds k
        have := length_skFoldRound
        cost_calls []
        omega) (decRoundP (List.take skFoldRound.length h))
    have := length_skFoldRound
    cost_calls []
    have : (500 * (k + 1) + 1100) * (k + 1) = (500 * k + 1100) * k + 1000 * k + 1600 := by ring
    omega

/-- A level's high part (`decHighP.c492`): at most `64·fold + 43`. -/
theorem decHighP_cost (hP : Includes P decHighP.c492.costDeps) (fold : ℕ) (h : List EvP)
    (hf : fold < 2 ^ 30) :
    machineCost P decHighP.c492.costIdx [encodeValue fold, encodeValue h] ≤ 64 * fold + 43 := by
  rw [decHighP.c492.costEq P hP]
  have := mapMReads_cost P (by includes) (by includes) (List.take fold (List.drop 1 h))
  have : (List.take fold (List.drop 1 h)).length ≤ fold := List.length_take_le _ _
  cost_calls []
  omega

theorem skLevelsPrice_cons₂ (logN A : ℕ) (l n : Whir.Level) (rest : List Whir.Level) :
    skLevelsPrice logN A (l :: n :: rest) = 377 * l.fold + (150 * (l.fold + logN + l.queries) + 1000) +
      11 * (8 * l.fold + logN + l.queries + 8) + skLevelsPrice logN (A + l.fold) (n :: rest) + 50 := rfl

theorem length_skLevels_le (logN : ℕ) : ∀ (levels : List Whir.Level) (A : ℕ),
    (skLevels logN A levels).length ≤ skLevelsPrice logN A levels
  | [], A => by simp [skLevels, skLevelsPrice]
  | [l], A => by
    simp only [skLevels, skLevelsPrice, List.length_append, List.length_replicate, length_skFoldRounds]
    omega
  | l :: n :: rest, A => by
    have := length_skLevels_le logN (n :: rest) (A + l.fold)
    have := length_skMidTail logN (A + l.fold) l n
    rw [skLevelsPrice_cons₂]
    simp only [skLevels, List.length_append, length_skFoldRounds] at *
    omega

/-- A price of `decLevelsP` (`decLevelsP.c480`) from `A` folds made. -/
@[expose] def decLevelsPrice (logN : ℕ) : ℕ → List Whir.Level → ℕ
  | _, [] => 3
  | A, [l] => (500 * l.fold + 1100) * l.fold + 1000 * l.fold +
      64 * (2 ^ (logN - (A + l.fold)) + l.fold) + 210
  | A, l :: n :: rest => (500 * l.fold + 1100) * l.fold + 1100 * l.fold +
      (150 * (l.fold + logN + l.queries) + 1000) + 45 * (skMidTail logN (A + l.fold) l n).length +
      skLevelsPrice logN (A + l.fold) (n :: rest) + 30 * (skLevels logN (A + l.fold) (n :: rest)).length +
      decLevelsPrice logN (A + l.fold) (n :: rest) + 410

/-- **The cut levels' trace** (`decLevelsP.c480`): at most `decLevelsPrice`, whatever the events. -/
theorem decLevelsP_cost (hP : Includes P decLevelsP.c480.costDeps) (logN : ℕ) (hN : logN < 50) :
    ∀ (levels : List Whir.Level) (A : ℕ) (h : List EvP), (∀ l ∈ levels, LevelOk l) →
      A + 50 * levels.length < 2 ^ 40 → skLevelsPrice logN A levels < 2 ^ 60 →
      machineCost P decLevelsP.c480.costIdx [encodeValue logN, encodeValue A, encodeValue levels,
        encodeValue h] ≤ decLevelsPrice logN A levels
  | [], A, h, _, _, _ => by rw [decLevelsP.c480.costEq_nil P hP]; rfl
  | [l], A, h, hl, hA, _ => by
    obtain ⟨hl1, hl2, hl3⟩ := hl l (by simp)
    simp only [List.length_singleton] at hA
    have h2 : 2 ^ (logN - (A + l.fold)) < 2 ^ 50 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [decLevelsP.c480.costEq_cons P hP]
    dsimp only
    have hlen := length_skFoldRounds l.fold
    have c1 := skFoldRounds_cost P (by includes) l.fold (by omega)
    have c2 := decRoundsP_cost P (by includes) l.fold (List.take (skFoldRounds l.fold).length h)
      (by omega)
    have c3 := bind_cost P (by includes) _ (.closure decLevelsP.c480.lam0.costIdx
        [encodeValue l, encodeValue logN, encodeValue A, encodeValue h])
      (fun rs ↦ RunsApp.of_spec (decLevelsP.c480.lam0.costSpec P (by includes) l logN A h rs))
      (461 * l.fold + 64 * (2 ^ (logN - (A + l.fold)) + l.fold) + 80) (fun rs ↦ by
        rw [appCost_fn]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [decLevelsP.c480.lam0.costEq P (by includes)]
        simp only [Nat.one_shiftLeft]
        have := mapMReads_cost P (by includes) (by includes) (List.take (2 ^ (logN - (A + l.fold)) +
          l.fold) (List.drop (skFoldRounds l.fold).length h))
        have := List.length_take_le (2 ^ (logN - (A + l.fold)) + l.fold)
          (List.drop (skFoldRounds l.fold).length h)
        have := optionMap_cost P (by includes) _ (.closure decLevelsP.c480.lam0.lam0.costIdx
            [encodeValue rs])
          (fun f ↦ RunsApp.of_spec (decLevelsP.c480.lam0.lam0.costSpec P (by includes) rs f)) 6
          (List.mapM (fun p : EvP ↦ p.1) (List.take (2 ^ (logN - (A + l.fold)) + l.fold)
            (List.drop (skFoldRounds l.fold).length h))) (fun f _ ↦ by
              rw [appCost_fn, List.singleton_append, decLevelsP.c480.lam0.lam0.costEq P (by includes)]
              rfl)
        cost_calls []
        omega) (decRoundsP l.fold (List.take (skFoldRounds l.fold).length h))
    cost_calls []
    unfold decLevelsPrice
    omega
  | l :: n :: rest, A, h, hl, hA, hPr => by
    have hl' := hl l (by simp)
    have hn' := hl n (by simp)
    obtain ⟨hl1, hl2, hl3⟩ := hl'
    simp only [List.length_cons] at hA
    rw [skLevelsPrice_cons₂] at hPr
    rw [decLevelsP.c480.costEq_cons P hP]
    dsimp only
    have hlen := length_skFoldRounds l.fold
    have hml := length_skMidTail logN (A + l.fold) l n
    have hsl := length_skLevels_le logN (n :: rest) (A + l.fold)
    have c1 := skFoldRounds_cost P (by includes) l.fold (by omega)
    have c2 := decRoundsP_cost P (by includes) l.fold (List.take (skFoldRounds l.fold).length h)
      (by omega)
    have c3 := bind_cost P (by includes) _ (.closure 493 [encodeValue n, encodeValue rest,
        encodeValue l, encodeValue logN, encodeValue A, encodeValue h])
      (fun rs ↦ RunsApp.of_spec (decLevelsP.c480.lam3.costSpec P (by includes) n rest l logN A h rs))
      (461 * l.fold + (150 * (l.fold + logN + l.queries) + 1000) + 45 * (skMidTail logN (A + l.fold) l n).length +
        skLevelsPrice logN (A + l.fold) (n :: rest) + 30 * (skLevels logN (A + l.fold) (n :: rest)).length +
        decLevelsPrice logN (A + l.fold) (n :: rest) + 64 * l.fold + 250) (fun rs ↦ by
        rw [appCost_fn, show (493 : ℕ) = decLevelsP.c480.lam3.costIdx from rfl]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [decLevelsP.c480.lam3.costEq P (by includes)]
        have d1 := skMidTail_cost P (by includes) logN (A + l.fold) l n (by omega) (by omega)
          ⟨hl1, hl2, hl3⟩ hn'
        have d2 := decHighP_cost P (by includes) l.fold (List.take (skMidTail logN (A + l.fold) l n).length
          (List.drop (skFoldRounds l.fold).length h)) (by omega)
        have d3 := bind_cost P (by includes) _ (.closure decLevelsP.c480.lam2.costIdx
            [encodeValue n, encodeValue rest, encodeValue l, encodeValue logN, encodeValue A,
              encodeValue rs, encodeValue (skMidTail logN (A + l.fold) l n).length, encodeValue (List.drop (skFoldRounds l.fold).length h)])
          (fun hi ↦ RunsApp.of_spec (decLevelsP.c480.lam2.costSpec P (by includes) n rest l logN A rs
            (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h) hi))
          (skLevelsPrice logN (A + l.fold) (n :: rest) + 27 * (skLevels logN (A + l.fold) (n :: rest)).length + 15 * (skMidTail logN (A + l.fold) l n).length +
            decLevelsPrice logN (A + l.fold) (n :: rest) + 90) (fun hi ↦ by
            rw [appCost_fn]
            simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
            rw [decLevelsP.c480.lam2.costEq P (by includes)]
            have e1 := skLevels_cost P (by includes) logN hN (n :: rest) (A + l.fold)
              (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons]; omega)
            have e2 := decLevelsP_cost hP logN hN (n :: rest) (A + l.fold)
              (List.take (skLevels logN (A + l.fold) (n :: rest)).length (List.drop (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h)))
              (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons]; omega)
              (by omega)
            have e3 := optionMap_cost P (by includes) _ (.closure decLevelsP.c480.lam1.costIdx
                [encodeValue rs, encodeValue hi])
              (fun tr ↦ RunsApp.of_spec (decLevelsP.c480.lam1.costSpec P (by includes) rs hi tr)) 9
              (decLevelsP logN (A + l.fold) (n :: rest)
                (List.take (skLevels logN (A + l.fold) (n :: rest)).length (List.drop (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h))))
              (fun tr _ ↦ by
                rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
                  decLevelsP.c480.lam1.costEq P (by includes)]
                rfl)
            cost_calls []
            omega) (decHighP l.fold (List.take (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h)))
        cost_calls []
        omega) (decRoundsP l.fold (List.take (skFoldRounds l.fold).length h))
    cost_calls []
    unfold decLevelsPrice
    omega

/-- The cut levels' prices at every admissible shape, by the kernel. -/
theorem ladder_dec_all : ∀ μ < 31, ∀ ρ < 5, (Whir.ladder μ ρ).all (fun lv ↦
    decide (decLevelsPrice μ 0 lv ≤ 400000)) = true := by
  decide +kernel

theorem ladder_dec {μ ρ : ℕ} {lv : List Whir.Level} (h : Whir.ladder μ ρ = some lv) :
    decLevelsPrice μ 0 lv ≤ 400000 := by
  obtain ⟨h1, h2⟩ := ladder_some_bounds h
  have := ladder_dec_all μ h1 ρ h2
  rw [h] at this
  simpa using this

/-- **The cut opening's trace** (`decWhirCutP.c478`): at most `403600`, whatever the events. -/
theorem decWhirCutP_cost (hP : Includes P decWhirCutP.c478.costDeps) (μ ρ : ℕ) (h : List EvP)
    (hμ : μ < 2 ^ 64) (hρ : ρ < 2 ^ 64) :
    machineCost P decWhirCutP.c478.costIdx [encodeValue μ, encodeValue ρ, encodeValue h] ≤ 403600 := by
  rw [decWhirCutP.c478.costEq P hP]
  have hl := ladder_cost P (by includes) μ ρ hμ hρ
  have hb := bind_le P (by includes) _ (.closure decWhirCutP.c478.lam0.costIdx
      [encodeValue μ, encodeValue h])
    (fun c ↦ RunsApp.of_spec (decWhirCutP.c478.lam0.costSpec P (by includes) μ h c))
    (Whir.ladder μ ρ) 400007 (fun lv hlv ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [decWhirCutP.c478.lam0.costEq P (by includes)]
      obtain ⟨h1, h2, h3, -⟩ := ladder_facts hlv
      have hb := ladder_some_bounds hlv
      have := decLevelsP_cost P (by includes) μ (by omega) lv 0 h h1 (by omega) (by omega)
      have := ladder_dec hlv
      omega)
  omega

/-- **The body's trace** (`decBodyLC`) at an admissible layout and rate, whatever the events: at
most `1001400000`. -/
theorem decBodyL_cost (hP : Includes P decBodyLC.costDeps) (lay : LayoutLite) (ρ : ℕ) (h : List EvP)
    (hl : LayOk lay) (hρ : ρ ≤ 4) :
    machineCost P decBodyLC.costIdx [encodeValue lay, encodeValue ρ, encodeValue h] ≤ 1001400000 := by
  have l1 := length_skBodyHeadL lay ρ hl
  have c1 := skBodyHeadL_cost P (by includes) lay ρ hl hρ
  have c2 := decWhirCutP_cost P (by includes) lay.stackLog ρ
    (List.drop (skBodyHeadL lay ρ).length h) (by have := hl.1; omega) (by omega)
  rw [decBodyLC.costEq P hP]
  cost_calls []
  omega

/-! ### The announced sizes -/

/-- The sizes from the announced values (`sizesOfL.c437`): `26` per value, `8` per bytecode word,
`977124000`. -/
theorem sizesOfL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.sizesOfL.c437.costDeps)
    (bytecode : List K) (ann : List E) (hb : bytecode.length < 2 ^ 63) :
    machineCost P Auto.LeanVM.Extraction.AS.sizesOfL.c437.costIdx [encodeValue bytecode,
      encodeValue ann] ≤ 26 * ann.length + 8 * bytecode.length + 977124000 := by
  rw [Auto.LeanVM.Extraction.AS.sizesOfL.c437.costEq P hP, FastLib.tablesLength]
  have hall := all_cost P (by includes) (fun value : E ↦ decide (value.limb 1 = 0))
    (.closure Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam0.costIdx [])
    (fun v ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam0.costSpec P
      (by includes) v)) 4 ann (fun v _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam0.costEq P (by includes)]
        rfl)
  have htl : (List.take 6 (List.drop 1 ann)).length ≤ 6 := List.length_take_le _ _
  have hm := map_cost P (by includes) (fun value : E ↦ LeanVM.Protocol.Verifier.kToNat (value.limb 0))
    (.closure Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam1.costIdx [])
    (fun v ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam1.costSpec P
      (by includes) v)) 2 (List.take 6 (List.drop 1 ann)) (fun v _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam1.costEq P (by includes)]
        rfl)
  have hrv := reverseAux_cost P (by includes) ann []
  have hbl := buildLayoutLite_cost P (by includes) bytecode
    (LeanVM.Protocol.Verifier.kToNat ((ann.headD 0).limb 0))
    (List.map (fun value ↦ LeanVM.Protocol.Verifier.kToNat (value.limb 0))
      (List.take 6 (List.drop 1 ann))) hb (kToNat_lt _) (fun r hr' ↦ by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hr'
        exact kToNat_lt _) (by simp only [List.length_map]; omega)
  have hbd := bind_le P (by includes) _ (.closure Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam2.costIdx
      [encodeValue (LeanVM.Protocol.Verifier.kToNat ((ann.getLastD 0).limb 0))])
    (fun L ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam2.costSpec P
      (by includes) _ L))
    (buildLayoutLite bytecode (LeanVM.Protocol.Verifier.kToNat ((ann.headD 0).limb 0))
      (List.map (fun value ↦ LeanVM.Protocol.Verifier.kToNat (value.limb 0))
        (List.take 6 (List.drop 1 ann)))) 28 (fun L hL ↦ by
      have := buildLayoutLite_stackLog hL
      rw [appCost_fn, List.singleton_append,
        Auto.LeanVM.Extraction.AS.sizesOfL.c437.lam2.costEq P (by includes),
        limbs_of_lt (by omega : L.stackLog < 2 ^ 64),
        limbs_of_lt (by simp [Whir.minLogStack]), limbs_of_lt (by simp [Whir.maxLogStack])]
      simp only [List.length_singleton]
      split_ifs <;> omega)
  have hk := kToNat_lt ((ann.getLastD 0).limb 0)
  have c1 := listCases_le ann 5 3
  have c2 := listCases_le ann.reverse 5 3
  cost_calls []
  split_ifs <;> omega

/-- **The announced sizes** (`decSizesLC`) from `n` events: at most
`80·n + 8·|bytecode| + 977124100`. -/
theorem decSizesL_cost (hP : Includes P decSizesLC.costDeps) (bytecode : List K) (h : List EvP)
    (hb : bytecode.length < 2 ^ 63) (hn : h.length < 2 ^ 60) :
    machineCost P decSizesLC.costIdx [encodeValue bytecode, encodeValue h] ≤
      80 * h.length + 8 * bytecode.length + 977124100 := by
  rw [decSizesLC.costEq P hP]
  have h1 := mapMReads_cost P (by includes) (by includes) h
  have h2 := bind_le P (by includes) _ (.closure decSizesLC.lam0.costIdx [encodeValue bytecode])
    (fun a ↦ RunsApp.of_spec (decSizesLC.lam0.costSpec P (by includes) bytecode a))
    (List.mapM (fun p : EvP ↦ p.1) h) (26 * h.length + 8 * bytecode.length + 977124004)
    (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, decSizesLC.lam0.costEq P (by includes)]
      have hl := LeanVM.Extraction.AS.length_of_mapM ha
      have := sizesOfL_cost P (by includes) bytecode a hb
      rw [hl] at this
      simp only [List.length_singleton]
      omega)
  omega

end Skeleton2

end

end LeanVM.Cost.Bounds.AS
