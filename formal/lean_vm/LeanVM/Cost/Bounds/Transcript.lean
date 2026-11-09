module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.SortedMap
public import LeanVM.Cost.Extractor.Transcript
import all LeanVM.Protocol.Extraction.Fast.SortedMap
public import LeanVM.Cost.Prices

/-!
# Bounds: the committed word's reader

* `replicate_cost`: `List.replicate n a` costs at most `15·n + 5`, for word-sized `n`;
* **`leafAt_cost`**: reading a position of the committed word (`leafAt leaves h w v`, the leaf
  `v mod 2^h`, or `w` zeros) costs at most `15·w + 15`, for `h < 64` and word-sized `v`, `w`.

The committed leaves themselves are bounded in `Bounds/Top.lean` (`leavesOfC_cost`, a lookup in
the transcript's index `preimageLookup_cost`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast

public section

attribute [local instance] lexOrd

variable (P : MachineProgram)

/-- **A position of the committed word**: at most `15·w + 15`. -/
theorem leafAt_cost (hP : Includes P leafAtC.costDeps) (leaves : Array (List K)) (h w v : ℕ)
    (hh : h < 64) (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) :
    machineCost P leafAtC.costIdx [encodeValue leaves, encodeValue h, encodeValue w, encodeValue v] ≤ 15 * w + 15 := by
  rw [leafAtC.costEq P hP]
  have h2 : 2 ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hh
  have hr := replicate_cost P (by includes) (0 : K) w hw
  rw [Nat.one_shiftLeft, limbs_of_lt h2, limbs_of_lt (by omega : h < 2 ^ 64), limbs_of_lt hv]
  omega

/-! ## Generic list functions -/

/-- `List.compareLex` (`compareLex.c112`), any element type: `17` per position of the second list
and the comparison's price, `7` at the end. -/
theorem compareLex_cost (hP : Includes P Auto.List.compareLex.c112.costDeps) {α : Type} [MachineEncoding α]
    (cmp : α → α → Ordering) (cmpVal : MachineValue)
    (hc : ∀ a b, RunsApp P cmpVal [encodeValue a, encodeValue b] (encodeValue (cmp a b))) (B : ℕ)
    (hB : ∀ a b : α, appCost P cmpVal [encodeValue a, encodeValue b] ≤ B) :
    ∀ (a b : List α), machineCost P Auto.List.compareLex.c112.costIdx [cmpVal, encodeValue a, encodeValue b] ≤
      (B + 17) * b.length + 7 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.compareLex.c112.costEq P hP cmp cmpVal hc]; cases b <;> simp
  | cons x a ih =>
    intro b
    rw [Auto.List.compareLex.c112.costEq P hP cmp cmpVal hc]
    cases b with
    | nil => simp
    | cons y b =>
      have h1 := ih b
      have h2 := hB x y
      simp only [List.length_cons]
      generalize cmp x y = o
      cases o <;> dsimp only <;> nlinarith

/-- Byte strings compared (`List.beq`, `beq.c114`): `15` per byte of the second, `7` at the end. -/
theorem bytesBeq_cost (hP : Includes P Auto.List.beq.c114.costDeps) :
    ∀ x y : List UInt8, machineCost P Auto.List.beq.c114.costIdx [encodeValue x, encodeValue y] ≤ 15 * y.length + 7 := by
  intro x
  induction x with
  | nil => intro y; rw [Auto.List.beq.c114.costEq_nil P hP]; cases y <;> simp
  | cons a x ih =>
    intro y
    rw [Auto.List.beq.c114.costEq_cons P hP]
    cases y with
    | nil => simp
    | cons b y =>
      have := ih y
      simp only [List.length_cons]
      split_ifs <;> omega

/-! ## The preimage index's map: keys `(digest words, length)` -/

/-- A preimage key: four words and a word-sized length. -/
@[expose] def PreKey (k : List UInt64 × ℕ) : Prop := k.1.length = 4 ∧ k.2 < 2 ^ 64

/-- Two words compared (`searchPreC.lam0`): at most `9`. -/
theorem cmpWord_cost (hP : Includes P searchPreC.lam0.costDeps) (a b : UInt64) :
    machineCost P searchPreC.lam0.costIdx [encodeValue a, encodeValue b] ≤ 9 := by
  rw [searchPreC.lam0.costEq P hP]
  split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- The binary search of a preimage key `k` (`searchIn.c117`): at most `C·(log₂(hi − lo) + 2)`,
`C = 58 + 26·|k.1| + 9·W` the price of a probe, `W` a bound of the limbs of the positions (up
to `2·H`), whatever their size. -/
theorem searchPre_cost (hP : Includes P searchIn.c117.costDeps)
    (t : Array ((List UInt64 × ℕ) × Hits)) (k : List UInt64 × ℕ) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hts : t.size ≤ H) (ht : ∀ e ∈ t, e.1.2 < 2 ^ 64) (hk : k.2 < 2 ^ 64) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c117.costIdx [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] ≤
        (58 + 26 * k.1.length + 9 * W) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]; exact cmpWord_cost P (by includes) a b)
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchIn.c117.costIdx [encodeValue t, encodeValue k, encodeValue x.1, encodeValue x.2])
    (58 + 26 * k.1.length + 9 * W) (58 + 26 * k.1.length + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c117.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    limbs_bound hW
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c117.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      dsimp only
      limbs_bound hW
      split_ifs <;> omega
    | some v =>
      have hv1 : v.1.2 < 2 ^ 64 := ht v (Array.mem_of_getElem? hv)
      dsimp only
      limbs_bound hW
      have hc := hcmp v.1.1 k.1
      generalize compareOn (fun x ↦ x.1) v.1 k = o1
      generalize compare v.1 k = o2
      cases o2
      · right
        refine ⟨((lo + hi) / 2 + 1, hi), ⟨by omega, hhi⟩, by dsimp only; omega, ?_⟩
        dsimp only
        cases o1 <;> dsimp only <;> split_ifs <;> omega
      · left
        cases o1 <;> dsimp only <;> split_ifs <;> omega
      · right
        refine ⟨(lo, (lo + hi) / 2), ⟨hlo, by omega⟩, by dsimp only; omega, ?_⟩
        dsimp only
        cases o1 <;> dsimp only <;> split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `mergeNewer` on preimage keys (`mergeNewer.c119`): at most `157` per entry and `3`. -/
theorem mergeNewerPre_cost (hP : Includes P mergeNewer.c119.costDeps) :
    ∀ (n : ℕ) (a b : List ((List UInt64 × ℕ) × Hits)), a.length + b.length = n →
      (∀ e ∈ a, PreKey e.1) → (∀ e ∈ b, PreKey e.1) →
      machineCost P mergeNewer.c119.costIdx [encodeValue a, encodeValue b] ≤ 157 * n + 3 := by
  have hcmp := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]; exact cmpWord_cost P (by includes) a b)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  cases a with
  | nil => rw [mergeNewer.c119.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c119.costEq_cons P hP]
    cases b with
    | nil => simp at hn ⊢; omega
    | cons y b =>
      dsimp only
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have hc := hcmp x.1.1 y.1.1
      rw [hy.1] at hc
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp)
        (fun e he ↦ ha e (by simp [he])) hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl
        (fun e he ↦ ha e (by simp [he])) (fun e he ↦ hb e (by simp [he]))
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp)
        ha (fun e he ↦ hb e (by simp [he]))
      simp only [List.length_cons] at hn h1 h3
      rw [limbs_of_lt hx.2, limbs_of_lt hy.2]
      generalize compareOn (fun x ↦ x.1) x.1 y.1 = o1
      generalize compare x.1 y.1 = o2
      cases o1 <;> cases o2 <;> dsimp only <;> (try split_ifs) <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Two levels merged (`levelMergePreC`): at most `161` per entry and `18`. -/
theorem levelMergePre_cost (hP : Includes P levelMergePreC.costDeps)
    (l l' : Level (List UInt64 × ℕ) Hits) (hQ : KeysIn PreKey [l, l'])
    (W : ℕ) (hw : limbCount l.weight ≤ W) (hw' : limbCount l'.weight ≤ W)
    (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P levelMergePreC.costIdx [encodeValue l, encodeValue l'] ≤
      18 + W + 161 * (l.entries.size + l'.entries.size) := by
  rw [levelMergePreC.costEq P hP]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) ≤ W :=
    max_le hws (max_le hw hw')
  have hm := mergeNewerPre_cost P (by includes) _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the preimage index, amortized** (`carry.c122`): `161·D + 40·(levels + 1)`
plus the drop of `161` times the potential. -/
theorem carryPre_amortized (hP : Includes P carry.c122.costDeps) (D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64 × ℕ) Hits) (hm : smGood m) (hQ : KeysIn PreKey m.levels)
    (hN : smWeightSum m < 2 ^ D) (l : Level (List UInt64 × ℕ) Hits) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, PreKey e.1) :
    machineCost P carry.c122.costIdx [encodeValue l, encodeValue m.levels] + 161 * potential D (carry l m.levels) ≤
      161 * potential D m.levels + 161 * D + (32 + 2 * W) * (m.levels.length + 1) := by
  refine insert_amortized PreKey (fun l ls ↦ machineCost P carry.c122.costIdx [encodeValue l, encodeValue ls])
    (32 + 2 * W) 161
    D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c122.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c122.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergePre_cost P (by includes) l l' hQ2 W (hW _ (by omega)) (hW _ (by omega))
      (hW _ (by omega))
    rw [carry.c122.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the preimage index (`getPreC`): a binary search per level. -/
theorem getPre_cost (hP : Includes P getPreC.costDeps)
    (m : SortedMap (List UInt64 × ℕ) Hits) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (hQ : KeysIn PreKey m.levels)
    (k : List UInt64 × ℕ) (hk : PreKey k) :
    machineCost P getPreC.costIdx [encodeValue m, encodeValue k] ≤
      m.levels.length * (20 + (162 + 9 * W) * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.closure getPreC.lam0.costIdx [encodeValue k]) [encodeValue l] ≤
      9 + (162 + 9 * W) * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.length_singleton, List.singleton_append, getPreC.lam0.costEq P (by includes)]
    have := searchPre_cost P (by includes) l.entries k H W hW (hm l hl)
      (fun e he ↦ (hQ l hl e he).2) hk.2 0 l.entries.size (by omega) (hm l hl)
    rw [hk.1] at this
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : (58 + 26 * 4 + 9 * W) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (162 + 9 * W) * (Nat.log2 H + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hfs := findSome_cost P (by includes) _ (.closure getPreC.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (getPreC.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [getPreC.costEq P hP]
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `Hits.merge h (.one y)` (`hitsMergeC`): at most `15·|y| + 20`. -/
theorem hitsMerge_cost (hP : Includes P hitsMergeC.costDeps) (h : Hits) (y : List UInt8) :
    machineCost P hitsMergeC.costIdx [encodeValue h, encodeValue (Hits.one y)] ≤ 15 * y.length + 20 := by
  cases h with
  | none => rw [hitsMergeC.costEq_none P hP]; omega
  | many => rw [hitsMergeC.costEq_many P hP]; dsimp only; omega
  | one x =>
    rw [hitsMergeC.costEq_one P hP]
    have := bytesBeq_cost P (by includes) x y
    dsimp only
    split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A pair's key (`hitKeyC`): at most `8·|bytes| + 24`. -/
theorem hitKey_cost (hP : Includes P hitKeyC.costDeps) (p : List UInt8 × Protocol.Digest)
    (hp : p.1.length < 2 ^ 64) :
    machineCost P hitKeyC.costIdx [encodeValue p] ≤ 8 * p.1.length + 24 := by
  rw [hitKeyC.costEq P hP]
  have := length_cost P (by includes) p.1 hp
  simp only [Vector.size_toArray]
  omega

/-- The preimage index's invariant after some insertions, `r` left: a good map of keys
`PreKey`, `r` more insertions keeping it below `2^D`. -/
@[expose] def PreInv (D : ℕ) (m : SortedMap (List UInt64 × ℕ) Hits) (r : ℕ) : Prop :=
  smGood m ∧ KeysIn PreKey m.levels ∧ smWeightSum m + r ≤ 2 ^ D

theorem preKey_hitKey (p : List UInt8 × Protocol.Digest) (hp : p.1.length < 2 ^ 64) :
    PreKey (hitKey p) := ⟨by simp [hitKey], hp⟩

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **One step of the preimage index, amortized**: a pair of at most `L` bytes into a map below
`2^D` insertions costs at most `31·L + 162·D² + 537·D + 145` (and `W·(9·D·(D + 2) + 2·(D + 1))`)
plus the drop of `161` times the potential. -/
theorem preimageStep_amortized (hP : Includes P preimageIndexC.lam0.costDeps) (D L W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hL : L < 2 ^ 64) (m : SortedMap (List UInt64 × ℕ) Hits) (r : ℕ)
    (hm : PreInv D m (r + 1)) (p : List UInt8 × Protocol.Digest) (hp : p.1.length ≤ L) :
    PreInv D (m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) r ∧
      machineCost P preimageIndexC.lam0.costIdx [encodeValue m, encodeValue p] +
          161 * potential D (m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))).levels ≤
        161 * potential D m.levels + preimageStepPrice L D W := by
  obtain ⟨hg, hQ, hw⟩ := hm
  have hk := preKey_hitKey p (by omega)
  have hN : smWeightSum m < 2 ^ D := by omega
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg hN
  refine ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ := smGood_insert hg (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))
    exact ⟨h1, keysIn_insert hQ hk _, by omega⟩
  · rw [preimageIndexC.lam0.costEq P hP, insertPreC.costEq P (by includes)]
    have hkey := hitKey_cost P (by includes) p (by omega)
    have hget := getPre_cost P (by includes) m (2 ^ D) W hW (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2)
      hQ (hitKey p) hk
    rw [Nat.log2_two_pow] at hget
    have hmerge := hitsMerge_cost P (by includes) (m.getD (hitKey p) .none) p.1
    have hcarry := carryPre_amortized P (by includes) D W hW m hg hQ hN
      ⟨1, #[(hitKey p, (m.getD (hitKey p) .none).merge (.one p.1))], by simp [Ascending]⟩ rfl rfl
      (fun e he ↦ by simp at he; rw [he]; exact hk)
    have hins : (m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))).levels =
        carry ⟨1, #[(hitKey p, (m.getD (hitKey p) .none).merge (.one p.1))], by simp [Ascending]⟩ m.levels := rfl
    rw [hins]
    have hlv : m.levels.length * (20 + (162 + 9 * W) * (D + 2)) ≤
        D * (20 + (162 + 9 * W) * (D + 2)) := Nat.mul_le_mul_right _ hlev
    have hc2 := Nat.mul_le_mul_left (32 + 2 * W) (show m.levels.length + 1 ≤ D + 1 by omega)
    have e1 : D * (20 + (162 + 9 * W) * (D + 2)) =
        162 * (D * D) + 344 * D + W * (9 * (D * (D + 2))) := by ring
    have e2 : (32 + 2 * W) * (D + 1) = 32 * D + 32 + W * (2 * (D + 1)) := by ring
    have e3 : W * (9 * (D * (D + 2)) + 2 * (D + 1)) =
        W * (9 * (D * (D + 2))) + W * (2 * (D + 1)) := by ring
    unfold preimageStepPrice
    generalize m.get? (hitKey p) = o
    cases o <;> dsimp only <;> omega

/-- **The preimage index** (`preimageIndex pairs`, compiled as `preimageIndexC`): at most
`n·(preimageStepPrice L D W + 11) + 9` for `n ≤ 2^D` pairs of at most `L` bytes, `W` a bound of the limbs
of the positions and weights (up to `2·2^D`): per
pair a key, a lookup (`D` binary searches of `≤ D + 2` probes), and an amortized insertion
(`161·D` merged entries). -/
theorem preimageIndex_cost (hP : Includes P preimageIndexC.costDeps) (D L W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hL : L < 2 ^ 64) (pairs : List (List UInt8 × Protocol.Digest)) (hn : pairs.length ≤ 2 ^ D)
    (hp : ∀ p ∈ pairs, p.1.length ≤ L) :
    machineCost P preimageIndexC.costIdx [encodeValue pairs] ≤
      pairs.length * (preimageStepPrice L D W + 11) + 9 := by
  rw [preimageIndexC.costEq P hP]
  have := listFoldl_amortized P (by includes) _ (.closure preimageIndexC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (preimageIndexC.lam0.costSpec P (by includes) a b))
    (preimageStepPrice L D W) (fun m ↦ 161 * potential D m.levels) (PreInv D)
    pairs SortedMap.empty ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h,
      by simp [smWeightSum_empty]; omega⟩
    (fun acc r hacc p hpm ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
      exact preimageStep_amortized P (by includes) D L W hW hL acc r hacc p (hp p hpm))
  have h0 : potential D (SortedMap.empty : SortedMap (List UInt64 × ℕ) Hits).levels = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.zero_add] at this
  nlinarith

/-! ## The first answers' map: byte-string keys -/

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Byte strings compared (`compareLex` with `searchBytesC.lam0`): `26` per byte of the second. -/
theorem compareBytes_cost (hP : Includes P searchIn.c132.costDeps) (a b : List UInt8) :
    machineCost P Auto.List.compareLex.c112.costIdx [.closure searchBytesC.lam0.costIdx [], encodeValue a, encodeValue b] ≤
      26 * b.length + 7 := by
  have := compareLex_cost P (by includes) _ (.closure searchBytesC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchBytesC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero, searchBytesC.lam0.costEq P (by includes)]
      split_ifs <;> omega) a b
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- The binary search of a byte string `k` (`searchIn.c132`): at most `(40 + 26·|k| + 9·W)·(log₂(hi − lo)
+ 2)`. -/
theorem searchBytes_cost (hP : Includes P searchIn.c132.costDeps)
    (t : Array (List UInt8 × Protocol.Digest)) (k : List UInt8) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c132.costIdx [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareBytes_cost P (by includes)
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchIn.c132.costIdx [encodeValue t, encodeValue k, encodeValue x.1, encodeValue x.2])
    (40 + 26 * k.length + 9 * W) (40 + 26 * k.length + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c132.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    limbs_bound hW
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c132.costEq P hP]
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

/-- Byte-string keys of at most `L` bytes. -/
@[expose] def BytesKey (L : ℕ) (k : List UInt8) : Prop := k.length ≤ L

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `mergeNewer` on byte-string keys (`mergeNewer.c134`): at most `26·L + 33` per entry and `3`. -/
theorem mergeNewerBytes_cost (hP : Includes P mergeNewer.c134.costDeps) (L : ℕ) :
    ∀ (n : ℕ) (a b : List (List UInt8 × Protocol.Digest)), a.length + b.length = n →
      (∀ e ∈ b, BytesKey L e.1) →
      machineCost P mergeNewer.c134.costIdx [encodeValue a, encodeValue b] ≤ (26 * L + 33) * n + 3 := by
  have hcmp := compareLex_cost P (by includes) _ (.closure searchBytesC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchBytesC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero, searchBytesC.lam0.costEq P (by includes)]
      split_ifs <;> omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hb
  cases a with
  | nil => rw [mergeNewer.c134.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c134.costEq_cons P hP]
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
/-- Two levels merged (`levelMergeBytesC`): at most `26·L + 37` per entry and `18`. -/
theorem levelMergeBytes_cost (hP : Includes P levelMergeBytesC.costDeps) (L : ℕ)
    (l l' : Level (List UInt8) Protocol.Digest) (hQ : KeysIn (BytesKey L) [l, l'])
    (W : ℕ) (hw : limbCount l.weight ≤ W) (hw' : limbCount l'.weight ≤ W)
    (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P levelMergeBytesC.costIdx [encodeValue l, encodeValue l'] ≤
      18 + W + (26 * L + 37) * (l.entries.size + l'.entries.size) := by
  rw [levelMergeBytesC.costEq P hP]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) ≤ W :=
    max_le hws (max_le hw hw')
  have hm := mergeNewerBytes_cost P (by includes) L _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the first answers' map, amortized** (`carry.c137`). -/
theorem carryBytes_amortized (hP : Includes P carry.c137.costDeps) (L D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt8) Protocol.Digest) (hm : smGood m)
    (hQ : KeysIn (BytesKey L) m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level (List UInt8) Protocol.Digest) (hw : l.weight = 1) (hs : l.entries.size = 1)
    (hk : ∀ e ∈ l.entries, BytesKey L e.1) :
    machineCost P carry.c137.costIdx [encodeValue l, encodeValue m.levels] +
        (26 * L + 37) * potential D (carry l m.levels) ≤
      (26 * L + 37) * potential D m.levels + (26 * L + 37) * D + (32 + 2 * W) * (m.levels.length + 1) := by
  refine insert_amortized (BytesKey L) (fun l ls ↦ machineCost P carry.c137.costIdx [encodeValue l, encodeValue ls])
    (32 + 2 * W) (26 * L + 37) D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c137.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c137.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeBytes_cost P (by includes) L l l' hQ2 W (hW _ (by omega)) (hW _ (by omega))
      (hW _ (by omega))
    rw [carry.c137.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the first answers' map (`getBytesC`): a binary search per level. -/
theorem getBytes_cost (hP : Includes P getBytesC.costDeps)
    (m : SortedMap (List UInt8) Protocol.Digest) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (k : List UInt8) :
    machineCost P getBytesC.costIdx [encodeValue m, encodeValue k] ≤
      m.levels.length * (20 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.closure getBytesC.lam0.costIdx [encodeValue k]) [encodeValue l] ≤
      9 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.length_singleton, List.singleton_append, getBytesC.lam0.costEq P (by includes)]
    have := searchBytes_cost P (by includes) l.entries k H W hW (hm l hl)
      0 l.entries.size (by omega) (hm l hl)
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : (40 + 26 * k.length + 9 * W) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _
    (.closure getBytesC.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (getBytesC.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [getBytesC.costEq P hP]
  nlinarith

/-- The first answers' invariant after some insertions, `r` left: a good map of keys of at most
`L` bytes, `r` more insertions keeping it below `2^D`. -/
@[expose] def BytesInv (L D : ℕ) (m : SortedMap (List UInt8) Protocol.Digest) (r : ℕ) : Prop :=
  smGood m ∧ KeysIn (BytesKey L) m.levels ∧ smWeightSum m + r ≤ 2 ^ D

/-- **One step of the first answers, amortized**: a pair whose key has at most `L` bytes. -/
theorem firstAnswersStep_amortized (hP : Includes P firstAnswersC.lam0.costDeps) (L D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (m : SortedMap (List UInt8) Protocol.Digest) (r : ℕ) (hm : BytesInv L D m (r + 1))
    (p : List UInt8 × Protocol.Digest) (hp : p.1.length ≤ L) :
    BytesInv L D (insertIfNew m p.1 p.2) r ∧
      machineCost P firstAnswersC.lam0.costIdx [encodeValue m, encodeValue p] +
          (26 * L + 37) * potential D (insertIfNew m p.1 p.2).levels ≤
        (26 * L + 37) * potential D m.levels + firstAnswersStepPrice L D W := by
  obtain ⟨hg, hQ, hw⟩ := hm
  have hN : smWeightSum m < 2 ^ D := by omega
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg hN
  have hget := getBytes_cost P (by includes) m (2 ^ D) W hW
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) p.1
  rw [Nat.log2_two_pow] at hget
  have hg1 : m.levels.length * (20 + (40 + 26 * p.1.length + 9 * W) * (D + 2)) ≤
      D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) :=
    Nat.mul_le_mul hlev (by
      have := Nat.mul_le_mul_right (D + 2)
        (show 40 + 26 * p.1.length + 9 * W ≤ 40 + 26 * L + 9 * W by omega)
      omega)
  rw [firstAnswersC.lam0.costEq P hP, insertIfNewC.costEq P (by includes)]
  unfold firstAnswersStepPrice
  by_cases hc : m.contains p.1 = true
  · simp only [insertIfNew, hc, ↓reduceIte]
    refine ⟨⟨hg, hQ, by omega⟩, ?_⟩
    generalize m.get? p.1 = o
    cases o <;> dsimp only <;> nlinarith
  · simp only [insertIfNew, hc, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h1, h2⟩ := smGood_insert hg p.1 p.2
    refine ⟨⟨h1, keysIn_insert hQ hp p.2, by omega⟩, ?_⟩
    rw [insertBytesC.costEq P (by includes)]
    have hcarry := carryBytes_amortized P (by includes) L D W hW m hg hQ hN
      ⟨1, #[(p.1, p.2)], by simp [Ascending]⟩ rfl rfl (fun e he ↦ by simp at he; rw [he]; exact hp)
    have hins : (m.insert p.1 p.2).levels = carry ⟨1, #[(p.1, p.2)], by simp [Ascending]⟩ m.levels :=
      rfl
    rw [hins]
    have hc1 := Nat.mul_le_mul_left (32 + 2 * W) (show m.levels.length + 1 ≤ D + 1 by omega)
    have hc2 : (32 + 2 * W) * (D + 1) = (32 + 2 * W) * D + 32 + 2 * W := by ring
    generalize m.get? p.1 = o
    cases o <;> dsimp only <;> nlinarith

/-- **The first answers** (`firstAnswers P`, compiled as `firstAnswersC`): at most
`n·(firstAnswersStepPrice L D W + 11) + 9` for `n ≤ 2^D` pairs whose byte strings have at
most `L` bytes, `W` a bound of the limbs of the positions and weights (up to `2·2^D`). -/
theorem firstAnswers_cost (hP : Includes P firstAnswersC.costDeps) (L D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (pairs : List (List UInt8 × Protocol.Digest)) (hn : pairs.length ≤ 2 ^ D)
    (hp : ∀ p ∈ pairs, p.1.length ≤ L) :
    machineCost P firstAnswersC.costIdx [encodeValue pairs] ≤
      pairs.length * (firstAnswersStepPrice L D W + 11) + 9 := by
  rw [firstAnswersC.costEq P hP]
  have := listFoldl_amortized P (by includes) _ (.closure firstAnswersC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (firstAnswersC.lam0.costSpec P (by includes) a b))
    (firstAnswersStepPrice L D W) (fun m ↦ (26 * L + 37) * potential D m.levels) (BytesInv L D)
    pairs SortedMap.empty ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h,
      by simp [smWeightSum_empty]; omega⟩
    (fun acc r hacc p hpm ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
      exact firstAnswersStep_amortized P (by includes) L D W hW acc r hacc p (hp p hpm))
  have h0 : potential D (SortedMap.empty : SortedMap (List UInt8) Protocol.Digest).levels = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.zero_add] at this
  nlinarith

/-! ## The replay's maps: word-list keys (`fwd`, `inv`: no value; `caps`: a path) -/

/-- Word-list keys of at most `L` words. -/
@[expose] def WordsKey (L : ℕ) (k : List UInt64) : Prop := k.length ≤ L

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Word lists compared (`compareLex` with `searchPreC.lam0`): `26` per word of the second. -/
theorem compareWordsU_cost (hP : Includes P searchIn.c145.costDeps) (a b : List UInt64) :
    machineCost P Auto.List.compareLex.c112.costIdx [.closure searchPreC.lam0.costIdx [], encodeValue a, encodeValue b] ≤
      26 * b.length + 7 := by
  have := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero, searchPreC.lam0.costEq P (by includes)]
      split_ifs <;> omega) a b
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- The binary search of a word list `k` (`searchIn.c145`): at most `(40 + 26·|k| + 9·W)·(log₂(hi − lo)
+ 2)`. -/
theorem searchWordsU_cost (hP : Includes P searchIn.c145.costDeps)
    (t : Array (List UInt64 × Unit)) (k : List UInt64) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c145.costIdx [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareWordsU_cost P (by includes)
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchIn.c145.costIdx [encodeValue t, encodeValue k, encodeValue x.1, encodeValue x.2])
    (40 + 26 * k.length + 9 * W) (40 + 26 * k.length + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c145.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    limbs_bound hW
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c145.costEq P hP]
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
/-- `mergeNewer` on word-list keys (`mergeNewer.c153`): at most `26·L + 33` per entry and `3`. -/
theorem mergeNewerU_cost (hP : Includes P mergeNewer.c153.costDeps) (L : ℕ) :
    ∀ (n : ℕ) (a b : List (List UInt64 × Unit)), a.length + b.length = n →
      (∀ e ∈ b, WordsKey L e.1) →
      machineCost P mergeNewer.c153.costIdx [encodeValue a, encodeValue b] ≤ (26 * L + 33) * n + 3 := by
  have hcmp := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero, searchPreC.lam0.costEq P (by includes)]
      split_ifs <;> omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hb
  cases a with
  | nil => rw [mergeNewer.c153.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c153.costEq_cons P hP]
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
/-- Two levels merged (`Level.merge.c152`): at most `26·L + 37` per entry and `18`. -/
theorem levelMergeU_cost (hP : Includes P Level.merge.c152.costDeps) (L : ℕ)
    (l l' : Level (List UInt64) Unit) (hQ : KeysIn (WordsKey L) [l, l'])
    (W : ℕ) (hw : limbCount l.weight ≤ W) (hw' : limbCount l'.weight ≤ W)
    (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P Level.merge.c152.costIdx [encodeValue l, encodeValue l'] ≤
      18 + W + (26 * L + 37) * (l.entries.size + l'.entries.size) := by
  rw [Level.merge.c152.costEq P hP]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) ≤ W :=
    max_le hws (max_le hw hw')
  have hm := mergeNewerU_cost P (by includes) L _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the replay's map, amortized** (`carry.c151`). -/
theorem carryU_amortized (hP : Includes P carry.c151.costDeps) (L D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64) Unit) (hm : smGood m)
    (hQ : KeysIn (WordsKey L) m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level (List UInt64) Unit) (hw : l.weight = 1) (hs : l.entries.size = 1)
    (hk : ∀ e ∈ l.entries, WordsKey L e.1) :
    machineCost P carry.c151.costIdx [encodeValue l, encodeValue m.levels] +
        (26 * L + 37) * potential D (carry l m.levels) ≤
      (26 * L + 37) * potential D m.levels + (26 * L + 37) * D + (32 + 2 * W) * (m.levels.length + 1) := by
  refine insert_amortized (WordsKey L) (fun l ls ↦ machineCost P carry.c151.costIdx [encodeValue l, encodeValue ls])
    (32 + 2 * W) (26 * L + 37) D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c151.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c151.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeU_cost P (by includes) L l l' hQ2 W (hW _ (by omega)) (hW _ (by omega))
      (hW _ (by omega))
    rw [carry.c151.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the replay's map (`SortedMap.get?.c143`): a binary search per level. -/
theorem getU_cost (hP : Includes P SortedMap.get?.c143.costDeps)
    (m : SortedMap (List UInt64) Unit) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (k : List UInt64) :
    machineCost P SortedMap.get?.c143.costIdx [encodeValue m, encodeValue k] ≤
      m.levels.length * (20 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.closure SortedMap.get?.c143.lam0.costIdx [encodeValue k]) [encodeValue l] ≤
      9 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.length_singleton, List.singleton_append, SortedMap.get?.c143.lam0.costEq P (by includes)]
    have := searchWordsU_cost P (by includes) l.entries k H W hW (hm l hl)
      0 l.entries.size (by omega) (hm l hl)
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : (40 + 26 * k.length + 9 * W) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _
    (.closure SortedMap.get?.c143.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (SortedMap.get?.c143.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [SortedMap.get?.c143.costEq P hP]
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Word lists compared (`compareLex` with `searchPreC.lam0`): `26` per word of the second. -/
theorem compareWordsC_cost (hP : Includes P searchIn.c148.costDeps) (a b : List UInt64) :
    machineCost P Auto.List.compareLex.c112.costIdx [.closure searchPreC.lam0.costIdx [], encodeValue a, encodeValue b] ≤
      26 * b.length + 7 := by
  have := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero, searchPreC.lam0.costEq P (by includes)]
      split_ifs <;> omega) a b
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- The binary search of a word list `k` (`searchIn.c148`): at most `(40 + 26·|k| + 9·W)·(log₂(hi − lo)
+ 2)`. -/
theorem searchWordsC_cost (hP : Includes P searchIn.c148.costDeps)
    (t : Array (List UInt64 × (LeanVM.Semantics.KeccakState × Option (List UInt8)))) (k : List UInt64) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c148.costIdx [encodeValue t, encodeValue k, encodeValue lo, encodeValue hi] ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareWordsC_cost P (by includes)
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchIn.c148.costIdx [encodeValue t, encodeValue k, encodeValue x.1, encodeValue x.2])
    (40 + 26 * k.length + 9 * W) (40 + 26 * k.length + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c148.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    limbs_bound hW
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c148.costEq P hP]
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
/-- `mergeNewer` on word-list keys (`mergeNewer.c166`): at most `26·L + 33` per entry and `3`. -/
theorem mergeNewerC_cost (hP : Includes P mergeNewer.c166.costDeps) (L : ℕ) :
    ∀ (n : ℕ) (a b : List (List UInt64 × (LeanVM.Semantics.KeccakState × Option (List UInt8)))), a.length + b.length = n →
      (∀ e ∈ b, WordsKey L e.1) →
      machineCost P mergeNewer.c166.costIdx [encodeValue a, encodeValue b] ≤ (26 * L + 33) * n + 3 := by
  have hcmp := compareLex_cost P (by includes) _ (.closure searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero, searchPreC.lam0.costEq P (by includes)]
      split_ifs <;> omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hb
  cases a with
  | nil => rw [mergeNewer.c166.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c166.costEq_cons P hP]
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
/-- Two levels merged (`Level.merge.c165`): at most `26·L + 37` per entry and `18`. -/
theorem levelMergeC_cost (hP : Includes P Level.merge.c165.costDeps) (L : ℕ)
    (l l' : Level (List UInt64) (LeanVM.Semantics.KeccakState × Option (List UInt8))) (hQ : KeysIn (WordsKey L) [l, l'])
    (W : ℕ) (hw : limbCount l.weight ≤ W) (hw' : limbCount l'.weight ≤ W)
    (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P Level.merge.c165.costIdx [encodeValue l, encodeValue l'] ≤
      18 + W + (26 * L + 37) * (l.entries.size + l'.entries.size) := by
  rw [Level.merge.c165.costEq P hP]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight)) ≤ W :=
    max_le hws (max_le hw hw')
  have hm := mergeNewerC_cost P (by includes) L _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the replay's map, amortized** (`carry.c164`). -/
theorem carryC_amortized (hP : Includes P carry.c164.costDeps) (L D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (m : SortedMap (List UInt64) (LeanVM.Semantics.KeccakState × Option (List UInt8))) (hm : smGood m)
    (hQ : KeysIn (WordsKey L) m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level (List UInt64) (LeanVM.Semantics.KeccakState × Option (List UInt8))) (hw : l.weight = 1) (hs : l.entries.size = 1)
    (hk : ∀ e ∈ l.entries, WordsKey L e.1) :
    machineCost P carry.c164.costIdx [encodeValue l, encodeValue m.levels] +
        (26 * L + 37) * potential D (carry l m.levels) ≤
      (26 * L + 37) * potential D m.levels + (26 * L + 37) * D + (32 + 2 * W) * (m.levels.length + 1) := by
  refine insert_amortized (WordsKey L) (fun l ls ↦ machineCost P carry.c164.costIdx [encodeValue l, encodeValue ls])
    (32 + 2 * W) (26 * L + 37) D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c164.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c164.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeC_cost P (by includes) L l l' hQ2 W (hW _ (by omega)) (hW _ (by omega))
      (hW _ (by omega))
    rw [carry.c164.costEq_cons P hP]
    have := hW l.weight (by omega)
    have := hW l'.weight (by omega)
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the replay's map (`SortedMap.get?.c146`): a binary search per level. -/
theorem getC_cost (hP : Includes P SortedMap.get?.c146.costDeps)
    (m : SortedMap (List UInt64) (LeanVM.Semantics.KeccakState × Option (List UInt8))) (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (k : List UInt64) :
    machineCost P SortedMap.get?.c146.costIdx [encodeValue m, encodeValue k] ≤
      m.levels.length * (20 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.closure SortedMap.get?.c146.lam0.costIdx [encodeValue k]) [encodeValue l] ≤
      9 + (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.length_singleton, List.singleton_append, SortedMap.get?.c146.lam0.costEq P (by includes)]
    have := searchWordsC_cost P (by includes) l.entries k H W hW (hm l hl)
      0 l.entries.size (by omega) (hm l hl)
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : (40 + 26 * k.length + 9 * W) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (40 + 26 * k.length + 9 * W) * (Nat.log2 H + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _
    (.closure SortedMap.get?.c146.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (SortedMap.get?.c146.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [SortedMap.get?.c146.costEq P hP]
  nlinarith


end

end LeanVM.Cost.Bounds
