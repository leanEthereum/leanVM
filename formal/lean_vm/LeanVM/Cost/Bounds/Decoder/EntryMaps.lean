module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.SortedMap
public import LeanVM.Cost.Decoder.EntryTable
import all LeanVM.Protocol.Extraction.Fast.SortedMap
public import LeanVM.Cost.Prices

/-!
# Bound: the entry table's sorted maps and searches, compiled

At the stable names compiled in `Cost/Decoder/EntryTable.lean`: the pc table's sorted map (`ℕ`
keys, `searchInPcC` … `getPcC`) and the binary search on call keys (`searchInKeyC`: the callee's
index and the codes of the call's words), the frame lookup in the sorted entry array
(`Bounds/Decoder/EntryArray.lean`). As the transcript's maps (`Bounds/Transcript.lean`): a binary
search per level, a merge per entry, an insertion amortized by the potential
(`Bounds/SortedMap.lean`).

* a call key's comparison: the index, then the two lists of codes lexicographically
  (`compareCodes_cost`, `tripleCmp_cost`: `64` per code of the second list), at most
  `keyCmpPrice k = 64·(|args| + |rets|) + 41` against the key `k` searched;
* `searchInKey_cost`: a binary search of `k`, `(keyCmpPrice k + 37 + 9W)` per halving;
* the pc table's map (`searchInPc_cost`, `getPc_cost`, `carryPc_amortized`): a lookup at most
  `D·(20 + (39 + 9·wl D)·(D + 2)) + 9`, an insertion amortized `37·D + (2·wl D + 32)·(levels + 1)`.

Keys are word-sized (`KeyOK L`, `NatKey`): the comparisons' limbs are `1`. Positions and weights
up to `2·2^D`, for any `D`, have at most `wl D = (D + 1)/64 + 1` limbs each (`limbs_le_wl_two`):
the prices gain `9·wl D` per binary-search step and `2·wl D` per carry step (`wl D = 1` for
`D ≤ 62`, the prices then as on words).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Located

public section

attribute [local instance] lexOrd

variable (P : MachineProgram)

/-! ## Keys -/

/-- A code triple of words. -/
@[expose] def TripleOK (x : ℕ × ℕ × ℕ) : Prop := x.1 < 2 ^ 64 ∧ x.2.1 < 2 ^ 64 ∧ x.2.2 < 2 ^ 64

/-- **A call key of at most `L` codes per list**, every number word-sized. -/
@[expose] def KeyOK (L : ℕ) (k : CallKey) : Prop :=
  k.1 < 2 ^ 64 ∧ k.2.1.length ≤ L ∧ k.2.2.length ≤ L ∧ (∀ x ∈ k.2.1, TripleOK x) ∧
    ∀ x ∈ k.2.2, TripleOK x

/-- A word-sized key of the pc table. -/
@[expose] def NatKey (k : ℕ) : Prop := k < 2 ^ 64

/-- The limbs of the positions and weights of a map below `2^D` insertions. -/
@[expose] def wl (D : ℕ) : ℕ := limbsBelowTwoPow (D + 1)

theorem wl_pos (D : ℕ) : 1 ≤ wl D := by unfold wl limbsBelowTwoPow; omega

theorem limbs_le_wl' {D x : ℕ} (h : x ≤ 2 * 2 ^ D) : limbCount x ≤ wl D := limbs_le_wl_two x h

/-- The price of comparing a key with the key `k` searched: `64` per code of `k`, `41`. -/
@[expose] def keyCmpPrice (k : CallKey) : ℕ := 64 * (k.2.1.length + k.2.2.length) + 41

/-- Two code triples compared (`searchInKeyC.lam0`): at most `47`. -/
theorem tripleCmp_cost (hP : Includes P searchInKeyC.lam0.costDeps) (a b : ℕ × ℕ × ℕ)
    (ha : TripleOK a) (hb : TripleOK b) :
    machineCost P searchInKeyC.lam0.costIdx [encodeValue a, encodeValue b] ≤ 47 := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  rw [searchInKeyC.lam0.costEq P hP, limbs_of_lt a1, limbs_of_lt b1, limbs_of_lt a2,
    limbs_of_lt b2, limbs_of_lt a3, limbs_of_lt b3]
  simp only [max_self]
  generalize compareOn (fun x ↦ x.1) a b = o1
  generalize compareOn (fun x ↦ x.1) a.2 b.2 = o2
  cases o1 <;> cases o2 <;> dsimp only <;> split_ifs <;> omega

/-- Two lists of code triples compared (`compareLex` with `searchInKeyC.lam0`): `64` per triple of
the second, `7`. -/
theorem compareCodes_cost (hP : Includes P Auto.List.compareLex.c112.costDeps)
    (hP' : Includes P searchInKeyC.lam0.costDeps) :
    ∀ (a b : List (ℕ × ℕ × ℕ)), (∀ x ∈ a, TripleOK x) → (∀ x ∈ b, TripleOK x) →
      machineCost P Auto.List.compareLex.c112.costIdx
          [.closure searchInKeyC.lam0.costIdx [], encodeValue a, encodeValue b] ≤
        64 * b.length + 7 := by
  have hc : ∀ x y : ℕ × ℕ × ℕ, RunsApp P (.closure searchInKeyC.lam0.costIdx [])
      [encodeValue x, encodeValue y] (encodeValue (compare x y)) :=
    fun x y ↦ RunsApp.of_spec (searchInKeyC.lam0.costSpec P hP' x y)
  intro a
  induction a with
  | nil =>
    intro b _ _
    rw [Auto.List.compareLex.c112.costEq P hP compare _ hc]
    cases b <;> simp
  | cons x a ih =>
    intro b ha hb
    rw [Auto.List.compareLex.c112.costEq P hP compare _ hc]
    cases b with
    | nil => simp
    | cons y b =>
      have h1 := ih b (fun z hz ↦ ha z (by simp [hz])) (fun z hz ↦ hb z (by simp [hz]))
      have h2 : appCost P (.closure searchInKeyC.lam0.costIdx []) [encodeValue x, encodeValue y] ≤
          47 := by
        rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
        exact tripleCmp_cost P hP' x y (ha x (by simp)) (hb y (by simp))
      simp only [List.length_cons]
      generalize compare x y = o
      cases o <;> dsimp only <;> omega

/-! ## The binary search on call keys -/

/-- **The binary search of a key `k`** (`searchInKeyC`), the entries' keys of at most `L` codes,
positions up to `2H` of at most `W` limbs: at most `(keyCmpPrice k + 37 + 9W)·(log₂(hi − lo) + 2)`. -/
theorem searchInKey_cost (hP : Includes P searchInKeyC.costDeps) (L : ℕ)
    (t : Array (CallKey × K)) (ht : ∀ e ∈ t, KeyOK L e.1) (k : CallKey) {L' : ℕ} (hk : KeyOK L' k)
    (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W) (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchInKeyC.costIdx [encodeValue t, encodeValue k, encodeValue lo,
        encodeValue hi] ≤ (keyCmpPrice k + 37 + 9 * W) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareCodes_cost P (by includes) (by includes)
  obtain ⟨hk1, -, -, hka, hkr⟩ := hk
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchInKeyC.costIdx [encodeValue t, encodeValue k, encodeValue x.1,
      encodeValue x.2])
    (keyCmpPrice k + 37 + 9 * W) (keyCmpPrice k + 37 + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchInKeyC.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    have := hW lo (by omega)
    have := hW hi (by omega)
    unfold keyCmpPrice
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchInKeyC.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    have h1 := hW lo (by omega)
    have h2 := hW hi (by omega)
    have h3 := hW (lo + hi) (by omega)
    have h4 := hW ((lo + hi) / 2) (by omega)
    have h5 := hW t.size (by omega)
    have h6 := hW ((lo + hi) / 2 + 1) (by omega)
    have hm3 : max (limbCount ((lo + hi) / 2 + 1)) (limbCount ((lo + hi) / 2)) ≤ W := max_le h6 h4
    generalize max (limbCount ((lo + hi) / 2 + 1)) (limbCount ((lo + hi) / 2)) = m5 at hm3 ⊢
    -- the positions' limbs as numbers at most `W`: no `max` left for `omega` to split
    have hm1 : max (limbCount lo) (limbCount hi) ≤ W := max_le h1 h2
    have hm2 : max (limbCount ((lo + hi) / 2)) (limbCount t.size) ≤ W := max_le h4 h5
    generalize max (limbCount lo) (limbCount hi) = m1 at hm1 ⊢
    generalize max (limbCount ((lo + hi) / 2)) (limbCount t.size) = m2 at hm2 ⊢
    generalize limbCount (lo + hi) = m3 at h3 ⊢
    generalize limbCount ((lo + hi) / 2) = m4 at h4 ⊢
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      dsimp only
      unfold keyCmpPrice
      split_ifs <;> omega
    | some v =>
      have hvt : v ∈ t := Array.mem_of_getElem? hv
      obtain ⟨hv1, -, -, hva, hvr⟩ := ht v hvt
      have hc1 := hcmp v.1.2.1 k.2.1 hva hka
      have hc2 := hcmp v.1.2.2 k.2.2 hvr hkr
      dsimp only
      rw [limbs_of_lt hv1, limbs_of_lt hk1]
      simp only [max_self]
      unfold keyCmpPrice
      generalize machineCost P Auto.List.compareLex.c112.costIdx
        [.closure searchInKeyC.lam0.costIdx [], encodeValue v.1.2.1, encodeValue k.2.1] = c1 at hc1 ⊢
      generalize machineCost P Auto.List.compareLex.c112.costIdx
        [.closure searchInKeyC.lam0.costIdx [], encodeValue v.1.2.2, encodeValue k.2.2] = c2 at hc2 ⊢
      -- the comparison's price, bounded once over its `9` outcomes
      have hcmpP : ∀ o1 o3 : Ordering,
          Ordering.rec (motive := fun _ ↦ ℕ) 1
            (c1 + Ordering.rec (motive := fun _ ↦ ℕ) 1 (c2 + 6) 1 o3 + 13) 1 o1 ≤ c1 + c2 + 19 := by
        intro o1 o3; cases o1 <;> cases o3 <;> dsimp only <;> omega
      have hif : ∀ (p q : Prop) [Decidable p] [Decidable q],
          (1 + if p then 1 else (1 + if q then 1 else 1) + 5) ≤ 8 := by
        intro p q _ _; split_ifs <;> omega
      have := hcmpP (compareOn (fun x ↦ x.1) v.1 k) (compareOn (fun x ↦ x.1) v.1.2 k.2)
      have := hif (v.1.1 < k.1) (v.1.1 = k.1)
      generalize compareOn (fun x ↦ x.1) v.1 k = o1 at *
      generalize compareOn (fun x ↦ x.1) v.1.2 k.2 = o3 at *
      clear hcmpP hif hv hvt hva hvr hka hkr ht hcmp hv1 hk1
      generalize compare v.1 k = o2
      cases o2
      · right
        refine ⟨((lo + hi) / 2 + 1, hi), ⟨by omega, hhi⟩, by dsimp only; omega, ?_⟩
        dsimp only
        split <;> omega
      · left
        dsimp only
        split <;> omega
      · right
        refine ⟨(lo, (lo + hi) / 2), ⟨hlo, by omega⟩, by dsimp only; omega, ?_⟩
        dsimp only
        split <;> omega

/-! ## The pc table's map: `ℕ` keys -/

/-- **The binary search of a pc** (`searchInPcC`), positions up to `2H` of at most `W` limbs: at
most `(39 + 9W)·(log₂(hi − lo) + 2)`. -/
theorem searchInPc_cost (hP : Includes P searchInPcC.costDeps)
    (t : Array (ℕ × List ℕ)) (ht : ∀ e ∈ t, NatKey e.1) (k : ℕ) (hk : NatKey k)
    (H W : ℕ) (hW : ∀ x, x ≤ 2 * H → limbCount x ≤ W) (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchInPcC.costIdx [encodeValue t, encodeValue k, encodeValue lo,
        encodeValue hi] ≤ (39 + 9 * W) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchInPcC.costIdx [encodeValue t, encodeValue k, encodeValue x.1,
      encodeValue x.2]) (39 + 9 * W) (39 + 9 * W) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchInPcC.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    have := hW lo (by omega)
    have := hW hi (by omega)
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchInPcC.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    have := hW lo (by omega)
    have := hW hi (by omega)
    have := hW (lo + hi) (by omega)
    have := hW ((lo + hi) / 2) (by omega)
    have := hW t.size (by omega)
    have := hW ((lo + hi) / 2 + 1) (by omega)
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      dsimp only
      split_ifs <;> omega
    | some v =>
      have hvt : v ∈ t := Array.mem_of_getElem? hv
      have hv1 : v.1 < 2 ^ 64 := ht v hvt
      have hk1 : k < 2 ^ 64 := hk
      dsimp only
      rw [limbs_of_lt hv1, limbs_of_lt hk1]
      simp only [max_self]
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

/-- `mergeNewer` on pcs (`mergeNewerPcC`): at most `33` per entry and `3`. -/
theorem mergeNewerPc_cost (hP : Includes P mergeNewerPcC.costDeps) :
    ∀ (n : ℕ) (a b : List (ℕ × List ℕ)), a.length + b.length = n →
      (∀ e ∈ a, NatKey e.1) → (∀ e ∈ b, NatKey e.1) →
      machineCost P mergeNewerPcC.costIdx [encodeValue a, encodeValue b] ≤ 33 * n + 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  cases a with
  | nil => rw [mergeNewerPcC.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewerPcC.costEq_cons P hP]
    cases b with
    | nil => simp only [List.length_cons, List.length_nil] at hn; dsimp only; omega
    | cons y b =>
      dsimp only
      have hx1 : x.1 < 2 ^ 64 := ha x (by simp)
      have hy1 : y.1 < 2 ^ 64 := hb y (by simp)
      have ha' : ∀ e ∈ a, NatKey e.1 := fun e he ↦ ha e (by simp [he])
      have hb' : ∀ e ∈ b, NatKey e.1 := fun e he ↦ hb e (by simp [he])
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp) ha' hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl ha' hb'
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp) ha hb'
      simp only [List.length_cons] at hn h1 h3
      rw [limbs_of_lt hx1, limbs_of_lt hy1]
      simp only [max_self]
      generalize compare x.1 y.1 = o2
      subst hn
      cases o2 <;> dsimp only <;> split_ifs <;> omega

/-- Two levels merged (`levelMergePcC`): at most `37` per entry and `18 + W`, the weights and their
sum of at most `W` limbs. -/
theorem levelMergePc_cost (hP : Includes P levelMergePcC.costDeps)
    (l l' : Level ℕ (List ℕ)) (hQ : KeysIn NatKey [l, l']) (W : ℕ) (hw : limbCount l.weight ≤ W)
    (hw' : limbCount l'.weight ≤ W) (hws : limbCount (l.weight + l'.weight) ≤ W) :
    machineCost P levelMergePcC.costIdx [encodeValue l, encodeValue l'] ≤
      18 + W + 37 * (l.entries.size + l'.entries.size) := by
  rw [levelMergePcC.costEq P hP]
  have hmx : max (limbCount (l.weight + l'.weight)) (max (limbCount l.weight) (limbCount l'.weight))
      ≤ W := max_le hws (max_le hw hw')
  have hm := mergeNewerPc_cost P (by includes) _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen ⊢
  omega

/-- **An insertion into the pc table's map, amortized** (`carryPcC`), below `2^D` insertions. -/
theorem carryPc_amortized (hP : Includes P carryPcC.costDeps) (D : ℕ)
    (m : SortedMap ℕ (List ℕ)) (hm : smGood m) (hQ : KeysIn NatKey m.levels)
    (hN : smWeightSum m < 2 ^ D) (l : Level ℕ (List ℕ)) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, NatKey e.1) :
    machineCost P carryPcC.costIdx [encodeValue l, encodeValue m.levels] +
        37 * potential D (carry l m.levels) ≤
      37 * potential D m.levels + 37 * D + (2 * wl D + 32) * (m.levels.length + 1) := by
  refine insert_amortized NatKey
    (fun l ls ↦ machineCost P carryPcC.costIdx [encodeValue l, encodeValue ls])
    (2 * wl D + 32) 37 D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carryPcC.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carryPcC.costEq_cons P hP]
    have := limbs_le_wl' (D := D) (x := l.weight) (by omega)
    have := limbs_le_wl' (D := D) (x := l'.weight) (by omega)
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have h3 := limbs_le_wl' (D := D) (x := l.weight) (by omega)
    have h4 := limbs_le_wl' (D := D) (x := l'.weight) (by omega)
    have h5 := limbs_le_wl' (D := D) (x := l.weight + l'.weight) (by omega)
    have := levelMergePc_cost P (by includes) l l' hQ2 (wl D) h3 h4 h5
    rw [carryPcC.costEq_cons P hP]
    simp only [heq, ↓reduceIte]
    omega

/-- **A lookup of a pc** (`getPcC`) in a map of at most `D` levels of at most `2^D` entries: at
most `D·(20 + (39 + 9·wl D)·(D + 2)) + 9`. -/
theorem getPc_cost (hP : Includes P getPcC.costDeps) (D : ℕ)
    (m : SortedMap ℕ (List ℕ)) (hQ : KeysIn NatKey m.levels) (hlev : m.levels.length ≤ D)
    (hsz : ∀ l ∈ m.levels, l.entries.size ≤ 2 ^ D) (k : ℕ) (hk : NatKey k) :
    machineCost P getPcC.costIdx [encodeValue m, encodeValue k] ≤
      D * (20 + (39 + 9 * wl D) * (D + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.closure getPcC.lam0.costIdx [encodeValue k])
      [encodeValue l] ≤ 9 + (39 + 9 * wl D) * (D + 2) := by
    intro l hl
    rw [appCost_fn, List.singleton_append, getPcC.lam0.costEq P (by includes),
      List.length_singleton]
    have := searchInPc_cost P (by includes) l.entries (fun e he ↦ hQ l hl e he) k hk (2 ^ D)
      (wl D) (fun x hx ↦ limbs_le_wl' hx) (hsz l hl) 0 l.entries.size (Nat.zero_le _) (hsz l hl)
    have h2 : Nat.log2 (l.entries.size - 0) ≤ D := by
      have := log2_mono (show l.entries.size - 0 ≤ 2 ^ D by have := hsz l hl; omega)
      rwa [Nat.log2_two_pow] at this
    have : (39 + 9 * wl D) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (39 + 9 * wl D) * (D + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _ (.closure getPcC.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (getPcC.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [getPcC.costEq P hP]
  generalize (39 + 9 * wl D) * (D + 2) = X at hfs ⊢
  have h1 := Nat.mul_le_mul_left (9 + X + 11) hlev
  have h2 : (9 + X + 11) * D = D * (20 + X) := by ring
  omega

end

end LeanVM.Cost.Bounds
