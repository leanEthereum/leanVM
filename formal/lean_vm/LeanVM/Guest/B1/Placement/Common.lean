/-
  LeanVM.Guest.B1.Placement.Common

  Range checks on a memory image, sums of g-powers, and the offsets `stackOffsets` lays out.
-/

module

public import LeanVM.Guest.B1.Placement.Kappas
public import LeanVM.Guest.Value.Pigeonhole

/-!
# Range checks, exponents and stack offsets

Ported from the BLAKE2s-era `B1/Tables/Common` (branch `mumbai`), prefixed `tb`:

* `tb_rc_sound'`, `tb_rc_complete`, `tbRcAux`: `assert log(x) < K` on a memory image of `2^μ`
  words, `μ ≤ 32` (`rangeCheck_iff`), with a choice of the gadget's auxiliary words for an honest
  valuation.
* `tb_gen_pow_eq_mul`: products of small g-powers are g-powers of the sums.
* `tb_stackFold_*`, `tb_stackOffsets_fst`: the fold of `stackOffsets` (V:830) over an order without
  repeats sets each index to the sum of the sizes before it (`tbPrefixSize`).
* `tb_group_stack_cert`: runs of columns of one size each (groups), named by ranks in
  `stackOffsets`'s order group by group, with each column at `g^` the sizes before it, are laid
  out as `stackOffsets` lays the columns out (`certify_placement`; `verify_tables`' bus blocks).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Range checks -/

/-- **A range check is sound** on any memory image of at most `2^32` words, whatever `K ≤ 2^33`:
both reads are below `2^32`, so their exponents' sum `K - 1` is below the order of `g`. -/
theorem tb_rc_sound' {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : K ≤ 2 ^ 33) {x y t1 t2 k : E} (hk : k = ofK (Parameters.addressOfIndex (K - 1)))
    (h1 : LoadHolds Lm.read x 0 t1) (h2 : k = x * y) (h3 : LoadHolds Lm.read y 0 t2) :
    ∃ e < K, x = gen ^ e := by
  have hμ64 : μ < 64 := by omega
  have h32 : 2 ^ μ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hμ
  obtain ⟨hx, h1⟩ := h1
  obtain ⟨hy, h3⟩ := h3
  rw [Parameters.addressOfIndex, pow_zero, mul_one] at h1 h3
  obtain ⟨i, hi, -⟩ := (read_some_iff hμ64 Lm _ _).mp h1
  obtain ⟨j, hj, -⟩ := (read_some_iff hμ64 Lm _ _).mp h3
  have ex : x = ofK (Parameters.addressOfIndex i) := by rw [eq_ofK_limb hx, hi]
  have ey : y = ofK (Parameters.addressOfIndex j) := by rw [eq_ofK_limb hy, hj]
  rw [hk, ex, ey, ← ofK_mul, Parameters.addressOfIndex, Parameters.addressOfIndex, ← pow_add] at h2
  have hij := gpow_injOn (by have := i.isLt; have := j.isLt; simp only [Set.mem_Iio]; omega)
    (by simp only [Set.mem_Iio]; omega) (ofK_injective h2).symm
  exact ⟨i, by omega, by rw [ex, gen_pow_eq_ofK]⟩

/-- The auxiliary words of a passing range check, chosen. -/
noncomputable def tbRcAux {μ : ℕ} (Lm : MemoryImage μ) (x : E) (K : ℕ) : E × E × E :=
  open Classical in
  if h : ∃ y t1 t2 : E, LoadHolds Lm.read x 0 t1 ∧ ofK (Parameters.addressOfIndex (K - 1)) = x * y ∧
      LoadHolds Lm.read y 0 t2 then
    (Classical.choose h, Classical.choose (Classical.choose_spec h),
      Classical.choose (Classical.choose_spec (Classical.choose_spec h)))
  else (0, 0, 0)

/-- A run of mapped words, entry by entry. -/
theorem tbReadsAt_map_iff {rd : Reader} {p : E} {l : List ℕ} {f : ℕ → E} :
    TbReadsAt rd p (l.map f) ↔ ∀ c < l.length, LoadHolds rd p c (f (l.getD c 0)) := by
  unfold TbReadsAt
  constructor
  · intro h c hc
    have := h c (by simpa using hc)
    rwa [List.getElem_map, ← List.getD_eq_getElem l 0 hc] at this
  · intro h c hc
    have hc' : c < l.length := by simpa using hc
    rw [List.getElem_map, ← List.getD_eq_getElem l 0 hc']
    exact h c hc'

/-! ## Exponents -/

theorem tb_gen_pow_inj' {a b : ℕ} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : gen ^ a = gen ^ b) :
    a = b := gen_pow_inj (by omega) (by omega) h

/-- `g^a = g^d · g^b` with all three small: `a = d + b`. -/
theorem tb_gen_pow_eq_mul {a b d : ℕ} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) (hd : d < 2 ^ 62)
    (h : gen ^ a = gen ^ d * gen ^ b) : a = d + b := by
  rw [← pow_add] at h; exact tb_gen_pow_inj' (by omega) (by omega) h

/-! ## Stack offsets -/

/-- The fold of `stackOffsets` (V:877-884). -/
def tbStackStep (size : ℕ → ℕ) (acc : List ℕ × ℕ) (i : ℕ) : List ℕ × ℕ :=
  (acc.1.set i acc.2, acc.2 + 2 ^ size i)

/-- The sum of the sizes of the first `r` entries of `ord`. -/
def tbPrefixSize (size : ℕ → ℕ) (ord : List ℕ) (r : ℕ) : ℕ :=
  ((ord.take r).map fun i => 2 ^ size i).sum

theorem tb_stackFold_take (size : ℕ → ℕ) (n : ℕ) (ord : List ℕ) (hnd : ord.Nodup)
    (hlt : ∀ i ∈ ord, i < n) :
    ∀ m ≤ ord.length,
      ((ord.take m).foldl (tbStackStep size) (List.replicate n 0, 0)).2 = tbPrefixSize size ord m ∧
      ((ord.take m).foldl (tbStackStep size) (List.replicate n 0, 0)).1.length = n ∧
      ∀ r < m, ((ord.take m).foldl (tbStackStep size) (List.replicate n 0, 0)).1.getD
        (ord.getD r 0) 0 = tbPrefixSize size ord r := by
  intro m hm
  induction m with
  | zero => simp [tbPrefixSize]
  | succ m ih =>
    obtain ⟨h2, hl, h1⟩ := ih (by omega)
    have hmo : m < ord.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hmo, Option.toList_some, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, tbStackStep]
    refine ⟨?_, ?_, fun r hr => ?_⟩
    · rw [h2, tbPrefixSize, tbPrefixSize, List.take_add_one, List.getElem?_eq_getElem hmo,
        Option.toList_some, List.map_append, List.sum_append]
      simp
    · rw [List.length_set, hl]
    · have hin : ord[m] < n := hlt _ (List.getElem_mem hmo)
      rcases Nat.lt_or_ge r m with hr' | hr'
      · have hne : ord[m] ≠ ord.getD r 0 := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          intro he
          exact absurd ((List.Nodup.getElem_inj_iff hnd).mp he) (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
        exact h1 r hr'
      · obtain rfl : r = m := by omega
        rw [List.getD_eq_getElem _ _ hmo, List.getD_eq_getElem?_getD, List.getElem?_set_self
          (by rw [hl]; exact hin), Option.getD_some, h2]

/-- **`stackOffsets`'s offsets** (V:877-884): along its order, entry `order[r]` is the sum of the
sizes before it, and the total is their sum. -/
theorem tb_stackOffsets_fst (sizes : List ℕ) (r : ℕ)
    (hr : r < sizes.length) :
    (stackOffsets sizes).1.getD
        (((List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))).getD r 0) 0 =
      tbPrefixSize (sizes.getD · 0) ((List.range sizes.length).mergeSort (stackLe (sizes.getD · 0)))
        r := by
  set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))
  have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have hlen : ord.length = sizes.length := by rw [hperm.length_eq, List.length_range]
  have h := tb_stackFold_take (sizes.getD · 0) sizes.length ord (hperm.nodup_iff.mpr List.nodup_range)
    (fun i hi => List.mem_range.mp (hperm.subset hi)) ord.length le_rfl
  rw [List.take_length] at h
  have hst : stackOffsets sizes = ((ord.foldl (tbStackStep (sizes.getD · 0))
      (List.replicate sizes.length 0, 0)).1, log2Ceil (ord.foldl (tbStackStep (sizes.getD · 0))
      (List.replicate sizes.length 0, 0)).2) := rfl
  rw [hst]
  exact h.2.2 r (by omega)

theorem tb_stackOffsets_length (sizes : List ℕ) : (stackOffsets sizes).1.length = sizes.length := by
  set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))
  have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have h := tb_stackFold_take (sizes.getD · 0) sizes.length ord (hperm.nodup_iff.mpr List.nodup_range)
    (fun i hi => List.mem_range.mp (hperm.subset hi)) ord.length le_rfl
  rw [List.take_length] at h
  exact h.2.1

theorem tb_prefixSize_full (size : ℕ → ℕ) (ord : List ℕ) :
    tbPrefixSize size ord ord.length = (ord.map fun i => 2 ^ size i).sum := by
  rw [tbPrefixSize, List.take_length]

theorem tb_prefixSize_succ (size : ℕ → ℕ) (ord : List ℕ) (r : ℕ) (hr : r < ord.length) :
    tbPrefixSize size ord (r + 1) = tbPrefixSize size ord r + 2 ^ size (ord.getD r 0) := by
  rw [tbPrefixSize, tbPrefixSize, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.map_append, List.sum_append, List.getD_eq_getElem _ _ hr]
  simp

/-! ## Stacking orders -/

/-- `g^33`, as the data writes it: the range check below `SIZE_BITS = 34`. -/
theorem word_g33 : word 8589934592 0 = ofK (Parameters.addressOfIndex 33) := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 8589934592) = ofK (Parameters.addressOfIndex 33)
  rw [show K.ofBits 8589934592 = Parameters.addressOfIndex 33 by decide +kernel]

/-- `stackOffsets`'s order of the sizes `κs` (V:878-879): larger first, ties by index. -/
def tbStackOrder (κs : List ℕ) : List ℕ :=
  (List.range κs.length).mergeSort (stackLe (κs.getD · 0))

/-- Choices below `n` as a function. -/
theorem tb_exists_fun_of_forall {α : Type} [Inhabited α] {n : ℕ} {P : ℕ → α → Prop}
    (h : ∀ r < n, ∃ a, P r a) : ∃ f : ℕ → α, ∀ r < n, P r (f r) := by
  classical
  exact ⟨fun r => if hr : r < n then Classical.choose (h r hr) else default,
    fun r hr => by simp only [hr, ↓reduceDIte]; exact Classical.choose_spec (h r hr)⟩

theorem tb_prefixSize_map (s : ℕ → ℕ) (l : List ℕ) (r : ℕ) :
    tbPrefixSize s l r = tbPrefixSize id (l.map s) r := by
  simp [tbPrefixSize, List.map_take, List.map_map, Function.comp_def]

theorem tb_prefixSize_congr {f f' : ℕ → ℕ} {ord : List ℕ} (h : ∀ x ∈ ord, f x = f' x) (j : ℕ) :
    tbPrefixSize f ord j = tbPrefixSize f' ord j := by
  unfold tbPrefixSize
  congr 1
  exact List.map_congr_left fun x hx ↦ by rw [h x (List.mem_of_mem_take hx)]

/-! ## Stacking groups of columns -/

/-- Group `g`'s columns, `start g .. start (g + 1)`. -/
def tbBlk (start : ℕ → ℕ) (g : ℕ) : List ℕ := List.range' (start g) (start (g + 1) - start g)

/-- The sizes of ranks `r' < r`'s groups: group `π r'` holds the columns `tbBlk start (π r')`,
each of log-size `κc (start (π r'))`. -/
def tbGroupPrefix (start κc π : ℕ → ℕ) (r : ℕ) : ℕ :=
  ((List.range r).map fun r' ↦ (start (π r' + 1) - start (π r')) * 2 ^ κc (start (π r'))).sum

theorem tb_groupPrefix_succ (start κc π : ℕ → ℕ) (r : ℕ) :
    tbGroupPrefix start κc π (r + 1) =
      tbGroupPrefix start κc π r + (start (π r + 1) - start (π r)) * 2 ^ κc (start (π r)) := by
  simp [tbGroupPrefix, List.range_succ]

theorem tb_start_mono {m : ℕ} {start : ℕ → ℕ} (hmono : ∀ g < m, start g ≤ start (g + 1)) :
    ∀ a b, a ≤ b → b ≤ m → start a ≤ start b := by
  intro a b hab hbm
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hmono b (by omega))
    · obtain rfl : a = b + 1 := by omega
      exact le_rfl

theorem tb_flatten_blocks {m : ℕ} {start : ℕ → ℕ} (h0 : start 0 = 0)
    (hmono : ∀ g < m, start g ≤ start (g + 1)) :
    ∀ k ≤ m, ((List.range k).map (tbBlk start)).flatten = List.range (start k)
  | 0, _ => by simp [h0]
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.flatten_append,
      tb_flatten_blocks h0 hmono k (by omega), List.map_singleton, List.flatten_singleton,
      List.range_eq_range', List.range_eq_range', tbBlk]
    have e := @List.range'_append 0 (start k) (start (k + 1) - start k) 1
    simp only [Nat.zero_add, Nat.one_mul] at e
    rw [e]
    have := hmono k (by omega)
    congr 1
    omega

theorem tb_flatten_split (Bs : List (List ℕ)) (r : ℕ) (hr : r < Bs.length) :
    Bs.flatten = (Bs.take r).flatten ++ (Bs[r] ++ (Bs.drop (r + 1)).flatten) := by
  conv_lhs => rw [← List.take_append_drop r Bs]
  rw [List.flatten_append, List.drop_eq_getElem_cons hr, List.flatten_cons]

/-- **Groups stacked in a certified order.** Group `g < m` holds the columns
`start g .. start (g + 1)`, all of log-size `κc (start g)`; ranks `r < m` name groups `π r`, with
non-increasing sizes and, on a tie, increasing groups; the columns of rank `r`'s group lie at
`off` as `g^` the sizes before them, the earlier ranks' groups' and the group's earlier columns'.
Then every column lies at `off` as `g^` its `stackOffsets` offset, and the ranks' groups' sizes sum
to the columns'. -/
theorem tb_group_stack_cert {rd : Reader} {off : E} {m : ℕ} (start κc π : ℕ → ℕ)
    (h0 : start 0 = 0) (hmono : ∀ g < m, start g ≤ start (g + 1))
    (hconst : ∀ g < m, ∀ c, start g ≤ c → c < start (g + 1) → κc c = κc (start g))
    (hπ : ∀ r < m, π r < m)
    (hadj : ∀ r, r + 1 < m → κc (start (π (r + 1))) ≤ κc (start (π r)) ∧
      (κc (start (π (r + 1))) = κc (start (π r)) → π r < π (r + 1)))
    (hoff : ∀ r < m, ∀ i, start (π r) + i < start (π r + 1) →
      LoadHolds rd off (start (π r) + i)
        (gen ^ (tbGroupPrefix start κc π r + i * 2 ^ κc (start (π r))))) :
    (∀ c < start m, LoadHolds rd off c
        (gen ^ (stackOffsets ((List.range (start m)).map κc)).1.getD c 0)) ∧
      tbGroupPrefix start κc π m = ((List.range (start m)).map fun c ↦ 2 ^ κc c).sum := by
  have hle := tb_start_mono hmono
  have hgrp : ∀ g < m, ∀ x ∈ tbBlk start g,
      start g ≤ x ∧ x < start (g + 1) ∧ κc x = κc (start g) := fun g hg x hx ↦ by
    rw [tbBlk, List.mem_range'_1] at hx
    have := hmono g hg
    exact ⟨hx.1, by omega, hconst g hg x hx.1 (by omega)⟩
  have hblkLen : ∀ g, (tbBlk start g).length = start (g + 1) - start g := fun g ↦ by
    simp [tbBlk]
  -- the sum of the sizes over part of a group
  have hsumBlk : ∀ g < m, ∀ l : List ℕ, (∀ x ∈ l, x ∈ tbBlk start g) →
      (l.map fun c ↦ 2 ^ κc c).sum = l.length * 2 ^ κc (start g) := fun g hg l hl ↦ by
    rw [List.map_congr_left (g := fun _ ↦ 2 ^ κc (start g)) fun x hx ↦ by
      rw [(hgrp g hg x (hl x hx)).2.2], List.map_const', List.sum_replicate, smul_eq_mul]
  -- the groups' order
  have hRt : ∀ a b c : ℕ, (κc (start b) < κc (start a) ∨ (κc (start b) = κc (start a) ∧ a < b)) →
      (κc (start c) < κc (start b) ∨ (κc (start c) = κc (start b) ∧ b < c)) →
      (κc (start c) < κc (start a) ∨ (κc (start c) = κc (start a) ∧ a < c)) := by
    intro a b c h1 h2; omega
  have hPpw : ((List.range m).map π).Pairwise
      fun a b ↦ κc (start b) < κc (start a) ∨ (κc (start b) = κc (start a) ∧ a < b) := by
    refine pairwise_of_adjacent hRt _ fun i h ↦ ?_
    simp only [List.length_map, List.length_range] at h
    simp only [List.getElem_map, List.getElem_range]
    have := hadj i h
    omega
  have hPnd : ((List.range m).map π).Nodup := hPpw.imp fun h e ↦ by subst e; omega
  have hPsub : (List.range m).map π ⊆ List.range m := fun x hx ↦ by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (hπ r (List.mem_range.mp hr))
  have hPperm : ((List.range m).map π).Perm (List.range m) :=
    (hPnd.subperm hPsub).perm_of_length_le (by simp)
  -- the columns' order
  set Bs := (List.range m).map fun r ↦ tbBlk start (π r) with hBs
  have hBsπ : Bs = ((List.range m).map π).map (tbBlk start) := by rw [hBs, List.map_map]; rfl
  have hBslen : Bs.length = m := by simp [Bs]
  have hBsget : ∀ r (h : r < Bs.length), Bs[r] = tbBlk start (π r) := fun r h ↦ by simp [Bs]
  have hBstake : ∀ r ≤ m, Bs.take r = (List.range r).map fun r' ↦ tbBlk start (π r') :=
    fun r hr ↦ by rw [hBs, ← List.map_take, List.take_range, Nat.min_eq_left hr]
  have hordperm : Bs.flatten.Perm (List.range (start m)) := by
    rw [← tb_flatten_blocks h0 hmono m le_rfl]
    refine List.Perm.flatten ?_
    rw [hBsπ]
    exact hPperm.map _
  have hordlt : ∀ x ∈ Bs.flatten, x < start m := fun x hx ↦
    List.mem_range.mp (hordperm.mem_iff.mp hx)
  have hordpw : Bs.flatten.Pairwise fun c c' ↦ κc c' < κc c ∨ (κc c' = κc c ∧ c < c') := by
    rw [List.pairwise_flatten]
    refine ⟨fun l hl ↦ ?_, ?_⟩
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hg := hπ r (List.mem_range.mp hr)
      refine (List.pairwise_lt_range' (s := start (π r)) (n := start (π r + 1) - start (π r))
        ).imp_of_mem fun ha hb hab ↦ ?_
      rw [(hgrp _ hg _ ha).2.2, (hgrp _ hg _ hb).2.2]
      exact Or.inr ⟨rfl, hab⟩
    · rw [hBsπ, List.pairwise_map]
      refine hPpw.imp_of_mem fun {a b} ha hb hab x hx y hy ↦ ?_
      have ha' := List.mem_range.mp (hPsub ha)
      have hb' := List.mem_range.mp (hPsub hb)
      obtain ⟨-, hx2, hx3⟩ := hgrp a ha' x hx
      obtain ⟨hy1, -, hy3⟩ := hgrp b hb' y hy
      rw [hx3, hy3]
      rcases hab with h | ⟨h1, h2⟩
      · exact Or.inl h
      · have := hle (a + 1) b (by omega) (by omega)
        exact Or.inr ⟨h1, by omega⟩
  -- the order is `stackOffsets`'s
  set κs := (List.range (start m)).map κc with hκs
  have hκslen : κs.length = start m := by simp [κs]
  have hκsget : ∀ c < start m, κs.getD c 0 = κc c := fun c hc ↦ by
    simp [κs, List.getElem?_range hc]
  have hord : Bs.flatten = (List.range κs.length).mergeSort (stackLe (κs.getD · 0)) := by
    rw [hκslen]
    refine eq_mergeSort_of_adjacent (κs.getD · 0) hordperm fun i h ↦ ?_
    have hp := List.pairwise_iff_getElem.mp hordpw i (i + 1) (by omega) h (by omega)
    rw [hκsget _ (hordlt _ (List.getElem_mem _)), hκsget _ (hordlt _ (List.getElem_mem _))]
    omega
  -- the sizes before a rank's group
  have hsumTake : ∀ r ≤ m, (((Bs.take r).flatten).map fun c ↦ 2 ^ κc c).sum =
      tbGroupPrefix start κc π r := fun r hr ↦ by
    rw [hBstake r hr, List.map_flatten, List.sum_flatten, List.map_map, List.map_map, tbGroupPrefix]
    congr 1
    refine List.map_congr_left fun r' hr' ↦ ?_
    have hg := hπ r' (by have := List.mem_range.mp hr'; omega)
    simp only [Function.comp_apply]
    rw [hsumBlk _ hg _ fun x hx ↦ hx, hblkLen]
  refine ⟨fun c hc ↦ ?_, ?_⟩
  · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp (hordperm.mem_iff.mpr (List.mem_range.mpr hc))
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    have hr' := List.mem_range.mp hr
    have hg := hπ r hr'
    obtain ⟨hc1, hc2, -⟩ := hgrp _ hg c hcl
    obtain ⟨i, rfl⟩ : ∃ i, c = start (π r) + i := ⟨c - start (π r), by omega⟩
    have hi : i < (tbBlk start (π r)).length := by rw [hblkLen]; omega
    have hsplit := tb_flatten_split Bs r (by omega)
    rw [hBsget] at hsplit
    set A := (Bs.take r).flatten
    have hAlen : A.length = ((List.range r).map fun r' ↦ start (π r' + 1) - start (π r')).sum := by
      simp only [A]
      rw [hBstake r (by omega), List.length_flatten, List.map_map]
      congr 1
      exact List.map_congr_left fun r' _ ↦ by simp only [Function.comp_apply, hblkLen]
    set j := A.length + i
    have hj : j < (Bs.flatten).length := by
      rw [hsplit, List.length_append, List.length_append]; omega
    have hgetj : Bs.flatten.getD j 0 = start (π r) + i := by
      rw [List.getD_eq_getElem?_getD, hsplit, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, List.getElem?_append_left hi]
      simp [tbBlk, List.getElem?_range' (show i < start (π r + 1) - start (π r) by omega)]
    have hpre : tbPrefixSize κc Bs.flatten j =
        tbGroupPrefix start κc π r + i * 2 ^ κc (start (π r)) := by
      rw [tbPrefixSize, hsplit, List.take_append, List.take_of_length_le (by omega),
        Nat.add_sub_cancel_left, List.take_append_of_le_length (by omega), List.map_append,
        List.sum_append, hsumTake r (by omega),
        hsumBlk _ hg _ fun x hx ↦ List.mem_of_mem_take hx, List.length_take, Nat.min_eq_left (by omega)]
    have hfst := tb_stackOffsets_fst κs j (by
      have := hordperm.length_eq
      rw [List.length_range] at this
      omega)
    rw [← hord, hgetj, ← tb_prefixSize_congr (f := κc) (fun x hx ↦ (hκsget x (hordlt x hx)).symm),
      hpre] at hfst
    rw [hfst]
    exact hoff r hr' i hc2
  · rw [← hsumTake m le_rfl, List.take_of_length_le (by omega)]
    exact (hordperm.map _).sum_eq

end
end LeanVM.Guest.B1.Tables
