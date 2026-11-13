module

public import LeanVM.Cost.Bounds.Decoder.EntryTable
public import LeanVM.Cost.Decoder.EntryTableEq

/-!
# Bound: the entry table as one sorted array, compiled

The prices of `Cost/Decoder/EntryTable.lean`'s sorted entry array (`entryArrayT`) and its frame
map (`frameAtA`): no presence lookup per filing, one stable sort, one binary search per frame.
Parameters as `Bounds/Decoder/EntryTable.lean`'s: `R` a memory read, `Pr` the precondition's test,
`Gpc` a pc lookup, `M` the functions entered at one pc; the pairs below `2^E`, any `E`, numbers
up to `2·2^E` of at most `W = wl E` limbs.

* `keyCmp_cost`: two keys compared, at most `keyCmpPrice b + 6` (`b` the second);
* `mergeSortList_cost_wl`: the extractor's merge sort on any number `n` of elements, the lengths
  of at most `W` limbs: `(B + 62 + 5W)·n·⌈log₂ n⌉ + (7W + 77)·n + 3` (`mergeSortList_cost` at
  `W = 1`, any length);
* `statePairs_cost`, `entryPairs_cost`: the pairs filed, per state at most
  `pairsStatePrice Gpc M Pr R = Gpc + (Pr + 66R + 41252)·M + 36`;
* `dedupFirst_cost`: `4295` per pair, `11`;
* **`entryArrayT_cost`**: the states' table, `M·|states| < 2^E`: at most
  `entryArrayStatePrice Gpc M Pr R E·|states| + 26`, per state the pairs and, per pair, the
  sort's `(4343 + 5·wl E)·E + 7·wl E + 77`, the dedup's `4295` and `1`;
* **`frameAtA_cost`**: one binary search of the call's key (`w = |args| + |rets|` words), at most
  `(64w + 78 + 9·wl E)·(E + 2) + 27w + R + 1584`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.Fast

public section

attribute [local instance] lexOrd

variable (P : MachineProgram)

/-! ## Two keys compared -/

/-- **Two keys compared** (`keyCmpC`), word-sized: at most `keyCmpPrice b + 6`. -/
theorem keyCmp_cost (hP : Includes P keyCmpC.costDeps) (a b : CallKey) {L L' : ℕ}
    (ha : KeyOK L a) (hb : KeyOK L' b) :
    machineCost P keyCmpC.costIdx [encodeValue a, encodeValue b] ≤ keyCmpPrice b + 6 := by
  obtain ⟨ha1, -, -, haa, har⟩ := ha
  obtain ⟨hb1, -, -, hba, hbr⟩ := hb
  have hcmp := compareCodes_cost P (by includes) (by includes)
  have hc1 := hcmp a.2.1 b.2.1 haa hba
  have hc2 := hcmp a.2.2 b.2.2 har hbr
  rw [keyCmpC.costEq P hP, limbs_of_lt ha1, limbs_of_lt hb1]
  simp only [max_self]
  unfold keyCmpPrice
  generalize machineCost P Auto.List.compareLex.c112.costIdx
    [.closure searchInKeyC.lam0.costIdx [], encodeValue a.2.1, encodeValue b.2.1] = c1 at hc1 ⊢
  generalize machineCost P Auto.List.compareLex.c112.costIdx
    [.closure searchInKeyC.lam0.costIdx [], encodeValue a.2.2, encodeValue b.2.2] = c2 at hc2 ⊢
  generalize compareOn (fun x ↦ x.1) a b = o1
  generalize compareOn (fun x ↦ x.1) a.2 b.2 = o3
  cases o1 <;> cases o3 <;> dsimp only <;> split_ifs <;> omega

/-- A state's key as filed (`entryKeyT_ok`): word-sized, at most `56` argument codes (`main_loop2`'s)
and `10` return codes. -/
@[expose, reducible] def EntryKeyOK (k : CallKey) : Prop := KeyOK 56 k ∧ k.2.2.length ≤ 10

/-- A filed key's comparison price: at most `64·66 + 41`. -/
theorem keyCmpPrice_le {k : CallKey} (h : EntryKeyOK k) : keyCmpPrice k ≤ 64 * 66 + 41 := by
  unfold keyCmpPrice; have := h.1.2.1; have := h.2; omega

/-- The pairs' order (`keyLeC`'s closure in `entryArrayTC`), filed keys: at most `64·66 + 57`. -/
theorem keyLeLam_cost (hP : Includes P entryArrayTC.lam0.costDeps) (a b : CallKey × K)
    (ha : EntryKeyOK a.1) (hb : EntryKeyOK b.1) :
    appCost P (.closure entryArrayTC.lam0.costIdx []) [encodeValue a, encodeValue b] ≤
      64 * 66 + 57 := by
  rw [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero, entryArrayTC.lam0.costEq P hP,
    keyLeC.costEq P (by includes)]
  have := keyCmp_cost P (by includes) a.1 b.1 ha.1 hb.1
  have hk := keyCmpPrice_le hb
  generalize keyCmp a.1 b.1 = o
  cases o <;> dsimp only <;> omega

/-! ## The merge sort on any number of elements -/

section MergeSortWl

variable {α : Type} [MachineEncoding α] (W N : ℕ) (hW : ∀ x, x ≤ N → limbCount x ≤ W)

include hW in
/-- `List.length` (`length.c128`), the counts of at most `W` limbs: `7 + W` per element, `3`. -/
theorem length_cost_wl (hP : Includes P Auto.List.length.c128.costDeps) :
    ∀ l : List α, l.length ≤ N →
      machineCost P Auto.List.length.c128.costIdx [encodeValue l] ≤ (7 + W) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.length.c128.costEq_nil P hP]; omega
  | cons x l ih =>
    intro hl
    simp only [List.length_cons] at hl
    rw [Auto.List.length.c128.costEq_cons P hP]
    have := ih (by omega)
    have hm : max (limbCount (l.length + 1)) (limbCount l.length) ≤ W :=
      max_le (hW (l.length + 1) (by omega)) (hW l.length (by omega))
    simp only [List.length_cons]
    nlinarith

include hW in
/-- `List.take n` (`take.c173`), `n ≤ N`: `17 + 2W` per element, `9 + 2W`. -/
theorem take_cost_wl (hP : Includes P Auto.List.take.c173.costDeps) :
    ∀ (n : ℕ) (l : List α), n ≤ N →
      machineCost P Auto.List.take.c173.costIdx [encodeValue n, encodeValue l] ≤
        (17 + 2 * W) * l.length + 9 + 2 * W
  | 0, l, _ => by rw [Auto.List.take.c173.costEq_zero P hP]; omega
  | n + 1, [], h => by
    rw [Auto.List.take.c173.costEq_succ P hP]
    have := hW (n + 1) h
    simp only [List.length_nil]
    omega
  | n + 1, x :: l, h => by
    rw [Auto.List.take.c173.costEq_succ P hP]
    have := take_cost_wl hP n l (by omega)
    have := hW (n + 1) h
    simp only [List.length_cons]
    nlinarith

include hW in
/-- `List.drop n` (`drop.c149`), `n ≤ N`: `13 + 2W` per element, `9 + 2W`. -/
theorem drop_cost_wl (hP : Includes P Auto.List.drop.c149.costDeps) :
    ∀ (n : ℕ) (l : List α), n ≤ N →
      machineCost P Auto.List.drop.c149.costIdx [encodeValue n, encodeValue l] ≤
        (13 + 2 * W) * l.length + 9 + 2 * W
  | 0, l, _ => by rw [Auto.List.drop.c149.costEq_zero P hP]; omega
  | n + 1, [], h => by
    rw [Auto.List.drop.c149.costEq_succ P hP]
    have := hW (n + 1) h
    simp only [List.length_nil]
    omega
  | n + 1, x :: l, h => by
    rw [Auto.List.drop.c149.costEq_succ P hP]
    have := drop_cost_wl hP n l (by omega)
    have := hW (n + 1) h
    simp only [List.length_cons]
    nlinarith

/-- The merge sort's recurrence closed, `n log n`, the work `c` per element and `K` per call. -/
theorem nlogn_halves_wl (c K d a b L T1 T2 Wk : ℕ) (hab : b ≤ a)
    (hL : Nat.clog 2 a + 1 = L)
    (h1 : T1 + K ≤ c * (a * Nat.clog 2 a) + d * a) (h2 : T2 + K ≤ c * (b * Nat.clog 2 b) + d * b)
    (hW : Wk ≤ c * (a + b) + K) :
    T1 + T2 + Wk + K ≤ c * ((a + b) * L) + d * (a + b) := by
  have hLb : Nat.clog 2 b ≤ Nat.clog 2 a := Nat.clog_mono_right 2 hab
  have e1 : c * (b * Nat.clog 2 b) ≤ c * (b * Nat.clog 2 a) :=
    Nat.mul_le_mul_left c (Nat.mul_le_mul_left b hLb)
  have e2 : c * ((a + b) * L) = c * (a * Nat.clog 2 a) + c * (b * Nat.clog 2 a) + c * (a + b) := by
    rw [← hL]; ring
  have e3 : d * (a + b) = d * a + d * b := by ring
  omega

include hW in
/-- **Merge sort** (`mergeSortList.c238`), `n log n`, the lengths of at most `W` limbs. -/
theorem mergeSortList_cost_wl_nlogn
    (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeSortList.c238.costDeps)
    (le : α → α → Bool) (leVal : MachineValue)
    (hle : ∀ a b, RunsApp P leVal [encodeValue a, encodeValue b] (encodeValue (le a b)))
    (B : ℕ) (Q : α → Prop) (hB : ∀ a b, Q a → Q b → appCost P leVal [encodeValue a, encodeValue b] ≤ B) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.length + 1 ≤ N → (∀ a ∈ l, Q a) → l ≠ [] →
      machineCost P Auto.LeanVM.Cost.InitLib.mergeSortList.c238.costIdx [encodeValue l, leVal] +
          (7 * W + 66) ≤
        (B + 62 + 5 * W) * (l.length * Nat.clog 2 l.length) + (7 * W + 77) * l.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hN hS hne
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · exact absurd rfl hne
  · rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c238.costEq_cons P hP x [] le leVal hle]
    simp
    omega
  · rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c238.costEq_cons P hP x (y :: t) le leVal hle]
    dsimp only
    simp only [List.length_cons] at hn hN ⊢
    set h1 := (t.length + 2 + 1) / 2 with hh1
    have l1 := hW t.length (by omega)
    have l2 := hW (t.length + 2) (by omega)
    have l3 := hW (t.length + 2 + 1) (by omega)
    have hlen := length_cost_wl P W N hW (by includes) t (by omega)
    have htake := take_cost_wl P W N hW (by includes) h1 (x :: y :: t) (by omega)
    have hdrop := drop_cost_wl P W N hW (by includes) h1 (x :: y :: t) (by omega)
    have hlt : (List.take h1 (x :: y :: t)).length = h1 := by simp; omega
    have hld : (List.drop h1 (x :: y :: t)).length = t.length + 2 - h1 := by simp
    have hmemT : ∀ a ∈ List.take h1 (x :: y :: t), Q a :=
      fun a ha ↦ hS a (List.mem_of_mem_take ha)
    have hmemD : ∀ a ∈ List.drop h1 (x :: y :: t), Q a :=
      fun a ha ↦ hS a (List.mem_of_mem_drop ha)
    have ih1 := ih h1 (by omega) (List.take h1 (x :: y :: t)) (by omega) (by omega) hmemT
      (by rw [← List.length_pos_iff_ne_nil, hlt]; omega)
    have ih2 := ih (t.length + 2 - h1) (by omega) (List.drop h1 (x :: y :: t)) (by omega)
      (by omega) hmemD (by rw [← List.length_pos_iff_ne_nil, hld]; omega)
    have hmerge := mergeList_cost P (by includes) le leVal hle B Q hB (h1 + (t.length + 2 - h1))
      (InitLib.mergeSortList (List.take h1 (x :: y :: t)) le)
      (InitLib.mergeSortList (List.drop h1 (x :: y :: t)) le)
      (by simp only [length_mergeSortList]; omega)
      (fun a ha ↦ hmemT a (mem_mergeSortList ha))
      (fun a ha ↦ hmemD a (mem_mergeSortList ha))
    simp only [length_mergeSortList, hlt, hld, List.length_cons] at ih1 ih2 hmerge htake hdrop
    have hsum : h1 + (t.length + 2 - h1) = t.length + 2 := by omega
    have hL := clog_half (n := t.length + 2) (by omega)
    have hwork : (7 + W) * t.length ≤ (7 + W) * (t.length + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have hm1 : max (limbCount (t.length + 2)) (limbCount t.length) ≤ W := max_le l2 l1
    have hm2 : max (limbCount (t.length + 2 + 1)) (limbCount (t.length + 2)) ≤ W := max_le l3 l2
    have := nlogn_halves_wl (B + 62 + 5 * W) (7 * W + 66) (7 * W + 77) h1 (t.length + 2 - h1)
      (Nat.clog 2 (t.length + 2)) _ _
      (machineCost P Auto.LeanVM.Cost.InitLib.mergeList.c239.costIdx
        [encodeValue (InitLib.mergeSortList (List.take h1 (x :: y :: t)) le),
          encodeValue (InitLib.mergeSortList (List.drop h1 (x :: y :: t)) le), leVal] +
        machineCost P Auto.List.length.c128.costIdx [encodeValue t] +
        max (limbCount (t.length + 2)) (limbCount t.length) +
        max (limbCount (t.length + 2 + 1)) (limbCount (t.length + 2)) + limbCount (t.length + 2 + 1) +
        machineCost P Auto.List.take.c173.costIdx [encodeValue h1, encodeValue (x :: y :: t)] +
        machineCost P Auto.List.drop.c149.costIdx [encodeValue h1, encodeValue (x :: y :: t)] + 42)
      (by omega) (by rw [← hL, hh1]) ih1 ih2 (by rw [hsum]; nlinarith)
    rw [hsum] at this
    rw [show t.length + 1 + 1 = t.length + 2 by omega]
    omega

include hW in
/-- **Merge sort**, any number `n` of elements, the lengths of at most `W` limbs (`n + 1 ≤ N`):
at most `(B + 62 + 5W)·n·⌈log₂ n⌉ + (7W + 77)·n + 3`. -/
theorem mergeSortList_cost_wl
    (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeSortList.c238.costDeps)
    (le : α → α → Bool) (leVal : MachineValue)
    (hle : ∀ a b, RunsApp P leVal [encodeValue a, encodeValue b] (encodeValue (le a b)))
    (B : ℕ) (Q : α → Prop) (hB : ∀ a b, Q a → Q b → appCost P leVal [encodeValue a, encodeValue b] ≤ B)
    (l : List α) (hN : l.length + 1 ≤ N) (hS : ∀ a ∈ l, Q a) :
    machineCost P Auto.LeanVM.Cost.InitLib.mergeSortList.c238.costIdx [encodeValue l, leVal] ≤
      (B + 62 + 5 * W) * (l.length * Nat.clog 2 l.length) + (7 * W + 77) * l.length + 3 := by
  cases l with
  | nil => rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c238.costEq_nil P hP le leVal hle]; omega
  | cons x l =>
    have := mergeSortList_cost_wl_nlogn P W N hW hP le leVal hle B Q hB _ (x :: l) le_rfl hN hS
      (by simp)
    omega

end MergeSortWl

/-! ## Dedup -/

theorem length_dedupFirst_le : ∀ l : List (CallKey × K), (dedupFirst l).length ≤ l.length
  | [] => by unfold dedupFirst; rfl
  | [_] => by unfold dedupFirst; rfl
  | a :: b :: l => by
    rw [dedupFirst]
    have h1 := length_dedupFirst_le (a :: l)
    have h2 := length_dedupFirst_le (b :: l)
    cases keyCmp a.1 b.1 <;> simp only [List.length_cons] at h1 h2 ⊢ <;> omega
termination_by l => l.length

/-- **Of each run, the first** (`dedupFirstC`), filed keys: `4295` per pair, `11`. -/
theorem dedupFirst_cost (hP : Includes P dedupFirstC.costDeps) :
    ∀ l : List (CallKey × K), (∀ e ∈ l, EntryKeyOK e.1) →
      machineCost P dedupFirstC.costIdx [encodeValue l] ≤ 4295 * l.length + 11
  | [], _ => by rw [dedupFirstC.costEq P hP]; simp
  | [_], _ => by rw [dedupFirstC.costEq P hP]; simp
  | a :: b :: l, hl => by
    rw [dedupFirstC.costEq P hP]
    dsimp only
    have hk := keyCmp_cost P (by includes) a.1 b.1 (hl a (by simp)).1 (hl b (by simp)).1
    have hkb := keyCmpPrice_le (hl b (by simp))
    have h1 := dedupFirst_cost hP (a :: l) (fun e he ↦ hl e (by
      rcases List.mem_cons.1 he with rfl | he
      · simp
      · simp [he]))
    have h2 := dedupFirst_cost hP (b :: l) (fun e he ↦ hl e (by simp [he]))
    simp only [List.length_cons] at h1 h2 ⊢
    generalize keyCmp a.1 b.1 = o
    cases o <;> dsimp only <;> omega
termination_by l => l.length

/-! ## The pairs filed -/

section Pairs

variable (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
  (pre : ℕ → K → Bool) (preVal : MachineValue)
  (hpre : ∀ (a : ℕ) (b : K), RunsApp P preVal [encodeValue a, encodeValue b] (encodeValue (pre a b)))
  (Pr : ℕ) (hPr : ∀ (j : ℕ) (fp : K), j < 2 ^ 64 → appCost P preVal [encodeValue j, encodeValue fp] ≤ Pr)

/-- The price of the pairs one state files: the pc lookup, per function entered there its
precondition's test and its key. -/
@[expose] def pairsStatePrice (Gpc M Pr R : ℕ) : ℕ := Gpc + (Pr + 66 * R + 41252) * M + 36

/-- The price per state of the sorted entry array: its pairs, and per pair the sort and the dedup. -/
@[expose] def entryArrayStatePrice (Gpc M Pr R E : ℕ) : ℕ :=
  pairsStatePrice Gpc M Pr R + M * ((4343 + 5 * wl E) * E + 7 * wl E + 4373)

include hrd hR hpre hPr in
/-- The pair state `s` files for function `j` (`pairOfC`): its precondition's test and its key. -/
theorem pairOf_cost (hP : Includes P pairOfC.costDeps) (s : Registers K) (j : ℕ) (hj : j < 2 ^ 64) :
    machineCost P pairOfC.costIdx [preVal, rdVal, encodeValue s, encodeValue j] ≤
      Pr + 66 * R + 41217 := by
  rw [pairOfC.costEq P hP pre preVal hpre rd rdVal hrd]
  have h1 := hPr j s.fp hj
  have h2 := entryKeyT_cost P rd rdVal hrd R hR (by includes) s j
  split_ifs <;> omega

/-- The pairs a state files: filed keys, at most one per function entered. -/
theorem statePairs_ok (pcT : SortedMap ℕ (List ℕ)) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64)
    (s : Registers K) : ∀ p ∈ statePairs pcT pre rd s, EntryKeyOK p.1 := by
  intro p hp
  unfold statePairs at hp
  obtain ⟨j, hj, hpj⟩ := List.mem_filterMap.1 hp
  unfold pairOf at hpj
  split_ifs at hpj
  cases hpj
  exact entryKeyT_ok rd s (hpc _ j hj)

theorem length_statePairs (pcT : SortedMap ℕ (List ℕ)) (s : Registers K) :
    (statePairs pcT pre rd s).length ≤ (pcT.getD (laneCode s.pc) []).length :=
  List.length_filterMap_le _ _

include hrd hR hpre hPr in
/-- **The pairs a state files** (`statePairsC`), at most `M` functions per pc, a pc lookup at most
`Gpc`: at most `Gpc + (Pr + 66R + 41241)·M + 18`. -/
theorem statePairs_cost (hP : Includes P statePairsC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc)
    (s : Registers K) :
    machineCost P statePairsC.costIdx [encodeValue pcT, preVal, rdVal, encodeValue s] ≤
      Gpc + (Pr + 66 * R + 41241) * M + 18 := by
  rw [statePairsC.costEq P hP pcT pre preVal hpre rd rdVal hrd]
  have hg := hG (laneCode s.pc) (UInt64.toNat_lt _)
  have hf := filterMap_cost P (by includes) _
    (.closure statePairsC.lam0.costIdx [preVal, rdVal, encodeValue s])
    (fun j ↦ RunsApp.of_spec (statePairsC.lam0.costSpec P (by includes) pre preVal hpre rd rdVal
      hrd s j))
    (Pr + 66 * R + 41225) (pcT.getD (laneCode s.pc) []) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        statePairsC.lam0.costEq P (by includes) pre preVal hpre rd rdVal hrd]
      simp only [List.length_cons, List.length_nil]
      have := pairOf_cost P rd rdVal hrd R hR pre preVal hpre Pr hPr (by includes) s j
        (hpc _ j hj)
      omega)
  have hm := Nat.mul_le_mul_left (Pr + 66 * R + 41225 + 16) (hM (laneCode s.pc))
  generalize pcT.get? (laneCode s.pc) = o
  cases o <;> dsimp only <;> nlinarith

/-- The pairs the states file: filed keys, at most `M` per state. -/
theorem entryPairs_ok (pcT : SortedMap ℕ (List ℕ)) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) :
    ∀ (states : List (Registers K)), ∀ p ∈ entryPairs pcT pre rd states, EntryKeyOK p.1
  | [] => by simp [entryPairs]
  | s :: ss => by
    intro p hp
    rw [entryPairs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact statePairs_ok rd pre pcT hpc s p hp
    · exact entryPairs_ok pcT hpc ss p hp

theorem length_entryPairs (pcT : SortedMap ℕ (List ℕ)) (M : ℕ)
    (hM : ∀ k, (pcT.getD k []).length ≤ M) :
    ∀ (states : List (Registers K)), (entryPairs pcT pre rd states).length ≤ M * states.length
  | [] => by simp [entryPairs]
  | s :: ss => by
    rw [entryPairs, List.length_append, List.length_cons, Nat.mul_succ]
    have := length_statePairs rd pre pcT s
    have := hM (laneCode s.pc)
    have := length_entryPairs pcT M hM ss
    omega

include hrd hR hpre hPr in
/-- **The pairs the states file** (`entryPairsC`): at most `pairsStatePrice Gpc M Pr R` per
state, `3`. -/
theorem entryPairs_cost (hP : Includes P entryPairsC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc) :
    ∀ states : List (Registers K),
      machineCost P entryPairsC.costIdx [encodeValue pcT, preVal, rdVal, encodeValue states] ≤
        pairsStatePrice Gpc M Pr R * states.length + 3
  | [] => by rw [entryPairsC.costEq_nil P hP pcT pre preVal hpre rd rdVal hrd]; omega
  | s :: ss => by
    rw [entryPairsC.costEq_cons P hP pcT pre preVal hpre rd rdVal hrd]
    have h1 := statePairs_cost P rd rdVal hrd R hR pre preVal hpre Pr hPr (by includes) pcT M Gpc
      hpc hM hG s
    have h2 := entryPairs_cost hP pcT M Gpc hpc hM hG ss
    have h3 := append_cost P (by includes) (statePairs pcT pre rd s) (entryPairs pcT pre rd ss)
    have h4 := length_statePairs rd pre pcT s
    have h5 := hM (laneCode s.pc)
    unfold pairsStatePrice at h2 ⊢
    have e : (Pr + 66 * R + 41252) * M = (Pr + 66 * R + 41241) * M + 11 * M := by ring
    simp only [List.length_cons, Nat.mul_succ]
    omega

/-- The sorted array: keys of at most `56` codes (filed keys), at most `M` per state. -/
theorem entryArrayT_ok (pcT : SortedMap ℕ (List ℕ)) (M : ℕ)
    (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (states : List (Registers K)) :
    (∀ e ∈ entryArrayT pcT pre states rd, KeyOK 56 e.1) ∧
      (entryArrayT pcT pre states rd).size ≤ M * states.length := by
  unfold entryArrayT
  refine ⟨fun e he ↦ ?_, ?_⟩
  · rw [List.mem_toArray] at he
    exact entryPairs_ok rd pre pcT hpc states e
      (List.mem_mergeSort.1 (mem_dedupFirst _ e he)) |>.1
  · rw [List.size_toArray]
    have := length_dedupFirst_le ((entryPairs pcT pre rd states).mergeSort keyLe)
    rw [List.length_mergeSort] at this
    have := length_entryPairs rd pre pcT M hM states
    omega

include hrd hR hpre hPr in
/-- **The entry table as one sorted array** (`entryArrayTC`), `M·|states| < 2^E`: the pairs filed,
their stable sort and the dedup, at most `entryArrayStatePrice Gpc M Pr R E · |states| + 26`. -/
theorem entryArrayT_cost (hP : Includes P entryArrayTC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc E : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64)
    (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc)
    (states : List (Registers K)) (hn : M * states.length < 2 ^ E) :
    machineCost P entryArrayTC.costIdx [encodeValue pcT, preVal, encodeValue states, rdVal] ≤
      entryArrayStatePrice Gpc M Pr R E * states.length + 26 := by
  rw [entryArrayTC.costEq P hP pcT pre preVal hpre states rd rdVal hrd]
  have hok := entryPairs_ok rd pre pcT hpc states
  have hlen := length_entryPairs rd pre pcT M hM states
  have h1 := entryPairs_cost P rd rdVal hrd R hR pre preVal hpre Pr hPr (by includes) pcT M Gpc
    hpc hM hG states
  have h2 := mergeSortList_cost_wl P (wl E) (2 * 2 ^ E) (fun x hx ↦ limbs_le_wl' hx)
    (by includes) keyLe (.closure entryArrayTC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (entryArrayTC.lam0.costSpec P (by includes) a b))
    (64 * 66 + 57) (fun e ↦ EntryKeyOK e.1)
    (fun a b ha hb ↦ keyLeLam_cost P (by includes) a b ha hb)
    (entryPairs pcT pre rd states) (by omega) hok
  have h3 := dedupFirst_cost P (by includes) ((entryPairs pcT pre rd states).mergeSort keyLe)
    (fun e he ↦ hok e (List.mem_mergeSort.1 he))
  have h4 := length_dedupFirst_le ((entryPairs pcT pre rd states).mergeSort keyLe)
  rw [List.length_mergeSort] at h3 h4
  generalize (dedupFirst ((entryPairs pcT pre rd states).mergeSort keyLe)).length = d at h4 ⊢
  generalize (entryPairs pcT pre rd states).length = n at hlen h2 h3 h4
  -- `⌈log₂ n⌉ ≤ E`
  have hclog : Nat.clog 2 n ≤ E := Nat.clog_le_of_le_pow (by omega)
  have hnE : n * Nat.clog 2 n ≤ n * E := Nat.mul_le_mul_left _ hclog
  have hc1 := Nat.mul_le_mul_left (64 * 66 + 57 + 62 + 5 * wl E) hnE
  have hpos := wl_pos E
  have hMs : ((4343 + 5 * wl E) * E + 7 * wl E + 4373) * n ≤
      ((4343 + 5 * wl E) * E + 7 * wl E + 4373) * (M * states.length) :=
    Nat.mul_le_mul_left _ hlen
  unfold entryArrayStatePrice
  nlinarith

end Pairs

/-! ## A frame lookup -/

/-- **The frame map on the sorted array** (`frameAtAC`): one binary search of the call's key
(`w = |args| + |rets|` words) in a table of keys of at most `56` codes and at most `2^E` pairs,
two frame reads: at most `(64w + 78 + 9·wl E)·(E + 2) + 27w + R + 1584`. -/
theorem frameAtA_cost (rd : Reader) (rdVal : MachineValue)
    (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
    (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
    (hP : Includes P frameAtAC.costDeps) (E : ℕ)
    (table : Array (CallKey × K)) (ht : ∀ e ∈ table, KeyOK 56 e.1) (hs : table.size ≤ 2 ^ E)
    (j : ℕ) (hj : j < 2 ^ 64) (args rets : List LeanVM.Parameters.E) (v : V) :
    machineCost P frameAtAC.costIdx [encodeValue table, rdVal, encodeValue j, encodeValue args,
        encodeValue rets, encodeValue v] ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) +
        27 * (args.length + rets.length) + R + 1584 := by
  rw [frameAtAC.costEq P hP table rd rdVal hrd]
  have h1 := isFunctionIndex_cost P (by includes) j hj
  have h2 := callKey_cost P (by includes) (canonIndex j) args rets
  have hk : KeyOK (args.length + rets.length) (callKey (canonIndex j) args rets) :=
    callKey_ok (canonIndex_lt64 j) (by omega) (by omega)
  have h3 := searchInKey_cost P (by includes) 56 table ht _ hk (2 ^ E) (wl E)
    (fun x hx ↦ limbs_le_wl' hx) hs 0 table.size (Nat.zero_le _) hs
  have hkc : keyCmpPrice (callKey (canonIndex j) args rets) =
      64 * (args.length + rets.length) + 41 := by
    simp [keyCmpPrice, callKey]
  have hlog : Nat.log2 (table.size - 0) ≤ E := by
    have := log2_mono (show table.size - 0 ≤ 2 ^ E by omega)
    rwa [Nat.log2_two_pow] at this
  have h3' : (keyCmpPrice (callKey (canonIndex j) args rets) + 37 + 9 * wl E) *
      (Nat.log2 (table.size - 0) + 2) ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) := by
    rw [hkc]
    exact Nat.mul_le_mul (by omega) (by omega)
  generalize (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) = X at h3' ⊢
  generalize searchIn table (callKey (canonIndex j) args rets) 0 table.size = o
  cases o with
  | none => dsimp only; split_ifs <;> omega
  | some fp =>
    have h4 := frameWordAt_cost P rd rdVal hrd R hR (by includes) fp j hj v
    dsimp only; split_ifs <;> omega

/-- **A frame looked up once** (`frameFpAC`, `frameAtA`'s search): one binary search of the call's
key (`w = |args| + |rets|` words): at most `(64w + 78 + 9·wl E)·(E + 2) + 27w + 49`. -/
theorem frameFpA_cost (hP : Includes P frameFpAC.costDeps) (E : ℕ)
    (table : Array (CallKey × K)) (ht : ∀ e ∈ table, KeyOK 56 e.1) (hs : table.size ≤ 2 ^ E)
    (j : ℕ) (hj : j < 2 ^ 64) (args rets : List LeanVM.Parameters.E) :
    machineCost P frameFpAC.costIdx [encodeValue table, encodeValue j, encodeValue args,
        encodeValue rets] ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) +
        27 * (args.length + rets.length) + 49 := by
  rw [frameFpAC.costEq P hP]
  have h1 := isFunctionIndex_cost P (by includes) j hj
  have h2 := callKey_cost P (by includes) (canonIndex j) args rets
  have hk : KeyOK (args.length + rets.length) (callKey (canonIndex j) args rets) :=
    callKey_ok (canonIndex_lt64 j) (by omega) (by omega)
  have h3 := searchInKey_cost P (by includes) 56 table ht _ hk (2 ^ E) (wl E)
    (fun x hx ↦ limbs_le_wl' hx) hs 0 table.size (Nat.zero_le _) hs
  have hkc : keyCmpPrice (callKey (canonIndex j) args rets) =
      64 * (args.length + rets.length) + 41 := by
    simp [keyCmpPrice, callKey]
  have hlog : Nat.log2 (table.size - 0) ≤ E := by
    have := log2_mono (show table.size - 0 ≤ 2 ^ E by omega)
    rwa [Nat.log2_two_pow] at this
  have h3' : (keyCmpPrice (callKey (canonIndex j) args rets) + 37 + 9 * wl E) *
      (Nat.log2 (table.size - 0) + 2) ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) := by
    rw [hkc]
    exact Nat.mul_le_mul (by omega) (by omega)
  generalize (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) = X at h3' ⊢
  split_ifs <;> omega

/-- **A word of a frame looked up once** (`frameValAtC`): at most `R + 1544`. -/
theorem frameValAt_cost (rd : Reader) (rdVal : MachineValue)
    (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
    (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
    (hP : Includes P frameValAtC.costDeps) (o : Option K) (j : ℕ) (hj : j < 2 ^ 64) (v : V) :
    machineCost P frameValAtC.costIdx [rdVal, encodeValue o, encodeValue j, encodeValue v] ≤
      R + 1544 := by
  rw [frameValAtC.costEq P hP rd rdVal hrd]
  cases o with
  | none => dsimp only; omega
  | some fp =>
    have h4 := frameWordAt_cost P rd rdVal hrd R hR (by includes) fp j hj v
    dsimp only; omega

end

end LeanVM.Cost.Bounds
