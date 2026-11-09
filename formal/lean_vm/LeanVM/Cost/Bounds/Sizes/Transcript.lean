module

public import LeanVM.Protocol.Extraction.Fast.Transcript

/-!
# Sizes along the extractor: the transcript and the committed word

* **Sorted maps** (`SortedMap`, Bentley–Saxe levels): after `N` insertions (`smGood`:
  levels of strictly increasing power-of-two weights, each holding at most its weight in
  entries; `smGood_insert`) a map holds at most `N` entries (`smEntryCount_le`) in at most
  `log₂(N + 1)` levels (`sm_two_pow_levels_le`: `2^levels ≤ N + 1`), so a lookup searches at most
  that many sorted arrays of at most `N` entries.
* **The transcript's index** (`transcriptIndex T L`, `N = |T|` permutation queries): the replay
  keeps at most `N + 1` paths (`replay_paths_length_le`), so at most `N + 1` evaluations, of at
  most `L` bytes each (`keccakEvaluationsFast_length_le`, `keccakEvaluationsFast_mem_length_le`);
  the index is a good map of at most `N + 1` insertions (`transcriptIndex_bounds`).
* **The committed word** (`subtreeLeavesWith`, `leafAt`): a subtree of height `h` has `2^h`
  leaves of `w` words each (`subtreeLeavesWith_size`, `subtreeLeavesWith_mem_length`), and every
  position of the word reads `w` words (`leafAt_length`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Extraction.Fast LeanVM.Extraction LeanVM.Parameters LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol LeanVM Common LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

/-! ## Sorted maps -/

section SortedMaps

variable {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
theorem length_mergeNewer_le : ∀ (a b : List (α × β)),
    (mergeNewer a b).length ≤ a.length + b.length
  | [], b => by simp [mergeNewer]
  | x :: a, [] => by simp [mergeNewer]
  | x :: a, y :: b => by
    rw [mergeNewer]
    split
    · have := length_mergeNewer_le a (y :: b); simp only [List.length_cons] at *; omega
    · have := length_mergeNewer_le a b; simp only [List.length_cons] at *; omega
    · have := length_mergeNewer_le (x :: a) b; simp only [List.length_cons] at *; omega

/-- A level is good: its weight a power of two, its entries at most its weight. -/
@[expose] def LevelGood (l : Level α β) : Prop :=
  (∃ e, l.weight = 2 ^ e) ∧ l.entries.size ≤ l.weight

/-- The levels' invariant: strictly increasing weights, each level good. -/
@[expose] def LevelsGood (ls : List (Level α β)) : Prop :=
  (ls.map (·.weight)).Pairwise (· < ·) ∧ ∀ l ∈ ls, LevelGood l

/-- **A sorted map's invariant.** -/
@[expose] def smGood (m : SortedMap α β) : Prop := LevelsGood m.levels

/-- The insertions a map holds (the weights' sum). -/
@[expose] def smWeightSum (m : SortedMap α β) : ℕ := (m.levels.map (·.weight)).sum

/-- The entries a map holds. -/
@[expose] def smEntryCount (m : SortedMap α β) : ℕ := (m.levels.map (·.entries.size)).sum

theorem pow_two_le_of_lt {e f : ℕ} (h : 2 ^ e < 2 ^ f) : 2 ^ (e + 1) ≤ 2 ^ f := by
  have : e < f := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h
  exact Nat.pow_le_pow_right (by norm_num) this

theorem carry_good : ∀ (ls : List (Level α β)) (l : Level α β), LevelsGood ls → LevelGood l →
    (∀ l' ∈ ls, l.weight ≤ l'.weight) →
    LevelsGood (carry l ls) ∧ ((carry l ls).map (·.weight)).sum = l.weight + (ls.map (·.weight)).sum
  | [], l, _, hl, _ => by
    rw [carry]
    exact ⟨⟨by simp, by simpa using hl⟩, by simp⟩
  | l' :: ls, l, hls, hl, hle => by
    rw [carry]
    obtain ⟨hpw, hgood⟩ := hls
    rw [List.map_cons, List.pairwise_cons] at hpw
    split
    · rename_i heq
      have hm : LevelGood (l.merge l') := by
        obtain ⟨⟨e, he⟩, hs⟩ := hl
        obtain ⟨-, hs'⟩ := hgood l' (by simp)
        refine ⟨⟨e + 1, by simp only [Level.merge]; rw [pow_succ]; omega⟩, ?_⟩
        simp only [Level.merge, List.size_toArray]
        have := length_mergeNewer_le l.entries.toList l'.entries.toList
        simp only [Array.length_toList] at this
        omega
      have hle' : ∀ l'' ∈ ls, (l.merge l').weight ≤ l''.weight := by
        intro l'' hl''
        have hlt := hpw.1 l''.weight (List.mem_map_of_mem hl'')
        obtain ⟨⟨e, he⟩, -⟩ := hl
        obtain ⟨⟨f, hf⟩, -⟩ := hgood l'' (by simp [hl''])
        simp only [Level.merge]
        have := pow_two_le_of_lt (e := e) (f := f) (by rw [← he, ← hf, heq]; exact hlt)
        rw [pow_succ] at this
        omega
      obtain ⟨h1, h2⟩ := carry_good ls (l.merge l')
        ⟨hpw.2, fun x hx ↦ hgood x (by simp [hx])⟩ hm hle'
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [Level.merge, List.map_cons, List.sum_cons]
      omega
    · rename_i hne
      have hlt : l.weight < l'.weight := lt_of_le_of_ne (hle l' (by simp)) hne
      refine ⟨⟨?_, ?_⟩, by simp⟩
      · rw [List.map_cons, List.map_cons, List.pairwise_cons, List.pairwise_cons]
        refine ⟨fun x hx ↦ ?_, hpw⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hlt
        · exact lt_trans hlt (hpw.1 x hx)
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hl
        · exact hgood x hx

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
theorem smGood_empty : smGood (SortedMap.empty : SortedMap α β) :=
  ⟨by simp [SortedMap.empty], by simp [SortedMap.empty]⟩

/-- A new level of one insertion on good levels. -/
theorem carry_good_one (ls : List (Level α β)) (l : Level α β) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (h : LevelsGood ls) :
    LevelsGood (carry l ls) ∧
      ((carry l ls).map (·.weight)).sum = (ls.map (·.weight)).sum + 1 := by
  have hl : LevelGood l := ⟨⟨0, hw⟩, by omega⟩
  have hle : ∀ l' ∈ ls, l.weight ≤ l'.weight := by
    intro l' hl'
    obtain ⟨⟨e, he⟩, -⟩ := h.2 l' hl'
    rw [hw, he]; exact Nat.one_le_two_pow
  obtain ⟨h1, h2⟩ := carry_good ls l h hl hle
  exact ⟨h1, by rw [h2, hw]; omega⟩

/-- **An insertion keeps the invariant and adds one to the weights.** -/
theorem smGood_insert {m : SortedMap α β} (h : smGood m) (k : α) (v : β) :
    smGood (m.insert k v) ∧ smWeightSum (m.insert k v) = smWeightSum m + 1 := by
  unfold smGood smWeightSum SortedMap.insert
  exact carry_good_one m.levels _ rfl rfl h

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
/-- **A good map holds at most its insertions in entries.** -/
theorem smEntryCount_le {m : SortedMap α β} (h : smGood m) : smEntryCount m ≤ smWeightSum m := by
  unfold smEntryCount smWeightSum
  have := h.2
  generalize m.levels = ls at this
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := (this l (by simp)).2
    have h2 := ih fun x hx ↦ this x (by simp [hx])
    omega

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
theorem levels_sum_ge : ∀ (ls : List (Level α β)) (j : ℕ), LevelsGood ls →
    (∀ l ∈ ls, 2 ^ j ≤ l.weight) → 2 ^ j * (2 ^ ls.length - 1) ≤ (ls.map (·.weight)).sum
  | [], _, _, _ => by simp
  | l :: ls, j, ⟨hpw, hg⟩, hlo => by
    rw [List.map_cons, List.pairwise_cons] at hpw
    have hl := hlo l (by simp)
    have hrest : ∀ l' ∈ ls, 2 ^ (j + 1) ≤ l'.weight := by
      intro l' hl'
      have hlt := hpw.1 l'.weight (List.mem_map_of_mem hl')
      obtain ⟨⟨e, he⟩, -⟩ := hg l (by simp)
      obtain ⟨⟨f, hf⟩, -⟩ := hg l' (by simp [hl'])
      have hej : j ≤ e := (Nat.pow_le_pow_iff_right (by norm_num)).1 (he ▸ hl)
      have := pow_two_le_of_lt (e := e) (f := f) (by rw [← he, ← hf]; exact hlt)
      rw [hf]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) this
    have ih := levels_sum_ge ls (j + 1) ⟨hpw.2, fun x hx ↦ hg x (by simp [hx])⟩ hrest
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e1 : 2 ^ (j + 1) * (2 ^ ls.length - 1) + 2 ^ j = 2 ^ j * (2 ^ (ls.length + 1) - 1) := by
      have h1 : 1 ≤ 2 ^ ls.length := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ (ls.length + 1) := Nat.one_le_two_pow
      zify [h1, h2]
      ring
    omega

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
/-- **A good map of `N` insertions has at most `log₂(N + 1)` levels**: `2^levels ≤ N + 1`. -/
theorem sm_two_pow_levels_le {m : SortedMap α β} (h : smGood m) :
    2 ^ m.levels.length ≤ smWeightSum m + 1 := by
  have := levels_sum_ge m.levels 0 h fun l hl ↦ by
    obtain ⟨⟨e, he⟩, -⟩ := h.2 l hl
    rw [he, pow_zero]; exact Nat.one_le_two_pow
  unfold smWeightSum
  have : 1 ≤ 2 ^ m.levels.length := Nat.one_le_two_pow
  omega

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
theorem smWeightSum_empty : smWeightSum (SortedMap.empty : SortedMap α β) = 0 := rfl

end SortedMaps

/-! ## The transcript's index -/

attribute [local instance] lexOrd

/-- The replay keeps at most one more path per query. -/
theorem replay_paths_length_le (B : ℕ) (T : List (PermutationQuery KeccakState × KeccakState)) :
    ∀ τ : ReplayFast, (T.foldl (ReplayFast.step B) τ).paths.length ≤ τ.paths.length + T.length := by
  induction T with
  | nil => intro τ; simp
  | cons q T ih =>
    intro τ
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    have : (ReplayFast.step B τ q).paths.length ≤ τ.paths.length + 1 := by
      obtain ⟨q, y⟩ := q
      cases q with
      | forward x =>
        simp only [ReplayFast.step]
        split
        · omega
        · split <;> simp
      | inverse y' =>
        simp only [ReplayFast.step]
        split <;> simp
    simp only [List.length_cons]
    omega

/-- **At most `N + 1` evaluations**, `N` the queries. -/
theorem keccakEvaluationsFast_length_le (T : List (PermutationQuery KeccakState × KeccakState))
    (L : ℕ) : (keccakEvaluationsFast T L).length ≤ T.length + 1 := by
  rw [keccakEvaluationsFast]
  refine (List.length_filterMap_le _ _).trans ?_
  have := replay_paths_length_le (L + rate) T ReplayFast.init
  have h0 : ReplayFast.init.paths.length = 1 := rfl
  omega

/-- **Each evaluation has at most `L` bytes.** -/
theorem keccakEvaluationsFast_mem_length_le {T : List (PermutationQuery KeccakState × KeccakState)}
    {L : ℕ} {e : Bytes × Digest} (he : e ∈ keccakEvaluationsFast T L) : e.1.length ≤ L := by
  rw [keccakEvaluationsFast, List.mem_filterMap] at he
  obtain ⟨p, -, hp⟩ := he
  rw [Option.bind_eq_some_iff] at hp
  obtain ⟨bs, -, hp⟩ := hp
  rw [Option.bind_eq_some_iff] at hp
  obtain ⟨m, -, hp⟩ := hp
  split at hp
  · cases hp; assumption
  · cases hp

/-- **The transcript's index**: a good sorted map of at most `N + 1` insertions (so at most
`N + 1` entries in at most `log₂(N + 2)` levels), keyed by digests and lengths `≤ L`. -/
theorem transcriptIndex_bounds (T : List (PermutationQuery KeccakState × KeccakState)) (L : ℕ) :
    smGood (transcriptIndex T L) ∧ smWeightSum (transcriptIndex T L) ≤ T.length + 1 := by
  rw [transcriptIndex, preimageIndex]
  have hgen : ∀ (l : List (Bytes × Digest)) (m : SortedMap (List UInt64 × ℕ) Hits), smGood m →
      smGood (l.foldl (fun m p ↦ m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m) ∧
      smWeightSum (l.foldl (fun m p ↦ m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m)
        = smWeightSum m + l.length := by
    intro l
    induction l with
    | nil => intro m hm; exact ⟨hm, by simp⟩
    | cons x l ih =>
      intro m hm
      obtain ⟨h1, h2⟩ := smGood_insert hm (hitKey x) ((m.getD (hitKey x) .none).merge (.one x.1))
      obtain ⟨h3, h4⟩ := ih _ h1
      refine ⟨h3, ?_⟩
      rw [List.foldl_cons, h4, h2, List.length_cons]
      omega
  obtain ⟨h1, h2⟩ := hgen _ _ smGood_empty
  refine ⟨h1, ?_⟩
  rw [h2, smWeightSum_empty, Nat.zero_add, answerPairs]
  refine (List.length_filterMap_le _ _).trans ?_
  rw [List.length_map]
  exact keccakEvaluationsFast_length_le T L

/-! ## The committed word -/

theorem bytesLanes_length : ∀ (w : ℕ) (b : Bytes), (bytesLanes w b).length = w
  | 0, _ => rfl
  | w + 1, b => by rw [bytesLanes, List.length_cons, bytesLanes_length w]

theorem leafOfWith_length (pre : Digest → ℕ → Option Bytes) (w : ℕ) (d : Digest) :
    (leafOfWith pre w d).length = w := by
  rw [leafOfWith]
  split
  · rw [bytesWords, List.length_map, bytesLanes_length]
  · rw [List.length_replicate]

/-- **A subtree of height `h` has `2^h` leaves.** -/
theorem subtreeLeavesWith_size (pre : Digest → ℕ → Option Bytes) (w : ℕ) :
    ∀ (h : ℕ) (d : Digest), (subtreeLeavesWith pre w h d).size = 2 ^ h := by
  intro h
  induction h with
  | zero => intro d; rfl
  | succ h ih =>
    intro d
    rw [subtreeLeavesWith]
    split
    · rw [Array.size_append, ih, ih, pow_succ]; omega
    · rw [Array.size_replicate]

/-- **Every leaf has `w` words.** -/
theorem subtreeLeavesWith_mem_length (pre : Digest → ℕ → Option Bytes) (w : ℕ) :
    ∀ (h : ℕ) (d : Digest) (x : List K), x ∈ subtreeLeavesWith pre w h d → x.length = w := by
  intro h
  induction h with
  | zero =>
    intro d x hx
    rw [subtreeLeavesWith, Array.mem_singleton] at hx
    rw [hx, leafOfWith_length]
  | succ h ih =>
    intro d x hx
    rw [subtreeLeavesWith] at hx
    split at hx
    · rw [Array.mem_append] at hx
      rcases hx with hx | hx
      · exact ih _ x hx
      · exact ih _ x hx
    · rw [Array.mem_replicate] at hx
      rw [hx.2, List.length_replicate]

/-- **Every position of the committed word reads `w` words.** -/
theorem leafAt_length (pre : Digest → ℕ → Option Bytes) (w h : ℕ) (d : Digest) (v : ℕ) :
    (leafAt (subtreeLeavesWith pre w h d) h w v).length = w := by
  rw [leafAt, Array.getD_eq_getD_getElem?]
  have hv : v % 2 ^ h < (subtreeLeavesWith pre w h d).size := by
    rw [subtreeLeavesWith_size]; exact Nat.mod_lt _ (by positivity)
  rw [Array.getElem?_eq_getElem hv, Option.getD_some]
  exact subtreeLeavesWith_mem_length pre w h d _ (Array.getElem_mem hv)

end

end LeanVM.Cost.Bounds
