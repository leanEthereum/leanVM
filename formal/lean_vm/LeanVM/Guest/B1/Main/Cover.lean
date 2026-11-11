/-
  LeanVM.Guest.B1.Main.Cover

  The coverage table of `main` as a bijection: every writer below the total stores its mark into
  one slot of its region, no two writers share a slot, so every slot holds one writer's mark, and
  the decoders' searches find them.
-/

module

public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Guest.Value.Pigeonhole

/-!
# The coverage table

The writers of `main`'s coverage table (lean_ethereum.py:4561-4632 at 40f877dc) are indexed by
`m < T`: the raw leanXMSS signatures (`m < RX`), the raw leanSPHINCS ones
(`RX ≤ m < RX + RS`), and child `c`'s claims, from its base `a c`: its leanXMSS claims, then its
leanSPHINCS ones (`Segs`). Writer `m` stores the mark `g^(wmark m)`: its index, except along a
gap-walked child list (`child_claim_list_mono`, `mx c`, `ms c`), whose claims all store the list's
first index. Each writer's slot lies in its region: leanXMSS slots below `LXS`, leanSPHINCS slots
in `[LXS, LXS + LSS)` (`region`, `InRegion`), and along a gap-walked list the slots strictly
increase (`Writers.mono`).

Two writers of one slot store one value (write-once memory), so one mark; writers of one mark are
one writer or two claims of one gap-walked list, whose slots differ: the slot map is injective
(`Writers.inj`), and with as many writers as slots, onto (`Writers.onto`, from
`Value.cover_of_writeOnce`).

For the decoders: `find_first` (the child whose segment holds a writer), `find_unique` (the slot
holding a mark), `filter_perm` (a segment's slots in a region).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

/-! ## Searches over a range -/

/-- The first index below `n` at which a monotone `A` passes `e` is the `c` with
`A c ≤ e < A (c + 1)`. -/
theorem find_first {A : ℕ → ℕ} (hA : Monotone A) {n c e : ℕ} (hc : c < n) (h1 : A c ≤ e)
    (h2 : e < A (c + 1)) :
    ((List.range n).find? fun c' => decide (e < A (c' + 1))).getD 0 = c := by
  have key : (List.range n).find? (fun c' => decide (e < A (c' + 1))) = some c := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using h2, c, by simpa using hc, by simp, fun j hj => ?_⟩
    simp only [List.getElem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      not_lt]
    exact le_trans (hA (show j + 1 ≤ c by omega)) h1
  rw [key]; rfl

/-- A search for the unique index below `n` passing `p`. -/
theorem find_unique {p : ℕ → Bool} {n s : ℕ} (hs : s < n) (hp : p s = true)
    (hu : ∀ t < n, p t = true → t = s) : ((List.range n).find? p).getD 0 = s := by
  have key : (List.range n).find? p = some s := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨hp, s, by simpa using hs, by simp, fun j hj => ?_⟩
    simp only [List.getElem_range]
    by_contra hc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    have := hu j (by omega) hc
    omega
  rw [key]; rfl

/-- The indices below `len` passing `P` are a permutation of the images of `j < k` under an
injective `f`. -/
theorem filter_perm {P : ℕ → Bool} {len k : ℕ} (f : ℕ → ℕ) (hf : ∀ j < k, f j < len ∧ P (f j))
    (hinj : ∀ i < k, ∀ j < k, f i = f j → i = j)
    (hall : ∀ s < len, P s = true → ∃ j < k, f j = s) :
    ((List.range len).filter P).Perm ((List.range k).map f) := by
  have hnd1 : ((List.range len).filter P).Nodup := (List.nodup_range).filter _
  have hnd2 : ((List.range k).map f).Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro i hi j hj h
    exact hinj i (List.mem_range.mp hi) j (List.mem_range.mp hj) h
  rw [List.perm_ext_iff_of_nodup hnd1 hnd2]
  intro s
  simp only [List.mem_filter, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨hs, hP⟩
    exact hall s hs hP
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(hf j hj).1, (hf j hj).2⟩

/-- The indices below `len` passing `P` are the images of `j < k` under an injective `f`: as many
as `k`. -/
theorem filter_card {P : ℕ → Bool} {len k : ℕ} (f : ℕ → ℕ) (hf : ∀ j < k, f j < len ∧ P (f j))
    (hinj : ∀ i < k, ∀ j < k, f i = f j → i = j)
    (hall : ∀ s < len, P s = true → ∃ j < k, f j = s) :
    ((List.range len).filter P).length = k := by
  rw [(filter_perm f hf hinj hall).length_eq, List.length_map, List.length_range]

/-- The indices below `len` passing `P`, in order, are the images of `j < k` under an `f` that
strictly increases. -/
theorem filter_eq_map {P : ℕ → Bool} {len k : ℕ} (f : ℕ → ℕ) (hf : ∀ j < k, f j < len ∧ P (f j))
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hall : ∀ s < len, P s = true → ∃ j < k, f j = s) :
    (List.range len).filter P = (List.range k).map f := by
  have hinj : ∀ i < k, ∀ j < k, f i = f j → i = j := by
    intro i hi j hj h
    rcases Nat.lt_trichotomy i j with h' | h' | h'
    · have := hmono i j h' hj; omega
    · exact h'
    · have := hmono j i h' hi; omega
  refine List.Perm.eq_of_sortedLE ?_ ?_ (filter_perm f hf hinj hall)
  · exact List.Pairwise.sortedLE ((List.pairwise_lt_range.filter _).imp le_of_lt)
  · refine List.Pairwise.sortedLE ?_
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {i j} _ hj hij => ?_
    exact le_of_lt (hmono i j hij (List.mem_range.mp hj))

/-! ## The segments -/

/-- The writers' structure: raw signature counts, the children's counts and walks. -/
structure Segs where
  RX : ℕ
  RS : ℕ
  NC : ℕ
  ex : ℕ → ℕ
  es : ℕ → ℕ
  /-- Child `c`'s leanXMSS list is gap-walked (one mark). -/
  mx : ℕ → Bool
  /-- Child `c`'s leanSPHINCS list is gap-walked (one mark). -/
  ms : ℕ → Bool

namespace Segs

variable (S : Segs)

/-- Child `c`'s base: the writers before its segment. -/
def a : ℕ → ℕ
  | 0 => S.RX + S.RS
  | c + 1 => a c + (S.ex c + S.es c)

theorem a_mono : Monotone S.a := monotone_nat_of_le_succ fun c => by simp [a]

theorem a_succ (c : ℕ) : S.a (c + 1) = S.a c + (S.ex c + S.es c) := rfl

/-- The child whose segment holds the writer `m`. -/
noncomputable def kid (m : ℕ) : ℕ := ((List.range S.NC).find? fun c => decide (m < S.a (c + 1))).getD 0

/-- The region of the writer `m`: `0` leanXMSS, `1` leanSPHINCS. -/
noncomputable def region (m : ℕ) : ℕ :=
  if m < S.RX then 0 else if m < S.RX + S.RS then 1 else
  if m - S.a (S.kid m) < S.ex (S.kid m) then 0 else 1

/-- **The mark writer `m` stores**, as a log: its index, but a gap-walked list's first index along
the list (`child_claim_list_mono` marks every claim with the list's base). -/
noncomputable def wmark (m : ℕ) : ℕ :=
  if m < S.RX + S.RS then m else
  if m - S.a (S.kid m) < S.ex (S.kid m) then (if S.mx (S.kid m) then S.a (S.kid m) else m)
  else (if S.ms (S.kid m) then S.a (S.kid m) + S.ex (S.kid m) else m)

theorem seg_exists {m : ℕ} (h0 : S.a 0 ≤ m) :
    ∀ n, m < S.a n → ∃ c, c < n ∧ S.a c ≤ m ∧ m < S.a (c + 1) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h1
    by_cases hn : m < S.a n
    · obtain ⟨c, hc, h⟩ := ih hn
      exact ⟨c, by omega, h⟩
    · exact ⟨n, by omega, by omega, h1⟩

theorem kid_spec {m : ℕ} (h0 : S.a 0 ≤ m) (h1 : m < S.a S.NC) :
    S.kid m < S.NC ∧ S.a (S.kid m) ≤ m ∧ m < S.a (S.kid m + 1) := by
  obtain ⟨c, hc, hc1, hc2⟩ := S.seg_exists h0 S.NC h1
  have := find_first S.a_mono hc hc1 hc2
  unfold kid
  rw [this]
  exact ⟨hc, hc1, hc2⟩

theorem kid_eq {c m : ℕ} (hc : c < S.NC) (h1 : S.a c ≤ m) (h2 : m < S.a (c + 1)) :
    S.kid m = c := find_first S.a_mono hc h1 h2

theorem a0_le (c : ℕ) : S.RX + S.RS ≤ S.a c := S.a_mono (Nat.zero_le c)

/-- A raw writer's mark is its index. -/
theorem wmark_raw {m : ℕ} (h : m < S.RX + S.RS) : S.wmark m = m := by
  unfold wmark; rw [ite_pos' h]

/-- A child's leanXMSS writer's mark. -/
theorem wmark_x {c m : ℕ} (hc : c < S.NC) (h1 : S.a c ≤ m) (h2 : m < S.a c + S.ex c) :
    S.wmark m = if S.mx c then S.a c else m := by
  have h0 := S.a0_le c
  have hk := S.kid_eq hc h1 (by rw [S.a_succ]; omega)
  unfold wmark; rw [ite_neg' (by omega), hk, ite_pos' (by omega)]

/-- A child's leanSPHINCS writer's mark. -/
theorem wmark_s {c m : ℕ} (hc : c < S.NC) (h1 : S.a c + S.ex c ≤ m) (h2 : m < S.a (c + 1)) :
    S.wmark m = if S.ms c then S.a c + S.ex c else m := by
  have h0 := S.a0_le c
  have hk := S.kid_eq hc (by omega) h2
  unfold wmark; rw [ite_neg' (by omega), hk, ite_neg' (by omega)]

/-- **A writer's mark lies in its own list's range**: at most its index, and at least the
list's first index (a raw writer's list is itself). -/
theorem wmark_range {m : ℕ} (hm : m < S.a S.NC) :
    S.wmark m ≤ m ∧ (m < S.RX + S.RS → S.wmark m = m) ∧
      (S.RX + S.RS ≤ m → S.a (S.kid m) ≤ S.wmark m ∧ S.kid m < S.NC ∧ S.a (S.kid m) ≤ m ∧
        m < S.a (S.kid m + 1) ∧
        (m < S.a (S.kid m) + S.ex (S.kid m) → S.wmark m < S.a (S.kid m) + S.ex (S.kid m)) ∧
        (S.a (S.kid m) + S.ex (S.kid m) ≤ m → S.a (S.kid m) + S.ex (S.kid m) ≤ S.wmark m)) := by
  by_cases hr : m < S.RX + S.RS
  · rw [S.wmark_raw hr]; exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (by omega)⟩
  · obtain ⟨hc, h1, h2⟩ := S.kid_spec (m := m) (by simp [a]; omega) hm
    set c := S.kid m
    have hs := S.a_succ c
    refine ⟨?_, fun h => absurd h hr, fun _ => ?_⟩
    · by_cases hx : m < S.a c + S.ex c
      · rw [S.wmark_x hc h1 hx]; split <;> omega
      · rw [S.wmark_s hc (by omega) h2]; split <;> omega
    · by_cases hx : m < S.a c + S.ex c
      · rw [S.wmark_x hc h1 hx]
        refine ⟨by split <;> omega, hc, h1, h2, fun _ => by split <;> omega, fun h => by omega⟩
      · rw [S.wmark_s hc (by omega) h2]
        refine ⟨by split <;> omega, hc, h1, h2, fun h => by omega, fun _ => by split <;> omega⟩

/-- **The writer of a mark in child `c`'s segment** lies in that segment. -/
theorem wmark_seg {c m : ℕ} (hm : m < S.a S.NC) (hc : c < S.NC) (h1 : S.a c ≤ S.wmark m)
    (h2 : S.wmark m < S.a (c + 1)) : S.a c ≤ m ∧ m < S.a (c + 1) := by
  obtain ⟨hle, hraw, hkid⟩ := S.wmark_range hm
  have h0 := S.a0_le c
  by_cases hr : m < S.RX + S.RS
  · rw [hraw hr] at h1; omega
  · obtain ⟨hk1, hkc, hk2, hk3, -, -⟩ := hkid (by omega)
    set k := S.kid m
    rcases Nat.lt_trichotomy k c with h | h | h
    · have := S.a_mono (show k + 1 ≤ c by omega); omega
    · subst h; exact ⟨hk2, hk3⟩
    · have := S.a_mono (show c + 1 ≤ k by omega); omega

/-- A writer whose mark is a raw signature's index is that raw signature. -/
theorem wmark_raw_eq {m : ℕ} (hm : m < S.a S.NC) (h : S.wmark m < S.RX + S.RS) :
    S.wmark m = m := by
  obtain ⟨-, hraw, hkid⟩ := S.wmark_range hm
  by_cases hr : m < S.RX + S.RS
  · exact hraw hr
  · have := (hkid (by omega)).1
    have := S.a0_le (S.kid m)
    omega

end Segs

/-- The slot `s` lies in the region `r` of a table of `LXS` leanXMSS slots, then `LSS`
leanSPHINCS slots. -/
def InRegion (LXS LSS : ℕ) (r s : ℕ) : Prop :=
  (r = 0 → s < LXS) ∧ (r = 1 → LXS ≤ s ∧ s < LXS + LSS)

theorem region_le (S : Segs) (m : ℕ) : S.region m ≤ 1 := by
  unfold Segs.region; split_ifs <;> omega

/-- The slot of a writer lies in its region's range, and conversely. -/
theorem inRegion_iff {X Y r s : ℕ} (h : InRegion X Y r s) (hr : r ≤ 1) :
    (s < X ↔ r = 0) ∧ (X ≤ s ∧ s < X + Y ↔ r = 1) := by
  obtain ⟨h0, h1⟩ := h
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · have := h0 rfl; omega
  · have := h1 rfl; omega

/-! ## The writers -/

/-- **What the writers establish**, for the coverage table at `cover` and the writers' slots
`sl`: writer `m` stores its mark `g^(wmark m)` in its region, and writers of one mark (a gap-walked
list) have strictly increasing slots. -/
structure Writers (rd : Reader) (cover : E) (S : Segs) (LXS LSS : ℕ) (sl : ℕ → ℕ) : Prop where
  wr : ∀ m < LXS + LSS, LoadHolds rd cover (sl m) (gen ^ S.wmark m)
  reg : ∀ m < LXS + LSS, InRegion LXS LSS (S.region m) (sl m)
  mono : ∀ m₁ m₂, m₁ < m₂ → m₂ < LXS + LSS → S.wmark m₁ = S.wmark m₂ → sl m₁ < sl m₂
  total : S.a S.NC = LXS + LSS
  small : LXS + LSS < 2 ^ 34

namespace Writers

variable {rd : Reader} {cover : E} {S : Segs} {LXS LSS : ℕ} {sl : ℕ → ℕ}

theorem lt (W : Writers rd cover S LXS LSS sl) {m : ℕ} (hm : m < LXS + LSS) :
    sl m < LXS + LSS := by
  have := inRegion_iff (W.reg m hm) (region_le S m)
  rcases (show S.region m = 0 ∨ S.region m = 1 by have := region_le S m; omega) with h | h
  · have := this.1.mpr h; omega
  · exact (this.2.mpr h).2

theorem wmark_lt (W : Writers rd cover S LXS LSS sl) {m : ℕ} (hm : m < LXS + LSS) :
    S.wmark m < LXS + LSS :=
  lt_of_le_of_lt (S.wmark_range (by rw [W.total]; exact hm)).1 hm

/-- **No two writers share a slot.** -/
theorem inj (W : Writers rd cover S LXS LSS sl) :
    ∀ m₁ < LXS + LSS, ∀ m₂ < LXS + LSS, sl m₁ = sl m₂ → m₁ = m₂ := by
  intro m₁ h₁ m₂ h₂ h
  have hs := W.small
  have e1 := W.wr m₁ h₁
  rw [h] at e1
  have hmk : S.wmark m₁ = S.wmark m₂ :=
    gen_pow_inj34 (by have := W.wmark_lt h₁; omega) (by have := W.wmark_lt h₂; omega)
      (loadHolds_unique e1 (W.wr m₂ h₂))
  rcases Nat.lt_trichotomy m₁ m₂ with hlt | heq | hlt
  · have := W.mono m₁ m₂ hlt h₂ hmk; omega
  · exact heq
  · have := W.mono m₂ m₁ hlt h₁ hmk.symm; omega

/-- **Every slot has its writer** (pigeonhole: as many writers as slots). -/
theorem onto (W : Writers rd cover S LXS LSS sl) :
    ∀ s < LXS + LSS, ∃ m < LXS + LSS, sl m = s := by
  intro s hs
  obtain ⟨m, ⟨hm, hms⟩, -⟩ := cover_of_writeOnce (N := LXS + LSS) (M := LXS + LSS) (slot := sl)
    (mark := sl) (mem := id) (fun m hm => W.lt hm) W.inj (fun _ _ => rfl) le_rfl s hs
  exact ⟨m, hm, hms⟩

/-- The writer of a raw signature's mark is that signature: a slot holding the mark `m`,
`m < RX + RS`, is writer `m`'s. -/
theorem uniq_raw (W : Writers rd cover S LXS LSS sl) {s m : ℕ} (hs : s < LXS + LSS)
    (hm : m < S.RX + S.RS) (hl : LoadHolds rd cover s (gen ^ m)) : s = sl m := by
  have hsm := W.small
  have hT := W.total
  have ha := S.a0_le S.NC
  obtain ⟨m', hm', rfl⟩ := W.onto s hs
  have hmk : S.wmark m' = m :=
    gen_pow_inj34 (by have := W.wmark_lt hm'; omega) (by omega)
      (loadHolds_unique (W.wr m' hm') hl)
  obtain ⟨-, hraw, hkid⟩ := S.wmark_range (by rw [hT]; exact hm')
  by_cases hr : m' < S.RX + S.RS
  · rw [hraw hr] at hmk; rw [hmk]
  · obtain ⟨hk1, hkc, -⟩ := hkid (by omega)
    have := S.a0_le (S.kid m')
    omega

end Writers

/-- The mark in slot `s` of the table at `cover`, as a log. -/
noncomputable def markAt (rd : Reader) (cover : E) (s : ℕ) : ℕ := gLog (memAt rd cover s)

theorem markAt_sl {rd : Reader} {cover : E} {S : Segs} {X Y : ℕ} {sl : ℕ → ℕ}
    (W : Writers rd cover S X Y sl) {m : ℕ} (hm : m < X + Y) : markAt rd cover (sl m) = S.wmark m := by
  have := W.wmark_lt hm
  have := W.small
  unfold markAt; rw [memAt_of_load (W.wr m hm), gLog_gen_pow (by omega)]

/-- **The slot of a raw signature's mark** is its writer's. -/
theorem slot_raw {rd : Reader} {cover : E} {S : Segs} {X Y : ℕ} {sl : ℕ → ℕ}
    (W : Writers rd cover S X Y sl) {t m : ℕ} (ht : t < X + Y) (hm : m < S.RX + S.RS)
    (h : markAt rd cover t = m) : t = sl m := by
  obtain ⟨m', hm', rfl⟩ := W.onto t ht
  rw [markAt_sl W hm'] at h
  have := S.wmark_raw_eq (by rw [W.total]; exact hm') (by omega)
  rw [← h, this]

end
end LeanVM.Guest.B1.Main
