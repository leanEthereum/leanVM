/-
  LeanVM.Guest.B1.Main.Decode

  The decoders of `main`'s witness against the filled coverage table: the marks, the running
  counts, the child of a mark, the slot of a mark, a segment's count in a region.
-/

module

public import LeanVM.Guest.B1.Main.World

/-!
# The decoders, read off the coverage table

With the coverage table filled (`Writers` of `writers`, every slot its writer's, `Writers.onto`):
`markOf` is the mark of the slot's writer (`markAt_sl`), `countOf` the base `a c` (`countOf_eq`),
a list's slots in a region (`kidSlots_eq`: its count, and by slot or by mark its slots), so a
child's statement is its records' (`kidStmt_eq`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec} {sl : ℕ → ℕ}

/-! ## Counts -/

theorem lg_eq_gLog (σ : Val) (v : ℕ) : lg σ v = gLog (σ (.n v)) := by unfold lg; rfl

theorem lxSlots_eq (MF : MainFacts C rd σ) : lxSlots σ = LXS σ := by
  have hT := MF.total.2
  unfold lxSlots; rw [MF.lxs, gLog_gen_pow (by omega)]

theorem lsSlots_eq (MF : MainFacts C rd σ) : lsSlots σ = LSS σ := by
  have hT := MF.total.2
  unfold lsSlots; rw [MF.lss, gLog_gen_pow (by omega)]

theorem nKids_eq (σ : Val) : nKids σ = lg σ 6 := by unfold nKids; rw [lg_eq_gLog]

theorem nRawX_eq (σ : Val) : nRawX σ = lg σ 2 := by unfold nRawX; rw [lg_eq_gLog]
theorem nRawS_eq (σ : Val) : nRawS σ = lg σ 5 := by unfold nRawS; rw [lg_eq_gLog]
theorem nDirect_eq (σ : Val) : nDirect σ = lg σ 7 := by unfold nDirect; rw [lg_eq_gLog]

theorem countOf_eq (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c : ℕ}
    (hc : c ≤ lg σ 6) : countOf rd σ c = (segsOf σ K).a c := by
  have hb := a_lt MF hK hc
  unfold countOf
  rw [cellAt_eq_memAt, memAt_of_load (written_eq MF hK c hc), gLog_gen_pow (by omega)]

/-! ## The marks -/

theorem markOf_eq (s : ℕ) : markOf rd σ s = markAt rd (σ (.n 45)) s := by
  unfold markOf markAt; rw [cellAt_eq_memAt]

/-! ## A list's slots in a region -/

/-- **A list's slots read off a region**: `n` claims at slots `f j` of the region `[lo, lo + len)`
with marks `a + j`, or all `a` along a gap walk (`mono`, the slots increasing), the only slots of
the region with marks in `[a, b)`: the region's count of `[a, b)` is `n`, and `kidSlots` reads
the slots `f j` in order. -/
theorem kidSlots_eq {lo len a b n : ℕ} {mono : Bool} (f : ℕ → ℕ)
    (hf : ∀ j < n, f j < len ∧ markOf rd σ (lo + f j) = a + (if mono then 0 else j))
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hmono : mono = true → ∀ i j, i < j → j < n → f i < f j) (hab : a + n ≤ b)
    (hall : ∀ s < len, a ≤ markOf rd σ (lo + s) → markOf rd σ (lo + s) < b → ∃ j < n, f j = s) :
    segCount rd σ lo len a b = n ∧ kidSlots rd σ lo len a b = (List.range n).map f := by
  have hcount : segCount rd σ lo len a b = n := by
    unfold segCount
    refine filter_card f (fun j hj => ⟨(hf j hj).1, ?_⟩) hinj (fun s hs hP => ?_)
    · rw [(hf j hj).2]; simp only [decide_eq_true_eq]; split <;> omega
    · simp only [decide_eq_true_eq] at hP; exact hall s hs hP.1 hP.2
  refine ⟨hcount, ?_⟩
  unfold kidSlots
  rw [hcount]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    split
    · unfold segCount at hcount; exact List.eq_nil_of_length_eq_zero hcount
    · rfl
  -- the filter's slots, in order, when the slots increase
  have hfilt : (∀ i j, i < j → j < n → f i < f j) →
      ((List.range len).filter fun s => decide (a ≤ markOf rd σ (lo + s) ∧
        markOf rd σ (lo + s) < b)) = (List.range n).map f := by
    intro hm
    refine filter_eq_map f (fun j hj => ⟨(hf j hj).1, ?_⟩) hm (fun s hs hP => ?_)
    · rw [(hf j hj).2]; simp only [decide_eq_true_eq]; split <;> omega
    · simp only [decide_eq_true_eq] at hP; exact hall s hs hP.1 hP.2
  cases mono with
  | true =>
    -- every slot holds `a`
    have hfirst : segCount rd σ lo len a (a + 1) = n := by
      unfold segCount
      refine filter_card f (fun j hj => ⟨(hf j hj).1, ?_⟩) hinj (fun s hs hP => ?_)
      · rw [(hf j hj).2]; simp
      · simp only [decide_eq_true_eq] at hP; exact hall s hs hP.1 (by omega)
    rw [ite_pos' hfirst]
    exact hfilt (hmono rfl)
  | false =>
    split
    · -- one claim
      rename_i hfirst
      have h1 : segCount rd σ lo len a (a + 1) = 1 := by
        unfold segCount
        refine filter_card f (fun j hj => ?_) (fun i hi j hj _ => by omega)
          (fun s hs hP => ?_)
        · obtain rfl : j = 0 := by omega
          refine ⟨(hf 0 hn).1, ?_⟩
          rw [(hf 0 hn).2]; simp
        · simp only [decide_eq_true_eq] at hP
          obtain ⟨j, hj, rfl⟩ := hall s hs hP.1 (by omega)
          have := (hf j hj).2
          simp only [Bool.false_eq_true, ↓reduceIte] at this
          exact ⟨0, by omega, by congr 1; omega⟩
      exact hfilt fun i j hij hj => by omega
    · -- by mark
      refine List.map_congr_left fun j hj => ?_
      have hj := List.mem_range.mp hj
      unfold slotOf
      refine find_unique (hf j hj).1 ?_ (fun t ht hp => ?_)
      · have := (hf j hj).2
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        simp [this]
      · simp only [decide_eq_true_eq] at hp
        obtain ⟨j', hj', rfl⟩ := hall t ht (by omega) (by omega)
        have := (hf j' hj').2
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        rw [show j' = j by omega]

/-! ## Regions of a child's writers -/

/-- The region of a writer in child `c`'s segment. -/
theorem region_kid {S : Segs} {c m : ℕ} (hc : c < S.NC) (h1 : S.a c ≤ m) (h2 : m < S.a (c + 1)) :
    S.region m = if m - S.a c < S.ex c then 0 else 1 := by
  have ha0 : S.a 0 ≤ S.a c := S.a_mono (Nat.zero_le c)
  have h0 : S.a 0 = S.RX + S.RS := rfl
  have hk : S.kid m = c := S.kid_eq hc h1 h2
  unfold Segs.region
  rw [ite_neg' (by omega), ite_neg' (by omega), hk]

theorem region_kid' {S : Segs} {c m : ℕ} (hc : c < S.NC) (h1 : S.a c ≤ m) (h2 : m < S.a (c + 1)) :
    (S.region m = 0 ↔ m < S.a c + S.ex c) ∧
      (S.region m = 1 ↔ S.a c + S.ex c ≤ m ∧ m < S.a c + S.ex c + S.es c) := by
  rw [region_kid hc h1 h2]
  have hs : S.a (c + 1) = S.a c + (S.ex c + S.es c) := rfl
  by_cases ha : m - S.a c < S.ex c
  · rw [ite_pos' ha]
    exact ⟨⟨fun _ => by omega, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), fun h => by omega⟩⟩
  · rw [ite_neg' ha]
    exact ⟨⟨fun h => absurd h (by decide), fun h => by omega⟩, ⟨fun _ => ⟨by omega, by omega⟩,
      fun _ => rfl⟩⟩

/-! ## A child's statement -/

section Kid

variable {rx rs : ℕ → ℕ}

/-- The writer of a slot of the table, its mark in child `c`'s segment: one of the child's. -/
theorem kid_writer (hW : Writers rd (σ (.n 45)) (segsOf σ K) (LXS σ) (LSS σ) (slOf σ K rx rs)) {c s : ℕ}
    (hc : c < lg σ 6) (hs : s < LXS σ + LSS σ)
    (h1 : (segsOf σ K).a c ≤ markAt rd (σ (.n 45)) s)
    (h2 : markAt rd (σ (.n 45)) s < (segsOf σ K).a (c + 1)) :
    (s < LXS σ → ∃ j < (K c).ex, (K c).ox j = s) ∧
      (LXS σ ≤ s → ∃ j < (K c).es, LXS σ + (K c).os j = s) := by
  obtain ⟨m, hm, rfl⟩ := hW.onto s hs
  rw [markAt_sl hW hm] at h1 h2
  have hcN : c < (segsOf σ K).NC := by rw [segsOf_NC]; exact hc
  obtain ⟨hm1, hm2⟩ := (segsOf σ K).wmark_seg (by rw [hW.total]; exact hm) hcN h1 h2
  obtain ⟨r0, r1⟩ := region_kid' hcN hm1 hm2
  obtain ⟨i0, i1⟩ := inRegion_iff (hW.reg m hm) (region_le _ _)
  have hsucc := (segsOf σ K).a_succ c
  simp only [segsOf_ex, segsOf_es] at r0 r1 hsucc
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hx := r0.mp (i0.mp hlt)
    refine ⟨m - (segsOf σ K).a c, by omega, ?_⟩
    rw [← slOf_x (rx := rx) (rs := rs) hc (by omega), Nat.add_sub_cancel' hm1]
  · have hx := r1.mp (i1.mp ⟨hge, hW.lt hm⟩)
    refine ⟨m - (segsOf σ K).a c - (K c).ex, by omega, ?_⟩
    rw [← slOf_s (rx := rx) (rs := rs) hc (by omega)]
    congr 1; omega

/-- **Child `c`'s statement, read off the coverage table**, is its records'. -/
theorem kidStmt_eq (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c))
    (hW : Writers rd (σ (.n 45)) (segsOf σ K) (LXS σ) (LSS σ) (slOf σ K rx rs)) {c : ℕ}
    (hc : c < lg σ 6) :
    kidStmt rd σ c =
      ⟨⟨(List.range (K c).ex).map fun j => xmssAt rd (σ (.n 31)) ((K c).ox j),
        (List.range (K c).es).map fun j => sphincsAt rd (σ (.n 34)) ((K c).os j),
        daDigestAt rd σ c⟩,
       deferOfCells (readCells rd (σ (.n 396) * gen ^ (24 * c)) 24)⟩ := by
  have hT := MF.total.2
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  have hcN : c < (segsOf σ K).NC := by rw [segsOf_NC]; exact hc
  have htot := hW.total
  have hab : (segsOf σ K).a (c + 1) ≤ LXS σ + LSS σ := by
    rw [← htot]; exact (segsOf σ K).a_mono (by omega)
  have hsucc : (segsOf σ K).a (c + 1) = (segsOf σ K).a c + ((K c).ex + (K c).es) := by
    rw [Segs.a_succ, segsOf_ex, segsOf_es]
  have hmk : ∀ s, markOf rd σ s = markAt rd (σ (.n 45)) s := fun s => markOf_eq s
  -- the leanXMSS list
  obtain ⟨hnx, hX⟩ := kidSlots_eq (rd := rd) (σ := σ) (lo := 0) (len := LXS σ)
    (a := (segsOf σ K).a c) (b := (segsOf σ K).a (c + 1)) (mono := (K c).mx) (K c).ox
    (fun j hj => by
      refine ⟨(kid_wx MF hK hc hj).1, ?_⟩
      rw [Nat.zero_add, hmk, ← slOf_x (rx := rx) (rs := rs) hc hj, markAt_sl hW (by omega),
        (segsOf σ K).wmark_x hcN (by omega) (by rw [segsOf_ex]; omega), segsOf_mx]
      split <;> simp)
    (fun i hi j hj h => by
      rw [← slOf_x (rx := rx) (rs := rs) hc hi, ← slOf_x (rx := rx) (rs := rs) hc hj] at h
      have := hW.inj _ (by omega) _ (by omega) h
      omega)
    (hK c hc).xmono (by omega)
    (fun s hs h1 h2 => by
      rw [Nat.zero_add, hmk] at h1 h2
      exact (kid_writer hW hc (by omega) h1 h2).1 hs)
  -- the leanSPHINCS list
  obtain ⟨-, hS⟩ := kidSlots_eq (rd := rd) (σ := σ) (lo := LXS σ) (len := LSS σ)
    (a := (segsOf σ K).a c + (K c).ex) (b := (segsOf σ K).a (c + 1)) (mono := (K c).ms) (K c).os
    (fun j hj => by
      refine ⟨(kid_ws MF hK hc hj).1, ?_⟩
      rw [hmk, ← slOf_s (rx := rx) (rs := rs) hc hj, markAt_sl hW (by omega),
        (segsOf σ K).wmark_s hcN (by rw [segsOf_ex]; omega)
          (by rw [Segs.a_succ, segsOf_ex, segsOf_es]; omega), segsOf_ms, segsOf_ex]
      split <;> simp)
    (fun i hi j hj h => by
      have h' : slOf σ K rx rs ((segsOf σ K).a c + (K c).ex + i) =
          slOf σ K rx rs ((segsOf σ K).a c + (K c).ex + j) := by
        rw [slOf_s hc hi, slOf_s hc hj, h]
      have := hW.inj _ (by omega) _ (by omega) h'
      omega)
    (hK c hc).smono (by omega)
    (fun s hs h1 h2 => by
      rw [hmk] at h1 h2
      obtain ⟨j, hj, he⟩ := (kid_writer hW hc (by omega) (by omega) h2).2 (by omega)
      exact ⟨j, hj, by omega⟩)
  unfold kidStmt
  simp only [countOf_eq MF hK (show c ≤ lg σ 6 by omega),
    countOf_eq MF hK (show c + 1 ≤ lg σ 6 by omega), lxSlots_eq MF, lsSlots_eq MF, hnx, hX, hS,
    List.map_map]
  rfl

end Kid

end
end LeanVM.Guest.B1.Main
