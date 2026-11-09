/-
  LeanVM.Guest.B1.Main.World

  `main`'s run as the coverage table's writers: the segments of the marks, the running counts as
  their bases, the writers in their regions, and the bijection.
-/

module

public import LeanVM.Guest.B1.Main.Kids

/-!
# `main`'s coverage table, filled

From `MainFacts` and the children's records (`KidOk`): the segments (`segsOf`), the running
counts `written[c] = g^(a c)` (`written_eq`), the writers' slots (`slOf`: the raw signatures'
chosen, `raw_slots`; a child's claims' its records'), the writers in their regions (`writers`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

/-- The segments of `main`'s marks. -/
noncomputable def segsOf (σ : Val) (K : ℕ → KidRec) : Segs :=
  ⟨lg σ 2, lg σ 5, lg σ 6, fun c => (K c).ex, fun c => (K c).es, fun c => (K c).mx,
    fun c => (K c).ms⟩

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec}

theorem segsOf_RX : (segsOf σ K).RX = lg σ 2 := rfl
theorem segsOf_RS : (segsOf σ K).RS = lg σ 5 := rfl
theorem segsOf_NC : (segsOf σ K).NC = lg σ 6 := rfl
theorem segsOf_ex (c : ℕ) : (segsOf σ K).ex c = (K c).ex := rfl
theorem segsOf_es (c : ℕ) : (segsOf σ K).es c = (K c).es := rfl
theorem segsOf_mx (c : ℕ) : (segsOf σ K).mx c = (K c).mx := rfl
theorem segsOf_ms (c : ℕ) : (segsOf σ K).ms c = (K c).ms := rfl

/-- The region sizes. -/
noncomputable abbrev LXS (σ : Val) : ℕ := lg σ 0 + lg σ 1
noncomputable abbrev LSS (σ : Val) : ℕ := lg σ 3 + lg σ 4

theorem a_le (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) :
    ∀ c ≤ lg σ 6, (segsOf σ K).a c ≤ 131070 + c * 131070 := by
  intro c
  induction c with
  | zero =>
    intro _
    have h2 := (MF.counts 2 (by simp)).2
    have h5 := (MF.counts 5 (by simp)).2
    rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]
    omega
  | succ c ih =>
    intro hc
    have := ih (by omega)
    obtain ⟨b1, b2⟩ := (hK c (by omega)).bounds
    rw [Segs.a.eq_2, segsOf_ex, segsOf_es]
    nlinarith

/-- **The running counts**: `written[c] = g^(a c)`. -/
theorem written_eq (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) :
    ∀ c ≤ lg σ 6, LoadHolds rd (σ (.n 420)) c (gen ^ (segsOf σ K).a c) := by
  intro c
  induction c with
  | zero => intro _; rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]; exact MF.written0
  | succ c ih =>
    intro hc
    have hk := hK c (by omega)
    have hb := loadHolds_unique hk.base (ih (by omega))
    have := hk.next
    rw [hb, ← pow_add, ← pow_add] at this
    rw [Segs.a.eq_2, segsOf_ex, segsOf_es]
    exact this

/-- `SlotBelow` against a known power: the slot is below. -/
theorem slotBelow_lt {b : E} {e M : ℕ} (hM : M < 2 ^ 34) (hb : b = gen ^ M) (h : SlotBelow b e) :
    e < M := by
  obtain ⟨L, hL, hbL, he⟩ := h
  have := gen_pow_inj34 (by omega) (by omega) (hb.symm.trans hbL)
  omega

/-- **The raw signatures' slots**: one slot of its region per raw signature, holding its mark. -/
theorem raw_slots (MF : MainFacts C rd σ) :
    ∃ rx rs : ℕ → ℕ, (∀ i < lg σ 2, rx i < LXS σ ∧ LoadHolds rd (σ (.n 66)) (rx i) (gen ^ i)) ∧
      ∀ j < lg σ 5, rs j < LSS σ ∧
        LoadHolds rd (σ (.n 66)) (LXS σ + rs j) (gen ^ (lg σ 2 + j)) := by
  have hT := MF.total
  have h40 := MF.lxs
  have h41 := MF.lss
  have hc2 := (MF.counts 2 (by simp)).1
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  have hx : ∀ i, i < lg σ 2 → ∃ s, s < LXS σ ∧ LoadHolds rd (σ (.n 66)) s (gen ^ i) := by
    intro i hi
    obtain ⟨-, s, hbl, hl⟩ := MF.rawx i hi
    exact ⟨s, belowLog_lt (by omega) h40 hbl, hl⟩
  have hs : ∀ j, j < lg σ 5 → ∃ s, s < LSS σ ∧
      LoadHolds rd (σ (.n 66)) (LXS σ + s) (gen ^ (lg σ 2 + j)) := by
    intro j hj
    obtain ⟨s, hbl, hl, -⟩ := MF.raws j hj
    refine ⟨s, belowLog_lt (by omega) h41 hbl, ?_⟩
    rw [h40, hc2, ← pow_add, ← pow_add, loadHolds_gen_pow_iff, Nat.add_zero] at hl
    exact hl
  choose! rx hrx using hx
  choose! rs hrs using hs
  exact ⟨rx, rs, hrx, hrs⟩

/-- **The writers' slots**: raw signatures' at `rx`, `LXS + rs`; child `c`'s leanXMSS claim `j` at
its slot `ox j`, its leanSPHINCS claim `j` at `LXS + os j`. -/
noncomputable def slOf (σ : Val) (K : ℕ → KidRec) (rx rs : ℕ → ℕ) (m : ℕ) : ℕ :=
  if m < lg σ 2 then rx m else if m < lg σ 2 + lg σ 5 then LXS σ + rs (m - lg σ 2) else
  if m - (segsOf σ K).a ((segsOf σ K).kid m) < (K ((segsOf σ K).kid m)).ex then
    (K ((segsOf σ K).kid m)).ox (m - (segsOf σ K).a ((segsOf σ K).kid m))
  else LXS σ + (K ((segsOf σ K).kid m)).os
    (m - (segsOf σ K).a ((segsOf σ K).kid m) - (K ((segsOf σ K).kid m)).ex)

section Slots

variable {rx rs : ℕ → ℕ}

theorem slOf_rx {m : ℕ} (h : m < lg σ 2) : slOf σ K rx rs m = rx m := by
  unfold slOf; rw [ite_pos' h]

theorem slOf_rs {m : ℕ} (h1 : lg σ 2 ≤ m) (h2 : m < lg σ 2 + lg σ 5) :
    slOf σ K rx rs m = LXS σ + rs (m - lg σ 2) := by
  unfold slOf; rw [ite_neg' (by omega), ite_pos' h2]

/-- Child `c`'s leanXMSS claim `j`'s slot. -/
theorem slOf_x {c j : ℕ} (hc : c < lg σ 6) (hj : j < (K c).ex) :
    slOf σ K rx rs ((segsOf σ K).a c + j) = (K c).ox j := by
  have h0 := (segsOf σ K).a0_le c
  rw [segsOf_RX, segsOf_RS] at h0
  have hk := (segsOf σ K).kid_eq (m := (segsOf σ K).a c + j) (by rw [segsOf_NC]; exact hc)
    (by omega) (by rw [Segs.a_succ, segsOf_ex, segsOf_es]; omega)
  unfold slOf
  rw [ite_neg' (by omega), ite_neg' (by omega), hk, ite_pos' (by omega), Nat.add_sub_cancel_left]

/-- Child `c`'s leanSPHINCS claim `j`'s slot. -/
theorem slOf_s {c j : ℕ} (hc : c < lg σ 6) (hj : j < (K c).es) :
    slOf σ K rx rs ((segsOf σ K).a c + (K c).ex + j) = LXS σ + (K c).os j := by
  have h0 := (segsOf σ K).a0_le c
  rw [segsOf_RX, segsOf_RS] at h0
  have hk := (segsOf σ K).kid_eq (m := (segsOf σ K).a c + (K c).ex + j)
    (by rw [segsOf_NC]; exact hc) (by omega)
    (by rw [Segs.a_succ, segsOf_ex, segsOf_es]; omega)
  unfold slOf
  rw [ite_neg' (by omega), ite_neg' (by omega), hk, ite_neg' (by omega)]
  congr 2; omega

end Slots

/-- A child's base is the running count before it. -/
theorem kid_base (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c : ℕ}
    (hc : c < lg σ 6) : (K c).base = gen ^ (segsOf σ K).a c :=
  loadHolds_unique (hK c hc).base (written_eq MF hK c (by omega))

/-- **Child `c`'s leanXMSS claim `j`**: its slot below `LXS`, holding its writer's mark. -/
theorem kid_wx (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c j : ℕ}
    (hc : c < lg σ 6) (hj : j < (K c).ex) :
    (K c).ox j < LXS σ ∧ LoadHolds rd (σ (.n 66)) ((K c).ox j)
      (gen ^ (segsOf σ K).wmark ((segsOf σ K).a c + j)) := by
  have hT := MF.total.2
  obtain ⟨hbl, hl, -⟩ := (hK c hc).xrec j hj
  refine ⟨slotBelow_lt (by unfold LXS; omega) MF.lxs hbl, ?_⟩
  rw [(segsOf σ K).wmark_x (by rw [segsOf_NC]; exact hc) (by omega) (by rw [segsOf_ex]; omega),
    segsOf_mx]
  rw [kid_base MF hK hc, ← pow_add] at hl
  cases hm : (K c).mx <;> simp only [hm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hl ⊢ <;>
    exact hl

/-- **Child `c`'s leanSPHINCS claim `j`**: its slot below `LSS` past `LXS`, holding its writer's
mark. -/
theorem kid_ws (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c j : ℕ}
    (hc : c < lg σ 6) (hj : j < (K c).es) :
    (K c).os j < LSS σ ∧ LoadHolds rd (σ (.n 66)) (LXS σ + (K c).os j)
      (gen ^ (segsOf σ K).wmark ((segsOf σ K).a c + (K c).ex + j)) := by
  have hT := MF.total.2
  obtain ⟨hbl, hl, -⟩ := (hK c hc).srec j hj
  refine ⟨slotBelow_lt (by unfold LSS; omega) MF.lss hbl, ?_⟩
  rw [(segsOf σ K).wmark_s (by rw [segsOf_NC]; exact hc) (by rw [segsOf_ex]; omega)
    (by rw [Segs.a_succ, segsOf_ex, segsOf_es]; omega), segsOf_ms, segsOf_ex]
  rw [MF.spcov, MF.lxs, kid_base MF hK hc, ← pow_add, ← pow_add, loadHolds_gen_pow_iff] at hl
  cases hm : (K c).ms <;> simp only [hm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hl ⊢ <;>
    exact hl

set_option maxRecDepth 20000 in
/-- **The writers of the coverage table.** -/
theorem writers (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {rx rs : ℕ → ℕ}
    (hrx : ∀ i < lg σ 2, rx i < LXS σ ∧ LoadHolds rd (σ (.n 66)) (rx i) (gen ^ i))
    (hrs : ∀ j < lg σ 5, rs j < LSS σ ∧
      LoadHolds rd (σ (.n 66)) (LXS σ + rs j) (gen ^ (lg σ 2 + j))) :
    Writers rd (σ (.n 66)) (segsOf σ K) (LXS σ) (LSS σ) (slOf σ K rx rs) := by
  have hT := MF.total
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  have hw := written_eq MF hK
  have htot : (segsOf σ K).a (segsOf σ K).NC = LXS σ + LSS σ := by
    rw [segsOf_NC]
    have h1 := hw (lg σ 6) le_rfl
    have h2 := MF.writtenN
    rw [hT.1] at h2
    have := loadHolds_unique h1 h2
    have hb := a_le MF hK (lg σ 6) le_rfl
    have hk6 := MF.kids.2
    exact gen_pow_inj34 (by omega) (by omega) this
  set S := segsOf σ K with hS
  have hRX : S.RX = lg σ 2 := rfl
  have hRS : S.RS = lg σ 5 := rfl
  -- every writer: raw leanXMSS, raw leanSPHINCS, a child's leanXMSS or leanSPHINCS claim
  have cases_m : ∀ m < LXS σ + LSS σ, m < lg σ 2 ∨ (lg σ 2 ≤ m ∧ m < lg σ 2 + lg σ 5) ∨
      ∃ c < lg σ 6, (∃ j < (K c).ex, m = S.a c + j) ∨
        ∃ j < (K c).es, m = S.a c + (K c).ex + j := by
    intro m hm
    by_cases h1 : m < lg σ 2
    · exact Or.inl h1
    by_cases h2 : m < lg σ 2 + lg σ 5
    · exact Or.inr (Or.inl ⟨by omega, h2⟩)
    obtain ⟨hc, hc1, hc2⟩ := S.kid_spec (m := m) (by simp [Segs.a, hRX, hRS]; omega)
      (by rw [htot]; exact hm)
    rw [Segs.a_succ, hS, segsOf_ex, segsOf_es, segsOf_NC] at *
    refine Or.inr (Or.inr ⟨_, hc, ?_⟩)
    by_cases hx : m - (segsOf σ K).a ((segsOf σ K).kid m) < (K ((segsOf σ K).kid m)).ex
    · exact Or.inl ⟨_, hx, by omega⟩
    · exact Or.inr ⟨m - (segsOf σ K).a ((segsOf σ K).kid m) - (K ((segsOf σ K).kid m)).ex,
        by omega, by omega⟩
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m₁ m₂ h12 hm₂ heq => ?_, htot, by omega⟩
  · -- the marks
    rcases cases_m m hm with h | ⟨h1, h2⟩ | ⟨c, hc, ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩⟩
    · rw [slOf_rx h, S.wmark_raw (by rw [hRX, hRS]; omega)]; exact (hrx m h).2
    · rw [slOf_rs h1 h2, S.wmark_raw (by rw [hRX, hRS]; omega)]
      have := (hrs (m - lg σ 2) (by omega)).2
      rwa [show lg σ 2 + (m - lg σ 2) = m by omega] at this
    · rw [slOf_x hc hj]; exact (kid_wx MF hK hc hj).2
    · rw [slOf_s hc hj]; exact (kid_ws MF hK hc hj).2
  · -- the regions
    rcases cases_m m hm with h | ⟨h1, h2⟩ | ⟨c, hc, ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩⟩
    · have hr : S.region m = 0 := by unfold Segs.region; rw [hRX, ite_pos' h]
      rw [hr, slOf_rx h]
      exact ⟨fun _ => (hrx m h).1, fun h => absurd h (by decide)⟩
    · have hr : S.region m = 1 := by
        unfold Segs.region; rw [hRX, hRS, ite_neg' (by omega), ite_pos' h2]
      rw [hr, slOf_rs h1 h2]
      have := (hrs (m - lg σ 2) (by omega)).1
      exact ⟨fun h => absurd h (by decide), fun _ => ⟨by omega, by omega⟩⟩
    · have h0 := S.a0_le c
      rw [hRX, hRS] at h0
      have hk := S.kid_eq (m := S.a c + j) (by rw [hS, segsOf_NC]; exact hc) (by omega)
        (by rw [Segs.a_succ, hS, segsOf_ex, segsOf_es]; omega)
      have hr : S.region (S.a c + j) = 0 := by
        unfold Segs.region
        rw [hRX, hRS, ite_neg' (by omega), ite_neg' (by omega), hk, hS, segsOf_ex,
          ite_pos' (by omega)]
      rw [hr, slOf_x hc hj]
      exact ⟨fun _ => (kid_wx MF hK hc hj).1, fun h => absurd h (by decide)⟩
    · have h0 := S.a0_le c
      rw [hRX, hRS] at h0
      have hk := S.kid_eq (m := S.a c + (K c).ex + j) (by rw [hS, segsOf_NC]; exact hc)
        (by omega) (by rw [Segs.a_succ, hS, segsOf_ex, segsOf_es]; omega)
      have hr : S.region (S.a c + (K c).ex + j) = 1 := by
        unfold Segs.region
        rw [hRX, hRS, ite_neg' (by omega), ite_neg' (by omega), hk, hS, segsOf_ex,
          ite_neg' (by omega)]
      rw [hr, slOf_s hc hj]
      have := (kid_ws MF hK hc hj).1
      exact ⟨fun h => absurd h (by decide), fun _ => ⟨by omega, by omega⟩⟩
  · -- one mark, a gap-walked list: increasing slots
    have hle1 := (S.wmark_range (m := m₁) (by rw [htot]; omega)).1
    rcases cases_m m₂ hm₂ with h | ⟨h1, h2⟩ | ⟨c, hc, ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩⟩
    · rw [S.wmark_raw (m := m₂) (by rw [hRX, hRS]; omega)] at heq; omega
    · rw [S.wmark_raw (m := m₂) (by rw [hRX, hRS]; omega)] at heq; omega
    · have hcN : c < S.NC := by rw [hS, segsOf_NC]; exact hc
      have hex : S.ex c = (K c).ex := rfl
      have hmx : S.mx c = (K c).mx := rfl
      rw [S.wmark_x (m := S.a c + j) hcN (by omega) (by rw [hex]; omega), hmx] at heq
      cases hm : (K c).mx
      · rw [hm] at heq; simp only [Bool.false_eq_true, ↓reduceIte] at heq; omega
      · rw [hm] at heq; simp only [↓reduceIte] at heq
        obtain ⟨i, rfl⟩ : ∃ i, m₁ = S.a c + i := ⟨m₁ - S.a c, by omega⟩
        rw [slOf_x hc (by omega), slOf_x hc hj]
        exact (hK c hc).xmono hm i j (by omega) hj
    · have hcN : c < S.NC := by rw [hS, segsOf_NC]; exact hc
      have hex : S.ex c = (K c).ex := rfl
      have hes : S.es c = (K c).es := rfl
      have hms : S.ms c = (K c).ms := rfl
      rw [S.wmark_s (m := S.a c + (K c).ex + j) hcN (by rw [hex]; omega)
        (by rw [Segs.a_succ, hex, hes]; omega), hms, hex] at heq
      cases hm : (K c).ms
      · rw [hm] at heq; simp only [Bool.false_eq_true, ↓reduceIte] at heq; omega
      · rw [hm] at heq; simp only [↓reduceIte] at heq
        obtain ⟨i, rfl⟩ : ∃ i, m₁ = S.a c + (K c).ex + i := ⟨m₁ - S.a c - (K c).ex, by omega⟩
        rw [slOf_s hc (by omega), slOf_s hc hj]
        have := (hK c hc).smono hm i j (by omega) hj
        omega

end
end LeanVM.Guest.B1.Main
