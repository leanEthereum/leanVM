/-
  LeanVM.Guest.B1.Terminal.ClaimsComplete

  The claims' blocks of `check_opening_terminal`, completely: on an evaluated valuation whose loads
  read their words and whose length checks agree, every statement holds and every load lies in a
  given region.
-/

module

public import LeanVM.Guest.B1.Terminal.TermFacts
public import LeanVM.Guest.B1.Ring.Loop14Complete

/-!
# The claims' blocks, completely

The completeness counterpart of `Terminal/Blocks`: on a valuation satisfying the blocks' defining
equations (`GoodS`, the evaluator's), whose stores are the public input's chain's only
(`StoresAtPi`), a block holds once its loads read words (`LoadHolds`); its loads lie in a region
`R` when their addresses do (`AddrIn`). `kapT_complete`: a low length's `g`-power;
`zrT_complete`, `qT_complete`, `pT_complete`: the three kinds of block; `claimsT_complete`: all
of them.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The word at `P·g^k` lies in the region `R`. -/
def AddrIn (R : ℕ → Prop) (P : E) (k : ℕ) : Prop := ∃ i, P.limb 0 * addressOfIndex k =
    addressOfIndex i ∧ R i

/-- The stores load through `.n 26`, the public input's chain. -/
def StoresAtPi (S : List Atom) : Prop := ∀ a ∈ S, ∃ d off, a = .load d (.n 26) off

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {R : ℕ → Prop}

theorem good_load (hS : StoresAtPi S) {d p : V} {off : ℕ} (hp : p ≠ .n 26)
    (h : GoodS rd S w σ (.atom (.load d p off))) : σ d = rdAt rd (σ p) off := by
  simp only [GoodS, Good] at h
  rcases h with h | h
  · obtain ⟨d', off', he⟩ := hS _ h
    simp only [Atom.load.injEq] at he
    exact absurd he.2.1 hp
  · exact h

theorem good_load_eq (hS : StoresAtPi S) {d p : V} {off : ℕ} (hp : p ≠ .n 26) {v : E}
    (h : GoodS rd S w σ (.atom (.load d p off))) (hl : LoadHolds rd (σ p) off v) :
    σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have e := (good_load hS hp h).trans (rt_rdAt_of_load hl)
  refine ⟨e, ?_⟩
  show LoadHolds rd (σ p) off (σ d)
  rw [e]; exact hl

theorem goodS_mul {d x y : ℕ} (h : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y))))
    (hx : x < d) (hy : y < d) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [GoodS, Good] at h
  rwa [ite_pos' (show (Core.V.n x).idx < (Core.V.n d).idx ∧ (Core.V.n y).idx < (Core.V.n d).idx from
    ⟨hx, hy⟩)] at h

theorem good_add {d x y : ℕ} (h : GoodS rd S w σ (.atom (.add (.n d) (.n x) (.n y)))) :
    σ (.n d) = σ (.n x) + σ (.n y) := h

theorem good_const {d : ℕ} {e : E} (h : GoodS rd S w σ (.atom (.const (.n d) e))) :
    σ (.n d) = e := h

theorem n_ne_26 {k : ℕ} (h : k ≠ 26) : (Core.V.n k) ≠ .n 26 := fun e => h (by injection e)

/-! ## The blocks -/

/-- **A low length's `g`-power, completely**: `kb[src]·g^adj`, no load. -/
theorem kapT_complete {src adj r : ℕ} (hsrc : src < 8) (hadj : adj < 64) (hr : 42 < r)
    (hg : ∀ s ∈ (kapT src adj r).1, GoodS rd S w σ s) :
    (∀ s ∈ (kapT src adj r).1, Fwd.SHolds C rd σ s) ∧
      (kapT src adj r).1.filterMap Stmt.loadS = [] ∧
      σ (.n (kapT src adj r).2.1) = σ (.n (kbV src)) * gen ^ adj ∧
      (kapT src adj r).2.1 < (kapT src adj r).2.2 ∧ r ≤ (kapT src adj r).2.2 := by
  unfold kapT at hg ⊢
  by_cases h0 : adj = 0
  · subst h0
    simp only [↓reduceIte, List.not_mem_nil, false_imp_iff, imp_true_iff, List.filterMap_nil,
      pow_zero, mul_one, true_and, le_refl, and_true] at hg ⊢
    simp only [kbV]; omega
  · simp only [h0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hg ⊢
    obtain ⟨g0, g1⟩ := hg
    have e0 := good_const g0
    have e1 := goodS_mul g1 (by simp only [kbV]; omega) (by omega)
    refine ⟨⟨e0, e1⟩, rfl, by rw [e1, e0, word_two_pow hadj], by omega, by omega⟩

/-- **A claim on a prefix chain, completely.** -/
theorem zrT_complete (hS : StoresAtPi S) {ch kr sel lr r acc n : ℕ} (hch' : ch < r) (hkr : kr < r)
    (hsel : sel < r) (hlr : lr < r) (hr : 26 < r) (hg : ∀ s ∈ zrT ch kr sel lr r acc, GoodS rd S w σ s)
    (ekr : σ (.n kr) = gen ^ n)
    (hch : ∃ v, LoadHolds rd (σ (.n ch) * gen ^ n) 0 v) (ach : AddrIn R (σ (.n ch) * gen ^ n) 0) :
    (∀ s ∈ zrT ch kr sel lr r acc, Fwd.SHolds C rd σ s) ∧
      ∀ q ∈ (zrT ch kr sel lr r acc).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2 := by
  have m : ∀ s, s ∈ zrT ch kr sel lr r acc → GoodS rd S w σ s := hg
  simp only [zrT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at m
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := m
  obtain ⟨CH, hch⟩ := hch
  have e0 := goodS_mul g0 hch' hkr
  rw [ekr] at e0
  rw [← e0] at hch ach
  obtain ⟨-, l1⟩ := good_load_eq hS (n_ne_26 (by omega)) g1 hch
  refine ⟨fun s hs => ?_, fun q hq => ?_⟩
  · simp only [zrT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (by rw [e0, ekr] : σ (.n r) = σ (.n ch) * σ (.n kr))
    · exact l1
    · exact goodS_mul g2 (by omega) (by omega)
    · exact goodS_mul g3 (by omega) (by omega)
    · exact good_add g4
    · exact goodS_mul g5 (by omega) (by omega)
  · simp only [zrT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    subst hq
    exact ach

/-- **A `q_keccak` lane's claim, completely.** -/
theorem qT_complete (hS : StoresAtPi S) {s kr lr r acc n : ℕ} (hsel : selV 4 < r) (hkr : kr < r)
    (hlr : lr < r) (hr : 26 < r) (hg : ∀ t ∈ qT s kr lr r acc, GoodS rd S w σ t)
    (ekr : σ (.n kr) = gen ^ n)
    (hslot : ∀ k < 6, ∀ t, (t = 24 ∨ t = 25) →
      (∃ v, LoadHolds rd (σ (.n t)) k v) ∧ AddrIn R (σ (.n t)) k)
    (hch : ∃ v, LoadHolds rd (σ (.n 22) * gen ^ n) 0 v) (ach : AddrIn R (σ (.n 22) * gen ^ n) 0) :
    (∀ t ∈ qT s kr lr r acc, Fwd.SHolds C rd σ t) ∧
      ∀ q ∈ (qT s kr lr r acc).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2 := by
  have m : ∀ t, t ∈ qT s kr lr r acc → GoodS rd S w σ t := hg
  simp only [qT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at m
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩ := m
  obtain ⟨CH, hch⟩ := hch
  have hsp : ∀ k < 6, slotPt s k = 24 ∨ slotPt s k = 25 := fun k _ => by
    unfold slotPt; split <;> simp
  have ls : ∀ k < 6, ∀ d, GoodS rd S w σ (.atom (.load (.n d) (.n (slotPt s k)) k)) →
      (Atom.load (.n d) (.n (slotPt s k)) k).Holds rd σ := fun k hk d g => by
    obtain ⟨v, hv⟩ := (hslot k hk _ (hsp k hk)).1
    exact (good_load_eq hS (n_ne_26 (by rcases hsp k hk with h | h <;> rw [h] <;> decide)) g hv).2
  have e11 := goodS_mul g11 (by omega) (by omega)
  rw [ekr] at e11
  rw [← e11] at hch ach
  obtain ⟨-, l12⟩ := good_load_eq hS (n_ne_26 (by omega)) g12 hch
  refine ⟨fun t ht => ?_, fun q hq => ?_⟩
  · simp only [qT, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact ls 5 (by decide) _ g0
    · exact ls 4 (by decide) _ g1
    · exact goodS_mul g2 (by omega) (by omega)
    · exact ls 3 (by decide) _ g3
    · exact goodS_mul g4 (by omega) (by omega)
    · exact ls 2 (by decide) _ g5
    · exact goodS_mul g6 (by omega) (by omega)
    · exact ls 1 (by decide) _ g7
    · exact goodS_mul g8 (by omega) (by omega)
    · exact ls 0 (by decide) _ g9
    · exact goodS_mul g10 (by omega) (by omega)
    · exact (by rw [e11, ekr] : σ (.n (r + 11)) = σ (.n 22) * σ (.n kr))
    · exact l12
    · exact goodS_mul g13 (by omega) (by omega)
    · exact goodS_mul g14 (by omega) (by omega)
    · exact goodS_mul g15 (by omega) (by omega)
    · exact good_add g16
    · exact goodS_mul g17 (by omega) (by omega)
  · simp only [qT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hslot 5 (by decide) _ (hsp 5 (by decide))).2
    · exact (hslot 4 (by decide) _ (hsp 4 (by decide))).2
    · exact (hslot 3 (by decide) _ (hsp 3 (by decide))).2
    · exact (hslot 2 (by decide) _ (hsp 2 (by decide))).2
    · exact (hslot 1 (by decide) _ (hsp 1 (by decide))).2
    · exact (hslot 0 (by decide) _ (hsp 0 (by decide))).2
    · exact ach

/-- **A public input's claim, completely**: no load. -/
theorem pT_complete {sel lr r acc : ℕ} (hsel : sel < r) (hlr : lr < r) (hr : 34 < r)
    (hg : ∀ t ∈ pT sel lr r acc, GoodS rd S w σ t) :
    (∀ t ∈ pT sel lr r acc, Fwd.SHolds C rd σ t) ∧
      ∀ q ∈ (pT sel lr r acc).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2 := by
  have m : ∀ t, t ∈ pT sel lr r acc → GoodS rd S w σ t := hg
  simp only [pT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at m
  obtain ⟨g0, g1, g2, g3⟩ := m
  refine ⟨fun t ht => ?_, fun q hq => ?_⟩
  · simp only [pT, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact goodS_mul g0 (by omega) (by omega)
    · exact goodS_mul g1 (by omega) (by omega)
    · exact good_add g2
    · exact goodS_mul g3 (by omega) (by omega)
  · simp [pT, Stmt.loadS] at hq

/-! ## All the claims -/

/-- What claim `j`'s block needs of the memory, the base's exponents `e`: its chain's word at its
low length `cLow e j`, its address in `R`. -/
def ClaimIn (rd : Reader) (σ : Val) (R : ℕ → Prop) (e : ℕ → ℕ) (j : ℕ) : Prop :=
  match termKind j with
  | 0 => (∃ v, LoadHolds rd (σ (.n 20) * gen ^ cLow e j) 0 v) ∧
      AddrIn R (σ (.n 20) * gen ^ cLow e j) 0
  | 1 | 3 => (∃ v, LoadHolds rd (σ (.n 22) * gen ^ cLow e j) 0 v) ∧
      AddrIn R (σ (.n 22) * gen ^ cLow e j) 0
  | _ => True

theorem termCol_lt_all : ∀ j < 159, termCol j < Tables.nCommittedCols := by decide +kernel

theorem termCol_lt {j : ℕ} (hj : j < 159) : termCol j < Tables.nCommittedCols := termCol_lt_all j hj

theorem selV_lt_all : ∀ c < Tables.nCommittedCols, selV c < claimsStart := by decide +kernel

theorem selV_lt {c : ℕ} (hc : c < Tables.nCommittedCols) : selV c < claimsStart := selV_lt_all c hc

/-- **The claims' blocks, completely.** -/
theorem claimsT_complete (hS : StoresAtPi S) {e : ℕ → ℕ}
    (he : ∀ i < 8, σ (.n (kbV i)) = gen ^ e i)
    (hslot : ∀ k < 6, ∀ t, (t = 24 ∨ t = 25) →
      (∃ v, LoadHolds rd (σ (.n t)) k v) ∧ AddrIn R (σ (.n t)) k) :
    ∀ (js : List ℕ) (r acc lr : ℕ), claimsStart ≤ r → acc < r → lr < r → (∀ j ∈ js, j < 159) →
      (∀ j ∈ js, ClaimIn rd σ R e j) →
      (∀ s ∈ (claimsT js r acc lr).1, GoodS rd S w σ s) →
      (∀ s ∈ (claimsT js r acc lr).1, Fwd.SHolds C rd σ s) ∧
        ∀ q ∈ (claimsT js r acc lr).1.filterMap Stmt.loadS, AddrIn R (σ q.1) q.2
  | [], _, _, _, _, _, _, _, _, _ =>
    ⟨fun s hs => by simp [claimsT] at hs, fun q hq => by simp [claimsT] at hq⟩
  | j :: js, r, acc, lr, hr, hacc, hlr, hjs, hin, hg => by
    have hj := hjs j List.mem_cons_self
    have hjs' : ∀ j' ∈ js, j' < 159 := fun j' h => hjs j' (List.mem_cons_of_mem _ h)
    have hin' : ∀ j' ∈ js, ClaimIn rd σ R e j' := fun j' h => hin j' (List.mem_cons_of_mem _ h)
    have hij := hin j List.mem_cons_self
    have hsel : selV (termCol j) < r := lt_of_lt_of_le (selV_lt (termCol_lt hj)) hr
    have hsel4 : selV 4 < r := lt_of_lt_of_le (selV_lt (by decide)) hr
    simp only [claimsT, List.mem_append, List.filterMap_append] at hg ⊢
    have hg1 : ∀ s ∈ (claimT j r acc lr).1, GoodS rd S w σ s := fun s h => hg s (Or.inl h)
    have hg2 := fun s h => hg s (Or.inr h)
    unfold claimT at hg1 hg2 ⊢
    simp only [claimKap] at hg1 hg2 ⊢
    -- the low length's power
    have hkap := fun (hgk : ∀ s ∈ (kapT (claimKappaSrc j) (claimKappaAdj j) r).1,
        GoodS rd S w σ s) =>
      kapT_complete (C := C) (claimKappaSrc_lt j) (claimKappaAdj_lt j)
        (show 42 < r by simp only [claimsStart] at hr; omega) hgk
    have ekr : ∀ (hgk : ∀ s ∈ (kapT (claimKappaSrc j) (claimKappaAdj j) r).1, GoodS rd S w σ s),
        σ (.n (kapT (claimKappaSrc j) (claimKappaAdj j) r).2.1) = gen ^ cLow e j := fun hgk => by
      rw [(hkap hgk).2.2.1, he _ (claimKappaSrc_lt j), ← pow_add]; rfl
    unfold ClaimIn at hij
    rcases hk : termKind j with _ | _ | _ | _ | k
    all_goals simp only [hk] at hg1 hg2 hij ⊢
    · simp only [List.mem_append] at hg1 ⊢
      have hgk := fun s h => hg1 s (Or.inl h)
      obtain ⟨k1, k2, -, k3, k4⟩ := hkap hgk
      have k5 : r ≤ (claimKap j r).2.2 := k4
      obtain ⟨b1, b2⟩ := zrT_complete (C := C) (R := R) hS (show 20 < (claimKap j r).2.2 by
          simp only [claimsStart] at hr; omega) k3 (by omega) (by omega) (by
          simp only [claimsStart] at hr; omega) (fun s h => hg1 s (Or.inr h)) (ekr hgk) hij.1 hij.2
      obtain ⟨c1, c2⟩ := claimsT_complete hS he hslot js _ _ _ (by omega) (by omega) (by omega)
        hjs' hin' hg2
      refine ⟨fun s h => ?_, fun q h => ?_⟩
      · rcases h with (h | h) | h
        · exact k1 s h
        · exact b1 s h
        · exact c1 s h
      · rw [List.filterMap_append, k2, List.nil_append] at h
        rcases h with h | h
        · exact b2 q h
        · exact c2 q h
    · simp only [List.mem_append] at hg1 ⊢
      have hgk := fun s h => hg1 s (Or.inl h)
      obtain ⟨k1, k2, -, k3, k4⟩ := hkap hgk
      have k5 : r ≤ (claimKap j r).2.2 := k4
      obtain ⟨b1, b2⟩ := zrT_complete (C := C) (R := R) hS (show 22 < (claimKap j r).2.2 by
          simp only [claimsStart] at hr; omega) k3 (by omega) (by omega) (by
          simp only [claimsStart] at hr; omega) (fun s h => hg1 s (Or.inr h)) (ekr hgk) hij.1 hij.2
      obtain ⟨c1, c2⟩ := claimsT_complete hS he hslot js _ _ _ (by omega) (by omega) (by omega)
        hjs' hin' hg2
      refine ⟨fun s h => ?_, fun q h => ?_⟩
      · rcases h with (h | h) | h
        · exact k1 s h
        · exact b1 s h
        · exact c1 s h
      · rw [List.filterMap_append, k2, List.nil_append] at h
        rcases h with h | h
        · exact b2 q h
        · exact c2 q h
    · obtain ⟨b1, b2⟩ := pT_complete (C := C) (R := R) hsel hlr (by
          simp only [claimsStart] at hr; omega) hg1
      obtain ⟨c1, c2⟩ := claimsT_complete hS he hslot js _ _ _ (by omega) (by omega) (by omega)
        hjs' hin' hg2
      exact ⟨fun s h => h.elim (b1 s) (c1 s), fun q h => h.elim (b2 q) (c2 q)⟩
    · simp only [List.mem_append] at hg1 ⊢
      have hgk := fun s h => hg1 s (Or.inl h)
      obtain ⟨k1, k2, -, k3, k4⟩ := hkap hgk
      have k5 : r ≤ (claimKap j r).2.2 := k4
      obtain ⟨b1, b2⟩ := qT_complete (C := C) (R := R) hS (by omega) k3 (by omega) (by
          simp only [claimsStart] at hr; omega) (fun s h => hg1 s (Or.inr h)) (ekr hgk) hslot
          hij.1 hij.2
      obtain ⟨c1, c2⟩ := claimsT_complete hS he hslot js _ _ _ (by omega) (by omega) (by omega)
        hjs' hin' hg2
      refine ⟨fun s h => ?_, fun q h => ?_⟩
      · rcases h with (h | h) | h
        · exact k1 s h
        · exact b1 s h
        · exact c1 s h
      · rw [List.filterMap_append, k2, List.nil_append] at h
        rcases h with h | h
        · exact b2 q h
        · exact c2 q h
    · obtain ⟨c1, c2⟩ := claimsT_complete hS he hslot js _ _ _ hr hacc hlr hjs' hin' hg2
      exact ⟨fun s h => h.elim (fun h => by simp at h) (c1 s),
        fun q h => h.elim (fun h => by simp at h) (c2 q)⟩

end
end LeanVM.Guest.B1.VerifySub
