/-
  LeanVM.Guest.B1.Bits.QueryWindows

  B1 for `decode_query_windows`: a squeezed word's bits as query positions and their windows.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsLib

/-!
# `decode_query_windows` (lean_ethereum.py:798-909 at 40f877dc)

`decode_query_windows(word, positions, win_ptrs, tabs, d, cd)` (template `qwBody d cd`) hints the
squeezed word's bits in windows, each `g^n` range checked below `2^w` and read back through
`tabs`, and asserts that the positions' windows and the 7-bit windows above them rebuild the word.
On a memory of at most `2^32` words, with `tabs[g^n] = n` (`WinTabs`, the table `open_stacked`
writes), its meaning (`MeaningDecodeQueryWindows`): position `j` is the word's `d` bits from
`j·d` (one chunk of `sampleQueriesAux`, V:1670), stored at `positions[j]`, and its windows
(`qwWin`: the path six bits at a time from the bottom, the cap child bit, the cap parent index)
are `g^`(their bits) in the frame run `p` from `j·qwN`, the pointer `p·g^(j·qwN)` stored at
`win_ptrs[j]`.

The proof: each window's cell is `g^n` with `n` below its bound (`qw_rc`, the range check on a
memory of at most `2^32` words) and its pattern `n` (`qwRead_sound`, `qwSplit_sound`); a
position's runs are the windows' tiled sum split at the limb boundary (`qwSums`), its store and
reconstruction term the sum and its shift (`qwPr_sound`); the reconstruction is the tiled sum of
the positions and the rest windows (`tS`), so each digit is the word's (`tS_get`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- The window table: `tabs[g^n] = n` for `n < 128` (`win_tabs`, lean_ethereum.py:1475-1478). -/
def WinTabs (rd : Reader) (tabs : E) : Prop := ∀ n < 128, LoadHolds rd tabs n (eOfNat n)

/-- Position `j` of depth `d` of a word: its bits `j·d ..< (j + 1)·d`. -/
def qwPosOf (d : ℕ) (w : E) (j : ℕ) : ℕ := (eToNat w >>> (j * d)) % 2 ^ d

/-- **`decode_query_windows(word, positions, win_ptrs, tabs, d, cd)`**: for each position
`j < 192 / d`, `positions[j]` is position `j` of the word and `win_ptrs[j]` names a frame run
holding the position's windows `g^(qwVal)`. -/
def MeaningDecodeQueryWindows (d cd : ℕ) (rd : Reader) : List E → List E → Prop
  | [w, pos, ptrs, _], rets => rets = [] ∧ ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat (qwPosOf d w j)) ∧
      ∃ p : E, LoadHolds rd ptrs j p ∧ FrameRun rd p (qwN d cd) fun i ↦ gen ^ qwVal d cd (qwPosOf d w j) i
  | _, _ => False

/-- `decode_query_windows__L{d}_L{cd}`'s core IR establishes its meaning, on a memory image of
at most `2^32` words holding the window table at `tabs`. -/
def decode_query_windows_Spec (name : String) (d cd : ℕ) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ) (args rets : List E), WinTabs L.read (args.getD 3 0) →
    coreProgram.Rel L.read name args rets → MeaningDecodeQueryWindows d cd L.read args rets

/-- Every deployed specialization. -/
def decode_query_windows_all_Spec : Prop :=
  ∀ p ∈ queryWindowsShapes, decode_query_windows_Spec p.1 p.2.1 p.2.2

/-! ## The shapes -/

/-- Window `i`'s start, `d` past the last. -/
def qwOff (d cd i : ℕ) : ℕ := if i < qwN d cd then (qwWin d cd i).1 else d

/-- The tiles of the reconstruction: the positions, then the rest windows, `192` past them. -/
def qwTop (d t : ℕ) : ℕ := if t < 192 / d then t * d else min 192 (192 / d * d + 7 * (t - 192 / d))

/-- What the proof needs of a shape, decided for the deployed ones. -/
def QwShape (d cd : ℕ) : Prop :=
  12 ≤ d ∧ d ≤ 30 ∧ 192 / d * qwN d cd ≤ 56 ∧ qwOff d cd 0 = 0 ∧ qwN d cd ≤ 8 ∧
    (∀ i < qwN d cd, 1 ≤ (qwWin d cd i).2 ∧ (qwWin d cd i).2 ≤ 7 ∧
      qwOff d cd i + (qwWin d cd i).2 = qwOff d cd (i + 1) ∧
      (qwWin d cd i).1 + (qwWin d cd i).2 ≤ d) ∧
    (∀ r < qwRestN d, (qwRestWin d r).1 = qwTop d (192 / d + r) ∧
      (qwRestWin d r).1 + (qwRestWin d r).2 = qwTop d (192 / d + r + 1) ∧
      1 ≤ (qwRestWin d r).2 ∧ (qwRestWin d r).2 ≤ 7 ∧
      (qwRestWin d r).1 + (qwRestWin d r).2 ≤ 192 ∧
      (qwRestWin d r).1 % 64 + (qwRestWin d r).2 ≤ 64) ∧
    qwTop d (192 / d + qwRestN d) = 192

instance (d cd : ℕ) : Decidable (QwShape d cd) := by unfold QwShape; infer_instance

theorem qwShape_all : ∀ p ∈ queryWindowsShapes, QwShape p.2.1 p.2.2 := by decide

/-! ## Range checks and table reads -/

theorem qwBound_eq {w : ℕ} (hw : w ≤ 7) :
    qwBound w = ofK (Parameters.addressOfIndex (2 ^ w - 1)) := by
  have : 2 ^ w ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hw
  rw [qwBound, gpowK_eq (by unfold u128Bound; omega), ofK_eq_ofLimbs]

/-- A range check against `g^(K-1)` on a memory of at most `2^32` words: `x = g^e`, `e < K`. -/
theorem qw_rc {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {x y t1 t2 : E} {K : ℕ} (hK1 : 1 ≤ K)
    (hK : K ≤ 128) (h1 : LoadHolds L.read x 0 t1)
    (hk : ofK (Parameters.addressOfIndex (K - 1)) = x * y) (h3 : LoadHolds L.read y 0 t2) :
    ∃ e < K, x = gen ^ e := by
  have hκ64 : κ < 64 := by omega
  have h32 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
  obtain ⟨hx, h1⟩ := h1
  obtain ⟨hy, h2⟩ := h3
  rw [Parameters.addressOfIndex, pow_zero, mul_one] at h1 h2
  obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp h1
  obtain ⟨j, hj, -⟩ := (read_some_iff hκ64 L _ _).mp h2
  have ex : x = ofK (Parameters.addressOfIndex i) := by rw [eq_ofK_limb hx, hi]
  have ey : y = ofK (Parameters.addressOfIndex j) := by rw [eq_ofK_limb hy, hj]
  rw [ex, ey, ← ofK_mul, Parameters.addressOfIndex, Parameters.addressOfIndex,
    Parameters.addressOfIndex, ← pow_add] at hk
  have hij := gpow_injOn (by have := i.isLt; have := j.isLt; simp only [Set.mem_Iio]; omega)
    (by simp only [Set.mem_Iio]; omega) (ofK_injective hk).symm
  exact ⟨i, by omega, by rw [ex, gen_pow_eq_ofK]⟩

section reads

variable {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {σ : Val} (hT : WinTabs L.read (σ (.n 3)))
include hκ hT

theorem qwRead_sound {c : V} {start w k : ℕ} (hw : w ≤ 7)
    (h : qwAH L.read σ (qwRead c start w k).1) :
    ∃ n < 2 ^ w, σ c = gen ^ n ∧ σ (qwRead c start w k).2.2 = eOfNat n := by
  simp only [qwRead, qwAH_cons, qwAH_nil, Atom.Holds] at h ⊢
  obtain ⟨-, hk, ⟨r1, r2, r3⟩, hm, hl, -⟩ := h
  have h2w : 2 ^ w ≤ 128 := le_trans (Nat.pow_le_pow_right (n := 2) (by decide) hw) (by decide)
  obtain ⟨n, hn, hc⟩ := qw_rc hκ L (K := 2 ^ w) Nat.one_le_two_pow h2w r1
    (by rw [← qwBound_eq hw, ← hk, r2]) r3
  refine ⟨n, hn, hc, ?_⟩
  rw [hm, hc, loadHolds_mul_gen_pow, Nat.add_zero] at hl
  exact loadHolds_unique hl (hT n (by omega))

theorem qwSplit_sound {c : V} {start a w k : ℕ} (ha1 : 1 ≤ a) (ha : a < w) (hw : w ≤ 7)
    (h : qwAH L.read σ (qwSplit c start a w k).1) :
    ∃ n1 < 2 ^ a, ∃ n2 < 2 ^ (w - a), σ c = gen ^ (n1 + 2 ^ a * n2) ∧
      σ (qwSplit c start a w k).2.2.1 = eOfNat n1 ∧ σ (qwSplit c start a w k).2.2.2 = eOfNat n2 := by
  simp only [qwSplit, qwAH_append, qwAH_cons, qwAH_nil, Atom.Holds] at h ⊢
  obtain ⟨⟨⟨-, -, hk2, ⟨r1, r2, r3⟩, hk6, ⟨s1, s2, s3⟩, -⟩, hsq⟩, hc, hm1, hl1, hm2, hl2, -⟩ := h
  have hsv := qwSquares_val hsq
  have h2a : 2 ^ a ≤ 128 :=
    le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show a ≤ 7 by omega)) (by decide)
  have h2b : 2 ^ (w - a) ≤ 128 :=
    le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show w - a ≤ 7 by omega)) (by decide)
  obtain ⟨n1, hn1, hc1⟩ := qw_rc hκ L (K := 2 ^ a) Nat.one_le_two_pow h2a r1
    (by rw [← qwBound_eq (by omega), ← hk2, r2]) r3
  obtain ⟨n2, hn2, hc2⟩ := qw_rc hκ L (K := 2 ^ (w - a)) Nat.one_le_two_pow h2b s1
    (by rw [← qwBound_eq (by omega), ← hk6, s2]) s3
  refine ⟨n1, hn1, n2, hn2, ?_, ?_, ?_⟩
  · rw [hc, hsv, hc1, hc2, ← pow_mul, ← pow_add, Nat.mul_comm]
  · rw [hm1, hc1, loadHolds_mul_gen_pow, Nat.add_zero] at hl1
    exact loadHolds_unique hl1 (hT n1 (by omega))
  · rw [hm2, hc2, loadHolds_mul_gen_pow, Nat.add_zero] at hl2
    exact loadHolds_unique hl2 (hT n2 (by omega))

end reads

/-! ## A window -/

/-- A window's term in the position's low run (below the limb boundary `cut`). -/
def qwLoT (off w cut n : ℕ) : E :=
  if off + w ≤ cut then eOfNat n * cbWord off
  else if off < cut then eOfNat (n % 2 ^ (cut - off)) * cbWord off else 0

/-- A window's term in the position's high run. -/
def qwHiT (off w cut n : ℕ) : E :=
  if off + w ≤ cut then 0
  else if off < cut then eOfNat (n / 2 ^ (cut - off)) else eOfNat n * cbWord (off - cut)

theorem qwWindow_sound {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {σ : Val}
    (hT : WinTabs L.read (σ (.n 3))) {d cd base cut at0 i k : ℕ} {lo hi : Option V}
    (hw : (qwWin d cd i).2 ≤ 7)
    (h : qwAH L.read σ (qwWindow d cd base cut at0 i k lo hi).1) :
    ∃ n < 2 ^ (qwWin d cd i).2, σ (.n (5 + at0 + i)) = gen ^ n ∧
      qwOpt σ (qwWindow d cd base cut at0 i k lo hi).2.2.1 =
        qwOpt σ lo + qwLoT (qwWin d cd i).1 (qwWin d cd i).2 cut n ∧
      qwOpt σ (qwWindow d cd base cut at0 i k lo hi).2.2.2 =
        qwOpt σ hi + qwHiT (qwWin d cd i).1 (qwWin d cd i).2 cut n := by
  set off := (qwWin d cd i).1
  set w := (qwWin d cd i).2
  unfold qwWindow at h ⊢
  simp only at h ⊢
  by_cases h1 : off + w ≤ cut
  · rw [ite_pos' h1] at h ⊢
    simp only [qwAH_append] at h
    obtain ⟨⟨hr, hs⟩, ha⟩ := h
    obtain ⟨n, hn, hc, hv⟩ := qwRead_sound hκ L hT hw hr
    refine ⟨n, hn, hc, ?_, ?_⟩
    · rw [qwAcc_val ha, qwScale_val hs, hv, qwLoT, ite_pos' h1]
    · rw [qwHiT, ite_pos' h1, add_zero]
  · rw [ite_neg' h1] at h ⊢
    by_cases h2 : off < cut
    · rw [ite_pos' h2] at h ⊢
      simp only [qwAH_append] at h
      obtain ⟨⟨⟨hr, hs⟩, ha⟩, hb⟩ := h
      obtain ⟨n1, hn1, n2, hn2, hc, hv1, hv2⟩ :=
        qwSplit_sound hκ L hT (a := cut - off) (w := w) (by omega) (by omega) hw hr
      have hlt : n1 + 2 ^ (cut - off) * n2 < 2 ^ w := by
        have : 2 ^ w = 2 ^ (cut - off) * 2 ^ (w - (cut - off)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [this]
        calc n1 + 2 ^ (cut - off) * n2 < 2 ^ (cut - off) + 2 ^ (cut - off) * n2 := by omega
          _ = 2 ^ (cut - off) * (n2 + 1) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ hn2
      have hm : (n1 + 2 ^ (cut - off) * n2) % 2 ^ (cut - off) = n1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn1]
      have hd : (n1 + 2 ^ (cut - off) * n2) / 2 ^ (cut - off) = n2 := by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hn1, Nat.zero_add]
      refine ⟨_, hlt, hc, ?_, ?_⟩
      · rw [qwAcc_val ha, qwScale_val hs, hv1, qwLoT, ite_neg' h1, ite_pos' h2, hm]
      · rw [qwAcc_val hb, hv2, qwHiT, ite_neg' h1, ite_pos' h2, hd]
    · rw [ite_neg' h2] at h ⊢
      simp only [qwAH_append] at h
      obtain ⟨⟨hr, hs⟩, ha⟩ := h
      obtain ⟨n, hn, hc, hv⟩ := qwRead_sound hκ L hT hw hr
      refine ⟨n, hn, hc, ?_, ?_⟩
      · rw [qwLoT, ite_neg' h1, ite_neg' h2, add_zero]
      · rw [qwAcc_val ha, qwScale_val hs, hv, qwHiT, ite_neg' h1, ite_neg' h2]

theorem qwWindows_sound {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {σ : Val}
    (hT : WinTabs L.read (σ (.n 3))) {d cd base cut at0 : ℕ} :
    ∀ (i m k : ℕ) (lo hi : Option V),
      (∀ t < m, 1 ≤ (qwWin d cd (i + t)).2 ∧ (qwWin d cd (i + t)).2 ≤ 7) →
      qwAH L.read σ (qwWindows d cd base cut at0 i m k lo hi).1 →
      ∃ ns : ℕ → ℕ, (∀ t < m, ns t < 2 ^ (qwWin d cd (i + t)).2 ∧
          σ (.n (5 + at0 + (i + t))) = gen ^ ns t) ∧
        qwOpt σ (qwWindows d cd base cut at0 i m k lo hi).2.2.1 = qwOpt σ lo +
          ∑ t ∈ Finset.range m, qwLoT (qwWin d cd (i + t)).1 (qwWin d cd (i + t)).2 cut (ns t) ∧
        qwOpt σ (qwWindows d cd base cut at0 i m k lo hi).2.2.2 = qwOpt σ hi +
          ∑ t ∈ Finset.range m, qwHiT (qwWin d cd (i + t)).1 (qwWin d cd (i + t)).2 cut (ns t)
  | _, 0, _, _, _, _, _ => ⟨fun _ ↦ 0, fun _ h ↦ absurd h (by omega), by simp [qwWindows],
      by simp [qwWindows]⟩
  | i, m + 1, k, lo, hi, hw, h => by
    simp only [qwWindows, qwAH_append] at h ⊢
    obtain ⟨hwin, hrest⟩ := h
    have hw0 := hw 0 (by omega)
    rw [Nat.add_zero] at hw0
    obtain ⟨n, hn, hc, hlo, hhi⟩ := qwWindow_sound hκ L hT hw0.2 hwin
    obtain ⟨ns, hns, elo, ehi⟩ := qwWindows_sound hκ L hT (i + 1) m _ _ _
      (fun t ht ↦ by rw [show i + 1 + t = i + (t + 1) by omega]; exact hw (t + 1) (by omega)) hrest
    refine ⟨fun t ↦ if t = 0 then n else ns (t - 1), fun t ht ↦ ?_, ?_, ?_⟩
    · rcases t with _ | t
      · rw [Nat.add_zero]; exact ⟨hn, hc⟩
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have := hns t (by omega)
        rwa [show i + 1 + t = i + (t + 1) by omega] at this
    · rw [elo, hlo, Finset.sum_range_succ', add_assoc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
      congr 1; rw [add_comm]; congr 1
      exact Finset.sum_congr rfl fun t _ ↦ by rw [show i + 1 + t = i + (t + 1) by omega]
    · rw [ehi, hhi, Finset.sum_range_succ', add_assoc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
      congr 1; rw [add_comm]; congr 1
      exact Finset.sum_congr rfl fun t _ ↦ by rw [show i + 1 + t = i + (t + 1) by omega]


/-! ## A position's runs -/

theorem nat_split {X Y c : ℕ} (h : X < 2 ^ c) : (X + 2 ^ c * Y) % 2 ^ c = X ∧ (X + 2 ^ c * Y) / 2 ^ c = Y :=
  ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h],
    by rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h, Nat.zero_add]⟩

/-- A pattern shifted inside a limb is its integer shifted. -/
theorem eOfNat_mul_cbWord {s w n : ℕ} (hn : n < 2 ^ w) (hw : 1 ≤ w) (h : s + w ≤ 64) :
    eOfNat n * cbWord s = eOfNat (2 ^ s * n) := by
  have hs : 2 ^ s * n < 2 ^ 64 :=
    calc 2 ^ s * n < 2 ^ s * 2 ^ w := Nat.mul_lt_mul_of_pos_left hn (by positivity)
      _ = 2 ^ (s + w) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h
  rw [cbWord_eq', coordBasis_of_lt (by omega), mul_comm, eOfNat_two_pow_mul hs]

theorem qwOff_lt {d cd i : ℕ} (h : i < qwN d cd) : qwOff d cd i = (qwWin d cd i).1 := by
  rw [qwOff, ite_pos' h]

theorem qwOff_top (d cd : ℕ) : qwOff d cd (qwN d cd) = d := by rw [qwOff, ite_neg' (lt_irrefl _)]

theorem qw_tiled {d cd : ℕ} (hs : QwShape d cd) {ns : ℕ → ℕ}
    (hns : ∀ t < qwN d cd, ns t < 2 ^ (qwWin d cd t).2) : Tiled (qwOff d cd) ns (qwN d cd) :=
  fun t ht ↦ by
    obtain ⟨-, -, he, -⟩ := hs.2.2.2.2.2.1 t ht
    exact ⟨by omega, by rw [← he, Nat.add_sub_cancel_left]; exact hns t ht⟩

/-- **A position's runs**: the windows' low and high terms sum to the tiled sum below the limb
boundary and above it. -/
theorem qwSums {d cd cut : ℕ} (hs : QwShape d cd) (hc : cut ≤ 64) {ns : ℕ → ℕ}
    (hns : ∀ t < qwN d cd, ns t < 2 ^ (qwWin d cd t).2) : ∀ m ≤ qwN d cd,
    ∑ t ∈ Finset.range m, qwLoT (qwWin d cd t).1 (qwWin d cd t).2 cut (ns t) =
        eOfNat (tS (qwOff d cd) ns m % 2 ^ cut) ∧
      ∑ t ∈ Finset.range m, qwHiT (qwWin d cd t).1 (qwWin d cd t).2 cut (ns t) =
        eOfNat (tS (qwOff d cd) ns m / 2 ^ cut)
  | 0, _ => by simp [tS, eOfNat_zero]
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := qwSums hs hc hns m (by omega)
    have ht := qw_tiled hs hns
    obtain ⟨hw1, hw7, he, hd⟩ := hs.2.2.2.2.2.1 m (by omega)
    have hd30 := hs.2.1
    have hS := tS_lt ht m (by omega)
    rw [qwOff_lt (by omega)] at hS
    set off := (qwWin d cd m).1
    set w := (qwWin d cd m).2
    set S := tS (qwOff d cd) ns m
    have hn := hns m (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih1, ih2, tS_succ, qwOff_lt (by omega)]
    by_cases h1 : off + w ≤ cut
    · have hlt : S + 2 ^ off * ns m < 2 ^ cut :=
        calc S + 2 ^ off * ns m < 2 ^ off + 2 ^ off * ns m := by omega
          _ = 2 ^ off * (ns m + 1) := by ring
          _ ≤ 2 ^ off * 2 ^ w := Nat.mul_le_mul_left _ hn
          _ = 2 ^ (off + w) := (Nat.pow_add _ _ _).symm
          _ ≤ 2 ^ cut := Nat.pow_le_pow_right (by decide) h1
      have hS' : S < 2 ^ cut := by omega
      rw [qwLoT, qwHiT, ite_pos' h1, ite_pos' h1, Nat.mod_eq_of_lt hS', Nat.mod_eq_of_lt hlt,
        Nat.div_eq_of_lt hS', Nat.div_eq_of_lt hlt, add_zero, eOfNat_mul_cbWord hn hw1 (by omega),
        add_comm, eOfNat_add_of_lt hS, Nat.add_comm]
      exact ⟨rfl, rfl⟩
    · by_cases h2 : off < cut
      · set a := cut - off
        have hca : 2 ^ cut = 2 ^ off * 2 ^ a := by rw [← Nat.pow_add]; congr 1; omega
        have hX : S + 2 ^ off * (ns m % 2 ^ a) < 2 ^ cut := by
          have := Nat.mod_lt (ns m) (show 0 < 2 ^ a by positivity)
          rw [hca]
          calc S + 2 ^ off * (ns m % 2 ^ a) < 2 ^ off + 2 ^ off * (ns m % 2 ^ a) := by omega
            _ = 2 ^ off * (ns m % 2 ^ a + 1) := by ring
            _ ≤ 2 ^ off * 2 ^ a := Nat.mul_le_mul_left _ this
        have hsum : S + 2 ^ off * ns m = S + 2 ^ off * (ns m % 2 ^ a) + 2 ^ cut * (ns m / 2 ^ a) := by
          rw [hca]
          conv_lhs => rw [← Nat.mod_add_div (ns m) (2 ^ a)]
          ring
        obtain ⟨e1, e2⟩ := nat_split (Y := ns m / 2 ^ a) hX
        have hS' : S < 2 ^ cut := by omega
        rw [qwLoT, qwHiT, ite_neg' h1, ite_neg' h1, ite_pos' h2, ite_pos' h2, hsum, e1, e2,
          Nat.mod_eq_of_lt hS', Nat.div_eq_of_lt hS', eOfNat_zero, zero_add,
          eOfNat_mul_cbWord (Nat.mod_lt _ (by positivity)) (show 1 ≤ a by omega)
            (show off + a ≤ 64 by omega), add_comm,
          eOfNat_add_of_lt hS, Nat.add_comm]
        exact ⟨rfl, rfl⟩
      · have hc' : 2 ^ off * ns m = 2 ^ cut * (2 ^ (off - cut) * ns m) := by
          rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
        have hSd : S / 2 ^ cut < 2 ^ (off - cut) := by
          rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
          rwa [show off - cut + cut = off by omega]
        rw [qwLoT, qwHiT, ite_neg' h1, ite_neg' h1, ite_neg' h2, ite_neg' h2, add_zero, hc',
          Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by positivity),
          eOfNat_mul_cbWord hn hw1 (by omega), add_comm, eOfNat_add_of_lt hSd, Nat.add_comm]
        exact ⟨rfl, rfl⟩


/-! ## A position's store, its reconstruction term and its pointer -/

theorem qwPr_sound {rd : Reader} {σ : Val} {j base cut d k : ℕ} {lo hi : V} {recon : Option V}
    (h : qwAH rd σ (qwPr j base cut d k lo hi recon).1) (hrec : recon = none → base = 0)
    {P : ℕ} (hP : P < 2 ^ d) (hd : 1 ≤ d) (hd30 : d ≤ 30) (hbase : base + d ≤ 192)
    (hcut : cut = 64 - base % 64) (hlo : σ lo = eOfNat (P % 2 ^ cut))
    (hhi : cut < d → σ hi = eOfNat (P / 2 ^ cut)) :
    LoadHolds rd (σ (.n 1)) j (eOfNat P) ∧
      qwOpt σ (qwPr j base cut d k lo hi recon).2.2 = qwOpt σ recon + eOfNat192 (2 ^ base * P) := by
  have hb64 : base % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold qwPr at h ⊢
  by_cases hc : cut < d
  · rw [ite_pos' hc] at h ⊢
    simp only [qwAH_cons, qwAH_nil, Atom.Holds] at h
    obtain ⟨e0, e1, e2, l2, e3, e4, e5, e6, e7, e8, -⟩ := h
    have hY : P / 2 ^ cut < 2 ^ (d - cut) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, Nat.sub_add_cancel hc.le]
      exact hP
    have hX : P % 2 ^ cut < 2 ^ cut := Nat.mod_lt _ (by positivity)
    have hpos : σ (.n (k + 2)) = eOfNat P := by
      rw [e2, e1, e0, hlo, hhi hc, mul_comm, eOfNat_mul_cbWord hY (by omega) (by omega), add_comm,
        eOfNat_add_of_lt hX, Nat.div_add_mod]
    have hbase0 : base ≠ 0 := by intro h0; rw [h0] at hcut; omega
    obtain ⟨rc, rfl⟩ : ∃ rc, recon = some rc := by
      cases recon with
      | none => exact absurd (hrec rfl) hbase0
      | some rc => exact ⟨rc, rfl⟩
    refine ⟨hpos ▸ l2, ?_⟩
    have hb1 : base < 192 := by omega
    have hbc : base + cut < 192 := by omega
    have hbc64 : (base + cut) % 64 = 0 := by omega
    have t1 : σ (.n (k + 4)) = eOfNat192 (2 ^ base * (P % 2 ^ cut)) := by
      rw [e4, e3, hlo, cbWord_eq', coordBasis_mul_eOfNat hb1]
      calc 2 ^ (base % 64) * (P % 2 ^ cut) < 2 ^ (base % 64) * 2 ^ cut :=
            Nat.mul_lt_mul_of_pos_left hX (by positivity)
        _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
    have t2 : σ (.n (k + 6)) = eOfNat192 (2 ^ (base + cut) * (P / 2 ^ cut)) := by
      rw [e6, e5, hhi hc, cbWord_eq', coordBasis_mul_eOfNat hbc]
      rw [hbc64, pow_zero, one_mul]
      exact lt_of_lt_of_le hY (Nat.pow_le_pow_right (by decide) (by omega))
    have hlt : 2 ^ base * (P % 2 ^ cut) < 2 ^ (base + cut) := by
      rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_left hX (by positivity)
    simp only [qwOpt]
    rw [e8, e7, t1, t2, eOfNat192_add_shift hlt, Nat.pow_add, Nat.mul_assoc, ← Nat.mul_add,
      Nat.mod_add_div]
    rfl
  · rw [ite_neg' hc] at h ⊢
    have hPc : P < 2 ^ cut := lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.mod_eq_of_lt hPc] at hlo
    have hb1 : base < 192 := by omega
    have hm : 2 ^ (base % 64) * P < 2 ^ 64 :=
      calc 2 ^ (base % 64) * P < 2 ^ (base % 64) * 2 ^ cut :=
            Nat.mul_lt_mul_of_pos_left hPc (by positivity)
        _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
    cases recon with
    | none =>
      simp only [qwAH_cons, qwAH_nil, Atom.Holds] at h
      obtain ⟨l, -⟩ := h
      have hb0 := hrec rfl
      refine ⟨hlo ▸ l, ?_⟩
      simp only [qwOpt]
      rw [hlo, hb0, pow_zero, one_mul, zero_add,
        eOfNat192_of_lt (lt_of_lt_of_le hPc (Nat.pow_le_pow_right (by decide) (by omega)))]
    | some rc =>
      simp only [qwAH_cons, qwAH_nil, Atom.Holds] at h
      obtain ⟨l, e0, e1, e2, -⟩ := h
      refine ⟨hlo ▸ l, ?_⟩
      simp only [qwOpt]
      rw [e2, e1, e0, hlo, cbWord_eq', coordBasis_mul_eOfNat hb1 hm]

theorem gw_eq {n : ℕ} (h : n < 2 ^ 64) : E.ofLimbs (gpowK n) 0 0 = gen ^ n := by
  rw [gpowK_eq (by unfold u128Bound; omega), ← ofK_eq_ofLimbs, gen_pow_eq_ofK]

theorem qwPtr_sound {rd : Reader} {σ : Val} {j n k : ℕ} (hjn : j * n + n ≤ 56)
    (h4 : FrameRun rd (σ (.n 4)) 56 fun i ↦ σ (.n (5 + i)))
    (h : qwAH rd σ (qwPtr j n k).1) :
    LoadHolds rd (σ (.n 2)) j (σ (.n (qwPtr j n k).2.2)) ∧
      FrameRun rd (σ (.n (qwPtr j n k).2.2)) n fun i ↦ σ (.n (5 + j * n + i)) := by
  unfold qwPtr at h ⊢
  by_cases hj : j = 0
  · subst hj
    simp only [↓reduceIte, qwAH_cons, qwAH_nil, Atom.Holds] at h ⊢
    refine ⟨h.1, h4.1, fun i hi v hv ↦ ?_⟩
    rw [h4.2 i (by omega) v hv, Nat.zero_mul, Nat.add_zero]
  · simp only [hj, ↓reduceIte, qwAH_cons, qwAH_nil, Atom.Holds] at h ⊢
    obtain ⟨⟨hk, hr⟩, l, -⟩ := h
    refine ⟨l, hk, fun i hi v hv ↦ ?_⟩
    rw [hr i (by simp; omega) v hv]
    simp

/-! ## Some sums are certainly there -/

theorem qwAcc_isSome (acc : Option V) (t : V) (k : ℕ) : (qwAcc acc t k).2.2.isSome = true := by
  cases acc <;> rfl

theorem qwWindow_lo_isSome {d cd base cut at0 i k : ℕ} {lo hi : Option V}
    (h : lo.isSome = true ∨ (qwWin d cd i).1 < cut) :
    (qwWindow d cd base cut at0 i k lo hi).2.2.1.isSome = true := by
  unfold qwWindow
  simp only
  split_ifs with h1 h2
  · exact qwAcc_isSome _ _ _
  · exact qwAcc_isSome _ _ _
  · rcases h with h | h
    · exact h
    · omega

theorem qwWindow_hi_isSome {d cd base cut at0 i k : ℕ} {lo hi : Option V}
    (h : hi.isSome = true ∨ cut < (qwWin d cd i).1 + (qwWin d cd i).2) :
    (qwWindow d cd base cut at0 i k lo hi).2.2.2.isSome = true := by
  unfold qwWindow
  simp only
  split_ifs with h1 h2
  · rcases h with h | h
    · exact h
    · omega
  · exact qwAcc_isSome _ _ _
  · exact qwAcc_isSome _ _ _

theorem qwWindows_isSome {d cd base cut at0 : ℕ} : ∀ (i m k : ℕ) (lo hi : Option V),
    ((lo.isSome = true ∨ ∃ t < m, (qwWin d cd (i + t)).1 < cut) →
      (qwWindows d cd base cut at0 i m k lo hi).2.2.1.isSome = true) ∧
    ((hi.isSome = true ∨ ∃ t < m, cut < (qwWin d cd (i + t)).1 + (qwWin d cd (i + t)).2) →
      (qwWindows d cd base cut at0 i m k lo hi).2.2.2.isSome = true)
  | _, 0, _, lo, hi => ⟨fun h ↦ h.elim id (fun ⟨_, h, _⟩ ↦ absurd h (by omega)),
      fun h ↦ h.elim id (fun ⟨_, h, _⟩ ↦ absurd h (by omega))⟩
  | i, m + 1, k, lo, hi => by
    simp only [qwWindows]
    have ih := qwWindows_isSome (d := d) (cd := cd) (base := base) (cut := cut) (at0 := at0)
      (i + 1) m (qwWindow d cd base cut at0 i k lo hi).2.1
      (qwWindow d cd base cut at0 i k lo hi).2.2.1 (qwWindow d cd base cut at0 i k lo hi).2.2.2
    refine ⟨fun h ↦ ih.1 ?_, fun h ↦ ih.2 ?_⟩
    · rcases h with h | ⟨t, ht, hc⟩
      · exact Or.inl (qwWindow_lo_isSome (Or.inl h))
      · rcases t with _ | t
        · exact Or.inl (qwWindow_lo_isSome (Or.inr hc))
        · exact Or.inr ⟨t, by omega, by rwa [show i + 1 + t = i + (t + 1) by omega]⟩
    · rcases h with h | ⟨t, ht, hc⟩
      · exact Or.inl (qwWindow_hi_isSome (Or.inl h))
      · rcases t with _ | t
        · exact Or.inl (qwWindow_hi_isSome (Or.inr hc))
        · exact Or.inr ⟨t, by omega, by rwa [show i + 1 + t = i + (t + 1) by omega]⟩

theorem qwOpt_getD {σ : Val} {o : Option V} (h : o.isSome = true) (v : V) :
    σ (o.getD v) = qwOpt σ o := by
  cases o with
  | none => simp at h
  | some _ => rfl


/-! ## A position -/

theorem qwPos_sound {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {σ : Val}
    (hT : WinTabs L.read (σ (.n 3))) (h4 : FrameRun L.read (σ (.n 4)) 56 fun i ↦ σ (.n (5 + i)))
    {d cd : ℕ} (hs : QwShape d cd) {j k : ℕ}
    {recon : Option V} (hj : j < 192 / d) (hrec : recon = none → j = 0)
    (h : qwAH L.read σ (qwPos d cd j k recon).1) :
    ∃ P < 2 ^ d, LoadHolds L.read (σ (.n 1)) j (eOfNat P) ∧
      qwOpt σ (qwPos d cd j k recon).2.2 = qwOpt σ recon + eOfNat192 (2 ^ (j * d) * P) ∧
      (qwPos d cd j k recon).2.2.isSome = true ∧
      ∃ p : E, LoadHolds L.read (σ (.n 2)) j p ∧
        FrameRun L.read p (qwN d cd) fun i ↦ gen ^ ((P >>> (qwWin d cd i).1) % 2 ^ (qwWin d cd i).2) := by
  have hd12 := hs.1
  have hd30 := hs.2.1
  have hwin := hs.2.2.2.2.2.1
  have hN8 := hs.2.2.2.2.1
  have hdpos : 0 < d := by omega
  have hbase : j * d + d ≤ 192 := by
    have := Nat.div_mul_le_self 192 d
    have : (j + 1) * d ≤ 192 / d * d := Nat.mul_le_mul_right _ hj
    nlinarith
  simp only [qwPos, qwAH_append] at h ⊢
  obtain ⟨⟨hw, hpr⟩, hpt⟩ := h
  set cut := 64 - j * d % 64
  have hcut : cut ≤ 64 := by omega
  obtain ⟨ns, hns, elo, ehi⟩ := qwWindows_sound hκ L hT 0 (qwN d cd) k none none
    (fun t ht ↦ by rw [Nat.zero_add]; exact ⟨(hwin t ht).1, (hwin t ht).2.1⟩) hw
  simp only [Nat.zero_add] at hns elo ehi
  have hns' : ∀ t < qwN d cd, ns t < 2 ^ (qwWin d cd t).2 := fun t ht ↦ (hns t ht).1
  have ht := qw_tiled hs hns'
  set P := tS (qwOff d cd) ns (qwN d cd) with hPdef
  have hP : P < 2 ^ d := by have := tS_lt ht _ le_rfl; rwa [qwOff_top] at this
  obtain ⟨sl, sh⟩ := qwSums hs hcut hns' (qwN d cd) le_rfl
  have hN1 : 1 ≤ qwN d cd := by unfold qwN; omega
  have hlos := (qwWindows_isSome (d := d) (cd := cd) (base := j * d) (cut := cut)
    (at0 := j * qwN d cd) 0 (qwN d cd) k none none).1 (Or.inr ⟨0, hN1, by
      rw [Nat.zero_add, ← qwOff_lt (by omega), hs.2.2.2.1]; omega⟩)
  have hhis : cut < d → _ := fun hc ↦ (qwWindows_isSome (d := d) (cd := cd) (base := j * d)
    (cut := cut) (at0 := j * qwN d cd) 0 (qwN d cd) k none none).2 (Or.inr ⟨qwN d cd - 1,
      by omega, by
        obtain ⟨-, -, he, -⟩ := hwin (qwN d cd - 1) (by omega)
        rw [Nat.zero_add, ← qwOff_lt (by omega), he, Nat.sub_add_cancel hN1, qwOff_top]
        exact hc⟩)
  obtain ⟨hpos, hrc⟩ := qwPr_sound hpr (fun h0 ↦ by rw [hrec h0, Nat.zero_mul]) hP (by omega) hd30
    hbase rfl (by rw [qwOpt_getD (σ := σ) hlos, elo, sl]; simp [qwOpt, P])
    (fun hc ↦ by rw [qwOpt_getD (σ := σ) (hhis hc), ehi, sh]; simp [qwOpt, P])
  have hjn : j * qwN d cd + qwN d cd ≤ 56 := by
    have := hs.2.2.1
    have : (j + 1) * qwN d cd ≤ 192 / d * qwN d cd := Nat.mul_le_mul_right _ hj
    nlinarith
  obtain ⟨lp, ⟨pk, pr⟩⟩ := qwPtr_sound hjn h4 hpt
  refine ⟨P, hP, hpos, hrc, ?_, _, lp, pk, fun i hi v hv ↦ ?_⟩
  · unfold qwPr; split
    · rfl
    · split <;> rfl
  · have hv' := pr i hi v hv
    simp only at hv' ⊢
    rw [hv', (hns i hi).2, Nat.shiftRight_eq_div_pow, ← qwOff_lt hi]
    obtain ⟨-, -, he, -⟩ := hwin i hi
    have := tS_get ht hi
    rw [← he, Nat.add_sub_cancel_left] at this
    rw [this]


/-! ## The positions, the rest, the word -/

theorem qwPositions_sound {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {σ : Val}
    (hT : WinTabs L.read (σ (.n 3))) (h4 : FrameRun L.read (σ (.n 4)) 56 fun i ↦ σ (.n (5 + i)))
    {d cd : ℕ} (hs : QwShape d cd) : ∀ (j m k : ℕ) (recon : Option V), j + m ≤ 192 / d →
      (recon = none → j = 0) → qwAH L.read σ (qwPositions d cd j m k recon).1 →
      ∃ Ps : ℕ → ℕ, (∀ t < m, Ps t < 2 ^ d ∧ LoadHolds L.read (σ (.n 1)) (j + t) (eOfNat (Ps t)) ∧
          ∃ p : E, LoadHolds L.read (σ (.n 2)) (j + t) p ∧ FrameRun L.read p (qwN d cd)
            fun i ↦ gen ^ ((Ps t >>> (qwWin d cd i).1) % 2 ^ (qwWin d cd i).2)) ∧
        qwOpt σ (qwPositions d cd j m k recon).2.2 = qwOpt σ recon +
          ∑ t ∈ Finset.range m, eOfNat192 (2 ^ ((j + t) * d) * Ps t) ∧
        (recon.isSome = true ∨ 1 ≤ m → (qwPositions d cd j m k recon).2.2.isSome = true)
  | _, 0, _, recon, _, _, _ => ⟨fun _ ↦ 0, fun _ h ↦ absurd h (by omega), by simp [qwPositions],
      fun h ↦ h.elim id (fun h ↦ absurd h (by omega))⟩
  | j, m + 1, k, recon, hjm, hrec, h => by
    simp only [qwPositions, qwAH_append] at h ⊢
    obtain ⟨hpos, hrest⟩ := h
    obtain ⟨P, hP, hl, hv, hsome, p, lp, fp⟩ := qwPos_sound hκ L hT h4 hs (by omega) hrec hpos
    obtain ⟨Ps, hPs, ev, esome⟩ := qwPositions_sound hκ L hT h4 hs (j + 1) m _ _ (by omega)
      (fun h0 ↦ by rw [h0] at hsome; exact absurd hsome (by decide)) hrest
    refine ⟨fun t ↦ if t = 0 then P else Ps (t - 1), fun t ht ↦ ?_, ?_, fun _ ↦ esome (Or.inl hsome)⟩
    · rcases t with _ | t
      · simp only [↓reduceIte, Nat.add_zero]
        exact ⟨hP, hl, p, lp, fp⟩
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        obtain ⟨a, b, c⟩ := hPs t (by omega)
        rw [show j + (t + 1) = j + 1 + t by omega]
        exact ⟨a, b, c⟩
    · rw [ev, hv, Finset.sum_range_succ', add_assoc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
      congr 1; rw [add_comm]; congr 1
      exact Finset.sum_congr rfl fun t _ ↦ by rw [show j + 1 + t = j + (t + 1) by omega]

theorem qwRest_sound {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {σ : Val}
    (hT : WinTabs L.read (σ (.n 3))) {d cd : ℕ} (hs : QwShape d cd) :
    ∀ (i m k : ℕ) (recon : Option V), i + m ≤ qwRestN d → qwAH L.read σ (qwRest d i m k recon).1 →
      ∃ rs : ℕ → ℕ, (∀ t < m, rs t < 2 ^ (qwRestWin d (i + t)).2) ∧
        qwOpt σ (qwRest d i m k recon).2.2 = qwOpt σ recon +
          ∑ t ∈ Finset.range m, eOfNat192 (2 ^ (qwRestWin d (i + t)).1 * rs t) ∧
        (recon.isSome = true → (qwRest d i m k recon).2.2.isSome = true)
  | _, 0, _, recon, _, _ => ⟨fun _ ↦ 0, fun _ h ↦ absurd h (by omega), by simp [qwRest], id⟩
  | i, m + 1, k, recon, him, h => by
    simp only [qwRest, qwAH_append] at h ⊢
    obtain ⟨⟨⟨hr, hsc⟩, ha⟩, hrest⟩ := h
    obtain ⟨-, -, hw1, hw7, h192, h64⟩ := hs.2.2.2.2.2.2.1 i (by omega)
    obtain ⟨n, hn, -, hv⟩ := qwRead_sound hκ L hT hw7 hr
    obtain ⟨rs, hrs, ev, esome⟩ := qwRest_sound hκ L hT hs (i + 1) m _ _ (by omega) hrest
    refine ⟨fun t ↦ if t = 0 then n else rs (t - 1), fun t ht ↦ ?_, ?_,
      fun _ ↦ esome (qwAcc_isSome _ _ _)⟩
    · rcases t with _ | t
      · simpa using hn
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [show i + (t + 1) = i + 1 + t by omega]
        exact hrs t (by omega)
    · have hst : (qwRestWin d i).1 < 192 := by omega
      have hm : 2 ^ ((qwRestWin d i).1 % 64) * n < 2 ^ 64 :=
        calc 2 ^ ((qwRestWin d i).1 % 64) * n < 2 ^ ((qwRestWin d i).1 % 64) * 2 ^ (qwRestWin d i).2 :=
              Nat.mul_lt_mul_of_pos_left hn (by positivity)
          _ = 2 ^ ((qwRestWin d i).1 % 64 + (qwRestWin d i).2) := (Nat.pow_add _ _ _).symm
          _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h64
      rw [ev, qwAcc_val ha, qwScale_val hsc, hv, mul_comm, cbWord_eq', coordBasis_mul_eOfNat hst hm,
        Finset.sum_range_succ', add_assoc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
      congr 1; rw [add_comm]; congr 1
      exact Finset.sum_congr rfl fun t _ ↦ by rw [show i + 1 + t = i + (t + 1) by omega]

theorem qwBody_atoms (d cd : ℕ) :
    ([Stmt.atom (.frameAddr (.n 4) qwRun)] ++ (qwPositions d cd 0 (192 / d) 61 none).1 ++
      (qwRest d 0 (qwRestN d) (qwPositions d cd 0 (192 / d) 61 none).2.1
        (qwPositions d cd 0 (192 / d) 61 none).2.2).1).all isAtomB = true := by
  simp only [List.all_append, qwPositions_atoms, qwRest_atoms, List.all_cons, List.all_nil,
    isAtomB, Bool.and_true]

/-- **`decode_query_windows` is sound** at a shape of the template. -/
theorem qw_sound {name : String} {d cd : ℕ} (hs : QwShape d cd) (hq : QwIs name (qwBody d cd)) :
    decode_query_windows_Spec name d cd := by
  intro κ hκ L args rets hT hrel
  obtain ⟨fn, hfind, hps, hbody⟩ := hq
  rw [rel_iff_sem hfind] at hrel
  obtain ⟨σ, hp, hb⟩ := hrel
  rw [hps] at hp
  rw [hbody] at hb
  subst hp
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at hT
  have hd12 := hs.1
  have hper : 192 / d * d ≤ 192 := Nat.div_mul_le_self 192 d
  have hper1 : 1 ≤ 192 / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by have := hs.2.1; omega)
  unfold qwBody at hb
  simp only at hb
  rw [holdsList_append, holdsList_atoms (allAtoms_of_all (qwBody_atoms d cd))] at hb
  obtain ⟨hA, hT2⟩ := hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_nil] at hT2
  obtain ⟨hassert, hret⟩ := hT2
  have hA' : qwAH L.read σ ([Stmt.atom (.frameAddr (.n 4) qwRun)] ++
      (qwPositions d cd 0 (192 / d) 61 none).1 ++ (qwRest d 0 (qwRestN d)
        (qwPositions d cd 0 (192 / d) 61 none).2.1 (qwPositions d cd 0 (192 / d) 61 none).2.2).1) :=
    hA
  rw [qwAH_append, qwAH_append, qwAH_cons, qwAH_nil] at hA'
  obtain ⟨⟨⟨hfa, -⟩, hpA⟩, hrA⟩ := hA'
  have h4 : FrameRun L.read (σ (.n 4)) 56 fun i ↦ σ (.n (5 + i)) :=
    ⟨hfa.1, fun i hi v hv ↦ by rw [hfa.2 i (by simp [qwRun]; omega) v hv]; simp [qwRun]⟩
  obtain ⟨Ps, hPs, hpv, hpsome⟩ := qwPositions_sound hκ L hT h4 hs 0 (192 / d) 61 none
    (by omega) (fun _ ↦ rfl) hpA
  obtain ⟨rs, hrs, hrv, hrsome⟩ := qwRest_sound hκ L hT hs 0 (qwRestN d) _ _ (by omega) hrA
  set N := 192 / d
  set V : ℕ → ℕ := fun t ↦ if t < N then Ps t else rs (t - N)
  have htop : ∀ t ≤ N, qwTop d t = t * d := fun t ht ↦ by
    unfold qwTop
    split_ifs with h
    · rfl
    · rw [show t = N by omega, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      exact Nat.min_eq_right hper
  have hrw := hs.2.2.2.2.2.2.1
  have ht : Tiled (qwTop d) V (N + qwRestN d) := fun t ht ↦ by
    by_cases h : t < N
    · rw [htop t h.le, htop (t + 1) h]
      refine ⟨Nat.mul_le_mul_right _ (by omega), ?_⟩
      simp only [V, h, ↓reduceIte]
      rw [show (t + 1) * d - t * d = d by rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]]
      exact (hPs t h).1
    · obtain ⟨e1, e2, -, -, -, -⟩ := hrw (t - N) (by omega)
      rw [show N + (t - N) = t by omega] at e1 e2
      rw [← e1, ← e2]
      refine ⟨by omega, ?_⟩
      simp only [V, h, ↓reduceIte]
      rw [Nat.add_sub_cancel_left]
      have := hrs (t - N) (by omega)
      rwa [Nat.zero_add] at this
  have htot : qwOpt σ (qwRest d 0 (qwRestN d) (qwPositions d cd 0 N 61 none).2.1
      (qwPositions d cd 0 N 61 none).2.2).2.2 = eOfNat192 (tS (qwTop d) V (N + qwRestN d)) := by
    rw [hrv, hpv, ← eOfNat192_tS ht _ le_rfl, Finset.sum_range_add]
    simp only [qwOpt, zero_add]
    congr 1
    · exact Finset.sum_congr rfl fun t htt ↦ by
        have := Finset.mem_range.mp htt
        simp only [V, this, ↓reduceIte, htop t this.le]
    · exact Finset.sum_congr rfl fun t htt ↦ by
        have := Finset.mem_range.mp htt
        obtain ⟨e1, -⟩ := hrw t this
        simp only [V, show ¬ N + t < N by omega, ↓reduceIte, Nat.add_sub_cancel_left]
        rw [e1]
  have hsome := hrsome (hpsome (Or.inr hper1))
  rw [← qwOpt_getD hsome (.n 0), e_add_eq_zero_iff.mp hassert] at htot
  have hW : eToNat (σ (.n 0)) = tS (qwTop d) V (N + qwRestN d) := by
    rw [htot, eToNat_eOfNat192, Nat.mod_eq_of_lt]
    have := tS_lt ht _ le_rfl
    rwa [hs.2.2.2.2.2.2.2] at this
  refine ⟨hret.symm, fun j hj ↦ ?_⟩
  have hpj : qwPosOf d (σ (.n 0)) j = Ps j := by
    have := tS_get ht (i := j) (by omega)
    rw [htop j hj.le, htop (j + 1) hj, show (j + 1) * d - j * d = d by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]] at this
    rw [qwPosOf, Nat.shiftRight_eq_div_pow, hW, this]
    simp only [V, show j < N from hj, ↓reduceIte]
  obtain ⟨-, hl, p, lp, fp⟩ := hPs j hj
  rw [Nat.zero_add] at hl lp
  refine ⟨hpj ▸ hl, p, lp, fp.1, fun i hi v hv ↦ ?_⟩
  rw [fp.2 i hi v hv, hpj]
  rfl

end
end LeanVM.Guest.B1
