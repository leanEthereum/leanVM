/-
  LeanVM.Guest.B1.Tables.VtKidsB

  `verify_tables`' callees complete by bounded trees (`VtKidsCompleteB`), and their bound.
-/

module

public import LeanVM.Guest.B1.Tables.VtCKids
public import LeanVM.Guest.B1.Tables.VtCPadB
public import LeanVM.Guest.B1.Tables.VtPlaced

/-!
# The callees, bounded

`vt_kids_complete` with each lift in its `CompleteAtB` form: a padding weight is its frame, a
selector or index chain at most 33 frames, `__loop79` at most 33 rounds with their
`sumcheck_round4`, `__loop80` at most 33 frames (`vtNameBd`, by the callee's name); `vtKidsTot`
sums them over the 75 calls.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A callee's bound, by its name: `__loop79` 33 rounds with their `sumcheck_round4`, `__loop16`
19 frames, a padding weight its frame, any other loop 33 frames. -/
def vtNameBd (fs : String → ℕ) (f : String) : ℕ :=
  if f = "__loop79" then 33 * (fs "__loop79" + fs "sumcheck_round4")
  else if f = "__loop16" then 19 * fs "__loop16"
  else if pwNames.contains f then fs f
  else 33 * fs f

/-- The largest padding weight's frame. -/
def pwMax (fs : String → ℕ) : ℕ := (pwNames.map fs).foldl max 0

/-- The 75 callees' bound: six padding weights, the 65 selectors, the two index chains,
`__loop79` and `__loop80`, each at its own name. -/
abbrev vtKidsTot (fs : String → ℕ) : ℕ :=
  6 * pwMax fs + 33 * (selNames.map fs).sum + 33 * fs "__loop14" + 19 * fs "__loop16" +
    33 * (fs "__loop79" + fs "sumcheck_round4") + 33 * fs "__loop80"

theorem fs_le_vtNameBd (fs : String → ℕ) (f : String) : fs f ≤ vtNameBd fs f := by
  unfold vtNameBd
  split_ifs with h1 h2 <;> (try subst h1) <;> (try subst h2) <;> omega

set_option maxRecDepth 100000 in
theorem pw_names_facts : ∀ j < 29, pwNames.getD j "" ≠ "__loop79" ∧ pwNames.getD j "" ≠ "__loop16" ∧
    pwNames.contains (pwNames.getD j "") = true := by decide

set_option maxRecDepth 100000 in
theorem sel_names_facts : ∀ i < 65, selNames.getD i "" ≠ "__loop79" ∧ selNames.getD i "" ≠ "__loop16" ∧
    pwNames.contains (selNames.getD i "") = false := by decide

theorem sel_nameBd (fs : String → ℕ) {i : ℕ} (hi : i < 65) :
    vtNameBd fs (selNames.getD i "") = 33 * fs (selNames.getD i "") := by
  obtain ⟨a, b, c⟩ := sel_names_facts i hi
  simp only [vtNameBd, a, b, c, ↓reduceIte, Bool.false_eq_true]

theorem pw_nameBd (fs : String → ℕ) {j : ℕ} (hj : j < 29) :
    vtNameBd fs (pwNames.getD j "") = fs (pwNames.getD j "") := by
  obtain ⟨a, b, c⟩ := pw_names_facts j hj
  simp only [vtNameBd, a, b, c, ↓reduceIte]

theorem pw_le_pwMax (fs : String → ℕ) {j : ℕ} (hj : j < 29) : fs (pwNames.getD j "") ≤ pwMax fs :=
  le_foldl_max _ 0 _ (List.mem_map_of_mem (f := fs)
    (List.getD_eq_getElem pwNames "" (by simpa [pwNames] using hj) ▸ List.getElem_mem _ :
      pwNames.getD j "" ∈ pwNames))

theorem sel_le33 (fs : String → ℕ) {i m : ℕ} (hm : m ≤ 32) :
    m * (fs (selNames.getD i "") + 0) + fs (selNames.getD i "") ≤ 33 * fs (selNames.getD i "") := by
  rw [Nat.add_zero]; nlinarith

theorem idx14_le (fs : String → ℕ) {m : ℕ} (hm : m ≤ 32) :
    m * (fs "__loop14" + 0) + fs "__loop14" ≤ vtNameBd fs "__loop14" := by
  have : vtNameBd fs "__loop14" = 33 * fs "__loop14" := by simp [vtNameBd, pwNames]
  rw [this, Nat.add_zero]; nlinarith

theorem idx16_le (fs : String → ℕ) : 18 * (fs "__loop16" + 0) + fs "__loop16" ≤ vtNameBd fs "__loop16" := by
  have : vtNameBd fs "__loop16" = 19 * fs "__loop16" := by simp [vtNameBd]
  rw [this]; omega

theorem l79_le (fs : String → ℕ) {m : ℕ} (hm : m ≤ 32) :
    m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79" ≤ vtNameBd fs "__loop79" := by
  have : vtNameBd fs "__loop79" = 33 * (fs "__loop79" + fs "sumcheck_round4") := by simp [vtNameBd]
  rw [this]; nlinarith

theorem l80_le (fs : String → ℕ) {m : ℕ} (hm : m ≤ 32) :
    m * (fs "__loop80" + 0) + fs "__loop80" ≤ vtNameBd fs "__loop80" := by
  have : vtNameBd fs "__loop80" = 33 * fs "__loop80" := by simp [vtNameBd, pwNames]
  rw [this, Nat.add_zero]; nlinarith

/-- **`verify_tables`' callees are complete, placed, each by a tree within its name's bound.** -/
def VtKidsCompleteB : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), 7 ≤ κ → ∀ (Lin : Main.Layout) (b n logMem : ℕ)
    (ks τs nr : ℕ → ℕ) (point chis : List E) (cvr : ℕ → Digest) (cur : E) (cl ch : ℕ → E)
    (wsr : ℕ → List E) (zeta sq chiP : E),
    point.length < 33 → logMem ≤ point.length → 18 ≤ point.length → n ≤ point.length →
    (∀ i < 65, ks (selBlk.getD i 0) ≤ point.length) →
    (∀ t < 6, τs t < 29 ∧ τs t ≤ point.length ∧ nr t ≤ 2 ^ τs t) →
    chis = ((List.range n).map ch).reverse →
    (∀ r < n, RunsTo (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) →
    (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd zeta point ∧ (∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) ∧
      ReadsAt rd chiP chis ∧ ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr)) →
    ∀ k ∈ vtKids Lin b n point.length logMem ks τs nr point zeta sq chiP
      (vtOwnW ks point logMem n cvr cur cl ch chis), k.taken = true →
      CompleteAtB fs cert κ k.f k.Lin k.args k.Out (vtNameBd fs k.f)

/-- **`verify_tables`' callees are complete, placed, each by a tree within its name's bound and
weight.** -/
def VtKidsCompleteW : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (Θ : Type) (w : Θ → String → ℕ) (κ : ℕ), 7 ≤ κ → ∀ (Lin : Main.Layout) (b n logMem : ℕ)
    (ks τs nr : ℕ → ℕ) (point chis : List E) (cvr : ℕ → Digest) (cur : E) (cl ch : ℕ → E)
    (wsr : ℕ → List E) (zeta sq chiP : E),
    point.length < 33 → logMem ≤ point.length → 18 ≤ point.length → n ≤ point.length →
    (∀ i < 65, ks (selBlk.getD i 0) ≤ point.length) →
    (∀ t < 6, τs t < 29 ∧ τs t ≤ point.length ∧ nr t ≤ 2 ^ τs t) →
    chis = ((List.range n).map ch).reverse →
    (∀ r < n, RunsTo (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) →
    (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd zeta point ∧ (∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) ∧
      ReadsAt rd chiP chis ∧ ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr)) →
    ∀ k ∈ vtKids Lin b n point.length logMem ks τs nr point zeta sq chiP
      (vtOwnW ks point logMem n cvr cur cl ch chis), k.taken = true →
      Main.CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (vtNameBd fs k.f) fun θ => vtNameBd (w θ) k.f

/-- **A selector's kid is complete by a bounded tree within weights**, on its honest buffers. -/
theorem vtc_sel_kidW {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ} {κ : ℕ}
    {Lin : Main.Layout} {b n : ℕ}
    {ks : ℕ → ℕ} {point : List E} {own : List (List E)} {zeta sq : E} {i : ℕ} (hi : i < 65)
    (hown : own.length = 205) (hsel : ∀ r < 3, own.getD (selBuf i + r) [] = (selW ks point i).getD r [])
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd zeta point ∧ ReadsAt rd sq ((List.range 34).map fun j => gen ^ 2 ^ j))
    (hμ : point.length < 33) (hm0 : 0 < point.length - ks (selBlk.getD i 0)) :
    Main.CompleteAtW fs cert w κ (selNames.getD i "") (Lin ++ bufL b (vtSizes n) own)
      [1, gen ^ (point.length - ks (selBlk.getD i 0)), vtPtr b n (selBuf i) * gen ^ ks (selBlk.getD i 0),
        vtPtr b n (selBuf i + 1), zeta * gen ^ ks (selBlk.getD i 0), vtPtr b n (selBuf i + 2), sq,
        gen ^ ks (selBlk.getD i 0)] (Returns []) (33 * fs (selNames.getD i ""))
      fun θ => 33 * w θ (selNames.getD i "") := by
  have hb : selBuf i + 2 < 205 := by unfold selBuf; split_ifs <;> omega
  refine ((sel_completeAtW (sel_ok i hi) (vtSel_mem i hi) hm0 κ fun rd hlow hL rd' hag j hj => ?_).bmono
    (sel_le33 fs (by omega))).wmono fun θ => sel_le33 (w θ) (by omega)
  obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
  have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
    hag t (regionL_append.mpr (Or.inl ht))
  have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1 hagL
  have hsq := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2) hlow hL1 hagL
  have R0 := vtc_own_reads hown hL hag (i := selBuf i + 0) (by omega)
  have R1 := vtc_own_reads hown hL hag (i := selBuf i + 1) (by omega)
  have R2 := vtc_own_reads hown hL hag (i := selBuf i + 2) (by omega)
  rw [hsel 0 (by omega)] at R0
  rw [hsel 1 (by omega)] at R1
  rw [hsel 2 (by omega)] at R2
  exact vtc_selBody_honest R0 R1 R2 hz (fun t ht => vtcs_get (f := fun j => gen ^ 2 ^ j) hsq ht) hμ hj

set_option maxHeartbeats 4000000 in
/-- **`verify_tables`' callees are complete, placed, by bounded trees within weights**, on its honest buffers. -/
theorem vt_kids_completeW : VtKidsCompleteW := by
  intro fs cert Θ w κ hκ Lin b n logMem ks τs nr point chis cvr cur cl ch wsr zeta sq chiP hμ hlm h18 hn hks hτ
    hchis hrun hLin k hk ht
  have hown := (vtc_own_length ks point logMem n cvr cur cl ch chis).trans (vtc_sizes_length n)
  have hzs : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd zeta point ∧ ReadsAt rd sq ((List.range 34).map fun j => gen ^ 2 ^ j) := fun rd h1 h2 =>
    ⟨(hLin rd h1 h2).1, fun t ht => by simpa using (hLin rd h1 h2).2.1 t (by simpa using ht)⟩
  obtain ⟨o3, o11, o15⟩ := vtc_own_idx ks point logMem n cvr cur cl ch chis
  have hidxR : ∀ {rd rd' : Reader}, LowDef κ rd →
      MemL rd (Lin ++ bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis)) →
      (∀ i, RegionL (Lin ++ bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis)) i →
        rd' (gpow i) = rd (gpow i)) →
      ReadsAt rd' zeta point ∧ (∀ t < 34, LoadHolds rd' (vtPtr b n 3) t (1 + gen ^ 2 ^ t)) := by
    intro rd rd' hlow hL hag
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    refine ⟨readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1
      fun t ht => hag t (regionL_append.mpr (Or.inl ht)), fun t ht => ?_⟩
    have R := vtc_own_reads hown hL hag (i := 3) (by omega)
    rw [o3] at R
    exact vtcs_get (f := fun t => 1 + gen ^ 2 ^ t) R ht
  simp only [vtKids, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hk
  rcases hk with ((⟨t, ht6, rfl⟩ | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | rfl | rfl
  · obtain ⟨h29, hτp, hnr⟩ := hτ t ht6
    have hj : τs t < pwNames.length := by simpa [pwNames] using h29
    show Main.CompleteAtW fs cert w κ (pwNames.getD (τs t) "") Lin _ _ (vtNameBd fs (pwNames.getD (τs t) ""))
      fun θ => vtNameBd (w θ) (pwNames.getD (τs t) "")
    rw [List.getD_eq_getElem _ _ hj]
    exact ((pw_completeAtW (τs t) hj hnr hτp (fun rd h1 h2 => (hLin rd h1 h2).1)).bmono
      (fs_le_vtNameBd fs _)).wmono fun θ => fs_le_vtNameBd (w θ) _
  · exact (vtc_sel_kidW (i := 0) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by norm_num)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by norm_num)).symm
  · exact (vtc_sel_kidW (i := 1) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by norm_num)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by norm_num)).symm
  · refine ((idx_completeAtW idx_ok.1 (by simp) (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).bmono (idx14_le fs (by omega))).wmono fun θ => idx14_le (w θ) (by omega)
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 11) (by omega)
    rw [o11] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · exact (vtc_sel_kidW (i := 2) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by norm_num)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by norm_num)).symm
  · refine ((idx_completeAtW idx_ok.2 (by simp) (by norm_num) κ fun rd hlow hL rd' hag j hj => ?_).bmono
      (idx16_le fs)).wmono fun θ => idx16_le (w θ)
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 15) (by omega)
    rw [o15] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · exact (vtc_sel_kidW (i := i + 3) (by omega) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by omega) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by omega)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by omega)).symm
  · refine ((loop79_completeAtW (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).bmono (l79_le fs (by omega))).wmono fun θ => l79_le (w θ) (by omega)
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have hws := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.2) hlow hL1 hagL
    have R := vtc_own_reads hown hL hag (i := 202 + 0) (by omega)
    have C := vtc_own_reads hown hL hag (i := 202 + 1) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at R C
    exact vtc_zcRound_honest R C hchi hchis hws hrun hj
  · refine ((loop80_completeAtW (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).bmono (l80_le fs (by omega))).wmono fun θ => l80_le (w θ) (by omega)
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1 hagL
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have P := vtc_own_reads hown hL hag (i := 202 + 2) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at P
    exact vtc_peqBody_honest P hz hchi hj hn (by rw [hchis]; simp)

/-- **`verify_tables`' callees are complete, placed, by bounded trees**, on its honest buffers. -/
theorem vt_kids_completeB : VtKidsCompleteB :=
  fun fs cert κ hκ Lin b n logMem ks τs nr point chis cvr cur cl ch wsr zeta sq chiP h1 h2 h3 h4 h5 h6 h7 h8 h9
    k hk ht => (vt_kids_completeW fs cert Empty (fun e => e.elim) κ hκ Lin b n logMem ks τs nr point chis cvr
      cur cl ch wsr zeta sq chiP h1 h2 h3 h4 h5 h6 h7 h8 h9 k hk ht).toB

/-- **The callees' bound**: the 75 callees of `vtKids`, each at its name's bound. -/
theorem vtKids_bound (fs : String → ℕ) (Lin : Main.Layout) (b n μ logMem : ℕ) (ks τs nr : ℕ → ℕ)
    (point : List E) (zeta sq chiP : E) (own : List (List E)) (hτ : ∀ t < 6, τs t < 29) :
    kidsBound fs (fun k => vtNameBd fs k.f) (vtKids Lin b n μ logMem ks τs nr point zeta sq chiP own) ≤
      vtKidsTot fs := by
  unfold kidsBound
  refine le_trans (List.sum_le_sum (g := fun k => vtNameBd fs k.f) fun k _ => ?_) ?_
  · split
    · exact le_rfl
    · exact fs_le_vtNameBd fs _
  rw [vtKids_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    List.map_map, Function.comp_def, vtSelKid]
  have hpw : ((List.range 6).map fun t => vtNameBd fs (pwNames.getD (τs t) "")).sum ≤ 6 * pwMax fs := by
    refine le_trans (List.sum_le_length_nsmul _ (pwMax fs) fun x hx => ?_) (by simp)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    have h29 := hτ t (List.mem_range.mp ht)
    rw [pw_nameBd fs h29]; exact pw_le_pwMax fs h29
  have hsel : ((List.range 62).map fun i => vtNameBd fs (selNames.getD (i + 3) "")).sum =
      33 * ((List.range 62).map fun i => fs (selNames.getD (i + 3) "")).sum := by
    rw [← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left fun i hi => sel_nameBd fs (by have := List.mem_range.mp hi; omega))
  have hsplit : (selNames.map fs).sum = fs (selNames.getD 0 "") + fs (selNames.getD 1 "") +
      fs (selNames.getD 2 "") + ((List.range 62).map fun i => fs (selNames.getD (i + 3) "")).sum := by
    have : selNames.map fs = [fs (selNames.getD 0 ""), fs (selNames.getD 1 ""), fs (selNames.getD 2 "")] ++
        (List.range 62).map (fun i => fs (selNames.getD (i + 3) "")) := rfl
    rw [this, List.sum_append]; simp only [List.sum_cons, List.sum_nil]; omega
  rw [sel_nameBd fs (i := 0) (by norm_num), sel_nameBd fs (i := 1) (by norm_num),
    sel_nameBd fs (i := 2) (by norm_num), hsel,
    show vtNameBd fs "__loop14" = 33 * fs "__loop14" by simp [vtNameBd, pwNames],
    show vtNameBd fs "__loop16" = 19 * fs "__loop16" by simp [vtNameBd],
    show vtNameBd fs "__loop79" = 33 * (fs "__loop79" + fs "sumcheck_round4") by simp [vtNameBd],
    show vtNameBd fs "__loop80" = 33 * fs "__loop80" by simp [vtNameBd, pwNames]]
  simp only [vtKidsTot]
  rw [hsplit]
  omega

/-- The buffers' sizes, at most. -/
theorem vtSizes_sum_le {n : ℕ} (hn : n ≤ 32) : (vtSizes n).sum ≤ vtSzPre.sum + 198 := by
  rw [vtSizes_split, List.sum_append]
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- **`verify_tables`' bound**: its frame, its buffers and its 75 callees. -/
abbrev vtTablesBound (fs : String → ℕ) : ℕ :=
  fs "verify_tables" + (vtSzPre.sum + 198) + vtKidsTot fs

/-- `verify_tables`' weight: its frame's and its 75 callees'. -/
abbrev vtTablesBoundW (ω : String → ℕ) : ℕ := ω "verify_tables" + vtKidsTot ω

end
end LeanVM.Guest.B1.VerifySub
