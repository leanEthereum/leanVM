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
`sumcheck_round4`, `__loop80` at most 33 frames. `vtKB fs` bounds every callee, entered or not.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A bound on each of `verify_tables`' callees. -/
abbrev vtKB (fs : String → ℕ) : ℕ :=
  (pwNames.map fs).sum + 33 * (selNames.map fs).sum + 33 * (fs "__loop14" + fs "__loop16") +
    33 * (fs "__loop79" + fs "sumcheck_round4") + 33 * fs "__loop80"

theorem pw_le_vtKB (fs : String → ℕ) (j : ℕ) (hj : j < 29) : fs (pwNames.getD j "") ≤ vtKB fs := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fs)
    (List.getD_eq_getElem pwNames "" (by simpa [pwNames] using hj) ▸ List.getElem_mem _ :
      pwNames.getD j "" ∈ pwNames))
  simp only [vtKB]; omega

theorem sel_le_vtKB (fs : String → ℕ) {i m : ℕ} (hi : i < 65) (hm : m ≤ 32) :
    m * (fs (selNames.getD i "") + 0) + fs (selNames.getD i "") ≤ vtKB fs := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fs) (vtSel_mem i hi))
  have : m * (fs (selNames.getD i "") + 0) ≤ 32 * (selNames.map fs).sum := by
    rw [Nat.add_zero]; exact Nat.mul_le_mul hm this
  simp only [vtKB]; omega

theorem idx14_le_vtKB (fs : String → ℕ) {m : ℕ} (hm : m ≤ 32) :
    m * (fs "__loop14" + 0) + fs "__loop14" ≤ vtKB fs := by
  have : m * (fs "__loop14" + 0) ≤ 32 * fs "__loop14" := by rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hm
  simp only [vtKB]; omega

theorem idx16_le_vtKB (fs : String → ℕ) : 18 * (fs "__loop16" + 0) + fs "__loop16" ≤ vtKB fs := by
  simp only [vtKB]; omega

theorem l79_le_vtKB (fs : String → ℕ) {m : ℕ} (hm : m ≤ 32) :
    m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79" ≤ vtKB fs := by
  have : m * (fs "__loop79" + fs "sumcheck_round4") ≤ 32 * (fs "__loop79" + fs "sumcheck_round4") :=
    Nat.mul_le_mul_right _ hm
  simp only [vtKB]; omega

theorem l80_le_vtKB (fs : String → ℕ) {m : ℕ} (hm : m ≤ 32) :
    m * (fs "__loop80" + 0) + fs "__loop80" ≤ vtKB fs := by
  have : m * (fs "__loop80" + 0) ≤ 32 * fs "__loop80" := by rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hm
  simp only [vtKB]; omega

/-- **`verify_tables`' callees are complete, placed, by trees of at most `vtKB fs` words.** -/
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
      CompleteAtB fs cert κ k.f k.Lin k.args k.Out (vtKB fs)

/-- **A selector's kid is complete by a bounded tree**, on its honest buffers. -/
theorem vtc_sel_kidB {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {Lin : Main.Layout} {b n : ℕ}
    {ks : ℕ → ℕ} {point : List E} {own : List (List E)} {zeta sq : E} {i : ℕ} (hi : i < 65)
    (hown : own.length = 205) (hsel : ∀ r < 3, own.getD (selBuf i + r) [] = (selW ks point i).getD r [])
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd zeta point ∧ ReadsAt rd sq ((List.range 34).map fun j => gen ^ 2 ^ j))
    (hμ : point.length < 33) (hm0 : 0 < point.length - ks (selBlk.getD i 0)) :
    CompleteAtB fs cert κ (selNames.getD i "") (Lin ++ bufL b (vtSizes n) own)
      [1, gen ^ (point.length - ks (selBlk.getD i 0)), vtPtr b n (selBuf i) * gen ^ ks (selBlk.getD i 0),
        vtPtr b n (selBuf i + 1), zeta * gen ^ ks (selBlk.getD i 0), vtPtr b n (selBuf i + 2), sq,
        gen ^ ks (selBlk.getD i 0)] (Returns []) (vtKB fs) := by
  have hb : selBuf i + 2 < 205 := by unfold selBuf; split_ifs <;> omega
  refine (sel_completeAtB (sel_ok i hi) (vtSel_mem i hi) hm0 κ fun rd hlow hL rd' hag j hj => ?_).mono le_rfl
    (sel_le_vtKB fs hi (by omega))
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
/-- **`verify_tables`' callees are complete, placed, by bounded trees**, on its honest buffers. -/
theorem vt_kids_completeB : VtKidsCompleteB := by
  intro fs cert κ hκ Lin b n logMem ks τs nr point chis cvr cur cl ch wsr zeta sq chiP hμ hlm h18 hn hks hτ
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
    show CompleteAtB fs cert κ (pwNames.getD (τs t) "") Lin _ _ (vtKB fs)
    rw [List.getD_eq_getElem _ _ hj]
    refine (pw_completeAtB (τs t) hj hnr hτp (fun rd h1 h2 => (hLin rd h1 h2).1)).mono le_rfl ?_
    have := pw_le_vtKB fs (τs t) (by omega)
    rwa [List.getD_eq_getElem _ _ hj] at this
  · exact vtc_sel_kidB (i := 0) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · exact vtc_sel_kidB (i := 1) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · refine (idx_completeAtB idx_ok.1 (by simp) (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).mono le_rfl (idx14_le_vtKB fs (by omega))
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 11) (by omega)
    rw [o11] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · exact vtc_sel_kidB (i := 2) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · refine (idx_completeAtB idx_ok.2 (by simp) (by norm_num) κ fun rd hlow hL rd' hag j hj => ?_).mono
      le_rfl (idx16_le_vtKB fs)
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 15) (by omega)
    rw [o15] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · exact vtc_sel_kidB (i := i + 3) (by omega) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by omega) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · refine (loop79_completeAtB (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).mono le_rfl (l79_le_vtKB fs (by omega))
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have hws := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.2) hlow hL1 hagL
    have R := vtc_own_reads hown hL hag (i := 202 + 0) (by omega)
    have C := vtc_own_reads hown hL hag (i := 202 + 1) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at R C
    exact vtc_zcRound_honest R C hchi hchis hws hrun hj
  · refine (loop80_completeAtB (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).mono le_rfl (l80_le_vtKB fs (by omega))
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1 hagL
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have P := vtc_own_reads hown hL hag (i := 202 + 2) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at P
    exact vtc_peqBody_honest P hz hchi hj hn (by rw [hchis]; simp)

/-- **The callees' bound**: every callee of `vtKids` within `vtKB fs`. -/
theorem vtKids_bound (fs : String → ℕ) (Lin : Main.Layout) (b n μ logMem : ℕ) (ks τs nr : ℕ → ℕ)
    (point : List E) (zeta sq chiP : E) (own : List (List E)) :
    kidsBound fs (fun _ => vtKB fs) (vtKids Lin b n μ logMem ks τs nr point zeta sq chiP own) ≤
      75 * vtKB fs := by
  have hsel : ∀ i < 65, fs (selNames.getD i "") ≤ vtKB fs := fun i hi => by
    have := sel_le_vtKB fs (m := 0) hi (by omega); omega
  have h14 : fs "__loop14" ≤ vtKB fs := by simp only [vtKB]; omega
  have h79 : fs "__loop79" ≤ vtKB fs := by simp only [vtKB]; omega
  have h80 : fs "__loop80" ≤ vtKB fs := by simp only [vtKB]; omega
  have hk : ∀ k ∈ vtKids Lin b n μ logMem ks τs nr point zeta sq chiP own,
      (if k.taken = true then vtKB fs else fs k.f) ≤ vtKB fs := by
    intro k hk
    rw [vtKids_eq] at hk
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hk
    rcases hk with ⟨t, -, rfl⟩ | (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ | rfl | rfl
    · simp
    · split <;> first | exact le_rfl | exact hsel 0 (by omega)
    · split <;> first | exact le_rfl | exact hsel 1 (by omega)
    · split <;> first | exact le_rfl | exact h14
    · split <;> first | exact le_rfl | exact hsel 2 (by omega)
    · simp
    · split <;> first | exact le_rfl | exact hsel (i + 3) (by omega)
    · split <;> first | exact le_rfl | exact h79
    · split <;> first | exact le_rfl | exact h80
  unfold kidsBound
  refine le_trans (List.sum_le_length_nsmul _ (vtKB fs) fun x hx => ?_) ?_
  · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hx
    exact hk k hk'
  · rw [List.length_map, vtKids_eq]
    simp

/-- The buffers' sizes, at most. -/
theorem vtSizes_sum_le {n : ℕ} (hn : n ≤ 32) : (vtSizes n).sum ≤ vtSzPre.sum + 198 := by
  rw [vtSizes_split, List.sum_append]
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- **`verify_tables`' bound**: its frame, its buffers and its 75 callees. -/
abbrev vtTablesBound (fs : String → ℕ) : ℕ :=
  fs "verify_tables" + (vtSzPre.sum + 198) + 75 * vtKB fs

end
end LeanVM.Guest.B1.VerifySub
