/-
  LeanVM.Guest.B1.Placement.StackCert

  The guest's certification of a stacking order, for any number of blocks: a hinted order whose
  adjacent ranks the guest checks, and whose running offsets it writes once per block, is
  `stackOffsets`'s.
-/

module

public import LeanVM.Guest.B1.Placement.Certify

/-!
# A certified stacking order (G:1911-1944, G:1912-1937)

`certify_placement` and `verify_tables`' block certification run the same loop: rank `r` names a
block `π r`, reads its log-size `k r`, checks it against the previous rank's (not larger; on a
tie, the index not smaller), writes the running offset `g^S r` to the block's cell, and grows the offset
by `2^(k r)`. `tb_stack_cert`: the ranks name every block once, and every block's cell holds
`g^offset` with `offset` `stackOffsets`'s, of the sizes `κs` (`κs[π r] = k r`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem tb_prefixSize_le' {n : ℕ} (k : ℕ → ℕ) (hk : ∀ r < n, k r < 34) :
    ∀ r ≤ n, tbPrefixSize id ((List.range n).map k) r ≤ r * 2 ^ 33
  | 0, _ => by simp [tbPrefixSize]
  | r + 1, hr => by
    rw [tb_prefixSize_succ _ _ _ (by simp; omega)]
    have := tb_prefixSize_le' (n := n) k hk r (by omega)
    simp only [id, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show r < n by omega), Option.map_some, Option.getD_some]
    have : 2 ^ k r ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by have := hk r (by omega); omega)
    nlinarith

theorem tb_prefixSize_strict' {n : ℕ} (k : ℕ → ℕ) :
    ∀ r r', r < r' → r' ≤ n →
      tbPrefixSize id ((List.range n).map k) r < tbPrefixSize id ((List.range n).map k) r'
  | r, r' + 1, h, h' => by
    rw [tb_prefixSize_succ _ _ _ (by simp; omega)]
    rcases Nat.lt_or_ge r r' with hlt | hge
    · have := tb_prefixSize_strict' (n := n) k r r' hlt (by omega)
      have : 0 < 2 ^ (((List.range n).map k).getD r' 0) := Nat.two_pow_pos _
      simp only [id]; omega
    · obtain rfl : r = r' := by omega
      have : 0 < 2 ^ (((List.range n).map k).getD r 0) := Nat.two_pow_pos _
      simp only [id]; omega

/-- **A certified stacking order.** Ranks `r < n` name blocks `π r < n` of log-sizes `k r < 34`;
block `π r`'s cell at `off` holds `g^(Σ_{r' < r} 2^(k r'))`; adjacent ranks have non-increasing
sizes, non-decreasing blocks on a tie. Then the ranks name every block once, and with `κs[π r] = k r`
every block's cell holds `g^` its `stackOffsets κs` offset; the total is `Σ 2^κ`. -/
theorem tb_stack_cert {rd : Reader} {off : E} {n : ℕ} (hn : n ≤ 2 ^ 20) (π k : ℕ → ℕ)
    (hπ : ∀ r < n, π r < n) (hk : ∀ r < n, k r < 34)
    (hoff : ∀ r < n, LoadHolds rd off (π r) (gen ^ tbPrefixSize id ((List.range n).map k) r))
    (hadj : ∀ i, i + 1 < n → k (i + 1) ≤ k i ∧ (k (i + 1) = k i → π i ≤ π (i + 1))) :
    ∃ κs : List ℕ, κs.length = n ∧ (∀ r < n, κs.getD (π r) 0 = k r) ∧
      (∀ c < n, ∃ r < n, π r = c) ∧
      (∀ c < n, LoadHolds rd off c (gen ^ (stackOffsets κs).1.getD c 0)) ∧
      tbPrefixSize id ((List.range n).map k) n = (κs.map (2 ^ ·)).sum := by
  have hSb : ∀ r ≤ n, tbPrefixSize id ((List.range n).map k) r < 2 ^ 62 := fun r hr => by
    have := tb_prefixSize_le' k hk r hr
    have : r * 2 ^ 33 ≤ 2 ^ 20 * 2 ^ 33 := Nat.mul_le_mul_right _ (by omega)
    have : (2 : ℕ) ^ 20 * 2 ^ 33 < 2 ^ 62 := by norm_num
    omega
  have hinj : ∀ r < n, ∀ r' < n, π r = π r' → r = r' := fun r hr r' hr' he => by
    have e := tb_loadHolds_unique (hoff r hr) (he ▸ hoff r' hr')
    have := tb_gen_pow_inj' (by have := hSb r (by omega); omega)
      (by have := hSb r' (by omega); omega) e
    rcases Nat.lt_trichotomy r r' with h | h | h
    · exact absurd this (Nat.ne_of_lt (tb_prefixSize_strict' k r r' h (by omega)))
    · exact h
    · exact absurd this (Nat.ne_of_gt (tb_prefixSize_strict' k r' r h (by omega)))
  have hsurj : ∀ c < n, ∃ r < n, π r = c := by
    let f : Fin n → Fin n := fun r => ⟨π r, hπ r r.2⟩
    have hfi : Function.Injective f := fun a b hab =>
      Fin.ext (hinj a a.2 b b.2 (congrArg Fin.val hab))
    have hfb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, rfl⟩
    intro c hc
    obtain ⟨r, hr⟩ := hfb.2 ⟨c, hc⟩
    exact ⟨r, r.2, congrArg Fin.val hr⟩
  obtain ⟨πi, hπi⟩ := tb_exists_fun_of_forall (n := n) (fun c hc => (hsurj c hc))
  have hπiπ : ∀ r < n, πi (π r) = r := fun r hr =>
    hinj _ (hπi _ (hπ r hr)).1 _ hr (hπi _ (hπ r hr)).2
  set κs := (List.range n).map fun c => k (πi c)
  have hlen : κs.length = n := by simp [κs]
  have hsize : ∀ c < n, κs.getD c 0 = k (πi c) := fun c hc => by
    simp [κs, List.getElem?_range hc]
  have hsizeπ : ∀ r < n, κs.getD (π r) 0 = k r := fun r hr => by
    rw [hsize _ (hπ r hr), hπiπ r hr]
  set ord := (List.range n).map π
  have hordget : ∀ r < n, ord.getD r 0 = π r := fun r hr => by
    simp [ord, List.getElem?_range hr]
  have hperm : ord.Perm (List.range n) := by
    rw [List.perm_ext_iff_of_nodup _ List.nodup_range]
    · intro a
      simp only [ord, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨r, hr, rfl⟩; exact hπ r hr
      · intro ha; obtain ⟨r, hr, he⟩ := hsurj a ha; exact ⟨r, hr, he⟩
    · exact (List.nodup_map_iff_inj_on List.nodup_range).mpr fun a ha b hb he =>
        hinj a (List.mem_range.mp ha) b (List.mem_range.mp hb) he
  have hord : ord = tbStackOrder κs := by
    rw [tbStackOrder, hlen]
    refine eq_mergeSort_of_adjacent (κs.getD · 0) hperm fun i hi => ?_
    have hi' : i + 1 < n := by simpa [ord] using hi
    simp only [ord, List.getElem_map, List.getElem_range]
    rw [hsizeπ i (by omega), hsizeπ (i + 1) hi']
    obtain ⟨h1, h2⟩ := hadj i hi'
    exact ⟨h1, fun he => h2 he.symm⟩
  have hSord : ∀ r ≤ n, tbPrefixSize (κs.getD · 0) ord r = tbPrefixSize id ((List.range n).map k) r := fun r hr => by
    have hmap : ord.map (κs.getD · 0) = (List.range n).map k := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => hsizeπ r (List.mem_range.mp hr)
    rw [tb_prefixSize_map, hmap]
  refine ⟨κs, hlen, hsizeπ, hsurj, fun c hc => ?_, ?_⟩
  · obtain ⟨r, hr, hrc⟩ : ∃ r, r < n ∧ π r = c := ⟨πi c, hπi c hc⟩
    have hr2 : r < κs.length := by rw [hlen]; exact hr
    rw [← hrc, ← hordget r hr, hord, tbStackOrder, tb_stackOffsets_fst κs r hr2,
      ← tbStackOrder, ← hord, hSord r (by omega), hordget r hr]
    exact hoff r hr
  · have hfull : tbPrefixSize (κs.getD · 0) ord n = (ord.map fun i => 2 ^ κs.getD i 0).sum := by
      have := tb_prefixSize_full (κs.getD · 0) ord
      rwa [show ord.length = n by simp [ord]] at this
    rw [← hSord n le_rfl, hfull,
      (hperm.map _).sum_eq]
    simp only [κs, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun c hc => by
      simp only [Function.comp_apply]; rw [hsize c (List.mem_range.mp hc)])

end
end LeanVM.Guest.B1.Tables
