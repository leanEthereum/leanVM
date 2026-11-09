/-
  LeanVM.Guest.B1.Place.OsKidsSp4

  The squeeze loop's words for the queries: the window pointers `osW` and the decoders' runs `osS`.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsSp3

/-!
# The window pointers and window runs, read

`osW_reads`, `osW_region`: level `l`'s window pointers, its squeeze loop at `p`, are the decoders'
`wins` runs shifted to each position's windows. `osS_mem`, `osS_wins`: decoder `j`'s run holds the
windows of the positions of the challenge it decodes (`qwRunList`). `readsAt_shift`: a run read
from a shifted pointer.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem readsAt_shift {rd : Reader} {a : ℕ} {xs : List E} (h : ReadsAt rd (ofK (Parameters.addressOfIndex a)) xs)
    {k m : ℕ} (hk : k + m < xs.length) :
    LoadHolds rd (ofK (Parameters.addressOfIndex (a + k))) m (xs[k + m]'hk) := by
  rw [← ofK_gpow_mul_gen, loadHolds_mul_gen_pow]
  exact h (k + m) hk

theorem regionL_append_left {L L' : Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append_right {L L' : Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_right _ hq, h1, h2⟩

variable {fs : String → ℕ} {cert : String → V → ℕ} {c : OsCfg}

/-- The exponent of query `k`'s window run, level `l`'s squeeze loop at `p`: its decoder's `wins`
run, shifted to the position's windows. -/
def osEb (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (l p k : ℕ) : ℕ :=
  sqDecAt fs (lvAt c l) (c.sqLoop l) (osSqN c l) p (k / (192 / (lvAt c l).depth)) +
    cert (sqDecName (lvAt c l)) (.n 5) +
      (k % (192 / (lvAt c l).depth)) * qwN (lvAt c l).depth (lvAt c l).capDepth

/-- **Level `l`'s window pointers.** -/
theorem osW_reads {b l p : ℕ} {rd : Reader} (hm : MemL rd (osW fs cert c b l p)) {k : ℕ}
    (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth)) :
    LoadHolds rd (ofK (Parameters.addressOfIndex (osBase c b 8 + (lvAt c l).posOff))) k
      (ofK (Parameters.addressOfIndex (osEb fs cert c l p k))) := by
  have := hm _ (List.mem_singleton_self _) k (by simpa using hk)
  simp only [List.getElem_map, List.getElem_range, osBp] at this
  rw [ofK_gpow_mul_gen] at this
  exact this

theorem osW_region {b l p : ℕ} {k : ℕ} (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth)) :
    RegionL (osW fs cert c b l p) (osBase c b 8 + (lvAt c l).posOff + k) :=
  ⟨_, List.mem_singleton_self _, by simp, by simpa using hk⟩

/-- Decoder `j`'s `wins` run in the loop's buffers. -/
theorem osS_mem {tr : OsTr} {l p j : ℕ} (hj : j < osSqN c l) :
    (sqDecAt fs (lvAt c l) (c.sqLoop l) (osSqN c l) p j + cert (sqDecName (lvAt c l)) (.n 5),
      qwRunList (lvAt c l).depth (lvAt c l).capDepth (sqWJ ((tr.L l).F2.squeezeN 0).2.cap j)) ∈
        osS fs cert c tr l p := by
  unfold osS sqRuns
  refine List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
  simp [qwRunL]

theorem osS_off {l : ℕ} {k t : ℕ} (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth))
    (ht : t < qwN (lvAt c l).depth (lvAt c l).capDepth) :
    1 ≤ 192 / (lvAt c l).depth ∧ k / (192 / (lvAt c l).depth) < osSqN c l ∧
      (k % (192 / (lvAt c l).depth)) * qwN (lvAt c l).depth (lvAt c l).capDepth + t <
        192 / (lvAt c l).depth * qwN (lvAt c l).depth (lvAt c l).capDepth := by
  have hper : 1 ≤ 192 / (lvAt c l).depth := by
    rcases Nat.eq_zero_or_pos (192 / (lvAt c l).depth) with h0 | h0
    · rw [h0] at hk; simp at hk
    · omega
  refine ⟨hper, by unfold osSqN; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk), ?_⟩
  have h1 := Nat.mod_lt k (show 0 < 192 / (lvAt c l).depth by omega)
  have h2 : (k % (192 / (lvAt c l).depth) + 1) * qwN (lvAt c l).depth (lvAt c l).capDepth ≤
      192 / (lvAt c l).depth * qwN (lvAt c l).depth (lvAt c l).capDepth :=
    Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, one_mul] at h2; omega

/-- **Query `k`'s windows** in its decoder's `wins` run. -/
theorem osS_wins {tr : OsTr} {l p : ℕ} {rd : Reader} (hm : MemL rd (osS fs cert c tr l p)) {k : ℕ}
    (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth))
    {t : ℕ} (ht : t < qwN (lvAt c l).depth (lvAt c l).capDepth) :
    LoadHolds rd (ofK (Parameters.addressOfIndex (osEb fs cert c l p k))) t
      (gen ^ qwVal (lvAt c l).depth (lvAt c l).capDepth
        (qwPosOf (lvAt c l).depth (sqWJ ((tr.L l).F2.squeezeN 0).2.cap (k / (192 / (lvAt c l).depth)))
          (k % (192 / (lvAt c l).depth))) t) := by
  obtain ⟨-, hj, hm2⟩ := osS_off (c := c) hk ht
  have hr := hm _ (osS_mem (fs := fs) (cert := cert) (tr := tr) (p := p) hj)
  have := readsAt_shift hr (k := (k % (192 / (lvAt c l).depth)) *
    qwN (lvAt c l).depth (lvAt c l).capDepth) (m := t) (by simpa [qwRunList] using hm2)
  simp only [qwRunList, List.getElem_map, List.getElem_range] at this
  rw [qwRunW_at _ ht] at this
  unfold osEb
  exact this

theorem osS_region {tr : OsTr} {l p : ℕ} {k : ℕ}
    (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth)) {t : ℕ}
    (ht : t < qwN (lvAt c l).depth (lvAt c l).capDepth) :
    RegionL (osS fs cert c tr l p) (osEb fs cert c l p k + t) := by
  obtain ⟨-, hj, hm2⟩ := osS_off (c := c) hk ht
  refine ⟨_, osS_mem (fs := fs) (cert := cert) (tr := tr) (p := p) hj, ?_, ?_⟩
  · unfold osEb; simp only; omega
  · unfold osEb; simp only [qwRunList, List.length_map, List.length_range]; omega

end
end LeanVM.Guest.B1
