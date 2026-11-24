/-
  LeanVM.Guest.B1.Place.OsQPlace

  A level's `opening_queries` call placed: its window pointers and windows read from the
  level's decoders, wherever their group is placed.
-/

module

public import LeanVM.Guest.B1.Place.OsSqGroup
public import LeanVM.Guest.B1.Opening.QueriesPlacedAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«decode_query_windows__L»

/-!
# A level's queries, placed

A level's `opening_queries` call reads the window pointers `sqW` and the decoders' runs `sqGroupRuns` of the level's
group at `p`, for every `p`: query `k`'s window pointer (`qptrs`' slot) is decoder `k / per`'s run shifted to position
`k % per` (`sqEb`, `sqEb_split`), its windows that run's words (`sqGroup_wins`), in its region (`sqGroup_region`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- Query `k`'s windows in the level's group at `p`: decoder `k / per`'s run at position
`k % per`. -/
def sqEb (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLv) (L : String) (n p k : ℕ) : ℕ :=
  sqDecPos fs lv L n p (k / sqPer lv) + cert (sqDecName lv) (.n (valf% «decode_query_windows» "wins[0]")) +
    (k % sqPer lv) * qwN lv.depth lv.capDepth

/-- Decoder `j`'s run is one of the group's. -/
theorem sqGroupRuns_mem {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n p : ℕ} {w : ℕ → E} {j : ℕ} (hj : j < n) :
    (sqDecPos fs lv L n p j + cert (sqDecName lv) (.n (valf% «decode_query_windows» "wins[0]")),
      qwRunList lv.depth lv.capDepth (w j)) ∈ sqGroupRuns fs cert lv L n p w := by
  unfold sqGroupRuns
  rcases j with _ | j
  · exact List.mem_append_left _ (by simp [qwRunL, sqDecPos])
  · refine List.mem_append_right _ ?_
    unfold sqRuns
    refine List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    simp [qwRunL, sqDecPos, Nat.add_comm 1 j]

theorem sqEb_split {lv : OsLv} {n k t : ℕ} (hk : k < n * sqPer lv)
    (ht : t < qwN lv.depth lv.capDepth) :
    k / sqPer lv < n ∧ (k % sqPer lv) * qwN lv.depth lv.capDepth + t <
      sqPer lv * qwN lv.depth lv.capDepth := by
  have hper : 0 < sqPer lv := by
    rcases Nat.eq_zero_or_pos (sqPer lv) with h0 | h0
    · rw [h0] at hk; simp at hk
    · exact h0
  refine ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk), ?_⟩
  have h1 := Nat.mod_lt k hper
  have h2 : (k % sqPer lv + 1) * qwN lv.depth lv.capDepth ≤ sqPer lv * qwN lv.depth lv.capDepth :=
    Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, one_mul] at h2; omega

/-- **Query `k`'s windows** in the group's runs. -/
theorem sqGroup_wins {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n p : ℕ} {w : ℕ → E} {rd : Reader} (hm : MemL rd (sqGroupRuns fs cert lv L n p w)) {k t : ℕ}
    (hk : k < n * sqPer lv) (ht : t < qwN lv.depth lv.capDepth) :
    LoadHolds rd (ofK (Parameters.addressOfIndex (sqEb fs cert lv L n p k))) t
      (gen ^ qwVal lv.depth lv.capDepth (qwPosOf lv.depth (w (k / sqPer lv)) (k % sqPer lv)) t) := by
  obtain ⟨hj, hlt⟩ := sqEb_split hk ht
  have hr := hm _ (sqGroupRuns_mem (fs := fs) (cert := cert) (L := L) (p := p) (w := w) hj)
  have hlen : (k % sqPer lv) * qwN lv.depth lv.capDepth + t <
      (qwRunList lv.depth lv.capDepth (w (k / sqPer lv))).length := by
    simpa [qwRunList] using hlt
  have := hr _ hlen
  simp only [qwRunList, List.getElem_map, List.getElem_range] at this
  rw [qwRunW_at _ ht] at this
  exact (loadHolds_ofK_iff (by unfold sqEb; ring)).mp this

theorem sqGroup_region {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n p : ℕ} {w : ℕ → E} {k t : ℕ} (hk : k < n * sqPer lv) (ht : t < qwN lv.depth lv.capDepth) :
    RegionL (sqGroupRuns fs cert lv L n p w) (sqEb fs cert lv L n p k + t) := by
  obtain ⟨hj, hlt⟩ := sqEb_split hk ht
  refine ⟨_, sqGroupRuns_mem (fs := fs) (cert := cert) (L := L) (p := p) (w := w) hj, ?_, ?_⟩
  · unfold sqEb; omega
  · simp only [qwRunList, List.length_map, List.length_range]
    unfold sqEb
    simp only [sqPer] at hlt ⊢
    omega

end
end LeanVM.Guest.B1
