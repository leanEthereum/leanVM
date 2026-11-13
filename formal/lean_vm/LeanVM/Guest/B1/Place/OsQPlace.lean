/-
  LeanVM.Guest.B1.Place.OsQPlace

  A level's `opening_queries` call placed: its window pointers and windows read from the
  level's decoders, wherever their group is placed.
-/

module

public import LeanVM.Guest.B1.Place.OsSqGroup
public import LeanVM.Guest.B1.Opening.QueriesPlacedAll

/-!
# A level's queries, placed

`os_q_completeAtB`: a level's `opening_queries` specialization (`OqCompleteDB`, S1b-2's) is
`CompleteAtB` within `oqBound` words on the caller's words `Lk`, the window pointers `sqW` and the
decoders' runs `sqGroupRuns` of the level's group at `p`, for every `p`: query `k`'s window pointer
(`qptrs`' slot) is decoder `k / per`'s run shifted to position `k % per` (`sqEb`), and its windows
are that run's words (`qwRunW_at`). The rest of `OqLinMem` and `OqLinReg` (the rounds' challenges,
the final coefficients, the positions, the cap's cells and flags) is read from `Lk`.
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
  sqDecPos fs lv L n p (k / sqPer lv) + cert (sqDecName lv) (.n 5) +
    (k % sqPer lv) * qwN lv.depth lv.capDepth

/-- Decoder `j`'s run is one of the group's. -/
theorem sqGroupRuns_mem {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n p : ℕ} {w : ℕ → E} {j : ℕ} (hj : j < n) :
    (sqDecPos fs lv L n p j + cert (sqDecName lv) (.n 5),
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

/-- Query `k`'s window pointer. -/
theorem sqW_ptr {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n eq p : ℕ} {rd : Reader} (hm : MemL rd (sqW fs cert lv L n eq p)) {k : ℕ}
    (hk : k < n * sqPer lv) :
    LoadHolds rd (ofK (Parameters.addressOfIndex (eq + lv.posOff))) k
      (ofK (Parameters.addressOfIndex (sqEb fs cert lv L n p k))) := by
  obtain ⟨hj, -⟩ := sqEb_split (t := 0) hk (by
    unfold qwN; omega)
  have hper : 0 < sqPer lv := by
    rcases Nat.eq_zero_or_pos (sqPer lv) with h0 | h0
    · rw [h0] at hk; simp at hk
    · exact h0
  have := sqW_load hm (b := p) hj (Nat.mod_lt k hper)
  rw [ofK_addr_shift] at this
  have e : qwPtrAt cert (sqDecName lv) (sqDecPos fs lv L n p (k / sqPer lv)) lv.depth lv.capDepth
      (k % sqPer lv) = ofK (Parameters.addressOfIndex (sqEb fs cert lv L n p k)) := by
    rw [qwPtrAt, ofK_addr_mul_gen_pow]; rfl
  rw [e] at this
  refine (loadHolds_ofK_iff ?_).mp this
  have := Nat.div_add_mod k (sqPer lv)
  rw [Nat.mul_comm] at this
  omega

/-- **A level's `opening_queries`, placed**, its group at `p`: from `OqCompleteDB`, the rest of
its caller's words read from `Lk`. -/
theorem os_q_completeAtB {fs : String → ℕ} {cert : String → V → ℕ} (κ : ℕ) {lv : OsLv}
    {L name loop : String} {s : Oq} {odd : ℕ} (hdb : OqCompleteDB fs cert name loop s odd)
    (hpd : s.pd + s.cd = lv.depth) (hcd : s.cd = lv.capDepth) {n N : ℕ} (hN : N + 1 < ordG)
    (hQ : oqCount odd s.base N ≤ n * sqPer lv) {w : ℕ → E} {Lk : Layout}
    {ecap eflags ecoefs ehs epos eq : ℕ} {lamInv : E} {rounds : List FoldRound} {hsv : List E}
    {qs : ℕ → ℕ} {rows : ℕ → List K} {sibs : ℕ → List Digest}
    (hrl : rounds.length = s.folds) (hhl : s.final = 1 → hsv.length = s.nHs)
    (hst : OqStatic s rounds hsv qs rows sibs (oqCount odd s.base N))
    (hqs : ∀ k < oqCount odd s.base N, qs k = qwPosOf lv.depth (w (k / sqPer lv)) (k % sqPer lv))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lk →
      RoundsAt rd (ofK (Parameters.addressOfIndex ecoefs)) rounds ∧
      (s.final = 1 → WordsAt rd (ofK (Parameters.addressOfIndex ehs)) hsv) ∧
      ∀ k < oqCount odd s.base N,
        LoadHolds rd (ofK (Parameters.addressOfIndex epos)) k (eOfNat (qs k)) ∧
        LoadHolds rd (ofK (Parameters.addressOfIndex ecap)) (2 * (2 ^ s.cd + qs k / 2 ^ s.pd))
          (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
        LoadHolds rd (ofK (Parameters.addressOfIndex ecap)) (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + 1)
          (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
        LoadHolds rd (ofK (Parameters.addressOfIndex eflags)) (2 ^ (s.cd - 1) + qs k / 2 ^ (s.pd + 1)) 1)
    (hreg : (∀ l < 2 * s.folds, RegionL Lk (ecoefs + l)) ∧
      (s.final = 1 → ∀ l < s.nHs, RegionL Lk (ehs + l)) ∧
      ∀ k < oqCount odd s.base N, RegionL Lk (epos + k) ∧
        RegionL Lk (eflags + (qs k / 2 ^ (s.pd + 1) + 2 ^ (s.cd - 1))) ∧
        ∀ e < 2, RegionL Lk (ecap + (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + e)))
    (p : ℕ) :
    CompleteAtB fs cert κ name (Lk ++ sqW fs cert lv L n eq p ++ sqGroupRuns fs cert lv L n p w)
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex (eq + lv.posOff)),
        gen ^ N]
      (Returns [if s.final = 1 then 0 else
        oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (oqBound fs name loop N) := by
  set Lin := Lk ++ sqW fs cert lv L n eq p ++ sqGroupRuns fs cert lv L n p w with hLin
  set eb := sqEb fs cert lv L n p with heb
  have hqwN : qwN (s.pd + s.cd) s.cd = qwN lv.depth lv.capDepth := by rw [hpd, hcd]
  have hRk : ∀ i, RegionL Lk i → RegionL Lin i := fun i ⟨q, hq, h1, h2⟩ ↦
    ⟨q, List.mem_append_left _ (List.mem_append_left _ hq), h1, h2⟩
  have hRw : ∀ i, RegionL (sqW fs cert lv L n eq p) i → RegionL Lin i := fun i ⟨q, hq, h1, h2⟩ ↦
    ⟨q, List.mem_append_left _ (List.mem_append_right _ hq), h1, h2⟩
  have hRs : ∀ i, RegionL (sqGroupRuns fs cert lv L n p w) i → RegionL Lin i :=
    fun i ⟨q, hq, h1, h2⟩ ↦ ⟨q, List.mem_append_right _ hq, h1, h2⟩
  obtain ⟨r1, r2, r3⟩ := hreg
  refine hdb trivial κ Lin N ecap eflags ecoefs (ehs) epos (eq + lv.posOff) lamInv rounds hsv eb qs
    rows sibs hN hrl hhl hst ⟨fun l hl ↦ hRk _ (r1 l hl), fun h l hl ↦ hRk _ (r2 h l hl),
      fun k hk ↦ ⟨hRk _ (r3 k hk).1, hRw _ ?_, fun i hi ↦ hRs _ ?_, hRk _ (r3 k hk).2.1,
        fun e he ↦ hRk _ ((r3 k hk).2.2 e he)⟩⟩ fun rd hl hm ↦ ?_
  · have hk' : k < n * sqPer lv := lt_of_lt_of_le hk hQ
    obtain ⟨hj, -⟩ := sqEb_split (t := 0) hk' (by unfold qwN; omega)
    have hper : 0 < sqPer lv := by
      rcases Nat.eq_zero_or_pos (sqPer lv) with h0 | h0
      · rw [h0] at hk'; simp at hk'
      · exact h0
    have := sqW_region (fs := fs) (cert := cert) (L := L) (eq := eq) (b := p) hj
      (Nat.mod_lt k hper)
    have e : eq + lv.posOff + k / sqPer lv * sqPer lv + k % sqPer lv = eq + lv.posOff + k := by
      have := Nat.div_add_mod k (sqPer lv); rw [Nat.mul_comm] at this; omega
    rwa [e] at this
  · rw [hqwN] at hi
    exact sqGroup_region (lt_of_lt_of_le hk hQ) hi
  obtain ⟨hmk, hmw, hms⟩ : MemL rd Lk ∧ MemL rd (sqW fs cert lv L n eq p) ∧
      MemL rd (sqGroupRuns fs cert lv L n p w) := by
    obtain ⟨h12, h3⟩ := Main.memL_append.mp hm
    obtain ⟨h1, h2⟩ := Main.memL_append.mp h12
    exact ⟨h1, h2, h3⟩
  obtain ⟨m1, m2, m3⟩ := hmem rd hl hmk
  refine ⟨m1, m2, fun k hk ↦ ⟨(m3 k hk).1, sqW_ptr hmw (lt_of_lt_of_le hk hQ), fun i hi ↦ ?_,
    (m3 k hk).2⟩⟩
  rw [hqwN] at hi
  have := sqGroup_wins hms (lt_of_lt_of_le hk hQ) hi
  rw [hpd, hcd, hqs k hk]
  exact this

end
end LeanVM.Guest.B1
