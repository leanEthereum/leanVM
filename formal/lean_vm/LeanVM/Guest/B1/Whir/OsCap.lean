/-
  LeanVM.Guest.B1.Whir.OsCap

  The honest Merkle cap of a level: its nodes from the level's openings, flagged on their climbs.
-/

module

public import LeanVM.Guest.B1.Whir.CapAgrees
public import LeanVM.Guest.B1.Whir.Cap
public import LeanVM.Guest.B1.Whir.QueriesComplete

/-!
# The honest cap (TRIAGE #29, #30)

A level's openings `qs` (positions with openings, each climbing to the root `rt`, agreeing where
they meet) fill a cap of depth `cd` over a tree of height `depth`: node `v`'s digest is what any
opening gives it (`osCapD`), and `v` is flagged when it lies on a climb above the cap's leaves
(`osCapFlags`). On every memory holding them, `verify_merkle_cap` means the root
(`osCap_meaning`), and every opening's cap leaf and its parent's flag are what `opening_queries`
reads (`osCap_leaf`, `osCap_parent`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- Node `v`'s digest: one an opening gives it, `default` if none does. -/
noncomputable def osCapD (depth : ℕ) (qs : List (ℕ × Opening)) (v : ℕ) : Digest := by
  classical
  exact if h : ∃ d, ∃ a ∈ qs, NodeIs depth a v d then Classical.choose h else default

/-- The cap's cells: node `v`'s two scalars at `2v`, `2v + 1`, for `v < 2^(cd + 1)`. -/
noncomputable def osCapCells (depth cd : ℕ) (qs : List (ℕ × Opening)) : List E :=
  (List.range (2 ^ (cd + 1))).flatMap fun v =>
    [(digestScalars (osCapD depth qs v)).1, (digestScalars (osCapD depth qs v)).2]

/-- Node `v` is on a climb above the cap's leaves. -/
def OsOnClimb (depth cd : ℕ) (qs : List (ℕ × Opening)) (v : ℕ) : Prop :=
  ∃ a ∈ qs, ∃ l, depth - cd < l ∧ l ≤ depth ∧ v = heapNode depth a.1 l

/-- The cap's flags: `1` on the climbs, for `v < 2^cd`. -/
noncomputable def osCapFlags (depth cd : ℕ) (qs : List (ℕ × Opening)) : List E := by
  classical
  exact (List.range (2 ^ cd)).map fun v => if OsOnClimb depth cd qs v then 1 else 0

/-- What the level's openings satisfy: each climbs to `rt` from below `2^depth`, at least one. -/
structure OsCapOk (depth cd : ℕ) (rt : Digest) (qs : List (ℕ × Opening)) : Prop where
  agree : BatchAgrees depth qs
  pos : ∀ a ∈ qs, a.1 < 2 ^ depth
  len : ∀ a ∈ qs, a.2.path.length = depth
  root : ∀ a ∈ qs, climb (m := Id) blake2sBytes (hashWords a.2.leaf) a.1 a.2.path = rt
  ne : qs ≠ []
  cd1 : 1 ≤ cd
  cdd : cd ≤ depth

variable {depth cd : ℕ} {rt : Digest} {qs : List (ℕ × Opening)}

theorem osCapD_eq (h : OsCapOk depth cd rt qs) {a : ℕ × Opening} (ha : a ∈ qs) {v : ℕ} {d : Digest}
    (hv : NodeIs depth a v d) : osCapD depth qs v = d := by
  classical
  have hex : ∃ d, ∃ a ∈ qs, NodeIs depth a v d := ⟨d, a, ha, hv⟩
  unfold osCapD
  simp only [hex, ↓reduceDIte]
  obtain ⟨b, hb, hbv⟩ := Classical.choose_spec hex
  exact h.agree b hb a ha v _ d hbv hv

theorem os_heapNode_lt {q l : ℕ} (hq : q < 2 ^ depth) (hl : l ≤ depth) :
    heapNode depth q l < 2 ^ (depth - l + 1) := by
  unfold heapNode
  have h1 : q / 2 ^ l < 2 ^ (depth - l) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show depth - l + l = depth by omega]; exact hq
  rw [pow_succ]; omega

theorem os_heapNode_ge {q l : ℕ} : 2 ^ (depth - l) ≤ heapNode depth q l := Nat.le_add_right _ _

theorem os_heapNode_top {q : ℕ} (hq : q < 2 ^ depth) : heapNode depth q depth = 1 := by
  unfold heapNode
  rw [Nat.sub_self, pow_zero, Nat.div_eq_of_lt hq]

theorem os_heapNode_half {q l : ℕ} (hl : l < depth) : heapNode depth q l / 2 = heapNode depth q (l + 1) := by
  rw [heapNode_succ hl]; have := Bool.toNat_le (q.testBit l); omega

/-- The digest a climb gives node `heapNode l`: its climb's, hashing its children's. -/
theorem os_cap_hashed (h : OsCapOk depth cd rt qs) {a : ℕ × Opening} (ha : a ∈ qs) {l : ℕ} (hl : l < depth) :
    osCapD depth qs (heapNode depth a.1 (l + 1)) =
      hashPair (osCapD depth qs (2 * heapNode depth a.1 (l + 1)))
        (osCapD depth qs (2 * heapNode depth a.1 (l + 1) + 1)) := by
  have hlen := h.len a ha
  have hc : osCapD depth qs (heapNode depth a.1 (l + 1)) = climbAt (hashWords a.2.leaf) a.1 a.2.path (l + 1) :=
    osCapD_eq h ha (Or.inl ⟨l + 1, hl, rfl, rfl⟩)
  have hcl : osCapD depth qs (heapNode depth a.1 l) = climbAt (hashWords a.2.leaf) a.1 a.2.path l :=
    osCapD_eq h ha (Or.inl ⟨l, hl.le, rfl, rfl⟩)
  have hsb : osCapD depth qs (sibNode depth a.1 l) = a.2.path.getD l default :=
    osCapD_eq h ha (Or.inr ⟨l, hl, rfl, rfl⟩)
  rw [hc, climbAt_succ _ _ _ (by omega)]
  have hn := heapNode_succ (q := a.1) hl
  unfold sibNode at hsb
  cases hb : a.1.testBit l
  · simp only [hb, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Nat.add_zero] at hn hsb
    rw [hn] at hcl
    rw [hcl, hsb]
    simp
  · simp only [hb, Bool.not_true, Bool.toNat_true, Bool.toNat_false, Nat.add_zero] at hn hsb
    rw [hn] at hcl
    rw [hcl, hsb]
    simp

theorem os_capCells_getD (v : ℕ) (hv : v < 2 ^ (cd + 1)) (i : ℕ) (hi : i < 2) :
    (osCapCells depth cd qs).getD (2 * v + i) 0 =
      [(digestScalars (osCapD depth qs v)).1, (digestScalars (osCapD depth qs v)).2].getD i 0 := by
  unfold osCapCells
  rw [List.flatMap, oq_getD_flatten_uniform _ 2 (fun _ => rfl) _ v i hv hi]

theorem os_capCells_length : (osCapCells depth cd qs).length = 2 * 2 ^ (cd + 1) := by
  unfold osCapCells
  rw [List.flatMap, oq_length_flatten_uniform _ 2 (fun _ => rfl)]

theorem os_capCell {rd : Reader} {cap : E} (hr : ReadsAt rd cap (osCapCells depth cd qs)) {v : ℕ}
    (hv : v < 2 ^ (cd + 1)) : CapCell rd cap v (osCapD depth qs v) := by
  have hl := (os_capCells_length (depth := depth) (cd := cd) (qs := qs))
  have g := fun i (hi : i < 2) => by
    have := hr (2 * v + i) (by rw [hl]; omega)
    rwa [← List.getD_eq_getElem _ 0, os_capCells_getD v hv i hi] at this
  exact ⟨by simpa using g 0 (by omega), by simpa using g 1 (by omega)⟩

theorem os_capFlags_getD {v : ℕ} (hv : v < 2 ^ cd) :
    (osCapFlags depth cd qs).getD v 0 = (by classical exact if OsOnClimb depth cd qs v then 1 else 0) := by
  classical
  unfold osCapFlags
  simp [List.getD_eq_getElem?_getD, hv]

theorem os_capFlag {rd : Reader} {flags : E} (hr : ReadsAt rd flags (osCapFlags depth cd qs)) {v : ℕ}
    (hv : v < 2 ^ cd) :
    LoadHolds rd flags v (by classical exact if OsOnClimb depth cd qs v then 1 else 0) := by
  have := hr v (by simp [osCapFlags, hv])
  rwa [← List.getD_eq_getElem _ 0, os_capFlags_getD hv] at this

theorem os_onClimb_flag {rd : Reader} {flags : E} (hr : ReadsAt rd flags (osCapFlags depth cd qs)) {v : ℕ}
    (hv : v < 2 ^ cd) (hc : OsOnClimb depth cd qs v) : LoadHolds rd flags v 1 := by
  classical
  have := os_capFlag hr hv
  simp only [hc, ↓reduceIte] at this
  exact this

theorem os_heapNode_cap {q l : ℕ} (hq : q < 2 ^ depth) (hl : depth - cd < l) (hl' : l ≤ depth) :
    heapNode depth q l < 2 ^ cd := by
  have := os_heapNode_lt (depth := depth) hq hl'
  exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))

/-- **`verify_merkle_cap` on the honest cap** means the level's root. -/
theorem osCap_meaning (h : OsCapOk depth cd rt qs) {rd : Reader} {cap flags : E}
    (hcap : ReadsAt rd cap (osCapCells depth cd qs)) (hfl : ReadsAt rd flags (osCapFlags depth cd qs)) :
    MeaningVerifyMerkleCap cd rd [cap, flags] [(digestScalars rt).1, (digestScalars rt).2] := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, a ∈ qs := by
    cases hq : qs with
    | nil => exact absurd hq h.ne
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  have hq := h.pos a ha
  have hcd1 := h.cd1
  have hcdd := h.cdd
  have h2 : 4 ≤ 2 ^ (cd + 1) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (cd + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have htop := os_heapNode_top (depth := depth) hq
  have hroot : osCapD depth qs 1 = rt := by
    rw [← htop, osCapD_eq h ha (Or.inl ⟨depth, le_rfl, rfl, rfl⟩), ← h.len a ha, climbAt_length, h.root a ha]
  have hh1 := os_cap_hashed h ha (l := depth - 1) (by omega)
  rw [show depth - 1 + 1 = depth by omega, htop] at hh1
  refine ⟨os_onClimb_flag hfl (by
      calc 1 < 2 := by decide
        _ ≤ 2 ^ cd := by calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ cd := Nat.pow_le_pow_right (by decide) hcd1)
      ⟨a, ha, depth, by omega, le_rfl, htop.symm⟩,
    ⟨osCapD depth qs 2, osCapD depth qs 3, os_capCell hcap (by omega), os_capCell hcap (by omega),
      by rw [← hh1]; exact os_capCell hcap (by omega)⟩, fun c hc2 hc => ?_,
    rt, by rw [← hroot]; exact os_capCell hcap (by omega), rfl⟩
  have hfc := os_capFlag hfl hc
  by_cases hon : OsOnClimb depth cd qs c
  · simp only [hon, ↓reduceIte] at hfc
    refine ⟨1, hfc, (isInK_iff _).mpr ⟨1, by simp⟩, fun _ => ?_⟩
    obtain ⟨b, hb, l, hl1, hl2, rfl⟩ := hon
    have hqb := h.pos b hb
    have hlt : l < depth := by
      rcases Nat.lt_or_ge l depth with h' | h'
      · exact h'
      · obtain rfl : l = depth := by omega
        rw [os_heapNode_top hqb] at hc2; omega
    refine ⟨?_, ?_⟩
    · rw [os_heapNode_half hlt]
      exact os_onClimb_flag hfl (os_heapNode_cap hqb (by omega) (by omega)) ⟨b, hb, l + 1, by omega, by omega, rfl⟩
    · have hl0 : l = l - 1 + 1 := by omega
      have hhb := os_cap_hashed h hb (l := l - 1) (by omega)
      rw [← hl0] at hhb
      have hcl := os_heapNode_cap (cd := cd) hqb hl1 hl2
      refine ⟨osCapD depth qs (2 * heapNode depth b.1 l), osCapD depth qs (2 * heapNode depth b.1 l + 1),
        os_capCell hcap (by rw [pow_succ]; omega), os_capCell hcap (by rw [pow_succ]; omega), ?_⟩
      rw [← hhb]; exact os_capCell hcap (by rw [pow_succ]; omega)
  · simp only [hon, ↓reduceIte] at hfc
    exact ⟨0, hfc, (isInK_iff _).mpr ⟨0, by simp⟩, fun h0 => absurd rfl h0⟩

/-- **An opening's cap leaf** holds its climb below the cap. -/
theorem osCap_leaf (h : OsCapOk depth cd rt qs) {rd : Reader} {cap : E}
    (hcap : ReadsAt rd cap (osCapCells depth cd qs)) {a : ℕ × Opening} (ha : a ∈ qs) :
    CapCell rd cap (2 ^ cd + a.1 / 2 ^ (depth - cd))
      (climb (m := Id) blake2sBytes (hashWords a.2.leaf) a.1 (a.2.path.take (depth - cd))) := by
  have hq := h.pos a ha
  have e : 2 ^ cd + a.1 / 2 ^ (depth - cd) = heapNode depth a.1 (depth - cd) := by
    rw [heapNode, show depth - (depth - cd) = cd by have := h.cdd; omega]
  have hlt := os_heapNode_lt (depth := depth) hq (l := depth - cd) (by omega)
  rw [show depth - (depth - cd) + 1 = cd + 1 by have := h.cdd; omega] at hlt
  have hd := osCapD_eq h ha (Or.inl ⟨depth - cd, by omega, rfl, rfl⟩)
  have hc := os_capCell hcap hlt
  rw [hd] at hc
  rw [e]; exact hc

/-- **An opening's cap leaf's parent** is flagged. -/
theorem osCap_parent (h : OsCapOk depth cd rt qs) {rd : Reader} {flags : E}
    (hfl : ReadsAt rd flags (osCapFlags depth cd qs)) {a : ℕ × Opening} (ha : a ∈ qs) :
    LoadHolds rd flags (2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1)) 1 := by
  have hq := h.pos a ha
  have hcd1 := h.cd1
  have hcdd := h.cdd
  have e : 2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1) = heapNode depth a.1 (depth - cd + 1) := by
    rw [heapNode, show depth - (depth - cd + 1) = cd - 1 by omega]
  rw [e]
  exact os_onClimb_flag hfl (os_heapNode_cap hq (by omega) (by omega)) ⟨a, ha, depth - cd + 1, by omega, by omega, rfl⟩

end
end LeanVM.Guest.B1
