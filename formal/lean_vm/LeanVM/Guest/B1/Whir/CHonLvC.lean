/-
  LeanVM.Guest.B1.Whir.CHonLvC

  A non-final level's calls and memory at the honest data, from `OsH`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonCall
public import LeanVM.Guest.B1.Whir.CHonMemFin
public import LeanVM.Guest.B1.Whir.CHonStep
public import LeanVM.Guest.B1.Whir.CHonLvP
public import LeanVM.Guest.B1.Whir.CHonNames
public import LeanVM.Guest.B1.Whir.CCaps
public import LeanVM.Guest.B1.Fs.Templates

/-!
# A non-final level's calls, honestly

`midC_of`: under `OsH` at the honest buffers, level `l < yr`'s calls and memory `MidC` at the
honest data (`LvAt.midW`), from the level's step of the run (`LvAt.NextStep`), the
configuration's facts (`HonStatic`, `HonNames`) and the run facts named as hypotheses.

The pieces: the cursor's words of the level (`segR`, `segF`), the buffers' fixed words
(`fixedAt_own`), the grinds' lanes (`grind_lane`), the cap's cells and flags (`caps_load`,
`flags_load`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem rdCell_one (S : KeccakState) : rdCell S 1 = cellsOfState S false 1 := rfl

/-- **A grind's lane** from its proof of work. -/
theorem grind_lane {s : Fs} {bits : ℕ} (hb : bits ≠ 0) {n : E}
    (h : powOk bits (Keccak.lane (s.nonceState n) 2) = true) :
    ((cellsOfState (s.nonceState n) false 1).limb 0).lane.toNat % 2 ^ bits = 0 :=
  (grindOk_iff hb n).mp (Or.inr h)

theorem roundsTr_length : ∀ (n : ℕ) (fs : List E) (cl : E) (xs : List E), fs.length = 5 →
    (roundsTr n fs cl xs).1.length = 5
  | 0, _, _, _, h => h
  | n + 1, _, _, _, _ => roundsTr_length n _ _ _ (roundRets_take_length _ _ _ _)

/-! ## The cursor's words -/

section Cursor

variable {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {cur tabs : E} {xs ys : List E}

/-- The words `ys`, a suffix of the cursor's, from their offset. -/
theorem readsAt_suffix (h : ReadsAt rd cur xs) (hs : ys <:+ xs) :
    ReadsAt rd (cur * gen ^ (xs.length - ys.length)) ys := by
  obtain ⟨pre, rfl⟩ := hs
  have := readsAt_shift h pre.length ys.length (by simp)
  rw [List.length_append, Nat.add_sub_cancel]
  rwa [List.drop_left', List.take_of_length_le le_rfl] at this

/-- **`m` words of the suffix `ys` from `k`**, at the cursor. -/
theorem segR (h : ReadsAt rd cur xs) (hs : ys <:+ xs) {k m : ℕ} (hkm : k + m ≤ ys.length) :
    ReadsAt rd (cur * gen ^ (xs.length - ys.length + k)) ((ys.drop k).take m) := by
  have := readsAt_shift (readsAt_suffix h hs) k m hkm
  rwa [mul_gen_pow_add] at this

/-- **`m` words of the suffix `ys` from `k` are fixed.** -/
theorem segF (hs : ys <:+ xs) {k m : ℕ} (hkm : k + m ≤ ys.length) :
    FixedAt c b own cur tabs xs (cur * gen ^ (xs.length - ys.length + k)) m :=
  fixedAt_cur (by have := hs.length_le; omega)

end Cursor

/-! ## The buffers' fixed words -/

namespace OsHD

variable (h : OsHD) {rd : Reader} {b : ℕ} {cur tabs : E} {xs : List E}

theorem own_length {j : ℕ} (hj : j < (osSizesF h.c).length) :
    (h.own.getD j []).length = (osSizesF h.c).getD j 0 := by
  rw [h.own_getD hj, ownAt, fitTo_length]

/-- **A buffer's words are fixed.** -/
theorem fixedAt_own {j o m : ℕ} (hj : j < (osSizesF h.c).length) (hne : j ≠ osIxQbp)
    (hom : o + m ≤ (osSizesF h.c).getD j 0) :
    FixedAt h.c b h.own cur tabs xs (osPtrF h.c b j * gen ^ o) m :=
  fixedAt_buf hj hne (by rw [h.own_length hj]; exact hom)

theorem fixedAt_own0 {j m : ℕ} (hj : j < (osSizesF h.c).length) (hne : j ≠ osIxQbp)
    (hom : m ≤ (osSizesF h.c).getD j 0) :
    FixedAt h.c b h.own cur tabs xs (osPtrF h.c b j) m := by
  have := h.fixedAt_own (b := b) (cur := cur) (tabs := tabs) (xs := xs) (o := 0) (m := m) hj hne (by omega)
  simpa using this

/-- The levels' folds within every fold. -/
theorem foldsEnd_le (hS : HonStatic h.c) {l : ℕ} (hl : l < h.c.levels.length) :
    (osLvAt h.c l).foldsOff + (osLvAt h.c l).folds ≤ h.c.nFolds := by
  have hyr := hS.yr
  have key : ∀ d, l + d ≤ h.c.yrLevel →
      (osLvAt h.c l).foldsOff + (osLvAt h.c l).folds ≤
        (osLvAt h.c (l + d)).foldsOff + (osLvAt h.c (l + d)).folds := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have := ih (by omega)
      rw [show l + (d + 1) = l + d + 1 by omega, hS.fo (l := l + d) (by omega)]
      omega
  have := key (h.c.yrLevel - l) (by omega)
  rw [show l + (h.c.yrLevel - l) = h.c.yrLevel by omega, hS.foT] at this
  exact this

/-! ## The cap -/

theorem caps_load (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l k : ℕ} (hl : l < h.c.levels.length)
    (hk : k < 2 ^ ((osLvAt h.c l).capDepth + 2)) :
    LoadHolds rd (osPtrF h.c b 0 * gen ^ (4 * (osLvAt h.c l).capOff)) k (h.cv l k) := by
  obtain ⟨hdc, htc⟩ := chain_disj hS.caps
  have tc := htc l hl
  have h0 := hS.head (j := 0) (by omega)
  simp only [headSizes, List.getD_cons_zero] at h0
  have a := h.loadOff hm (hS.headLt (j := 0) (by omega)) (by unfold osIxQbp; omega)
    (o := 4 * (osLvAt h.c l).capOff) (e := k) (by rw [h0]; omega)
  rw [ownW_caps, capsC, getD_mapRange _ (by omega), segAt_at (val := h.cv) hdc hl hk] at a
  exact a

theorem flags_load (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l k : ℕ} (hl : l < h.c.levels.length)
    (hk : k < 2 ^ (osLvAt h.c l).capDepth) :
    LoadHolds rd (osPtrF h.c b 1 * gen ^ (osLvAt h.c l).capOff) k (h.fv l k) := by
  obtain ⟨hdf, htf⟩ := chain_disj hS.flags
  have tf := htf l hl
  have h1 := hS.head (j := 1) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h1
  have a := h.loadOff hm (hS.headLt (j := 1) (by omega)) (by unfold osIxQbp; omega)
    (o := (osLvAt h.c l).capOff) (e := k) (by rw [h1]; omega)
  rw [ownW_flags, flagsC, getD_mapRange _ (by omega), segAt_at (val := h.fv) hdf hl hk] at a
  exact a

/-- **`verify_merkle_cap`'s meaning** on level `l`'s honest cap in memory. -/
theorem cap_pre (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length)
    {root : Digest} {height width : ℕ} {ps : List ℕ} {phase : List Opening}
    (hlen : phase.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (ho : k < phase.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] phase[k]) = true)
    (hps : ∀ q ∈ ps, q < 2 ^ height) (hag : Guest.Limits.OpeningsAgree height (ps.zip phase))
    (hcd : 2 ≤ (osLvAt h.c l).capDepth) (hcdd : (osLvAt h.c l).capDepth ≤ height) (hne : 0 < ps.length)
    (hcv : h.cv l = capCellH height ps phase) (hfv : h.fv l = capFlH height (osLvAt h.c l).capDepth ps phase) :
    MeaningVerifyMerkleCap (osLvAt h.c l).capDepth rd
      [osPtrF h.c b 0 * gen ^ (4 * (osLvAt h.c l).capOff), osPtrF h.c b 1 * gen ^ (osLvAt h.c l).capOff]
      [(digestHalves root).1, (digestHalves root).2] :=
  capH_meaning hlen hok hps hag hcd hcdd hne
    (fun k _ hk ↦ by rw [← hcv]; exact h.caps_load hS hm hl hk)
    (fun k _ hk ↦ by rw [← hfv]; exact h.flags_load hS hm hl hk)

/-- The cap's words are fixed. -/
theorem cap_fixed (hS : HonStatic h.c) {l : ℕ} (hl : l < h.c.levels.length) :
    ∀ q ∈ (OsKind.cap (osLvAt h.c l).capDepth).spec,
      FixedAt h.c b h.own cur tabs xs
        ([osPtrF h.c b 0 * gen ^ (4 * (osLvAt h.c l).capOff), osPtrF h.c b 1 * gen ^ (osLvAt h.c l).capOff].getD
          q.1 0) q.2 := by
  obtain ⟨-, htc⟩ := chain_disj hS.caps
  obtain ⟨-, htf⟩ := chain_disj hS.flags
  have tc := htc l hl
  have tf := htf l hl
  have h0 := hS.head (j := 0) (by omega)
  have h1 := hS.head (j := 1) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h0 h1
  intro q hq
  simp only [OsKind.spec, merkleCapSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact h.fixedAt_own (hS.headLt (j := 0) (by omega)) (by unfold osIxQbp; omega) (by rw [h0]; omega)
  · exact h.fixedAt_own (hS.headLt (j := 1) (by omega)) (by unfold osIxQbp; omega) (by rw [h1]; omega)

end OsHD

end
end LeanVM.Guest.B1.Whir
