/-
  LeanVM.Guest.B1.Place.KidLp

  open_stacked's `level_positions` calls placed, from their placed statement.
-/

module

public import LeanVM.Guest.B1.Place.KidLr
public import LeanVM.Guest.B1.Place.Lp

/-!
# `level_positions`' calls, placed

`os_lp_kid`: level `l`'s `level_positions` call, at its honest arguments (`osLpArgs`), entered at
`p`, reads the callees' words and the level's window pointers (`osW … l p`, into its decoders'
frames `D l p`) and hands back the decoders' runs (`osS … l p`): `CompleteAtPO`, from `LpAtO` and
the level's honest data (`LvHelperFacts`: the capacity, the decoded positions).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {c : OsCfg} {tr : OsTr} {b0 : ℕ}
  {Lin : Layout}

theorem ofK_addr_mul_gen (a m : ℕ) : ofK (addressOfIndex a) * gen ^ m = ofK (addressOfIndex (a + m)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul']
  congr 1
  simp only [Parameters.addressOfIndex, pow_add]

/-- A layout's entry's cells lie in its region. -/
theorem regionL_entry {L : Layout} {q : ℕ × List E} (hq : q ∈ L) {k : ℕ} (hk : k < q.2.length) :
    RegionL L (q.1 + k) := ⟨q, hq, by omega, by omega⟩

/-- A run from an entry's cell `off`: its loads lie in the layout. -/
theorem regPtr_entry {L : Layout} {q : ℕ × List E} (hq : q ∈ L) {off n : ℕ}
    (hn : off + n ≤ q.2.length) : ∀ t < n, ∃ i,
      (ofK (addressOfIndex q.1) * gen ^ off).limb 0 * addressOfIndex t = addressOfIndex i ∧
        RegionL L i := fun t ht ↦
  ⟨q.1 + off + t, by rw [ofK_addr_mul_gen, Main.addr_ofK], by
    rw [Nat.add_assoc]; exact regionL_entry hq (by omega)⟩

/-- An own buffer but the window pointers is an entry of the callees' words. -/
theorem osLk_entry {j : ℕ} (hj : j < 16 + c.levels.length) (hne : j ≠ 6)
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap) :
    (osBase c b0 j, (osOwnL c tr fun _ _ ↦ 0).getD j []) ∈ osLk c tr b0 Lin := by
  have hf := osOwnL_fit c tr (fun _ _ ↦ 0) hpt htl
  have hjs : j < (osSizesL c).length := by rw [osSizesL_length]; exact hj
  have e := os_bufL_getD (b := b0) hf hjs
  have hl : j < (bufL b0 (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).length := by
    rw [bufL_os_length]; exact hj
  have hmem : (bufL b0 (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).getD j default ∈
      (bufL b0 (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).eraseIdx 6 := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.mem_eraseIdx_iff_getElem.mpr ⟨j, hl, hne, rfl⟩
  rw [e] at hmem
  exact List.mem_append_left _ hmem

theorem readsAt_getD {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- **`query_positions`' slots of level `i`** are its decoded positions. -/
theorem qposC_getD (hs : OsSizes c) {i : ℕ} (hi : i < c.levels.length) {j : ℕ}
    (hj : j < (lvAt c i).squeezes * (192 / (lvAt c i).depth)) :
    (qposC c tr).getD ((lvAt c i).posOff + j) 0 = posAt c tr i j := by
  have hpos := hs.pos
  have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
    (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (c.levels.length - 1 - i) i
    (by omega)
  have hend' : (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤
      c.levels.length * ligPosCap := hend
  have hown : ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length ((lvAt c i).posOff + j) = i := by
    have := ownerOf_eq (off := fun i ↦ (lvAt c i).posOff)
      (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (i := i)
      (k := (lvAt c i).posOff + j) (by omega) (by
      show (lvAt c i).posOff + j < (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth)
      omega) (c.levels.length - 1 - i) (by omega)
    rwa [show i + 1 + (c.levels.length - 1 - i) = c.levels.length by omega] at this
  rw [qposC, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range]
  simp only [hown, Nat.add_sub_cancel_left, hj, ↓reduceIte]

/-- **Level `l`'s `level_positions` call, placed**, at its honest arguments, its decoders at `D l`. -/
theorem os_lp_kid (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length)
    (hper : 0 < 192 / (lvAt c l).depth)
    (hH : LvHelperFacts c tr l) {name : String} {Bd : Option ℕ} {D : ℕ → ℕ → ℕ → ℕ}
    (hlp : LpAtO fs cert κ name (lvAt c l).squeezes (lvAt c l).depth (lvAt c l).capDepth (D l) Bd)
    (hB : BoundsAt fs name Bd) :
    CompleteAtPO fs cert κ name (fun p ↦ osLk c tr b0 Lin ++ osW cert c D b0 l p)
      (osLpArgs c tr (osAtOf c b0) l) (sqLast (lvAt c l) (tr.L l).F2.cap) (osS cert c tr D l) Bd := by
  obtain ⟨-, -, -, -, -, g5, -, g7, -, -⟩ := osOwnL_getD_head c tr fun _ _ ↦ 0
  set sq := (lvAt c l).squeezes
  set per := 192 / (lvAt c l).depth
  have hpos := hs.pos
  have hend' : (lvAt c l).posOff + sq * per ≤ c.levels.length * ligPosCap := off_end
    (off := fun i ↦ (lvAt c i).posOff) (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth))
    hpos (c.levels.length - 1 - l) l (by omega)
  have e5 : (osAtOf c b0).P.qpos = ofK (addressOfIndex (osBase c b0 5)) := rfl
  have e6 : (osAtOf c b0).P.qbp = ofK (addressOfIndex (osBase c b0 6)) := rfl
  have e7 : (osAtOf c b0).P.win = ofK (addressOfIndex (osBase c b0 7)) := rfl
  refine hlp _ _ _ _ _ hH.cap5 hH.capCan (fun p ↦ ?_) (fun p rd hl' hm ↦ ?_) hB
  · -- the loads' regions
    intro q hq t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    have hc5 : ((tr.L l).F2.cap ++ [(osAtOf c b0).P.qpos * gen ^ (lvAt c l).posOff,
        (osAtOf c b0).P.qbp * gen ^ (lvAt c l).posOff, (osAtOf c b0).P.win]).getD 5 0 =
          (osAtOf c b0).P.qpos * gen ^ (lvAt c l).posOff := by
      rw [List.getD_append_right _ _ _ _ (by rw [hH.cap5]), hH.cap5]; rfl
    have hc6 : ((tr.L l).F2.cap ++ [(osAtOf c b0).P.qpos * gen ^ (lvAt c l).posOff,
        (osAtOf c b0).P.qbp * gen ^ (lvAt c l).posOff, (osAtOf c b0).P.win]).getD 6 0 =
          (osAtOf c b0).P.qbp * gen ^ (lvAt c l).posOff := by
      rw [List.getD_append_right _ _ _ _ (by rw [hH.cap5]; omega), hH.cap5]; rfl
    have hc7 : ((tr.L l).F2.cap ++ [(osAtOf c b0).P.qpos * gen ^ (lvAt c l).posOff,
        (osAtOf c b0).P.qbp * gen ^ (lvAt c l).posOff, (osAtOf c b0).P.win]).getD 7 0 =
          (osAtOf c b0).P.win * gen ^ 0 := by
      rw [List.getD_append_right _ _ _ _ (by rw [hH.cap5]; omega), hH.cap5, pow_zero, mul_one]; rfl
    rcases hq with rfl | rfl | rfl
    · rw [hc5, e5]
      obtain ⟨i, hi, hr⟩ := regPtr_entry (osLk_entry (b0 := b0) (Lin := Lin) (j := 5) (by omega)
        (by omega) hpt htl) (off := (lvAt c l).posOff) (n := sq * per)
        (by rw [g5, qposC_length]; exact hend') t ht
      exact ⟨i, hi, (List.mem_append.mp hr.choose_spec.1).elim (fun h ↦ ⟨_, List.mem_append_left _
        (List.mem_append_left _ h), hr.choose_spec.2⟩) fun h ↦ ⟨_, List.mem_append_left _
        (List.mem_append_right _ h), hr.choose_spec.2⟩⟩
    · rw [hc6, e6]
      have hmem : (osBase c b0 6 + (lvAt c l).posOff, (List.range (sq * per)).map fun k ↦
          osBp cert c D (fun _ ↦ p) l (k / per) * gen ^ ((k % per) * qwN (lvAt c l).depth
            (lvAt c l).capDepth)) ∈ osLk c tr b0 Lin ++ osW cert c D b0 l p :=
        List.mem_append_right _ (List.mem_singleton_self _)
      refine ⟨osBase c b0 6 + (lvAt c l).posOff + t, by rw [ofK_addr_mul_gen, Main.addr_ofK], ?_⟩
      exact regionL_entry hmem (by simp only [List.length_map, List.length_range]; exact ht)
    · rw [hc7, e7]
      obtain ⟨i, hi, hr⟩ := regPtr_entry (osLk_entry (b0 := b0) (Lin := Lin) (j := 7) (by omega)
        (by omega) hpt htl) (off := 0) (n := 128) (by rw [g7]; simp [winC]) t ht
      exact ⟨i, hi, (List.mem_append.mp hr.choose_spec.1).elim (fun h ↦ ⟨_, List.mem_append_left _
        (List.mem_append_left _ h), hr.choose_spec.2⟩) fun h ↦ ⟨_, List.mem_append_left _
        (List.mem_append_right _ h), hr.choose_spec.2⟩⟩
  · -- the memory
    obtain ⟨hmk, hmw⟩ := Main.memL_append.mp hm
    refine ⟨fun n hn ↦ ?_, fun j hj t ht ↦ ⟨?_, ?_⟩⟩
    · have h := osLk_readsAt hpt htl hmk (j := 7) (by omega) (by omega)
      rw [g7] at h
      have := readsAt_map_range h hn
      rwa [word_eOfNat] at this
    · have h := osLk_readsAt hpt htl hmk (j := 5) (by omega) (by omega)
      rw [g5] at h
      have hk : j * per + t < sq * per := by
        have h1 : (j + 1) * per ≤ sq * per := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at h1; omega
      have h2 := readsAt_getD h (k := (lvAt c l).posOff + (j * per + t)) (by
        rw [qposC_length]; omega)
      rw [qposC_getD hs hl hk, hH.pos j hj t ht] at h2
      rw [loadHolds_mul_gen_pow]
      exact h2
    · have h := hmw _ (List.mem_singleton_self _)
      have hk : j * per + t < sq * per := by
        have h1 : (j + 1) * per ≤ sq * per := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at h1; omega
      have h2 := readsAt_map_range h hk
      have hq1 : (j * per + t) / per = j := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hper, Nat.div_eq_of_lt ht, Nat.zero_add]
      have hq2 : (j * per + t) % per = t := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
      rw [hq1, hq2] at h2
      show LoadHolds rd (ofK (addressOfIndex (osBase c b0 6)) * gen ^ (lvAt c l).posOff) _ _
      rw [ofK_addr_mul_gen]
      exact h2

end
end LeanVM.Guest.B1
