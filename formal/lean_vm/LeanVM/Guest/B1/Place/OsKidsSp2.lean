/-
  LeanVM.Guest.B1.Place.OsKidsSp2

  open_stacked's squeeze loops, placed on the honest trace.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsSp1

/-!
# The squeeze loops, placed

**`os_sq_rel`, `os_sq_completeAtP`**: level `l`'s squeeze loop (`c.sqLoop l`), at its honest
arguments `[1, g^n, sqz, qpos, qbp, tabs]` (the pointers `osAtOf c b`), placed at `p`, reads the
callees' words `osLk` and its window pointers `osW … l p` and returns its decoders' `wins` runs
`osS … l p` (`OsCompleteAtP`), from `sqLoop_relAtIn`: the squeeze run from `sqzC`, the window
table from `winC`, the decoded positions from `qposC`, the window pointers from `osW`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem ofK_gpow_mul_gen (a m : ℕ) : ofK (addressOfIndex a) * gen ^ m = ofK (addressOfIndex (a +
    m)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul']
  congr 1
  simp only [Parameters.addressOfIndex, pow_add]

theorem osPtrAt_eq (c : OsCfg) (b j : ℕ) : osPtrAt c b j = ofK (Parameters.addressOfIndex (osBase c b j)) := rfl

theorem osAtOf_qpos (c : OsCfg) (b : ℕ) : (osAtOf c b).P.qpos = osPtrAt c b 7 := rfl

theorem osAtOf_win (c : OsCfg) (b : ℕ) : (osAtOf c b).P.win = osPtrAt c b 9 := rfl

theorem SpLv.F2_pend (L : SpLv) : L.F2.pend = [] := by
  unfold SpLv.F2; split <;> rfl

theorem loadHolds_xm {rd : Reader} {p : E} {j m k : ℕ} {w : E} :
    LoadHolds rd (p * (gen ^ j) ^ m) k w ↔ LoadHolds rd p (j * m + k) w := by
  rw [← pow_mul, loadHolds_mul_gen_pow]

/-- **Level `l`'s squeeze loop, placed**, within its loop's and decoders' frames (`sqTot`). -/
theorem os_sq_rel (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {c : OsCfg}
    {tr : OsTr} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length) {fn : Fn}
    (hfind : coreProgram.find? (c.sqLoop l) = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody (lvAt c l) (c.sqLoop l)) (hlp : coreProgram.loop (c.sqLoop l) = true)
    (hdec : QwDecodeAtD fs cert κ (lvAt c l).depth (lvAt c l).capDepth (sqDecName (lvAt c l)))
    (b : ℕ) (Lin : Layout) :
    ∀ fp, ∃ Lown : Layout, Within (osS fs cert c tr l fp ++ Lown) fp
        (sqTot fs (lvAt c l) (c.sqLoop l) (lvAt c l).squeezes 0) ∧
      DisjL (osS fs cert c tr l fp ++ Lown) ∧
      ∀ rd, LowDef κ rd →
        MemL rd (osS fs cert c tr l fp ++ Lown ++ (osLk c tr b Lin ++ osW fs cert c b l fp)) →
        RelAtIn coreProgram fs cert rd (RegionL (osLk c tr b Lin ++ osW fs cert c b l fp))
          (RegionL (osS fs cert c tr l fp)) fp
          (sqTot fs (lvAt c l) (c.sqLoop l) (lvAt c l).squeezes 0) (c.sqLoop l)
          [1, gen ^ (lvAt c l).squeezes, osPtrAt c b (osIxSqz l), osPtrAt c b 7, osPtrAt c b 8,
            osPtrAt c b 9] [] := by
  intro fp
  have hlv := h.lvb l hl
  have hfit := h.fit l hl
  have hst := hF.lv l hl
  have hsq : (lvAt c l).squeezes ≤ c.maxSq := hs.sq l hl
  have hper := hlv.per
  have hpend : (tr.L l).F2.pend = [] := SpLv.F2_pend _
  have hF2 : (tr.L l).F2 = ⟨(tr.L l).F2.cap, []⟩ := fs_of_pend_nil hpend
  have hcap0 : ((tr.L l).F2.squeezeN 0).2.cap = (tr.L l).F2.cap := rfl
  have hsqj : ∀ j, sqCapJ ((tr.L l).F2.squeezeN 0).2.cap j = ((tr.L l).F2.squeezeN j).2.cap := fun j ↦ by
    rw [hcap0, sqCapJ]; conv_rhs => rw [hF2]
  have hcapF : ∃ S : KeccakState, (tr.L l).F2.cap = capOf S := by
    unfold SpLv.F2; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨S, hS⟩ := hcapF
  have hcl : ((tr.L l).F2.squeezeN 0).2.cap.length = 5 := by rw [hcap0, hS]; rfl
  have hcan : AllCanonical ((tr.L l).F2.squeezeN 0).2.cap := by rw [hcap0, hS]; exact capOf_canonical S
  -- the memory facts
  have hsqzR : ∀ rd, MemL rd (osLk c tr b Lin) → ReadsAt rd (osPtrAt c b (osIxSqz l)) (sqzC c tr l) :=
    fun rd hm ↦ by
      have := osLk_reads hm (fun _ _ ↦ 0) (j := osIxSqz l) (by unfold osIxSqz; omega)
        (by unfold osIxSqz; omega)
      rwa [(osOwnL_getD_lv6 c tr (fun _ _ ↦ 0) hl).1] at this
  refine (sqLoop_relAtIn fs cert κ hfind hp hb hlp
    hlv.digits hst.posOff hdec hlv.sq0 hlv.sqOrd hcl hcan (Lin := osLk c tr b Lin ++ osW fs cert c b l fp)
    fp (fun rd hl' hm j hj ↦ ?_) (fun rd hl' hm ↦ ⟨?_, fun j hj i hi ↦ ?_⟩) (fun j hj t ht ↦ ?_)
    (fun j hj ↦ ?_))
  · -- the squeeze run
    obtain ⟨hmk, -⟩ := Main.memL_append.mp hm
    have hB := lvMemB_cont hF h hs (osLk_fixed hmk) hl (hsqzR rd hmk)
    have hnext := sqNext_of_rows hpend (n := (lvAt c l).squeezes) hB.rows j hj
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rw [loadHolds_xm, hsqj, show j * 5 + i = 5 * j + i by ring]
      exact hB.rows j (Nat.le_of_lt hj) i hi
    · rw [hsqj]; exact hnext i hi
  · -- the window table
    obtain ⟨hmk, -⟩ := Main.memL_append.mp hm
    intro n hn
    have := readsAt_map_range (osLk_fixed hmk).win (k := n) hn
    rw [osAtOf_win, word_eOfNat] at this
    exact this
  · -- the decoded positions and the window pointers
    obtain ⟨hmk, hmw⟩ := Main.memL_append.mp hm
    have hfix := osLk_fixed hmk
    have hk : j * (192 / (lvAt c l).depth) + i < (lvAt c l).squeezes * (192 / (lvAt c l).depth) := by
      have : (j + 1) * (192 / (lvAt c l).depth) ≤ (lvAt c l).squeezes * (192 / (lvAt c l).depth) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at this; omega
    have hdiv : (j * (192 / (lvAt c l).depth) + i) / (192 / (lvAt c l).depth) = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
    have hmod : (j * (192 / (lvAt c l).depth) + i) % (192 / (lvAt c l).depth) = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    refine ⟨?_, ?_⟩
    · rw [loadHolds_xm, loadHolds_mul_gen_pow]
      have := qpos_all hs hfix hl hk
      rw [osAtOf_qpos] at this
      have e : posAt c tr l (j * (192 / (lvAt c l).depth) + i) =
          eOfNat (qwPosOf (lvAt c l).depth (sqWJ ((tr.L l).F2.squeezeN 0).2.cap j) i) := by
        unfold posAt qwPosOf
        rw [hdiv, hmod, squeezeN_getD _ _ _ (by rw [hfit.nsq]; omega)]
        unfold sqWJ
        rw [hsqj, ← fs_of_pend_nil (squeezeN_pend hpend j)]
        rfl
      rw [e] at this
      exact this
    · have hq := hmw _ (List.mem_singleton_self _)
      have := hq (j * (192 / (lvAt c l).depth) + i) (by simpa using hk)
      simp only [List.getElem_map, List.getElem_range, hdiv, hmod, osBp, osSqN] at this
      rw [osPtrAt_eq, ofK_gpow_mul_gen (osBase c b 8) (lvAt c l).posOff, loadHolds_xm]
      exact this
  · -- the squeeze run's addresses
    obtain ⟨q, hq, h1, h2⟩ := osLk_region c tr b Lin (fun _ _ ↦ 0) (j := osIxSqz l)
      (by unfold osIxSqz; omega) (by unfold osIxSqz; omega) (k := j * 5 + t) (by
        rw [(osOwnL_getD_lv6 c tr (fun _ _ ↦ 0) hl).1]
        simp only [sqzC, List.length_map, List.length_range]
        have : j + 2 ≤ c.maxSq + 1 := by omega
        nlinarith)
    refine ⟨osBase c b (osIxSqz l) + (j * 5 + t), ?_, q, List.mem_append_left _ hq, h1, h2⟩
    rw [osPtrAt_eq, ← pow_mul, ofK_gpow_mul_gen, Main.addr_ofK, Nat.add_assoc]

  · -- the decoders' positions, window pointers and table lie in the callees' words and the
    -- level's window pointers
    have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
      (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hs.pos
      (c.levels.length - 1 - l) l (by omega)
    have hend' : (lvAt c l).posOff + (lvAt c l).squeezes * (192 / (lvAt c l).depth) ≤ c.posLen := hend
    intro q hq t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    have hk : ∀ t < 192 / (lvAt c l).depth,
        j * (192 / (lvAt c l).depth) + t < (lvAt c l).squeezes * (192 / (lvAt c l).depth) := by
      intro t ht
      have : (j + 1) * (192 / (lvAt c l).depth) ≤ (lvAt c l).squeezes * (192 / (lvAt c l).depth) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at this; omega
    rcases hq with rfl | rfl | rfl
    · have hk := hk t ht
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      obtain ⟨q, hq, h1, h2⟩ := osLk_region c tr b Lin (fun _ _ ↦ 0) (j := 7) (by omega) (by omega)
        (k := (lvAt c l).posOff + j * (192 / (lvAt c l).depth) + t) (by
          rw [(osOwnL_getD_head6 c tr (fun _ _ ↦ 0)).2.2.2.1]
          simp only [qposC, List.length_map, List.length_range]
          omega)
      refine ⟨osBase c b 7 + ((lvAt c l).posOff + j * (192 / (lvAt c l).depth) + t), ?_, q,
        List.mem_append_left _ hq, h1, h2⟩
      rw [osPtrAt_eq, ofK_gpow_mul_gen, ← pow_mul, ofK_gpow_mul_gen, Main.addr_ofK]
      congr 1; ring
    · have hk := hk t ht
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      refine ⟨osBase c b 8 + (lvAt c l).posOff + j * (192 / (lvAt c l).depth) + t, ?_,
        _, List.mem_append_right _ (List.mem_singleton_self _), ?_, ?_⟩
      · rw [osPtrAt_eq, ofK_gpow_mul_gen, ← pow_mul, ofK_gpow_mul_gen, Main.addr_ofK]
      · dsimp only; omega
      · simp only [List.length_map, List.length_range]; omega
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      simp only at ht
      obtain ⟨q, hq, h1, h2⟩ := osLk_region c tr b Lin (fun _ _ ↦ 0) (j := 9) (by omega) (by omega)
        (k := t) (by rw [(osOwnL_getD_head6 c tr (fun _ _ ↦ 0)).2.2.2.2.2]; simpa [winC] using ht)
      exact ⟨osBase c b 9 + t, by rw [osPtrAt_eq, Main.addr_ofK], q, List.mem_append_left _ hq,
        h1, h2⟩

/-- **Level `l`'s squeeze loop, placed.** -/
theorem os_sq_completeAtP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {c : OsCfg}
    {tr : OsTr} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length) {fn : Fn}
    (hfind : coreProgram.find? (c.sqLoop l) = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody (lvAt c l) (c.sqLoop l)) (hlp : coreProgram.loop (c.sqLoop l) = true)
    (hdec : QwDecodeAtD fs cert κ (lvAt c l).depth (lvAt c l).capDepth (sqDecName (lvAt c l)))
    (b : ℕ) (Lin : Layout) :
    OsCompleteAtP fs cert κ (c.sqLoop l) (fun p ↦ osLk c tr b Lin ++ osW fs cert c b l p)
      [1, gen ^ (lvAt c l).squeezes, osPtrAt c b (osIxSqz l), osPtrAt c b 7, osPtrAt c b 8,
        osPtrAt c b 9] []
      (osS fs cert c tr l) := fun fp ↦
  let ⟨Lown, hW, hD, hR⟩ := os_sq_rel fs cert κ hF h hs hl hfind hp hb hlp hdec b Lin fp
  ⟨_, Lown, hW, hD, hR⟩

end
end LeanVM.Guest.B1
