/-
  LeanVM.Guest.B1.Place.OsLiftLv

  A level of f128's `open_stacked` placed: its named callees on the callees' words, its decoder
  group wherever placed, its `opening_queries` on the group's words.
-/

module

public import LeanVM.Guest.B1.Place.OsLiftLib
public import LeanVM.Guest.B1.Place.OsCallK
public import LeanVM.Guest.B1.Whir.CSqLoop

/-!
# A level, placed

`os_lv_ok`: on a body holding at the dispatch relation on every memory holding the callees'
words `Lk` (`osLkF`, one such memory existing), with the special calls at their honest values
(`OsSpecVals`), level `i`'s frames (`osLvKs`) satisfy `OsLvKPOk`: the calls before its squeezes
named (`os_kid_named`); its decoder and squeeze loop the group `os_sq_groupB` (the window pointers
`osWL`, the runs `osSL`); after them `λ`'s grind and the cap named, and `opening_queries` by
`os_q_completeAtB`, its words the honest data's (`OsHonest`) at the buffers' bases.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- Level `i`'s window pointers, its group at `p`. -/
def osWL (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (b0 i p : ℕ) : Layout :=
  sqW fs cert (osLvAt c i) (c.sqLoop i) (osLvAt c i).squeezes (osBaseF c b0 osIxQbp) p

/-- Level `i`'s decoders' runs, its group at `p`. -/
def osSL (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (word : ℕ → ℕ → E) (i p : ℕ) :
    Layout :=
  sqGroupRuns fs cert (osLvAt c i) (c.sqLoop i) (osLvAt c i).squeezes p (word i)

/-- Level `i`'s frames. -/
noncomputable def osLvK (σ : Val) (c : OsCfg) (i : ℕ) : OsLvKP :=
  ⟨((lvA c i (osLvAt c i) (osStAt c i)).filterMap Stmt.callS).map (mkCall σ),
    [mkCall σ (osDecCall c i), mkCall σ (osSqCall c i)],
    ((lvB c i (osLvAt c i) (osStAt c i)).filterMap Stmt.callS).map (mkCall σ)⟩

theorem osLvKs_get' (σ : Val) (c : OsCfg) {i : ℕ} (hi : i < c.levels.length) :
    (osLvKs σ c 0 c.levels (osHead c).2)[i]'(by rw [osLvKs_length]; exact hi) = osLvK σ c i := by
  rw [osLvKs_get σ c 0 c.levels (osHead c).2 i hi]
  have e : c.levels[i] = osLvAt c i := (List.getD_eq_getElem _ _ hi).symm
  simp only [Nat.zero_add, e]
  rfl

theorem forall₂_getD_len {own : List (List E)} {sizes : List ℕ}
    (h : List.Forall₂ (fun w s ↦ w.length = s) own sizes) {j : ℕ} (hj : j < sizes.length) :
    (own.getD j []).length = sizes.getD j 0 := by
  have hl := h.length_eq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  exact (List.forall₂_iff_get.mp h).2 j (by omega) hj

theorem sqLoop_loop {c : OsCfg} {l : ℕ} {fn : Fn} (hf : coreProgram.find? (c.sqLoop l) = some fn)
    (hb : fn.body = sqLoopBody (osLvAt c l) (c.sqLoop l)) : coreProgram.loop (c.sqLoop l) = true := by
  have hn : fn.name = c.sqLoop l := by simpa using List.find?_some hf
  rw [Program.loop_of_find? hf, Fn.loop, hb, hn]
  simp [sqLoopBody, osLoopTail, List.reverse_append]

/-- **A level's frames are placed**, the group at any position. -/
theorem os_lv_ok (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 11 ≤ κ)
    {c : OsCfg} (hA : PlaceAll c)
    (hsq : ∀ l < c.levels.length,
      FnIs (c.sqLoop l) (osParams 6) (sqLoopBody (osLvAt c l) (c.sqLoop l)))
    {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonest c args cur tabs xs tgt inn res pt pt1) {Lin : Layout}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) {b0 : ℕ}
    {σ : Val}
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLkF c b0 H.own Lin) →
      AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkF c b0 H.own Lin))) rd σ (osBodyA c))
    {rd0 : Reader} (hl0 : LowDef κ rd0) (hm0 : MemL rd0 (osLkF c b0 H.own Lin))
    (hSV : OsSpecVals c b0 tabs H.word H.lamInv H.batched H.mu σ) {i : ℕ}
    (hi : i < c.levels.length)
    (hin : ∀ c' ∈ (osLvK σ c i).calls, c' ∈ ((osBodyA c).filterMap Stmt.callS).map (mkCall σ)) :
    OsLvKPOk fs cert κ σ (osLkF c b0 H.own Lin) (osWL fs cert c b0 i) (osSL fs cert c H.word i)
      (osLvK σ c i) := by
  obtain ⟨hP, hyr, hSz, hLv⟩ := hA
  set Lk := osLkF c b0 H.own Lin with hLk
  have hlen : H.own.length = (osSizesF c).length := H.own_len.length_eq
  have hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk := ⟨rd0, hl0, hm0⟩
  have hnamed : ∀ x, osNamedB x = true → x.1 = none ∧ ∃ K, osKindOf x.2.1 = some K := fun x hx ↦ by
    simp only [osNamedB, Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hx
    exact hx
  obtain ⟨hS1, hSo, hSmax, hper, hpw, hpo, hqw, hent, hpd, hcd, hcd1, hN, hQ, hfo, hfin, hnhs,
    hcap4, hcap1, hpos, -⟩ := hLv i hi
  obtain ⟨-, -, hLvP, -⟩ := hP
  obtain ⟨hnA, hnH, -, -, -, -⟩ := hLvP i hi
  refine ⟨fun c' hc' ht ↦ ?_, ?_, fun p c' hc' ht ↦ ?_⟩
  · -- before the squeezes: named
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨-, K, hK⟩ := hnamed x (List.all_eq_true.mp hnA x hx)
    exact os_kid_named (osCalleesRegD_holds hκ) (osRoundRegD_holds hκ) hall hex
      (hin _ (List.mem_append_left _ hc')) ht (by rw [mkCall_f]; exact hK)
  · -- the decoders
    obtain ⟨fn, hf1, hf2, hf3⟩ := hsq i hi
    obtain ⟨-, -, -, -, -, -, h11v, -, hsqz⟩ := hSz
    obtain ⟨hzl, hzne, hzs⟩ := hsqz i hi
    obtain ⟨d1, d2, d3, d4, d5⟩ := hSV.1 i hi
    have hit : SqIterC (osLvAt c i) := by have := sqIterC'_holds (osLvAt c i) hpw hpo; exact this
    have hdec : QwDecodeAtD fs cert κ (osLvAt c i).depth (osLvAt c i).capDepth (sqDecName (osLvAt c i)) :=
      qwDecodeAtD_holds hrf hcons (by omega) _ hqw
    have hzlen : (H.own.getD (osIxSqz c i) []).length = (c.maxSq + 1) * 5 := by
      rw [forall₂_getD_len H.own_len hzl, hzs]
    have h11 : 11 < (osSizesF c).length := by
      have := osIxQbp_lt c; simp only [osIxQbp] at this; omega
    have hqlen : (H.own.getD 11 []).length = c.posLen := by
      rw [forall₂_getD_len H.own_len h11]; exact h11v
    refine (os_sq_groupB fs cert κ hf1 hf2 hf3 (sqLoop_loop hf1 hf3) hit hdec hS1 hSo
      (H.cap_len i) (H.cap_word i) (sqz := osPtrF c b0 (osIxSqz c i)) (tabs := tabs)
      (eqp := osBaseF c b0 11) (eq := osBaseF c b0 osIxQbp) (Lk := Lk)
      (fun rd hl hm ↦ ⟨(hLin rd hl (memL_lin_of_lk hm)).2,
        fun j hj1 hj ↦ H.rowsMem b0 rd (osMemF_of_lk hlen hm) i hi j hj1 hj,
        fun j hj i' hi' ↦ H.posMem b0 rd (osMemF_of_lk hlen hm) i hi j hj i' hi'⟩)
      (fun j hj1 hj t ht ↦ ⟨osBaseF c b0 (osIxSqz c i) + (j * 5 + t), by
          rw [osPtrF, ptr_pow_limb, Nat.add_assoc],
        regionL_lk_buf hlen hzl hzne (by rw [hzlen]; have := Nat.mul_le_mul_right 5 hSmax; omega)⟩)
      (fun j hj t ht ↦ by
        have h1 : (osLvAt c i).posOff + j * sqPer (osLvAt c i) + t < c.posLen := by
          have : (j + 1) * sqPer (osLvAt c i) ≤ (osLvAt c i).squeezes * sqPer (osLvAt c i) := Nat.mul_le_mul_right _ hj
          rw [Nat.add_mul, Nat.one_mul] at this
          simp only [sqPer] at this ht hj ⊢; omega
        have := regionL_lk_buf (b := b0) (Lin := Lin) hlen h11 (by decide)
          (t := (osLvAt c i).posOff + j * sqPer (osLvAt c i) + t) (by rw [hqlen]; exact h1)
        simpa only [Nat.add_assoc] using this)
      (fun t ht ↦ by
        obtain ⟨i', hi', hR⟩ := tabs_region hl0 (memL_lin_of_lk hm0) (fun rd hl hm ↦ (hLin rd hl hm).2) ht
        exact ⟨i', hi', regionL_lk_lin hR⟩)
      σ (mkCall σ (osDecCall c i)) (mkCall σ (osSqCall c i)) (by rw [mkCall_f]; rfl)
      (mkCall_taken_none σ rfl) (by rw [mkCall_args]; exact d1) (by rw [mkCall_rets]; rfl)
      (by rw [mkCall_f]; rfl) (mkCall_taken_some σ d2) (by rw [mkCall_args]; exact d3)
      (by rw [mkCall_rets]; rfl) le_rfl).toD
  · -- after the squeezes
    have hinB : ∀ c'' ∈ (osLvK σ c i).B, c'' ∈ ((osBodyA c).filterMap Stmt.callS).map (mkCall σ) :=
      fun c'' h ↦ hin c'' (List.mem_append_right _ (List.mem_append_right _ h))
    have hcB := hc'
    simp only [osLvK, lvB_callS, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton] at hc'
    rcases hc' with hc' | rfl
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
      obtain ⟨-, K, hK⟩ := hnamed x (List.all_eq_true.mp hnH x hx)
      exact completeAtD_lin_mono (os_kid_named (osCalleesRegD_holds hκ) (osRoundRegD_holds hκ) hall
        hex (hinB _ hcB) ht (by rw [mkCall_f]; exact hK))
        fun q hq ↦ List.mem_append_left _ (List.mem_append_left _ hq)
    · -- the queries
      obtain ⟨-, -, -, d4, d5⟩ := hSV.1 i hi
      obtain ⟨-, -, hHsl, hg0, hg1, hg5, hg11, hgHs, -⟩ := hSz
      have h0 : 0 < (osSizesF c).length := by have := osIxQbp_lt c; simp only [osIxQbp] at this; omega
      have h1 : 1 < (osSizesF c).length := by have := osIxQbp_lt c; simp only [osIxQbp] at this; omega
      have h5 : 5 < (osSizesF c).length := by have := osIxQbp_lt c; simp only [osIxQbp] at this; omega
      have h11 : 11 < (osSizesF c).length := by have := osIxQbp_lt c; simp only [osIxQbp] at this; omega
      have hdb := opening_queries_completeAtB fs cert _ (oqEntry_mem hent)
      simp only at hdb
      have e1 : (oqShapeOf (osQueriesName c i (osLvAt c i))).oq = oqS c i := rfl
      have e2 : (oqShapeOf (osQueriesName c i (osLvAt c i))).odd = oqOdd c i := rfl
      rw [e1, e2] at hdb
      set ehs := if i = c.yrLevel then osBaseF c b0 (osIxHsF c) else osBaseF c b0 8 + i * hsStride
        with hehs
      have hhs : osHsPtr c b0 i = ofK (addressOfIndex ehs) := by
        unfold osHsPtr
        split
        · next h => simp only [hehs, h, ↓reduceIte]; rfl
        · next h => simp only [hehs, h, ↓reduceIte, osPtrF_mul]
      have hst := H.static i hi
      have hq := os_q_completeAtB (fs := fs) (cert := cert) κ (lv := osLvAt c i) (L := c.sqLoop i)
        (s := oqS c i) (odd := oqOdd c i) hdb hpd
        hcd (n := (osLvAt c i).squeezes) (N := oqN c i) hN hQ (w := H.word i) (Lk := Lk)
        (ecap := osBaseF c b0 0 + 4 * (osLvAt c i).capOff) (eflags := osBaseF c b0 1 + (osLvAt c i).capOff)
        (ecoefs := osBaseF c b0 5 + 3 * (osLvAt c i).foldsOff) (ehs := ehs)
        (epos := osBaseF c b0 11 + (osLvAt c i).posOff) (eq := osBaseF c b0 osIxQbp) (lamInv := H.lamInv i)
        (H.rounds_len i hi) (H.hsv_len i hi) hst (H.qs_eq i hi) (fun rd hl hm ↦ ?_) ?_ p
      · rw [mkCall_f, mkCall_args, mkCall_rets]
        show CompleteAtD fs cert κ (osQCall c i).2.1 _ ((osQCall c i).2.2.1.map σ)
          (Returns ((osQCall c i).2.2.2.map σ))
        have ha : (osQCall c i).2.2.1.map σ = [ofK (addressOfIndex (osBaseF c b0 0 + 4 * (osLvAt c i).capOff)),
            ofK (addressOfIndex (osBaseF c b0 1 + (osLvAt c i).capOff)), H.lamInv i,
            ofK (addressOfIndex (osBaseF c b0 5 + 3 * (osLvAt c i).foldsOff)), ofK (addressOfIndex ehs),
            ofK (addressOfIndex (osBaseF c b0 11 + (osLvAt c i).posOff)),
            ofK (addressOfIndex (osBaseF c b0 osIxQbp + (osLvAt c i).posOff)), gen ^ oqN c i] := by
          rw [d4, osPtrF_mul, osPtrF_mul, osPtrF_mul, osPtrF_mul, osPtrF_mul, hhs]
        rw [ha, d5, H.batched_eq i hi]
        exact hq.toCompleteAtD
      · -- the queries' words
        have hM := osMemF_of_lk hlen hm
        obtain ⟨q1, q2, q3⟩ := H.qMem b0 rd hM i hi
        rw [osPtrF_mul] at q1
        refine ⟨q1, fun hf ↦ by rw [← hhs]; exact q2 hf, fun k hk ↦ ⟨?_, ?_⟩⟩
        · have hk' : k < (osLvAt c i).squeezes * sqPer (osLvAt c i) := lt_of_lt_of_le hk hQ
          have hper : 0 < sqPer (osLvAt c i) := by simp only [sqPer]; omega
          have hj : k / sqPer (osLvAt c i) < (osLvAt c i).squeezes := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
          have := H.posMem b0 rd hM i hi (k / sqPer (osLvAt c i)) hj (k % sqPer (osLvAt c i)) (Nat.mod_lt _ hper)
          rw [osPtrF, ofK_addr_shift, ← H.qs_eq i hi k hk] at this
          refine (loadHolds_ofK_iff ?_).mp this
          have := Nat.div_add_mod k (sqPer (osLvAt c i))
          rw [Nat.mul_comm] at this
          omega
        · obtain ⟨c1, c2, c3⟩ := q3 k hk
          rw [osPtrF_mul] at c1 c2 c3
          exact ⟨c1, c2, c3⟩
      · -- their addresses
        have hlen0 := forall₂_getD_len H.own_len h0
        have hlen1 := forall₂_getD_len H.own_len h1
        have hlen5 := forall₂_getD_len H.own_len h5
        have hlen11 := forall₂_getD_len H.own_len h11
        refine ⟨fun l' hl' ↦ ?_, fun hf l' hl' ↦ ?_, fun k hk ↦ ?_⟩
        · have := regionL_lk_buf (b := b0) (Lin := Lin) hlen h5 (by decide)
            (t := 3 * (osLvAt c i).foldsOff + l') (by rw [hlen5, hg5]; omega)
          simpa only [Nat.add_assoc] using this
        · have hyr : i = c.yrLevel := by
            by_contra h; simp only [hfin, h, ↓reduceIte] at hf; exact absurd hf (by decide)
          have hlenH := forall₂_getD_len H.own_len hHsl
          have := regionL_lk_buf (b := b0) (Lin := Lin) hlen hHsl (by unfold osIxHsF osIxQbp; omega)
            (t := l') (by rw [hlenH, hgHs, ← hyr]; have := hnhs hyr; omega)
          simp only [hehs, hyr, ↓reduceIte]
          exact this
        · obtain ⟨hql, -⟩ := hst k hk
          have hk' : k < (osLvAt c i).squeezes * sqPer (osLvAt c i) := lt_of_lt_of_le hk hQ
          have hcd1' := hcd1
          have hcd' := hcd
          generalize hpdv : (oqS c i).pd = pd at hql ⊢
          generalize hcdv : (oqS c i).cd = cd at hql hcd1' hcd' ⊢
          rw [← hcd'] at hcap4 hcap1
          have key : ∀ n, 1 ≤ n → 2 ^ n = 2 * 2 ^ (n - 1) := fun n hn ↦ by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rw [Nat.add_sub_cancel, pow_succ]; ring
          have hqd : H.qs i k / 2 ^ pd < 2 ^ cd := pow_div_lt' hql
          have hqf : H.qs i k / 2 ^ (pd + 1) < 2 ^ (cd - 1) :=
            pow_div_lt' (by rw [show pd + 1 + (cd - 1) = pd + cd by omega]; exact hql)
          have e1 : 2 ^ cd = 2 * 2 ^ (cd - 1) := key cd hcd1'
          have e2 : 2 ^ (cd + 2) = 4 * 2 ^ cd := by rw [pow_add]; ring
          refine ⟨?_, ?_, fun e he ↦ ?_⟩
          · have := regionL_lk_buf (b := b0) (Lin := Lin) hlen h11 (by decide)
              (t := (osLvAt c i).posOff + k) (by rw [hlen11, hg11]; simp only [sqPer] at hk'; omega)
            simpa only [Nat.add_assoc] using this
          · have := regionL_lk_buf (b := b0) (Lin := Lin) hlen h1 (by decide)
              (t := (osLvAt c i).capOff + (H.qs i k / 2 ^ (pd + 1) + 2 ^ (cd - 1)))
              (by rw [hlen1, hg1]; omega)
            simpa only [Nat.add_assoc] using this
          · have := regionL_lk_buf (b := b0) (Lin := Lin) hlen h0 (by decide)
              (t := 4 * (osLvAt c i).capOff + (2 * (2 ^ cd + H.qs i k / 2 ^ pd) + e))
              (by rw [hlen0, hg0]; omega)
            simpa only [Nat.add_assoc] using this

end
end LeanVM.Guest.B1
