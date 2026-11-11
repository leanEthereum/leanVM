/-
  LeanVM.Guest.B1.Whir.Squeezes

  The query positions of a level: the Spec's `sampleQueries` from the query grind's challenge, and
  the template's squeezes and decodes (`osSqueezes`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Commit

/-!
# The query positions (G:1605-1631)

* `sqPositions d w count`: query `k` is the position `k % P` of sample `k / P`, `P = 128 / d`
  (`qwPosOf`), the samples `w`;
* `sampleQueriesAux_run`: from a sponge with nothing waiting, `sampleQueriesAux` squeezes
  `⌈rem / P⌉` samples, the positions theirs; `sampleQueries_runG`: from a grind's ground challenge
  `c` and capacity `cap`, the first sample is `c`, the rest squeezed from `cap`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The Spec's positions -/

theorem RunsFromG.of_eq {α : Type} {p : VerifierProgram α} {cap : List E} {c : E} {xs xs' : List E}
    {a a' : α} {t t' : Fs} (h : RunsFromG p cap c xs a t) (hx : xs = xs') (ha : a = a')
    (ht : t = t') : RunsFromG p cap c xs' a' t' := by
  subst hx ha ht; exact h

/-- The positions of `count` queries of depth `d` from the samples `w`: query `k` is position
`k % P` of sample `k / P`, `P = 128 / d`. -/
def sqPositions (d : ℕ) (w : ℕ → E) (count : ℕ) : List ℕ :=
  (List.range count).map fun k ↦ qwPosOf d (w (k / (128 / d))) (k % (128 / d))

/-- The samples `rem` positions take, `⌈rem / P⌉`. -/
def sqCount (P rem : ℕ) : ℕ := (rem + P - 1) / P

theorem sqCount_zero (P : ℕ) (hP : 1 ≤ P) : sqCount P 0 = 0 := by
  unfold sqCount; rw [Nat.zero_add]; exact Nat.div_eq_of_lt (by omega)

theorem sqCount_step {P rem : ℕ} (hP : 1 ≤ P) (h0 : rem ≠ 0) :
    sqCount P rem = sqCount P (rem - min P rem) + 1 := by
  unfold sqCount
  by_cases hr : rem ≤ P
  · rw [min_eq_right hr, Nat.sub_self, Nat.zero_add,
      Nat.div_eq_of_lt (show P - 1 < P by omega), Nat.zero_add]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · rw [min_eq_left (by omega), show rem + P - 1 = rem - P + P - 1 + P by omega,
      Nat.add_div_right _ (by omega)]

/-- **`sampleQueriesAux` from a sponge with nothing waiting**: `⌈rem / P⌉` squeezes, the positions
theirs. -/
theorem sampleQueriesAux_run (d : ℕ) (hP : 1 ≤ 128 / d) :
    ∀ (fuel rem : ℕ) (F : Fs), rem ≤ 128 / d * fuel →
      RunsTo (sampleQueriesAux d fuel rem) F []
        (sqPositions d (fun j ↦ (F.squeezeN j).2.squeeze.1) rem)
        (F.squeezeN (sqCount (128 / d) rem)).2
  | 0, rem, F, h => by
    obtain rfl : rem = 0 := by simpa using h
    rw [sqCount_zero _ hP]
    exact runsTo_ret _ _
  | fuel + 1, rem, F, h => by
    by_cases h0 : rem = 0
    · subst h0
      rw [sqCount_zero _ hP]
      simp only [sampleQueriesAux, ↓reduceIte]
      exact runsTo_ret _ _
    · set P := 128 / d with hPd
      have hrest : rem - min P rem ≤ P * fuel := by
        rcases Nat.le_total rem P with hr | hr
        · rw [min_eq_right hr]; omega
        · rw [min_eq_left hr]; rw [Nat.mul_succ] at h; omega
      have ih := sampleQueriesAux_run d hP fuel (rem - min P rem) F.squeeze.2 hrest
      have hrun := (runsTo_sampleE F).bind (f := fun x ↦ do
          let rest ← sampleQueriesAux d fuel (rem - min P rem)
          return (List.range (min P rem)).map (fun c ↦ (eToNat x >>> (c * d)) % 2 ^ d) ++ rest)
        (ih.bind (f := fun rest ↦ (pure ((List.range (min P rem)).map
          (fun c ↦ (eToNat F.squeeze.1 >>> (c * d)) % 2 ^ d) ++ rest) : VerifierProgram (List ℕ)))
          (runsTo_ret _ _))
      simp only [sampleQueriesAux, h0, ↓reduceIte]
      refine RunsTo.of_eq hrun rfl rfl ?_ ?_
      · apply List.ext_getElem (by simp [sqPositions])
        intro k h1 h2
        simp only [sqPositions, List.getElem_map, List.getElem_range]
        by_cases hk : k < min P rem
        · rw [List.getElem_append_left (by simpa using hk)]
          simp only [List.getElem_map, List.getElem_range]
          have hkP : k < P := lt_of_lt_of_le hk (min_le_left _ _)
          rw [Nat.div_eq_of_lt hkP, Nat.mod_eq_of_lt hkP]
          rfl
        · rw [List.getElem_append_right (by simp only [List.length_map, List.length_range]; omega)]
          simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
          have hmin : min P rem = P := by
            simp only [sqPositions, List.length_map, List.length_range] at h2
            exact min_eq_left (by omega)
          rw [hmin] at hk ⊢
          obtain ⟨j, rfl⟩ : ∃ j, k = j + P := ⟨k - P, by omega⟩
          rw [Nat.add_sub_cancel, Nat.add_div_right _ (by omega), Nat.add_mod_right]
          rfl
      · rw [sqCount_step hP h0]
        rfl

/-- **`sampleQueries` from a grind's ground challenge** `c` at the capacity `cap`: the first
sample is `c`, the next squeezed from `cap`; `⌈count / P⌉` samples. -/
theorem sampleQueries_runG (d count : ℕ) (hP : 1 ≤ 128 / d) (hc : 0 < count) (cap : List E)
    (c : E) :
    RunsFromG (sampleQueries d count) cap c []
      (sqPositions d (fun j ↦ if j = 0 then c else
        (((⟨cap, []⟩ : Fs).squeezeN (j - 1)).2.squeeze.1)) count)
      ((⟨cap, []⟩ : Fs).squeezeN (sqCount (128 / d) count - 1)).2 := by
  obtain ⟨fuel, rfl⟩ : ∃ fuel, count = fuel + 1 := ⟨count - 1, by omega⟩
  set P := 128 / d with hPd
  have hrest : fuel + 1 - min P (fuel + 1) ≤ P * fuel := by
    rcases Nat.le_total (fuel + 1) P with hr | hr
    · rw [min_eq_right hr]; omega
    · rw [min_eq_left hr]
      have : P * fuel ≥ 1 * fuel := Nat.mul_le_mul_right _ hP
      omega
  have ih := sampleQueriesAux_run d hP fuel (fuel + 1 - min P (fuel + 1)) ⟨cap, []⟩ hrest
  have hrun := (runsFromG_sample cap c).bind (f := fun x ↦ do
      let rest ← sampleQueriesAux d fuel (fuel + 1 - min P (fuel + 1))
      return (List.range (min P (fuel + 1))).map (fun i ↦ (eToNat x >>> (i * d)) % 2 ^ d) ++ rest)
    (ih.bind (f := fun rest ↦ (pure ((List.range (min P (fuel + 1))).map
      (fun i ↦ (eToNat c >>> (i * d)) % 2 ^ d) ++ rest) : VerifierProgram (List ℕ)))
      (runsTo_ret _ _))
  simp only [sampleQueries, sampleQueriesAux, Nat.add_one_ne_zero, ↓reduceIte]
  refine RunsFromG.of_eq hrun rfl ?_ ?_
  · apply List.ext_getElem (by simp [sqPositions])
    intro k h1 h2
    simp only [sqPositions, List.getElem_map, List.getElem_range]
    by_cases hk : k < min P (fuel + 1)
    · rw [List.getElem_append_left (by simpa using hk)]
      simp only [List.getElem_map, List.getElem_range]
      have hkP : k < P := lt_of_lt_of_le hk (min_le_left _ _)
      rw [Nat.div_eq_of_lt hkP, Nat.mod_eq_of_lt hkP]
      rfl
    · rw [List.getElem_append_right (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      have hmin : min P (fuel + 1) = P := by
        simp only [sqPositions, List.length_map, List.length_range] at h2
        exact min_eq_left (by omega)
      rw [hmin] at hk ⊢
      obtain ⟨j, rfl⟩ : ∃ j, k = j + P := ⟨k - P, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right _ (by omega), Nat.add_mod_right]
      simp [hPd]
  · rw [sqCount_step hP (Nat.add_one_ne_zero fuel), Nat.add_sub_cancel]

/-! ## The template's squeezes -/

/-- Sample `j` of a level's positions: the query grind's challenge `w0`, then the squeezes from the
capacity `cap`. -/
def sqSample (w0 : E) (cap : List E) (j : ℕ) : E :=
  if j = 0 then w0 else ((⟨cap, []⟩ : Fs).squeezeN (j - 1)).2.squeeze.1

/-- The name of a level's `decode_query_windows`. -/
def decName (lv : OsLv) : String :=
  "decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth

/-- What a level's squeezes leave (G:1605-1631): sample `j < S` decoded at `posOff + j·P` of
`query_positions` and `query_win_ptrs`; the sponge after the `S - 1` squeezes. -/
structure SqOut (rd : Reader) (σ : Val) (lv : OsLv) (st st' : OsSt) (w0 : E) (cap : List E) :
    Prop where
  dec : ∀ j < lv.squeezes, MeaningDecodeQueryWindows lv.depth lv.capDepth rd
    [sqSample w0 cap j, σ (.n osQpos) * gen ^ (lv.posOff + j * (128 / lv.depth)),
      σ (.n osQbp) * gen ^ (lv.posOff + j * (128 / lv.depth)), σ (.n osTabs)] []
  F : st'.F σ = ((⟨cap, []⟩ : Fs).squeezeN (lv.squeezes - 1)).2
  fs : st'.fs.length = 5
  mats : MatsOk σ st'.mats
  cur : st'.cur σ = st.cur σ
  co : st'.co = st.co
  claim : st'.claim = st.claim
  pad : st'.pad = st.pad

/-- **A level's squeezes, soundly** (G:1605-1631): from the capacity `cap` the guest carries (the
query grind's permutation's) and its challenge `w0`. -/
theorem osSqueezes_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hle : CallRel.Le C (coreProgram.Rel rd))
    (hdec : ∀ a r, WinTabs rd (a.getD 3 0) → coreProgram.Rel rd (decName lv) a r →
      MeaningDecodeQueryWindows lv.depth lv.capDepth rd a r)
    (hsq : FnIs (c.sqLoop lvl) (osParams 6) (sqLoopBody lv (c.sqLoop lvl)))
    (hpw : digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth)
    (hpo : lv.posOff < u128Bound) (hS : 1 ≤ lv.squeezes) (hSo : lv.squeezes < ordG)
    (hS5 : lv.squeezes * 5 < u128Bound) (hwt : WinTabs rd (σ (.n osTabs)))
    (hm : MatsOk σ st.mats) (hfs : st.fs.length = 5) {cap : List E} (hF : st.F σ = ⟨cap, []⟩) {w0 : E}
    (hw0 : σ (.n st.word0) = w0) (hok : AllOk C rd σ (osSqueezes c lvl lv st).1) :
    SqOut rd σ lv st (osSqueezes c lvl lv st).2 w0 cap := by
  unfold osSqueezes at hok ⊢
  simp only [allOk_append, and_assoc] at hok
  obtain ⟨-, hst, hqp, hwp, hdc, hlp, hlast⟩ := hok
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  have hcap : cap = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    have := congrArg Fs.cap hF
    simp only [OsSt.F, hf, List.map_cons, List.map_nil] at this
    exact this.symm
  subst hcap
  rw [hf] at hst
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons, allOk_nil,
    and_true, stmtOk_atom, holds_load, osLd, Nat.zero_add] at hst
  obtain ⟨l0, l1, l2, l3, l4⟩ := hst
  set sqz := st.k + 1 with hsqz
  obtain ⟨eqp, hmq⟩ := osMatS_val' hqp hm hpo
  obtain ⟨ewp, hmw⟩ := osMatS_val' hwp hmq hpo
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil] at hdc
  have hD0 := hdec _ _ (by simpa using hwt) (hle _ _ _ hdc)
  rw [eqp, ewp, hw0] at hD0
  set l := (osMatS c.plan osQbp lv.posOff (osMatS c.plan osQpos lv.posOff
    { st with k := st.k + 2 }).2.2).2.2.k with hl
  simp only [osLoopCall, allOk_cons, allOk_nil, and_true, holds_const, holds_add, osCst, osAdd,
    StmtOk, List.map_cons, List.map_nil] at hlp
  obtain ⟨g1, gS, gsum, g3, g4, -, hcall⟩ := hlp
  have hg1 : gw 1 = gen ^ 1 := gw_eq (by decide)
  have hgS : gw lv.squeezes = gen ^ lv.squeezes := gw_eq (lt_trans (by omega) hS5)
  set cap := [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] with hcapd
  have h0 : ∀ i < 5, LoadHolds rd (σ (.n sqz)) (5 * 1 + i) (cap.getD i 0) := by
    intro i hi
    interval_cases i
    exacts [l0, l1, l2, l3, l4]
  have hit : ∀ j, 1 ≤ j → j < 1 + (lv.squeezes - 1) →
      SqIter rd lv.depth lv.capDepth lv.posOff (σ (.n sqz)) (σ (.n osQpos)) (σ (.n osQbp))
        (σ (.n osTabs)) (gen ^ j) := by
    intro j h1 h2
    obtain ⟨fn, hfind, hps, hbody⟩ := hsq
    refine sqLoop_sound hfind lv hps hbody hpw hpo hdec (e := 1) (by omega) hSo _ _ _ _ hwt
      (fun hne ↦ ?_) j h1 (by omega)
    have := hle _ _ _ (hcall (by rw [gsum, g1, gS, hg1, hgS]; exact hne))
    rwa [g3, g4, hg1, hgS] at this
  obtain ⟨hrows, hdecs⟩ := sqChain cap rfl h0 hit
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_mul,
    holds_load, osCst, osMul, osLd, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, and_assoc] at hlast
  obtain ⟨e5, e6, m0, m1, m2, m3, m4⟩ := hlast
  have hS5' : gw (lv.squeezes * 5) = gen ^ (lv.squeezes * 5) := gw_eq hS5
  have hoff : 5 * (1 + (lv.squeezes - 1)) = lv.squeezes * 5 := by omega
  have hrowE : ∀ i < 5, LoadHolds rd (σ (.n sqz)) (5 * (1 + (lv.squeezes - 1)) + i)
      ([σ (.n (l + 7)), σ (.n (l + 8)), σ (.n (l + 9)), σ (.n (l + 10)), σ (.n (l + 11))].getD i 0) := by
    intro i hi
    rw [hoff, ← loadHolds_mul_gen_pow, ← hS5', ← e5, ← e6]
    interval_cases i
    exacts [m0, m1, m2, m3, m4]
  have hcl : ((⟨cap, []⟩ : Fs).squeezeN (lv.squeezes - 1)).2.cap.length = 5 := by
    rcases h : lv.squeezes - 1 with _ | n
    · rfl
    · rw [squeezeN_snoc]; simp [Fs.squeeze, capOf]
  have hfin := five_eq (by rfl) hcl hrowE (hrows _ le_rfl)
  dsimp only
  refine ⟨fun j hj ↦ ?_, ?_, rfl, hmw, rfl, rfl, rfl, rfl⟩
  · rcases j with _ | j
    · simpa [sqSample] using hD0
    · have := hdecs j (by omega)
      simpa [sqSample, Nat.add_comm 1 j] using this
  · refine (fs_mk_eq ?_ (squeezeN_pend rfl _)).symm
    rw [← hfin]
    rfl

end
end LeanVM.Guest.B1.Whir
