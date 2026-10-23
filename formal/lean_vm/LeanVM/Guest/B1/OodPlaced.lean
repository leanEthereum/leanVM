/-
  LeanVM.Guest.B1.OodPlaced

  `opening_ood_point` placed: its states' run its own `HeapBuf`, its loop `__loop9` after it.
-/

module

public import LeanVM.Guest.B1.OpeningOod
public import LeanVM.Guest.B1.G1Placed
public import LeanVM.Guest.B1.Whir.OsCallees
public import LeanVM.Guest.B1.Da.Atoms
public import LeanVM.Guest.Memory.LoopPre

/-!
# `opening_ood_point`, placed (TRIAGE #32)

At frame position `fp` the states' run is the `HeapBuf` of `2m + 2` words at `fp + fs f`
(`allocDyn` of `g^(2m+2)`, which needs `2m + 2` below the order of `g`), holding the state after
each squeeze (`oodStates`); `__loop9`, pure, is placed after it, reading the run and the caller's
point. The challenges at `point` are pinned by `sampleN`'s determinism, so on every memory defined
below `2^k` holding the caller's words they lie in those words (`readsAt_lift`).

`ood_holds`: the honest valuation (`opening_ood_point_iff`'s, kept explicit);
`opening_ood_point_completeRel`: the placed form on `OodPointPre` (`Whir/OsCallees.lean`), the
meaning without the states' run, `2m + 2 < ordG`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The honest valuation -/

/-- The honest valuation at the states' run `p`, returning `r0`, `r1`. -/
noncomputable def oodVal (fs0 fs1 point ng p r0 r1 : E) : Val :=
  setl (Val.ofArgs [fs0, fs1, point, ng]) 4 [gen, ng * gen, ng * gen * (ng * gen), p,
    1, 1 + ng, 1, p * ng, p * ng * ng, r0, r1]

theorem ood_holds (rd : Reader) (fs0 fs1 point ng p r0 r1 : E) (m : ℕ) (hN : ng = gen ^ m)
    (l0 : LoadHolds rd p 0 fs0) (l1 : LoadHolds rd p 1 fs1) (l13 : LoadHolds rd p (2 * m) r0)
    (l14 : LoadHolds rd p (2 * m + 1) r1) (hK : IsInK (1 + ng))
    (hcall : 1 + ng ≠ 0 → coreProgram.Rel rd "__loop9" [1, ng, p, point] []) :
    (Fn.params Data.core9).map (oodVal fs0 fs1 point ng p r0 r1) = [fs0, fs1, point, ng] ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd (oodVal fs0 fs1 point ng p r0 r1) (Fn.body Data.core9)
        False (fun rs => rs = [r0, r1]) := by
  rw [show Fn.params Data.core9 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    show Fn.body Data.core9 = Data.core9.body from rfl, Data.core9.body]
  unfold oodVal
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_one,
    word_gen, true_and]
  have hx : ∀ k w, LoadHolds rd (p * ng * ng) k w ↔ LoadHolds rd p (2 * m + k) w := by
    intro k w
    rw [hN, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, ← two_mul]
  refine ⟨?_, ?_⟩
  · b1_look
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · exact l0
    · exact l1
    · exact hK
    · exact hcall
    · exact (hx 0 _).mpr l13
    · exact (hx 1 _).mpr l14

/-! ## The body's path -/

/-- `opening_ood_point`'s statements before its return. -/
def oodPre : List Stmt :=
  [.atom (.const (.n 4) (word 2 0 0)), .atom (.mul (.n 5) (.n 3) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.hint (.allocDyn (.n 7) (.n 6))),
    .atom (.load (.n 0) (.n 7) 0), .atom (.load (.n 1) (.n 7) 1), .atom (.const (.n 8) (word 1 0 0)),
    .atom (.add (.n 9) (.n 8) (.n 3)), .atom (.const (.n 10) (word 1 0 0)),
    .callIf (.n 9) "__loop9" [.n 10, .n 3, .n 7, .n 2], .atom (.mul (.n 11) (.n 7) (.n 3)),
    .atom (.mul (.n 12) (.n 11) (.n 3)), .atom (.load (.n 13) (.n 12) 0),
    .atom (.load (.n 14) (.n 12) 1)]

theorem core9_body_eq : Fn.body Data.core9 = oodPre ++ [.ret [.n 13, .n 14]] := rfl

theorem oodPre_shape : oodPre.all Main.Stmt.straight = true ∧
    oodPre.filterMap Main.Stmt.allocSz = [(.n 7, .inr (.n 6))] ∧ oodPre.filterMap Main.Stmt.addrS = [] ∧
    oodPre.filterMap Main.Stmt.callS = [(some (.n 9), "__loop9", [.n 10, .n 3, .n 7, .n 2], [])] ∧
    oodPre.filterMap Stmt.loadS = [(.n 7, 0), (.n 7, 1), (.n 12, 0), (.n 12, 1)] := by
  decide +kernel

/-- The states' run: the state after each of the `m` squeezes from `cv`, two words each. -/
def oodStates (cv : Digest) (m : ℕ) : List E :=
  (List.range (m + 1)).flatMap fun j => [(digestScalars (sqAll j cv).2).1, (digestScalars (sqAll j cv).2).2]

theorem ood_pairs_facts (f g : ℕ → E) : ∀ n, ((List.range n).flatMap fun c => [f c, g c]).length = 2 * n ∧
    ∀ j < n, ((List.range n).flatMap fun c => [f c, g c]).getD (2 * j) 0 = f j ∧
      ((List.range n).flatMap fun c => [f c, g c]).getD (2 * j + 1) 0 = g j
  | 0 => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hl, hg⟩ := ood_pairs_facts f g n
    rw [List.range_succ, List.flatMap_append]
    refine ⟨by simp [hl]; ring, fun j hj => ?_⟩
    by_cases hjn : j < n
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hg j hjn
    · obtain rfl : j = n := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl,
        Nat.sub_self, show 2 * j + 1 - 2 * j = 1 by omega]
      exact ⟨rfl, rfl⟩

theorem length_oodStates (cv : Digest) (m : ℕ) : (oodStates cv m).length = 2 * m + 2 :=
  (ood_pairs_facts _ _ (m + 1)).1

theorem oodStates_getD (cv : Digest) (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    (oodStates cv m).getD (2 * j) 0 = (digestScalars (sqAll j cv).2).1 ∧
      (oodStates cv m).getD (2 * j + 1) 0 = (digestScalars (sqAll j cv).2).2 :=
  (ood_pairs_facts _ _ (m + 1)).2 j (by omega)

theorem find_loop9_pure : coreProgram.PureIn ["__loop9"] := g1_pure_one find_loop9 (by decide +kernel)

theorem not_loop_ood : coreProgram.loop "opening_ood_point" = false := by
  rw [Program.loop_of_find? find_opening_ood_point]; decide +kernel

/-! ## The placed form -/

theorem g1_loadHolds_of_memL {rd : Reader} {b : ℕ} {xs : List E} (h : MemL rd [(b, xs)]) {j : ℕ}
    (hj : j < xs.length) : LoadHolds rd (ofK (Parameters.gpow b)) j (xs.getD j 0) := by
  rw [List.getD_eq_getElem _ _ hj]; exact h _ List.mem_cons_self j hj

theorem ood_one_add_ne {m : ℕ} (hm : m < ordG) (h0 : 0 < m) : 1 + gen ^ m ≠ 0 := by
  intro h
  rw [e_add_eq_zero_iff, ← pow_zero gen] at h
  have := gen_pow_inj hm (by decide) h.symm
  omega

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)

/-- **`opening_ood_point`, placed**: on `OodPointPre`, it returns the final state's cells and no buffer,
its states' run its own `HeapBuf`. -/
theorem opening_ood_point_completeRel : CompleteRel fs cert k "opening_ood_point" OodPointPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨fs0, fs1, point, ng, rfl⟩ : ∃ fs0 fs1 point ng, args = [fs0, fs1, point, ng] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨m, hm, hm2, hN, hcase⟩ := hpre rd1 hl1 hL1
  set b0 := fp + fs "opening_ood_point" with hb0
  set p : E := ofK (Parameters.gpow b0) with hpdef
  obtain ⟨st, r0, r1, hst, hrets, s0, s1, sr0, sr1, hloop⟩ : ∃ (st : List E) (r0 r1 : E),
      st.length = 2 * m + 2 ∧ rets = [r0, r1] ∧ st.getD 0 0 = fs0 ∧ st.getD 1 0 = fs1 ∧
      st.getD (2 * m) 0 = r0 ∧ st.getD (2 * m + 1) 0 = r1 ∧
      (0 < m → ∀ rd, MemL rd ([(b0, st)] ++ Lin) → coreProgram.Rel rd "__loop9" [1, ng, p, point] []) := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨h0, cv, rs, cv', hcv, hrun, -, rfl⟩
    · exact ⟨[fs0, fs1], fs0, fs1, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
    · obtain ⟨rfl, rfl⟩ := (runsTo_sampleN m cv).iff.mp hrun
      have hpt : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd point (sqAll m cv).1 := by
        intro rd hl hL
        obtain ⟨m', hm', -, hN', hc'⟩ := hpre rd hl hL
        have hmm : m' = m := gen_pow_inj hm' hm (hN'.symm.trans hN)
        subst hmm
        rcases hc' with ⟨h0', -⟩ | ⟨-, cv2, rs2, cv2', hcv2, hrun2, hpt2, -⟩
        · omega
        · obtain rfl : cv2 = cv := digestScalars_injective (hcv2.symm.trans hcv)
          obtain ⟨rfl, -⟩ := (runsTo_sampleN m' cv2).iff.mp hrun2
          exact hpt2
      have hpt' := (readsAt_lift hl1 hL1 hpt).2
      obtain ⟨g0, g1⟩ := oodStates_getD cv m (Nat.zero_le m)
      obtain ⟨gm0, gm1⟩ := oodStates_getD cv m le_rfl
      refine ⟨oodStates cv m, _, _, length_oodStates cv m, rfl, ?_, ?_, gm0, gm1, fun _ rd hM => ?_⟩
      · rw [g0]; exact (congrArg Prod.fst hcv).symm
      · rw [g1]; exact (congrArg Prod.snd hcv).symm
      · obtain ⟨hS, hL⟩ := Main.memL_append.mp hM
        have hsc : OodScratch rd p cv m := fun j hj => by
          obtain ⟨a0, a1⟩ := oodStates_getD cv m hj
          rw [← a0, ← a1]
          exact ⟨g1_loadHolds_of_memL hS (by rw [length_oodStates]; omega),
            g1_loadHolds_of_memL hS (by rw [length_oodStates]; omega)⟩
        exact ((guarded_loop_iff (loop9_step rd ng p point)).mpr ⟨m, hm, hN,
          (loop9_bodies_iff rd p point m h0).mpr ⟨cv, hsc, hpt' rd hL⟩⟩).2
          (by rw [hN]; exact ood_one_add_ne hm h0)
  have hLoopC : 0 < m → CompleteAt fs cert k "__loop9" ([(b0, st)] ++ Lin) [1, ng, p, point] (Returns []) :=
    fun h0 => completeAt_of_rel_pure find_loop9_pure (by simp) (hloop h0) k
  set b := b0 + (2 * m + 2) with hbdef
  obtain ⟨nl, Ll, hWl, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ (0 < m → ∀ rd,
      LowDef k rd → MemL rd ([] ++ Ll ++ ([(b0, st)] ++ Lin)) →
        RelAtIn coreProgram fs cert rd (RegionL ([(b0, st)] ++ Lin)) (RegionL []) b nl "__loop9"
          [1, ng, p, point] []) ∧ (m = 0 → nl = fs "__loop9") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hr⟩ := hLoopC h0 b
      exact ⟨n', Lo, by simpa using hw, fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop9", [], by simp [Within], fun h => absurd h h0, fun _ => rfl⟩
  refine ⟨fs "opening_ood_point" + (2 * m + 2) + nl, [(b0, st)] ++ Ll, [r0, r1], [], ⟨hrets.symm, rfl⟩,
    ?_, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    refine ⟨fun q hq => ?_, hWl.mono (by omega) (by omega)⟩
    rw [List.mem_singleton] at hq
    subst hq
    simp only [hst]
    omega
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hS, hLl⟩ := Main.memL_append.mp hM1
  have l0 : LoadHolds rd p 0 fs0 := s0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l1 : LoadHolds rd p 1 fs1 := s1 ▸ g1_loadHolds_of_memL hS (by omega)
  have l13 : LoadHolds rd p (2 * m) r0 := sr0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l14 : LoadHolds rd p (2 * m + 1) r1 := sr1 ▸ g1_loadHolds_of_memL hS (by omega)
  have hK : IsInK (1 + ng) := by
    rw [hN]; exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
  have hcall : 1 + ng ≠ 0 → coreProgram.Rel rd "__loop9" [1, ng, p, point] [] := fun hne =>
    hloop (by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hN, h, pow_zero]; exact e_add_self 1) hne
      · exact h) rd (Main.memL_append.mpr ⟨hS, hLin⟩)
  obtain ⟨hpar, hh⟩ := ood_holds rd fs0 fs1 point ng p r0 r1 m hN l0 l1 l13 l14 hK hcall
  set τ := oodVal fs0 fs1 point ng p r0 r1 with hτ
  have t7 : τ (.n 7) = p := by simp only [hτ, oodVal]; b1_look
  have t9 : τ (.n 9) = 1 + ng := by simp only [hτ, oodVal]; b1_look
  have t10 : τ (.n 10) = 1 := by simp only [hτ, oodVal]; b1_look
  have t3 : τ (.n 3) = ng := by simp only [hτ, oodVal]; b1_look
  have t2 : τ (.n 2) = point := by simp only [hτ, oodVal]; b1_look
  have t6 : τ (.n 6) = ng * gen * (ng * gen) := by simp only [hτ, oodVal]; b1_look
  have t12 : τ (.n 12) = p * ng * ng := by simp only [hτ, oodVal]; b1_look
  have t13 : τ (.n 13) = r0 := by simp only [hτ, oodVal]; b1_look
  have t14 : τ (.n 14) = r1 := by simp only [hτ, oodVal]; b1_look
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core9) = true :=
    coreProgram_wf Data.core9 (List.mem_of_find?_eq_some find_opening_ood_point)
  rw [core9_body_eq] at hwf hh
  obtain ⟨hstr, hal, had, hca, hlo⟩ := oodPre_shape
  have hw := Main.walk_straight τ [.n 13, .n 14] oodPre hstr
  have hs := walk_sat _ hwf hh
  rw [hw] at hs
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ oodPre hstr
  rw [hal] at e1 e2
  rw [had] at e3
  rw [hca] at e4
  have h6 : logG (τ (.n 6)) = 2 * m + 2 := by
    rw [t6, hN, show gen ^ m * gen * (gen ^ m * gen) = gen ^ (2 * m + 2) by ring, gen_pow_eq_ofK]
    exact logG_spec hm2
  simp only [List.map_cons, List.map_nil, Sum.elim_inr, h6] at e1 e2
  have hp12 : τ (.n 12) = gen ^ (b0 + 2 * m) := by
    rw [t12, hpdef, hN, ← gen_pow_eq_ofK]; ring
  have hbuf : ∀ i, b0 ≤ i → i < b0 + (2 * m + 2) → ownData cert fp (fp + fs "opening_ood_point")
      "opening_ood_point" [2 * m + 2] (oodPre.flatMap (Main.slEvs τ)) i := fun i h1 h2 =>
    Or.inl ⟨(2 * m + 2, b0), by simp [bases, hb0], h1, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (args := [fs0, fs1, point, ng])
    (rets := [r0, r1]) coreProgram_wf find_opening_ood_point (Or.inl not_loop_ood) hpar
    (by rw [core9_body_eq]; exact hw) (by simp [t13, t14]) (fun e he => (hs.1 e he).1)
    (by rw [e1, e2]; simp [bases, t7, hpdef, hb0])
    (fun q hq => by rw [e3] at hq; exact absurd hq List.not_mem_nil)
    (by
      rw [show calls (oodPre.flatMap (Main.slEvs τ)) =
        [⟨"__loop9", [.n 10, .n 3, .n 7, .n 2], [], decide (τ (.n 9) ≠ 0)⟩] from e4.trans rfl, e2]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL ([(b0, st)] ++ Lin), RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rcases List.mem_append.mp hq with hq | hq
        · rw [List.mem_singleton] at hq
          subst hq
          exact Or.inl (Or.inr (hbuf i h1 (by rw [hst] at h2; exact h2)))
        · exact Or.inl (Or.inl ⟨q, hq, h1, h2⟩)
      · by_cases h0 : 0 < m
        · have hne : τ (.n 9) ≠ 0 := by rw [t9, hN]; exact ood_one_add_ne hm h0
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t10, t3, t7, t2]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, Main.memL_append.mpr ⟨hS, hLin⟩⟩)
        · have hz : τ (.n 9) = 0 := by
            rw [t9, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by
      rw [e2]
      rw [loadAddrs_straight τ oodPre hstr, hlo] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact ⟨b0 + 0, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 1, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 0, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 1, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h

/-- **`opening_ood_point`, placed**: on `OodPointPre`, it returns the final state's cells and no buffer,
its states' run its own `HeapBuf`. -/
theorem opening_ood_point_completeRelD : CompleteRelD fs cert k "opening_ood_point" OodPointPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨fs0, fs1, point, ng, rfl⟩ : ∃ fs0 fs1 point ng, args = [fs0, fs1, point, ng] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨m, hm, hm2, hN, hcase⟩ := hpre rd1 hl1 hL1
  set b0 := fp + fs "opening_ood_point" with hb0
  set p : E := ofK (Parameters.gpow b0) with hpdef
  obtain ⟨st, r0, r1, hst, hrets, s0, s1, sr0, sr1, hloop⟩ : ∃ (st : List E) (r0 r1 : E),
      st.length = 2 * m + 2 ∧ rets = [r0, r1] ∧ st.getD 0 0 = fs0 ∧ st.getD 1 0 = fs1 ∧
      st.getD (2 * m) 0 = r0 ∧ st.getD (2 * m + 1) 0 = r1 ∧
      (0 < m → ∀ rd, MemL rd ([(b0, st)] ++ Lin) → coreProgram.Rel rd "__loop9" [1, ng, p, point] []) := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨h0, cv, rs, cv', hcv, hrun, -, rfl⟩
    · exact ⟨[fs0, fs1], fs0, fs1, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
    · obtain ⟨rfl, rfl⟩ := (runsTo_sampleN m cv).iff.mp hrun
      have hpt : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd point (sqAll m cv).1 := by
        intro rd hl hL
        obtain ⟨m', hm', -, hN', hc'⟩ := hpre rd hl hL
        have hmm : m' = m := gen_pow_inj hm' hm (hN'.symm.trans hN)
        subst hmm
        rcases hc' with ⟨h0', -⟩ | ⟨-, cv2, rs2, cv2', hcv2, hrun2, hpt2, -⟩
        · omega
        · obtain rfl : cv2 = cv := digestScalars_injective (hcv2.symm.trans hcv)
          obtain ⟨rfl, -⟩ := (runsTo_sampleN m' cv2).iff.mp hrun2
          exact hpt2
      have hpt' := (readsAt_lift hl1 hL1 hpt).2
      obtain ⟨g0, g1⟩ := oodStates_getD cv m (Nat.zero_le m)
      obtain ⟨gm0, gm1⟩ := oodStates_getD cv m le_rfl
      refine ⟨oodStates cv m, _, _, length_oodStates cv m, rfl, ?_, ?_, gm0, gm1, fun _ rd hM => ?_⟩
      · rw [g0]; exact (congrArg Prod.fst hcv).symm
      · rw [g1]; exact (congrArg Prod.snd hcv).symm
      · obtain ⟨hS, hL⟩ := Main.memL_append.mp hM
        have hsc : OodScratch rd p cv m := fun j hj => by
          obtain ⟨a0, a1⟩ := oodStates_getD cv m hj
          rw [← a0, ← a1]
          exact ⟨g1_loadHolds_of_memL hS (by rw [length_oodStates]; omega),
            g1_loadHolds_of_memL hS (by rw [length_oodStates]; omega)⟩
        exact ((guarded_loop_iff (loop9_step rd ng p point)).mpr ⟨m, hm, hN,
          (loop9_bodies_iff rd p point m h0).mpr ⟨cv, hsc, hpt' rd hL⟩⟩).2
          (by rw [hN]; exact ood_one_add_ne hm h0)
  have hLoopC : 0 < m → CompleteAtD fs cert k "__loop9" ([(b0, st)] ++ Lin) [1, ng, p, point] (Returns []) :=
    fun h0 => completeAt_of_rel_pureD find_loop9_pure (by simp) (hloop h0) k
  set b := b0 + (2 * m + 2) with hbdef
  obtain ⟨nl, Ll, hWl, hDl, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ DisjL Ll ∧ (0 < m → ∀ rd,
      LowDef k rd → MemL rd ([] ++ Ll ++ ([(b0, st)] ++ Lin)) →
        RelAtIn coreProgram fs cert rd (RegionL ([(b0, st)] ++ Lin)) (RegionL []) b nl "__loop9"
          [1, ng, p, point] []) ∧ (m = 0 → nl = fs "__loop9") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hd, hr⟩ := hLoopC h0 b
      exact ⟨n', Lo, by simpa using hw, by simpa using hd, fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop9", [], by simp [Within], disj_nil, fun h => absurd h h0, fun _ => rfl⟩
  refine ⟨fs "opening_ood_point" + (2 * m + 2) + nl, [(b0, st)] ++ Ll, [r0, r1], [], ⟨hrets.symm, rfl⟩,
    ?_, ?_, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    refine ⟨fun q hq => ?_, hWl.mono (by omega) (by omega)⟩
    rw [List.mem_singleton] at hq
    subst hq
    simp only [hst]
    omega
  · rw [List.nil_append]
    refine disj_append (by simp [DisjL]) hDl (fun q hq => ?_) hWl le_rfl
    rw [List.mem_singleton] at hq
    subst hq
    simp only [hst]
    omega
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hS, hLl⟩ := Main.memL_append.mp hM1
  have l0 : LoadHolds rd p 0 fs0 := s0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l1 : LoadHolds rd p 1 fs1 := s1 ▸ g1_loadHolds_of_memL hS (by omega)
  have l13 : LoadHolds rd p (2 * m) r0 := sr0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l14 : LoadHolds rd p (2 * m + 1) r1 := sr1 ▸ g1_loadHolds_of_memL hS (by omega)
  have hK : IsInK (1 + ng) := by
    rw [hN]; exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
  have hcall : 1 + ng ≠ 0 → coreProgram.Rel rd "__loop9" [1, ng, p, point] [] := fun hne =>
    hloop (by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hN, h, pow_zero]; exact e_add_self 1) hne
      · exact h) rd (Main.memL_append.mpr ⟨hS, hLin⟩)
  obtain ⟨hpar, hh⟩ := ood_holds rd fs0 fs1 point ng p r0 r1 m hN l0 l1 l13 l14 hK hcall
  set τ := oodVal fs0 fs1 point ng p r0 r1 with hτ
  have t7 : τ (.n 7) = p := by simp only [hτ, oodVal]; b1_look
  have t9 : τ (.n 9) = 1 + ng := by simp only [hτ, oodVal]; b1_look
  have t10 : τ (.n 10) = 1 := by simp only [hτ, oodVal]; b1_look
  have t3 : τ (.n 3) = ng := by simp only [hτ, oodVal]; b1_look
  have t2 : τ (.n 2) = point := by simp only [hτ, oodVal]; b1_look
  have t6 : τ (.n 6) = ng * gen * (ng * gen) := by simp only [hτ, oodVal]; b1_look
  have t12 : τ (.n 12) = p * ng * ng := by simp only [hτ, oodVal]; b1_look
  have t13 : τ (.n 13) = r0 := by simp only [hτ, oodVal]; b1_look
  have t14 : τ (.n 14) = r1 := by simp only [hτ, oodVal]; b1_look
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core9) = true :=
    coreProgram_wf Data.core9 (List.mem_of_find?_eq_some find_opening_ood_point)
  rw [core9_body_eq] at hwf hh
  obtain ⟨hstr, hal, had, hca, hlo⟩ := oodPre_shape
  have hw := Main.walk_straight τ [.n 13, .n 14] oodPre hstr
  have hs := walk_sat _ hwf hh
  rw [hw] at hs
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ oodPre hstr
  rw [hal] at e1 e2
  rw [had] at e3
  rw [hca] at e4
  have h6 : logG (τ (.n 6)) = 2 * m + 2 := by
    rw [t6, hN, show gen ^ m * gen * (gen ^ m * gen) = gen ^ (2 * m + 2) by ring, gen_pow_eq_ofK]
    exact logG_spec hm2
  simp only [List.map_cons, List.map_nil, Sum.elim_inr, h6] at e1 e2
  have hp12 : τ (.n 12) = gen ^ (b0 + 2 * m) := by
    rw [t12, hpdef, hN, ← gen_pow_eq_ofK]; ring
  have hbuf : ∀ i, b0 ≤ i → i < b0 + (2 * m + 2) → ownData cert fp (fp + fs "opening_ood_point")
      "opening_ood_point" [2 * m + 2] (oodPre.flatMap (Main.slEvs τ)) i := fun i h1 h2 =>
    Or.inl ⟨(2 * m + 2, b0), by simp [bases, hb0], h1, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (args := [fs0, fs1, point, ng])
    (rets := [r0, r1]) coreProgram_wf find_opening_ood_point (Or.inl not_loop_ood) hpar
    (by rw [core9_body_eq]; exact hw) (by simp [t13, t14]) (fun e he => (hs.1 e he).1)
    (by rw [e1, e2]; simp [bases, t7, hpdef, hb0])
    (fun q hq => by rw [e3] at hq; exact absurd hq List.not_mem_nil)
    (by
      rw [show calls (oodPre.flatMap (Main.slEvs τ)) =
        [⟨"__loop9", [.n 10, .n 3, .n 7, .n 2], [], decide (τ (.n 9) ≠ 0)⟩] from e4.trans rfl, e2]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL ([(b0, st)] ++ Lin), RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rcases List.mem_append.mp hq with hq | hq
        · rw [List.mem_singleton] at hq
          subst hq
          exact Or.inl (Or.inr (hbuf i h1 (by rw [hst] at h2; exact h2)))
        · exact Or.inl (Or.inl ⟨q, hq, h1, h2⟩)
      · by_cases h0 : 0 < m
        · have hne : τ (.n 9) ≠ 0 := by rw [t9, hN]; exact ood_one_add_ne hm h0
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t10, t3, t7, t2]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, Main.memL_append.mpr ⟨hS, hLin⟩⟩)
        · have hz : τ (.n 9) = 0 := by
            rw [t9, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by
      rw [e2]
      rw [loadAddrs_straight τ oodPre hstr, hlo] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact ⟨b0 + 0, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 1, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 0, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 1, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h

/-- **`opening_ood_point`, placed**: on `OodPointPre`, it returns the final state's cells and no buffer,
its states' run its own `HeapBuf`. -/
theorem opening_ood_point_completeRelB  (B9 : E → ℕ)
    (h9 : TotalLeOn coreProgram fs "__loop9" LoopPre fun a => B9 (a.getD 1 0)) :
    ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, LowDef k rd → MemL rd Lin → OodPointPre rd args rets) →
      CompleteAtB fs cert k "opening_ood_point" Lin args (Returns rets)
        (fs "opening_ood_point" + (2 * logG (args.getD 3 0) + 2) + max (B9 (args.getD 3 0)) (fs "__loop9")) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨fs0, fs1, point, ng, rfl⟩ : ∃ fs0 fs1 point ng, args = [fs0, fs1, point, ng] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨m, hm, hm2, hN, hcase⟩ := hpre rd1 hl1 hL1
  set b0 := fp + fs "opening_ood_point" with hb0
  set p : E := ofK (Parameters.gpow b0) with hpdef
  obtain ⟨st, r0, r1, hst, hrets, s0, s1, sr0, sr1, hloop⟩ : ∃ (st : List E) (r0 r1 : E),
      st.length = 2 * m + 2 ∧ rets = [r0, r1] ∧ st.getD 0 0 = fs0 ∧ st.getD 1 0 = fs1 ∧
      st.getD (2 * m) 0 = r0 ∧ st.getD (2 * m + 1) 0 = r1 ∧
      (0 < m → ∀ rd, MemL rd ([(b0, st)] ++ Lin) → coreProgram.Rel rd "__loop9" [1, ng, p, point] []) := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨h0, cv, rs, cv', hcv, hrun, -, rfl⟩
    · exact ⟨[fs0, fs1], fs0, fs1, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
    · obtain ⟨rfl, rfl⟩ := (runsTo_sampleN m cv).iff.mp hrun
      have hpt : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd point (sqAll m cv).1 := by
        intro rd hl hL
        obtain ⟨m', hm', -, hN', hc'⟩ := hpre rd hl hL
        have hmm : m' = m := gen_pow_inj hm' hm (hN'.symm.trans hN)
        subst hmm
        rcases hc' with ⟨h0', -⟩ | ⟨-, cv2, rs2, cv2', hcv2, hrun2, hpt2, -⟩
        · omega
        · obtain rfl : cv2 = cv := digestScalars_injective (hcv2.symm.trans hcv)
          obtain ⟨rfl, -⟩ := (runsTo_sampleN m' cv2).iff.mp hrun2
          exact hpt2
      have hpt' := (readsAt_lift hl1 hL1 hpt).2
      obtain ⟨g0, g1⟩ := oodStates_getD cv m (Nat.zero_le m)
      obtain ⟨gm0, gm1⟩ := oodStates_getD cv m le_rfl
      refine ⟨oodStates cv m, _, _, length_oodStates cv m, rfl, ?_, ?_, gm0, gm1, fun _ rd hM => ?_⟩
      · rw [g0]; exact (congrArg Prod.fst hcv).symm
      · rw [g1]; exact (congrArg Prod.snd hcv).symm
      · obtain ⟨hS, hL⟩ := Main.memL_append.mp hM
        have hsc : OodScratch rd p cv m := fun j hj => by
          obtain ⟨a0, a1⟩ := oodStates_getD cv m hj
          rw [← a0, ← a1]
          exact ⟨g1_loadHolds_of_memL hS (by rw [length_oodStates]; omega),
            g1_loadHolds_of_memL hS (by rw [length_oodStates]; omega)⟩
        exact ((guarded_loop_iff (loop9_step rd ng p point)).mpr ⟨m, hm, hN,
          (loop9_bodies_iff rd p point m h0).mpr ⟨cv, hsc, hpt' rd hL⟩⟩).2
          (by rw [hN]; exact ood_one_add_ne hm h0)
  have hLoopC : 0 < m → CompleteAtB fs cert k "__loop9" ([(b0, st)] ++ Lin) [1, ng, p, point] (Returns []) (B9 ng) :=
    fun h0 => completeAt_of_rel_pureBat find_loop9_pure (by simp) (hloop h0) k fun rd t hn hv hb =>
      h9 rd t _ [] hn (by rw [hN]; exact loopPre_gen h0 hm _) hv hb
  set b := b0 + (2 * m + 2) with hbdef
  obtain ⟨nl, Ll, hWl, hDl, hnb, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ DisjL Ll ∧
      nl ≤ max (B9 ng) (fs "__loop9") ∧ (0 < m → ∀ rd,
      LowDef k rd → MemL rd ([] ++ Ll ++ ([(b0, st)] ++ Lin)) →
        RelAtIn coreProgram fs cert rd (RegionL ([(b0, st)] ++ Lin)) (RegionL []) b nl "__loop9"
          [1, ng, p, point] []) ∧ (m = 0 → nl = fs "__loop9") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hd, hnb, hr⟩ := hLoopC h0 b
      exact ⟨n', Lo, by simpa using hw, by simpa using hd, le_trans hnb (le_max_left _ _), fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop9", [], by simp [Within], disj_nil, le_max_right _ _, fun h => absurd h h0, fun _ => rfl⟩
  refine ⟨fs "opening_ood_point" + (2 * m + 2) + nl, [(b0, st)] ++ Ll, [r0, r1], [], ⟨hrets.symm, rfl⟩,
    ?_, ?_, ?_, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    refine ⟨fun q hq => ?_, hWl.mono (by omega) (by omega)⟩
    rw [List.mem_singleton] at hq
    subst hq
    simp only [hst]
    omega
  · rw [List.nil_append]
    refine disj_append (by simp [DisjL]) hDl (fun q hq => ?_) hWl le_rfl
    rw [List.mem_singleton] at hq
    subst hq
    simp only [hst]
    omega
  · have hlg : logG ng = m := by rw [hN, gen_pow_eq_ofK]; exact logG_spec hm
    change fs "opening_ood_point" + (2 * m + 2) + nl ≤
      fs "opening_ood_point" + (2 * logG ng + 2) + max (B9 ng) (fs "__loop9")
    rw [hlg]
    omega
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hS, hLl⟩ := Main.memL_append.mp hM1
  have l0 : LoadHolds rd p 0 fs0 := s0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l1 : LoadHolds rd p 1 fs1 := s1 ▸ g1_loadHolds_of_memL hS (by omega)
  have l13 : LoadHolds rd p (2 * m) r0 := sr0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l14 : LoadHolds rd p (2 * m + 1) r1 := sr1 ▸ g1_loadHolds_of_memL hS (by omega)
  have hK : IsInK (1 + ng) := by
    rw [hN]; exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
  have hcall : 1 + ng ≠ 0 → coreProgram.Rel rd "__loop9" [1, ng, p, point] [] := fun hne =>
    hloop (by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hN, h, pow_zero]; exact e_add_self 1) hne
      · exact h) rd (Main.memL_append.mpr ⟨hS, hLin⟩)
  obtain ⟨hpar, hh⟩ := ood_holds rd fs0 fs1 point ng p r0 r1 m hN l0 l1 l13 l14 hK hcall
  set τ := oodVal fs0 fs1 point ng p r0 r1 with hτ
  have t7 : τ (.n 7) = p := by simp only [hτ, oodVal]; b1_look
  have t9 : τ (.n 9) = 1 + ng := by simp only [hτ, oodVal]; b1_look
  have t10 : τ (.n 10) = 1 := by simp only [hτ, oodVal]; b1_look
  have t3 : τ (.n 3) = ng := by simp only [hτ, oodVal]; b1_look
  have t2 : τ (.n 2) = point := by simp only [hτ, oodVal]; b1_look
  have t6 : τ (.n 6) = ng * gen * (ng * gen) := by simp only [hτ, oodVal]; b1_look
  have t12 : τ (.n 12) = p * ng * ng := by simp only [hτ, oodVal]; b1_look
  have t13 : τ (.n 13) = r0 := by simp only [hτ, oodVal]; b1_look
  have t14 : τ (.n 14) = r1 := by simp only [hτ, oodVal]; b1_look
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core9) = true :=
    coreProgram_wf Data.core9 (List.mem_of_find?_eq_some find_opening_ood_point)
  rw [core9_body_eq] at hwf hh
  obtain ⟨hstr, hal, had, hca, hlo⟩ := oodPre_shape
  have hw := Main.walk_straight τ [.n 13, .n 14] oodPre hstr
  have hs := walk_sat _ hwf hh
  rw [hw] at hs
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ oodPre hstr
  rw [hal] at e1 e2
  rw [had] at e3
  rw [hca] at e4
  have h6 : logG (τ (.n 6)) = 2 * m + 2 := by
    rw [t6, hN, show gen ^ m * gen * (gen ^ m * gen) = gen ^ (2 * m + 2) by ring, gen_pow_eq_ofK]
    exact logG_spec hm2
  simp only [List.map_cons, List.map_nil, Sum.elim_inr, h6] at e1 e2
  have hp12 : τ (.n 12) = gen ^ (b0 + 2 * m) := by
    rw [t12, hpdef, hN, ← gen_pow_eq_ofK]; ring
  have hbuf : ∀ i, b0 ≤ i → i < b0 + (2 * m + 2) → ownData cert fp (fp + fs "opening_ood_point")
      "opening_ood_point" [2 * m + 2] (oodPre.flatMap (Main.slEvs τ)) i := fun i h1 h2 =>
    Or.inl ⟨(2 * m + 2, b0), by simp [bases, hb0], h1, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (args := [fs0, fs1, point, ng])
    (rets := [r0, r1]) coreProgram_wf find_opening_ood_point (Or.inl not_loop_ood) hpar
    (by rw [core9_body_eq]; exact hw) (by simp [t13, t14]) (fun e he => (hs.1 e he).1)
    (by rw [e1, e2]; simp [bases, t7, hpdef, hb0])
    (fun q hq => by rw [e3] at hq; exact absurd hq List.not_mem_nil)
    (by
      rw [show calls (oodPre.flatMap (Main.slEvs τ)) =
        [⟨"__loop9", [.n 10, .n 3, .n 7, .n 2], [], decide (τ (.n 9) ≠ 0)⟩] from e4.trans rfl, e2]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL ([(b0, st)] ++ Lin), RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rcases List.mem_append.mp hq with hq | hq
        · rw [List.mem_singleton] at hq
          subst hq
          exact Or.inl (Or.inr (hbuf i h1 (by rw [hst] at h2; exact h2)))
        · exact Or.inl (Or.inl ⟨q, hq, h1, h2⟩)
      · by_cases h0 : 0 < m
        · have hne : τ (.n 9) ≠ 0 := by rw [t9, hN]; exact ood_one_add_ne hm h0
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t10, t3, t7, t2]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, Main.memL_append.mpr ⟨hS, hLin⟩⟩)
        · have hz : τ (.n 9) = 0 := by
            rw [t9, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by
      rw [e2]
      rw [loadAddrs_straight τ oodPre hstr, hlo] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact ⟨b0 + 0, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 1, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 0, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 1, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h

end
end LeanVM.Guest.B1
