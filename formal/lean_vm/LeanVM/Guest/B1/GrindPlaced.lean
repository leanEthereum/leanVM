/-
  LeanVM.Guest.B1.GrindPlaced

  `grind_check` placed: its frame run of the lane's bits at the certificate's cell, its loop
  `__loop6` reading the run.
-/

module

public import LeanVM.Guest.B1.Grind
public import LeanVM.Guest.B1.G1Placed
public import LeanVM.Guest.B1.Whir.OsCallees
public import LeanVM.Guest.B1.Da.Atoms
public import LeanVM.Guest.Memory.LoopPre

/-!
# `grind_check`, placed (TRIAGE #18)

At frame position `fp` the lane's 64 bits are the frame's cells from `fp + cert "grind_check" (.n 34)`
(`frameAddr`), and `__loop6`, placed after the frame, reads the run's first `bits` cells as zero.
`bits ≤ 64` keeps those reads in the run; the proof-of-work makes them zero (`gc_bits_of_powOk`).
The loop is pure, so it is placed by `completeAt_of_rel_pure` on the run.

`gc_holds`: the honest valuation at a given run pointer (`grind_check_complete_aux`'s, kept
explicit); `grind_check_completeRel`: the placed form on `GrindPre` (`Whir/OsCallees.lean`),
`grind_check`'s meaning without its frame run, `bits ≤ 64`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The honest valuation at a run pointer -/

theorem gc_holds (rd : Reader) (s0 s1 nonce N : E) (m : ℕ) (hm : m < ordG) (hN : N = gen ^ m)
    (cv : Digest) (hcv : (s0, s1) = digestScalars cv) (hpow : powOk m nonce (gcDigest cv nonce) = true)
    (p : E) (hpK : IsInK p)
    (hfr : ∀ k < 64, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w →
      w = bitE ((kToNat ((digestScalars (gcDigest cv nonce)).1.limb 0)).testBit k))
    (hloads : ∀ j < m, LoadHolds rd p j 0) :
    ∃ τ : Val, (τ (.n 287) = p ∧ τ (.n 289) = 1 + N ∧ τ (.n 290) = 1 ∧ τ (.n 3) = N) ∧
      (Fn.params Data.core3).map τ = [s0, s1, nonce, N] ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd τ gcBody False (fun rs => rs = []) := by
  rw [show Fn.params Data.core3 = [.n 0, .n 1, .n 2, .n 3] from rfl, gcBody]
  simp only [holdsList_append, Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 5) [.atom (.const (.n 6) (word 0 0 0)),
    .atom (.assertEq (.n 2) (.n 6))] [] rfl rfl]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, holds_squeezeStateT _ _ _ (show 3 < 256 by decide),
    holds_fsCompressT _ _ _ _ (show 4 < 256 by decide), holds_canonicalLimbsT,
    holdsList_range_flatten 64 gcBit (fun i => by cases i <;> rfl), holds_gcBit, List.map_cons,
    List.map_nil, word_one, word_zero, true_and]
  set B := absorbCv cv 0 3
  set o0 := (digestScalars (absorbCv B nonce 4)).1
  set L := kToNat (o0.limb 0)
  have hL : L < 2 ^ 64 := (o0.limb 0).toBitVec.isLt
  set τ := setl (setv (setv (setl (setv (setv (setl (Val.ofArgs [s0, s1, nonce, N]) 4
    [1, N + 1, 0, s0, s1]) 9 7 (sqStateVals cv 3)) 16 14 (fsVals nonce B 4)) 30
    [ofK (o0.limb 0), o0 + ofK (o0.limb 0), word 1 0 1, ofK (o0.limb 1)]) 34 64
    (fun i => bitE (L.testBit i))) 98 189 (gcVals L)) 287 [p, 1, 1 + N, 1]
  have tb : ∀ i < 64, τ (.n (34 + i)) = bitE (L.testBit i) := fun i hi => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
      Nat.add_sub_cancel_left]
  have tg : ∀ t < 189, τ (.n (98 + t)) = gcVals L t := fun t ht => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have t28 : τ (.n 28) = o0 := by simp only [τ]; b1_look; rfl
  have t30 : τ (.n 30) = ofK (o0.limb 0) := by simp only [τ]; b1_look
  have t2 : τ (.n 2) = nonce := by simp only [τ]; b1_look
  have t5 : τ (.n 5) = N + 1 := by simp only [τ]; b1_look
  have t6 : τ (.n 6) = 0 := by simp only [τ]; b1_look
  have t287 : τ (.n 287) = p := by simp only [τ]; b1_look
  have hcall := (guarded_loop_iff (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hloads j hj⟩
  refine ⟨τ, ⟨t287, by simp only [τ]; b1_look, by simp only [τ]; b1_look, by simp only [τ]; b1_look⟩,
    ?_, ?_, ?_, ⟨?_, fun h5 => ?_, fun _ => trivial⟩, ?_, ?_, ⟨cv, ?_, fun k hk => ?_⟩,
    ⟨B, ?_, fun k hk1 hk2 => ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, trivial⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · rw [t5, hN]; exact isInK_add (gen_pow_isInK m) (by rw [← pow_zero gen]; exact gen_pow_isInK 0)
  · rw [t5, hN, e_add_eq_zero_iff, ← pow_zero gen] at h5
    have hm0 : m = 0 := gen_pow_inj (by omega) (by decide) h5
    subst hm0
    unfold powOk at hpow
    simp only [↓reduceIte, decide_eq_true_eq] at hpow
    have hn : nonce = 0 := by rw [eq_ofLimbs nonce, hpow.1, hpow.2.1, hpow.2.2, ← zero_eq_ofLimbs]
    rw [t6, t2, hn]
    exact ⟨rfl, add_zero 0, trivial⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcv
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
    show ((digestScalars (absorbCv cv 0 3)).1, (digestScalars (absorbCv cv 0 3)).2) = _
    rw [Prod.mk.eta]
  · rw [t2]
    simp only [τ]; b1_look
  · rw [t28]; exact (isCanonical128_digestScalars _).1
  · rw [t30, t28]
  · simp only [τ]; b1_look; rfl
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; rfl
  · cases i with
    | zero =>
      show τ (.n (34 + 0)) = τ (.n (34 + 0)) * τ (.n (34 + 0))
      rw [tb 0 hi, bitE_mul_self]
    | succ i =>
      have e1 := tb (i + 1) hi
      have e2 := tg (3 * i) (by omega)
      have e3 := tg (3 * i + 1) (by omega)
      have e4 := tg (3 * i + 2) (by omega)
      rw [gcVals_0] at e2
      rw [gcVals_1] at e3
      rw [gcVals_2] at e4
      rw [show 34 + (i + 1) = 35 + i by omega] at e1
      rw [show 98 + (3 * i + 1) = 99 + 3 * i by omega] at e3
      rw [show 98 + (3 * i + 2) = 100 + 3 * i by omega] at e4
      have ea : τ (.n (gcAcc i)) = gcAccV L i := by
        cases i with
        | zero => exact tb 0 (by omega)
        | succ i =>
          have := tg (3 * i + 2) (by omega)
          rw [gcVals_2, show 98 + (3 * i + 2) = 100 + 3 * i by omega] at this
          exact this
      refine ⟨by rw [e1, bitE_mul_self], e2, by rw [e3, e1, e2], by rw [e4, ea, e3, gcAccV]⟩
  · have e := tg 188 (by omega)
    rw [show (188 : ℕ) = 3 * 62 + 2 by rfl, gcVals_2, gcAccV_eq L 63 (by omega)] at e
    rw [show 98 + (3 * 62 + 2) = 286 by rfl] at e
    have hr := reconstruct_bits 0 hL
    simp only [Nat.zero_add, pow_zero, one_mul] at hr
    rw [e, t30, show (63 : ℕ) + 1 = 64 from rfl, hr, eOfNat192_of_lt hL]
    have : eOfNat L = ofK (o0.limb 0) := by rw [eOfNat, ofBits_kToNat]
    rw [this]
    exact e_add_self _
  · rw [t287]; exact hpK
  · intro k hk w hw
    rw [t287] at hw
    rw [gcRun_getElem, tb k (by rw [length_gcRun] at hk; exact hk)]
    exact hfr k (by rw [length_gcRun] at hk; exact hk) w hw
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcall.1
  · simp only [τ]; b1_look; exact hcall.2

/-! ## The body's path -/

/-- `grind_check`'s statements after its branch, before its return. -/
def gcRest : List Stmt :=
  [.atom (.copy (.n 7) (.n 0)), .atom (.copy (.n 8) (.n 1))] ++
  squeezeStateT (.n 7) (.n 8) 9 3 ++ fsCompressT (.n 14) (.n 15) (.n 2) 16 4 ++
  canonicalLimbsT (.n 28) 30 ++ [.atom (.hint (.bits (.n 30) 0 64 (.stack gcRun)))] ++
  ((List.range 64).map gcBit).flatten ++
  [.atom (.assertEq (.n 286) (.n 30)), .atom (.frameAddr (.n 287) gcRun),
    .atom (.const (.n 288) (word 1 0 0)), .atom (.add (.n 289) (.n 288) (.n 3)),
    .atom (.const (.n 290) (word 1 0 0)), .callIf (.n 289) "__loop6" [.n 290, .n 3, .n 287]]

theorem gcBody_eq : gcBody = [.atom (.const (.n 4) (word 1 0 0)), .atom (.add (.n 5) (.n 3) (.n 4))] ++
    (.ite (.n 5) [.atom (.const (.n 6) (word 0 0 0)), .atom (.assertEq (.n 2) (.n 6))] [] ::
      (gcRest ++ [.ret []])) := by
  simp only [gcBody, gcRest, List.append_assoc, List.cons_append, List.nil_append]

/-- The events of the branch. -/
noncomputable def gcHead (σ : Val) : List Ev :=
  [.atom (.const (.n 4) (word 1 0 0)), .atom (.add (.n 5) (.n 3) (.n 4)), .inK (.n 5)] ++
    if σ (.n 5) = 0 then [.atom (.const (.n 6) (word 0 0 0)), .atom (.assertEq (.n 2) (.n 6))] else []

theorem walk_gcBody (σ : Val) : walk σ gcBody = .ret (gcHead σ ++ gcRest.flatMap (Main.slEvs σ)) [] := by
  have hst : gcRest.all Main.Stmt.straight = true := by decide +kernel
  rw [gcBody_eq, walk_pre_straight σ _ _ rfl, walk, Main.walk_straight σ [] gcRest hst]
  by_cases h : σ (.n 5) = 0 <;>
    simp [walk1, walk, Main.slEvs, Out.seq, Out.pre, gcHead, h]

/-- What the kernel checks of `gcRest`. -/
theorem gcRest_shape : gcRest.all Main.Stmt.straight = true ∧
    (gcRest.filterMap Main.Stmt.allocSz).isEmpty = true ∧
    gcRest.filterMap Main.Stmt.addrS = [(.n 287, .n 34)] ∧
    gcRest.filterMap Main.Stmt.callS = [(some (.n 289), "__loop6", [.n 290, .n 3, .n 287], [])] ∧
    gcRest.filterMap Digest.stmtRun? = [(.n 34, 64)] ∧ (gcRest.filterMap Stmt.loadS).isEmpty = true := by
  decide +kernel

theorem gcHead_none (σ : Val) : ∀ e ∈ gcHead σ, Ev.allocDst? e = none ∧ Ev.alloc? σ e = none ∧
    Ev.addr? e = none ∧ Ev.call? e = none ∧ Ev.run? e = none ∧ Ev.loadAddr? σ e = none := by
  intro e he
  unfold gcHead at he
  split at he <;>
    simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at he <;>
    rcases he with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem filterMap_gcHead {β : Type} {g : Ev → Option β} (σ : Val) (hg : ∀ e ∈ gcHead σ, g e = none)
    (l : List Ev) : (gcHead σ ++ l).filterMap g = l.filterMap g := by
  rw [List.filterMap_append, List.filterMap_eq_nil_iff.mpr hg, List.nil_append]

/-! ## The proof-of-work's bits -/

theorem gc_bits_of_powOk {m : ℕ} {nonce : E} {D : Digest} (hm : 0 < m) (h : powOk m nonce D = true) :
    ∀ i < m, (kToNat ((digestScalars D).1.limb 0)).testBit i = false := by
  intro i hi
  unfold powOk at h
  rw [ite_neg' (by omega), decide_eq_true_eq, ← kToNat_digestScalars_limb0] at h
  have := congrArg (fun x => Nat.testBit x i) h
  simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit] at this
  simpa [hi] using this

/-! ## The placed form -/

/-- The lane's 64 bits for the digest of `cv` and `nonce`. -/
noncomputable def gcBitsW (cv : Digest) (nonce : E) : List E :=
  (List.range 64).map fun i => bitE ((kToNat ((digestScalars (gcDigest cv nonce)).1.limb 0)).testBit i)

theorem find_loop6_pure : coreProgram.PureIn ["__loop6"] := g1_pure_one find_loop6 (by decide +kernel)

theorem not_loop_grind_check : coreProgram.loop "grind_check" = false := by
  rw [Program.loop_of_find? find_grind_check]; decide +kernel

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)

/-- **`grind_check`, placed**: on `GrindPre` (the state the cells of `cv`, `powOk bits` of the digest,
`bits ≤ 64`), it returns nothing and no buffer, its frame run the lane's bits. -/
theorem grind_check_completeRel (hc : cert "grind_check" (.n 34) + 64 ≤ fs "grind_check") :
    CompleteRel fs cert k "grind_check" GrindPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨s0, s1, nonce, N, rfl⟩ : ∃ s0 s1 nonce N, args = [s0, s1, nonce, N] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨rfl, m, hm, hm64, hN, cv, hcv, hpow⟩ := hpre rd1 hl1 hL1
  set c := cert "grind_check" (.n 34) with hcdef
  set p : E := ofK (Parameters.gpow (fp + c)) with hpdef
  set Lrun : Main.Layout := [(fp + c, gcBitsW cv nonce)] with hLrun
  have hrd_run : ∀ rd, MemL rd Lrun → ∀ j < 64, LoadHolds rd p j ((gcBitsW cv nonce).getD j 0) := by
    intro rd h j hj
    have := h _ List.mem_cons_self j (by simpa [gcBitsW] using hj)
    rwa [List.getD_eq_getElem _ _ (by simpa [gcBitsW] using hj)]
  have hzero : ∀ rd, MemL rd Lrun → ∀ j < m, LoadHolds rd p j 0 := by
    intro rd h j hj
    have := hrd_run rd h j (by omega)
    rwa [gcBitsW, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
      gc_bits_of_powOk (by omega) hpow j hj] at this
  -- The loop, placed after the frame, when entered.
  have hloop : 0 < m → CompleteAt fs cert k "__loop6" Lrun [1, N, p] (Returns []) := fun h0 =>
    completeAt_of_rel_pure find_loop6_pure (by simp) (fun rd hL => ((guarded_loop_iff
      (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hzero rd hL j hj⟩).2 (by
          rw [hN]; intro h
          rw [e_add_eq_zero_iff, ← pow_zero gen] at h
          have := gen_pow_inj (by omega) (by decide) h.symm
          omega)) k
  set b := fp + fs "grind_check"
  obtain ⟨nl, Ll, hWl, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ (0 < m → ∀ rd, LowDef k rd →
      MemL rd ([] ++ Ll ++ Lrun) →
        RelAtIn coreProgram fs cert rd (RegionL Lrun) (RegionL []) b nl "__loop6" [1, N, p] []) ∧
      (m = 0 → nl = fs "__loop6") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hr⟩ := hloop h0 b
      exact ⟨n', Lo, by simpa using hw, fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop6", [], by simp [Within], fun h => absurd h h0, fun _ => rfl⟩
  refine ⟨fs "grind_check" + nl, Lrun ++ Ll, [], [], ⟨rfl, rfl⟩, ?_, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    refine ⟨fun q hq => ?_, hWl.mono (by omega) (by omega)⟩
    rw [hLrun, List.mem_singleton] at hq
    subst hq
    simp only [gcBitsW, List.length_map, List.length_range]
    omega
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hRun, hLl⟩ := Main.memL_append.mp hM1
  have hfr : ∀ k < 64, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w →
      w = bitE ((kToNat ((digestScalars (gcDigest cv nonce)).1.limb 0)).testBit k) := by
    intro j hj w hw
    have := (hrd_run rd hRun j hj).2
    rw [hw, Option.some.injEq] at this
    rw [this, gcBitsW, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  obtain ⟨τ, ⟨t287, t289, t290, t3⟩, hpar, hh⟩ := gc_holds rd s0 s1 nonce N m hm hN cv hcv hpow p
    (ofK_isInK _) hfr (hzero rd hRun)
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core3) = true :=
    coreProgram_wf Data.core3 (List.mem_of_find?_eq_some find_grind_check)
  rw [core3_body] at hwf
  have hs := walk_sat _ hwf hh
  rw [walk_gcBody] at hs
  obtain ⟨hst, hal, had, hca, hru, hlo⟩ := gcRest_shape
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ gcRest hst
  set es := gcHead τ ++ gcRest.flatMap (Main.slEvs τ) with hes_def
  have hAD : allocDsts es = [] := by
    rw [allocDsts, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).1)]
    exact e1.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAL : allocs τ es = [] := by
    rw [allocs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.1)]
    exact e2.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAA : addrs es = [(.n 287, .n 34)] := by
    rw [addrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.1)]
    exact e3.trans had
  have hCA : calls es = [⟨"__loop6", [.n 290, .n 3, .n 287], [], decide (τ (.n 289) ≠ 0)⟩] := by
    rw [calls, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.1)]
    exact e4.trans (by rw [hca]; rfl)
  have hRU : runs es = [(.n 34, 64)] := by
    rw [runs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.1)]
    exact (Digest.runs_straight τ gcRest hst).trans hru
  have hLA : loadAddrs τ es = [] := by
    rw [loadAddrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.2)]
    exact (loadAddrs_straight τ gcRest hst).trans (by rw [g1_filterMap_nil hlo]; rfl)
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (es := es) (args := [s0, s1, nonce, N])
    (rets := []) coreProgram_wf
    find_grind_check (Or.inl not_loop_grind_check) hpar (by rw [core3_body]; exact walk_gcBody τ) rfl
    (fun e he => (hs.1 e he).1) (by rw [hAD, hAL]; rfl)
    (fun q hq => by
      rw [hAA, List.mem_singleton] at hq
      subst hq
      exact t287)
    (by
      rw [hCA, hAL, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL Lrun, RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rw [hLrun, List.mem_singleton] at hq
        subst hq
        refine Or.inl (Or.inr (Or.inr ⟨(.n 34, 64), by rw [hRU]; exact List.mem_singleton_self _,
          h1, ?_⟩))
        simpa [gcBitsW] using h2
      · by_cases h0 : 0 < m
        · have hne : τ (.n 289) ≠ 0 := by
            rw [t289, hN]; intro h
            rw [e_add_eq_zero_iff, ← pow_zero gen] at h
            have := gen_pow_inj (by omega) (by decide) h.symm
            omega
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t290, t3, t287]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, hRun⟩)
        · have hz : τ (.n 289) = 0 := by
            rw [t289, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by rw [hLA] at hA; exact absurd hA (List.not_mem_nil))
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [hAL, List.sum_nil, Nat.add_zero] at h

/-- **`grind_check`, placed**: on `GrindPre` (the state the cells of `cv`, `powOk bits` of the digest,
`bits ≤ 64`), it returns nothing and no buffer, its frame run the lane's bits. -/
theorem grind_check_completeRelD (hc : cert "grind_check" (.n 34) + 64 ≤ fs "grind_check") :
    CompleteRelD fs cert k "grind_check" GrindPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨s0, s1, nonce, N, rfl⟩ : ∃ s0 s1 nonce N, args = [s0, s1, nonce, N] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨rfl, m, hm, hm64, hN, cv, hcv, hpow⟩ := hpre rd1 hl1 hL1
  set c := cert "grind_check" (.n 34) with hcdef
  set p : E := ofK (Parameters.gpow (fp + c)) with hpdef
  set Lrun : Main.Layout := [(fp + c, gcBitsW cv nonce)] with hLrun
  have hrd_run : ∀ rd, MemL rd Lrun → ∀ j < 64, LoadHolds rd p j ((gcBitsW cv nonce).getD j 0) := by
    intro rd h j hj
    have := h _ List.mem_cons_self j (by simpa [gcBitsW] using hj)
    rwa [List.getD_eq_getElem _ _ (by simpa [gcBitsW] using hj)]
  have hzero : ∀ rd, MemL rd Lrun → ∀ j < m, LoadHolds rd p j 0 := by
    intro rd h j hj
    have := hrd_run rd h j (by omega)
    rwa [gcBitsW, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
      gc_bits_of_powOk (by omega) hpow j hj] at this
  -- The loop, placed after the frame, when entered.
  have hloop : 0 < m → CompleteAtD fs cert k "__loop6" Lrun [1, N, p] (Returns []) := fun h0 =>
    completeAt_of_rel_pureD find_loop6_pure (by simp) (fun rd hL => ((guarded_loop_iff
      (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hzero rd hL j hj⟩).2 (by
          rw [hN]; intro h
          rw [e_add_eq_zero_iff, ← pow_zero gen] at h
          have := gen_pow_inj (by omega) (by decide) h.symm
          omega)) k
  set b := fp + fs "grind_check"
  obtain ⟨nl, Ll, hWl, hDl, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ DisjL Ll ∧ (0 < m → ∀ rd, LowDef k rd →
      MemL rd ([] ++ Ll ++ Lrun) →
        RelAtIn coreProgram fs cert rd (RegionL Lrun) (RegionL []) b nl "__loop6" [1, N, p] []) ∧
      (m = 0 → nl = fs "__loop6") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hd, hr⟩ := hloop h0 b
      exact ⟨n', Lo, by simpa using hw, by simpa using hd, fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop6", [], by simp [Within], disj_nil, fun h => absurd h h0, fun _ => rfl⟩
  have hWr : Within Lrun (fp + c) 64 := fun q hq => by
    rw [hLrun, List.mem_singleton] at hq
    subst hq
    simp only [gcBitsW, List.length_map, List.length_range]
    omega
  refine ⟨fs "grind_check" + nl, Lrun ++ Ll, [], [], ⟨rfl, rfl⟩, ?_, ?_, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨fun q hq => by have := hWr q hq; omega, hWl.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (by simp [hLrun, DisjL]) hDl hWr hWl (by omega)
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hRun, hLl⟩ := Main.memL_append.mp hM1
  have hfr : ∀ k < 64, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w →
      w = bitE ((kToNat ((digestScalars (gcDigest cv nonce)).1.limb 0)).testBit k) := by
    intro j hj w hw
    have := (hrd_run rd hRun j hj).2
    rw [hw, Option.some.injEq] at this
    rw [this, gcBitsW, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  obtain ⟨τ, ⟨t287, t289, t290, t3⟩, hpar, hh⟩ := gc_holds rd s0 s1 nonce N m hm hN cv hcv hpow p
    (ofK_isInK _) hfr (hzero rd hRun)
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core3) = true :=
    coreProgram_wf Data.core3 (List.mem_of_find?_eq_some find_grind_check)
  rw [core3_body] at hwf
  have hs := walk_sat _ hwf hh
  rw [walk_gcBody] at hs
  obtain ⟨hst, hal, had, hca, hru, hlo⟩ := gcRest_shape
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ gcRest hst
  set es := gcHead τ ++ gcRest.flatMap (Main.slEvs τ) with hes_def
  have hAD : allocDsts es = [] := by
    rw [allocDsts, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).1)]
    exact e1.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAL : allocs τ es = [] := by
    rw [allocs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.1)]
    exact e2.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAA : addrs es = [(.n 287, .n 34)] := by
    rw [addrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.1)]
    exact e3.trans had
  have hCA : calls es = [⟨"__loop6", [.n 290, .n 3, .n 287], [], decide (τ (.n 289) ≠ 0)⟩] := by
    rw [calls, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.1)]
    exact e4.trans (by rw [hca]; rfl)
  have hRU : runs es = [(.n 34, 64)] := by
    rw [runs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.1)]
    exact (Digest.runs_straight τ gcRest hst).trans hru
  have hLA : loadAddrs τ es = [] := by
    rw [loadAddrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.2)]
    exact (loadAddrs_straight τ gcRest hst).trans (by rw [g1_filterMap_nil hlo]; rfl)
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (es := es) (args := [s0, s1, nonce, N])
    (rets := []) coreProgram_wf
    find_grind_check (Or.inl not_loop_grind_check) hpar (by rw [core3_body]; exact walk_gcBody τ) rfl
    (fun e he => (hs.1 e he).1) (by rw [hAD, hAL]; rfl)
    (fun q hq => by
      rw [hAA, List.mem_singleton] at hq
      subst hq
      exact t287)
    (by
      rw [hCA, hAL, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL Lrun, RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rw [hLrun, List.mem_singleton] at hq
        subst hq
        refine Or.inl (Or.inr (Or.inr ⟨(.n 34, 64), by rw [hRU]; exact List.mem_singleton_self _,
          h1, ?_⟩))
        simpa [gcBitsW] using h2
      · by_cases h0 : 0 < m
        · have hne : τ (.n 289) ≠ 0 := by
            rw [t289, hN]; intro h
            rw [e_add_eq_zero_iff, ← pow_zero gen] at h
            have := gen_pow_inj (by omega) (by decide) h.symm
            omega
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t290, t3, t287]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, hRun⟩)
        · have hz : τ (.n 289) = 0 := by
            rw [t289, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by rw [hLA] at hA; exact absurd hA (List.not_mem_nil))
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [hAL, List.sum_nil, Nat.add_zero] at h

/-- **`grind_check`, placed**: on `GrindPre` (the state the cells of `cv`, `powOk bits` of the digest,
`bits ≤ 64`), it returns nothing and no buffer, its frame run the lane's bits. -/
theorem grind_check_completeRelB (hc : cert "grind_check" (.n 34) + 64 ≤ fs "grind_check") (B6 : E → ℕ)
    (h6 : TotalLeOn coreProgram fs "__loop6" LoopPre fun a => B6 (a.getD 1 0)) :
    ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, LowDef k rd → MemL rd Lin → GrindPre rd args rets) →
      CompleteAtB fs cert k "grind_check" Lin args (Returns rets)
        (fs "grind_check" + max (B6 (args.getD 3 0)) (fs "__loop6")) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨s0, s1, nonce, N, rfl⟩ : ∃ s0 s1 nonce N, args = [s0, s1, nonce, N] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨rfl, m, hm, hm64, hN, cv, hcv, hpow⟩ := hpre rd1 hl1 hL1
  set c := cert "grind_check" (.n 34) with hcdef
  set p : E := ofK (Parameters.gpow (fp + c)) with hpdef
  set Lrun : Main.Layout := [(fp + c, gcBitsW cv nonce)] with hLrun
  have hrd_run : ∀ rd, MemL rd Lrun → ∀ j < 64, LoadHolds rd p j ((gcBitsW cv nonce).getD j 0) := by
    intro rd h j hj
    have := h _ List.mem_cons_self j (by simpa [gcBitsW] using hj)
    rwa [List.getD_eq_getElem _ _ (by simpa [gcBitsW] using hj)]
  have hzero : ∀ rd, MemL rd Lrun → ∀ j < m, LoadHolds rd p j 0 := by
    intro rd h j hj
    have := hrd_run rd h j (by omega)
    rwa [gcBitsW, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
      gc_bits_of_powOk (by omega) hpow j hj] at this
  -- The loop, placed after the frame, when entered.
  have hloop : 0 < m → CompleteAtB fs cert k "__loop6" Lrun [1, N, p] (Returns []) (B6 N) := fun h0 =>
    completeAt_of_rel_pureBat find_loop6_pure (by simp) (fun rd hL => ((guarded_loop_iff
      (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hzero rd hL j hj⟩).2 (by
          rw [hN]; intro h
          rw [e_add_eq_zero_iff, ← pow_zero gen] at h
          have := gen_pow_inj (by omega) (by decide) h.symm
          omega)) k fun rd t hn hv hb =>
      h6 rd t _ [] hn (by rw [hN]; exact loopPre_gen h0 hm _) hv hb
  set b := fp + fs "grind_check"
  obtain ⟨nl, Ll, hWl, hDl, hnb, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ DisjL Ll ∧
      nl ≤ max (B6 N) (fs "__loop6") ∧ (0 < m → ∀ rd, LowDef k rd →
      MemL rd ([] ++ Ll ++ Lrun) →
        RelAtIn coreProgram fs cert rd (RegionL Lrun) (RegionL []) b nl "__loop6" [1, N, p] []) ∧
      (m = 0 → nl = fs "__loop6") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hd, hnb, hr⟩ := hloop h0 b
      exact ⟨n', Lo, by simpa using hw, by simpa using hd, le_trans hnb (le_max_left _ _), fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop6", [], by simp [Within], disj_nil, le_max_right _ _, fun h => absurd h h0, fun _ => rfl⟩
  have hWr : Within Lrun (fp + c) 64 := fun q hq => by
    rw [hLrun, List.mem_singleton] at hq
    subst hq
    simp only [gcBitsW, List.length_map, List.length_range]
    omega
  refine ⟨fs "grind_check" + nl, Lrun ++ Ll, [], [], ⟨rfl, rfl⟩, ?_, ?_, Nat.add_le_add_left hnb _, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨fun q hq => by have := hWr q hq; omega, hWl.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (by simp [hLrun, DisjL]) hDl hWr hWl (by omega)
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hRun, hLl⟩ := Main.memL_append.mp hM1
  have hfr : ∀ k < 64, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w →
      w = bitE ((kToNat ((digestScalars (gcDigest cv nonce)).1.limb 0)).testBit k) := by
    intro j hj w hw
    have := (hrd_run rd hRun j hj).2
    rw [hw, Option.some.injEq] at this
    rw [this, gcBitsW, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  obtain ⟨τ, ⟨t287, t289, t290, t3⟩, hpar, hh⟩ := gc_holds rd s0 s1 nonce N m hm hN cv hcv hpow p
    (ofK_isInK _) hfr (hzero rd hRun)
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core3) = true :=
    coreProgram_wf Data.core3 (List.mem_of_find?_eq_some find_grind_check)
  rw [core3_body] at hwf
  have hs := walk_sat _ hwf hh
  rw [walk_gcBody] at hs
  obtain ⟨hst, hal, had, hca, hru, hlo⟩ := gcRest_shape
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ gcRest hst
  set es := gcHead τ ++ gcRest.flatMap (Main.slEvs τ) with hes_def
  have hAD : allocDsts es = [] := by
    rw [allocDsts, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).1)]
    exact e1.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAL : allocs τ es = [] := by
    rw [allocs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.1)]
    exact e2.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAA : addrs es = [(.n 287, .n 34)] := by
    rw [addrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.1)]
    exact e3.trans had
  have hCA : calls es = [⟨"__loop6", [.n 290, .n 3, .n 287], [], decide (τ (.n 289) ≠ 0)⟩] := by
    rw [calls, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.1)]
    exact e4.trans (by rw [hca]; rfl)
  have hRU : runs es = [(.n 34, 64)] := by
    rw [runs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.1)]
    exact (Digest.runs_straight τ gcRest hst).trans hru
  have hLA : loadAddrs τ es = [] := by
    rw [loadAddrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.2)]
    exact (loadAddrs_straight τ gcRest hst).trans (by rw [g1_filterMap_nil hlo]; rfl)
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (es := es) (args := [s0, s1, nonce, N])
    (rets := []) coreProgram_wf
    find_grind_check (Or.inl not_loop_grind_check) hpar (by rw [core3_body]; exact walk_gcBody τ) rfl
    (fun e he => (hs.1 e he).1) (by rw [hAD, hAL]; rfl)
    (fun q hq => by
      rw [hAA, List.mem_singleton] at hq
      subst hq
      exact t287)
    (by
      rw [hCA, hAL, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL Lrun, RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rw [hLrun, List.mem_singleton] at hq
        subst hq
        refine Or.inl (Or.inr (Or.inr ⟨(.n 34, 64), by rw [hRU]; exact List.mem_singleton_self _,
          h1, ?_⟩))
        simpa [gcBitsW] using h2
      · by_cases h0 : 0 < m
        · have hne : τ (.n 289) ≠ 0 := by
            rw [t289, hN]; intro h
            rw [e_add_eq_zero_iff, ← pow_zero gen] at h
            have := gen_pow_inj (by omega) (by decide) h.symm
            omega
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t290, t3, t287]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, hRun⟩)
        · have hz : τ (.n 289) = 0 := by
            rw [t289, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by rw [hLA] at hA; exact absurd hA (List.not_mem_nil))
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [hAL, List.sum_nil, Nat.add_zero] at h

end
end LeanVM.Guest.B1
