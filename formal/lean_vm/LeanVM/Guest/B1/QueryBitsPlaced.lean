/-
  LeanVM.Guest.B1.QueryBitsPlaced

  `decode_query_bits__L{d}` placed: its frame run of the word's bits at the certificate's cell,
  its positions and pointers in the caller's words.
-/

module

public import LeanVM.Guest.B1.QueryBits
public import LeanVM.Guest.B1.G1Placed
public import LeanVM.Guest.B1.Da.Atoms

/-!
# `decode_query_bits__L{d}`, placed (TRIAGE #17)

At frame position `fp` the run of the word's 192 bits is the frame's cells from
`fp + cert name (.n 3)` (`frameAddr`), and the function stores the positions and the run's
pointers `g^(fp + cert name (.n 3))·g^(j·d)` in the caller's words. It calls nothing and allocates
nothing, so its tree is its frame's `fs name` words; its data is the run, which the caller's Merkle
paths read afterwards. The words it stores are pinned, so on every memory defined below `2^k`
holding the caller's words they lie in those words (`pinned_region`).

`dq_holds`: the honest valuation at a given run pointer (the valuation of
`decode_query_bits_complete_aux`, kept explicit); `dq_completeAt`: the placed form, for a body of
the shape `DqShape` the kernel checks at each depth; `dq_completeAt_all`: the 13 depths.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The honest valuation at a run pointer -/

theorem dq_holds (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 26) (rd : Reader) (w pos ptrs p : E)
    (hpK : IsInK p)
    (hfr : ∀ k < 192, ∀ w', rd (p.limb 0 * Parameters.gpow k) = some w' → w' = bitE ((eToNat w).testBit k))
    (hl : ∀ j < 192 / d, LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
      LoadHolds rd ptrs j (p * gen ^ (j * d))) :
    ∃ τ : Val, τ (.n 0) = w ∧ τ (.n 1) = pos ∧ τ (.n 2) = ptrs ∧ τ (.n 195) = p ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd τ (dqBody d) False (fun rs => rs = []) := by
  have hq0 : 0 < 192 / d := Nat.div_pos (by omega) hd0
  have hqd : 192 / d * d ≤ 192 := Nat.div_mul_le_self 192 d
  unfold dqBody
  generalize 192 / d = q at *
  obtain ⟨B, hB⟩ : ∃ B : ℕ → E, B = fun i => bitE ((eToNat w).testBit i) := ⟨_, rfl⟩
  have hBi : ∀ i, B i = bitE ((eToNat w).testBit i) := fun i => by rw [hB]
  obtain ⟨vals, hvals⟩ : ∃ l, l = dqGroupsV B p d 0 q 196 none ++ dqLeftV B (q * d) (192 - q * d) :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Val, τ = setv (setv (setv (Val.ofArgs [w, pos, ptrs]) 3 192 B) 195 1
      (fun _ => p)) 196 vals.length (fun i => vals.getD i 0) := ⟨_, rfl⟩
  have t0 : τ (.n 0) = w := by rw [hτ]; b1_look
  have t1 : τ (.n 1) = pos := by rw [hτ]; b1_look
  have t2 : τ (.n 2) = ptrs := by rw [hτ]; b1_look
  have t195 : τ (.n 195) = p := by
    rw [hτ, set_n_lt (by omega), set_n_in (by omega) (by omega)]
  have tb : BitsAre τ B := fun i hi => ⟨by
    rw [bitsOf, hτ, set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
      Nat.add_sub_cancel_left], by rw [hBi]; exact bitE_mul_self _⟩
  have tv : Agree τ 196 vals := fun i hi => by
    rw [hτ, set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  rw [hvals, agree_append] at tv
  obtain ⟨G1, G2⟩ := dqGroups_of_agree (rd := rd) hd0 hd tb t195 q 0 196 none (by simpa using hqd)
    (fun _ h => absurd h (by simp)) ⟨fun _ => rfl, fun _ => rfl⟩ (fun c hc => by
      obtain ⟨l1, l2⟩ := hl c (by omega)
      rw [t1, t2, Nat.zero_add]
      refine ⟨?_, l2⟩
      simp only [hBi]
      rw [dq_position _ _ _ (by omega)]
      exact l1) tv.1
  obtain ⟨-, -, g3, g4⟩ := dqGroups_facts hd0 hd q 0 196 none (by simpa using hqd) (fun _ => rfl)
    (Or.inl hq0) G1
  simp only [Nat.zero_mul, optVal_none τ, zero_add] at g4
  rw [← optVal_getD (σ := τ) g3 (.n 0)] at g4
  have hrv : τ ((dqGroups d 0 q 196 none).2.2.getD (.n 0)) =
      ∑ m ∈ Finset.range (q * d), B m * cbWord m := by
    rw [g4]
    exact Finset.sum_congr rfl fun m hm => by
      rw [(tb m (by have := Finset.mem_range.mp hm; omega)).1]
  have L1 := dqLeft_of_agree tb (192 - q * d) (q * d) (dqGroups d 0 q 196 none).2.1 _ (by omega) hrv
    (by rw [G2]; exact tv.2)
  obtain ⟨-, l2⟩ := dqLeft_facts _ _ _ _ L1
  have hw : τ (dqLeft (q * d) (192 - q * d) (dqGroups d 0 q 196 none).2.1
      ((dqGroups d 0 q 196 none).2.2.getD (.n 0))).2 = w := by
    rw [l2, hrv]
    have hr := reconstruct_bits 0 (eToNat_lt w)
    simp only [Nat.zero_add, pow_zero, one_mul, eOfNat192_eToNat] at hr
    rw [← hr, show Finset.range 192 = Finset.range (q * d + (192 - q * d)) by congr 1; omega,
      Finset.sum_range_add]
    simp only [← hBi, cbWord_eq]
    exact congrArg _ (Finset.sum_congr rfl fun m hm => by
      rw [(tb _ (by have := Finset.mem_range.mp hm; omega)).1])
  refine ⟨τ, t0, t1, t2, t195, ?_⟩
  simp only [holdsList_append, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, true_and]
  rw [holds_dqGroups, holds_dqLeft]
  refine ⟨⟨by rw [t195]; exact hpK, fun k hk w' hw' => ?_⟩, G1, L1, ?_, rfl⟩
  · rw [t195] at hw'
    rw [hfr k (by rw [length_dqRun] at hk; exact hk) w' hw', dqRun_getElem]
    exact ((tb k (by rw [length_dqRun] at hk; exact hk)).1.trans (hBi k)).symm
  · rw [hw, t0]
    exact e_add_self w

/-! ## The body's path -/

/-- The statements of `decode_query_bits` at depth `d` before its return. -/
def dqPre (d : ℕ) : List Stmt :=
  [.atom (.hint (.bits (.n 0) 0 192 (.stack dqRun))), .atom (.frameAddr (.n 195) dqRun)] ++
    (dqGroups d 0 (192 / d) 196 none).1 ++
    (dqLeft (192 / d * d) (192 - 192 / d * d) (dqGroups d 0 (192 / d) 196 none).2.1
      ((dqGroups d 0 (192 / d) 196 none).2.2.getD (.n 0))).1 ++
    [.atom (.assertEq (dqLeft (192 / d * d) (192 - 192 / d * d) (dqGroups d 0 (192 / d) 196 none).2.1
      ((dqGroups d 0 (192 / d) 196 none).2.2.getD (.n 0))).2 (.n 0))]

theorem dqBody_eq (d : ℕ) : dqBody d = dqPre d ++ [.ret []] := by
  simp only [dqBody, dqPre, List.append_assoc, List.cons_append, List.nil_append]

/-- What the kernel checks of the body at depth `d`: straight, no `HeapBuf`, no call, one
`frameAddr` naming the 192-cell run from `.n 3` at `.n 195`, and loads only from `pos` or `ptrs`
at the groups' offsets. -/
def DqShape (d : ℕ) : Prop :=
  (dqPre d).all Main.Stmt.straight = true ∧ ((dqPre d).filterMap Main.Stmt.allocSz).isEmpty = true ∧
    (dqPre d).filterMap Main.Stmt.addrS = [(.n 195, .n 3)] ∧
    ((dqPre d).filterMap Main.Stmt.callS).isEmpty = true ∧
    (dqPre d).filterMap Digest.stmtRun? = [(.n 3, 192)] ∧
    ((dqPre d).filterMap Stmt.loadS).all (fun q => (q.1 == .n 1 || q.1 == .n 2) && decide (q.2 < 192 / d)) = true

instance (d : ℕ) : Decidable (DqShape d) := by unfold DqShape; infer_instance

/-- The 192 bits of `w`. -/
def dqBitsW (w : E) : List E := (List.range 192).map fun i => bitE ((eToNat w).testBit i)

/-! ## The placed form -/

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)

/-- **`decode_query_bits` at depth `d`, placed**: at every frame pointer `fp`, on every memory
where the caller's words hold the positions at `pos` and the run's pointers at `ptrs`, a tree of
`fs name` words, its data the run of `w`'s bits at `fp + cert name (.n 3)`. -/
theorem dq_completeAt {name : String} {f : Fn} (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 26)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = dqBody d) (hsh : DqShape d) (hc : cert name (.n 3) + 192 ≤ fs name)
    (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert name (.n 3))) * gen ^ (j * d))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert name (.n 3), dqBitsW w)] ++ Lown) fp (fs name) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert name (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert name (.n 3), dqBitsW w)])
          fp (fs name) name [w, pos, ptrs] [] := by
  refine ⟨[], fun q hq => ?_, fun rd hl hM => ?_⟩
  · obtain rfl : q = (fp + cert name (.n 3), dqBitsW w) := by simpa using hq
    simp only [dqBitsW, List.length_map, List.length_range]
    omega
  · simp only [List.append_nil] at hM
    obtain ⟨hR, hLin⟩ := Main.memL_append.mp hM
    set c := cert name (.n 3) with hcdef
    have hrun := hR _ List.mem_cons_self
    have hfr : ∀ k < 192, ∀ w', rd ((ofK (Parameters.gpow (fp + c))).limb 0 * Parameters.gpow k) = some w' →
        w' = bitE ((eToNat w).testBit k) := fun k hk w' hw' => by
      have := (hrun k (by simpa [dqBitsW] using hk)).2
      rw [hw', Option.some.injEq] at this
      rw [this]
      simp [dqBitsW]
    obtain ⟨τ, t0, t1, t2, t195, hh⟩ := dq_holds d hd0 hd rd w pos ptrs _ (ofK_isInK _) hfr
      (fun j hj => hpre rd hl hLin j hj)
    obtain ⟨hst, hal, had, hca, hru, hlo⟩ := hsh
    have hwf : Stmt.wfList coreProgram f.body = true :=
      coreProgram_wf f (List.mem_of_find?_eq_some hfind)
    rw [hbody, dqBody_eq] at hwf
    rw [dqBody_eq] at hh
    have hw := Main.walk_straight τ [] (dqPre d) hst
    obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ (dqPre d) hst
    rw [g1_filterMap_nil hal, List.map_nil] at e1 e2
    rw [had] at e3
    rw [g1_filterMap_nil hca, List.map_nil] at e4
    have hs := walk_sat _ hwf hh
    rw [hw] at hs
    have hru' := Digest.runs_straight τ (dqPre d) hst
    rw [hru] at hru'
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
      (D := RegionL [(fp + c, dqBitsW w)]) (Dk := fun _ => False) (fp := fp) (N := 0)
      (args := [w, pos, ptrs]) (rets := []) coreProgram_wf
      hfind (Or.inr e4) (by rw [hparams]; simp [t0, t1, t2]) (by rw [hbody, dqBody_eq]; exact hw) rfl
      (fun e he => (hs.1 e he).1) (by rw [e1, e2]; rfl)
      (fun q hq => by
        rw [e3, List.mem_singleton] at hq
        subst hq
        exact t195)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [loadAddrs_straight τ (dqPre d) hst] at hA
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
        have hq' := List.all_eq_true.mp hlo q hq
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hq'
        obtain ⟨hq1 | hq1, hq2⟩ := hq'
        · rw [hq1, t1]
          obtain ⟨i, hi, hr⟩ := pinned_region hl hLin (fun rd' hl' hL' => (hpre rd' hl' hL' q.2 hq2).1.2)
          exact ⟨i, hi, Or.inr (Or.inl hr)⟩
        · rw [hq1, t2]
          obtain ⟨i, hi, hr⟩ := pinned_region hl hLin (fun rd' hl' hL' => (hpre rd' hl' hL' q.2 hq2).2.2)
          exact ⟨i, hi, Or.inr (Or.inl hr)⟩)
      (fun i hi => by
        obtain ⟨q, hq, h1, h2⟩ := hi
        rw [List.mem_singleton] at hq
        subst hq
        refine Or.inl (Or.inr ⟨(.n 3, 192), by rw [hru']; exact List.mem_singleton_self _, h1, ?_⟩)
        simpa [dqBitsW] using h2)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h

/-- **`decode_query_bits` at depth `d`, placed**: at every frame pointer `fp`, on every memory
where the caller's words hold the positions at `pos` and the run's pointers at `ptrs`, a tree of
`fs name` words, its data the run of `w`'s bits at `fp + cert name (.n 3)`. -/
theorem dq_completeAtD {name : String} {f : Fn} (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 26)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = dqBody d) (hsh : DqShape d) (hc : cert name (.n 3) + 192 ≤ fs name)
    (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert name (.n 3))) * gen ^ (j * d))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert name (.n 3), dqBitsW w)] ++ Lown) fp (fs name) ∧ DisjL ([(fp + cert name (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert name (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert name (.n 3), dqBitsW w)])
          fp (fs name) name [w, pos, ptrs] [] := by
  refine ⟨[], fun q hq => ?_, by simp [DisjL], fun rd hl hM => ?_⟩
  · obtain rfl : q = (fp + cert name (.n 3), dqBitsW w) := by simpa using hq
    simp only [dqBitsW, List.length_map, List.length_range]
    omega
  · simp only [List.append_nil] at hM
    obtain ⟨hR, hLin⟩ := Main.memL_append.mp hM
    set c := cert name (.n 3) with hcdef
    have hrun := hR _ List.mem_cons_self
    have hfr : ∀ k < 192, ∀ w', rd ((ofK (Parameters.gpow (fp + c))).limb 0 * Parameters.gpow k) = some w' →
        w' = bitE ((eToNat w).testBit k) := fun k hk w' hw' => by
      have := (hrun k (by simpa [dqBitsW] using hk)).2
      rw [hw', Option.some.injEq] at this
      rw [this]
      simp [dqBitsW]
    obtain ⟨τ, t0, t1, t2, t195, hh⟩ := dq_holds d hd0 hd rd w pos ptrs _ (ofK_isInK _) hfr
      (fun j hj => hpre rd hl hLin j hj)
    obtain ⟨hst, hal, had, hca, hru, hlo⟩ := hsh
    have hwf : Stmt.wfList coreProgram f.body = true :=
      coreProgram_wf f (List.mem_of_find?_eq_some hfind)
    rw [hbody, dqBody_eq] at hwf
    rw [dqBody_eq] at hh
    have hw := Main.walk_straight τ [] (dqPre d) hst
    obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ (dqPre d) hst
    rw [g1_filterMap_nil hal, List.map_nil] at e1 e2
    rw [had] at e3
    rw [g1_filterMap_nil hca, List.map_nil] at e4
    have hs := walk_sat _ hwf hh
    rw [hw] at hs
    have hru' := Digest.runs_straight τ (dqPre d) hst
    rw [hru] at hru'
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
      (D := RegionL [(fp + c, dqBitsW w)]) (Dk := fun _ => False) (fp := fp) (N := 0)
      (args := [w, pos, ptrs]) (rets := []) coreProgram_wf
      hfind (Or.inr e4) (by rw [hparams]; simp [t0, t1, t2]) (by rw [hbody, dqBody_eq]; exact hw) rfl
      (fun e he => (hs.1 e he).1) (by rw [e1, e2]; rfl)
      (fun q hq => by
        rw [e3, List.mem_singleton] at hq
        subst hq
        exact t195)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [loadAddrs_straight τ (dqPre d) hst] at hA
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
        have hq' := List.all_eq_true.mp hlo q hq
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hq'
        obtain ⟨hq1 | hq1, hq2⟩ := hq'
        · rw [hq1, t1]
          obtain ⟨i, hi, hr⟩ := pinned_region hl hLin (fun rd' hl' hL' => (hpre rd' hl' hL' q.2 hq2).1.2)
          exact ⟨i, hi, Or.inr (Or.inl hr)⟩
        · rw [hq1, t2]
          obtain ⟨i, hi, hr⟩ := pinned_region hl hLin (fun rd' hl' hL' => (hpre rd' hl' hL' q.2 hq2).2.2)
          exact ⟨i, hi, Or.inr (Or.inl hr)⟩)
      (fun i hi => by
        obtain ⟨q, hq, h1, h2⟩ := hi
        rw [List.mem_singleton] at hq
        subst hq
        refine Or.inl (Or.inr ⟨(.n 3, 192), by rw [hru']; exact List.mem_singleton_self _, h1, ?_⟩)
        simpa [dqBitsW] using h2)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h

/-! ## The 13 depths -/

set_option maxRecDepth 100000 in
theorem dq_completeAt_L14 (hc : cert (dqName 14) (.n 3) + 192 ≤ fs (dqName 14)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 14,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 14)) % 2 ^ 14)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 14) (.n 3))) * gen ^ (j * 14))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 14) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 14)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 14) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 14) (.n 3), dqBitsW w)])
          fp (fs (dqName 14)) (dqName 14) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 14 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 14) (j := 980) (by decide +kernel) rfl) rfl core980_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L14D (hc : cert (dqName 14) (.n 3) + 192 ≤ fs (dqName 14)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 14,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 14)) % 2 ^ 14)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 14) (.n 3))) * gen ^ (j * 14))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 14) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 14)) ∧ DisjL ([(fp + cert (dqName 14) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 14) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 14) (.n 3), dqBitsW w)])
          fp (fs (dqName 14)) (dqName 14) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 14 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 14) (j := 980) (by decide +kernel) rfl) rfl core980_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L15 (hc : cert (dqName 15) (.n 3) + 192 ≤ fs (dqName 15)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 15,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 15)) % 2 ^ 15)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 15) (.n 3))) * gen ^ (j * 15))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 15) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 15)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 15) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 15) (.n 3), dqBitsW w)])
          fp (fs (dqName 15)) (dqName 15) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 15 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 15) (j := 977) (by decide +kernel) rfl) rfl core977_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L15D (hc : cert (dqName 15) (.n 3) + 192 ≤ fs (dqName 15)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 15,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 15)) % 2 ^ 15)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 15) (.n 3))) * gen ^ (j * 15))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 15) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 15)) ∧ DisjL ([(fp + cert (dqName 15) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 15) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 15) (.n 3), dqBitsW w)])
          fp (fs (dqName 15)) (dqName 15) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 15 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 15) (j := 977) (by decide +kernel) rfl) rfl core977_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L16 (hc : cert (dqName 16) (.n 3) + 192 ≤ fs (dqName 16)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 16,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 16)) % 2 ^ 16)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 16) (.n 3))) * gen ^ (j * 16))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 16) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 16)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 16) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 16) (.n 3), dqBitsW w)])
          fp (fs (dqName 16)) (dqName 16) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 16 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 16) (j := 974) (by decide +kernel) rfl) rfl core974_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L16D (hc : cert (dqName 16) (.n 3) + 192 ≤ fs (dqName 16)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 16,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 16)) % 2 ^ 16)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 16) (.n 3))) * gen ^ (j * 16))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 16) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 16)) ∧ DisjL ([(fp + cert (dqName 16) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 16) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 16) (.n 3), dqBitsW w)])
          fp (fs (dqName 16)) (dqName 16) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 16 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 16) (j := 974) (by decide +kernel) rfl) rfl core974_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L17 (hc : cert (dqName 17) (.n 3) + 192 ≤ fs (dqName 17)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 17,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 17)) % 2 ^ 17)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 17) (.n 3))) * gen ^ (j * 17))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 17) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 17)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 17) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 17) (.n 3), dqBitsW w)])
          fp (fs (dqName 17)) (dqName 17) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 17 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 17) (j := 971) (by decide +kernel) rfl) rfl core971_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L17D (hc : cert (dqName 17) (.n 3) + 192 ≤ fs (dqName 17)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 17,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 17)) % 2 ^ 17)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 17) (.n 3))) * gen ^ (j * 17))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 17) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 17)) ∧ DisjL ([(fp + cert (dqName 17) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 17) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 17) (.n 3), dqBitsW w)])
          fp (fs (dqName 17)) (dqName 17) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 17 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 17) (j := 971) (by decide +kernel) rfl) rfl core971_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L18 (hc : cert (dqName 18) (.n 3) + 192 ≤ fs (dqName 18)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 18,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 18)) % 2 ^ 18)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 18) (.n 3))) * gen ^ (j * 18))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 18) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 18)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 18) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 18) (.n 3), dqBitsW w)])
          fp (fs (dqName 18)) (dqName 18) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 18 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 18) (j := 982) (by decide +kernel) rfl) rfl core982_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L18D (hc : cert (dqName 18) (.n 3) + 192 ≤ fs (dqName 18)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 18,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 18)) % 2 ^ 18)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 18) (.n 3))) * gen ^ (j * 18))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 18) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 18)) ∧ DisjL ([(fp + cert (dqName 18) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 18) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 18) (.n 3), dqBitsW w)])
          fp (fs (dqName 18)) (dqName 18) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 18 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 18) (j := 982) (by decide +kernel) rfl) rfl core982_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L19 (hc : cert (dqName 19) (.n 3) + 192 ≤ fs (dqName 19)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 19,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 19)) % 2 ^ 19)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 19) (.n 3))) * gen ^ (j * 19))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 19) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 19)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 19) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 19) (.n 3), dqBitsW w)])
          fp (fs (dqName 19)) (dqName 19) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 19 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 19) (j := 986) (by decide +kernel) rfl) rfl core986_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L19D (hc : cert (dqName 19) (.n 3) + 192 ≤ fs (dqName 19)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 19,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 19)) % 2 ^ 19)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 19) (.n 3))) * gen ^ (j * 19))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 19) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 19)) ∧ DisjL ([(fp + cert (dqName 19) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 19) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 19) (.n 3), dqBitsW w)])
          fp (fs (dqName 19)) (dqName 19) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 19 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 19) (j := 986) (by decide +kernel) rfl) rfl core986_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L20 (hc : cert (dqName 20) (.n 3) + 192 ≤ fs (dqName 20)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 20,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 20)) % 2 ^ 20)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 20) (.n 3))) * gen ^ (j * 20))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 20) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 20)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 20) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 20) (.n 3), dqBitsW w)])
          fp (fs (dqName 20)) (dqName 20) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 20 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 20) (j := 990) (by decide +kernel) rfl) rfl core990_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L20D (hc : cert (dqName 20) (.n 3) + 192 ≤ fs (dqName 20)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 20,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 20)) % 2 ^ 20)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 20) (.n 3))) * gen ^ (j * 20))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 20) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 20)) ∧ DisjL ([(fp + cert (dqName 20) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 20) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 20) (.n 3), dqBitsW w)])
          fp (fs (dqName 20)) (dqName 20) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 20 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 20) (j := 990) (by decide +kernel) rfl) rfl core990_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L21 (hc : cert (dqName 21) (.n 3) + 192 ≤ fs (dqName 21)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 21,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 21)) % 2 ^ 21)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 21) (.n 3))) * gen ^ (j * 21))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 21) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 21)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 21) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 21) (.n 3), dqBitsW w)])
          fp (fs (dqName 21)) (dqName 21) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 21 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 21) (j := 994) (by decide +kernel) rfl) rfl core994_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L21D (hc : cert (dqName 21) (.n 3) + 192 ≤ fs (dqName 21)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 21,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 21)) % 2 ^ 21)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 21) (.n 3))) * gen ^ (j * 21))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 21) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 21)) ∧ DisjL ([(fp + cert (dqName 21) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 21) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 21) (.n 3), dqBitsW w)])
          fp (fs (dqName 21)) (dqName 21) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 21 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 21) (j := 994) (by decide +kernel) rfl) rfl core994_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L22 (hc : cert (dqName 22) (.n 3) + 192 ≤ fs (dqName 22)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 22,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 22)) % 2 ^ 22)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 22) (.n 3))) * gen ^ (j * 22))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 22) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 22)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 22) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 22) (.n 3), dqBitsW w)])
          fp (fs (dqName 22)) (dqName 22) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 22 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 22) (j := 998) (by decide +kernel) rfl) rfl core998_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L22D (hc : cert (dqName 22) (.n 3) + 192 ≤ fs (dqName 22)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 22,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 22)) % 2 ^ 22)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 22) (.n 3))) * gen ^ (j * 22))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 22) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 22)) ∧ DisjL ([(fp + cert (dqName 22) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 22) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 22) (.n 3), dqBitsW w)])
          fp (fs (dqName 22)) (dqName 22) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 22 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 22) (j := 998) (by decide +kernel) rfl) rfl core998_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L23 (hc : cert (dqName 23) (.n 3) + 192 ≤ fs (dqName 23)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 23,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 23)) % 2 ^ 23)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 23) (.n 3))) * gen ^ (j * 23))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 23) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 23)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 23) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 23) (.n 3), dqBitsW w)])
          fp (fs (dqName 23)) (dqName 23) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 23 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 23) (j := 1002) (by decide +kernel) rfl) rfl core1002_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L23D (hc : cert (dqName 23) (.n 3) + 192 ≤ fs (dqName 23)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 23,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 23)) % 2 ^ 23)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 23) (.n 3))) * gen ^ (j * 23))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 23) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 23)) ∧ DisjL ([(fp + cert (dqName 23) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 23) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 23) (.n 3), dqBitsW w)])
          fp (fs (dqName 23)) (dqName 23) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 23 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 23) (j := 1002) (by decide +kernel) rfl) rfl core1002_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L24 (hc : cert (dqName 24) (.n 3) + 192 ≤ fs (dqName 24)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 24,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 24)) % 2 ^ 24)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 24) (.n 3))) * gen ^ (j * 24))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 24) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 24)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 24) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 24) (.n 3), dqBitsW w)])
          fp (fs (dqName 24)) (dqName 24) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 24 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 24) (j := 1018) (by decide +kernel) rfl) rfl core1018_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L24D (hc : cert (dqName 24) (.n 3) + 192 ≤ fs (dqName 24)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 24,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 24)) % 2 ^ 24)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 24) (.n 3))) * gen ^ (j * 24))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 24) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 24)) ∧ DisjL ([(fp + cert (dqName 24) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 24) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 24) (.n 3), dqBitsW w)])
          fp (fs (dqName 24)) (dqName 24) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 24 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 24) (j := 1018) (by decide +kernel) rfl) rfl core1018_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L25 (hc : cert (dqName 25) (.n 3) + 192 ≤ fs (dqName 25)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 25,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 25)) % 2 ^ 25)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 25) (.n 3))) * gen ^ (j * 25))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 25) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 25)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 25) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 25) (.n 3), dqBitsW w)])
          fp (fs (dqName 25)) (dqName 25) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 25 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 25) (j := 1023) (by decide +kernel) rfl) rfl core1023_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L25D (hc : cert (dqName 25) (.n 3) + 192 ≤ fs (dqName 25)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 25,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 25)) % 2 ^ 25)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 25) (.n 3))) * gen ^ (j * 25))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 25) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 25)) ∧ DisjL ([(fp + cert (dqName 25) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 25) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 25) (.n 3), dqBitsW w)])
          fp (fs (dqName 25)) (dqName 25) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 25 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 25) (j := 1023) (by decide +kernel) rfl) rfl core1023_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L26 (hc : cert (dqName 26) (.n 3) + 192 ≤ fs (dqName 26)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 26,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 26)) % 2 ^ 26)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 26) (.n 3))) * gen ^ (j * 26))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 26) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 26)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 26) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 26) (.n 3), dqBitsW w)])
          fp (fs (dqName 26)) (dqName 26) [w, pos, ptrs] [] :=
  dq_completeAt fs cert k 26 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 26) (j := 1035) (by decide +kernel) rfl) rfl core1035_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

set_option maxRecDepth 100000 in
theorem dq_completeAt_L26D (hc : cert (dqName 26) (.n 3) + 192 ≤ fs (dqName 26)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / 26,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * 26)) % 2 ^ 26)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName 26) (.n 3))) * gen ^ (j * 26))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName 26) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName 26)) ∧ DisjL ([(fp + cert (dqName 26) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName 26) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName 26) (.n 3), dqBitsW w)])
          fp (fs (dqName 26)) (dqName 26) [w, pos, ptrs] [] :=
  dq_completeAtD fs cert k 26 (by decide) (by decide)
    (Program.find?_of_indexOf? (n := dqName 26) (j := 1035) (by decide +kernel) rfl) rfl core1035_body (by decide +kernel)
    hc w pos ptrs Lin fp hpre

/-- **`decode_query_bits__L{d}`, placed, at the 13 depths.** -/
theorem dq_completeAt_all (d : ℕ) (h1 : 14 ≤ d) (h2 : d ≤ 26) (hc : cert (dqName d) (.n 3) + 192 ≤ fs (dqName d)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName d) (.n 3))) * gen ^ (j * d))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName d) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName d)) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName d) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName d) (.n 3), dqBitsW w)])
          fp (fs (dqName d)) (dqName d) [w, pos, ptrs] [] := by
  revert hc hpre
  interval_cases d
  · exact fun hc hpre => dq_completeAt_L14 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L15 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L16 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L17 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L18 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L19 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L20 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L21 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L22 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L23 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L24 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L25 fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L26 fs cert k hc w pos ptrs Lin fp hpre

/-- **`decode_query_bits__L{d}`, placed, at the 13 depths.** -/
theorem dq_completeAt_allD (d : ℕ) (h1 : 14 ≤ d) (h2 : d ≤ 26) (hc : cert (dqName d) (.n 3) + 192 ≤ fs (dqName d)) (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ)
    (hpre : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert (dqName d) (.n 3))) * gen ^ (j * d))) :
    ∃ Lown : Main.Layout, Within ([(fp + cert (dqName d) (.n 3), dqBitsW w)] ++ Lown) fp (fs (dqName d)) ∧ DisjL ([(fp + cert (dqName d) (.n 3), dqBitsW w)] ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd ([(fp + cert (dqName d) (.n 3), dqBitsW w)] ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL [(fp + cert (dqName d) (.n 3), dqBitsW w)])
          fp (fs (dqName d)) (dqName d) [w, pos, ptrs] [] := by
  revert hc hpre
  interval_cases d
  · exact fun hc hpre => dq_completeAt_L14D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L15D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L16D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L17D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L18D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L19D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L20D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L21D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L22D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L23D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L24D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L25D fs cert k hc w pos ptrs Lin fp hpre
  · exact fun hc hpre => dq_completeAt_L26D fs cert k hc w pos ptrs Lin fp hpre

end
end LeanVM.Guest.B1
