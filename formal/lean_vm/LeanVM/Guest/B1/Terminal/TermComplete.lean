/-
  LeanVM.Guest.B1.Terminal.TermComplete

  **`check_opening_terminal` is complete, placed** (G:3232-3318; TRIAGE #70): on the caller's
  words making `TermPre` true, when the WHIR terminal equation holds, it returns at every frame
  pointer.
-/

module

public import LeanVM.Guest.B1.Terminal.TermSigma

/-!
# `check_opening_terminal`, completely

The honest direction of `MeaningTerminal`: `check_opening_terminal_completeAt`. Its hypotheses:

* `hpre`: `TermPre` (what `verify_sub` establishes, soundness's precondition) on every memory
  holding the caller's words `Lin` (defined below `2^κ`);
* `hreg`: the words it reads lie in `Lin` (`TermRegion`: the bus point, the tables' point of
  `nc` words, `g^nc` being its argument `g_zc_n`, the base `kappa_base`, the columns' offsets, the
  nibble shares at `g_squares·g^34`, the outputs' and the ring switch's points, the coefficients,
  the terminal point and its complements);
* `hbus`: the bus point has at most `34` coordinates, so its prefix chain (`|bus.point| + 1` words)
  fits the guest's `35`-word buffer (G:3237; `TermPre` allows `40`);
* `hfin`: the WHIR terminal equation `(inner + basis(x))·residual = target`, `MeaningTerminal`'s
  conclusion;
* `6 ≤ κ`: the memory is defined below `64`, where `eq_prefix_chain`'s range checks read.

The proof (`completeAt_flatDepR`): the honest buffers (`termOwn`: the three prefix chains and the
public input's chain), the 107 callees complete (`termKids_complete`, each column selector on
`selector_tables`' result), the honest valuation (`term_sigma`). The data that do not depend on the
memory (the tables' point `chis`, the lengths) come from one memory holding `Lin`; without one the
statement is empty.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- Two memories holding a layout agree on its words. -/
theorem memL_agree {rd rd' : Reader} {L : Main.Layout} (h : MemL rd L) (h' : MemL rd' L) {i : ℕ}
    (hi : RegionL L i) : rd (addressOfIndex i) = rd' (addressOfIndex i) := by
  obtain ⟨q, hq, h1, h2⟩ := hi
  have l := (h q hq (i - q.1) (by omega)).2
  have l' := (h' q hq (i - q.1) (by omega)).2
  rw [Main.addr_ofK, Nat.add_sub_cancel' h1] at l l'
  exact l.trans l'.symm

theorem readsAt_transfer {rd rd' : Reader} {L : Main.Layout} (h : MemL rd L) (h' : MemL rd' L)
    {b : ℕ} {xs : List E} (hr : ReadsAt rd (ofK (addressOfIndex b)) xs)
    (hreg : ∀ k < xs.length, RegionL L (b + k)) : ReadsAt rd' (ofK (addressOfIndex b)) xs :=
        fun k hk =>
  ⟨(hr k hk).1, by rw [Main.addr_ofK, ← memL_agree h h' (hreg k hk), ← Main.addr_ofK]; exact (hr k hk).2⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`check_opening_terminal` is complete, placed** (the honest direction of `MeaningTerminal`):
on the caller's words making `TermPre` true, reading only them, when the WHIR terminal equation
holds, it returns nothing at every frame pointer. -/
theorem check_opening_terminal_completeAt (κ : ℕ) (hκ : 6 ≤ κ) (B : TermBases) (Lin : Main.Layout)
    {layout : Layout} {bus : BusResult} {claims : List ColumnClaim} {out : ColumnClaim} {lam : E}
    {ringPoint coeffs x : List E} {rm gmu gzcn glm gtau lamCl inner yr target : E} {nc : ℕ}
    (hnc : nc ≤ 40) (hgz : gzcn = gen ^ nc)
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → TermPre rd layout bus claims out lam ringPoint coeffs x
      (termArgs B rm gmu gzcn glm gtau lamCl inner yr target))
    (hreg : ∀ i, TermRegion B bus.point.length nc (layout.tableLogHeights.getD opKeccak 0) i →
      RegionL Lin i)
    (hbus : bus.point.length ≤ 34)
    (hfin : (inner + stackWeight layout (openedClaims claims [out]) ringPoint coeffs lam x) * yr =
      target) :
    CompleteAtD fs cert κ "check_opening_terminal" Lin
      (termArgs B rm gmu gzcn glm gtau lamCl inner yr target) (Returns []) := by
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  swap
  · intro fp
    exact ⟨0, [], [], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, hl0, hm0⟩ := hex
  have P0 := hpre rd0 hl0 hm0
  simp only [TermPre, termArgs] at P0
  obtain ⟨hT, hPC, -, hP, hSL, hSL28, hlm1, hlm32, hbus40, hHL, -, hglm, hgtau, -, -, -, -, hopl,
    -, hrpl, -, hcfl, -, hxl, -, -⟩ := P0
  obtain ⟨chis, -, hgmu, hchR, hgzc, hchL, -⟩ := hT
  obtain ⟨hkap, -⟩ := hPC
  have hncl : chis.length = nc := gen_pow_inj_le (by omega) (by omega) (hgzc.symm.trans hgz)
  subst hncl
  have hchis : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex B.chi)) chis :=
    fun rd _ hm => readsAt_transfer hm0 hm hchR fun k hk => hreg _ (by simp only [TermRegion]; omega)
  set kappas := columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights
    with hkdef
  set KC := Tables.committedKappas kappas with hKCdef
  set τ := layout.tableLogHeights.getD opKeccak 0 with hτ
  have hLdef : layout.stackLog = max Whir.minLogStack (stackOffsets KC).2 := by
    rw [hSL, placementsOf_snd]
  have hKClen : KC.length = Tables.nCommittedCols := Tables.committedKappas_length _ hkap
  have hK : ∀ c < Tables.nCommittedCols, KC.getD c 0 ≤ layout.stackLog := fun c hc ↦ by
    have := size_le_stackOffsets KC (i := c) (by omega); rw [hLdef]; omega
  have hO : ∀ c, (stackOffsets KC).1.getD c 0 < 2 ^ layout.stackLog := fun c ↦
    lt_of_lt_of_le (stackOffsets_lt KC c) (Nat.pow_le_pow_right (by decide) (by rw [hLdef]; omega))
  have hk6 : kappas.take 6 = [layout.logMemory, layout.logMemory, layout.logMemory,
      layout.logMemory, Tables.guestLogBytecode, τ + 6] := kappas_small hHL
  have hK5 : KC.getD 5 0 = τ + 6 := by
    rw [committedKappas_small hkap (by decide), ← getD_take_nat (n := 6) (by decide), hk6]; rfl
  have hK5L := hK 5 (by decide)
  rw [hK5] at hK5L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  set D := termD B layout bus out ringPoint coeffs x chis rm gmu gzcn glm gtau with hD
  have hst : ∀ rd, LowDef κ rd → MemL rd Lin →
      MemL rd (Tables.stLin B.pt B.pt1 (pt28 x) (pt128 x)) := fun rd hl hm q hq => by
    have P := hpre rd hl hm
    simp only [TermPre, termArgs] at P
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpt, hpt1⟩ := P
    simp only [Tables.stLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact readsAt_take hpt 28
    · exact readsAt_take hpt1 28
  have f1 : D.τ + 6 ≤ 34 := by show τ + 6 ≤ 34; omega
  have f2 : D.ringPoint.length = D.τ + 6 := by
    show ringPoint.length = τ + 6; rw [hrpl, Tables.qkeccakSlotBits_eq]
  have f3 : D.coeffs.length = 64 := by show coeffs.length = 64; rw [hcfl]; rfl
  have f4 : D.x.length ≤ 28 := by show x.length ≤ 28; omega
  have f5 : D.outPt.length = D.τ + 6 := by
    show out.point.length = τ + 6; rw [hopl, Tables.qkeccakSlotBits_eq]
  have f7 : D.chis.length ≤ 34 := by show chis.length ≤ 34; omega
  refine completeAt_flatDepR find_term term_not_loop κ Lin _ [] term_body' term_flat term_addrs
    (by decide +kernel)
    [35, 35, 35, 41] (fun _ => termOwn D) (fun _ => ?_)
    (fun fp => termKids Lin D (fp + fs "check_opening_terminal")) (fun fp => ?_)
    (fun fp outs _ => termKids_regions Lin D _ hreg f1 f2 f3 f4 outs)
    (fun fp outs _ rd hl hB hLin hLo => ?_) (fun fp outs hlen' ho rd hl hB hLin _ => ?_)
  · simp only [termOwn, List.forall₂_cons, eqChain_length, piW_length,
      List.Forall₂.nil, and_true]
    have hol : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
    show bus.point.length + 1 ≤ 35 ∧ chis.length + 1 ≤ 35 ∧ layout.logMemory + 1 ≤ 35 ∧
      out.point.length + 1 ≤ 41
    omega
  · refine termKids_complete κ hκ Lin D _ hreg hbus f7 f4 f1 f5 f2 f3 hgmu hgzc hglm hgtau hlm1
      hlm32 (fun c hc => ?_) (fun c hc => ?_)
      (fun rd hl hm => ?_)
    · have := hK c hc; show KC.getD c 0 < 29; omega
    · exact ⟨lt_of_lt_of_le (hO c) (Nat.pow_le_pow_right (by decide) hSL28),
        dvd_stackOffset KC (by omega)⟩
    · have P := hpre rd hl hm
      simp only [TermPre, termArgs] at P
      obtain ⟨⟨chis', hzR, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hoz, -, -, -, -, -,
        -, hpt1⟩ := P
      exact ⟨hzR, hchis rd hl hm, hoz, hpt1⟩
  · have P := hpre rd hl hLin
    simp only [TermPre, termArgs] at P
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hgt, -, -, -, -, -, hrp, -, hct, -, -, hpt1⟩ := P
    refine termKids_mem Lin D _ outs hB hLin hLo (hst rd hl hLin) ?_ fun q hq => ?_
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      rw [ofK_gpow_mul_gen] at hgt
      exact reads_of_gTabs hgt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · show ReadsAt rd (ofK (addressOfIndex (B.zv + 39))) ringPoint
      rw [← ofK_gpow_mul_gen]; exact hrp
    · exact readsAt_take hpt1 _
    · exact hct
  · exact term_sigma B Lin (fp + fs "check_opening_terminal") outs rd (hpre rd hl hLin)
      (hchis rd hl hLin) hgzc (by omega) hreg hbus hfin (by rw [hlen', termKids_length]) ho hB

end
end LeanVM.Guest.B1.VerifySub
