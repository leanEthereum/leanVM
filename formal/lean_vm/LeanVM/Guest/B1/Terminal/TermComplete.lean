/-
  LeanVM.Guest.B1.Terminal.TermComplete

  What the terminal's completeness proofs read from `TermPre` on one memory holding the caller's
  words (`term_setup`).
-/

module

public import LeanVM.Guest.B1.Terminal.TermSigma

/-!
# `check_opening_terminal`, its data fixed

The honest direction of `MeaningTerminal` (`check_opening_terminal_completeAtB`) has these
hypotheses:

* `hpre`: `TermPre` (what `verify_sub` establishes, soundness's precondition) on every memory
  holding the caller's words `Lin` (defined below `2^κ`);
* `hreg`: the words it reads lie in `Lin` (`TermRegion`: the bus point, the tables' point of
  `nc` words, `g^nc` being its argument `g_zc_n`, the base `kappa_base`, the columns' offsets, the
  nibble shares at `g_squares·g^34`, the outputs' and the ring switch's points, the coefficients,
  the terminal point and its complements);
* `hbus`: the bus point has at most `34` coordinates, so its prefix chain (`|bus.point| + 1` words)
  fits the guest's `35`-word buffer (`TermPre` allows `40`);
* `hfin`: the WHIR terminal equation `(inner + basis(x))·residual = target`, `MeaningTerminal`'s
  conclusion;
* `6 ≤ κ`: the memory is defined below `64`, where `eq_prefix_chain`'s range checks read.

The data that do not depend on the memory (the tables' point `chis`, the lengths) come from one
memory holding `Lin` (`term_setup`), as do the facts about them the callees' completeness and the
honest buffers (`termOwn`) need (`TermFacts`); without such a memory the statement is empty.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem readsAt_transfer {rd rd' : Reader} {L : Main.Layout} (h : MemL rd L) (h' : MemL rd' L)
    {b : ℕ} {xs : List E} (hr : ReadsAt rd (ofK (addressOfIndex b)) xs)
    (hreg : ∀ k < xs.length, RegionL L (b + k)) : ReadsAt rd' (ofK (addressOfIndex b)) xs :=
        fun k hk =>
  ⟨(hr k hk).1, by
    rw [Main.addr_ofK, ← Main.memL_agree h h' _ (hreg k hk), ← Main.addr_ofK]; exact (hr k hk).2⟩

/-- **The facts about the terminal's data** its callees' completeness (`termKids_completeB`,
`termKids_regions`, `termKids_mem`) and its honest buffers read. -/
structure TermFacts (κ : ℕ) (Lin : Main.Layout) (D : TermData) : Prop where
  own : List.Forall₂ (fun c s => c.length ≤ s) (termOwn D) [35, 35, 35, 41, 31]
  reg : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ D.ood.length i → RegionL Lin i
  zl : D.zs.length ≤ 34
  cl : D.chis.length ≤ 34
  xl : D.x.length ≤ 32
  τl : D.τ + 6 ≤ 34
  ol : D.outPt.length = D.τ + 6
  rl : D.ringPoint.length = D.τ + 6
  cf : D.coeffs.length = 64
  gmu : D.gmu = gen ^ D.zs.length
  gz : D.gzcn = gen ^ D.chis.length
  glm : D.glm = gen ^ D.m
  gtau : D.gtau = gen ^ D.τ
  m1 : 1 ≤ D.m
  m : D.m ≤ 32
  KC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31
  OF : ∀ c < Tables.nCommittedCols, D.OF.getD c 0 < 2 ^ 32 ∧ 2 ^ D.KC.getD c 0 ∣ D.OF.getD c 0
  rd : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.zeta)) D.zs ∧
    ReadsAt rd (ofK (addressOfIndex D.B.chi)) D.chis ∧
    ReadsAt rd (ofK (addressOfIndex D.B.zv)) D.outPt ∧ ReadsAt rd (ofK (addressOfIndex D.B.pt1)) (p1Of D.x)
  odl : D.ood.length ≤ 30
  gm : D.gm = gen ^ D.ood.length
  rdO : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.oz)) D.ood
  mem : ∀ b0 outs rd, LowDef κ rd → MemL rd (bufL b0 [35, 35, 35, 41, 31] (termOwn D)) → MemL rd Lin →
    MemL rd (outsL (kidsAt (termKids Lin D b0) [] outs) outs) →
    MemL rd (Kid.lins (kidsAt (termKids Lin D b0) [] outs))

/-- **The terminal's data, from one memory holding the caller's words**: the tables' point `chis`
(`nc` words, read on every such memory) and `TermFacts` of the terminal's data. -/
theorem term_setup (κ : ℕ) (B : TermBases) (Lin : Main.Layout)
    {layout : Layout} {bus : BusResult} {claims : List ColumnClaim} {out : ColumnClaim} {lam : E}
    {ringPoint coeffs oodPoint x : List E} {rm gmu gzcn glm gtau lamCl inner yr target gm : E} {nc : ℕ}
    (hnc : nc ≤ 40) (hgz : gzcn = gen ^ nc)
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → TermPre rd layout bus claims out lam ringPoint coeffs
      oodPoint x (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm))
    (hreg : ∀ i, TermRegion B bus.point.length nc (layout.tableLogHeights.getD opKeccak 0)
      layout.stackLog i → RegionL Lin i)
    (hbus : bus.point.length ≤ 34) {rd0 : Reader} (hl0 : LowDef κ rd0) (hm0 : MemL rd0 Lin) :
    ∃ chis : List E, chis.length = nc ∧
      (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex B.chi)) chis) ∧
      TermFacts κ Lin (termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu gzcn glm gtau gm lamCl) := by
  have P0 := hpre rd0 hl0 hm0
  simp only [TermPre, termArgs] at P0
  obtain ⟨hT, hPC, -, hP, hSL, hSL30, hlm1, hlm32, hbus40, hHL, -, hglm, hgtau, -, -, -, -, hopl,
    -, hrpl, -, hcfl, -, hxl, -, -, hodl, -, hgm⟩ := P0
  have hSL28 : layout.stackLog ≤ 32 := by omega
  obtain ⟨chis, -, hgmu, hchR, hgzc, hchL, -⟩ := hT
  obtain ⟨hkap, -⟩ := hPC
  have hncl : chis.length = nc := gen_pow_inj_le (by omega) (by omega) (hgzc.symm.trans hgz)
  subst hncl
  have hchis : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex B.chi)) chis :=
    fun rd _ hm => readsAt_transfer hm0 hm hchR fun k hk => hreg _ (by term_region)
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
  have hk5 : kappas.take 5 = [layout.logMemory, layout.logMemory, layout.logMemory,
      Tables.guestLogBytecode, τ + 6] := kappas_small hHL
  have hK4 : KC.getD 4 0 = τ + 6 := by
    rw [committedKappas_small hkap (by decide), ← getD_take_nat (n := 5) (by decide), hk5]; rfl
  have hK4L := hK 4 (by decide)
  rw [hK4] at hK4L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hol : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
  refine ⟨chis, rfl, hchis, ?own, ?reg, hbus, (by omega : chis.length ≤ 34), (by omega : x.length ≤ 32), (by omega : τ + 6 ≤ 34),
    hol, (by rw [hrpl, Tables.qkeccakSlotBits_eq] : ringPoint.length = τ + 6),
    (by rw [hcfl]; rfl : coeffs.length = 64), hgmu, hgzc, hglm, hgtau, hlm1, hlm32,
    fun c hc => (by have := hK c hc; omega : KC.getD c 0 < 31),
    fun c hc => ⟨lt_of_lt_of_le (hO c) (Nat.pow_le_pow_right (by decide) hSL28),
      dvd_stackOffset KC (by omega)⟩, fun rd hl hm => ?rd, (by omega : oodPoint.length ≤ 30),
    (by rw [hgm, hodl] : gm = gen ^ oodPoint.length), fun rd hl hm => ?rdO,
    fun b0 outs rd hl hB hLin hLo => ?mem⟩
  case own =>
    simp only [termOwn, List.forall₂_cons, eqChain_length, piW_length, List.Forall₂.nil, and_true]
    show bus.point.length + 1 ≤ 35 ∧ chis.length + 1 ≤ 35 ∧ layout.logMemory + 1 ≤ 35 ∧
      out.point.length + 1 ≤ 41 ∧ oodPoint.length + 1 ≤ 31
    omega
  case reg =>
    show ∀ i, TermRegion B bus.point.length chis.length τ oodPoint.length i → RegionL Lin i
    rw [hodl]; exact hreg
  case rd =>
    have P := hpre rd hl hm
    simp only [TermPre, termArgs] at P
    obtain ⟨⟨chis', hzR, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hoz, -, -, -, -, -,
      -, hpt1, -⟩ := P
    exact ⟨hzR, hchis rd hl hm, hoz, hpt1⟩
  case rdO =>
    have P := hpre rd hl hm
    simp only [TermPre, termArgs] at P
    exact P.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  case mem =>
    have P := hpre rd hl hLin
    simp only [TermPre, termArgs] at P
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hgt, -, -, -, -, -, hrp, -, hct, -, hpt, hpt1, -⟩ :=
      P
    refine termKids_mem Lin _ _ outs hB hLin hLo (fun q hq => ?_) ?_ fun q hq => ?_
    · simp only [Tables.stLin, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact readsAt_take hpt 32
      · exact readsAt_take hpt1 32
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

end
end LeanVM.Guest.B1.VerifySub
