/-
  LeanVM.Guest.B1.Terminal.TermSigma

  `check_opening_terminal`'s honest valuation: on a memory holding the caller's words (its
  precondition `TermPre`), its buffers and its callees' results, every statement holds, every
  load lies in those words, and the frames match its callees; its last check is the WHIR terminal.
-/

module

public import LeanVM.Guest.B1.Terminal.TermEval
public import LeanVM.Protocol.EndToEnd.Complete.BusStack

/-!
# The terminal's honest valuation

`termD`: the honest data of `TermPre`'s parameters. `term_sigma`: the evaluated valuation
(`termW`'s oracle) satisfies what `completeAt_flatDepR` asks: the parameters, the dispatches, the
body (its claims' blocks by `claimsT_complete`, its head, selectors and tail by `TermEval`), the
buffers, the frames (`callsMatch_kidsAt`) and the loads. Its last check: the sum the blocks build is
the opening's weight, as in the soundness proof (`claimsT_sound`, `claimTerm_eq`, `stackWeight_eq`),
so the honest terminal equation passes it.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (MemL RegionL)
open Finset

@[expose] public section

/-! ## Facts -/

theorem dvd_stackOffset (sizes : List ℕ) {b : ℕ} (hb : b < sizes.length) :
    2 ^ sizes.getD b 0 ∣ (stackOffsets sizes).1.getD b 0 := by
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem (EndToEnd.Complete.mem_stackOrder.mpr hb)
  have := EndToEnd.Complete.dvd_blockOffset sizes k hk
  rw [e] at this
  exact this

theorem dispOk_of_noDisp {σ : Val} {s : Stmt} (h : noDispB s = true) : DispOk σ s := by
  cases s <;> simp_all [DispOk, noDispB]

def isAtomB : Stmt → Bool
  | .atom _ => true
  | _ => false

theorem claims_atoms : termClaims.1.all isAtomB = true := by decide +kernel

theorem getD_seg {α : Type} (A M Z : List α) (d : α) (hA : A.length = 4) (hM : M.length = 94)
    (j : ℕ) : (A ++ M ++ Z).getD j d =
      if j < 4 then A.getD j d else if j < 98 then M.getD (j - 4) d else Z.getD (j - 98) d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.append_assoc, List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hA]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp [hA, hM]

theorem getD_map_lt {α β : Type} (f : α → β) {l : List α} {j : ℕ} (d : α) (d' : β)
    (h : j < l.length) : (l.map f).getD j d' = f (l.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

/-- The honest data of `TermPre`'s parameters: the out-of-domain chain's seed is the power of
`lam_cl` after the kept claims, times `lam_cl`. -/
def termD (B : TermBases) (layout : Layout) (bus : BusResult) (out : ColumnClaim)
    (ringPoint coeffs x chis oodPoint : List E) (rm gmu gzcn glm gtau gm lamCl : E) : TermData where
  B := B
  rm := rm
  gmu := gmu
  gzcn := gzcn
  glm := glm
  gtau := gtau
  zs := bus.point
  chis := chis
  outPt := out.point
  ringPoint := ringPoint
  coeffs := coeffs
  x := x
  ood := oodPoint
  gm := gm
  sO := lamCl ^ (1 + poolRank Tables.nClaims) * lamCl
  KC := Tables.committedKappas
    (columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights)
  OF := (stackOffsets (Tables.committedKappas
    (columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights))).1
  m := layout.logMemory
  τ := layout.tableLogHeights.getD opKeccak 0

theorem termKids_getD_sel (Lin : Main.Layout) (D : TermData) (b0 : ℕ) {c : ℕ}
    (hc : c < Tables.nCommittedCols) : (termKids Lin D b0).getD (4 + c) noKid = selKid D c := by
  have hc' : c < 94 := hc
  rw [termKids, getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols]), ite_neg' (by omega),
    ite_pos' (by omega), show 4 + c - 4 = c by omega,
    List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

theorem termKids_getD_out (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    (termKids Lin D b0).getD 98 noKid = fun _ => ⟨"eq_prefix_chain", true,
      [ofK (addressOfIndex (b0 + 105)), word 1 0, ofK (addressOfIndex D.B.zv),
        ofK (addressOfIndex D.B.pt1), D.gtau * word 64 0],
      (b0 + 105, eqChain (word 1 0) D.outPt ((p1Of D.x).take D.outPt.length)) :: Lin,
      Returns []⟩ := by
  rw [termKids, getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols]), ite_neg' (by omega),
    ite_neg' (by omega)]
  rfl

theorem termKids_getD_rsw (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    (termKids Lin D b0).getD 99 noKid = fun _ => ⟨"ring_switch_weight", true,
      [ofK (addressOfIndex D.B.zv) * word 549755813888 0, ofK (addressOfIndex D.B.pt1),
        ofK (addressOfIndex D.B.ct), D.gtau * word 64 0],
      [(D.B.zv + 39, D.ringPoint), (D.B.pt1, (p1Of D.x).take (D.τ + 6)), (D.B.ct, D.coeffs)],
      Returns [ringWeight D.ringPoint (((p1Of D.x).take (D.τ + 6)).map (1 + ·)) D.coeffs]⟩ := by
  rw [termKids, getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols]), ite_neg' (by omega),
    ite_neg' (by omega)]
  rfl

theorem termKids_getD_ood (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    (termKids Lin D b0).getD 100 noKid = fun _ => ⟨"eq_prefix_chain", true,
      [ofK (addressOfIndex (b0 + 146)), D.sO, ofK (addressOfIndex D.B.oz),
        ofK (addressOfIndex D.B.pt1), D.gm],
      (b0 + 146, eqChain D.sO D.ood ((p1Of D.x).take D.ood.length)) :: Lin, Returns []⟩ := by
  rw [termKids, getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols]), ite_neg' (by omega),
    ite_neg' (by omega)]
  rfl

/-! ## The honest valuation -/

/-- The base's words `[1, g^log_mem, g^τ_0, …, g^τ_5]`. -/
def kbWords (layout : Layout) : List E :=
  1 :: gen ^ layout.logMemory :: layout.tableLogHeights.map (gen ^ ·)

theorem kbWords_getD {layout : Layout} (hl : layout.tableLogHeights.length = 6) {i : ℕ}
    (hi : i < 8) : (kbWords layout).getD i 0 = gen ^ kbExp layout i := by
  rw [List.getD_eq_getElem _ _ (by simp [kbWords, hl]; omega)]
  exact kb_words hl hi

/-- An honest prefix chain's word `n`: the seed times the eq weight of the prefixes. -/
theorem eqChain_value {s : E} {as x : List E} {n : ℕ} (hn : n ≤ as.length)
    (hx : x.length ≤ termPointCap) (hnx : n ≤ x.length) :
    (eqChain s as ((p1Of x).take as.length)).getD n 0 = s * eqEval (as.take n) (x.take n) := by
  have hpl : (p1Of x).length = 40 := p1Of_length hx
  have hx' : x.length ≤ 40 := hx
  simp only [eqChain]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
    prefixProd_seed]
  refine congrArg (s * ·) (prefixProd_eq hn (by simp [hpl]; omega) hnx fun i hi => ?_)
  have : ((p1Of x).take as.length).getD i 0 = (p1Of x).getD i 0 := by
    simp [List.getD_eq_getElem?_getD, show i < as.length by omega]
  rw [this]
  exact x1_getD hx (by simp only [termPointCap]; omega)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **`check_opening_terminal`'s honest valuation**, on a memory holding the caller's words, the
buffers and the callees' results: what `completeAt_flatDepR` asks of it. -/
theorem term_sigma (B : TermBases) (Lin : Main.Layout) {layout : Layout} {bus : BusResult}
    {claims : List ColumnClaim} {out : ColumnClaim} {lam : E}
    {ringPoint coeffs x chis oodPoint : List E}
    {rm gmu gzcn glm gtau lamCl inner yr target gm : E} (b0 : ℕ)
    (outs : List (List E × Main.Layout)) (rd : Reader)
    (P : TermPre rd layout bus claims out lam ringPoint coeffs oodPoint x
      (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm))
    (hchis : ReadsAt rd (ofK (addressOfIndex B.chi)) chis) (hgz : gzcn = gen ^ chis.length)
    (hcl : chis.length ≤ 34)
    (hreg : ∀ i, TermRegion B bus.point.length chis.length (layout.tableLogHeights.getD opKeccak 0)
      layout.stackLog i → RegionL Lin i)
    (hbus : bus.point.length ≤ 34)
    (hfin : (inner + stackWeight layout (openedClaims claims [out]) ringPoint coeffs oodPoint lam x) *
      yr = target)
    (hol : outs.length = 101)
    (ho : OutsOk (kidsAt (termKids Lin (termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu
      gzcn glm gtau gm lamCl) b0) [] outs) outs)
    (hB : MemL rd (bufL b0 [35, 35, 35, 41, 31]
      (termOwn (termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu gzcn glm gtau gm
        lamCl)))) :
    ∃ σ : Val, (fn% «check_opening_terminal»).params.map σ = termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm ∧
      (∀ s ∈ termPre, DispOk σ s) ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «check_opening_terminal»).body False (fun r => r = []) ∧
      (termPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) =
        [35, 35, 35, 41, 31] ∧
      ((termPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b0 [35, 35, 35, 41, 31]).map (fun b => ofK (addressOfIndex b)) ∧
      CallsMatch σ ((termPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (kidsAt (termKids Lin (termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu gzcn glm
          gtau gm lamCl) b0) [] outs) outs ∧
      ∀ q ∈ termPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
          addressOfIndex i ∧
        (RegionL Lin i ∨ RegionL (bufL b0 [35, 35, 35, 41, 31]
          (termOwn (termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu gzcn glm gtau gm
            lamCl))) i ∨
          outRegion (kidsAt (termKids Lin (termD B layout bus out ringPoint coeffs x chis oodPoint rm
            gmu gzcn glm gtau gm lamCl) b0) [] outs) outs i) := by
  set D := termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu gzcn glm gtau gm lamCl
    with hD
  set args := termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm with hargs
  -- the precondition
  simp only [TermPre, hargs, termArgs] at P
  obtain ⟨hT, hPC, -, hP, hSL, hSL30, hlm1, -, hbus40, hHL, -, hglm, hgtau, hkbR, -, hlamC,
    hoc, hopl, hoz, hrpl, hrp, hcfl, hct, hxl, hpt, hpt1, hodl, hodR, hgm⟩ := P
  have hSL28 : layout.stackLog ≤ 32 := by omega
  obtain ⟨chis', hzR, hgmu, hchR, hgzc, hchL, -, hcols, hpts⟩ := hT
  obtain ⟨hkap, hOr⟩ := hPC
  have hcc : chis' = chis := by
    have hl : chis'.length = chis.length :=
      gen_pow_inj_le (by omega) (by omega) (hgzc.symm.trans hgz)
    exact readsAt_unique hchR hchis hl
  subst hcc
  set kappas := columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights
    with hkdef
  set KC := Tables.committedKappas kappas with hKCdef
  set τ := layout.tableLogHeights.getD opKeccak 0 with hτ
  set m := layout.logMemory with hmdef
  have hKClen : KC.length = Tables.nCommittedCols := Tables.committedKappas_length _ hkap
  have hKC : KC = (List.range Tables.nCommittedCols).map fun c ↦
      (0 :: layout.logMemory :: layout.tableLogHeights).getD (Tables.colKappaSrc c) 0 +
        Tables.colKappaAdj c :=
    Tables.committedKappas_columnKappas layout.logMemory layout.tableLogHeights hHL
  have hLdef : layout.stackLog = max Whir.minLogStack (stackOffsets KC).2 := by
    rw [hSL, placementsOf_snd]
  have hK : ∀ c < Tables.nCommittedCols, KC.getD c 0 ≤ layout.stackLog := fun c hc ↦ by
    have := size_le_stackOffsets KC (i := c) (by omega); rw [hLdef]; omega
  have hO : ∀ c, (stackOffsets KC).1.getD c 0 < 2 ^ layout.stackLog := fun c ↦
    lt_of_lt_of_le (stackOffsets_lt KC c) (Nat.pow_le_pow_right (by decide) (by rw [hLdef]; omega))
  have hoff' : ∀ c < Tables.nCommittedCols,
      LoadHolds rd (ofK (addressOfIndex B.off)) c (gen ^ (stackOffsets KC).1.getD c 0) :=
    fun c hc ↦ by
      have hl : c < (stackOffsets KC).1.length := by rw [stackOffsets_length]; omega
      have := hOr c (by simpa using hl)
      rw [List.getElem_map] at this
      rw [List.getD_eq_getElem _ _ hl]; exact this
  have hKCv : ∀ c < Tables.nCommittedCols, KC.getD c 0 =
      kbExp layout (Tables.colKappaSrc c) + Tables.colKappaAdj c := fun c hc ↦ by
    rw [hKC, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]
    rfl
  have hsrc8 : ∀ c, Tables.colKappaSrc c < 8 := fun c ↦ by
    unfold Tables.colKappaSrc; split_ifs <;> omega
  have hk5 : kappas.take 5 = [layout.logMemory, layout.logMemory, layout.logMemory,
      Tables.guestLogBytecode, τ + 6] := kappas_small hHL
  have hksmall : ∀ c < 5, kappas.getD c 0 =
      [layout.logMemory, layout.logMemory, layout.logMemory, Tables.guestLogBytecode,
        τ + 6].getD c 0 := fun c hc ↦ by
    rw [← hk5, getD_take_nat hc]
  have hK4 : KC.getD 4 0 = τ + 6 := by
    rw [committedKappas_small hkap (by decide), hksmall 4 (by decide)]; rfl
  have hmem : ∀ c < 3, KC.getD c 0 = layout.logMemory := fun c hc ↦ by
    rw [committedKappas_small hkap (by omega), hksmall c (by omega)]
    interval_cases c <;> rfl
  have hK4L := hK 4 (by decide)
  rw [hK4] at hK4L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hpl40 : (p1Of x).length = 40 := p1Of_length hxl40
  have hpt40 : (padPoint x).length = 40 := padPoint_length hxl40
  have hclen : claims.length = 159 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  have hptj : ∀ j < 159, (claims.map (·.point))[j]? = some (claims.getD j default).point :=
    fun j hj ↦ by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
      rfl
  have hlow : ∀ j < 157, (claims.getD j default).point.length = claimLow layout j := fun j hj ↦
    (hpts j _ (hptj j (by omega))).1 hj
  have hpz' : ∀ j < 4, claimLow layout j ≤ bus.point.length := fun j hj ↦ by
    have := congrArg List.length ((hpts j _ (hptj j (by omega))).2.1 hj)
    rw [List.length_take, hlow j (by omega)] at this
    omega
  have hpc' : ∀ j, 4 ≤ j → j < 157 → claimLow layout j ≤ chis'.length := fun j h1 h2 ↦ by
    have := congrArg List.length ((hpts j _ (hptj j (by omega))).2.2.1 h1 h2)
    rw [List.length_take, hlow j h2] at this
    omega
  -- the valuation
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = B1.Val.ofArgs (ev rd (termW b0 outs) args termT) := ⟨_, rfl⟩
  have hchk : chk args.length termT = some 1715 := term_chk
  have hgs : ∀ s ∈ termT, GoodS rd [.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1]
      (termW b0 outs) σ s := by
    have h := (ev_spec rd (termW b0 outs) termT args hchk).2.2
    rw [show args.length = 20 from rfl, term_stores, ← hσdef] at h
    exact h
  have ea : ∀ i, i < 20 → σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσdef]; exact ev_params rd _ hchk (by simpa [hargs, termArgs] using hi)
  have e0 : σ (.n 0) = ofK (addressOfIndex B.gsq) := ea 0 (by omega)
  have e3 : σ (.n 3) = rm := ea 3 (by omega)
  have e6 : σ (.n 6) = glm := ea 6 (by omega)
  have e7 : σ (.n 7) = gtau := ea 7 (by omega)
  have e8 : σ (.n 8) = ofK (addressOfIndex B.kb) := ea 8 (by omega)
  have e9 : σ (.n 9) = lamCl := ea 9 (by omega)
  have e10 : σ (.n 10) = ofK (addressOfIndex B.off) := ea 10 (by omega)
  have e11 : σ (.n 11) = ofK (addressOfIndex B.zv) := ea 11 (by omega)
  have e13 : σ (.n 13) = ofK (addressOfIndex B.pt) := ea 13 (by omega)
  have e14 : σ (.n 14) = ofK (addressOfIndex B.pt1) := ea 14 (by omega)
  have e18 : σ (.n 18) = ofK (addressOfIndex B.oz) := ea 18 (by omega)
  have e19 : σ (.n 19) = gm := ea 19 (by omega)
  have hS : StoresAtPi [Atom.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1] := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> exact ⟨_, _, rfl⟩
  have gPre : ∀ s ∈ termPre, GoodS rd [.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1]
      (termW b0 outs) σ s := fun s hs => hgs s (by rw [termT_split]; exact List.mem_append_left _ hs)
  have gH : ∀ s ∈ termHeadT, GoodS rd [.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hs)))
  have gS : ∀ s ∈ selsT, GoodS rd [.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))
  have gC : ∀ s ∈ termClaims.1, GoodS rd [.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_left _ (List.mem_append_right _ hs))
  have gT : ∀ s ∈ termTailPre, GoodS rd [.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_right _ hs)
  have e7' : σ (.n 7) = gen ^ τ := by rw [e7, hgtau]
  have hoL : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
  -- the regions
  set R : ℕ → Prop := fun i => RegionL Lin i ∨
    RegionL (bufL b0 [35, 35, 35, 41, 31] (termOwn D)) i ∨
    outRegion (kidsAt (termKids Lin D b0) [] outs) outs i with hR
  have aL : ∀ b k, TermRegion B bus.point.length chis'.length τ layout.stackLog (b + k) →
      AddrIn R (ofK (addressOfIndex b)) k := fun b k h
          => ⟨b + k, Main.addr_ofK b k, Or.inl (hreg _ h)⟩
  have hBuf := hB
  rw [termBuf_eq] at hBuf
  have rB : ∀ i, RegionL (termBufs D b0) i → R i := fun i h =>
    Or.inr (Or.inl (by rw [termBuf_eq]; exact h))
  have m0 : (b0, eqChain (word 1 0) bus.point ((p1Of x).take bus.point.length)) ∈ termBufs D b0 :=
    List.mem_cons_self
  have m1 : (b0 + 35, eqChain (word 1 0) chis' ((p1Of x).take chis'.length)) ∈ termBufs D b0 :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : (b0 + 70, piW rm (p1Of x) m) ∈ termBufs D b0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : (b0 + 105, eqChain (word 1 0) out.point ((p1Of x).take out.point.length)) ∈
      termBufs D b0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have m4 : (b0 + 146, eqChain D.sO oodPoint ((p1Of x).take oodPoint.length)) ∈ termBufs D b0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  -- the head
  have h14 : LoadHolds rd (σ (.n 14)) 0 ((p1Of x).getD 0 0) := by
    rw [e14]; exact readsAt_getD hpt1 (by simp [padPoint_length hxl40])
  have hkbL : ∀ i < 8, LoadHolds rd (σ (.n 8)) i ((kbWords layout).getD i 0) := fun i hi ↦ by
    rw [e8, List.getD_eq_getElem _ _ (by simp [kbWords, hHL]; omega)]
    exact hkbR i (by simp [hHL]; omega)
  obtain ⟨hHs, hHl, e20, e21, e22, e23, e24, e25, e26, e31, e32, e34, ekb, e43⟩ :=
    head_complete (R := R) hS gH (m := m) (rm := rm) (ps := p1Of x) (kbw := kbWords layout) hlm1
      (by rw [e6, hglm]) e3 h14
      (by rw [e14]; exact aL _ _ (by simp only [TermRegion]; omega)) (hBuf _ m2)
      (fun k hk => rB _ ⟨_, m2, by omega, by rw [piW_length]; omega⟩) hkbL
      (fun i hi => by rw [e8]; exact aL _ _ (by simp only [TermRegion]; omega))
  have hkb : ∀ i < 8, σ (.n (kbV i)) = gen ^ kbExp layout i := fun i hi ↦ by
    rw [ekb i hi, kbWords_getD hHL hi]
  have hkapc : ∀ c < Tables.nCommittedCols,
      σ (.n (kbV (Tables.colKappaSrc c))) * gen ^ Tables.colKappaAdj c = gen ^ KC.getD c 0 :=
    fun c hc ↦ by rw [hkb _ (hsrc8 c), hKCv c hc, pow_add]
  -- the selectors
  have hst3 : Tables.stOut B.pt B.pt1 (pt32 x) (pt132 x) (stRes outs).1 (stRes outs).2 := by
    have := outsOk_at ho 3 (by rw [termKids_length]; omega) (by omega) (by rw [termKid3])
    rw [termKid3] at this
    exact this
  have hKC31 : ∀ c < Tables.nCommittedCols, KC.getD c 0 < 31 := fun c hc => by
    have := hK c hc; omega
  have hsl : ∀ c, c < Tables.nCommittedCols →
      (∀ s ∈ selBlockT c, Fwd.SHolds TrivC rd σ s) ∧ (∀ s ∈ selBlockT c, DispOk σ s) ∧
      (∀ q ∈ (selBlockT c).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n (selStart c)) = gen ^ (stackOffsets KC).1.getD c 0 ∧
      σ (.n (selKap c).2.1) = gen ^ KC.getD c 0 ∧
      σ (.n ((selKap c).2.2 + 1)) = σ (.n 0) * gen ^ 34 ∧
      σ (.n (selV c)) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := fun c hc =>
    sel_complete hS hc (fun s hs => gS s (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hs⟩))
      (hKC31 c hc) (by rw [e10]; exact hoff' c hc)
      (by rw [e10]; exact aL _ _ (by simp only [TermRegion]; omega))
      (hkapc c hc)
  have hselv : ∀ c < Tables.nCommittedCols, σ (.n (selV c)) =
      selProd ((stackOffsets KC).1.getD c 0) (KC.getD c 0) (layout.stackLog - KC.getD c 0) x := by
    intro c hc
    have hc' : c < 94 := hc
    have ht : (kidAt (termKids Lin D b0) [] outs (4 + c)).taken = true := by
      unfold kidAt
      rw [List.nil_append, termKids_getD_sel Lin D b0 hc]
      refine @decide_eq_true _ (Classical.propDecidable _) ?_
      rw [stRes_take, ite_pos' (by omega)]
      exact hst3
    have := outsOk_at ho (4 + c) (by rw [termKids_length]; omega) (by omega) ht
    unfold kidAt at this
    rw [List.nil_append, termKids_getD_sel Lin D b0 hc] at this
    obtain ⟨h1, -⟩ := this
    rw [(hsl c hc).2.2.2.2.2.2, h1]
    rw [List.getD_cons_zero]
    show selRet x KC (stackOffsets KC).1 c = _
    unfold selRet pt32 pt132 p1Of
    rw [bitsEq_sel _ (by have := hK c hc; omega) hxl40,
      selProd_pad hxl (hO c) (hK c hc) (by omega)]
  -- the claims
  have hslot : ∀ k < 6, ∀ t, (t = 24 ∨ t = 25) →
      (∃ v, LoadHolds rd (σ (.n t)) k v) ∧ AddrIn R (σ (.n t)) k := by
    intro k hk t ht
    rcases ht with rfl | rfl
    · rw [e24, e13, e7']
      exact ⟨⟨_, (loadHolds_mul_gen_pow _ _ _ _ _).mpr (readsAt_getD hpt (k := τ + k) (by omega))⟩,
        ⟨B.pt + τ + k, rt_addr_mul _ _ _, Or.inl (hreg _ (by simp only [TermRegion]; omega))⟩⟩
    · rw [e25, e14, e7']
      exact ⟨⟨_, (loadHolds_mul_gen_pow _ _ _ _ _).mpr (readsAt_getD hpt1 (k := τ + k)
        (by simp [padPoint_length hxl40]; omega))⟩,
        ⟨B.pt1 + τ + k, rt_addr_mul _ _ _, Or.inl (hreg _ (by simp only [TermRegion]; omega))⟩⟩
  have hin : ∀ j ∈ List.range Tables.nClaims, ClaimIn rd σ R (kbExp layout) j := by
    intro j hj
    have hj' : j < 159 := List.mem_range.mp hj
    obtain ⟨-, -, -, -, f0, f1, -, f3⟩ := claimFact_all j hj'
    unfold ClaimIn
    rw [cLow_kbExp _ hj']
    split
    · rename_i hk
      have hj4 : j < 4 := (f0 hk).1
      have hle := hpz' j hj4
      refine ⟨⟨_, by
        rw [e20, loadHolds_mul_gen_pow, Nat.add_zero]
        exact readsAt_getD (hBuf _ m0) (by rw [eqChain_length]; omega)⟩, ?_⟩
      rw [e20]
      exact ⟨b0 + claimLow layout j + 0, rt_addr_mul _ _ _,
        rB _ ⟨_, m0, by omega, by rw [eqChain_length]; omega⟩⟩
    · rename_i hk
      have hj4 : 4 ≤ j ∧ j < 157 := ⟨(f1 hk).1, (f1 hk).2.1⟩
      have hle := hpc' j hj4.1 hj4.2
      refine ⟨⟨_, by
        rw [e22, loadHolds_mul_gen_pow, Nat.add_zero]
        exact readsAt_getD (hBuf _ m1) (by rw [eqChain_length]; omega)⟩, ?_⟩
      rw [e22]
      exact ⟨b0 + 35 + claimLow layout j + 0, rt_addr_mul _ _ _,
        rB _ ⟨_, m1, by omega, by rw [eqChain_length]; omega⟩⟩
    · rename_i hk
      have hj4 : 4 ≤ j ∧ j < 157 := ⟨(f3 hk).1, (f3 hk).2.1⟩
      have hle := hpc' j hj4.1 hj4.2
      refine ⟨⟨_, by
        rw [e22, loadHolds_mul_gen_pow, Nat.add_zero]
        exact readsAt_getD (hBuf _ m1) (by rw [eqChain_length]; omega)⟩, ?_⟩
      rw [e22]
      exact ⟨b0 + 35 + claimLow layout j + 0, rt_addr_mul _ _ _,
        rB _ ⟨_, m1, by omega, by rw [eqChain_length]; omega⟩⟩
    · exact True.intro
  obtain ⟨hCs, hCl⟩ := claimsT_complete (C := TrivC) hS hkb hslot (List.range Tables.nClaims)
    claimsStart 15 9 (by decide) (by decide) (by decide) (fun j hj => List.mem_range.mp hj) hin gC
  -- the tail
  have hchO : LoadHolds rd (ofK (addressOfIndex (b0 + 105))) (τ + 6)
      ((eqChain (word 1 0) out.point ((p1Of x).take out.point.length)).getD (τ + 6) 0) :=
    readsAt_getD (hBuf _ m3) (by rw [eqChain_length]; omega)
  have hchD : LoadHolds rd (ofK (addressOfIndex (b0 + 146))) layout.stackLog
      ((eqChain D.sO oodPoint ((p1Of x).take oodPoint.length)).getD layout.stackLog 0) :=
    readsAt_getD (hBuf _ m4) (by rw [eqChain_length]; omega)
  obtain ⟨hTs, hTl, e1694, e1695, e1697, e1699, e1701, e1702, e1704, e1709, e1710, e1712, e1714⟩ :=
    tail_complete (R := R) hS gT e7' (by rw [e19, hgm]) hchO
      (rB _ ⟨_, m3, by omega, by rw [eqChain_length]; omega⟩) hchD
      (rB _ ⟨_, m4, by omega, by rw [eqChain_length]; omega⟩)
  -- the claims' sum
  have hclH : Stmt.HoldsList TrivC rd σ termClaims.1 True (fun _ => True) := by
    refine holdsList_of_atoms _ (fun s hs => ?_) trivial
    have hat := List.all_eq_true.mp claims_atoms s hs
    cases s with
    | atom a => exact ⟨a, rfl, hCs _ hs⟩
    | _ => simp [isAtomB] at hat
  rw [termClaims, List.range_eq_range'] at hclH
  have h9 : σ (.n 9) = lam := by rw [e9, hlamC]
  obtain ⟨hsum, hlamO, -⟩ := claimsT_sound (C := TrivC) hkb (rk := poolRank) h9 159 0 claimsStart
    15 9 (fun j hj ↦ poolRank_succ (by omega)) (by rw [h9]; simp [poolRank]) hclH
  rw [show (claimsT (List.range' 0 159) claimsStart 15 9).2 = (1694, 1692, 1693) by
    rw [← termClaims_end, termClaims, List.range_eq_range']] at hsum hlamO
  simp only [zero_add] at hsum hlamO
  -- the context of the claims' terms
  have hmem0 : (layout.placement memory0).variableCount = layout.logMemory := by
    have := placement_committed hkap hP (cc := 0) (by decide)
    rw [committedCols_getD (by decide)] at this
    rw [show memory0 = 0 from rfl, show colOfCommitted 0 = 0 from rfl] at *
    rw [this, hmem 0 (by decide)]
  have hmx : m ≤ x.length := by have := hK 0 (by decide); rw [hmem 0 (by decide)] at this; omega
  have hzc : ∀ n ≤ bus.point.length, n ≤ layout.stackLog →
      valOf rd (σ (.n 20)) n = eqEval (bus.point.take n) (x.take n) := fun n h1 h2 => by
    rw [e20, valOf_eq (readsAt_getD (hBuf _ m0) (by rw [eqChain_length]; omega)),
      eqChain_value h1 hxl40 (by omega), word_one, one_mul]
  have hrc : ∀ n ≤ chis'.length, n ≤ layout.stackLog →
      valOf rd (σ (.n 22)) n = eqEval (chis'.take n) (x.take n) := fun n h1 h2 => by
    rw [e22, valOf_eq (readsAt_getD (hBuf _ m1) (by rw [eqChain_length]; omega)),
      eqChain_value h1 hxl40 (by omega), word_one, one_mul]
  have hs1 : ∀ k < 6, valOf rd (σ (.n 24)) k = x.getD (τ + k) 0 := fun k hk => by
    rw [e24, e13, e7', valOf_eq ((loadHolds_mul_gen_pow _ _ _ _ _).mpr
      (readsAt_getD hpt (k := τ + k) (by omega)))]
    exact padPoint_getD x (τ + k)
  have hs0 : ∀ k < 6, valOf rd (σ (.n 25)) k = 1 + x.getD (τ + k) 0 := fun k hk => by
    rw [e25, e14, e7', valOf_eq ((loadHolds_mul_gen_pow _ _ _ _ _).mpr
      (readsAt_getD hpt1 (k := τ + k) (by simp [padPoint_length hxl40]; omega)))]
    exact x1_getD hxl40 (by simp only [termPointCap]; omega)
  have h34 : σ (.n 34) = eqEval (rm :: List.replicate (m - 1) 0) (x.take m) := by
    rw [e34, piW_getD le_rfl, ite_neg' (by omega)]
    show (rm + ((padPoint x).map (1 + ·)).getD 0 0) *
      ∏ i ∈ Ico 1 m, ((padPoint x).map (1 + ·)).getD i 0 = _
    rw [x1_getD hxl40 (by decide), ← piChain_eq hlm1 hmx]
    refine congrArg (_ * ·) (prod_congr rfl fun i hi ↦ ?_)
    rw [x1_getD hxl40 (by have := (mem_Ico.mp hi).2; simp only [termPointCap]; omega)]
  have T : ClaimsCtx rd σ layout kappas claims bus.point chis' x rm :=
    { hkap := hkap, hKC := hKC, hP := hP, hx := hxl, hL := hSL28, hK := hK,
      hq := stackOffsets_dvd KC 4, hK4 := hK4,
      hlane := fun g h1 h2 ↦ kappas_keccak hHL (by omega) (by omega), hmem := hmem,
      hlm := hlm1, hmem0 := hmem0, hcols := hcols, hzs := hbus40, hchis := hchL,
      hpz := fun j hj ↦ (hpts j _ (hptj j (by omega))).2.1 hj,
      hpc := fun j h1 h2 ↦ (hpts j _ (hptj j (by omega))).2.2.1 h1 h2,
      hpp := fun j h1 h2 ↦ (hpts j _ (hptj j h2)).2.2.2 h1,
      hlen := hlow, hsel := hselv, hzc := hzc, hrc := hrc, hs1 := hs1, hs0 := hs0, hpi := h34 }
  -- the terminal check
  have hq4 := placement_committed hkap hP (cc := 4) (by decide)
  rw [committedCols_getD (by decide), show colOfCommitted 4 = 4 from rfl] at hq4
  have hret : σ (.n 1702) = ringWeight ringPoint (x.take (τ + 6)) coeffs := by
    have ht : (kidAt (termKids Lin D b0) [] outs 99).taken = true := by
      unfold kidAt; rw [List.nil_append, termKids_getD_rsw]
    have := outsOk_at ho 99 (by rw [termKids_length]; omega) (by omega) ht
    unfold kidAt at this
    rw [List.nil_append, termKids_getD_rsw] at this
    obtain ⟨h1, -⟩ := this
    rw [e1702, h1]
    show ringWeight ringPoint ((((padPoint x).map (1 + ·)).take (τ + 6)).map (1 + ·)) coeffs = _
    rw [map_one_take (by omega)]
  have h1704 : σ (.n 1704) = eqEval out.point (x.take (τ + 6)) := by
    rw [e1704, show τ + 6 = out.point.length from hoL.symm, eqChain_value le_rfl hxl40 (by omega),
      word_one, one_mul, List.take_of_length_le le_rfl]
  have h1712 : σ (.n 1712) = lam ^ (1 + poolRank Tables.nClaims) * lam * eqEval oodPoint x := by
    rw [e1712, show layout.stackLog = oodPoint.length from hodl.symm,
      eqChain_value le_rfl hxl40 (by omega), List.take_of_length_le le_rfl,
      List.take_of_length_le (by omega)]
    show (lamCl ^ (1 + poolRank Tables.nClaims) * lamCl) * _ = _
    rw [hlamC]
  have hfin' : σ (.n 1714) = σ (.n 17) := by
    have e15 : σ (.n 15) = inner := ea 15 (by omega)
    have e16 : σ (.n 16) = yr := ea 16 (by omega)
    have e17 : σ (.n 17) = target := ea 17 (by omega)
    rw [e17, ← hfin, ← e15, ← e16, stackWeight_eq layout out ringPoint coeffs oodPoint lam x hcols,
      e1714, hsum, hret, h1704, hlamO, h1712]
    rw [sum_congr rfl fun j hj ↦ claimTerm_eq T (mem_range.mp hj),
      ringClaim_eq (show layout.placement qkeccak = _ from hq4) hxl,
      wOf_committed (by rw [hoc]; exact hq4) (by rw [hoL, hK4]) hxl (hK 4 (by decide)),
      hselv 4 (by decide), hK4]
    ring
  -- the body
  have hall : ∀ s ∈ termPre, Fwd.SHolds TrivC rd σ s := by
    intro s hs
    simp only [termPre, List.mem_append] at hs
    rcases hs with ((h | h) | h) | h
    · exact hHs s h
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp h
      exact (hsl c (List.mem_range.mp hc)).1 s h
    · exact hCs s h
    · exact hTs hfin' s h
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [term_params]
    apply List.ext_getElem (by simp [hargs, termArgs])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [ea i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  · intro s hs
    simp only [termPre, List.mem_append] at hs
    rcases hs with ((h | h) | h) | h
    · exact dispOk_of_noDisp (List.all_eq_true.mp head_noDisp s h)
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp h
      exact (hsl c (List.mem_range.mp hc)).2.1 s h
    · exact dispOk_of_noDisp (List.all_eq_true.mp claims_noDisp s h)
    · exact dispOk_of_noDisp (List.all_eq_true.mp tail_noDisp s h)
  · rw [term_body']
    exact Fwd.holdsList_straight termPre [] False _ hall rfl
  · rw [term_allocs]; rfl
  · rw [term_allocs]
    simp [bases, e20, e22, e26, e1694, e1709, Nat.add_assoc]
  · rw [term_callSF σ]
    refine callsMatch_kidsAt _ _ _ _ (by simp [termKids_length, Tables.nCommittedCols])
      (by rw [termKids_length, hol]) fun j hj => ?_
    have hj' : j < 101 := by simpa [Tables.nCommittedCols] using hj
    rw [getD_map_lt (Main.mkCall σ) (none, "", [], []) noCall (by simpa using hj),
      getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols])]
    have hOK := fun (ht : (kidAt (termKids Lin D b0) [] outs j).taken = true) =>
      outsOk_at ho j (by rw [termKids_length]; omega) (by omega) ht
    unfold kidAt at hOK ⊢
    rw [List.nil_append] at hOK ⊢
    split_ifs with h4 h98
    · interval_cases j
      · refine ⟨rfl, rfl, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        show [σ (.n 20), σ (.n 21), σ (.n 1), σ (.n 14), σ (.n 4)] = _
        rw [e20, e21, ea 1 (by omega), e14, ea 4 (by omega)]; rfl
      · refine ⟨rfl, rfl, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        show [σ (.n 22), σ (.n 23), σ (.n 2), σ (.n 14), σ (.n 5)] = _
        rw [e22, e23, ea 2 (by omega), e14, ea 5 (by omega)]; rfl
      · refine ⟨rfl, ?_, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        · show decide (σ (.n 31) ≠ 0) = decide (word 2 0 + glm ≠ 0)
          rw [e31, hglm]
        · show [σ (.n 32), σ (.n 6), σ (.n 26), σ (.n 14)] = _
          rw [e32, e6, e26, e14]; rfl
      · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩⟩
        · show [σ (.n 13), σ (.n 14)] = _
          rw [e13, e14]; rfl
        · obtain ⟨ese, h1, -⟩ := hst3
          show [σ (.n 43)] = (stRes outs).1
          rw [e43, h1]; rfl
    · obtain ⟨c, rfl⟩ : ∃ c, j = 4 + c := ⟨j - 4, by omega⟩
      have hc : c < Tables.nCommittedCols := by show c < 94; omega
      rw [show 4 + c - 4 = c by omega, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map,
        List.getElem_range]
      rw [termKids_getD_sel Lin D b0 hc] at hOK ⊢
      obtain ⟨-, -, -, e36, e37, e38, esel⟩ := hsl c hc
      have hlog : logG (σ (.n (selKap c).2.1)) = KC.getD c 0 := by
        rw [e37, gen_pow_eq_ofK]; exact logG_spec (by have := hKC31 c hc; omega)
      refine ⟨?_, ?_, fun ht => ⟨?_, ?_⟩⟩
      · show colSelNames.getD (logG (σ (.n (selKap c).2.1))) "" =
          Tables.lName "column_selector" (KC.getD c 0)
        rw [hlog, colSelNames, List.getD_eq_getElem _ _ (by simp; exact hKC31 c hc),
          List.getElem_map, List.getElem_range]
      · show true = @decide _ (Classical.propDecidable _)
        refine (@decide_eq_true _ (Classical.propDecidable _) ?_).symm
        rw [stRes_take, ite_pos' (by omega)]
        exact hst3
      · show [σ (.n (selStart c)), σ (.n 43), σ (.n ((selKap c).2.2 + 1))] =
          [gen ^ (stackOffsets KC).1.getD c 0, (stRes (outs.take (4 + c))).1.getD 0 0,
            ofK (addressOfIndex (B.gsq + 34))]
        rw [stRes_take, ite_pos' (by omega), e36, e43, e38, e0, ofK_gpow_mul_gen]
      · show [σ (.n (selV c))] = _
        rw [esel, (hOK ht).1, List.getD_cons_zero]
    · have : j = 98 ∨ j = 99 ∨ j = 100 := by omega
      rcases this with rfl | rfl | rfl
      · rw [termKids_getD_out] at hOK ⊢
        refine ⟨rfl, rfl, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        show [σ (.n 1694), σ (.n 1695), σ (.n 11), σ (.n 14), σ (.n 1697)] =
          [ofK (addressOfIndex (b0 + 105)), word 1 0, ofK (addressOfIndex B.zv),
            ofK (addressOfIndex B.pt1), gtau * word 64 0]
        rw [e1694, e1695, e11, e14, e1697, hgtau]
      · rw [termKids_getD_rsw] at hOK ⊢
        refine ⟨rfl, rfl, fun ht => ⟨?_, ?_⟩⟩
        · show [σ (.n 1699), σ (.n 14), σ (.n 12), σ (.n 1701)] =
            [ofK (addressOfIndex B.zv) * word 549755813888 0, ofK (addressOfIndex B.pt1),
              ofK (addressOfIndex B.ct), gtau * word 64 0]
          rw [e1699, e11, e14, ea 12 (by omega), e1701, hgtau]; rfl
        · show [σ (.n 1702)] = _
          rw [e1702, (hOK ht).1]; rfl
      · rw [termKids_getD_ood] at hOK ⊢
        refine ⟨rfl, rfl, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        show [σ (.n 1709), σ (.n 1710), σ (.n 18), σ (.n 14), σ (.n 19)] =
          [ofK (addressOfIndex (b0 + 146)), lamCl ^ (1 + poolRank Tables.nClaims) * lamCl,
            ofK (addressOfIndex B.oz), ofK (addressOfIndex B.pt1), gm]
        rw [e1709, e1710, hlamO, e9, e18, e14, e19, hlamC]
  · intro q hq
    simp only [termPre, List.filterMap_append, List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact hHl q h
    · obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp h
      obtain ⟨c, hc, hs⟩ := List.mem_flatMap.mp hs
      exact (hsl c (List.mem_range.mp hc)).2.2.1 q (List.mem_filterMap.mpr ⟨s, hs, hq⟩)
    · exact hCl q h
    · exact hTl q h

end
end LeanVM.Guest.B1.VerifySub
