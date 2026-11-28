/-
  LeanVM.Guest.B1.VsC.CalleesB

  `verify_sub`'s callees' placed completeness with their ends bounded: the statements.
-/

module

public import LeanVM.Guest.B1.VsC.CalleesA
public import LeanVM.Guest.B1.VsC.EndBnd

/-!
# `verify_sub`'s callees, their ends bounded: the statements

`VsWinHyp`'s continuation carries `cur < 2^60 → st.kc ≤ cur + 2^40`, so each callee `verify_sub`
enters must end within a bound of its cursor. `CallAtA` does not bound its end (`callAtA_wrap`), so
the bound is part of each callee's statement, as `AtEveryB` is of `main`'s callees.

For each field of `VsCalleesCompleteA`, `…CompleteAE … Bd` is its statement with the end `e` also
satisfying `Bd c e` at the cursor `c = fp + fs f`; `…CompleteAB … β` is it at `EndLe c β` (`c < 2^60 →
e ≤ c + 2^β`). `…AE.toA` forgets the bound, `…AE.mono` weakens it. The proofs give the bound
`FsSmall fs → e ≤ c + 2^β` at every `fs`, so the unbounded statements keep their proofs.

`VsCalleesEndA fs al cert k`: the bounded fields but `open_stacked`'s (`OpenStackedEndA`, vsc32's,
`OpenStackedEndA.lean`), and `VsCalleesEndA.toA` with `open_stacked` given. Each callee is
entered once by `verify_sub` but the link's rounds and terminal (at most `12` calls in all), so the
bounds, `2^24` (Keccak, the terminal), `2^20` (the stack, the ring), `2^22` (each link callee),
sum to below `2^27`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Link
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)

/-! ## The statements with an end bound `Bd` -/

/-- `CertifyStackCompleteA`, its end `e` with `Bd (fp + fs "certify_stack") e`. -/
def CertifyStackCompleteAE (Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ (bytecode : List K) (logMemory : ℕ) (rows : List ℕ) (layout : Layout) (qt qk fp : ℕ),
    buildLayout bytecode logMemory rows = some layout → layout.stackLog ≤ 30 →
    qt + (winTabAt + 2 ^ winTabBits) ≤ fp → qk + (2 + nTables) ≤ fp →
    ∃ e, Bd (fp + fs "certify_stack") e ∧ CallAtA fs al cert k "certify_stack" [ptrAtV qk, ptrAtV qt]
      [gen ^ layout.stackLog, ptrAtV (csOffsAt (fp + fs "certify_stack")),
        ptrAtV (csOffsAt (fp + fs "certify_stack") + 52)]
      (fun i => (qt ≤ i ∧ i < qt + (winTabAt + 2 ^ winTabBits)) ∨ (qk ≤ i ∧ i < qk + (2 + nTables)))
      (fun i => csOffsAt (fp + fs "certify_stack") ≤ i ∧ i < csOffsAt (fp + fs "certify_stack") + 104)
      (fun rd => StackPlaced rd layout (gen ^ layout.stackLog) (ptrAtV (csOffsAt (fp + fs "certify_stack")))
        (ptrAtV (csOffsAt (fp + fs "certify_stack") + 52)))
      (fun rd => ExpTables rd (ptrAtV qt) ∧
        ReadsAt rd (ptrAtV qk) (kappaSources layout.logMemory layout.tableLogHeights))
      (fun rd t => t.pops coreProgram rd = Prover.stackHints (stackKappas layout) ∧
        t.Every (ExactAt coreProgram rd))
      (fs "certify_stack") fp (fp + fs "certify_stack") e

/-- `CheckStackTerminalCompleteA`, its end `e` with `Bd (fp + fs "check_stack_terminal") e`. -/
def CheckStackTerminalCompleteAE (Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ (args : List E) (layout : Layout) (link : LinkEnd) (chi r qPoint kOut kIn f g x z : List E)
    (rho lam rm : E) (outputs : List ColumnClaim) (keccakSlices : List E) (oodValue v0 v1 : E)
    (claims : List StackClaim) (fp : ℕ),
    stackedClaims layout link (publicClaimsPure layout rm v0 v1) outputs kIn keccakSlices f g rho
        (fun y ↦ eqEval z y, oodValue) = some claims → layout.stackLog ≤ 30 →
    (args.getD 19 0 + stackedBasis claims lam x) * args.getD 20 0 = args.getD 21 0 →
    PtrsBelow (cstArrays args chi r kOut kIn f g z) fp →
    ∃ e, Bd (fp + fs "check_stack_terminal") e ∧ CallAtA fs al cert k "check_stack_terminal" args []
      (ptrRegion (cstArrays args chi r kOut kIn f g z)) (fun _ => False) (fun _ => True)
      (fun rd => StackCtxAt rd args layout link chi r qPoint kOut kIn f g x z rho lam rm outputs)
      PostQuiet (fs "check_stack_terminal") fp (fp + fs "check_stack_terminal") e

/-- `RingSwitchTargetCompleteA`, its end `e` with `Bd (fp + fs "ring_switch_target") e`. -/
def RingSwitchTargetCompleteAE (Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ (sl mc : E) (s ch : List E) (fp : ℕ), s.length = kBits → ch.length = 2 * ringMapWidth →
    PtrsBelow [(sl, kBits), (mc, 2 * ringMapWidth)] fp →
    ∃ e, Bd (fp + fs "ring_switch_target") e ∧ CallAtA fs al cert k "ring_switch_target" [sl, mc]
      [ringTarget s (ch.take ringMapWidth) (ch.drop ringMapWidth)]
      (ptrRegion [(sl, kBits), (mc, 2 * ringMapWidth)]) (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd sl s ∧ ReadsAt rd mc ch)
      PostQuiet (fs "ring_switch_target") fp (fp + fs "ring_switch_target") e

/-- `VerifyKeccakCompleteA`, its end `e` with `Bd (fp + fs "verify_keccak") e`. -/
def VerifyKeccakCompleteAE (Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur chi ol zv sl tabs : E) (τ : ℕ) (chis outs xs op point slices : List E) (word : E)
    (s' : Fs) (fp : ℕ),
    keccakTauMin ≤ τ → τ ≤ keccakTauMax → τ ≤ chis.length → outs.length = 25 →
    (∃ sp, (⟨[f0, f1, f2, f3, f4], []⟩ : Fs).Carries sp) →
    RunsTo (verifyKeccak τ (chis.take τ) outs) ⟨[f0, f1, f2, f3, f4], []⟩ xs
      ([⟨qkeccak, op, word⟩], point, slices) s' →
    s'.pend.length = rateScalars → slices.length = 64 →
    PtrsBelow (vkArrays cur chi ol zv sl tabs xs chis op point) fp →
    ∃ e, Bd (fp + fs "verify_keccak") e ∧
      CallAtA fs al cert k "verify_keccak" [f0, f1, f2, f3, f4, cur, gen ^ τ, chi, ol, zv, sl, tabs]
      (capOf s'.perm ++ [cur * gen ^ xs.length, word])
      (ptrRegion (vkArrays cur chi ol zv sl tabs xs chis op point)) (fun _ => False) (fun _ => True)
      (fun rd => WinTabs rd tabs ∧ ReadsAt rd chi chis ∧ ReadsAt rd ol outs ∧ ReadsAt rd cur xs ∧
        ReadsAt rd zv op ∧ ReadsAt rd (zv * gen ^ qkeccakVarsCap) point ∧ ReadsAt rd sl slices)
      PostQuiet (fs "verify_keccak") fp (fp + fs "verify_keccak") e

/-- `SqueezePackedCompleteA`, its end `e` with `Bd (fp + fs "squeeze_packed") e`. -/
def SqueezePackedCompleteAE (Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ (f0 f1 f2 f3 f4 out : E) (p fp : ℕ), p < 64 →
    PtrsBelow [(out, (pkSqueeze p [f0, f1, f2, f3, f4]).1.length)] fp →
    ∃ e, Bd (fp + fs "squeeze_packed") e ∧ CallAtA fs al cert k "squeeze_packed" [f0, f1, f2, f3, f4, out, gen ^ p]
      (pkSqueeze p [f0, f1, f2, f3, f4]).2
      (ptrRegion [(out, (pkSqueeze p [f0, f1, f2, f3, f4]).1.length)]) (fun _ => False) (fun _ => True)
      (fun rd ↦ ReadsAt rd out (pkSqueeze p [f0, f1, f2, f3, f4]).1)
      PostQuiet (fs "squeeze_packed") fp (fp + fs "squeeze_packed") e

/-- `LinkRoundsCompleteA`, its end `e` with `Bd (fp + fs name) e`. -/
def LinkRoundsCompleteAE (nt bits : ℕ) (name : String) (Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur cl point tabs : E) (l : List (E × RSt)) (nw fp : ℕ), l.length < 64 → cur ≠ 0 →
    (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cur = cur * gen ^ nw →
    PtrsBelow (lrArrays cur point tabs nw l.length) fp →
    ∃ e, Bd (fp + fs name) e ∧ CallAtA fs al cert k name [f0, f1, f2, f3, f4, cur, cl, point, gen ^ l.length, tabs]
      (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cells
      (ptrRegion (lrArrays cur point tabs nw l.length)) (fun _ => False) (fun _ => True)
      (fun rd ↦ (bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l ∧
        ReadsAt rd point (l.map Prod.fst))
      PostQuiet (fs name) fp (fp + fs name) e

/-- `LinkTerminalCompleteA`, its end `e` with `Bd (fp + fs name) e`. -/
def LinkTerminalCompleteAE (w : ℕ) (name : String) (Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ c, Chunks.new w = some c →
    ∀ (r sent coef shifts certW nu rest claim : E) (rs sl shs nus : List E) (fp : ℕ), rs.length = c.width →
      sl.length = 64 → shs.length = 12 → nus.length = c.d →
      claim = (Functionals.new c rs 12).summand coef shs ((Functionals.new c rs 12).values c sl)
        (nus.map (certW * ·)) + rest →
      PtrsBelow (ltArrays r sent shifts nu rs.length nus.length) fp →
      ∃ e, Bd (fp + fs name) e ∧ CallAtA fs al cert k name [r, sent, coef, shifts, certW, nu, rest, claim] [0]
        (ptrRegion (ltArrays r sent shifts nu rs.length nus.length)) (fun _ => False) (fun _ => True)
        (fun rd ↦ ReadsAt rd r rs ∧ (∀ k < 64, LoadHolds rd sent (80 + k) (sl.getD k 0)) ∧
          ReadsAt rd shifts shs ∧ ReadsAt rd nu nus)
        PostQuiet (fs name) fp (fp + fs name) e

/-! ## At `EndLe` -/

/-- **`certify_stack`, its end within `2^β`.** -/
abbrev CertifyStackCompleteAB (β : ℕ) : Prop := CertifyStackCompleteAE fs al cert k (EndLe · β ·)
/-- **`check_stack_terminal`, its end within `2^β`.** -/
abbrev CheckStackTerminalCompleteAB (β : ℕ) : Prop := CheckStackTerminalCompleteAE fs al cert k (EndLe · β ·)
/-- **`ring_switch_target`, its end within `2^β`.** -/
abbrev RingSwitchTargetCompleteAB (β : ℕ) : Prop := RingSwitchTargetCompleteAE fs al cert k (EndLe · β ·)
/-- **`verify_keccak`, its end within `2^β`.** -/
abbrev VerifyKeccakCompleteAB (β : ℕ) : Prop := VerifyKeccakCompleteAE fs al cert k (EndLe · β ·)
/-- **`squeeze_packed`, its end within `2^β`.** -/
abbrev SqueezePackedCompleteAB (β : ℕ) : Prop := SqueezePackedCompleteAE fs al cert k (EndLe · β ·)
/-- **`link_rounds__L{nt}_L{bits}`, its end within `2^β`.** -/
abbrev LinkRoundsCompleteAB (nt bits : ℕ) (name : String) (β : ℕ) : Prop :=
  LinkRoundsCompleteAE fs al cert k nt bits name (EndLe · β ·)
/-- **`link_terminal__L{w}`, its end within `2^β`.** -/
abbrev LinkTerminalCompleteAB (w : ℕ) (name : String) (β : ℕ) : Prop :=
  LinkTerminalCompleteAE fs al cert k w name (EndLe · β ·)
/-- **The link callees `verify_sub` enters, their ends bounded** (`VsLinkCalleesA`'s fields). -/
structure VsLinkCalleesAB : Prop where
  rounds_L1_L0 : LinkRoundsCompleteAB fs al cert k 1 0 "link_rounds__L1_L0" 22
  rounds_L6_L0 : LinkRoundsCompleteAB fs al cert k 6 0 "link_rounds__L6_L0" 22
  rounds_L7_L0 : LinkRoundsCompleteAB fs al cert k 7 0 "link_rounds__L7_L0" 22
  rounds_L8_L1 : LinkRoundsCompleteAB fs al cert k 8 1 "link_rounds__L8_L1" 22
  rounds_L9_L1 : LinkRoundsCompleteAB fs al cert k 9 1 "link_rounds__L9_L1" 22
  rounds_L10_L1 : LinkRoundsCompleteAB fs al cert k 10 1 "link_rounds__L10_L1" 22
  squeeze_packed : SqueezePackedCompleteAB fs al cert k 22
  terminal : ∀ w, 19 ≤ w → w ≤ 24 → LinkTerminalCompleteAB fs al cert k w (ltNames.getD (w - 19) "") 22

/-- **`verify_sub`'s callees, their ends bounded**, but `open_stacked` (`OpenStackedEndA`). -/
structure VsCalleesEndA : Prop where
  link : VsLinkCalleesAB fs al cert k
  certify_stack : CertifyStackCompleteAB fs al cert k 20
  check_stack_terminal : CheckStackTerminalCompleteAB fs al cert k 24
  ring_switch_target : RingSwitchTargetCompleteAB fs al cert k 20
  verify_keccak : VerifyKeccakCompleteAB fs al cert k 24

variable {fs al cert k}

/-! ## Forgetting and weakening the bound -/

section
variable {Bd Bd' : ℕ → ℕ → Prop}

theorem CertifyStackCompleteAE.toA (h : CertifyStackCompleteAE fs al cert k Bd) :
    CertifyStackCompleteA fs al cert k := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  obtain ⟨e, -, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  exact ⟨e, he⟩

theorem CertifyStackCompleteAE.mono (h : CertifyStackCompleteAE fs al cert k Bd)
    (hB : ∀ c e, Bd c e → Bd' c e) : CertifyStackCompleteAE fs al cert k Bd' := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  obtain ⟨e, hb, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  exact ⟨e, hB _ e hb, he⟩

theorem CheckStackTerminalCompleteAE.toA (h : CheckStackTerminalCompleteAE fs al cert k Bd) :
    CheckStackTerminalCompleteA fs al cert k := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
  obtain ⟨e, -, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
  exact ⟨e, he⟩

theorem CheckStackTerminalCompleteAE.mono (h : CheckStackTerminalCompleteAE fs al cert k Bd)
    (hB : ∀ c e, Bd c e → Bd' c e) : CheckStackTerminalCompleteAE fs al cert k Bd' := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
  obtain ⟨e, hb, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
  exact ⟨e, hB _ e hb, he⟩

theorem RingSwitchTargetCompleteAE.toA (h : RingSwitchTargetCompleteAE fs al cert k Bd) :
    RingSwitchTargetCompleteA fs al cert k := by
  intro x0 x1 x2 x3 x4 x5 x6 x7
  obtain ⟨e, -, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7
  exact ⟨e, he⟩

theorem RingSwitchTargetCompleteAE.mono (h : RingSwitchTargetCompleteAE fs al cert k Bd)
    (hB : ∀ c e, Bd c e → Bd' c e) : RingSwitchTargetCompleteAE fs al cert k Bd' := by
  intro x0 x1 x2 x3 x4 x5 x6 x7
  obtain ⟨e, hb, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7
  exact ⟨e, hB _ e hb, he⟩

theorem VerifyKeccakCompleteAE.toA (h : VerifyKeccakCompleteAE fs al cert k Bd) :
    VerifyKeccakCompleteA fs al cert k := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
  obtain ⟨e, -, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
  exact ⟨e, he⟩

theorem VerifyKeccakCompleteAE.mono (h : VerifyKeccakCompleteAE fs al cert k Bd)
    (hB : ∀ c e, Bd c e → Bd' c e) : VerifyKeccakCompleteAE fs al cert k Bd' := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
  obtain ⟨e, hb, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
  exact ⟨e, hB _ e hb, he⟩

theorem SqueezePackedCompleteAE.toA (h : SqueezePackedCompleteAE fs al cert k Bd) :
    SqueezePackedCompleteA fs al cert k := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
  obtain ⟨e, -, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
  exact ⟨e, he⟩

theorem SqueezePackedCompleteAE.mono (h : SqueezePackedCompleteAE fs al cert k Bd)
    (hB : ∀ c e, Bd c e → Bd' c e) : SqueezePackedCompleteAE fs al cert k Bd' := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
  obtain ⟨e, hb, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
  exact ⟨e, hB _ e hb, he⟩

theorem LinkRoundsCompleteAE.toA {nt bits : ℕ} {name : String}
    (h : LinkRoundsCompleteAE fs al cert k nt bits name Bd) :
    LinkRoundsCompleteA fs al cert k nt bits name := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  obtain ⟨e, -, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  exact ⟨e, he⟩

theorem LinkRoundsCompleteAE.mono {nt bits : ℕ} {name : String}
    (h : LinkRoundsCompleteAE fs al cert k nt bits name Bd)
    (hB : ∀ c e, Bd c e → Bd' c e) : LinkRoundsCompleteAE fs al cert k nt bits name Bd' := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  obtain ⟨e, hb, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  exact ⟨e, hB _ e hb, he⟩

theorem LinkTerminalCompleteAE.toA {w : ℕ} {name : String}
    (h : LinkTerminalCompleteAE fs al cert k w name Bd) :
    LinkTerminalCompleteA fs al cert k w name := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  obtain ⟨e, -, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  exact ⟨e, he⟩

theorem LinkTerminalCompleteAE.mono {w : ℕ} {name : String}
    (h : LinkTerminalCompleteAE fs al cert k w name Bd)
    (hB : ∀ c e, Bd c e → Bd' c e) : LinkTerminalCompleteAE fs al cert k w name Bd' := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  obtain ⟨e, hb, he⟩ := h x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  exact ⟨e, hB _ e hb, he⟩

end

/-- The link callees, their bounds forgotten. -/
theorem VsLinkCalleesAB.toA (h : VsLinkCalleesAB fs al cert k) : VsLinkCalleesA fs al cert k :=
  ⟨h.rounds_L1_L0.toA, h.rounds_L6_L0.toA, h.rounds_L7_L0.toA, h.rounds_L8_L1.toA, h.rounds_L9_L1.toA,
    h.rounds_L10_L1.toA, h.squeeze_packed.toA, fun w h1 h2 => (h.terminal w h1 h2).toA⟩

/-- **`verify_sub`'s callees**, their bounds forgotten, `open_stacked`'s given. -/
theorem VsCalleesEndA.toA (h : VsCalleesEndA fs al cert k)
    (hos : ∀ m, m ≤ 14 → OpenStackedCompleteA fs al cert k m) : VsCalleesCompleteA fs al cert k :=
  ⟨h.link.toA, h.certify_stack.toA, h.check_stack_terminal.toA, h.ring_switch_target.toA,
    h.verify_keccak.toA, hos⟩

end
end LeanVM.Guest.B1.VsC
