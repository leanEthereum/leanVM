module

public import NativeRustcVmX64.Top.VerifyExecution.Commit
public import NativeRustcVmX64.Bus.Common
public import NativeRustcVmX64.Code.Vm.CommitStack.Names
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmX64.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmX64.Code.Vm.ReadOod.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmX64.Code.Vm.TablePhase.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmX64.Code.Vm.VerifyExecution.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution` on x86-64

**`verifyExecution_spec`**: rustc's `verify_execution`, placed anywhere in the program, meets its
contract (`VerifyExecutionPre`, `VerifyExecutionPost`) given its callees' contracts. The prologue
(`b0`) pushes the callee-saved registers and the public input's address (offset `40`) and calls
`read_announced_sizes` into the layout, the working area's first bytes; `b1` returns `0` when it
failed, else the walk's rest from the stack's commitment on (`callCommit`, which calls the next
phases in turn down to the stacked opening, `callVso`). The walk is run on the bytecode's and the
public input's words at the entry (`bcE`, `pubE`), which any words there are.
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm (WordsAt wordsOf wordOf)
open NativeRustcVm.Top (workAreaBytes walkCommit run_bind_eq readAnnouncedSizes_some)
open NativeRustcVm.Layout (LayoutWAt)

public section

/-- The bytecode's words at the entry. -/
@[expose] def bcE (m0 : MachineData) : List UInt64 := wordsOf m0.dmem (reg m0 .rsi) (reg m0 .rdx).toNat

/-- The public input's words at the entry. -/
@[expose] def pubE (m0 : MachineData) : Vector UInt64 4 :=
  Vector.ofFn fun i ↦ wordOf m0.dmem (reg m0 .rcx + BitVec.ofNat 64 (8 * i.val))

theorem length_bcE (m0 : MachineData) : (bcE m0).length = (reg m0 .rdx).toNat := by
  simp [bcE, wordsOf]

theorem bcE_eq {m0 : MachineData} {bcw : List UInt64} (hl : bcw.length = (reg m0 .rdx).toNat)
    (h : WordsAt m0.dmem (reg m0 .rsi) bcw) : bcw = bcE m0 := by
  have := NativeRustcVm.wordsOf_of_wordsAt h
  rw [hl] at this
  exact this.symm

theorem pubE_eq {m0 : MachineData} {P : Vector UInt64 4}
    (h : WordsAt m0.dmem (reg m0 .rcx) P.toList) : P = pubE m0 := by
  apply Vector.ext
  intro i hi
  have hw := NativeRustcVm.WordsAt.getElem h (i := i) (by simpa using hi)
  simp only [pubE, Vector.getElem_ofFn]
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  simp

theorem wordsAt_pubE {m0 : MachineData} (h : NativeRustcVm.Mapped m0.dmem (reg m0 .rcx) 32) :
    WordsAt m0.dmem (reg m0 .rcx) (pubE m0).toList := by
  refine NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ ?_
  have hi4 : i < 4 := by simpa using hi
  simp only [pubE, Vector.toList_ofFn, List.getElem_ofFn]
  exact NativeRustcVm.wordAt_of_mapped (NativeRustcVm.Mapped.sub h (by omega))

variable [Host] {k : Nat}

/-- **The walk**, from the entry: the function returns the walk's result on the bytecode's and the
public input's words at the entry. -/
theorem walk (hp : Placed code k)
    (hras : ∀ bc a s, Spec (Labels.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.entryLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s))
    (hcs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s))
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    (hbb : ∀ a s L, Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L))
    (htp : ∀ a s layout bus, Spec (Labels.label NativeRustcVmX64.Vm.TablePhase.entryLabel) (TablePhasePre a s layout bus)
      (TablePhasePost a s layout bus))
    (htc : ∀ evals cs, Spec (Labels.label NativeRustcVmX64.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre evals cs)
      (TableColumnClaimsPost evals cs))
    (hpi : ∀ a s layout pub cs, Spec (Labels.label NativeRustcVmX64.Vm.PublicInputPhase.entryLabel)
      (PublicInputPhasePre a s layout pub cs) (PublicInputPhasePost a s layout pub cs))
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmX64.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {s : TState} {m0 : MachineData} (hpre : VerifyExecutionPre a s m0) :
    Eventually (step1 Host.exe)
      (Done a m0 ((verifyExecution (bcE m0).toArray (pubE m0)).run s))
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b0Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨-, -, -, hts0, hroots, -⟩ := hpre
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  -- `b0`: the prologue, `call read_announced_sizes`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 96) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b0Offset + b0.length)).toBitVec) ⟨g.fmapped, g.fnw⟩
    (by simp) (List.pairwise_singleton _ _)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw1, hw40, hrdi, hrsi, hrdx, hrbx, hr12, hr13, hr14⟩ := after_eq run_b0 ▸ ok_b0
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) fun w hw ↦ ⟨(hw1 w hw).1, (hw1 w hw).2.2⟩
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 96 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17888 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have hC : AtCall m0 st1.data :=
    ⟨Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs, fun q hq ↦
      hs1 q fun hq' ↦ hq (wr_s g (by have := hs1' q hq'; omega))⟩
  have eRdi : reg st1.data .rdi = reg m0 .rdi := hm1.regs .rdi _ hrdi
  have eRsi : reg st1.data .rsi = reg m0 .rdx := hm1.regs .rsi _ hrsi
  have eRdx : reg st1.data .rdx = off (reg m0 .r8) 0 := by
    rw [off_zero]; exact hm1.regs .rdx _ hrdx
  have eRbx : reg st1.data .rbx = reg m0 .r8 := hm1.regs .rbx _ hrbx
  have eR12 : reg st1.data .r12 = reg m0 .rsi := hm1.regs .r12 _ hr12
  have eR13 : reg st1.data .r13 = reg m0 .rdx := hm1.regs .r13 _ hr13
  have eR14 : reg st1.data .r14 = reg m0 .rdi := hm1.regs .r14 _ hr14
  have h40 : NativeRustcVm.WordAt st1.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)) :=
    NativeRustcVmX64.Bus.wordAt_write_eq hm1 (r := 0) (b := stackBelow m0 96) (sz := 104) rfl (by decide) _ hw40
      (show reg m0 .rcx = (UInt64.ofBitVec (reg m0 .rcx)).toBitVec from rfl)
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    hts0.frame (fun p hp ↦ hm1.kept hwf0 p hp) (fun q hq ↦ by
      have := hs1' q hq
      have := g.aS
      have := g.tS
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inR g.tN).mp hi; omega
      · have := (inR g.aN).mp hi; omega) hs1
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN : readAnnouncedSizesStack = 8032 := rfl
  have hN' : 8032 ≤ 17792 + 32 := by decide
  have hRo := hC.rodataAt g hc hN'
  have hpre1 : ReadAnnouncedSizesPre (bcE m0).toArray a s st1.data := by
    unfold ReadAnnouncedSizesPre
    simp only [eRdi, eRsi, eRdx]
    rw [hN]
    have hrc : NativeRustcVm.Apart (off (reg m0 .r8) 0) 3912 rcAddr 192 := by
      have := g.wRod (o := 0) (n := 3912) (by omega) (by omega) .keccakRC
      rwa [rc_len, ← rcAddr_eq] at this
    refine ⟨hC.stackOk g hc hN', hRo.rcAt, hRo, hts1, hC.tstateOk g hc hN', g.rt,
      by rw [List.size_toArray, length_bcE], hC.readable g (by omega) (by decide),
      hC.offStack g hc (by omega) (by decide) hN', g.wRod (by omega) (by decide), hrc,
      g.apartWT (by omega) (by decide), g.apartWA (by omega) (by decide), ?_⟩
    apply hC.got g hc hN'
    intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨g.gotT hl, g.gotA hl, g.gotW hl (by omega) (by decide), g.gotRc hl⟩
  refine call_then hpc1 (hras _ a s) hpre1 fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hrax, hres, hch, hsv⟩ := hpost
  simp only [eRdi, eRdx, hN, show NativeRustcVm.Layout.layoutBytes = 3912 from rfl] at hres hch
  have hR2 : ∀ q, (NativeRustcVm.InRange (off (reg m0 .r8) 0) 3912 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st1.data 8032) 8032 q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 3912) := by
    rintro q (hq | hq | hq)
    · have := g.inW (o := 0) (n := 3912) (by omega) (by omega) hq; omega
    · exact Or.inr (Or.inl (g.inT hq))
    · have := hC.inS g hc hN' hq; left; omega
  have h2 : At m0 st2.data := hC.ret g eRbx eR14 hsv hrsp2 hch fun q hq ↦ by
    rcases hR2 q hq with hq | hq | hq
    · exact Or.inl hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have h40' : NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)) :=
    keep40 g hch (fun q hq ↦ by
      rcases hR2 q hq with h' | h' | h'
      · left; omega
      · right; right; left; exact h'
      · right; right; right; omega) h40
  -- `b1`: the tag tested.
  rw [NativeRustcVm.Top.verifyExecution_eq, run_bind_eq]
  generalize hr : (readAnnouncedSizes (bcE m0).toArray).run s = r at hrax hres
  obtain ⟨hwf2, hm2⟩ := h2.env g (ret := 0)
  obtain ⟨hmid1, hmem1, hk1, hrdx1⟩ := after_eq run_b1 ▸ ok_b1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp)
    (show exec b1 bodyS = some (after b1 bodyS,
      .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.VerifyExecution.label_10) by
      rw [after_eq run_b1]; exact run_b1) hwf2 nofun
    (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b0Offset + b0.length = k + NativeRustcVmX64.Vm.VerifyExecution.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b0_next]])) hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨h3, hd3, hkr⟩ := h2.block g hm3 hmid1 hmem1 hk1
  simp only [PcOk] at hpc3
  have hcnd : (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not.eval
      (frameEnv m0 st2.data 96 [] (fun _ ↦ 0) 0) = !r.isSome := by
    simp only [SBool.eval]
    rw [show (Sym.reg .rax).eval (frameEnv m0 st2.data 96 [] (fun _ ↦ 0) 0) = reg st2.data .rax
      from rfl, hrax]
    cases r.isSome <;> rfl
  rw [hcnd] at hpc3
  cases hb : r.isSome with
  | false =>
    rw [hb] at hpc3
    simp only [Bool.not_false, ↓reduceIte] at hpc3
    have hn : r = none := Option.not_isSome_iff_eq_none.mp (by rw [hb]; decide)
    rw [hn]
    exact fail hp g h3 (hpc3.trans (lbl_10 hp))
  | true =>
    rw [hb] at hpc3
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    obtain ⟨⟨⟨L, rate⟩, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
    obtain ⟨hrate, hL, hts'⟩ := hres _ _ _ rfl
    obtain ⟨hbc, hsl, hvc, hroots'⟩ := readAnnouncedSizes_some hr
    rw [off_zero] at hL
    have k12 : reg st3.data .r12 = reg st1.data .r12 := (hkr .r12 (by simp)).trans (hsv.1 .r12 rfl)
    have k13 : reg st3.data .r13 = reg st1.data .r13 := (hkr .r13 (by simp)).trans (hsv.1 .r13 rfl)
    exact callCommit hp hcs hro hbb htp htc hpi hkp hrs hvso g h3
      (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b1Offset + b1.length = k + NativeRustcVmX64.Vm.VerifyExecution.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b1_next]])) (rate := rate)
      (by rw [show reg st3.data .rdx = reg st2.data .rdx from hm3.regs .rdx _ hrdx1]; exact hrate)
      (by rw [k12]; exact eR12) (by rw [k13]; exact eR13)
      (by rw [hd3]; exact h40') (wordsAt_pubE g.mP) (by rw [hd3]; exact hts')
      (by rw [hroots', hroots]) (by rw [hd3]; exact hL) hsl
      (show (L.placement _).variableCount ≤ 31 by omega)
      (by rw [hbc, List.size_toArray, length_bcE])
      (by rw [hbc]; exact NativeRustcVm.wordsAt_of_mapped g.mB)

/-- **`verify_execution` meets its contract.** -/
theorem verifyExecution_spec (hp : Placed code k)
    (hras : ∀ bc a s, Spec (Labels.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.entryLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s))
    (hcs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s))
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    (hbb : ∀ a s L, Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L))
    (htp : ∀ a s layout bus, Spec (Labels.label NativeRustcVmX64.Vm.TablePhase.entryLabel) (TablePhasePre a s layout bus)
      (TablePhasePost a s layout bus))
    (htc : ∀ evals cs, Spec (Labels.label NativeRustcVmX64.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre evals cs)
      (TableColumnClaimsPost evals cs))
    (hpi : ∀ a s layout pub cs, Spec (Labels.label NativeRustcVmX64.Vm.PublicInputPhase.entryLabel)
      (PublicInputPhasePre a s layout pub cs) (PublicInputPhasePost a s layout pub cs))
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmX64.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s) := by
  intro m0 hpre
  rw [lbl_entry hp]
  refine Eventually.mono (walk hp hras hcs hro hbb htp htc hpi hkp hrs hvso hpre)
    fun st ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ⟨h1, h2, fun bcw hl hbc P hP ↦ ?_, h5, h6⟩
  rw [bcE_eq hl hbc, pubE_eq hP]
  exact ⟨h3, h4⟩

end

end NativeRustcVmX64.Top.VerifyExecution
