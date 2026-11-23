module

public import NativeRustcVmArm.Code.Vm.CommitStack.Names
public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmArm.Code.Vm.ReadOod.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Code.Vm.TablePhase.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Code.Vm.VerifyExecution.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call2

/-!
# `verify_execution` on AArch64

**`verifyExecution_spec`**: rustc's `verify_execution`, placed anywhere in the program, meets its
contract (`VerifyExecutionPre`, `VerifyExecutionPost`) given its callees' contracts. The prologue
(`b0`) calls `read_announced_sizes` into the layout, the working area's first bytes; `b1` returns
`0` when it failed, else the walk's rest from the stack's commitment on (`call2`, which calls the
next phases in turn down to the stacked opening, `call10`). The walk is run on the bytecode's and
the public input's words at the entry (`bcE`, `pubE`), which any words there are.
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm (WordsAt wordsOf wordOf)
open NativeRustcVm.Top (workAreaBytes walkCommit run_bind_eq readAnnouncedSizes_some)
open NativeRustcVm.Layout (LayoutWAt)

public section

/-- The bytecode's words at the entry. -/
@[expose] def bcE (m0 : MachineData) : List UInt64 :=
  wordsOf m0.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat

/-- The public input's words at the entry. -/
@[expose] def pubE (m0 : MachineData) : Vector UInt64 4 :=
  Vector.ofFn fun i ↦ wordOf m0.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * i.val))

theorem length_bcE (m0 : MachineData) : (bcE m0).length = m0.regs.X2.toNat := by
  simp [bcE, wordsOf]

theorem bcE_eq {m0 : MachineData} {bcw : List UInt64} (hl : bcw.length = m0.regs.X2.toNat)
    (h : WordsAt m0.dmem m0.regs.X1.toBitVec bcw) : bcw = bcE m0 := by
  have := NativeRustcVm.wordsOf_of_wordsAt h
  rw [hl] at this
  exact this.symm

theorem pubE_eq {m0 : MachineData} {P : Vector UInt64 4}
    (h : WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) : P = pubE m0 := by
  apply Vector.ext
  intro i hi
  have hw := NativeRustcVm.WordsAt.getElem h (i := i) (by simpa using hi)
  simp only [pubE, Vector.getElem_ofFn]
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  simp

theorem wordsAt_pubE {m0 : MachineData} (h : NativeRustcVm.Mapped m0.dmem m0.regs.X3.toBitVec 32) :
    WordsAt m0.dmem m0.regs.X3.toBitVec (pubE m0).toList := by
  refine NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ ?_
  have hi4 : i < 4 := by simpa using hi
  simp only [pubE, Vector.toList_ofFn, List.getElem_ofFn]
  exact wordAt_wordOf (NativeRustcVm.Mapped.sub h (by omega))

variable [Host] {k : Nat}

/-- **The walk**, from the entry: the function returns the walk's result on the bytecode's and the
public input's words at the entry. -/
theorem walk (hp : Placed code k) (hR : Rest)
    (hras : ∀ bc a s, Spec (Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.entryLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s))
    (hcs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s))
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    {a : DecArea} {s : TState} {m0 : MachineData} (hpre : VerifyExecutionPre a s m0) :
    Eventually (step1 Host.exe)
      (Done a m0 ((verifyExecution (bcE m0).toArray (pubE m0)).run s))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b0Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨-, -, -, hts0, hroots, -⟩ := hpre
  have hs := g.s
  have hal := g.al
  have hwN := g.wN
  have hsl := m0.regs.SP.toBitVec.isLt
  have hF := frame_toNat g
  set F := m0.regs.SP.toBitVec - BitVec.ofNat 64 96 with hFdef
  have hsb0 : (stackBelow m0 verifyExecutionStack).toNat = m0.regs.SP.toBitVec.toNat - 18384 :=
    toNat_subAddr hs
  have hFm : Mapped m0.dmem F 96 :=
    Mapped.within g.mS (by rw [hsb0]; unfold verifyExecutionStack; omega)
      (by rw [hsb0, hF]; omega) (by rw [hsb0, hF]; unfold verifyExecutionStack; omega)
  -- The prologue.
  have hwf0 : (Env.ofMachine m0 [(F, 96)]).WF :=
    Env.wf_of ⟨⟨hFm, show F.toNat + 96 ≤ 2 ^ 64 by omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (Env.ofMachine m0 [(F, 96)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ show F.toNat % 16 = 0 by omega, trivial⟩
      (show m0.regs.SP.toBitVec = F + BitVec.ofInt 64 96 by
        rw [show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl, hFdef, BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  refine exec_then (hb0 hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hW0 : ∀ q, Written (Env.ofMachine m0 [(F, 96)]) (after b0 entryS) q →
      m0.regs.SP.toBitVec.toNat - 96 + 16 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toBitVec.toNat := by
    intro q hq
    have hb0m := b0_mem
    have := written_sub (env := Env.ofMachine m0 [(F, 96)]) (r := 0) rfl hb0m hq
    omega
  have hm1' : Match (Env.ofMachine m0 [(F, 96)]) (after b0 entryS) st1.data := by
    rw [after_eq run_b0]; exact hm1
  have hB1 : Body m0 96 slots (Writable m0) st1.data := by
    refine ⟨?_, fun p hp ↦ ?_, fun r hr hn ↦ ?_, fun q hq ↦ ?_, hm1.kept hwf0⟩
    · rw [hm1.sp]; show F + BitVec.ofInt 64 0 = F; simp
    · have hw := b0_slots p hp
      rw [after_eq run_b0] at hw
      exact hm1.bytesAt_write (r := 0) (b := F) (sz := 96) rfl ((slotsIn p hp).2) hw
    · have hr' : r ∈ nonslots := by cases r <;> simp_all [calleeSaved, slots, nonslots]
      have h := b0_regs r hr'
      rw [after_eq run_b0] at h
      exact UInt64.toBitVec_inj.mp (hm1.regs r _ h)
    · refine hm1.get?_mem0 hwf0 fun hw ↦ hq ?_
      have := hW0 q (by rw [after_eq run_b0]; exact hw)
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
      show InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 verifyExecutionStack)
        verifyExecutionStack q
      rw [inRange_below (show verifyExecutionStack ≤ _ from hs)]
      unfold verifyExecutionStack
      omega
  have rg : ∀ (r r' : XReg), (after b0 entryS).reg r = some (.reg r') →
      st1.data.regs.getXReg r = m0.regs.getXReg r' := fun _ _ h ↦
    UInt64.toBitVec_inj.mp (hm1'.regs _ _ h)
  have h1 : At m0 st1.data := ⟨hB1, rg .X19 .X4 (by rw [after_eq run_b0]; rfl),
    rg .X20 .X0 (by rw [after_eq run_b0]; rfl)⟩
  have r0 : st1.data.regs.X0 = m0.regs.X0 := rg .X0 .X0 (by rw [after_eq run_b0]; rfl)
  have r1 : st1.data.regs.X1 = m0.regs.X2 := rg .X1 .X2 (by rw [after_eq run_b0]; rfl)
  have r2 : st1.data.regs.X2 = m0.regs.X4 := rg .X2 .X4 (by rw [after_eq run_b0]; rfl)
  have k22 : st1.data.regs.X22 = m0.regs.X3 := rg .X22 .X3 (by rw [after_eq run_b0]; rfl)
  have k23 : st1.data.regs.X23 = m0.regs.X2 := rg .X23 .X2 (by rw [after_eq run_b0]; rfl)
  have k24 : st1.data.regs.X24 = m0.regs.X1 := rg .X24 .X1 (by rw [after_eq run_b0]; rfl)
  have hs1 : SameOutside m0.dmem st1.data.dmem
      (Written (Env.ofMachine m0 [(F, 96)]) (after b0 entryS)) :=
    hm1'.sameOutside hwf0
  have hts1 : TStateAt st1.data.dmem m0.regs.X0.toBitVec a s :=
    hts0.frame (hm1'.kept hwf0) (fun q hq ↦ by
      have := hW0 q hq
      have := g.tS
      have := g.aS
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inRange_nat g.tN).mp hi; omega
      · have := (inRange_nat g.aN).mp hi; omega) hs1
  -- `read_announced_sizes`.
  have hN : readAnnouncedSizesStack ≤ 18288 := by decide
  have hRo := h1.rodataAt g hN
  have e0 : m0.regs.X4.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 0 :=
    (NativeRustcVm.addr_add_zero _).symm
  have hpre1 : ReadAnnouncedSizesPre (bcE m0).toArray a s st1.data := by
    unfold ReadAnnouncedSizesPre
    simp only [r0, r2]
    rw [e0]
    have hrc := (itemApart (g.rodataApart (o := 0) (n := 3912) (by omega) (by omega))).1
    exact ⟨h1.stackOk g hN, hRo.rcAt, hRo, hts1, h1.tstateOk g hN, g.rt,
      by rw [r1, List.size_toArray, length_bcE], h1.readable g (by omega) (by decide),
      h1.offStack g (by omega) (by decide) hN, g.rodataApart (by omega) (by decide), hrc,
      g.apartWT (by omega) (by decide), g.apartWA (by omega) (by decide)⟩
  refine call_then hpc1 (hras _ a s) hpre1 fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hch, hsv⟩ := hpost
  simp only [r0, r2] at hres hch
  rw [e0] at hres hch
  have hN' : readAnnouncedSizesStack ≤ 18288 := hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact wr_w g (o := 0) (n := 3912) (by omega) (by omega) hq
    · exact wr_t g hq
    · exact wr_stk h1 g hN' hq
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b0Offset + b0.length = k + NativeRustcVmArm.Vm.VerifyExecution.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b0_next]] at hpc2
  rw [NativeRustcVm.Top.verifyExecution_eq, run_bind_eq]
  generalize hr : (readAnnouncedSizes (bcE m0).toArray).run s = r at hx0 hres
  have bk := branch_keeps b1 (by simp)
  have ck := call_keeps b1 (by simp)
  rw [after_eq run_b1] at bk ck
  refine branch hp g (hb1 hp) run_b1 bk ck.1 h2 hpc2 (bne_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => cases hb
  obtain ⟨⟨⟨L, rate⟩, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hrate, hL, hts'⟩ := hres _ _ _ rfl
  obtain ⟨hbc, hsl, hvc, hroots'⟩ := readAnnouncedSizes_some hr
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b1Offset + b1.length = k + NativeRustcVmArm.Vm.VerifyExecution.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b1_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e22 : st3.data.regs.X22 = st1.data.regs.X22 := reg .X22 rfl
  have e23 : st3.data.regs.X23 = st1.data.regs.X23 := reg .X23 rfl
  have e24 : st3.data.regs.X24 = st1.data.regs.X24 := reg .X24 rfl
  rw [NativeRustcVm.addr_add_zero] at hL
  exact call2 hp hR hcs hro g h3 hpc3 (rate := rate)
    (by rw [show st3.data.regs.X1 = st2.data.regs.X1 from hreg3 .X1]; exact hrate)
    (by rw [e22, k22]) (by rw [e23, k23]) (by rw [e24, k24]) (wordsAt_pubE g.mP) (hd3 ▸ hts')
    (by rw [hroots']; exact hroots) (hd3 ▸ hL) hsl
    (show (L.placement _).variableCount ≤ 31 by omega)
    (by rw [hbc, List.size_toArray, length_bcE]) (by rw [hbc]; exact wordsAt_wordsOf g.mB)

/-- **`verify_execution` meets its contract.** -/
theorem verifyExecution_spec (hp : Placed code k)
    (hras : ∀ bc a s, Spec (Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.entryLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s))
    (hcs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s))
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    (hbb : ∀ a s L, Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L))
    (htp : ∀ a s layout bus, Spec (Labels.label NativeRustcVmArm.Vm.TablePhase.entryLabel) (TablePhasePre a s layout bus)
      (TablePhasePost a s layout bus))
    (htc : ∀ evals cs, Spec (Labels.label NativeRustcVmArm.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre evals cs)
      (TableColumnClaimsPost evals cs))
    (hpi : ∀ a s layout pub cs, Spec (Labels.label NativeRustcVmArm.Vm.PublicInputPhase.entryLabel)
      (PublicInputPhasePre a s layout pub cs) (PublicInputPhasePost a s layout pub cs))
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmArm.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmArm.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s) := by
  intro m0 hpre
  rw [lbl_entry hp]
  refine Eventually.mono (walk hp ⟨hbb, htp, htc, hpi, hkp, hrs, hvso⟩ hras hcs hro hpre)
    fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, fun bcw hl hbc P hP ↦ ?_, h4, h5⟩
  rw [bcE_eq hl hbc, pubE_eq hP]
  exact ⟨h2, h3⟩

end

end NativeRustcVmArm.Top.VerifyExecution
