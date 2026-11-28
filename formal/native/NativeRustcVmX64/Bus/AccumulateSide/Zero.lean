module

public import NativeRustcVmX64.Bus.AccumulateSide.Front
public import NativeRustcVmX64.Bus.AccumulateSide.FactsZ
public import NativeRustcVmX64.Mem
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `accumulate_side`: the frame's `FormBuf` cleared, the table loop set up (x86-64)

`b12`, `b13` clear the frame's bytes `136` to `6056` (`zeroLoop`), `b14` copies them over the
`FormBuf`'s terms (`memcpy`); `b15` checks the table blocks' count, `b16` sets the loop's values
up: `toTables`, from `b12` to the table loop's head at turn `0`.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- The forms after `j` table blocks, and the padding rows. -/
abbrev stA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (Fm : Array (Array FormW)) (SL : BusLayoutW) (m0 : MachineData) (j : Nat) :
    Array (Array FormW) × EW :=
  stAt Fm (reg m0 .rdx).toNat (BA L rows bl) SL (wA m0) (betaA m0) (ptA m0) j

/-- Table block `j`. -/
abbrev bkA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) (j : Nat) :
    BusBlockW :=
  (BA L rows bl).getD j default

/-- Table block `j`'s form. -/
abbrev fmA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (j : Nat) : FormW :=
  blockForm (bkA L rows bl j) (wA m0) (betaA m0)

/-- Table block `j`'s padding weight. -/
abbrev pwA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (j : Nat) : EW :=
  paddingWeight ((ptA m0).extract 0 (bkA L rows bl j).logRows) (bkA L rows bl j).rows

/-- Table block `j`'s padding row's value. -/
abbrev evA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (j : Nat) : EW :=
  (fmA L rows bl m0 j).evaluate (tablesW.getD (bkA L rows bl j).owner default).padding

/-- `TABLES`' word `i`. -/
abbrev twA (i : Nat) : UInt64 := NativeRustcVmX64.Tables.TableTerms.tablesWords.getD i 0

/-- The table loop's values at turn `j`. -/
def lpT [Labels] (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (Fm : Array (Array FormW)) (SL : BusLayoutW) (m0 : MachineData) (j : Nat) : Nat → UInt64
  | 0 => (16 * j).toUInt64
  | 1 => (stA L rows bl Fm SL m0 j).2.c0
  | 2 => (stA L rows bl Fm SL m0 j).2.c1
  | 3 => (onesT SL (ptA m0) j).c0
  | 4 => (onesT SL (ptA m0) j).c1
  | 5 => (tsel SL (ptA m0) j).c0
  | 6 => (tsel SL (ptA m0) j).c1
  | 7 => (bkA L rows bl j).owner.toUInt64
  | 8 => (((bl[j]?).map NativeRustcVm.Data.Block.tuple).getD 0).toUInt64
  | 9 => (fmA L rows bl m0 j).size.toUInt64
  | 10 => .ofBitVec (off (fb m0) 6064)
  | 11 => twA (5 * (bkA L rows bl j).owner + 3)
  | 12 => twA (5 * (bkA L rows bl j).owner + 4)
  | 13 => (onesT SL (ptA m0) (j + 1)).c0
  | 14 => (onesT SL (ptA m0) (j + 1)).c1
  | 15 => .ofBitVec (rodataAddr .padding +
      BitVec.ofNat 64 (16 * (twA (5 * (bkA L rows bl j).owner + 3)).toNat))
  | 16 => (pwA L rows bl m0 j).c0
  | 17 => (pwA L rows bl m0 j).c1
  | 18 => (tsel SL (ptA m0) j * pwA L rows bl m0 j).c0
  | 19 => (tsel SL (ptA m0) j * pwA L rows bl m0 j).c1
  | 20 => (evA L rows bl m0 j).c0
  | 21 => (evA L rows bl m0 j).c1
  | 22 => (16 * (j + 1)).toUInt64
  | _ => 0

/-- **The table loop's head** at turn `j`. -/
def TH [Labels] (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (Fm : Array (Array FormW)) (SL : BusLayoutW) (m0 : MachineData) (j : Nat)
    (st : MachineData) : Prop :=
  St m0 (outs m0) (Vt SL m0 (lpT L rows bl Fm SL m0 j)) DT 8 st ∧
    FormsAt st.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 j).1

end

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

omit [Host] in
/-- The forms where nothing was written but the stack. -/
theorem St.formsZ [Labels] (h : Pre L rows bl Fm SL m0) {V : Nat → UInt64} {D : List (Sym × Nat)}
    {o : Nat} {m : MachineData} (hst : St m0 Z V D o m) :
    Same m0.dmem m.dmem (reg m0 .rsi) formsBytes := fun j hj ↦
  hst.same _ fun hq ↦ hq.elim (fun h ↦ h.elim) fun hq ↦
    NativeRustcVm.Apart.not_inRange_add h.formsOk.2 h.forms_nw (noWrap_stackBelow h.stack) hj
      (Ring.inRange_le hq (by omega))

/-- **A turn of the zeroing loop** (`b13`): RAX `72 + 80 t`. -/
theorem zeroTurn (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {lp : Nat → UInt64} {t : Nat}
    (ht : t < 74) {st : MachineData} (hst : St m0 Z (Vt SL m0 lp) D12 8 st)
    (hrax : st.regs.get64 .rax = BitVec.ofNat 64 (72 + 80 * t)) :
    Eventually (step1 Host.exe) (fun st' ↦ St m0 Z (Vt SL m0 lp) D12 8 st'.data ∧
      st'.data.regs.get64 .rax = BitVec.ofNat 64 (72 + 80 * (t + 1)) ∧
      ((st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b13Offset) ∧ t + 1 < 74) ∨
        (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b14Offset) ∧ t + 1 = 74)))
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b13Offset)⟩ := by
  have hnw := h.frame_nw
  unfold NativeRustcVm.NoWrap at hnw
  have hfbN := h.fbN
  have hF : F = 12032 := rfl
  have hsp : rspOf st = off (fb m0) 8 := hst.fr.sp
  let a := off (fb m0) (80 + 80 * t)
  have ha : rspOf st + st.regs.get64 .rax = a := by
    rw [hsp, hrax]
    show fb m0 + BitVec.ofNat 64 8 + _ = fb m0 + _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  have haN : a.toNat = (fb m0).toNat + (80 + 80 * t) := toNat_off (by omega)
  let env := Env.ofMachine st [(a, 136)]
  have hwf : env.WF := Env.wf_of ⟨⟨fun i hi ↦ by
      have := frame_mapped h.stack le_F (80 + 80 * t + i) (by omega)
      rw [show fb m0 + BitVec.ofNat 64 (80 + 80 * t + i) = a + BitVec.ofNat 64 i from by
        show _ = off (fb m0) (80 + 80 * t) + _
        rw [off_add]] at this
      exact hst.fr.kept _ this, by unfold NoWrap; rw [haN]; omega⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hm : Match env zS st :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show BinOp.apply .add .W64 (st.regs.get64 .rsp) (st.regs.get64 .rax) = a + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, add64]
      exact ha, trivial⟩
  obtain ⟨hregs, hrax', hws⟩ := ok_b13
  refine exec_then (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf nofun hm
    fun st' hm' hpc ↦ ?_
  have hkeep : ∀ r, r ≠ .rax → st'.data.regs.get64 r = st.regs.get64 r := fun r hr ↦ by
    have := List.all_eq_true.mp hregs r (mem_allRegs r)
    simp only [Bool.or_eq_true] at this
    exact hm'.regs r _ (beq_iff_eq.mp (this.resolve_left fun he ↦ hr (Reg64.eq_of_beq he)))
  have hwr : ∀ q, Written env (after b13 zS) q →
      (fb m0).toNat + 136 + 80 * t ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 216 + 80 * t := by
    rintro q ⟨w, hw, b, sz, hb, h1, h2⟩
    have := List.all_eq_true.mp hws w hw
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨hr, ho1⟩, ho2⟩ := this
    rw [hr] at hb
    cases hb
    rw [haN] at h1 h2
    omega
  have hsame : NativeRustcVm.SameOutside st.dmem st'.data.dmem fun q ↦
      (fb m0).toNat + 136 + 80 * t ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 216 + 80 * t :=
    fun q hq ↦ hm'.get?_mem0 hwf fun hW ↦ hq (hwr q hW)
  have hj : ∀ j, (j < 136 + 80 * t ∨ 216 + 80 * t ≤ j) → j < F + 8 →
      st'.data.dmem.get? (fb m0 + BitVec.ofNat 64 j) = st.dmem.get? (fb m0 + BitVec.ofNat 64 j) :=
    fun j hj hjF ↦ hsame _ fun hq ↦ by
      rw [show fb m0 + BitVec.ofNat 64 j = off (fb m0) j from rfl, toNat_off (by omega)] at hq
      omega
  have hst' : St m0 Z (Vt SL m0 lp) D12 8 st'.data := by
    refine ⟨⟨?_, fun p hp ↦ ?_, fun j hjj ↦ ?_, kept_trans hst.fr.kept (hm'.kept hwf),
      fun r hr hs ↦ ?_⟩, fun q hq ↦ ?_, ?_⟩
    · show st'.data.regs.get64 .rsp = _
      rw [hkeep .rsp (by decide)]; exact hst.fr.sp
    · refine bytesAt_congr (hst.fr.slot p hp) fun i hi ↦ ?_
      have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
      rw [off_add]
      exact hj _ (.inr (by have := slots_ge p hp; omega)) (by have := slots_le p hp; omega)
    · exact (hj _ (.inr (by omega)) (by omega)).trans (hst.fr.ret j hjj)
    · show st'.data.regs.get64 r = _
      rw [hkeep r (by rintro rfl; cases hr)]; exact hst.fr.regs r hr hs
    · refine (hsame q fun hq' ↦ hq (.inr ?_)).trans (hst.same q hq)
      refine h.frame_stk (lo := 0) (n := F) (by omega) ?_
      rw [off_zero, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
      omega
    · exact hst.hd.keep (rk := fun r ↦ r != .rax) (lo := 136) (hi := 6056) (top := F + 8)
        (by decide) (fun r hr ↦ hkeep r fun hrr ↦ by subst hrr; exact absurd hr (by decide)) fun j hjr ↦ hj j (by omega) (by omega)
  simp only [PcOk] at hpc
  have hc : c13.eval env = decide (t + 1 ≠ 74) := by
    show (!(CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 80) (st.regs.get64 .rax))
      (BitVec.ofNat 64 5992))) = _
    rw [add64, hrax, ← BitVec.ofNat_add, eq64]
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff]
    constructor
    · intro hne heq; exact hne (by rw [show 80 + (72 + 80 * t) = 5992 by omega])
    · intro hne heq
      have := congrArg BitVec.toNat heq
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
      exact hne (by omega)
  have erax : st'.data.regs.get64 .rax = BitVec.ofNat 64 (72 + 80 * (t + 1)) := by
    rw [hm'.regs .rax _ hrax']
    show BinOp.apply .add .W64 (BitVec.ofNat 64 80) (st.regs.get64 .rax) = _
    rw [add64, hrax, ← BitVec.ofNat_add]
    congr 1
    omega
  rw [hc] at hpc
  by_cases hl : t + 1 = 74
  · simp only [hl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc
    exact .done _ ⟨hst', erax, .inr ⟨by rw [hpc]; rfl, hl⟩⟩
  · simp only [hl, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc
    exact .done _ ⟨hst', erax, .inl ⟨by rw [hpc]; exact hp.label NativeRustcVmX64.Vm.AccumulateSide.label_9_at, by omega⟩⟩
/-- **The zeroing loop** from turn `t`. -/
theorem zeroLoop (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {lp : Nat → UInt64} {t : Nat}
    (ht : t < 74) {st : MachineData} (hst : St m0 Z (Vt SL m0 lp) D12 8 st)
    (hrax : st.regs.get64 .rax = BitVec.ofNat 64 (72 + 80 * t)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b14Offset) ∧
      St m0 Z (Vt SL m0 lp) D12 8 st'.data)
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b13Offset)⟩ := by
  refine Sym.loop (fun n (s : MachineState) ↦ ∃ t, n = 74 - t ∧ t < 74 ∧
      s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b13Offset) ∧ St m0 Z (Vt SL m0 lp) D12 8 s.data ∧
      s.data.regs.get64 .rax = BitVec.ofNat 64 (72 + 80 * t))
    (fun n s ⟨t, hn, ht, hpc, hst, hrax⟩ ↦ ?_) ⟨t, rfl, ht, rfl, hst, hrax⟩
  obtain ⟨d, pc⟩ := s
  simp only at hpc hst hrax
  subst hpc
  refine (zeroTurn hp h ht hst hrax).mono fun s' ⟨hst', hrax', hx⟩ ↦ ?_
  rcases hx with ⟨hpc', hlt⟩ | ⟨hpc', -⟩
  · exact .inr ⟨74 - (t + 1), by omega, t + 1, rfl, hlt, hpc', hst', hrax'⟩
  · exact .inl ⟨hpc', hst'⟩

/-- **From `b12` to the table loop's head.** -/
theorem toTables (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {lp : Nat → UInt64}
    {st : MachineData} (hst : St m0 Z (Vt SL m0 lp) D12 8 st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset) ∧
      TH L rows bl Fm SL m0 0 st'.data)
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b12Offset)⟩ := by
  have hnw := h.frame_nw
  unfold NativeRustcVm.NoWrap at hnw
  have hfbN := h.fbN
  have hF : F = 12032 := rfl
  -- `b12`: RAX `72`.
  obtain ⟨-, -, -, -, -, -, -, -, hmid12, hw12, htr12, hax12⟩ := ok_b10
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b12_in_code (by simp [b12]) hp) exit_b12 nofun hst.fr hst.same
    (hst.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst.fr.kept)
    (St.mt hst ⟨rfl, trivial⟩ trivial trivial trivial) hmid12 hw12 (by decide) htr12
    fun st1 hm1 hpc1 hst1 _ ↦ ?_
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b13Offset) := hpc1
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1' hst1 hm1
  subst hpc1'
  refine Eventually.bind (zeroLoop hp h (t := 0) (by decide) hst1 (hm1.regs .rax _ hax12))
    fun s ⟨hpc2, hst2⟩ ↦ ?_
  obtain ⟨d2, pc2⟩ := s
  simp only at hpc2 hst2
  subst hpc2
  -- `b14`: `memcpy`.
  obtain ⟨hmid14, hw14, htr14, hdi14, hsi14, hdx14⟩ := ok_b14
  refine St.run h (rest := [(gotAddr "memcpy", 8)]) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b14Offset + b14.length)).toBitVec) rfl
    (infix_of b14_in_code (by simp [b14]) hp) exit_b14 (fun _ _ ↦ rfl) hst2.fr hst2.same
    (hst2.hd.reg0 (by decide) rfl) (by decide) (wf1 h hst2.fr.kept h.gotIn)
    (St.mt_copy h hst2 (fun _ hq ↦ hq.elim)) hmid14 hw14 (by decide) htr14
    fun st3 hm3 hpc3 hst3 _ ↦ ?_
  have e_di : reg st3.data .rdi = off (fb m0) 6064 := (hm3.regs .rdi _ hdi14).trans (eval_ptr0 6064)
  have e_si : reg st3.data .rsi = off (fb m0) 136 := (hm3.regs .rsi _ hsi14).trans (eval_ptr0 136)
  have e_dx : (reg st3.data .rdx).toNat = 5920 := by
    rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ hdx14]; rfl
  have hsp3 : rspOf st3.data = fb m0 := by rw [hst3.fr.sp, off_zero]
  have hfm := Mapped.keeps (frame_mapped h.stack le_F) hst3.fr.kept
  have hpre : MemcpyPre st3.data := by
    unfold MemcpyPre
    rw [e_di, e_si, e_dx]
    refine ⟨St.stackOk h hst3 le_mc, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_, ?_, ?_, ?_⟩
    · rw [off_add]; exact hfm _ (by omega)
    · rw [off_add]; exact hfm _ (by omega)
    · unfold NoWrap; rw [toNat_off (by omega)]; omega
    · unfold NoWrap; rw [toNat_off (by omega)]; omega
    · unfold Apart; rw [toNat_off (by omega), toNat_off (by omega)]; omega
    · unfold Apart; rw [toNat_off (by omega), hsp3]; omega
  refine St.call h hst3 le_mc (lo := 6064) (n := 5920) (by decide) (by decide)
    hmc hpc3 hpre (W := Z) (fun _ h ↦ h.elim) (fun _ hq ↦ ⟨?_, hq.2.2.2⟩)
    fun m4 hst4 _ ↦ ?_
  · have h1 := hq.2.2.1
    rw [e_di, e_dx] at h1
    exact NativeRustcVm.SameOutside.mono h1 fun q hq' ↦ .inr (.inl hq')
  -- `b15`: the table blocks' count.
  have hsl := h.slIn
  have hAS : Apart (rspOf m0 + 8#64) 88 (stackArg m0 0) 888 := Apart.symm' h.slArgs
  let env5 := frameEnv m0 m4 F [(rspOf m0 + 8#64, 88), (stackArg m0 0, 888)] (fun _ ↦ 0) 0
  have hwf5 : env5.WF := wf2 h hst4.fr.kept h.argsIn hsl hAS
  have hm5 : Match env5 slS m4 :=
    St.mt hst4 ⟨rfl, rfl, rfl, trivial⟩ trivial trivial (allOf_append argAliases_ok ⟨by
      show env5.load 1 0 8 = stackArg m0 0 + BitVec.ofInt 64 0
      rw [St.arg h hst4 Z_outs (i := 0) (by decide)]; simp, trivial⟩)
  have htb := h.tb
  have hlen := h.sl_size
  have hb1 := h.blen
  have hbl : bl.length ≤ 51 := by have := htb.1; omega
  have l264 : env5.load 2 64 8 = BitVec.ofNat 64 bl.length := by
    rw [← hlen]
    exact St.load h hst4 Z_outs hsl (r := 2) (j := 0) (by simp; rfl) (o' := 64)
      (by decide) (by rw [Nat.zero_add]; exact htb.2)
  have l040 : env5.load 0 40 8 = BitVec.ofNat 64 bl.length := by
    rw [show env5.load 0 40 8 = (Env.ofMachine m4 [(fb m0, F + 8)]).load 0 40 8 from rfl,
      hst4.hd.load (r := 0) (o := 40) (i := 4) (by decide)]
    show reg m0 .r8 = _
    exact bv_eq h.r8
  obtain ⟨hmid15, hw15, htr15, hcx15⟩ := ok_b15
  have hpc4 : (⟨m4, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b14Offset + b14.length)⟩ : MachineState) =
      ⟨m4, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b15Offset)⟩ := rfl
  rw [hpc4]
  refine St.run h (rest := [(rspOf m0 + 8#64, 88), (stackArg m0 0, 888)]) (vs := fun _ ↦ 0)
    (ret := 0) rfl (infix_of b15_in_code (by simp [b15]) hp) exit_b15 nofun hst4.fr hst4.same
    ((hst4.hd.reg0 (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88), (stackArg m0 0, 888)])
      (by decide) rfl).append (St.holdsDA h hst4 Z_outs)) (by decide) hwf5 hm5 hmid15 hw15
    (by decide) htr15 fun st5 hm5' hpc5 hst5 _ ↦ ?_
  have hc15 : c15.eval env5 = false := by
    show (!(CmpOp.apply .ult .W64 (BinOp.apply .sub .W64 (env5.load 2 64 8) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 50)) && !(CmpOp.apply .eq .W64 (BinOp.apply .sub .W64 (env5.load 2 64 8)
        (BitVec.ofNat 64 1)) (BitVec.ofNat 64 50))) = false
    rw [l264, show BinOp.apply .sub .W64 (BitVec.ofNat 64 bl.length) (BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (bl.length - 1) from by
        simp only [BinOp.apply, low_W64, ext_W64]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
        simp; omega, eq64]
    simp only [CmpOp.apply, low_W64, ult_ofNat (by omega : bl.length - 1 < 2 ^ 64)
      (by decide : 50 < 2 ^ 64)]
    by_cases hl : bl.length - 1 < 50
    · simp [hl]
    · have : bl.length - 1 = 50 := by omega
      simp [this]
  have e_cx : st5.data.regs.get64 .rcx = BitVec.ofNat 64 bl.length := by
    rw [hm5'.regs .rcx _ hcx15]
    unfold rcx15
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [show env5.load 0 40 8 = _ from l040, l264]
    simp
  have hc15' : c15.eval (frameEnv m0 m4 F [(rspOf m0 + 8#64, 88), (stackArg m0 0, 888)]
      (fun _ ↦ 0) 0) = false := hc15
  simp only [PcOk] at hpc5
  rw [hc15'] at hpc5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  -- `b16`: the loop's values.
  have hst5' : St m0 Z (Vt SL m0 lp) D15 8 st5.data :=
    St.add hst5 (fun _ _ ↦ rfl) (holds_reg (r := .rcx) (i := 4) (by
      rw [e_cx]; exact (bv_eq h.r8).symm) (holds_nil _ _ _))
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b16Offset) := hpc5
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5' hst5'
  subst hpc5'
  obtain ⟨hmid16, hw16, htr16, h40, h88⟩ := ok_b16
  refine St.run h (rest := [(rspOf m0 + 8#64, 88)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b16_in_code (by simp [b16]) hp) exit_b16 nofun hst5'.fr hst5'.same
    ((hst5'.hd.reg0 (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88)]) (by decide) rfl).append
      (St.holdsDA h hst5' Z_outs)) (by decide) (wf1 h hst5'.fr.kept h.argsIn)
    (St.mt hst5' ⟨rfl, rfl, trivial⟩ trivial trivial argAliases_ok) hmid16 hw16 (by decide) htr16
    fun st6 _ hpc6 hst6 hc ↦ .done _ ⟨hpc6, ?_, ?_⟩
  · have g_cx := hst5'.hd.reg (r := .rcx) (i := 4) (by decide)
    have g16 := hst5'.hd.load (r := 0) (o := 16) (i := 2) (by decide)
    have g88 := hst5'.hd.load (r := 0) (o := 88) (i := 1) (by decide)
    refine St.widen (St.sub (St.add (V' := Vt SL m0 (lpT L rows bl Fm SL m0 0)) hst6
      (fun p hp ↦ Vt_lt (by revert p hp; decide))
      (holds_content (s := Lw 40) (i := 25) (hc _ _ rfl h40) ?_
        (holds_content (s := Lw 88) (i := 24) (hc _ _ rfl h88) ?_
          (holds_cons (s := Rg .r12) (i := 32) ?_ (holds_cons (s := Rg .rsi) (i := 33) ?_
            (holds_cons (s := Rg .rdx) (i := 34) ?_ (holds_cons (s := Rg .r14) (i := 35) ?_
              (holds_cons (s := Rg .r15) (i := 36) ?_ (holds_nil _ _ _))))))))) (by decide))
      fun _ h ↦ h.elim
    · show BinOp.apply .shl .W64 (d5.regs.get64 .rcx) (BitVec.ofNat 64 4) = _
      rw [g_cx, shl4]
      rfl
    · show BinOp.apply .add .W64 (BinOp.apply .mul .W64
        ((Env.ofMachine d5 [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 16 8)
        (BitVec.ofNat 64 5928))
        ((Env.ofMachine d5 [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 88 8) = _
      rw [show (Env.ofMachine d5 [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 16 8 =
        (Env.ofMachine d5 [(fb m0, F + 8)]).load 0 16 8 from rfl,
        show (Env.ofMachine d5 [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]).load 0 88 8 =
        (Env.ofMachine d5 [(fb m0, F + 8)]).load 0 88 8 from rfl, g16, g88]
      simp only [BinOp.apply, low_W64, ext_W64]
      rfl
    · exact (hst6.hd (Rg .r12, 27) (by decide)).trans rfl
    · exact (hst6.hd (Rg .rsi, 27) (by decide)).trans rfl
    · exact (hst6.hd (Rg .rdx, 27) (by decide)).trans rfl
    · exact (hst6.hd (Rg .r14, 22) (by decide)).trans rfl
    · exact (hst6.hd (Rg .r15, 23) (by decide)).trans rfl
  · exact FormsAt.of_same h.forms (St.formsZ h hst6)

end

end NativeRustcVmX64.Bus.AccumulateSide
