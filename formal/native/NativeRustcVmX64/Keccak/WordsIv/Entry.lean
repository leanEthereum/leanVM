module

public import NativeRustcVmX64.Keccak.WordsIv.Lane
public import NativeRustcVmX64.Keccak.WordsHash.Entry
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): the entry

`setup_run`: the entry block (`entry`, `b0`) pushes the callee-saved registers, keeps the count in
R13, the bytecode in R12, its word count in R15, saves `out` in the frame and calls `memset` to
zero the lanes; the setup block (`setup`, `b1`) saves `nb = len / 136` (`nb_val`) and `len`, and
branches on `136 ≤ len` (`SetupAt`). `entry_run`: then the first whole block's head (`fullInit`,
`b21`: RBP zero, RBX the lanes, R14 `17 nb`; `FullHead`), or, with no whole block, the last
block's head (`TailStart`). `fullHead_step` (`b26`), `tail_head` (`b2`): from a head to the
block's first lane.
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region
  load_of_wordAt)
open NativeRustcVmX64.Keccak (bytesAt_of_same)
open NativeRustcVm.Keccak (wordBlocks)
open NativeRustcVmX64.WordsHash (frame Ctx Lanes pre RegsAt keepsRegs ctx_step lanes_keep
  lanes_congr regsAt_keep rsp_of rsp_eval frame_wf frame_add frame_add_toNat frame_mapped
  frame_noWrap stack_facts inStack_of_frame inFrame_of_lanes firstOverlap_none_of wordAt_zero
  lane_replicate ult_136 pre_zero add64)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- R13 the count, R12 the bytecode, R15 its word count. -/
def baseR (m0 : MachineData) : List (Reg64 × BitVec 64) :=
  [(.r13, m0.regs.get64 .rsi), (.r12, bc m0), (.r15, m0.regs.get64 .r8)]

/-- The whole blocks' other registers: RBX the lanes, R14 their words' count `17 nb`. -/
def Rf (m0 : MachineData) : List (Reg64 × BitVec 64) :=
  [(.rbx, frame m0 + BitVec.ofNat 64 40), (.r14, BitVec.ofNat 64 (17 * nb m0))]

variable [Host]

/-- **After the setup**: the lanes zero, at the first whole block's set-up if `len` holds one,
else at the last block's head. -/
def SetupAt (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 (slotsI m0) (baseR m0) 8 st.data ∧ Lanes m0 st.data.dmem (fun _ => 0) ∧
    st.pc = if 136 ≤ (m0.regs.get64 .rdx).toNat then Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b21Offset)
      else Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b2Offset)

/-- **At the head of whole block `b`.** -/
def FullHead (m0 : MachineData) (k b : Nat) (st : MachineState) : Prop :=
  Ctx m0 (slotsI m0) (RL m0 .rbp (17 * b) (Rf m0)) 8 st.data ∧
    Lanes m0 st.data.dmem (Keccak.lane (wordBlocks (wv m0) b)) ∧ b < nb m0 ∧
    st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b26Offset)

/-- **At the last block's head**: the lanes the whole blocks' state. -/
def TailStart (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 (slotsI m0) (baseR m0) 8 st.data ∧
    Lanes m0 st.data.dmem (Keccak.lane (wordBlocks (wv m0) (nb m0))) ∧
    st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b2Offset)

end

public section

theorem len_small [Labels] {m0 : MachineData} (g : Geo m0) : (m0.regs.get64 .rdx).toNat < 2 ^ 32 := by
  have := g.len
  have := g.small
  unfold lenI at *
  omega

variable [Host]

/-- **The entry and the setup.** -/
theorem setup_run (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0) :
    Eventually (step1 Host.exe) (SetupAt m0 k) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b0Offset)⟩ := by
  have hstk := g.stk
  have hs := stack_facts hstk
  have h40 : (frame m0 + BitVec.ofNat 64 40).toNat = (frame m0).toNat + 40 :=
    frame_add_toNat hstk (by decide)
  let env0 := Env.ofMachine m0 [(frame m0, 296), (gotAddr "memset", 8)] (fun _ => 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b1Offset)).toBitVec
  obtain ⟨_, hgnw, hgs, _⟩ := g.got.1 "memset" (by simp)
  have hgf : Apart (frame m0) 296 (gotAddr "memset") 8 := by
    change Apart (gotAddr "memset") 8
      (stackBelow m0 NativeRustcVmX64.keccak256WordsStack) _ at hgs
    rw [WordsHash.stk_eq] at hgs
    unfold Apart at hgs ⊢
    omega
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk (fun _ h => h), frame_noWrap hstk⟩,
      ⟨g.got.mapped (by simp), hgnw⟩, trivial⟩ (List.pairwise_pair.mpr hgf)
  have hm0 : Match env0 startEntry m0 := by
    refine Match.withKnownBytes ?_ ?_
    · exact match_ofMachine ⟨rfl, rfl, trivial⟩
        ⟨rsp_eval (frame_add m0).symm rfl, trivial⟩ trivial trivial
        ⟨(BitVec.add_zero _).symm, trivial⟩
    · intro i hi
      simpa [env0, Env.base, Sym.eval] using g.got.byte (l := "memset") (by simp) hi
  have hb0 : env0.regions[0]? = some (frame m0, 296) := rfl
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) entry hwf0 (fun _ _ => rfl) hm0
    fun st1 hm1 hpc1 => ?_
  have hrdi1 : st1.data.regs.get64 .rdi = frame m0 + BitVec.ofNat 64 40 :=
    (hm1.regs .rdi _ rfl).trans (by simp [Sym.eval, env0])
  have hrdx1 : (st1.data.regs.get64 .rdx).toNat = 200 := by rw [hm1.regs .rdx _ rfl]; rfl
  have hrsi1 : st1.data.regs.get64 .rsi = 0#64 := by rw [hm1.regs .rsi _ rfl]; rfl
  have hrsp1 : rspOf st1.data = frame m0 + BitVec.ofNat 64 0 := rsp_of hm1 rfl rfl
  have hkept1 : Kept m0.dmem st1.data.dmem := hm1.kept hwf0
  have hpre1 : MemsetPre st1.data := by
    unfold MemsetPre
    simp only [NativeRustcX64.reg, hrdi1, hrdx1]
    refine ⟨⟨Nat.zero_le _, by rw [hrsp1, BitVec.add_zero]; omega, fun i hi => ?_⟩,
      fun i hi => ?_, ?_, ?_⟩
    · rw [hrsp1, BitVec.add_zero, BitVec.sub_zero]
      exact frame_mapped hstk hkept1 _ (by omega)
    · rw [addr_add]
      exact frame_mapped hstk hkept1 _ (by omega)
    · unfold NoWrap; rw [h40]; omega
    · unfold Apart; rw [h40, hrsp1, BitVec.add_zero]; omega
  refine call_then hpc1 hms hpre1 fun st2 hpc2 hrsp2 hpost => ?_
  obtain ⟨-, hzero, hsame2, hsaved2⟩ := hpost
  simp only [NativeRustcX64.reg, hrdi1, hrdx1, hrsi1] at hzero hsame2
  let env2 := Env.ofMachine st2.data [(frame m0, 296)]
  have hkept2 : Kept m0.dmem st2.data.dmem := fun p h => hsaved2.2 p (hkept1 p h)
  have hwf2 : env2.WF := frame_wf hstk hkept2
  have hrsp2' : rspOf st2.data = frame m0 + BitVec.ofNat 64 8 := by
    rw [hrsp2, hrsp1, BitVec.add_zero]
  have hm2 : Match env2 startMain st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨rsp_eval hrsp2' rfl, trivial⟩ trivial trivial trivial
  have hb2 : env2.regions[0]? = some (frame m0, 296) := rfl
  have r2 : ∀ r, calleeSaved r = true → st2.data.regs.get64 r = st1.data.regs.get64 r :=
    hsaved2.1
  have e13 : st2.data.regs.get64 .r13 = m0.regs.get64 .rsi := by
    rw [r2 .r13 rfl, hm1.regs .r13 _ rfl]; rfl
  have e12 : st2.data.regs.get64 .r12 = bc m0 := by
    rw [r2 .r12 rfl, hm1.regs .r12 _ rfl]; rfl
  have e15 : st2.data.regs.get64 .r15 = m0.regs.get64 .r8 := by
    rw [r2 .r15 rfl, hm1.regs .r15 _ rfl]; rfl
  have ebx : st2.data.regs.get64 .rbx = m0.regs.get64 .rdx := by
    rw [r2 .rbx rfl, hm1.regs .rbx _ rfl]; rfl
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b1Offset) := hpc2
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) setup hwf2 (fun _ h => by cases h)
    hpc2' hm2 fun st3 hm3 hpc3 => .done _ ⟨?_, ?_, ?_⟩
  · -- a slot `entry` wrote, kept by `memset` and `setup`
    have hslot : ∀ {o : Nat} {w : BitVec 64}, 32 ≤ o ∧ o + 8 ≤ 40 ∨ 240 ≤ o ∧ o + 8 ≤ 296 →
        WordAt st1.data.dmem (frame m0 + BitVec.ofNat 64 o) w →
        WordAt st3.data.dmem (frame m0 + BitVec.ofNat 64 o) w := fun {o} {w} ho h => by
      refine wordAt_keep hm3 hb2 (by omega) (firstOverlap_none_of fun w hw _ => ?_)
        (bytesAt_of_same hsame2 h fun i hi hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> simp <;> omega
      · simp only [List.length_map, List.length_range] at hi
        have hp : (frame m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i).toNat =
            (frame m0).toNat + (o + i) := by
          rw [addr_add, frame_add_toNat hstk (by omega)]
        rw [inRange_iff (by rw [h40]; omega), h40, hp] at hr
        omega
    refine ⟨rsp_of hm3 rfl rfl, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, ?_, ?_, trivial⟩, ?_, ?_, ?_⟩
    · exact (hm3.regs .r13 _ rfl).trans e13
    · exact (hm3.regs .r12 _ rfl).trans e12
    · exact (hm3.regs .r15 _ rfl).trans e15
    · refine wordAt_of_eq (wordAt_write hm3 hb2 (by simp) rfl) ?_
      simp only [Sym.eval, env2, Env.ofMachine_regs, ebx]
      rw [bv_eq_ofNat (m0.regs.get64 .rdx), nb_val (len_small g)]
      rfl
    · exact wordAt_of_eq (wordAt_write hm3 hb2 (by simp) rfl) (by
        simp only [Sym.eval, env2, Env.ofMachine_regs, ebx])
    · exact hslot (by simp) (wordAt_of_eq (wordAt_write hm1 hb0 (by simp) rfl) rfl)
    · simp only [NativeRustcVmX64.WordsHash.SlotsAt, NativeRustcVmX64.WordsHash.savedSlots, AllOf]
      exact ⟨hslot (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        trivial⟩
    · intro p hp
      have hpf : ¬ InRange (frame m0) 288 p := fun h => hp (inStack_of_frame hstk le_rfl h)
      exact (same_region hm3 hwf2 hb2 (lim := 32) (by decide) (by decide) p
        fun h => hpf (by have := frame_noWrap hstk; unfold NoWrap at this
                         rw [inRange_iff (by omega)] at h ⊢; omega)).trans
        ((hsame2 p fun h => hpf (inFrame_of_lanes hstk h)).trans
          (same_region hm1 hwf0 hb0 (lim := 288) (by decide) (by decide) p hpf))
    · exact fun p h => hm3.kept hwf2 p (hkept2 p h)
  · intro i hi
    have h := wordAt_zero (by rfl) hzero hi
    rw [addr_add] at h
    exact wordAt_keep hm3 hb2 (by omega) (firstOverlap_none_of fun w hw _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp <;> omega) h
  · simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, env2, Env.ofMachine_regs, ebx,
      ult_136] at hpc3
    rw [hpc3]
    by_cases h : 136 ≤ (m0.regs.get64 .rdx).toNat
    · simp only [show ¬ (m0.regs.get64 .rdx).toNat < 136 by omega, decide_false, Bool.not_false,
        ↓reduceIte, h]
      exact label_at hp b21_in_code rfl
    · simp only [show (m0.regs.get64 .rdx).toNat < 136 by omega, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, h]
      rfl

omit [Host] in
/-- The slot of `nb`, loaded. -/
theorem load_nb {m0 m : MachineData} {R : List (Reg64 × BitVec 64)} {o : Nat}
    (hc : Ctx m0 (slotsI m0) R o m) {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hb : rs[0]? = some (frame m0, 296)) :
    (Env.ofMachine m rs vars ret).load 0 16 8 = BitVec.ofNat 64 (nb m0) := by
  apply load_of_wordAt (r := 0)
  simp only [Env.base_ofMachine_eq, hb, Option.map_some, Option.getD_some]
  exact hc.slots.1

omit [Host] in
/-- `17 nb`, from the slot of `nb`. -/
theorem nb17_eval [Labels] {m0 : MachineData} (g : Geo m0) {env : Env}
    (h : env.load 0 16 8 = BitVec.ofNat 64 (nb m0)) :
    (Sym.bin .add .W64 (.load 0 16 8) (.bin .shl .W32 (.un .trunc .W32 (.load 0 16 8)) (.lit 4))).eval
      env = BitVec.ofNat 64 (17 * nb m0) := by
  simp only [Sym.eval, h]
  exact nb17_val (by have := nb_small g; omega)

omit [Host] in
/-- An index against the count R13 (from the entry's RSI). -/
theorem ult_cnt [Labels] {m0 : MachineData} (g : Geo m0) {i : Nat} (hi : i < 2 ^ 32) :
    (BitVec.ofNat 64 i).ult (m0.regs.get64 .rsi) = decide (i < cnt m0) := by
  have hc := cnt_small g
  rw [bv_eq_ofNat (m0.regs.get64 .rsi)]
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by unfold cnt at hc; omega)]
  rfl

/-- **The entry**: to the head of the first whole block, or with none, of the last block. -/
theorem entry_run (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0) :
    Eventually (step1 Host.exe) (fun st => FullHead m0 k 0 st ∨ TailStart m0 k st)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b0Offset)⟩ := by
  refine Eventually.bind (setup_run hms hp g) fun st h => ?_
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  by_cases h : 136 ≤ (m0.regs.get64 .rdx).toNat
  · simp only [h, ↓reduceIte] at hpc
    subst hpc
    obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
    have hnb := load_nb hc (rs := [(frame m0, 296)]) (vars := fun _ => 0) (ret := 0) rfl
    refine exec_then (b21_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullInit hwf
      (fun _ h => by cases h) hm fun st hm' hpc => .done _ (.inl ⟨?_, ?_, ?_, ?_⟩)
    · refine ctx_step g.stk (slotsI_low m0) hc hm' hwf rfl rfl rfl
        ⟨(hm'.regs .r13 _ rfl).trans hc.regs.1, (hm'.regs .r12 _ rfl).trans hc.regs.2.1,
          (hm'.regs .r15 _ rfl).trans hc.regs.2.2.1, (hm'.regs .rbp _ rfl).trans rfl, ?_, ?_,
          trivial⟩
      · show st.data.regs.get64 .rbx = _
        rw [hm'.regs .rbx _ rfl]
        simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rfl
      · show st.data.regs.get64 .r14 = _
        rw [hm'.regs .r14 _ rfl]
        exact nb17_eval g hnb
    · refine lanes_congr (lanes_keep hm' rfl (fun w hw => by cases hw) hl) fun i _ => ?_
      rw [show wordBlocks (wv m0) 0 = Vector.replicate 25 0 from rfl, lane_replicate]
    · unfold nb lenI; omega
    · simp only [PcOk] at hpc
      rw [hpc]
      exact label_at hp b26_in_code rfl
  · simp only [h, ↓reduceIte] at hpc
    refine .done _ (.inr ⟨hc, ?_, hpc⟩)
    have h0 : nb m0 = 0 := by unfold nb lenI; omega
    show Lanes m0 m.dmem (Keccak.lane (wordBlocks (wv m0) (nb m0)))
    rw [h0]
    exact lanes_congr hl fun i _ => (lane_replicate i).symm

/-- **A whole block's head**: its first index is below the count. -/
theorem fullHead_step {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    {st : MachineState} (h : FullHead m0 k b st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RL m0 .rbp (17 * b) (Rf m0)) (wordBlocks (wv m0) b) (17 * b) 0 NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b27Offset NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b46Offset) st := by
  obtain ⟨hc, hl, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hb hpc
  subst hpc
  obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  have hin : 17 * b + 0 < cnt m0 := full_lt g hb (by decide)
  have hc32 := cnt_small g
  refine exec_then (b26_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullHead hwf
    (fun _ h => by cases h) hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_⟩
  · exact ctx_step g.stk (slotsI_low m0) hc hm' hwf rfl rfl rfl
      (regsAt_keep hm' hc.regs (names := [.r13, .r12, .r15, .rbp, .rbx, .r14]) rfl
        (by decide +kernel))
  · rw [pre_zero]
    exact lanes_keep hm' rfl (fun w hw => by cases hw) hl
  · simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs,
      hc.regs.2.2.2.1, hc.regs.1, ult_cnt g (show 17 * b < 2 ^ 32 by omega)] at hpc
    rw [hpc]
    simp only [show 17 * b < cnt m0 by omega, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, hin]
    rfl

/-- **The last block's head**: to its first lane, by whether index `17 nb` is below the count. -/
theorem tail_head {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailStart m0 k st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RL m0 .rbx (17 * nb m0) []) (wordBlocks (wv m0) (nb m0)) (17 * nb m0) 0 NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b3Offset
        NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b78Offset) st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  subst hpc
  obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  have hnb := load_nb hc (rs := [(frame m0, 296)]) (vars := fun _ => 0) (ret := 0) rfl
  have hle := nb17_le g
  have hc32 := cnt_small g
  refine exec_then (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailHead hwf
    (fun _ h => by cases h) hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_⟩
  · refine ctx_step g.stk (slotsI_low m0) hc hm' hwf rfl rfl rfl
      ⟨(hm'.regs .r13 _ rfl).trans hc.regs.1, (hm'.regs .r12 _ rfl).trans hc.regs.2.1,
        (hm'.regs .r15 _ rfl).trans hc.regs.2.2.1, ?_, trivial⟩
    show st.data.regs.get64 .rbx = _
    rw [hm'.regs .rbx _ rfl]
    exact nb17_eval g hnb
  · rw [pre_zero]
    exact lanes_keep hm' rfl (fun w hw => by cases hw) hl
  · simp only [PcOk, SBool.eval, CmpOp.apply, low_W64] at hpc
    rw [nb17_eval g hnb, show (Sym.reg .r13).eval (Env.ofMachine m [(frame m0, 296)]) =
      m0.regs.get64 .rsi from hc.regs.1, ult_cnt g (show 17 * nb m0 < 2 ^ 32 by omega)] at hpc
    rw [hpc]
    by_cases hin : 17 * nb m0 + 0 < cnt m0
    · simp only [show 17 * nb m0 < cnt m0 by omega, hin, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [show ¬ 17 * nb m0 < cnt m0 by omega, hin, decide_false, Bool.not_false,
        ↓reduceIte]
      exact label_at hp b78_in_code rfl

end

end NativeRustcVmX64.WordsIv
