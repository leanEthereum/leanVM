module

public import NativeRustcVmX64.Keccak.WordsHash.Lane
public import NativeRustcVmX64.Keccak.WordsHash.Vals
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): the entry

`setup_run`: the entry block (`entry`, `b0`) pushes the callee-saved registers, saves `out` in the
frame and calls `memset` to zero the lanes; the setup block (`setup`, `b1`) saves `mhi` and
`nb = len / 136` (`nb_val`), puts the bound `min(count, n) = n` in R12 and branches on
`136 ≤ len` (`SetupAt`). `entry_run`: then the first whole block's head (`fullInit`, `b5`: RBX
zero, R13 `17 nb`, RBP the lanes; `FullHead`), or, with no whole block, the last block's head
(`TailStart`). `fullHead_step` (`b10`), `tail_head` (`b2`): from a head to the block's first lane.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region
  load_of_wordAt)
open NativeRustcVmX64.Keccak (bytesAt_of_same)
open NativeRustcVm.Keccak (wordBlocks)
open Vm.Keccak256WordsOfHashWords

@[expose] public section

/-- R14 `len`. -/
def lenR (m0 : MachineData) : List (Reg64 × BitVec 64) := [(.r14, m0.regs.get64 .rdx)]

/-- The whole blocks' registers: R13 their words' count `17 nb`, RBP the lanes, R14 `len`. -/
def fullR (m0 : MachineData) : List (Reg64 × BitVec 64) :=
  [(.r13, BitVec.ofNat 64 (17 * nb m0)), (.rbp, frame m0 + BitVec.ofNat 64 40),
    (.r14, m0.regs.get64 .rdx)]

/-- The last block's registers: RSI `nb`, R14 `len`. -/
def tailR (m0 : MachineData) : List (Reg64 × BitVec 64) :=
  [(.rsi, BitVec.ofNat 64 (nb m0)), (.r14, m0.regs.get64 .rdx)]

/-- The state after the whole blocks. -/
abbrev stA (m0 : MachineData) : KeccakState := wordBlocks (word m0) (nb m0)

variable [Host]

/-- **After the setup**: the lanes zero, at the first whole block's set-up if `len` holds one,
else at the last block's head. -/
def SetupAt (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  HCtx m0 (lenR m0) 8 st.data ∧ Lanes m0 st.data.dmem (fun _ => 0) ∧
    st.pc = if 136 ≤ (m0.regs.get64 .rdx).toNat then Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b5Offset) else Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b2Offset)

/-- **At the head of whole block `b`.** -/
def FullHead (m0 : MachineData) (k b : Nat) (st : MachineState) : Prop :=
  HCtx m0 ((.rbx, BitVec.ofNat 64 (17 * b)) :: fullR m0) 8 st.data ∧
    Lanes m0 st.data.dmem (Keccak.lane (wordBlocks (word m0) b)) ∧ b < nb m0 ∧
    st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b10Offset)

/-- **At the last block's head**: the lanes the whole blocks' state. -/
def TailStart (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  HCtx m0 (lenR m0) 8 st.data ∧ Lanes m0 st.data.dmem (Keccak.lane (stA m0)) ∧
    st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b2Offset)

end

public section

theorem lane_replicate (i : Nat) : Keccak.lane (Vector.replicate 25 0 : KeccakState) i = 0 := by
  unfold Keccak.lane
  simp only [Vector.toArray_replicate, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- A word of zero bytes is zero. -/
theorem wordAt_zero {d : DataMem} {a : BitVec 64} {x : UInt8} (hx : x = 0)
    (h : BytesAt d a (List.replicate 200 x)) {i : Nat} (hi : i < 25) :
    WordAt d (a + BitVec.ofNat 64 (8 * i)) (0 : UInt64).toBitVec := by
  intro t ht
  simp only [List.length_map, List.length_range] at ht
  rw [addr_add, h (8 * i + t) (by rw [List.length_replicate]; omega), List.getElem_replicate, hx]
  simp [byteOf]

/-- The lanes are in the frame. -/
theorem inFrame_of_lanes {m0 : MachineData}
    (hstk : StackOk m0 NativeRustcVmX64.keccak256WordsStack) {p : BitVec 64}
    (h : InRange (frame m0 + BitVec.ofNat 64 40) 200 p) : InRange (frame m0) 288 p := by
  have hs := stack_facts hstk
  have h40 := frame_add_toNat hstk (o := 40) (by decide)
  rw [inRange_iff (by rw [h40]; omega), h40] at h
  rw [inRange_iff (by omega)]
  omega

theorem bv_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem ult_136 {x : BitVec 64} :
    (x.ult (BitVec.ofNat 64 136)) = decide (x.toNat < 136) := by
  simp [BitVec.ult]

variable [Host]

/-- A label of a block. -/
theorem label_at {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) {l : Label} {b' : List Directive} (h : b = .label l :: b') :
    Labels.label l = Host.addrOf (k + j) := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

set_option linter.unusedSimpArgs false in
/-- **The entry and the setup.** -/
theorem setup_run (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0) :
    Eventually (step1 Host.exe) (SetupAt m0 k) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b0Offset)⟩ := by
  have hstk := g.stk
  have hs := stack_facts hstk
  have h40 : (frame m0 + BitVec.ofNat 64 40).toNat = (frame m0).toNat + 40 :=
    frame_add_toNat hstk (by decide)
  let env0 := Env.ofMachine m0 [(frame m0, 296), (gotAddr "memset", 8)] (fun _ => 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b1Offset)).toBitVec
  obtain ⟨_, hgnw, hgs, _⟩ := g.got.1 "memset" (by simp)
  have hgf : Apart (frame m0) 296 (gotAddr "memset") 8 := by
    change Apart (gotAddr "memset") 8
      (stackBelow m0 NativeRustcVmX64.keccak256WordsStack) _ at hgs
    rw [stk_eq] at hgs
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
  -- the registers `setup` reads
  have r2 : ∀ r, calleeSaved r = true → st2.data.regs.get64 r = st1.data.regs.get64 r :=
    hsaved2.1
  have e14 : st2.data.regs.get64 .r14 = m0.regs.get64 .rdx := by
    rw [r2 .r14 rfl, hm1.regs .r14 _ rfl]; rfl
  have e15 : st2.data.regs.get64 .r15 = ws m0 := by
    rw [r2 .r15 rfl, hm1.regs .r15 _ rfl]; rfl
  have e12 : st2.data.regs.get64 .r12 = BitVec.ofNat 64 (nW m0) := by
    rw [r2 .r12 rfl, hm1.regs .r12 _ rfl]; exact bv_eq_ofNat _
  have ebp : st2.data.regs.get64 .rbp = BitVec.ofNat 64 (nW m0) := by
    rw [r2 .rbp rfl, hm1.regs .rbp _ rfl]
    show m0.regs.get64 .rsi = _
    rw [bv_eq_ofNat (m0.regs.get64 .rsi), g.cnt]
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b1Offset) := hpc2
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) setup hwf2 (fun _ h => by cases h)
    hpc2' hm2 fun st3 hm3 hpc3 => .done _ ⟨?_, ?_, ?_⟩
  · -- a slot `entry` wrote, kept by `memset` and `setup`
    have hslot : ∀ {o : Nat} {w : BitVec 64}, 32 ≤ o ∧ o + 8 ≤ 40 ∨ 240 ≤ o ∧ o + 8 ≤ 296 →
        WordAt st1.data.dmem (frame m0 + BitVec.ofNat 64 o) w →
        WordAt st3.data.dmem (frame m0 + BitVec.ofNat 64 o) w := fun {o} {w} ho h => by
      refine wordAt_keep hm3 hb2 (by omega) (firstOverlap_none_of fun w hw _ => ?_)
        (bytesAt_of_same hsame2 h fun i hi hr => ?_)
      · simp only [setup, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> simp <;> omega
      · simp only [List.length_map, List.length_range] at hi
        have hp : (frame m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i).toNat =
            (frame m0).toNat + (o + i) := by
          rw [addr_add, frame_add_toNat hstk (by omega)]
        rw [inRange_iff (by rw [h40]; omega), h40, hp] at hr
        omega
    refine ⟨rsp_of hm3 rfl rfl, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, ?_, ?_, trivial⟩, ?_, ?_, ?_⟩
    · show st3.data.regs.get64 .r12 = _
      rw [hm3.regs .r12 _ rfl]
      simp only [Sym.eval, env2, Env.ofMachine_regs, e12, ebp, ite_self]
    · exact (hm3.regs .r15 _ rfl).trans e15
    · exact (hm3.regs .r14 _ rfl).trans e14
    · exact wordAt_of_eq (wordAt_write hm3 hb2 (by simp) rfl) (by
        simp only [Sym.eval, env2, Env.ofMachine_regs, e14]; rfl)
    · exact wordAt_of_eq (wordAt_write hm3 hb2 (by simp) rfl) (by
        simp only [Sym.eval, env2, Env.ofMachine_regs, e14, nb_val]; rfl)
    · exact hslot (by simp) (wordAt_of_eq (wordAt_write hm1 hb0 (by simp) rfl) rfl)
    · simp only [SlotsAt, savedSlots, AllOf]
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
      simp only [setup, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp <;> omega) h
  · simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, env2, Env.ofMachine_regs, e14,
      ult_136] at hpc3
    rw [hpc3]
    by_cases h : 136 ≤ (m0.regs.get64 .rdx).toNat
    · simp only [show ¬ (m0.regs.get64 .rdx).toNat < 136 by omega, decide_false, Bool.not_false,
        ↓reduceIte, h]
      exact label_at hp b5_in_code rfl
    · simp only [show (m0.regs.get64 .rdx).toNat < 136 by omega, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, h]
      rfl

omit [Host] in
/-- The slot of `nb`, loaded. -/
theorem load_nb {m0 m : MachineData} {R : List (Reg64 × BitVec 64)} {o : Nat}
    (hc : HCtx m0 R o m) {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hb : rs[0]? = some (frame m0, 296)) :
    (Env.ofMachine m rs vars ret).load 0 24 8 = BitVec.ofNat 64 (nb m0) := by
  apply load_of_wordAt (r := 0)
  simp only [Env.base_ofMachine_eq, hb, Option.map_some, Option.getD_some]
  exact hc.slots.2.1

omit [Host] in
theorem nb_pos {m0 : MachineData} (h : 136 ≤ (m0.regs.get64 .rdx).toNat) : 0 < nb m0 := by
  unfold nb
  omega

/-- **The entry**: to the head of the first whole block, or with none, of the last block. -/
theorem entry_run (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0) :
    Eventually (step1 Host.exe) (fun st => FullHead m0 k 0 st ∨ TailStart m0 k st)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b0Offset)⟩ := by
  refine Eventually.bind (setup_run hms hp g) fun st h => ?_
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  by_cases h : 136 ≤ (m0.regs.get64 .rdx).toNat
  · simp only [h, ↓reduceIte] at hpc
    subst hpc
    obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
    have hnb := load_nb hc (rs := [(frame m0, 296)]) (vars := fun _ => 0) (ret := 0) rfl
    refine exec_then (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullInit hwf
      (fun _ h => by cases h) hm fun st hm' hpc => .done _ (.inl ⟨?_, ?_, nb_pos h, ?_⟩)
    · refine ctx_step g.stk (slotsH_low m0) hc hm' hwf rfl rfl rfl
        ⟨(hm'.regs .r12 _ rfl).trans hc.regs.1, (hm'.regs .r15 _ rfl).trans hc.regs.2.1,
          (hm'.regs .rbx _ rfl).trans rfl, ?_, ?_, (hm'.regs .r14 _ rfl).trans hc.regs.2.2.1,
          trivial⟩
      · show st.data.regs.get64 .r13 = _
        rw [hm'.regs .r13 _ rfl]
        simp only [Sym.eval, hnb, nb17_val]
      · show st.data.regs.get64 .rbp = _
        rw [hm'.regs .rbp _ rfl]
        simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rfl
    · refine lanes_congr (lanes_keep hm' rfl (fun w hw => by cases hw) hl) fun i _ => ?_
      rw [show wordBlocks (word m0) 0 = Vector.replicate 25 0 from rfl, lane_replicate]
    · simp only [PcOk] at hpc
      rw [hpc]
      exact label_at hp b10_in_code rfl
  · simp only [h, ↓reduceIte] at hpc
    refine .done _ (.inr ⟨hc, ?_, hpc⟩)
    have h0 : nb m0 = 0 := by unfold nb; omega
    show Lanes m0 m.dmem (Keccak.lane (wordBlocks (word m0) (nb m0)))
    rw [h0]
    exact lanes_congr hl fun i _ => (lane_replicate i).symm

/-- **A whole block's head**: its first word is in the slice. -/
theorem fullHead_step {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    {st : MachineState} (h : FullHead m0 k b st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 0 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b11Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b29Offset) st := by
  obtain ⟨hc, hl, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hb hpc
  subst hpc
  obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  have hin : 17 * b + 0 < nW m0 := by have := nb_le g; omega
  have hn := n_lt g
  refine exec_then (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullHead hwf
    (fun _ h => by cases h) hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_⟩
  · exact ctx_step g.stk (slotsH_low m0) hc hm' hwf rfl rfl rfl
      (regsAt_keep hm' hc.regs (names := [.r12, .r15, .rbx, .r13, .rbp, .r14]) rfl
        (by decide +kernel))
  · rw [pre_zero]
    exact lanes_keep hm' rfl (fun w hw => by cases hw) hl
  · have hult : (BitVec.ofNat 64 (17 * b)).ult (BitVec.ofNat 64 (nW m0)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs,
      hc.regs.2.2.1, hc.regs.1, hult] at hpc
    rw [hpc]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hin]
    rfl

/-- **The last block's head**: to its first lane, loaded if word `17 nb` is in the slice. -/
theorem tail_head {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailStart m0 k st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR m0) (stA m0) (17 * nb m0) 0 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b3Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b46Offset) st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  subst hpc
  obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  have hnb := load_nb hc (rs := [(frame m0, 296)]) (vars := fun _ => 0) (ret := 0) rfl
  have hle := nb_le g
  have hn := n_lt g
  refine exec_then (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailHead hwf
    (fun _ h => by cases h) hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_⟩
  · refine ctx_step g.stk (slotsH_low m0) hc hm' hwf rfl rfl rfl
      ⟨(hm'.regs .r12 _ rfl).trans hc.regs.1, (hm'.regs .r15 _ rfl).trans hc.regs.2.1, ?_,
        (hm'.regs .rsi _ rfl).trans hnb, (hm'.regs .r14 _ rfl).trans hc.regs.2.2.1, trivial⟩
    show st.data.regs.get64 .rax = _
    rw [hm'.regs .rax _ rfl]
    simp only [Sym.eval, hnb, nb17_val]
  · rw [pre_zero]
    exact lanes_keep hm' rfl (fun w hw => by cases hw) hl
  · have hult : (BitVec.ofNat 64 (17 * nb m0)).ult (BitVec.ofNat 64 (nW m0)) =
        decide (17 * nb m0 + 0 < nW m0) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, hnb,
      nb17_val, hc.regs.1, hult] at hpc
    rw [hpc]
    by_cases hin : 17 * nb m0 + 0 < nW m0
    · simp only [hin, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [hin, decide_false, Bool.not_false, ↓reduceIte]
      exact label_at hp b46_in_code rfl

end

end NativeRustcVmX64.WordsHash
