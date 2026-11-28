module

public import NativeRustcVmX64.Bus.BusLayout.SizesRun
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names

/-!
# `bus_layout`'s offsets (x86-64)

From `NativeRustcVmX64.Vm.BusLayout.label_16` to the placements' loop (`offsets_run`): `memset` of the offsets (`b20`),
`stack_offsets` of the sizes (`b21`; it succeeds, `b22`), the layout's start in the frame
(`b23`: its depth, no placement): `PInv 0`.
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmX64.Vm.BusLayout

public section

/-- **The placements' loop head** `NativeRustcVmX64.Vm.BusLayout.label_19`, `j` placements pushed. -/
structure PInv (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (j : Nat)
    (st : MachineData) : Prop where
  bd : Body m0 1808 busLayoutStack slots 8 st
  rbx : reg st .rbx = reg m0 .rdi
  r14 : reg st .r14 = reg m0 .rdx
  r15 : (reg st .r15).toNat = nf m0 + bl.length
  rax : reg st .rax = off (fb m0) 24
  rcx : reg st .rcx = BitVec.ofNat 64 j
  rdx : reg st .rdx = BitVec.ofNat 64 (min j (nf m0))
  lt : j < nf m0 + bl.length
  sizes : SizesAt st.dmem L bl m0 (nf m0 + bl.length)
  offs : OffsAt st.dmem L bl m0
  part : Part st.dmem L bl m0 j

/-- Words of the frame kept where memory changed only in a range apart from them. -/
theorem frameWord_keep {m0 : MachineData} {d d' : DataMem} {a n o : Nat} {w : UInt64}
    (hst : StackOk m0 busLayoutStack) (ho : o + 8 ≤ 1808)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off (fb m0) a) n))
    (hd : o + 8 ≤ a ∨ a + n ≤ o) (han : a + n ≤ 1808)
    (h : NativeRustcVm.WordAt d (off (fb m0) o) w) : NativeRustcVm.WordAt d' (off (fb m0) o) w := by
  have hN : 1808 ≤ busLayoutStack := by decide
  have hrsp := hst.1
  have htop := hst.2.1
  have hb : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  refine bytesAt_congr h fun i hi ↦ ?_
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  refine hs _ fun hq ↦ ?_
  rw [inRange_off_iff (by omega) (by omega)] at hq
  omega

/-- Words of the frame kept by a callee writing a range of the frame apart from them and its
stack. -/
theorem frameWord_keep_call {m0 d d' : MachineData} {a n o S' : Nat} {w : UInt64}
    (hst : StackOk m0 busLayoutStack) (hb : Body m0 1808 busLayoutStack slots 0 d)
    (hFS : 1808 + S' ≤ busLayoutStack) (ho : o + 8 ≤ 1808)
    (hs : Changes d d' S' (off (fb m0) a) n) (hd : o + 8 ≤ a ∨ a + n ≤ o) (han : a + n ≤ 1808)
    (h : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o) w := by
  have hN : 1808 ≤ busLayoutStack := by decide
  have hrsp := hst.1
  have htop := hst.2.1
  have hb' : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  refine bytesAt_congr h fun i hi ↦ ?_
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  refine hs _ fun hq ↦ ?_
  rcases hq with hq | hq
  · have hq' : NativeRustcVm.InRange (off (fb m0) a) n (off (fb m0) (o + i)) := hq
    rw [inRange_off_iff (by omega) (by omega)] at hq'
    omega
  · exact not_callee hst hb.sp0 hFS (by omega) hq

theorem sizes_keep' {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d d' : DataMem} {k a n : Nat} (hst : StackOk m0 busLayoutStack) (h : SizesAt d L bl m0 k)
    (hk : k ≤ 54) (hd : a + n ≤ 896 ∨ 896 + 8 * k ≤ a) (han : a + n ≤ 1808)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off (fb m0) a) n)) :
    SizesAt d' L bl m0 k := fun j hj ↦
  frameWord_keep hst (by omega) hs (by omega) han (h j hj)

theorem offs_keep {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d d' : DataMem} {a n : Nat} (hst : StackOk m0 busLayoutStack) (hn : nf m0 + bl.length ≤ 54)
    (h : OffsAt d L bl m0) (hd : a + n ≤ 1328) (han : a + n ≤ 1808)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off (fb m0) a) n)) :
    OffsAt d' L bl m0 := fun j hj ↦
  frameWord_keep hst (by omega) hs (by omega) han (h j hj)

/-- The sizes `stack_offsets` reads. -/
theorem natsOf_S [Labels] {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    (hpre : BusLayoutPre L bl m0) {m : MachineData}
    (hs : SizesAt m.dmem L bl m0 (nf m0 + bl.length)) {a : BitVec 64} (ha : a = off (fb m0) 896) :
    natsOf m a (nf m0 + bl.length) = (S L bl m0).toArray := by
  unfold natsOf
  rw [ha]
  congr 1
  apply List.ext_getElem (by simp [S_length])
  intro i hi1 hi2
  simp only [List.length_map, NativeRustcVm.length_wordsOf] at hi1
  simp only [List.getElem_map, NativeRustcVm.wordsOf, List.getElem_range]
  rw [show off (fb m0) 896 + BitVec.ofNat 64 (8 * i) = off (fb m0) (896 + 8 * i) from off_add _ _ _,
    NativeRustcVm.wordOf_of_wordAt (hs i hi1),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some, Nat.toUInt64_eq,
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (pre_S_le hpre _ (List.getElem_mem hi2))
      (by decide))]

/-- The offsets `stack_offsets` wrote. -/
theorem offsAt_of {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d : DataMem} (h : NativeRustcVm.WordsAt d (off (fb m0) 1328) (natWords (O L bl m0).1)) :
    OffsAt d L bl m0 := fun j hj ↦ by
  have hsz : (O L bl m0).1.size = nf m0 + bl.length := by rw [size_so, fws_size]
  have h' := NativeRustcVm.WordsAt.getElem h (i := j) (by simp [natWords, hsz, hj])
  rw [off_add] at h'
  simp only [natWords, List.getElem_map, Array.getElem_toList] at h'
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]

theorem toNat_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  rw [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- A range of the frame below the slots, for a callee: readable, apart from its stack. -/
theorem frame_ok {m0 d : MachineData} (hst : StackOk m0 busLayoutStack)
    (hb : Body m0 1808 busLayoutStack slots 0 d) {a n S' : Nat} (h8 : 8 ≤ a) (han : a + n ≤ 1808)
    (hFS : 1808 + S' ≤ busLayoutStack) :
    Readable d (off (fb m0) a) n ∧ OffStack d (off (fb m0) a) n S' := by
  have hN : 1808 ≤ busLayoutStack := by decide
  have hrsp := hst.1
  have htop := hst.2.1
  have hb' : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hoff : (off (fb m0) a).toNat = (fb m0).toNat + a := toNat_off (by omega)
  refine ⟨⟨fun t ht ↦ ?_, ?_⟩, ?_⟩
  · rw [off_add]; exact hb.fr.kept _ (frame_mapped hst hN (a + t) (by omega))
  · show NativeRustcVm.NoWrap _ _
    unfold NativeRustcVm.NoWrap; rw [hoff]; omega
  · show NativeRustcVm.Apart _ _ _ _
    rw [stackBelow_callee hb.sp0 (by omega)]
    have h2 := stackBelow_toNat (m := m0) (n := 1808 + S') (by omega)
    unfold NativeRustcVm.Apart
    rw [hoff, h2]
    omega

variable [Host] {k : Nat}

/-- **The offsets, the layout's start**: from `NativeRustcVmX64.Vm.BusLayout.label_16` to the placements' loop. -/
theorem offsets_run (hp : Placed code k)
    (hms : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hso : Spec (Labels.label NativeRustcVmX64.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost)
    {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    (hpre : BusLayoutPre L bl m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b20Offset))
    (hD : SzDone L bl m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b26Offset) ∧
      PInv L bl m0 0 st'.data) st := by
  have hst := hpre.1
  have hN : 1808 ≤ busLayoutStack := by decide
  have hSO : 1808 + stackOffsetsStack ≤ busLayoutStack := by decide
  have hn54 := pre_n hpre
  have hbl2 := hpre.2.2.2.2.1
  have hrsp := hst.1
  have htop := hst.2.1
  have hbase : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hbd := hD.bd
  -- `b20`: `memset` of the offsets.
  have hwf0 := wf_got hpre hbd.fr.kept (l := "memset") (by simp) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b20Offset + b20.length)).toBitVec)
  refine exec_at (infix_of b20_in_code (by simp [b20]) hp) run_b20 hwf0 (fun _ _ ↦ rfl) hpc
    (match_got hpre hbd.same (by simp) hbd.fr.sp)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, hdi1, hdx1, hsi1, h12_1, hk1⟩ := after_eq run_b20 ▸ ok_b20
  have bd1 := Body.of_block hst hN hbd hwf0 hm1 hmid1 (fun w h ↦ (hw1 w h).1) slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (fb m0) 8) := fun q hq ↦ hm1.get?_mem0 hwf0 fun hW ↦ hq (by
    obtain ⟨w, hw, b, sz, hb, j, h1, h2, rfl⟩ := written_off hwf0 hW
    have ⟨hr, hn⟩ := hw1 w hw
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact inRange_off_self (by omega) (by omega))
  have edi : reg st1.data .rdi = off (fb m0) 1328 := (hm1.regs .rdi _ hdi1).trans (eval_ptr0 1328)
  have edx : (reg st1.data .rdx).toNat = 432 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx1]; rfl
  have e12 : reg st1.data .r12 = off (fb m0) 1328 := (hm1.regs .r12 _ h12_1).trans (eval_ptr0 1328)
  obtain ⟨hR1, hO1⟩ := frame_ok hst bd1 (a := 1328) (n := 432) (S' := 0) (by omega) (by omega) (by omega)
  have hpreM : MemsetPre st1.data := by
    refine ⟨bd1.stackOk hst (by omega), ?_, ?_, ?_⟩
    · show NativeRustcVm.Mapped _ _ _; rw [edi, edx]; exact hR1.1
    · show NativeRustcVm.NoWrap _ _; rw [edi, edx]; exact hR1.2
    · show NativeRustcVm.Apart _ _ _ _
      rw [edi, edx, bd1.sp0]
      have hoff : (off (fb m0) 1328).toNat = (fb m0).toNat + 1328 := toNat_off (by omega)
      have hfb : (stackBelow m0 1808).toNat = (fb m0).toNat := rfl
      unfold NativeRustcVm.Apart; rw [hoff, hfb]; omega
  refine call_then hpc1 hms hpreM fun st2 hpc2 hrsp2 ⟨_, _, hso2, hsv2⟩ ↦ ?_
  rw [edi, edx] at hso2
  have bd2 := Body.call_frame (S' := 0) hst hN bd1 (a := 1328) (n := 432) (by omega) (by omega)
    hsv2 hrsp2 (NativeRustcVm.Transcript.SameOutside.mono hso2 fun _ h ↦ .inl h)
  have hsz2 : SizesAt st2.data.dmem L bl m0 (nf m0 + bl.length) :=
    sizes_keep' hst (sizes_keep' hst hD.sizes hn54 (.inl (by omega)) (by omega)
      (show NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
        (NativeRustcVm.InRange (off (fb m0) 0) 8) by rw [off_zero]; exact hs1))
      hn54 (.inr (by omega)) (by omega) hso2
  -- `b21`: `stack_offsets`.
  have hwf2 := wf0 (d := st2.data) hst hN bd2.fr.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b21Offset + b21.length)).toBitVec)
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) run_b21 hwf2 (fun _ _ ↦ rfl)
    (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b20_next)))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨bd2.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hw3, hdi3, hcx3, hsi3, hdx3, hk3⟩ := after_eq run_b21 ▸ ok_b21
  have bd3 := Body.of_block hst hN bd2 hwf2 hm3 hmid3 (fun w h ↦ (hw3 w h).1) slots_le
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (fb m0) 8) := fun q hq ↦ hm3.get?_mem0 hwf2 fun hW ↦ hq (by
    obtain ⟨w, hw, b, sz, hb, j, h1, h2, rfl⟩ := written_off hwf2 hW
    have ⟨hr, hn⟩ := hw3 w hw
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact inRange_off_self (by omega) (by omega))
  have hsz3 : SizesAt st3.data.dmem L bl m0 (nf m0 + bl.length) :=
    sizes_keep' hst hsz2 hn54 (.inl (by omega)) (by omega)
      (show NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
        (NativeRustcVm.InRange (off (fb m0) 0) 8) by rw [off_zero]; exact hs3)
  have e15_2 : reg st2.data .r15 = reg st.data .r15 :=
    (hsv2.1 .r15 rfl).trans (hk1.reg' hm1 (by simp))
  have edi3 : reg st3.data .rdi = off (fb m0) 896 := (hm3.regs .rdi _ hdi3).trans (eval_ptr0 896)
  have esi3 : (reg st3.data .rsi).toNat = nf m0 + bl.length := by
    rw [show reg st3.data .rsi = _ from hm3.regs .rsi _ hsi3]
    show (reg st2.data .r15).toNat = _
    rw [e15_2]; exact hD.r15
  have ecx3 : (reg st3.data .rcx).toNat = 54 := by
    rw [show reg st3.data .rcx = _ from hm3.regs .rcx _ hcx3]; rfl
  have edx3 : reg st3.data .rdx = off (fb m0) 1328 := by
    rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ hdx3]
    exact (hsv2.1 .r12 rfl).trans e12
  obtain ⟨hRs, hOs⟩ := frame_ok hst bd3 (a := 896) (n := 8 * (nf m0 + bl.length))
    (S' := stackOffsetsStack) (by omega) (by omega) hSO
  obtain ⟨hRo, hOo⟩ := frame_ok hst bd3 (a := 1328) (n := 8 * 54)
    (S' := stackOffsetsStack) (by omega) (by omega) hSO
  have hpreS : StackOffsetsPre st3.data := by
    refine ⟨bd3.stackOk hst hSO, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [esi3]; unfold columnCountW; omega
    · rw [edi3, esi3]; exact hRs
    · rw [edi3, esi3]; exact hOs
    · rw [edx3, ecx3]; exact hRo
    · rw [edx3, ecx3]; exact hOo
    · show NativeRustcVm.Apart _ _ _ _
      rw [edi3, esi3, edx3, ecx3]
      have h1 : (off (fb m0) 896).toNat = (fb m0).toNat + 896 := toNat_off (by omega)
      have h2 : (off (fb m0) 1328).toNat = (fb m0).toNat + 1328 := toNat_off (by omega)
      unfold NativeRustcVm.Apart; rw [h1, h2]; omega
    · have hg := (pre_got hpre).symbols (show ["memset"].Sublist ["memcpy", "memset"] by decide)
      refine got_callee hg (fun l hl i hi ↦
        get_keep hst bd3.same (hg.1 l hl).2.2.1 (hg.1 l hl).2.1 hi)
        bd3.sp0 hst.1 hSO ?_
      rw [edi3, esi3, edx3, ecx3]
      intro l hl a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact got_apart_frame hg hst hl hN (by omega)
      · exact got_apart_frame hg hst hl hN (by omega)
  refine call_then hpc3 hso hpreS fun st4 hpc4 hrsp4 ⟨hres4, hch4, hsv4⟩ ↦ ?_
  have hnats : natsOf st3.data (reg st3.data .rdi) (reg st3.data .rsi).toNat = (S L bl m0).toArray :=
    by rw [esi3]; exact natsOf_S hpre hsz3 edi3
  rw [hnats, esi3, ecx3, edx3] at hres4
  rw [ecx3, edx3] at hch4
  have hfit : OffsetsFit (S L bl m0).toArray :=
    offsetsFit (pre_S_le hpre) (by rw [S_length]; exact hn54)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hfit⟩)] at hres4
  obtain ⟨hax4, hdx4, hoffs4⟩ := hres4
  have bd4 := Body.call_frame hst hN bd3 (a := 1328) (n := 8 * 54) (by omega) hSO
    hsv4 hrsp4 hch4
  have hoffs : OffsAt st4.data.dmem L bl m0 := offsAt_of hoffs4
  have hsz4 : SizesAt st4.data.dmem L bl m0 (nf m0 + bl.length) := fun j hj ↦
    frameWord_keep_call hst bd3 hSO (by omega) hch4 (.inl (by omega)) (by omega) (hsz3 j hj)
  have e4 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st4.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv4.1 _ rfl).trans ((hk3.reg' hm3 (by simp)).trans ((hsv2.1 _ rfl).trans
        (hk1.reg' hm1 (by simp))))
  -- `b22`: it succeeded.
  have hwf4 := wf0 (d := st4.data) hst hN bd4.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b22_in_code (by simp [b22]) hp) run_b22 hwf4 nofun
    (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b21_next)))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨bd4.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hmem5, hk5⟩ := after_eq run_b22 ▸ ok_b22
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
  have bd5 : Body m0 1808 busLayoutStack slots 8 st5.data :=
    ⟨Frame.of_block bd4.fr hwf4 hm5 hmid5 slots_le, by rw [hd5]; exact bd4.same⟩
  simp only [PcOk] at hpc5
  change st5.pc = if (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not.eval
    (Env.ofMachine st4.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = true then _
    else _ at hpc5
  have hc5 : (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not.eval
      (Env.ofMachine st4.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = false := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [show st4.data.regs.get64 .rax = 1#64 from hax4]
    rfl
  rw [hc5] at hpc5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  -- `b23`: the layout's start.
  have hwf5 := wf0 (d := st5.data) hst hN bd5.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b23_in_code (by simp [b23]) hp) run_b23 hwf5 nofun
    (hpc5.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b22_next)))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨bd5.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hw6, hwr6, hbd6, hax6, hcx6, hdx6, hk6⟩ := after_eq run_b23 ▸ ok_b23
  have bd6 := Body.of_block hst hN bd5 hwf5 hm6 hmid6 hw6 slots_le
  have hs6 := sameOutside_sub hwf5 hm6 (r := 0) rfl (show 896 ≤ 1808 + 8 by omega) (lo := 8)
    fun w hw ↦ ⟨hw6 w hw, hbd6 w hw⟩
  rw [show 896 - 8 = 888 by rfl] at hs6
  simp only [PcOk] at hpc6
  have K6 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st6.data r = reg st.data r := fun r hr ↦
    (hk6.reg' hm6 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h])).trans ((hk5.reg' hm5 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h])).trans (e4 r hr))
  refine .done _ ⟨hpc6.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_19_at), bd6, ?_, ?_, ?_,
    (hm6.regs .rax _ hax6).trans (eval_ptr0 24), hm6.regs .rcx _ hcx6,
    (hm6.regs .rdx _ hdx6).trans rfl, by omega, ?_, ?_, ?_⟩
  · exact (K6 .rbx (by simp)).trans hD.rg.rbx
  · exact (K6 .r14 (by simp)).trans hD.rg.r14
  · rw [K6 .r15 (by simp)]; exact hD.r15
  · exact sizes_keep' hst (show SizesAt st5.data.dmem L bl m0 _ by rw [hd5]; exact hsz4) hn54
      (.inl (by omega)) (by omega) hs6
  · exact offs_keep hst hn54 (show OffsAt st5.data.dmem L bl m0 by rw [hd5]; exact hoffs)
      (by omega) (by omega) hs6
  · refine ⟨?_, ?_, fun j hj ↦ absurd hj (by omega), fun j hj ↦ absurd hj (by omega)⟩
    · refine wordAt_write_eq hm6 (b := fb m0) (o := 8) rfl (by omega) (.reg .rdx)
        (hwr6.find (by simp)) ?_
      show reg st5.data .rdx = _
      rw [hk5.reg' hm5 (by simp)]
      apply BitVec.eq_of_toNat_eq
      rw [hdx4, toNat_toUInt64' (pre_depth_lt hpre)]
    · refine wordAt_write_eq hm6 (b := fb m0) (o := 72) rfl (by omega) (.lit 0)
        (hwr6.find (by simp)) ?_
      rw [Nat.zero_sub]; rfl

end

end NativeRustcVmX64.Bus.BusLayout
