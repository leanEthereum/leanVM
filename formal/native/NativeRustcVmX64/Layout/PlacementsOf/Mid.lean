module

public import NativeRustcVmX64.Layout.PlacementsOf.Turn1
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names

/-!
# `placements_of` on x86-64: `stack_offsets` (`b9` to `b15`)

After the first loop: `b9` zeroes `block_offsets` (`memset`), `b10` checks the count (`94`),
`b11` calls `stack_offsets` on the stacked columns' sizes (`sizesOf`), which places them
(`ow_getD`, `ow_snd`) and fits (`fit`); `b12` checks its `Some`, `b13` keeps the stack's
log-size at the frame's `8` and zeroes `offsets` (`memset`), `b14` and `b15` start the second
loop (`mid`, `I2 m0 0`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

section
variable [Labels]

/-- **The second loop** at `.L10`: the offsets of the stacked columns before the `i`th copied
into `offsets`. -/
structure I2 (m0 : MachineData) (i : Nat) (d : MachineData) : Prop where
  b : B m0 8 d
  le : i ≤ 94
  rax : (reg d .rax).toNat = i
  r13 : (reg d .r13).toNat = 94
  rbp : reg d .rbp = rodataAddr .keccakSlot
  r12 : reg d .r12 = rodataAddr .keccakOutput
  r14 : reg d .r14 = kk m0
  rbx : reg d .rbx = pp m0
  tot : WordAt d.dmem (off (fb m0) 8) (log2Ceil (sumF (κ m0) 0)).toUInt64
  cols : ∀ q (h : q < 94), WordAt d.dmem (off (fb m0) (1280 + 8 * q))
    (blockList[q]'(by rw [blockList_length]; exact h)).toUInt64
  offs : ∀ q (h : q < 94), WordAt d.dmem (off (fb m0) (3808 + 8 * q))
    (sumF (κ m0) (keyF (κ m0) (blockList[q]'(by rw [blockList_length]; exact h)))).toUInt64
  done : ∀ q (h : q < 94), q < i →
    WordAt d.dmem (off (fb m0) (16 + 8 * blockList[q]'(by rw [blockList_length]; exact h)))
      (sumF (κ m0) (keyF (κ m0) (blockList[q]'(by rw [blockList_length]; exact h)))).toUInt64

end

end

public section

section
variable [Labels] {m0 : MachineData}

/-- A part of the frame from its byte `8` is off the stack of a callee at its base. -/
theorem part_offStack (hF : Facts m0) {d : MachineData} (hb : B m0 0 d) {o l n' : Nat}
    (h8 : 8 ≤ o) (hl : o + l ≤ 5120) (hn' : 5120 + n' ≤ 6464) :
    OffStack d (off (fb m0) o) l n' := by
  have := hF.rsp
  show (off (fb m0) o).toNat + l ≤ (stackBelow d n').toNat ∨
    (stackBelow d n').toNat + (n' + 8) ≤ (off (fb m0) o).toNat
  rw [stackBelow_callee hb.rsp0 (by omega), stackBelow_toNat (by omega), hF.off_toNat (by omega)]
  omega

omit [Labels] in
/-- A word of the frame kept by a change elsewhere. -/
theorem word_keep {d d' : Mem 64} {o : Nat} {v : UInt64} (h : WordAt d (off (fb m0) o) v)
    {X : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' X)
    (hX : ∀ i < 8, ¬ X (off (fb m0) (o + i))) : WordAt d' (off (fb m0) o) v :=
  bytesAt_congr h fun i hi ↦ by
    have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
    rw [off_add]
    exact hs _ (hX i hi8)

/-- The sizes `block_sizes` holds: `sizesOf`. -/
theorem natsOf_sizes (hF : Facts m0) {d : MachineData}
    (h : ∀ q (hq : q < 94), WordAt d.dmem (off (fb m0) (2544 + 8 * q))
      (κ m0 (blockList[q]'(by rw [blockList_length]; exact hq))).toUInt64) :
    natsOf d (off (fb m0) 2544) 94 = sizesOf (κ m0) := by
  apply Array.ext
  · simp [natsOf, sizesOf, NativeRustcVm.wordsOf, blockList_length]
  · intro q h1 h2
    have hq : q < 94 := by simpa [natsOf, NativeRustcVm.wordsOf] using h1
    simp only [natsOf, sizesOf, List.getElem_toArray, List.getElem_map, NativeRustcVm.wordsOf,
      List.getElem_range]
    rw [off_add, NativeRustcVm.wordOf_of_wordAt (h q hq)]
    have := hF.κ_le (c := blockList[q]'(by rw [blockList_length]; exact hq))
      (lt_of_mem_blockList (List.getElem_mem _))
    exact toNat_toUInt64 (by omega)

end

variable [Host] {k : Nat} {m0 : MachineData}

/-- **`b9` to `b15`**: the stacked columns placed, the second loop's head. -/
theorem mid (hp : Placed code k) (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hso : Spec (label NativeRustcVmX64.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost) (hF : Facts m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b9Offset)) (hI : I1 m0 158 158 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b16Offset) ∧ I2 m0 0 s.data) st := by
  have hrsp := hF.rsp
  have h158 : below 158 = blockList := below_158
  have hn94 : (below 158).length = 94 := by rw [h158, blockList_length]
  -- the columns and sizes, by position in `blockList`
  have hcols : ∀ (d : MachineData), (∀ q (h : q < (below 158).length),
      WordAt d.dmem (off (fb m0) (1280 + 8 * q)) ((below 158)[q]).toUInt64) →
      ∀ q (h : q < 94), WordAt d.dmem (off (fb m0) (1280 + 8 * q))
        (blockList[q]'(by rw [blockList_length]; exact h)).toUInt64 := fun d h q hq ↦ by
    have := h q (by omega); simp only [h158] at this; exact this
  have hsizes : ∀ (d : MachineData), (∀ q (h : q < (below 158).length),
      WordAt d.dmem (off (fb m0) (2544 + 8 * q)) (κ m0 (below 158)[q]).toUInt64) →
      ∀ q (h : q < 94), WordAt d.dmem (off (fb m0) (2544 + 8 * q))
        (κ m0 (blockList[q]'(by rw [blockList_length]; exact h))).toUInt64 := fun d h q hq ↦ by
    have := h q (by omega); simp only [h158] at this; exact this
  -- `b9`: `memset(block_offsets)`
  obtain ⟨hok9, h97, h96, h92, hw9, hK9⟩ := ok_b9
  refine runGot (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b9Offset + b9.length)).toBitVec) hF
    (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b9 (fun _ _ ↦ rfl) hpc hI.b hok9
    (fun w hw => ⟨(hw9 w hw).1, by have := (hw9 w hw).2; omega⟩)
    fun st1 hm1 hpc1 hb1 ↦ ?_
  have hwf1 := hF.got_wf (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b9Offset + b9.length)).toBitVec)
    hI.b
  have hs1 := sameOutside_low hwf1 hm1 (r := 0) rfl (by decide) hw9
  have hrdi1 : reg st1.data .rdi = off (fb m0) 3808 := (hm1.regs .rdi _ h97).trans (eval_ptr0 3808)
  have hrdx1 : (reg st1.data .rdx).toNat = 1264 := by
    show (st1.data.regs.get64 .rdx).toNat = _; rw [hm1.regs .rdx _ h92]; rfl
  refine call_then hpc1 hms (memset_pre hF hb1 hrdi1 hrdx1 (by omega) (by omega))
    fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  have hb2 := memset_post hF hb1 hrdi1 hrdx1 (by omega) hpost2 hrsp2
  obtain ⟨-, -, hso2, hsv2⟩ := hpost2
  rw [hrdi1, hrdx1] at hso2
  have hK1 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg st2.data r = reg st.data r :=
    fun r hr ↦ (hsv2.1 r (cs_callee r (sub5 r hr))).trans (kreg hm1 hK9 hr)
  -- the words of the first loop, kept by `b9` and `memset`
  have keep12 : ∀ {o : Nat} {v : UInt64}, 8 ≤ o → o + 8 ≤ 3808 →
      WordAt st.data.dmem (off (fb m0) o) v → WordAt st2.data.dmem (off (fb m0) o) v :=
    fun ho ho' h ↦ word_keep (word_keep h hs1 fun i hi ↦ notin_base (by omega) (by omega))
      hso2 fun i hi ↦ notin_off (by omega) (by omega) (by omega)
  have cols2 := hcols _ hI.cols
  have sizes2 := hsizes _ hI.sizes
  replace cols2 : ∀ q (h : q < 94), WordAt st2.data.dmem (off (fb m0) (1280 + 8 * q))
      (blockList[q]'(by rw [blockList_length]; exact h)).toUInt64 :=
    fun q hq ↦ keep12 (by omega) (by omega) (cols2 q hq)
  replace sizes2 : ∀ q (h : q < 94), WordAt st2.data.dmem (off (fb m0) (2544 + 8 * q))
      (κ m0 (blockList[q]'(by rw [blockList_length]; exact h))).toUInt64 :=
    fun q hq ↦ keep12 (by omega) (by omega) (sizes2 q hq)
  have hr13 : (reg st2.data .r13).toNat = 94 := by rw [hK1 .r13 (by simp), hI.r13, hn94]
  -- `b10`: the count
  obtain ⟨hok10, hmem10, hK10⟩ := ok_b10
  refine step0 hF (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b10 nofun
    (hpc2.trans rfl) hb2 hok10 hmem10 fun st3 hm3 hpc3 hb3 hd3 ↦ ?_
  simp only [PcOk] at hpc3
  obtain ⟨-, hno3⟩ := pc_of (P := ¬ 94 < 159) hpc3 (by
    rw [SBool.eval, ult_eval, decide_not]
    have e : ((Sym.reg .r13).eval (frameEnv m0 st2.data 5120 [] (fun _ ↦ 0) 0)).toNat = 94 := hr13
    rw [e]; rfl)
  -- `b11`: `stack_offsets`
  obtain ⟨hok11, h117, h116, h112, h111, hw11, hK11⟩ := ok_b11
  refine run0 (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b11Offset + b11.length)).toBitVec) hF
    (b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b11 (fun _ _ ↦ rfl)
    ((hno3 (by omega)).trans rfl) hb3 hok11 fun st4 hm4 hpc4 hb4 ↦ ?_
  have hwf4 := fr_wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b11Offset + b11.length)).toBitVec)
    hb3 hF.stack (by decide)
  have hs4 := sameOutside_low hwf4 hm4 (r := 0) rfl (by decide) hw11
  have hd23 : st3.data.dmem = st2.data.dmem := hd3
  have x7 : reg st4.data .rdi = off (fb m0) 2544 := (hm4.regs .rdi _ h117).trans (eval_ptr0 2544)
  have x6 : (reg st4.data .rsi).toNat = 94 := by
    show (st4.data.regs.get64 .rsi).toNat = _
    rw [hm4.regs .rsi _ h116]
    show (reg st3.data .r13).toNat = _
    rw [kreg hm3 hK10 (by simp [cs])]; exact hr13
  have x2 : reg st4.data .rdx = off (fb m0) 3808 := (hm4.regs .rdx _ h112).trans (eval_ptr0 3808)
  have x1 : (reg st4.data .rcx).toNat = 158 := by
    show (st4.data.regs.get64 .rcx).toNat = _; rw [hm4.regs .rcx _ h111]; rfl
  have keep4 : ∀ {o : Nat} {v : UInt64}, 8 ≤ o → o < 5072 →
      WordAt st2.data.dmem (off (fb m0) o) v → WordAt st4.data.dmem (off (fb m0) o) v :=
    fun ho ho' h ↦ word_keep (d := st3.data.dmem) (by rw [hd23]; exact h) hs4
      fun i hi ↦ notin_base (by omega) (by omega)
  have hsz : natsOf st4.data (reg st4.data .rdi) 94 = sizesOf (κ m0) := by
    rw [x7]
    exact natsOf_sizes hF fun q hq ↦ keep4 (by omega) (by omega) (sizes2 q hq)
  have hpre4 : StackOffsetsPre st4.data := by
    unfold StackOffsetsPre
    rw [x7, x6, x2, x1]
    have p1 := hF.part (o := 2544) (l := 8 * 94) hb4 (by omega)
    have p2 := hF.part (o := 3808) (l := 8 * 158) hb4 (by omega)
    exact ⟨hb4.stackOk hF.stack (by decide), by decide, p1, part_offStack hF hb4 (by omega)
      (by omega) (by decide), p2, part_offStack hF hb4 (by omega) (by omega) (by decide),
      hF.part_apart (by omega) (by omega) (by omega),
      got_callee hF.got (hF.got_bytes hb4) hb4.rsp0 hF.stack.1 (by decide) (by
        intro l hl a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;>
          exact got_apart_frame hF.got hF.stack hl (by decide) (by dsimp only; decide))⟩
  refine call_then hpc4 hso hpre4 fun st5 hpc5 hrsp5 hpost5 ↦ ?_
  obtain ⟨hres, hch5, hsv5⟩ := hpost5
  rw [x6, x1, hsz, x2, ite_eq_left_of_eq_true _ _ (eq_true (show 94 ≤ 158 ∧ OffsetsFit (sizesOf (κ m0))
    from ⟨by omega, fit (κ m0) fun c hc ↦ hF.κ_le hc⟩))] at hres
  obtain ⟨hrax5, hrdx5, hws5⟩ := hres
  unfold Changes at hch5
  rw [x2, x1] at hch5
  have hnot5 : ∀ j, 5072 ≤ j → j < 5128 → ¬ (NativeRustcVm.InRange (off (fb m0) 3808) (8 * 158)
      (off (fb m0) j) ∨ NativeRustcVm.InRange (stackBelow st4.data stackOffsetsStack)
        stackOffsetsStack (off (fb m0) j)) := by
    rintro j h1 h2 (h | h)
    · exact notin_off (by omega) (by omega) (by omega) h
    · exact (hb4.callee hF.stack (by decide) h).2 (fb_in hF.stack (by decide) (by omega))
  have hb5 : B m0 8 st5.data := hb4.call hsv5 hrsp5 hch5
    (fun q h ↦ h.elim (fun h ↦ Or.inr (inRange_frame_stack hF.rsp.2 hF.rsp.1 (by decide)
      (inRange_mono (hF.part_low (by omega) h) (by omega))))
      (fun h ↦ Or.inr (hb4.callee hF.stack (by decide) h).1))
    (fun p hp i hi ↦ hnot5 _ (by have := slots_ge p hp; omega) (by have := slots_le p hp; omega))
    (fun j hj ↦ hnot5 _ (by omega) (by omega))
  have keep5 : ∀ {o : Nat} {v : UInt64}, 8 ≤ o → o + 8 ≤ 3808 →
      WordAt st4.data.dmem (off (fb m0) o) v → WordAt st5.data.dmem (off (fb m0) o) v :=
    fun ho ho' h ↦ word_keep h hch5 fun i hi h' ↦ h'.elim
      (fun h' ↦ notin_off (by omega) (by omega) (by omega) h')
      (fun h' ↦ (hb4.callee hF.stack (by decide) h').2 (fb_in hF.stack (by decide) (by omega)))
  -- the offsets
  have offs5 : ∀ q (h : q < 94), WordAt st5.data.dmem (off (fb m0) (3808 + 8 * q))
      (sumF (κ m0) (keyF (κ m0) (blockList[q]'(by rw [blockList_length]; exact h)))).toUInt64 := by
    intro q hq
    have hl : q < (natWords (stackOffsets (sizesOf (κ m0))).1).length := by
      simp [natWords, ow_size, blockList_length, hq]
    have hw := NativeRustcVm.WordsAt.getElem hws5 hl
    rw [off_add] at hw
    have e := ow_getD (κ m0) (q := q) (by rw [blockList_length]; exact hq)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
      (by rw [ow_size, blockList_length]; exact hq), Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [blockList_length]; exact hq), Option.getD_some] at e
    simp only [natWords, List.getElem_map, Array.getElem_toList, e] at hw
    exact hw
  have hK45 : ∀ r ∈ cs, reg st5.data r = reg st2.data r := fun r hr ↦
    (hsv5.1 r (cs_callee r hr)).trans
      ((kreg hm4 hK11 hr).trans (kreg hm3 hK10 hr))
  -- `b12`: `Some`
  obtain ⟨hok12, hmem12, hK12⟩ := ok_b12
  refine step0 hF (b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b12 nofun
    (hpc5.trans rfl) hb5 hok12 hmem12 fun st6 hm6 hpc6 hb6 hd6 ↦ ?_
  simp only [PcOk] at hpc6
  obtain ⟨-, hno6⟩ := pc_of (P := ¬ 1 = 1) hpc6 (by
    rw [SBool.eval, eq_eval, decide_not]
    have e : ((Sym.reg .rax).eval (frameEnv m0 st5.data 5120 [] (fun _ ↦ 0) 0)).toNat = 1 := by
      show (reg st5.data .rax).toNat = _; rw [hrax5]; rfl
    rw [e]; rfl)
  -- `b13`: the stack's log-size kept, `memset(offsets)`
  obtain ⟨hok13, h137, h136, h132, hw13, hv13, hK13⟩ := ok_b13
  refine runGot (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b13Offset + b13.length)).toBitVec) hF
    (b13_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b13 (fun _ _ ↦ rfl)
    ((hno6 (by omega)).trans rfl) hb6 hok13
    (fun w hw => ⟨(hw13 w hw).1, by have := (hw13 w hw).2; omega⟩)
    fun st7 hm7 hpc7 hb7 ↦ ?_
  have hwf7 := hF.got_wf (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b13Offset + b13.length)).toBitVec)
    hb6
  have hs7 := sameOutside_low hwf7 hm7 (r := 0) rfl (by decide) hw13
  have htot7 : WordAt st7.data.dmem (off (fb m0) 8) (log2Ceil (sumF (κ m0) 0)).toUInt64 := by
    have := wordAt_write hm7 (r := 0) (o := 8) rfl (by decide) hv13
    rwa [u64_of (show ((Sym.reg .rdx).eval _).toNat = _ by
      show (reg st6.data .rdx).toNat = _
      rw [kreg hm6 hK12 (by simp), hrdx5, ow_snd])] at this
  have hrdi7 : reg st7.data .rdi = off (fb m0) 16 := (hm7.regs .rdi _ h137).trans (eval_ptr0 16)
  have hrdx7 : (reg st7.data .rdx).toNat = 1264 := by
    show (st7.data.regs.get64 .rdx).toNat = _; rw [hm7.regs .rdx _ h132]; rfl
  refine call_then hpc7 hms (memset_pre hF hb7 hrdi7 hrdx7 (by omega) (by omega))
    fun st8 hpc8 hrsp8 hpost8 ↦ ?_
  have hb8 := memset_post hF hb7 hrdi7 hrdx7 (by omega) hpost8 hrsp8
  obtain ⟨-, -, hso8, hsv8⟩ := hpost8
  rw [hrdi7, hrdx7] at hso8
  have keep8 : ∀ {o : Nat} {v : UInt64}, 1280 ≤ o → o < 5072 →
      WordAt st5.data.dmem (off (fb m0) o) v → WordAt st8.data.dmem (off (fb m0) o) v :=
    fun ho ho' h ↦ word_keep (word_keep (d := st6.data.dmem) (by rw [hd6]; exact h) hs7
        fun i hi ↦ notin_base (by omega) (by omega))
      hso8 fun i hi ↦ notin_off (by omega) (by omega) (by omega)
  have htot8 : WordAt st8.data.dmem (off (fb m0) 8) (log2Ceil (sumF (κ m0) 0)).toUInt64 :=
    word_keep htot7 hso8 fun i hi ↦ notin_off (by omega) (by omega) (by omega)
  have hK8 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg st8.data r = reg st2.data r :=
    fun r hr ↦ (hsv8.1 r (cs_callee r (sub5 r hr))).trans
      ((kreg hm7 hK13 hr).trans ((kreg hm6 hK12 (sub5d r hr)).trans (hK45 r (sub5 r hr))))
  -- `b14`, `b15`
  obtain ⟨hok14, hmem14, hK14⟩ := ok_b14
  refine step0 hF (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b14 nofun
    (hpc8.trans rfl) hb8 hok14 hmem14 fun st9 hm9 hpc9 hb9 hd9 ↦ ?_
  have hr13' : (reg st8.data .r13).toNat = 94 := by rw [hK8 .r13 (by simp)]; exact hr13
  simp only [PcOk] at hpc9
  obtain ⟨-, hno9⟩ := pc_of (P := (94 : Nat) = 0) hpc9 (by
    rw [test_eval']
    have e : ((Sym.reg .r13).eval (frameEnv m0 st8.data 5120 [] (fun _ ↦ 0) 0)).toNat = 94 := hr13'
    rw [e])
  obtain ⟨hok15, hmem15, hax15, hK15⟩ := ok_b15
  refine step0 hF (b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b15 nofun
    ((hno9 (by omega)).trans rfl) hb9 hok15 hmem15 fun st10 hm10 hpc10 hb10 hd10 ↦ .done _
      ⟨hpc10.trans rfl, ?_⟩
  have hK10' : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg st10.data r = reg st.data r :=
    fun r hr ↦ (kreg hm10 hK15 hr).trans ((kreg hm9 hK14 (sub5 r hr)).trans
      ((hK8 r hr).trans (hK1 r hr)))
  have hd := hd10.trans hd9
  refine ⟨hb10, by omega, ?_, by rw [hK10' .r13 (by simp), hI.r13, hn94],
    (hK10' .rbp (by simp)).trans hI.rbp, (hK10' .r12 (by simp)).trans hI.r12,
    (hK10' .r14 (by simp)).trans hI.r14, (hK10' .rbx (by simp)).trans hI.rbx, hd ▸ htot8,
    fun q hq ↦ hd ▸ keep8 (by omega) (by omega) (keep5 (by omega) (by omega) (keep4 (by omega)
      (by omega) (cols2 q hq))), fun q hq ↦ hd ▸ keep8 (by omega) (by omega) (offs5 q hq),
    fun q hq h ↦ absurd h (by omega)⟩
  show (st10.data.regs.get64 .rax).toNat = _; rw [hm10.regs .rax _ hax15]; rfl

end

end NativeRustcVmX64.Layout.PlacementsOf
