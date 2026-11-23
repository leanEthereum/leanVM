module

public import NativeRustcVmX64.Wire.Decode.Entry
public import NativeRustcVm.Wire.RowsFacts
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names

/-!
# `decode`: the stream and the phase count (x86-64)

`stream_run`: from `Reader::words`' call (`At3`, `b3`), the stream's words into the decoded area
from word `1`, their tag (`b4`), the count stored at word `0` and `Reader::le` for the phase count
`p` (`b5`), its tag and `p ≤ 8` (`b6`), the room for the stream (`b7`), `p` stored at word
`streamEnd L` and the loop's registers (`b8`): to the loop's head with no phase read (`Head`), or
out with `None`.
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.Decode
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  after after_eq eval_ptr0 wordAt_write mapped_off stackOk_callee streamEnd_eval trunc32_mod)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off Mapped.keeps PhaseAt)
open NativeRustcVmX64.Wire.PhaseM (bytesAt_keep wordAt_keep wordsAt_keep reader_keep iv_of_inRange
  le4_call Read4 read4_cases callee_toNat toNat_toUInt64)
open NativeRustcVmX64.Sumcheck (testAl_eq)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **The loop's head** (`b9`, `NativeRustcVmX64.Vm.Decode.label_6`) after `i` of the `p` phases (`done`), the reader at
`ci`: the model's rest is `tailPh` from there. -/
structure Head [Labels] [Host] (m0 : MachineData) (k n : Nat) (ws : List K) (p i : Nat)
    (done : List PhaseOut) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b9Offset)
  bod : Bod m0 8 st.data
  pos : 4 ≤ LN m0
  model : decodeM (Bs m0) = tailPh (Bs m0) (streamOf n ws) done (p - i) ci
  ple : p ≤ 8
  ile : i ≤ p
  dlen : done.length = i
  dec : Dec m0 st.data.dmem n ws p done
  rd : ReaderAt st.data.dmem (rdA m0) (BP m0) (Bs m0) ci
  r12 : (reg st.data .r12).toNat = p
  rbp : (reg st.data .rbp).toNat = i
  r13 : reg st.data .r13 + BitVec.ofNat 64 395288 = wd m0 (phaseBase (LN m0) i)
  r14 : 9 ≤ (reg st.data .r14).toNat

/-- **After the stream's words** (`b5`). -/
structure At5 [Labels] [Host] (m0 : MachineData) (k n : Nat) (ws : List K) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b5Offset)
  bod : Bod m0 8 st.data
  h1 : rdU32 (Bs m0) 0 = some (n, 4)
  hw : rdWords (Bs m0) (2 * n) 4 = some (ws, 4 + 16 * n)
  fit : 4 + 16 * n ≤ LN m0
  wsl : ws.length = 2 * n
  hlt : 2 * n < LEN m0
  pos : 4 ≤ LN m0
  words : NativeRustcVm.WordsAt st.data.dmem (wd m0 1) (ws.map K.lane)
  rd : ReaderAt st.data.dmem (rdA m0) (BP m0) (Bs m0) (4 + 16 * n)
  r12 : (reg st.data .r12).toNat = n
  r13 : reg st.data .r13 = DEC m0
  r14 : reg st.data .r14 = reg m0 .rcx

/-- **After the phase count** (`b7`). -/
structure At7 [Labels] [Host] (m0 : MachineData) (k n : Nat) (ws : List K) (p : Nat)
    (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b7Offset)
  bod : Bod m0 8 st.data
  h1 : rdU32 (Bs m0) 0 = some (n, 4)
  hw : rdWords (Bs m0) (2 * n) 4 = some (ws, 4 + 16 * n)
  hv : rdU32 (Bs m0) (4 + 16 * n) = some (p, 8 + 16 * n)
  p8 : p < 9
  fit : 4 + 16 * n ≤ LN m0
  wsl : ws.length = 2 * n
  pos : 4 ≤ LN m0
  count : NativeRustcVm.WordAt st.data.dmem (wd m0 0) n.toUInt64
  words : NativeRustcVm.WordsAt st.data.dmem (wd m0 1) (ws.map K.lane)
  rd : ReaderAt st.data.dmem (rdA m0) (BP m0) (Bs m0) (8 + 16 * n)
  rdx : (reg st.data .rdx).toNat = p
  r13 : reg st.data .r13 = DEC m0
  r14 : reg st.data .r14 = reg m0 .rcx


end

public section

variable {m0 : MachineData}

theorem add_lit_eq (x : BitVec 64) (n : Nat) :
    BinOp.apply .add .W64 x (BitVec.ofNat 64 n) = x + BitVec.ofNat 64 n := by
  simp [BinOp.apply]

theorem add_lit_eq' (x : BitVec 64) (n : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 n) x = x + BitVec.ofNat 64 n := by
  simp [BinOp.apply, BitVec.add_comm]

/-- AL after a byte merged in. -/
theorem merge_mod (x y : BitVec 64) :
    (BinOp.apply .merge .W8 x y).toNat % 256 = y.toNat % 256 := by
  have h := congrArg BitVec.toNat (NativeRustcVmX64.Transcript.low8_replaceLow x (low .W8 y))
  simp only [BinOp.apply]
  rw [toNat_low, toNat_low] at h
  exact h


section
variable [Labels]

/-- The phase count's address, `R13 + 8 RAX`. -/
theorem pc_addr (G : Geo m0) {r : BitVec 64} {i : Nat} (hr : r.toNat = i) (hi : i < LEN m0) :
    BinOp.apply .add .W64 (DEC m0) (BinOp.apply .mul .W64 r (BitVec.ofNat 64 8)) = wd m0 i := by
  have hdn := G.dNw
  apply BitVec.eq_of_toNat_eq
  rw [G.wd hi]
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    hr]
  omega

end

variable [Host] {k : Nat}

/-- **The stream's words**, from `Reader::words`' call to the count's store. -/
theorem words_run (hp : Placed code k) (G : Geo m0)
    (hrw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) {n : Nat}
    {st : MachineState} (h : At3 m0 k n st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ ∃ ws, At5 m0 k n ws st') st := by
  obtain ⟨hpc, hbod, hR, h1, hnl, hrcx, hrdx, hlt, hr13, hr14, hpos⟩ := h
  have hst := G.st
  have hsp := G.sp
  have htop := G.top
  have hlen := G.len
  rw [decodedWords_eq] at hlen
  have hdn := G.dNw
  have hwn := G.wNw
  have hbn := G.bNw
  have hsD := G.sD
  have hsB := G.sB (by omega)
  have hbD := G.bD (by omega)
  have hS := stackBelow_toNat (m := m0) (n := 80) (by omega)
  have hr := G.fr (j := 8) (by omega)
  have hr' : (rdA m0).toNat = SP0 m0 - 72 := by rw [hr]; omega
  -- `b3`: `Reader::words`.
  obtain ⟨hmid3, hw3, hrsi3, hrdi3, hr12_3, hk3⟩ := ok_b3
  refine cblk hp G b3_in_code (by simp [b3]) exit_b3 hmid3 hw3 (hk3 .rbx (by simp))
    (hk3 .r15 (by simp)) hpc hbod fun s1 hb1 hs1 hm1 hpc1 ↦ ?_
  have hsp1 : rspOf s1.data = stackBelow m0 80 := by rw [hb1.fr.sp, off_zero]
  have hrsi : reg s1.data .rsi = off (DEC m0) 8 := by
    rw [show reg s1.data .rsi = _ from hm1.regs .rsi _ hrsi3]
    simp only [Sym.eval, Env.ofMachine_regs, add_lit_eq]
    rw [show st.data.regs.get64 .r13 = DEC m0 from hr13]
  have hrdi : reg s1.data .rdi = rdA m0 := (hm1.regs .rdi _ hrdi3).trans (eval_ptr0 8)
  have hrdx : (reg s1.data .rdx).toNat = 2 * n := by
    rw [show reg s1.data .rdx = _ from hm1.regs .rdx _ (hk3 .rdx (by simp))]; exact hrdx
  have hR1 : ReaderAt s1.data.dmem (rdA m0) (BP m0) (Bs m0) 4 :=
    reader_keep hR hs1 (fun q hq ↦ by rw [hr]; omega) (fun q hq ↦ by rw [length_Bs]; omega)
  have hrs : (off (DEC m0) 8).toNat = (DEC m0).toNat + 8 := toNat_off (by omega)
  obtain ⟨hc48, -⟩ := callee_toNat (n := 48) hsp1 (by omega)
  have hpre : ReaderWordsPre s1.data := by
    refine ⟨stackOk_callee hst hb1.fr.kept hsp1 (by unfold readerWordsStack readerLeStack; omega),
      ?_, BP m0, Bs m0, 4, by rw [hrdi]; exact hR1, ?_⟩
    · rw [hrsi, hrdx]
      have hdm : NativeRustcVm.Mapped m0.dmem (DEC m0) (8 * LEN m0) := G.dOk.1
      show NativeRustcVm.Mapped s1.data.dmem (off (DEC m0) 8) (8 * (2 * n)) ∧
        (off (DEC m0) 8).toNat + 8 * (2 * n) ≤ 2 ^ 64
      exact ⟨mapped_off (Mapped.keeps hdm hb1.fr.kept) (by omega), by omega⟩
    · rw [hrsi, hrdi, hrdx]
      simp only [stackR, readerWordsStack, readerLeStack, length_Bs, Nat.reduceAdd]
      exact disjoint4 (by rw [hc48, hr']; omega) (by rw [hc48]; omega) (by rw [hc48, hrs]; omega)
        (by rw [hr']; omega) (by rw [hr', hrs]; omega) (by rw [hrs]; omega)
  refine call_then hpc1 hrw hpre fun s2 hpc2 hrsp2 ⟨hres2, hso2, hsv2⟩ ↦ ?_
  rw [hrdi] at hres2 hso2
  rw [hrsi, hrdx] at hso2
  have hres := hres2 (BP m0) (Bs m0) 4 hR1
  rw [hrdx, hrsi] at hres
  have hc16 : (off (rdA m0) 16).toNat = SP0 m0 - 80 + 24 := by rw [off_off]; exact G.fr (by omega)
  have hb2 : Bod m0 8 s2.data := by
    refine Bod.call G hb1 hsv2 hrsp2 hso2 fun q ⟨Rg, hRg, hq⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRg
    rcases hRg with rfl | rfl | rfl <;>
      simp only [NativeRustcVm.Region.Holds, curRegion, frameR, readerWordsStack, readerLeStack,
        Nat.reduceAdd] at hq
    · have := iv_of_inRange (by rw [hrs]; omega) hq
      rw [hrs] at this
      exact ⟨.inr (.inl (by omega)), by omega⟩
    · have := iv_of_inRange (a := off (rdA m0) 16) (n := 8) (by rw [hc16]; omega) hq
      rw [hc16] at this
      exact ⟨.inl (by omega), by omega⟩
    · have := iv_of_inRange (a := stackBelow s1.data 48) (n := 48) (by rw [hc48]; omega) hq
      rw [hc48] at this
      exact ⟨.inl (by omega), by omega⟩
  have rk2 : ∀ x ∈ [Reg64.r13, .r14], reg s2.data x = reg st.data x := fun x hx ↦ by
    have hc : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    refine (hsv2.1 x hc).trans ?_
    exact hm1.regs x _ (hk3 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp))
  have h12_2 : reg s2.data .r12 = reg st.data .rcx := by
    exact (hsv2.1 .r12 rfl).trans (hm1.regs .r12 _ hr12_3)
  -- `b4`: the words' tag.
  refine fblk hp G b4_in_code (by simp [b4]) exit_b4 nofun ok_b4.1 (ok_b4.2 .rbx (by simp))
    (ok_b4.2 .r15 (by simp)) (st := ⟨s2.data, _⟩) (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b3_next))
    hb2 fun s3 hb3 hd3 hm3 hpc3 ↦ ?_
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, testAl_eq] at hpc3
  rcases hw : rdWords (Bs m0) (2 * n) 4 with _ | ⟨ws, c'⟩
  · -- The stream's words missing: `None`.
    rw [hw] at hres
    rw [show (s2.data.regs.get64 .rax).toNat % 256 = 0 from hres] at hpc3
    simp only [decide_true, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.Decode.label_9_at] at hpc3
    exact Eventually.mono (none_run hp G hpc3 hb3 (by rw [decodeM_eq, h1]; simp only [hw]))
      fun _ h ↦ .inl h
  rw [hw] at hres
  obtain ⟨hal, hws2, hR2⟩ := hres
  rw [show (s2.data.regs.get64 .rax).toNat % 256 = 1 from hal] at hpc3
  simp only [Nat.one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
  have hwsl : ws.length = 2 * n := rdWords_length hw
  have hc' : c' = 4 + 16 * n ∧ 4 + 16 * n ≤ LN m0 := by
    unfold rdWords at hw
    split at hw
    · rename_i hle'
      cases hw
      rw [length_Bs] at hle'
      omega
    · cases hw
  obtain ⟨rfl, hfit⟩ := hc'
  have rk3 : ∀ x ∈ [Reg64.r13, .r14], reg s3.data x = reg st.data x := fun x hx ↦ by
    rw [show reg s3.data x = _ from hm3.regs x _ (ok_b4.2 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp))]
    exact rk2 x hx
  have h12_3 : reg s3.data .r12 = reg st.data .rcx := by
    rw [show reg s3.data .r12 = _ from hm3.regs .r12 _ (ok_b4.2 .r12 (by simp))]; exact h12_2
  refine .done _ (.inr ⟨ws, hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b4_next), hb3, h1, hw, hfit,
    hwsl, hlt, hpos, by rw [hd3]; exact hws2, by rw [hd3]; exact hR2, ?_, ?_, ?_⟩)
  · rw [h12_3]; exact hrcx
  · rw [rk3 .r13 (by simp)]; exact hr13
  · rw [rk3 .r14 (by simp)]; exact hr14

/-- **The phase count**, from the count's store to the room's check. -/
theorem count_run (hp : Placed code k) (G : Geo m0)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {n : Nat} {ws : List K}
    {st : MachineState} (h : At5 m0 k n ws st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ ∃ p, At7 m0 k n ws p st') st := by
  obtain ⟨hpc3, hb3, h1, hw, hfit, hwsl, hlt, hpos, hws3, hR3, h12, h13, h14⟩ := h
  have hst := G.st
  have hsp := G.sp
  have htop := G.top
  have hlen := G.len
  rw [decodedWords_eq] at hlen
  have hdn := G.dNw
  have hwn := G.wNw
  have hbn := G.bNw
  have hsD := G.sD
  have hsB := G.sB (by omega)
  have hbD := G.bD (by omega)
  have hS := stackBelow_toNat (m := m0) (n := 80) (by omega)
  have hr := G.fr (j := 8) (by omega)
  have hr' : (rdA m0).toNat = SP0 m0 - 72 := by rw [hr]; omega
  -- `b5`: the count stored, `Reader::le` for the phase count.
  have hd0 : (DEC m0).toNat + 8 ≤ SP0 m0 - 1296 ∨ SP0 m0 + 8 ≤ (DEC m0).toNat := by omega
  have hwf5 := frame_wf (m0 := m0) (d := st.data) (F := 80) (rest := [(DEC m0, 8)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b5Offset + b5.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by omega)) hb3.fr.kept, frame_noWrap hst (by omega)⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      have hdm : NativeRustcVm.Mapped m0.dmem (DEC m0) (8 * LEN m0) := G.dOk.1
      exact ⟨NativeRustcVm.Mapped.mono (Mapped.keeps hdm hb3.fr.kept) (by omega),
        show (DEC m0).toNat + 8 ≤ 2 ^ 64 by omega⟩)
    (List.pairwise_pair.mpr (by
      show NativeRustcVm.Apart (stackBelow m0 80) (80 + 8) (DEC m0) 8
      unfold NativeRustcVm.Apart; rw [hS]; omega))
  have hm5 : Match (frameEnv m0 st.data 80 [(DEC m0, 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b5Offset + b5.length)).toBitVec) cntS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb3.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show reg st.data .r13 = _ + BitVec.ofInt 64 0
        rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero, h13]
        rfl, trivial⟩
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf5 (fun _ _ ↦ rfl)
    hpc3 hm5 fun s4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid5, hmem5, hcw5, hrsi5, hrdi5, hk5⟩ := ok_b5
  have hf4 : Frame m0 80 slots 0 s4.data := Frame.of_block hb3.fr hwf5 hm4 hmid5 slots_le
  have hs4 : NativeRustcVm.SameOutside st.data.dmem s4.data.dmem (fun q ↦
      (SP0 m0 - 80 ≤ q.toNat ∧ q.toNat < SP0 m0 - 72) ∨
      ((DEC m0).toNat ≤ q.toNat ∧ q.toNat < (DEC m0).toNat + 8)) := fun q hq ↦
    hm4.get?_mem0 hwf5 fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq (by
      rw [hmem5] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        dsimp only at h1 h2
        rw [hS] at h1 h2
        exact .inl (by omega)
      · simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        dsimp only at h1 h2
        exact .inr (by omega))
  have hcnt : NativeRustcVm.WordAt s4.data.dmem (wd m0 0) n.toUInt64 := by
    have := wordAt_write hm4 (r := 1) (o := 0) (b := DEC m0) (sz := 8) rfl (by omega) hcw5
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rw [show st.data.regs.get64 .r12 = reg st.data .r12 from rfl, ofBitVec_eq_toUInt64,
      h12] at this
    exact this
  -- `Reader::le` for the phase count.
  have hR4 : ReaderAt s4.data.dmem (rdA m0) (BP m0) (Bs m0) (4 + 16 * n) :=
    reader_keep hR3 hs4 (fun q hq ↦ by rcases hq with hq | hq <;> omega)
      (fun q hq ↦ by rw [length_Bs]; rcases hq with hq | hq <;> omega)
  have hrdi4 : reg s4.data .rdi = rdA m0 := (hm4.regs .rdi _ hrdi5).trans (eval_ptr0 8)
  have hrsi4 : (reg s4.data .rsi).toNat = 4 := by
    rw [show reg s4.data .rsi = _ from hm4.regs .rsi _ hrsi5]; rfl
  have rk4 : ∀ x ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg s4.data x = reg st.data x :=
    fun x hx ↦ hm4.regs x _ (hk5 x hx)
  refine le4_call hle hst (F := 80) (by omega) (lo := 32) (by omega) slots_lo hf4 hR4 hrdi4 hrsi4
    (by rw [hr']; omega) (by rw [hr']; omega) hpc4 fun m5 hf5 hcs5 hso5 hr5 ↦ ?_
  have hc16 : (off (rdA m0) 16).toNat = SP0 m0 - 80 + 24 := by rw [off_off]; exact G.fr (by omega)
  have hso5' : NativeRustcVm.SameOutside s4.data.dmem m5.dmem
      (fun q ↦ SP0 m0 - 56 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) := hso5.mono fun q hq ↦ by
    have := iv_of_inRange (a := off (rdA m0) 16) (n := 8) (by rw [hc16]; omega) hq
    rw [hc16] at this; omega
  have rk5 : ∀ x ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg m5 x = reg st.data x := fun x hx ↦ by
    have hc : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hcs5 x hc]; exact rk4 x hx
  have hb5 : Bod m0 8 m5 := by
    refine ⟨hf5, ((hb3.chg.trans hs4).trans hso5').mono fun q hq ↦ ?_, ?_, ?_⟩
    · rcases hq with (hq | hq | hq) | hq
      · exact hq
      · exact .inl (by omega)
      · exact .inr (.inl (by omega))
      · exact .inl (by omega)
    · rw [rk5 .rbx (by simp)]; exact hb3.rbx
    · rw [rk5 .r15 (by simp)]; exact hb3.r15
  have hd45 : NativeRustcVm.SameOutside st.data.dmem m5.dmem (fun q ↦
      (SP0 m0 - 80 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) ∨
      ((DEC m0).toNat ≤ q.toNat ∧ q.toNat < (DEC m0).toNat + 8)) :=
    (hs4.trans hso5').mono fun q hq ↦ by
      rcases hq with (hq | hq) | hq
      · exact .inl (by omega)
      · exact .inr hq
      · exact .inl (by omega)
  -- `b6`: the tag, `p ≤ 8`.
  refine fblk hp G b6_in_code (by simp [b6]) exit_b6 nofun ok_b6.1 (ok_b6.2 .rbx (by simp))
    (ok_b6.2 .r15 (by simp)) (st := ⟨m5, _⟩) (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b5_next) hb5
    fun s6 hb6 hd6 hm6 hpc6 ↦ ?_
  have rk6 : ∀ x ∈ [Reg64.rdx, .rbx, .r12, .r13, .r14, .r15], reg s6.data x = reg m5 x :=
    fun x hx ↦ hm6.regs x _ (ok_b6.2 x hx)
  rcases read4_cases hr5 with ⟨hn5, h05⟩ | ⟨p, hv5, h05, hdx5, hpl, hR5⟩
  · -- No phase count: `None`.
    have hc6 : c6.eval (frameEnv m0 m5 80 []) = true := c6_zero _ h05
    have hpc6' : s6.pc = if c6.eval (frameEnv m0 m5 80 []) = true then Labels.label NativeRustcVmX64.Vm.Decode.label_9
        else Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b6Offset + b6.length) := hpc6
    simp only [hc6, ↓reduceIte] at hpc6'
    rw [hp.label NativeRustcVmX64.Vm.Decode.label_9_at] at hpc6'
    refine Eventually.mono (none_run hp G hpc6' hb6 ?_) fun _ h ↦ .inl h
    simp only [decodeM_eq, h1, hw, afterStream, hn5]
  have hp6 : (reg s6.data .rdx).toNat = p := by rw [rk6 .rdx (by simp)]; exact hdx5
  have hc6 : c6.eval (frameEnv m0 m5 80 []) = !decide (p < 9) := c6_one _ h05 hdx5
  have hpc6' : s6.pc = if c6.eval (frameEnv m0 m5 80 []) = true then Labels.label NativeRustcVmX64.Vm.Decode.label_9
      else Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b6Offset + b6.length) := hpc6
  rw [hc6] at hpc6'
  by_cases hp8 : p < 9
  swap
  · -- More than eight phases: `None`.
    simp only [decide_eq_false hp8, Bool.not_false, ↓reduceIte] at hpc6'
    rw [hp.label NativeRustcVmX64.Vm.Decode.label_9_at] at hpc6'
    refine Eventually.mono (none_run hp G hpc6' hb6 ?_) fun _ h ↦ .inl h
    simp only [decodeM_eq, h1, hw, afterStream, hv5,
      show wireMaxPhases < p by unfold wireMaxPhases; omega, ↓reduceIte]
  simp only [decide_eq_true hp8, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc6'
  have hR6 : ReaderAt s6.data.dmem (rdA m0) (BP m0) (Bs m0) (8 + 16 * n) := by
    rw [hd6, show 8 + 16 * n = 4 + 16 * n + 4 by omega]; exact hR5
  refine .done _ (.inr ⟨p, hpc6'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b6_next), hb6, h1, hw,
    by rw [show 8 + 16 * n = 4 + 16 * n + 4 by omega]; exact hv5, hp8, hfit, hwsl, hpos, ?_, ?_,
    hR6, hp6, ?_, ?_⟩)
  · rw [hd6]
    refine wordAt_keep hcnt hso5' (by rw [show (wd m0 0).toNat = (DEC m0).toNat from
      (G.wd (by omega)).trans (by omega)]; omega) fun q hq ↦ ?_
    rw [show (wd m0 0).toNat = (DEC m0).toNat from (G.wd (by omega)).trans (by omega)]
    omega
  · rw [hd6]
    have hw1 : (wd m0 1).toNat = (DEC m0).toNat + 8 := G.wd (by omega)
    refine wordsAt_keep hws3 hd45 (by rw [hw1, List.length_map, hwsl]; omega) fun q hq ↦ ?_
    rw [hw1, List.length_map, hwsl]
    rcases hq with hq | hq <;> omega
  · rw [rk6 .r13 (by simp), rk5 .r13 (by simp)]; exact h13
  · rw [rk6 .r14 (by simp), rk5 .r14 (by simp)]; exact h14


end

end NativeRustcVmX64.Wire.Decode
