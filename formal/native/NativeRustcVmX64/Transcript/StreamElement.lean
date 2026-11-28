module

public import NativeRustcVmX64.Transcript.StreamElement.Exec
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.DecodedStreamElement.Names

/-!
# `Decoded::stream_element` on x86-64

**`streamElement_spec`**: the `Option<EW>` at RDI becomes `stream[i]?`. The slice is not empty
(`b0`); `i` below the count (`b1`) and `2 i + 3` within the slice without a carry (`b2`, never
failing below the count, the stream within `streamEnd l`) lead to `b4`, which copies element `i`;
otherwise `b3` stores the tag `0`. Each block runs from a fresh environment of the state it starts
in, the `ret`s from one of the return address.
-/

namespace NativeRustcVmX64.Transcript.StreamElement

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.DecodedStreamElement
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem toBitVec_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- **`b2`'s exit**: taken where `2 i + 3` is within the length. -/
theorem condB2_eval [Labels] (env : Env) {i n : Nat} (hi : (env.regs .rcx).toNat = i)
    (hn : (env.regs .rdx).toNat = n) (h : 2 * i + 3 ≤ n) : condB2.eval env = true := by
  have hn64 := (env.regs .rdx).isLt
  have hs : (sum3.eval env).toNat = 2 * i + 3 := by
    simp only [sum3, Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_sub, BitVec.toNat_add, hi, BitVec.toNat_ofNat]
    omega
  have h2 : ((Sym.bin .add .W64 (.reg .rcx) (.reg .rcx)).eval env).toNat = 2 * i := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_add, hi]
    omega
  have hc1 : ((SBool.cmp .ult .W64 sum3 (.reg .rdx)).not.and
      (SBool.cmp .eq .W64 sum3 (.reg .rdx)).not).eval env = false := by
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · have : (sum3.eval env).ult (env.regs .rdx) = true := by
        simp only [BitVec.ult, hs, hn, decide_eq_true_eq]; omega
      simp [this]
    · have : sum3.eval env = env.regs .rdx := BitVec.eq_of_toNat_eq (by rw [hs, hn, h'])
      simp [this]
  have hc2 : (SBool.cmp .ult .W64 (.bin .add .W64 (.reg .rcx) (.reg .rcx))
      (.lit 18446744073709551613)).not.eval env = false := by
    simp only [SBool.eval, CmpOp.apply, low_W64]
    have : ((Sym.bin .add .W64 (.reg .rcx) (.reg .rcx)).eval env).ult
        ((Sym.lit 18446744073709551613).eval env) = true := by
      simp only [BitVec.ult]
      rw [h2]
      simp only [Sym.eval, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    simp [this]
  simp only [condB2, SBool.eval, CmpOp.apply]
  simp only [Sym.eval, hc1, hc2, BinOp.apply, Bool.false_eq_true, ite_false, low8_replaceLow,
    low_ext]
  decide

variable [Host] {k : Nat}

/-- What a block keeps of the machine state it starts in. -/
structure Kept (m m' : MachineData) : Prop where
  dmem : m'.dmem = m.dmem
  saved : Saved m m'
  rsp : reg m' .rsp = reg m .rsp
  rdi : reg m' .rdi = reg m .rdi
  rsi : reg m' .rsi = reg m .rsi

/-- The `ret`, from a state with the entry's RSP and callee-saved registers, the output (apart
from the return address) the only bytes changed. -/
theorem finish_ret (hp : Placed code k) {m0 : MachineData} {stream : Array EW} {st : MachineState}
    {j : Nat} {b : List Directive} (hb : b.IsInfixAt code j) (hne : b ≠ [])
    (hpc : st.pc = Host.addrOf (k + j)) {x : Exit} {S : SState} (hx : exec b retS = some (S, x))
    (hok : EpiOk 0 [] S = true ∧ S.mem = []) (hst : StackOk m0 0)
    (hsv : Saved m0 st.data) (hrsp : rspOf st.data = rspOf m0)
    (hon : NativeRustcVm.NoWrap (reg m0 .rdi) 24)
    (hap : NativeRustcVm.Apart (reg m0 .rdi) 24 (stackBelow m0 0) (0 + 8))
    (hso : NativeRustcVm.SameOutside m0.dmem st.data.dmem (NativeRustcVm.InRange (reg m0 .rdi) 24))
    (hout : OptEWAt st.data.dmem (reg m0 .rdi) stream[(reg m0 .rcx).toNat]?)
    (hxr : x = .ret (.load 0 0 8)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ StreamElementPost stream m0 st'.data) st := by
  subst hxr
  have hfnw := frame_noWrap hst le_rfl
  have hf : Frame m0 0 [] 0 st.data := Frame.of_saved hsv hrsp fun j hj ↦ by
    refine hso _ fun h ↦ ?_
    have hq : NativeRustcVm.InRange (stackBelow m0 0) (0 + 8) (rspOf m0 + BitVec.ofNat 64 j) := by
      rw [← frame_add (m0 := m0) 0 j]
      exact inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega)
    exact not_inRange_of_apart hap hon hfnw h hq
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 0) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst le_rfl) hf.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of hb hne hp) hx hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm' hpc' => ?_
  obtain ⟨hsv', hrsp'⟩ := Frame.epilogue hf hwf hm' hok.1
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hok.2
  simp only [PcOk] at hpc'
  exact .done _ ⟨by rw [hpc']; exact hf.load_ret hst le_rfl, hrsp', by rw [hd]; exact hout,
    fun q hq ↦ by rw [hd]; exact hso q hq, hsv'⟩

/-- The tag `0` stored at the output: `None`. -/
theorem finish_none (hp : Placed code k) {m0 : MachineData} {stream : Array EW} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.DecodedStreamElement.b3Offset)) (hst : StackOk m0 0)
    (hon : NativeRustcVm.NoWrap (reg m0 .rdi) 24) (hom : NativeRustcVm.Mapped m0.dmem (reg m0 .rdi) 24)
    (hap : NativeRustcVm.Apart (reg m0 .rdi) 24 (stackBelow m0 0) (0 + 8))
    (hK : Kept m0 st.data) (hi : stream.size ≤ (reg m0 .rcx).toNat) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ StreamElementPost stream m0 st'.data) st := by
  set o := reg m0 .rdi
  have hon' : o.toNat + 24 ≤ 2 ^ 64 := hon
  have hwf : (Env.ofMachine st.data [(o, 24)]).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hK.saved.2 _ (hom i hi), hon⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(o, 24)]) noneS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨known_ptr rfl hK.rdi, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of ((infix_take b3 3).trans b3_in_code (by simp [b3])) (by simp [b3]) hp)
    run_b3 hwf nofun hpc hm fun st' hm' hpc' => ?_
  obtain ⟨hw, hws, hkeeps, hsp⟩ := after_eq run_b3 ▸ none_b3
  have hsame : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange o 24) :=
    sameOutside_region hwf hm' rfl hws
  refine finish_ret hp ((infix_drop b3 3).trans b3_in_code (by simp [b3])) (by simp [b3])
    (hpc'.trans (congrArg Host.addrOf (by simp [b3, Nat.add_assoc]))) run_b3r
    (after_eq run_b3r ▸ ⟨ok_ret.1, ok_ret.2.1⟩) hst
    (hK.saved.trans (Match.saved hm hm' hwf rfl hkeeps))
    (((hm'.regs .rsp _ hsp)).trans hK.rsp) hon hap
    (fun q hq ↦ by rw [hsame q hq, hK.dmem]) ?_ rfl
  rw [Array.getElem?_eq_none hi]
  have := wordAt_write hm' (r := 0) (o := 0) rfl (by omega) fun i hi ↦ by
    rw [Nat.zero_add]; exact hw i hi
  rwa [off_zero] at this

/-- **`Decoded::stream_element` meets its contract.** -/
theorem streamElement_spec (hp : Placed code k) (a : DecArea) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmX64.Vm.DecodedStreamElement.entryLabel) (StreamElementPre a stream openings)
      (StreamElementPost stream) := by
  rintro m0 ⟨hst, hx1, hx2, ⟨hrm, hrn⟩, hdec, hom, hon, hap, hapS⟩
  have hl64 := hdec.l_lt
  have hlen := hdec.len
  have hse := streamEnd_lt a.l
  have hsl := hdec.stream_le
  have hrn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hrn
  simp only [DecArea.region] at hrm
  simp only [NativeVm.streamEnd, NativeVm.maxStream] at hse hsl
  have hlen64 : a.len < 2 ^ 64 := by omega
  -- `b0`: the slice is not empty.
  unfold NativeRustcVmX64.Vm.DecodedStreamElement.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.DecodedStreamElement.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 (Env.wf_nil m0) nofun
    (match_nil m0) fun st1 hm1 hpc1 => ?_
  obtain ⟨hk1, hmem1, hr1⟩ := after_eq run_b0 ▸ ok_b0
  have hreg1 : ∀ r, reg st1.data r = reg m0 r := fun r ↦
    hm1.regs r _ (hr1 r (mem_allRegs r))
  have hK1 : Kept m0 st1.data :=
    ⟨hm1.dmem_eq (Env.wf_nil _) hmem1, Match.saved (match_nil m0) hm1 (Env.wf_nil _) rfl hk1,
      hreg1 _, hreg1 _, hreg1 _⟩
  simp only [PcOk] at hpc1
  split at hpc1
  · rename_i hc
    exfalso
    sym_simp_at hc
    simp only [Env.ofMachine_regs, BitVec.and_self, beq_iff_eq] at hc
    have : (reg m0 .rdx).toNat = 0 := by rw [show reg m0 .rdx = _ from hc]; rfl
    simp only [NativeVm.decodedWords, NativeVm.phaseBase] at hlen
    omega
  -- `b1`: `i` against the count.
  have hwfc : (Env.ofMachine st1.data [(a.words, 8)]).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ by
      show (st1.data.dmem.get? (a.words + BitVec.ofNat 64 i)).isSome
      exact hK1.saved.2 _ (hrm i (by simp only [NativeVm.decodedWords, NativeVm.phaseBase] at hlen; omega)), by
        show a.words.toNat + 8 ≤ 2 ^ 64
        simp only [NativeVm.decodedWords, NativeVm.phaseBase] at hlen; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hmc : Match (Env.ofMachine st1.data [(a.words, 8)]) countS st1.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨known_ptr rfl (hK1.rsi.trans hx1), trivial⟩ trivial trivial
      trivial
  have hd1 : st1.data.dmem = m0.dmem := hK1.dmem
  have hcnt : (Env.ofMachine st1.data [(a.words, 8)]).load 0 0 8 = stream.size.toUInt64.toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [hd1]; exact hdec.stream_count)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwfc nofun hpc1 hmc
    fun st2 hm2 hpc2 => ?_
  obtain ⟨hk2, hmem2, hrsi2, hr2⟩ := after_eq run_b1 ▸ ok_b1
  have hreg2 : ∀ r, r ≠ .rsi → reg st2.data r = reg m0 r := fun r hr ↦
    (hm2.regs r _ (hr2 r (mem_allRegs r) hr)).trans (hreg1 r)
  have hK2 : Kept m0 st2.data :=
    ⟨(hm2.dmem_eq hwfc hmem2).trans hd1, hK1.saved.trans (Match.saved hmc hm2 hwfc rfl hk2),
      hreg2 _ (by decide), hreg2 _ (by decide),
      ((hm2.regs .rsi _ hrsi2).trans (eval_ptr rfl)).trans hx1.symm⟩
  have hsize64 : stream.size < 2 ^ 64 := by omega
  have hN : (m0.regs.get64 .rcx).toNat = (reg m0 .rcx).toNat := rfl
  have hrcx1 : st1.data.regs.get64 .rcx = m0.regs.get64 .rcx := hreg1 .rcx
  simp only [PcOk] at hpc2
  split at hpc2
  · rename_i hc
    refine finish_none hp (hpc2.trans (hp.label NativeRustcVmX64.Vm.DecodedStreamElement.label_4_at)) hst hon hom hapS hK2 ?_
    sym_simp_at hc
    rw [hcnt] at hc
    simp only [Env.ofMachine_regs, Bool.not_eq_true', BitVec.ult] at hc
    have hc := of_decide_eq_false hc
    rw [toBitVec_toUInt64' hsize64, hrcx1] at hc
    omega
  -- `b2`: `2 i + 3` within the slice.
  rename_i hc
  have hi : (reg m0 .rcx).toNat < stream.size := by
    sym_simp_at hc
    rw [hcnt] at hc
    simp only [Env.ofMachine_regs, Bool.not_eq_true', BitVec.ult, Bool.not_eq_false] at hc
    have hc := of_decide_eq_true hc
    rw [toBitVec_toUInt64' hsize64, hrcx1] at hc
    exact hc
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 (Env.wf_nil _) nofun hpc2
    (match_nil _) fun st3 hm3 hpc3 => ?_
  obtain ⟨hk3, hmem3, hsp3, hdi3, hsi3, hcx3⟩ := after_eq run_b2 ▸ ok_b2
  simp only [PcOk] at hpc3
  have hrcx2 : st2.data.regs.get64 .rcx = m0.regs.get64 .rcx := hreg2 .rcx (by decide)
  have hrdx2 : st2.data.regs.get64 .rdx = m0.regs.get64 .rdx := hreg2 .rdx (by decide)
  simp only [condB2_eval (Env.ofMachine st2.data []) (i := (reg m0 .rcx).toNat) (n := a.len)
    (by rw [Env.ofMachine_regs, hrcx2]) (by rw [Env.ofMachine_regs, hrdx2]; exact hx2)
    (by omega), ↓reduceIte] at hpc3
  have hK3 : Kept m0 st3.data :=
    ⟨(hm3.dmem_eq (Env.wf_nil _) hmem3).trans hK2.dmem,
      hK2.saved.trans (Match.saved (match_nil _) hm3 (Env.wf_nil _) rfl hk3),
      (hm3.regs .rsp _ hsp3).trans hK2.rsp, (hm3.regs .rdi _ hdi3).trans hK2.rdi,
      (hm3.regs .rsi _ hsi3).trans hK2.rsi⟩
  -- `b4`: element `i` copied.
  have hcx : (reg st3.data .rcx).toNat = 2 * (reg m0 .rcx).toNat := by
    rw [show reg st3.data .rcx = _ from hm3.regs .rcx _ hcx3]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [BitVec.toNat_add, hrcx2]
    omega
  set o := reg m0 .rdi
  set e := a.word (1 + 2 * (reg m0 .rcx).toNat)
  have he : e.toNat = a.words.toNat + 8 * (1 + 2 * (reg m0 .rcx).toNat) := toNat_off (by omega)
  have hon' : o.toNat + 24 ≤ 2 ^ 64 := hon
  have hap' : o.toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ o.toNat := hap
  have hwf4 : (Env.ofMachine st3.data [(o, 24), (e, 16)]).WF := by
    refine Env.wf_of ⟨⟨fun j hj ↦ ?_, hon'⟩, ⟨fun j hj ↦ ?_, ?_⟩, trivial⟩ ?_
    · show (st3.data.dmem.get? (o + BitVec.ofNat 64 j)).isSome
      rw [hK3.dmem]; exact hom j hj
    · show (st3.data.dmem.get? (e + BitVec.ofNat 64 j)).isSome
      rw [hK3.dmem, off_add]; exact hrm _ (by omega)
    · show e.toNat + 16 ≤ 2 ^ 64
      omega
    · refine List.pairwise_pair.mpr ?_
      show o.toNat + 24 ≤ e.toNat ∨ e.toNat + 16 ≤ o.toNat
      omega
  have hm4 : Match (Env.ofMachine st3.data [(o, 24), (e, 16)]) someS st3.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨known_ptr rfl hK3.rdi, trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    show _ = (Env.ofMachine st3.data [(o, 24), (e, 16)]).base 1 + BitVec.ofInt 64 (-8)
    rw [show (Env.ofMachine st3.data [(o, 24), (e, 16)]).base 1 = e from rfl]
    simp only [elemAddr, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    apply BitVec.eq_of_toNat_eq
    have hrsi3 : st3.data.regs.get64 .rsi = a.words := hK3.rsi.trans hx1
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, hcx, he, hrsi3]
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
    omega
  refine exec_at (infix_of ((infix_take b4 7).trans b4_in_code (by simp [b4])) (by simp [b4]) hp)
    run_b4 hwf4 nofun (hpc3.trans (hp.label NativeRustcVmX64.Vm.DecodedStreamElement.label_6_at)) hm4 fun st4 hm4' hpc4 => ?_
  obtain ⟨hw0, hw1, hw2, hws, hkeeps, hsp4⟩ := after_eq run_b4 ▸ some_b4
  have hsame : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem (NativeRustcVm.InRange o 24) :=
    sameOutside_region hwf4 hm4' rfl hws
  have hel := hdec.stream _ hi
  rw [ewAt_iff] at hel
  have hl0 : (Env.ofMachine st3.data [(o, 24), (e, 16)]).load 1 0 8 =
      stream[(reg m0 .rcx).toNat].c0.toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [hK3.dmem, off_zero]; exact hel.1)
  have hl1 : (Env.ofMachine st3.data [(o, 24), (e, 16)]).load 1 8 8 =
      stream[(reg m0 .rcx).toNat].c1.toBitVec :=
    load_ofMachine (o := 8) rfl (by rw [hK3.dmem]; exact hel.2)
  refine finish_ret hp ((infix_drop b4 7).trans b4_in_code (by simp [b4])) (by simp [b4])
    (hpc4.trans (congrArg Host.addrOf (by simp [b4, Nat.add_assoc]))) run_b4r
    (after_eq run_b4r ▸ ⟨ok_ret.2.2.1, ok_ret.2.2.2⟩) hst
    (hK3.saved.trans (Match.saved hm4 hm4' hwf4 rfl hkeeps))
    ((hm4'.regs .rsp _ hsp4).trans hK3.rsp) hon hapS
    (fun q hq ↦ by rw [hsame q hq, hK3.dmem]) ?_ rfl
  rw [Array.getElem?_eq_getElem hi]
  refine ⟨?_, ewAt_iff.mpr ⟨?_, ?_⟩⟩
  · have := wordAt_write hm4' (r := 0) (o := 0) rfl (by omega) fun j hj ↦ by
      rw [Nat.zero_add]; exact hw0 j hj
    rwa [off_zero] at this
  · have := wordAt_write hm4' (r := 0) (o := 8) rfl (by omega) hw1
    rwa [Sym.eval, hl0] at this
  · have := wordAt_write hm4' (r := 0) (o := 16) rfl (by omega) hw2
    rw [Sym.eval, hl1] at this
    rwa [off_off]

end

end NativeRustcVmX64.Transcript.StreamElement
