module

public import NativeRustcVmX64.Wire.ReaderWords.Loop
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names

/-!
# `Reader::words` meets its contract (x86-64)

`readerWords_spec`: the prologue and the bound check (`b0`: the cursor plus `8 n` carries;
`b1`: it passes the length): `None`, the epilogue (`b9`, `fin`) with AL `0`; else no word (`b2`):
`Some` with AL `1`; else the loop (`b3`, then `step` per word, `LInv`): each word read by
`Reader::le`, which cannot fail within the bound, and stored; then `Some` (`b7`, `b9`).
-/

namespace NativeRustcVmX64.Wire.ReaderWords

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ReaderWords
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap match_rsp
  Frame.of_prologue Frame.of_block sameOutside_low after_eq known_ptr inRange_mono)
open NativeRustcVm.Transcript (Mapped.keeps)
open NativeRustcVmX64.Wire.ReaderLe (carry_apply above_apply toNat_toUInt64)
open LeanVM.Parameters

public section

theorem eightN_eval [Labels] (env : Env) :
    (eightN.eval env).toNat = 8 * (env.regs .rdx).toNat % 2 ^ 64 := by
  simp only [eightN, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

variable [Host] {k : Nat}

/-- **`Reader::words` meets its contract.** -/
theorem readerWords_spec (hp : Placed code k)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) :
    Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost := by
  intro m0 ⟨hst', hout, bp, B, c, hR, hd⟩
  have g := geo_of hst' hout hR hd
  have hst : StackOk m0 48 := hst'
  have hL := hR.len_lt
  have hc : c < 2 ^ 64 := by have := hR.c_le; omega
  have h8n : 8 * (reg m0 .rdx).toNat < 2 ^ 64 := by
    have := g.oS; have := g.onw; have := hst.2.1
    unfold NativeRustcVm.Apart at *; unfold NativeRustcVm.NoWrap at *
    have := NativeRustcVmX64.stackBelow_toNat (m := m0) (n := 48) hst.1
    omega
  rw [show Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderWords.b0Offset) from hp.label NativeRustcVmX64.Vm.ReaderWords.entry_at]
  -- `b0`: the prologue, the carry.
  have hrS := g.g.sr
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 48) (rest := [(reg m0 .rdi, 24)]) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst (by decide), frame_noWrap hst (by decide)⟩
    (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact hR.ok)
    (List.pairwise_pair.mpr (by unfold NativeRustcVm.Apart at hrS ⊢; dsimp only; omega))
  have hm0 : Match (frameEnv m0 m0 48 [(reg m0 .rdi, 24)]) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hws1, hrax, hr15, hrcx, hrdi, hrdx, hrsi⟩ := ok_b0
  have hf1 : Frame m0 48 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 48) 48) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hc1 : Chg m0 st1.data := fun q hq ↦ hs1 q fun h ↦ hq (.inl h)
  have hcur : (frameEnv m0 m0 48 [(reg m0 .rdi, 24)]).load 1 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [show (frameEnv m0 m0 48 [(reg m0 .rdi, 24)]).base 1 = (reg m0 .rdi) from rfl]; exact hR.cur)
  have h8 : (eightN.eval (frameEnv m0 m0 48 [(reg m0 .rdi, 24)])).toNat = 8 * (reg m0 .rdx).toNat := by
    rw [eightN_eval]
    exact Nat.mod_eq_of_lt h8n
  have hax1 : reg st1.data .rax = 0 := hm1.regs .rax _ hrax
  simp only [PcOk, SBool.eval, carry_apply, Sym.eval, h8, hcur, toNat_toUInt64 hc,
    hp.label NativeRustcVmX64.Vm.ReaderWords.label_8_at, show k + NativeRustcVmX64.Vm.ReaderWords.b0Offset + b0.length = k + NativeRustcVmX64.Vm.ReaderWords.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderWords.b0_next]] at hpc1
  by_cases hcy : 2 ^ 64 ≤ 8 * (reg m0 .rdx).toNat + c
  · rw [decide_eq_true hcy] at hpc1
    simp only [↓reduceIte] at hpc1
    refine fin hp hst hR hpc1 hf1 ?_ hc1
    simp only [rdWords, show ¬c + 8 * (reg m0 .rdx).toNat ≤ B.length by omega, ↓reduceIte]
    unfold boolRet; rw [hax1]; rfl
  rw [decide_eq_false hcy] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b1`: the length.
  have hrdi1 : reg st1.data .rdi = (reg m0 .rdi) :=
    (hm1.regs .rdi _ hrdi).trans (NativeRustcVmX64.Transcript.eval_ptr rfl)
  have hrcx1 : (reg st1.data .rcx).toNat = 8 * (reg m0 .rdx).toNat + c := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, h8, hcur,
      toNat_toUInt64 hc]
    omega
  have hwf1 := frame_wf (m0 := m0) (d := st1.data) (F := 48) (rest := [(reg m0 .rdi, 24)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf1.kept, frame_noWrap hst (by decide)⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨Mapped.keeps hR.ok.1 hf1.kept, hR.ok.2⟩)
    (List.pairwise_pair.mpr (by unfold NativeRustcVm.Apart at hrS ⊢; dsimp only; omega))
  have hR1 : ReaderAt st1.data.dmem (reg m0 .rdi) bp B c := g.reader hR fun q hq ↦ hs1 q fun h ↦ hq (.inl h)
  have hm1' : Match (frameEnv m0 st1.data 48 [(reg m0 .rdi, 24)]) chkS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf1.rsp_eval, known_ptr rfl hrdi1, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf1 nofun hpc1 hm1'
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hrax2, hr14_2, hr15_2, hrdx2, hrsi2⟩ := ok_b1
  have hf2 : Frame m0 48 slots 8 st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
  have hlen1 : (frameEnv m0 st1.data 48 [(reg m0 .rdi, 24)]).load 1 8 8 = B.length.toUInt64.toBitVec :=
    load_word (by rw [show (frameEnv m0 st1.data 48 [(reg m0 .rdi, 24)]).base 1 = (reg m0 .rdi) from rfl]; exact hR1.len)
  simp only [PcOk, SBool.eval, Sym.eval, above_apply, hlen1, toNat_toUInt64 hL,
    hp.label NativeRustcVmX64.Vm.ReaderWords.label_8_at, show k + NativeRustcVmX64.Vm.ReaderWords.b1Offset + b1.length = k + NativeRustcVmX64.Vm.ReaderWords.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderWords.b1_next]] at hpc2
  change st2.pc = if decide (B.length < (reg st1.data .rcx).toNat) = true then _ else _ at hpc2
  rw [hrcx1] at hpc2
  have hax2 : reg st2.data .rax = 0 := (hm2.regs .rax _ hrax2).trans hax1
  have hc2 : Chg m0 st2.data := fun q hq ↦ by rw [hd2]; exact hc1 q hq
  by_cases hab : B.length < 8 * (reg m0 .rdx).toNat + c
  · rw [decide_eq_true hab] at hpc2
    simp only [↓reduceIte] at hpc2
    refine fin hp hst hR hpc2 hf2 ?_ hc2
    simp only [rdWords, show ¬c + 8 * (reg m0 .rdx).toNat ≤ B.length by omega, ↓reduceIte]
    unfold boolRet; rw [hax2]; rfl
  rw [decide_eq_false hab] at hpc2
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
  have hfit : c + 8 * (reg m0 .rdx).toNat ≤ B.length := by omega
  have hR2 : ReaderAt st2.data.dmem (reg m0 .rdi) bp B c := by rw [hd2]; exact hR1
  have hr14 : reg st2.data .r14 = (reg m0 .rdi) :=
    (hm2.regs .r14 _ hr14_2).trans (NativeRustcVmX64.Transcript.eval_ptr rfl)
  have hr15' : reg st2.data .r15 = BitVec.ofNat 64 (8 * (reg m0 .rdx).toNat) := by
    rw [show reg st2.data .r15 = reg st1.data .r15 from hm2.regs .r15 _ hr15_2,
      show reg st1.data .r15 = _ from hm1.regs .r15 _ hr15]
    apply BitVec.eq_of_toNat_eq
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h8n]
  have hrdx2' : reg st2.data .rdx = reg m0 .rdx :=
    (hm2.regs .rdx _ hrdx2).trans (hm1.regs .rdx _ hrdx)
  have hrsi2' : reg st2.data .rsi = reg m0 .rsi :=
    (hm2.regs .rsi _ hrsi2).trans (hm1.regs .rsi _ hrsi)
  -- `b2`: no word.
  refine fr_step hp hst (j := NativeRustcVmX64.Vm.ReaderWords.b2Offset) b2_in_code (by simp [b2]) exit_b2 nofun ok_b2.1 hpc2 hf2
    fun st3 hf3 hd3 hm3 hpc3 ↦ ?_
  have hk3 : ∀ x ∈ [Reg64.rsi, .rdx, .r14, .r15], reg st3.data x = reg st2.data x :=
    fun x hx ↦ hm3.regs x _ (ok_b2.2.2 x hx)
  have hb3 : boolRet st3.data = 1 := by
    unfold boolRet
    rw [show reg st3.data .rax = _ from hm3.regs .rax _ ok_b2.2.1]
    exact merge_one _
  have hc3 : Chg m0 st3.data := fun q hq ↦ by rw [hd3]; exact hc2 q hq
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hp.label NativeRustcVmX64.Vm.ReaderWords.label_8_at,
    show k + NativeRustcVmX64.Vm.ReaderWords.b2Offset + b2.length = k + NativeRustcVmX64.Vm.ReaderWords.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderWords.b2_next]] at hpc3
  change st3.pc = if (BinOp.apply .and .W64 (reg st2.data .rdx) (reg st2.data .rdx) ==
    BitVec.ofNat 64 0) = true then _ else _ at hpc3
  have hand : BinOp.apply .and .W64 (reg st2.data .rdx) (reg st2.data .rdx) = reg m0 .rdx := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self, hrdx2']
  rw [hand] at hpc3
  by_cases hn0 : (reg m0 .rdx).toNat = 0
  · have he : (reg m0 .rdx == BitVec.ofNat 64 0) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hn0]; rfl
    rw [he] at hpc3
    simp only [↓reduceIte] at hpc3
    refine fin hp hst hR hpc3 hf3 ?_ hc3
    simp only [rdWords, hn0, Nat.mul_zero, Nat.add_zero, List.range_zero, List.map_nil,
      hR.c_le, ↓reduceIte]
    exact ⟨hb3, NativeRustcVm.wordsAt_nil _ _, by rw [hd3]; simpa using hR2⟩
  have he : (reg m0 .rdx == BitVec.ofNat 64 0) = false := by
    rw [beq_eq_false_iff_ne]; intro h; apply hn0; rw [h]; rfl
  rw [he] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `b3`: the loop's set-up.
  refine fr_step hp hst (j := NativeRustcVmX64.Vm.ReaderWords.b3Offset) b3_in_code (by simp [b3]) exit_b3 nofun ok_b3.1 hpc3 hf3
    fun st4 hf4 hd4 hm4 hpc4 ↦ ?_
  obtain ⟨-, hrbx4, hr12_4, hk4⟩ := ok_b3
  simp only [PcOk, show k + NativeRustcVmX64.Vm.ReaderWords.b3Offset + b3.length = k + NativeRustcVmX64.Vm.ReaderWords.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderWords.b3_next]] at hpc4
  have hI0 : LInv (k := k) m0 bp B c 0 st4 := by
    refine ⟨hpc4, hf4, by omega, hfit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hm4.regs .r14 _ (hk4 .r14 (by simp))).trans ((hk3 .r14 (by simp)).trans hr14)
    · exact (hm4.regs .rbx _ hrbx4).trans ((hk3 .rsi (by simp)).trans hrsi2')
    · rw [show reg st4.data .r12 = _ from hm4.regs .r12 _ hr12_4]; rfl
    · exact (hm4.regs .r15 _ (hk4 .r15 (by simp))).trans ((hk3 .r15 (by simp)).trans hr15')
    · rw [hd4, hd3]; simpa using hR2
    · exact NativeRustcVm.wordsAt_nil _ _
    · exact fun q hq ↦ by rw [hd4]; exact hc3 q hq
  -- The loop.
  refine Sym.loop (I := fun j st ↦ ∃ i, j = (reg m0 .rdx).toNat - i ∧ LInv (k := k) m0 bp B c i st)
    (fun j st ⟨i, hj, hI⟩ ↦ Eventually.bind (step hp hle g hI) fun st' h ↦ ?_) ⟨0, rfl, hI0⟩
  rcases h with hD | hI'
  · -- `b7`, `b9`: `Some`.
    refine Eventually.mono (fr_step hp hst (j := NativeRustcVmX64.Vm.ReaderWords.b7Offset) b7_in_code (by simp [b7]) exit_b7 nofun
      ok_b7.1 hD.pc hD.fr fun st5 hf5 hd5 hm5 hpc5 ↦ ?_) fun _ h ↦ .inl h
    simp only [PcOk, hp.label NativeRustcVmX64.Vm.ReaderWords.label_8_at] at hpc5
    refine fin hp hst hR hpc5 hf5 ?_ fun q hq ↦ by rw [hd5]; exact hD.chg q hq
    simp only [rdWords, hfit, ↓reduceIte]
    refine ⟨?_, ?_, by rw [hd5]; exact hD.rd⟩
    · unfold boolRet
      rw [show reg st5.data .rax = _ from hm5.regs .rax _ ok_b7.2]
      exact merge_one _
    · rw [hd5, List.map_map]
      exact hD.ws
  · exact .done _ (.inr ⟨(reg m0 .rdx).toNat - (i + 1), by have := hI.lt; omega, i + 1, rfl, hI'⟩)

end

end NativeRustcVmX64.Wire.ReaderWords
