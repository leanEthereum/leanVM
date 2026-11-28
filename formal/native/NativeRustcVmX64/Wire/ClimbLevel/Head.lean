module

public import NativeRustcVmX64.Wire.ClimbLevel.State

/-!
# `climb_level`'s loop head (x86-64)

A block writing the frame only (`fw_step`); node `i`'s set-up (`b4`): the scan from node `0`
(`head_step`); the next node's check (`b3`): the loop's head again, or `Some` (`b21`, the return):
`nxt_step`.
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap
  Frame.of_block after after_eq MidOk)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 ult64 toNat_add64)
open NativeRustcVmX64.Sumcheck (WordW wordAt_written writesIn_of_mid)

public section

theorem ofNat_add64 (a b : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a + b) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact (BitVec.ofNat_add a b).symm

theorem off_add64 (b : BitVec 64) (o i : Nat) :
    BinOp.apply .add .W64 (off b o) (BitVec.ofNat 64 i) = off b (o + i) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact off_add b o i

theorem lit_add_off64 (b : BitVec 64) (o a : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 a) (off b o) = off b (o + a) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.add_comm]
  exact off_add b o a

theorem toNat_off_mod (b : BitVec 64) {x : Nat} (hx : x < 2 ^ 64) :
    (off b x).toNat = (b.toNat + x) % 2 ^ 64 := by
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

variable [Labels]

/-- Two addresses of the nodes are equal exactly when their offsets are. -/
theorem Geo.nd_eq (g : Geo m0 bp B.length) {x y : Nat} (hx : x ≤ 40 * cnt m0)
    (hy : y ≤ 40 * cnt m0) : (off (nodes m0) x).toNat = (off (nodes m0) y).toNat ↔ x = y := by
  have := g.nN
  have := g.n256
  have := (nodes m0).isLt
  rw [toNat_off_mod _ (by omega), toNat_off_mod _ (by omega)]
  omega

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

variable [Host] {k : Nat}

/-- **A block from `frS`** (at `j`) writing the frame only, within offsets `lo` to `hi`: the frame
kept, memory changed only there. -/
theorem fw_step (hp : Placed code k) (g : Geo m0 bp B.length) {bj : List Directive}
    {j : Nat} (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Exit}
    (hrun : exec bj frS = some (after bj frS, x)) (hx : ∀ l, x = .call l → False)
    (hok : MidOk 208 8 slots (after bj frS) = true) {lo hi : Nat}
    (hfr : FrW lo hi (after bj frS) = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 208 slots 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Frame m0 208 slots 8 st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (fun q ↦
        sp m0 - 208 + lo ≤ q.toNat ∧ q.toNat < sp m0 - 208 + hi) →
      Match (frameEnv m0 st.data 208 []) (after bj frS) st'.data →
      PcOk (frameEnv m0 st.data 208 []) x (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := 0)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (Wire.infix_of hb hne hp) hrun hwf (fun l h ↦ (hx l h).elim) hpc hm
    fun st' hm' hpc' ↦ cont st' (Frame.of_block hf hwf hm' hok slots_le) ?_ hm' hpc'
  refine NativeRustcVm.SameOutside.mono (same_num hwf hm' (writesIn_of_mid hok) hfr)
    fun q hq ↦ ?_
  rw [g.fb_toNat] at hq
  rcases hq with hq | ⟨_, hx, _⟩
  · exact hq
  · cases hx

section
variable (hp : Placed code k) (g : Geo m0 bp B.length) (hl : ns.length = cnt m0)
include hp g hl

/-- **Node `i`'s set-up** (`b4`): the scan from node `0`. -/
theorem head_step {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hI : Head k m0 bp B c ns i sl ci st) :
    Eventually (step1 Host.exe) (Scan k m0 bp B c ns i sl ci 0) st := by
  have h0 := g.s0
  have hsp := sp_eq m0
  have hn := g.n256
  have hli := hI.lt
  obtain ⟨hmid, hfr, hw72, hw80, hrax, hrcx, hK⟩ := ok_b4
  refine fw_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b4Offset) b4_in_code (by simp [b4]) exit_b4 nofun hmid hfr hI.pc hI.fr
    fun st' hf' hs' hm' hpc' ↦ ?_
  have hk := regs_kept hK fun r v h ↦ hm'.regs r v h
  have hpar := par_le (ns := ns) i sl
  have hls : (sn sl).length = i := by
    rw [sn_length, sibsM_length B ns _ c hI.hs, take_length_of_le (by omega)]
  simp only [PcOk] at hpc'
  refine .done _ ⟨hpc'.trans (congrArg Host.addrOf rfl), hf', hI.hs,
    hI.mm.keep g hl hs' fun q hq ↦ by unfold Mov; omega, ⟨?_, ?_⟩, hli,
    (hk .rbp (by simp [loopRegs])).trans hI.rbp, (hk .r12 (by simp [loopRegs])).trans hI.r12,
    (hk .rbx (by simp [loopRegs])).trans hI.rbx, (hk .r14 (by simp [loopRegs])).trans hI.r14,
    (hk .r15 (by simp [loopRegs])).trans hI.r15, ?_, ?_, Nat.zero_le _,
    fun j' h _ _ ↦ absurd h (Nat.not_lt_zero _)⟩
  · exact wordAt_written hm' (r := 0) (o := 72) rfl (by decide) hw72 (by
      show BinOp.apply .add .W64 (reg st.data .r12) (BitVec.ofNat 64 1) = _
      rw [hI.r12, ofNat_add64])
  · exact wordAt_written hm' (r := 0) (o := 80) rfl (by decide) hw80 (by
      show BinOp.apply .add .W64 (reg st.data .rbp) (BitVec.ofNat 64 40) = _
      rw [hI.rbp, off_add64, show 40 * i + 40 = 40 * (i + 1) by omega])
  · refine (hm'.regs .rcx _ hrcx).trans ?_
    rw [eval_load, Wire.load_word hI.mm.loc.n40, Nat.sub_zero]
  · rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax, eval_load,
      Wire.load_word hI.mm.loc.bm]
    show nodes m0 + BitVec.ofNat 64 18446744073709551576 + BitVec.ofNat 64 40 =
      nodes m0 + BitVec.ofNat 64 (40 * 0)
    rw [BitVec.add_assoc]
    rfl

/-- **The next node's check** (`b3`): the loop's head, or `Some` and the return. -/
theorem nxt_step (hR : ReaderAt m0.dmem (rdr m0) bp B c) (hns : NodesAt m0.dmem (nodes m0) ns)
    {j : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hI : Nxt k m0 bp B c ns j sl ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ Head k m0 bp B c ns j sl ci st') st := by
  have hle := hI.le
  obtain ⟨hok, hrbp, hr12, hK⟩ := ok_b3
  refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b3Offset) b3_in_code (by simp [b3]) exit_b3 nofun hok hI.pc hI.fr
    fun st' hf' hd' hr' hpc' ↦ ?_
  have hk := regs_kept hK hr'
  have hpc2 := pc_cond hpc' (P := j = cnt m0) (by
    show CmpOp.apply .eq .W64 ((frameEnv m0 st.data 208 []).load 0 80 8)
      ((frameEnv m0 st.data 208 []).load 0 48 8) = _
    rw [Wire.load_word hI.nx.ad, Wire.load_word hI.mm.loc.en, eq64]
    show decide ((off (nodes m0) (40 * j)).toNat = (off (nodes m0) (40 * cnt m0)).toNat) = _
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, g.nd_eq (by omega) (by omega)]
    omega)
  by_cases hj : j = cnt m0
  · rw [ite_t hj, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_8_at] at hpc2
    obtain ⟨hok21, hrax21, hK21⟩ := ok_b21
    refine Eventually.mono (fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b21Offset) b21_in_code (by simp [b21]) exit_b21 nofun
      hok21 hpc2 hf' fun s1 hf1 hd1 hr1 hpc1 ↦ ?_) fun _ h ↦ .inl h
    simp only [PcOk] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.ClimbLevel.label_11_at] at hpc1
    have hrbx := (regs_kept hK21 hr1 .rbx (by simp)).trans ((hk .rbx (by simp)).trans hI.rbx)
    have htake : ns.take j = ns := List.take_of_length_le (by omega)
    have hmm := hI.mm
    rw [htake] at hmm
    refine fin hp g hR hns hl hpc1 hf1 ?_ (by rw [hd1, hd']; exact hmm.chg)
    have hs' : sibsM B ns ns c = some (sl, ci) := by have := hI.hs; rwa [htake] at this
    unfold Res
    rw [hs']
    refine ⟨hr1 .rax _ hrax21, ?_, by rw [hd1, hd']; exact hmm.sb, ?_, by rw [hd1, hd']; exact hmm.rd⟩
    · rw [hrbx, htake, BitVec.toNat_ofNat]
      have := hmm.lp
      omega
    · rw [hd1, hd']; exact hmm.nx
  · rw [ite_f hj] at hpc2
    refine .done _ (.inr ⟨hpc2.trans (congrArg Host.addrOf rfl), hf', hI.hs,
      by rw [hd']; exact hI.mm, by omega, ?_, ?_, (hk .rbx (by simp)).trans hI.rbx,
      (hk .r14 (by simp)).trans hI.r14, (hk .r15 (by simp)).trans hI.r15⟩)
    · rw [hr' .rbp _ hrbp, eval_load, Wire.load_word hI.nx.ad]
    · rw [hr' .r12 _ hr12, eval_load, Wire.load_word hI.nx.ix]

end

end

end NativeRustcVmX64.Wire.ClimbLevel
