module

public import NativeRustcVmX64.Wire.RdRows.Basic
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names

/-!
# `rd_rows`' calls of `Reader::words` (x86-64)

The values BL takes (`merge_val`), the locals loaded (`Loc.load_lw`, `Loc.load_rd`), a byte of a
window of the leaves as numbers (`inW_iff`), and the call (`words_call`): `Reader::words`' contract
from the places, the frame kept, what it changes (the row's window, the cursor, its own stack below
the frame) and its result.
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv Frame.call Frame.of_block frame_noWrap
  stackOk_callee stackBelow_callee after MidOk)
open NativeRustcVm.Transcript (off off_zero off_add)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64}

/-- BL after `movb $v, %bl`. -/
theorem merge_val (x : BitVec 64) {v : Nat} (hv : v < 256) :
    (BinOp.apply .merge .W8 x (BitVec.ofNat 64 v)).toNat % 256 = v := by
  have h := congrArg BitVec.toNat
    (NativeRustcVmX64.Transcript.low8_replaceLow x (low .W8 (BitVec.ofNat 64 v)))
  simp only [low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Width.bits, Nat.reducePow] at h
  simp only [BinOp.apply, low, Width.bits]
  omega

theorem Loc.load_lw [Labels] {m : MachineData} (h : Loc m0 m.dmem) {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 m 80 rest vars ret).load 0 8 8 = reg m0 .rdx :=
  Wire.load_word h.lw

theorem Loc.load_rd [Labels] {m : MachineData} (h : Loc m0 m.dmem) {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 m 80 rest vars ret).load 0 16 8 = rdr m0 :=
  Wire.load_word h.rd

/-- A window of the leaves, as numbers. -/
theorem inW_iff {L : Nat} (g : Geo m0 bp L) {o sz : Nat} (hin : o + sz ≤ 512 * nr m0)
    (hsz : 0 < sz) {q : BitVec 64} :
    NativeRustcVm.InRange (off (lv m0) o) sz q ↔
      (lv m0).toNat + o ≤ q.toNat ∧ q.toNat < (lv m0).toNat + o + sz := by
  have := g.lvNw
  have ht : (off (lv m0) o).toNat = (lv m0).toNat + o :=
    NativeRustcVm.Transcript.toNat_off (by omega)
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega), ht]

/-- **A call of `Reader::words`** for `nw` words into the leaves at `o`, from the frame with RSP at
its base: back at the return address in the frame (RSP at offset `8`), the callee-saved registers
kept, the window, the cursor and the callee's stack changed at most, the read's outcome. -/
theorem words_call [Host] (hw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost)
    {B : List UInt8} {ci : Nat} (g : Geo m0 bp B.length) {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (hf : Frame m0 80 slots 0 st.data)
    (hR : ReaderAt st.data.dmem (rdr m0) bp B ci) (hrdi : reg st.data .rdi = rdr m0)
    {o nw : Nat} (hin : o + 8 * nw ≤ 512 * nr m0) (hrsi : reg st.data .rsi = off (lv m0) o)
    (hrdx : (reg st.data .rdx).toNat = nw)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, Frame m0 80 slots 8 m2 →
      (∀ x, calleeSaved x = true → reg m2 x = reg st.data x) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        ((lv m0).toNat + o ≤ q.toNat ∧ q.toNat < (lv m0).toNat + o + 8 * nw) ∨
        ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
        ((rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 80)) →
      (match rdWords B nw ci with
        | some (ws, c') => boolRet m2 = 1 ∧ WordsAt m2.dmem (off (lv m0) o) (ws.map K.lane) ∧
            ReaderAt m2.dmem (rdr m0) bp B c'
        | none => boolRet m2 = 0) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have h0 := g.s0
  have hlv := g.lvNw
  have hS := g.lvS
  have hrS := g.rS
  have hrW := g.rW
  have hrN := g.rNw
  have hgS := g.g.sb
  have hrb := g.g.rb
  have haB := g.aB
  have hbN := g.g.bpNw
  unfold NativeRustcVm.Apart at hgS hrb haB
  unfold NativeRustcVm.NoWrap at hbN
  rw [h0.2.2] at hgS
  have hsp : rspOf st.data = stackBelow m0 80 := by rw [hf.sp, off_zero]
  have hsb48 : stackBelow st.data 48 = stackBelow m0 128 :=
    stackBelow_callee hsp (by omega)
  have hat : (off (lv m0) o).toNat = ((lv m0).toNat + o) % 2 ^ 64 := by
    rw [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hwin : ∀ q, NativeRustcVm.InRange (off (lv m0) o) (8 * nw) q →
      (lv m0).toNat + o ≤ q.toNat ∧ q.toNat < (lv m0).toNat + o + 8 * nw := by
    intro q hq
    rcases Nat.eq_zero_or_pos nw with h | h
    · subst h
      unfold NativeRustcVm.InRange at hq
      omega
    · exact (inW_iff g hin (by omega)).mp hq
  have hP : ReaderWordsPre st.data := by
    refine ⟨stackOk_callee g.g.st hf.kept hsp (by unfold readerWordsStack readerLeStack; omega),
      ⟨fun t ht ↦ ?_, ?_⟩, bp, B, ci, by rw [hrdi]; exact hR, ?_⟩
    · change t < 8 * (reg st.data .rdx).toNat at ht
      rw [hrdx] at ht
      rw [hrsi, off_add]
      exact hf.kept _ (g.lvMap _ (by omega))
    · show (reg st.data .rsi).toNat + 8 * (reg st.data .rdx).toNat ≤ 2 ^ 64
      rw [hrsi, hrdx, hat]
      omega
    · simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, stackR, hsb48, readerWordsStack, readerLeStack,
        List.Pairwise.nil, and_true, hrdi, hrsi, hrdx]
      unfold NativeRustcVm.Apart
      rw [hat, h0.2.2]
      refine ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, fun _ h ↦ h.elim⟩
  refine Eventually.bind (Spec.apply hw hpc.1 hP) fun st' ⟨hpc', hrsp', hres, hs, hsv⟩ ↦ ?_
  rw [hpc.2] at hpc'
  rw [hrdi, hrsi, hrdx] at hres hs
  have hfrS := NativeRustcVmX64.Transcript.frame_noWrap g.g.st (F := 80) (by decide)
  have hsb := g.sb_toNat
  have hRq : ∀ q, NativeRustcVm.InAny [⟨off (lv m0) o, 8 * nw⟩, curRegion (rdr m0),
      frameR st.data readerWordsStack] q →
      ((lv m0).toNat + o ≤ q.toNat ∧ q.toNat < (lv m0).toNat + o + 8 * nw) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
      ((rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 80) := by
    intro q ⟨r, hr, hq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (hwin q hq)
    · exact .inr (.inl ((g.cur_iff).mp hq))
    · refine .inr (.inr ?_)
      have hq' : NativeRustcVm.InRange (stackBelow m0 128) 48 q := by
        have : frameR st.data readerWordsStack = ⟨stackBelow m0 128, 48⟩ := by
          rw [frameR, show readerWordsStack = 48 by decide, hsb48]
        rw [this] at hq
        exact hq
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [h0.2.2]; omega),
        h0.2.2] at hq'
      omega
  have hf' : Frame m0 80 slots 8 st'.data :=
    Frame.call hf hsv hrsp' hs (fun q hq hin ↦ by
      rw [NativeRustcVm.inRange_iff hfrS, hsb] at hin
      rcases hRq q hq with h | h | h <;> omega) hfrS slots_le
  obtain ⟨m2, pc2⟩ := st'
  simp only at hpc'
  subst hpc'
  refine cont m2 hf' (fun x hx ↦ hsv.1 x hx) (fun q hq ↦ hs q fun h ↦ hq (hRq q h)) ?_
  exact hres bp B ci hR

/-- The low byte test `testb %al, %al; je`. -/
theorem al_zero (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0) =
      decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low, ext, BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Width.bits]
  omega

/-- **A block ending in the call of `Reader::words`** (at `j`, from `frS`: RDI the reader loaded
from the frame, RSI `vsi` the address of `nw` words of the leaves at `o`, RDX `vdx` their count):
back after the call in the frame, the callee-saved registers the block's, memory changed at most in
the window, the cursor and the stack below the locals, the read's outcome. -/
theorem call_block [Host] {k : Nat} (hp : Placed code k)
    (hw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost)
    {B : List UInt8} {ci : Nat} (g : Geo m0 bp B.length) {bj : List Directive} {j : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ [])
    (hrun : exec bj frS = some (after bj frS,
      .call NativeRustcVmX64.Vm.ReaderWords.entryLabel))
    (hok : MidOk 80 0 slots (after bj frS) = true)
    (hlow : ∀ w ∈ (after bj frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8)
    (hrdi : (after bj frS).reg .rdi = some (.load 0 16 8))
    {vsi vdx : Sym} (hsi : (after bj frS).reg .rsi = some vsi)
    (hdx : (after bj frS).reg .rdx = some vdx)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 80 slots 8 st.data)
    (hloc : Loc m0 st.data.dmem) (hR : ReaderAt st.data.dmem (rdr m0) bp B ci)
    {o nw : Nat} (hin : o + 8 * nw ≤ 512 * nr m0)
    (hvsi : vsi.eval (frameEnv m0 st.data 80 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec) =
      off (lv m0) o)
    (hvdx : (vdx.eval (frameEnv m0 st.data 80 [] (fun _ ↦ 0)
      (Host.addrOf (k + j + bj.length)).toBitVec)).toNat = nw)
    {R : MachineState → Prop}
    (cont : ∀ m2, Frame m0 80 slots 8 m2 →
      (∀ r v, (after bj frS).reg r = some v → calleeSaved r = true →
        reg m2 r = v.eval (frameEnv m0 st.data 80 [] (fun _ ↦ 0)
          (Host.addrOf (k + j + bj.length)).toBitVec)) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        ((lv m0).toNat + o ≤ q.toNat ∧ q.toNat < (lv m0).toNat + o + 8 * nw) ∨
        ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
        ((rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 72)) →
      (match rdWords B nw ci with
        | some (ws, c') => boolRet m2 = 1 ∧ WordsAt m2.dmem (off (lv m0) o) (ws.map K.lane) ∧
            ReaderAt m2.dmem (rdr m0) bp B c'
        | none => boolRet m2 = 0) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + j + bj.length)⟩) :
    Eventually (step1 Host.exe) R st := by
  have h0 := g.s0
  have hsb := g.sb_toNat
  let ret := (Host.addrOf (k + j + bj.length)).toBitVec
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := ret)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := ret)
  refine exec_at (Wire.infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : Frame m0 80 slots 0 st1.data := Frame.of_block hf hwf hm1 hok slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 80) 8) :=
    NativeRustcVmX64.Transcript.sameOutside_low hwf hm1 (r := 0) rfl (by decide) hlow
  have hsbR : ∀ q, NativeRustcVm.InRange (stackBelow m0 80) 8 q →
      (rspOf m0).toNat - 80 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 72 := fun q hq ↦ by
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega), hsb] at hq
    omega
  have hR1 : ReaderAt st1.data.dmem (rdr m0) bp B ci :=
    g.reader hR hs1 fun q hq ↦ .inl (by
      have := hsbR q hq
      rw [g.Stk_iff]; omega)
  have hrdi1 : reg st1.data .rdi = rdr m0 := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hrdi, eval_load]
    exact hloc.load_rd
  have hrsi1 : reg st1.data .rsi = off (lv m0) o := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hsi]
    exact hvsi
  have hrdx1 : (reg st1.data .rdx).toNat = nw := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx]
    exact hvdx
  simp only [PcOk] at hpc1
  refine words_call hw g hf1 hR1 hrdi1 hin hrsi1 hrdx1 hpc1
    fun m2 hf2 hcs2 hs2 hres2 ↦ cont m2 hf2 (fun r v hr hcs ↦ ?_) (fun q hq ↦ ?_) hres2
  · rw [hcs2 r hcs]
    exact hm1.regs r v hr
  · rw [← hs1 q fun h ↦ hq (.inr (.inr (by have := hsbR q h; omega)))]
    refine hs2 q fun h ↦ hq ?_
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (by omega))

end

end NativeRustcVmX64.Wire.RdRows
