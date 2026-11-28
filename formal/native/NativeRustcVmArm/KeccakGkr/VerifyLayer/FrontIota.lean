module

public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontFw
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontBits
import Mathlib.Tactic.IntervalCases

/-!
# `verify_layer`'s front: the segment kernel and ι's bit weights

From `.LVerifyLayer_12` (`b15`, `k + NativeRustcVmArm.Vm.VerifyLayer.b15Offset`, the projection in X21, X22, `AtI`): the segment kernel
of the claim's point into the frame at `904` (`eq_kernel`), the first round constant's bit
weights (`b17`, `bitsA_loop`), the second's (`b19`, `bitsB_loop`), to `b21` (`k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset`, `AtJ`,
`seg_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

@[expose] public section

/-- **After the projection** (`b15`). -/
structure AtI [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (st : MachineData) : Prop where
  fb : FB m0 st
  fm : FM m0 a s1 p st.dmem
  x25 : st.regs.X25.toNat = c.mu.size
  acc : (⟨st.regs.X21, st.regs.X22⟩ : EW) = projectedOf c.mu p

/-- The segment kernel. -/
abbrev segK (m0 : MachineData) (c : KeccakClaimW) : Array EW :=
  eqKernel (c.point.extract (m0.regs.X1.toNat - 4) c.point.size)

/-- The first round constant. -/
abbrev wA (m0 : MachineData) : UInt64 := keccakRCW.getD (11 - m0.regs.X2.toNat) 0

/-- The second round constant. -/
abbrev wB (m0 : MachineData) : UInt64 := keccakRCW.getD (23 - m0.regs.X2.toNat) 0

/-- **After the segment kernel** (`b17`, `k + NativeRustcVmArm.Vm.VerifyLayer.b17Offset`): its first two entries in the frame at
`904`, the claim's point's address in X19. -/
structure AtS [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (st : MachineData) : Prop where
  fb : FB m0 st
  fm : FM m0 a s1 p st.dmem
  x25 : st.regs.X25.toNat = c.mu.size
  acc : (⟨st.regs.X21, st.regs.X22⟩ : EW) = projectedOf c.mu p
  x19 : st.regs.X19.toBitVec = cA m0 + BitVec.ofNat 64 288
  s0a : NativeRustcVm.WordAt st.dmem (loc m0 904) ((segK m0 c).getD 0 0).c0
  s0b : NativeRustcVm.WordAt st.dmem (loc m0 912) ((segK m0 c).getD 0 0).c1
  s1a : NativeRustcVm.WordAt st.dmem (loc m0 920) ((segK m0 c).getD 1 0).c0
  s1b : NativeRustcVm.WordAt st.dmem (loc m0 928) ((segK m0 c).getD 1 0).c1

/-- The frame's words of `projWords` kept past the segment kernel. -/
def pWords (m0 : MachineData) : List (Nat × UInt64) :=
  [(104, m0.regs.X0), (120, m0.regs.X4), (136, m0.regs.X3),
    (80, UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 16)),
    (88, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 51200)),
    (96, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107528)),
    (144, UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 24)), (128, m0.regs.X2)]

/-- The offsets of `pWords`. -/
def pOffs : List Nat := [104, 120, 136, 80, 88, 96, 144, 128]

/-- The frame's words from the segment kernel on: `pWords` and the claim's point. -/
def iWords (m0 : MachineData) : List (Nat × UInt64) :=
  (32, UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 288)) :: pWords m0

/-- The offsets of `iWords`. -/
def iOffs : List Nat := 32 :: pOffs

/-- **At the first check's sums** (`b21`, `k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset`): the projection, the segment kernel's two
entries, the two round constants' bit weights as four accumulators each. -/
structure AtJ [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (st : MachineData) : Prop where
  fb : FB m0 st
  fw : Bus.FrameWords st.dmem (base m0 2032) (iWords m0)
  prod : NativeRustcVm.EWsAt st.dmem (loc m0 152) p.toList
  psz : p.size = 47
  ts : TStateAt st.dmem (tA m0) a s1
  x25 : st.regs.X25.toNat = c.mu.size
  acc : (⟨st.regs.X21, st.regs.X22⟩ : EW) = projectedOf c.mu p
  s0a : NativeRustcVm.WordAt st.dmem (loc m0 112) ((segK m0 c).getD 0 0).c0
  s0b : NativeRustcVm.WordAt st.dmem (loc m0 72) ((segK m0 c).getD 0 0).c1
  s1a : NativeRustcVm.WordAt st.dmem (loc m0 64) ((segK m0 c).getD 1 0).c0
  s1b : NativeRustcVm.WordAt st.dmem (loc m0 56) ((segK m0 c).getD 1 0).c1
  x10 : st.regs.X10 = (bAcc c (wA m0) 1 16).c0 ^^^ (bAcc c (wA m0) 0 16).c0
  x11 : st.regs.X11 = (bAcc c (wA m0) 3 16).c0 ^^^ (bAcc c (wA m0) 2 16).c0
  w40 : NativeRustcVm.WordAt st.dmem (loc m0 40)
    ((bAcc c (wA m0) 3 16).c1 ^^^ (bAcc c (wA m0) 2 16).c1)
  w48 : NativeRustcVm.WordAt st.dmem (loc m0 48)
    ((bAcc c (wA m0) 1 16).c1 ^^^ (bAcc c (wA m0) 0 16).c1)
  b0 : (⟨st.regs.X5, st.regs.X17⟩ : EW) = bAcc c (wB m0) 0 16
  b1 : (⟨st.regs.X6, st.regs.X18⟩ : EW) = bAcc c (wB m0) 1 16
  b2 : (⟨st.regs.X7, st.regs.X2⟩ : EW) = bAcc c (wB m0) 2 16
  b3 : (⟨st.regs.X19, st.regs.X3⟩ : EW) = bAcc c (wB m0) 3 16

end

public section

theorem iWords_map (m0 : MachineData) : (iWords m0).map Prod.fst = iOffs := rfl

theorem pWords_map (m0 : MachineData) : (pWords m0).map Prod.fst = pOffs := rfl

theorem pWords_sub (m0 : MachineData) : ∀ q ∈ pWords m0, q ∈ projWords m0 := by
  intro q hq
  simp only [pWords, projWords, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  rcases hq with h | h | h | h | h | h | h | h <;> simp [h]

theorem fw_sub {d : DataMem} {b : BitVec 64} {ws ws' : List (Nat × UInt64)}
    (h : Bus.FrameWords d b ws) (hs : ∀ q ∈ ws', q ∈ ws) : Bus.FrameWords d b ws' :=
  fun q hq ↦ h q (hs q hq)

theorem fw_cons {d : DataMem} {b : BitVec 64} {o : Nat} {v : UInt64} {ws : List (Nat × UInt64)}
    (hw : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) v) (h : Bus.FrameWords d b ws) :
    Bus.FrameWords d b ((o, v) :: ws) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hw
  · exact h q hq

theorem iteF [Labels] {env : Env} {cnd : SBool} {A B : Sym} (h : cnd.eval env = false) :
    (Sym.ite cnd A B).eval env = B.eval env := by
  rw [ev_ite, h]; rfl

theorem memExt3 (v : BitVec 64) :
    (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 v).toNat = v.toNat * 8 % 2 ^ 64 := by
  simp only [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned, BitVec.toNat_ofInt,
    Int.shiftLeft_eq]
  omega

/-- A word of a table at an index scaled by `8`. -/
theorem ev_loadx [Labels] {m : MachineData} {rs : List (BitVec 64 × Nat)} {r : Nat} {i : Sym}
    {b : BitVec 64} {v : UInt64} {n : Nat} (hb : (Env.ofMachine m rs).base r = b)
    (hi : (i.eval (Env.ofMachine m rs)).toNat = n) (hn : n < 2 ^ 60)
    (h : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 (8 * n)) v) :
    (Sym.loadx r 0 (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 i) 8).eval (Env.ofMachine m rs) =
      v.toBitVec := by
  rw [Sym.eval, ev_un, memExt3, hi, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  exact Ring.load_word (by rw [hb]; exact h)

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The frame and the round constants as an environment's regions. -/
theorem wf_rc (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) :
    (Env.ofMachine m [(base m0 2032, 2032), (rcAddr, 192)]).WF := by
  have g := geo_of h
  have pg := pgeo_of h
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := pg.rn; have := pg.rs
  refine Env.wf_of ⟨⟨fun i hi ↦ hb.kept _ ((frame_mapped (pre_stack h) N_ge) i hi),
    base_noWrap (by omega)⟩, ⟨fun i hi ↦ hb.kept _ (pg.rm i hi), by unfold NoWrap; omega⟩,
    trivial⟩ ?_
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  simp only [List.mem_singleton, forall_eq]
  unfold Apart
  rw [hbN]
  omega

/-- **`FM` kept by a block** writing the frame from byte `904` on. -/
theorem FM.blk (h : VerifyLayerPre a s c m0) {s1 : TState} {p : Array EW} {m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 2032, 2032) :: rs)).WF)
    (hw : S.mem.all (fun w ↦ w.r == 0 && 904 ≤ w.off && w.off + w.n ≤ 2032) = true)
    (hf : FM m0 a s1 p m.dmem) : FM m0 a s1 p m'.dmem := by
  have hw' : ∀ w ∈ S.mem, w.r = 0 ∧ 904 ≤ w.off ∧ w.off + w.n ≤ 2032 := fun w hm' ↦ by
    have := List.all_eq_true.mp hw w hm'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hsame : ∀ o n, o + n ≤ 904 → NativeRustcVm.Layout.Same m.dmem m'.dmem (loc m0 o) n :=
    fun o n hon ↦ same_blk hm hwf (by omega) (List.all_eq_true.mpr fun w hm' ↦ by
      obtain ⟨h1, h2, -⟩ := hw' w hm'
      simp only [h1, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]
      omega)
  exact ⟨fun q hq ↦ same_word (hf.fw q hq)
      (hsame q.1 8 (by have := projWords_le m0 q hq; omega)),
    ewsAt_same hf.prod (hsame 152 752 (by omega)) (by rw [Array.length_toList, hf.psz]),
    hf.psz, ts_frame h hm hwf (fun w hm' ↦ ⟨(hw' w hm').1, (hw' w hm').2.2⟩) hf.ts⟩

/-- **`FM` kept by a call** writing its stack and `n` bytes of the frame from `o ≥ 904`. -/
theorem FM.call (h : VerifyLayerPre a s c m0) {s1 : TState} {p : Array EW} {m m' : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616) {o n : Nat}
    (ho : 904 ≤ o) (hon : o + n ≤ 2032)
    (hs : SameOutside m.dmem m'.dmem fun q ↦
      InRange (stackBelow m N') N' q ∨ InRange (loc m0 o) n q)
    (hk : Kept m.dmem m'.dmem) (hf : FM m0 a s1 p m.dmem) : FM m0 a s1 p m'.dmem := by
  have g := geo_of h
  have hR : ∀ q, (InRange (stackBelow m N') N' q ∨ InRange (loc m0 o) n q) →
      Bel m0 q ∨ InRange (loc m0 o) n q ∨ ¬InRange (base m0 2032) 2032 q :=
    fun q hq ↦ hq.elim (fun h' ↦ .inl (bel_of g hsp hle h')) (fun h' ↦ .inr (.inl h'))
  exact ⟨fw_call g hs hR hon (fun q hq ↦ by have := projWords_le m0 q hq; omega) hf.fw,
    ewsAt_same hf.prod (same_call g hs hR hon (o' := 152) (n' := 752) (by omega) (by omega))
      (by rw [Array.length_toList, hf.psz]),
    hf.psz, ts_call h hsp hle hs hk (fun q hq ↦ loc_ts h hon hq) hf.ts⟩

end

theorem extract_toList (xs : Array EW) (P : Nat) :
    (xs.extract P xs.size).toList = xs.toList.drop P := by simp

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The segment kernel**, from `b15` to `b17`. -/
theorem segA_run (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hek : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost) {p : Array EW}
    {s1 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b15Offset))
    (hi : AtI m0 a c p s1 st.data) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b17Offset) → AtS m0 a c p s1 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have g := geo_of h
  obtain ⟨hP, hP2⟩ := pre_seg h
  have hc0 := claimAt_fb h hi.fb
  have hL : c.point.size ≤ 30 := by have := hc0.2.2.1; rwa [Array.length_toList] at this
  have hLw := hc0.2.2.2.1
  rw [Array.length_toList] at hLw
  simp only [NativeRustcVm.KeccakGkr.off, NativeRustcVm.KeccakGkr.pointOff] at hLw
  obtain ⟨L, hL0⟩ : ∃ L, c.point.size = L := ⟨_, rfl⟩
  obtain ⟨P, hP0⟩ : ∃ P, m0.regs.X1.toNat - 4 = P := ⟨_, rfl⟩
  rw [hL0] at hL hLw
  rw [hL0, hP0] at hP hP2
  have hfw := hi.fm.fw
  have hw112 := FrameWords.get hfw (o := 112) (v := packW m0) (by simp [projWords])
  have hw136 := FrameWords.get hfw (o := 136) (v := m0.regs.X3) (by simp [projWords])
  have hX1 : m0.regs.X1.toNat < 2 ^ 64 := m0.regs.X1.toBitVec.isLt
  have hpk : (packW m0).toBitVec.toNat = P := by
    rw [show (packW m0).toBitVec = BitVec.ofNat 64 (m0.regs.X1.toNat - 4) from rfl,
      BitVec.toNat_ofNat, hP0]
    exact Nat.mod_eq_of_lt (by omega)
  have hLn : (L.toUInt64).toBitVec.toNat = L := by simp; omega
  -- `b15`: `eq_kernel`'s arguments.
  have hb0 := FB.body h hi.fb
  have hwf1 := wf_claim h hb0
  have hm1 := match_claimF h hb0 hw136
  refine exec_at (blk hp b15_in_code (by simp [b15])) e15 hwf1 hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  have hfb1 := fb_blkW h hi.fb hm1' hwf1 rfl (by decide)
  have hfm1 := FM.blk h hm1' hwf1 (by decide) hi.fm
  simp only [PcOk, NativeRustcVmArm.Vm.VerifyLayer.b15_length, NativeRustcVmArm.Vm.VerifyLayer.b15Length, show k + NativeRustcVmArm.Vm.VerifyLayer.b15Offset + 24 = k + NativeRustcVmArm.Vm.VerifyLayer.b16Offset by simpa only [NativeRustcVmArm.Vm.VerifyLayer.b15_length, NativeRustcVmArm.Vm.VerifyLayer.b15Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.VerifyLayer.b15_next] at hpc1
  have l280 := ld1 (m := st.data) (b0 := base m0 2032) (n0 := 2032) (n1 := 768) (o := 280) hLw
  have l112 := ld0 (m := st.data) (b1 := cA m0) (n0 := 2032) (n1 := 768) (o := 112) hw112
  have l136 := ld0 (m := st.data) (b1 := cA m0) (n0 := 2032) (n1 := 768) (o := 136) hw136
  have hc1 : (SBool.cmp .ult .W64 (.load 1 280 8) (.lit 31)).eval
      (Env.ofMachine st.data [(base m0 2032, 2032), (cA m0, 768)]) = true := by
    rw [sb_cmp, ult_apply, l280, hLn, litN 31]
    exact decide_eq_true (by omega)
  have hI : (Sym.ite (.cmp .ult .W64 (.load 1 280 8) (.lit 31)) (.load 1 280 8) (.lit 0)).eval
      (Env.ofMachine st.data [(base m0 2032, 2032), (cA m0, 768)]) = (L.toUInt64).toBitVec := by
    rw [iteT hc1, l280]
  have hc2 : (SBool.cmp .ult .W64
      (.ite (.cmp .ult .W64 (.load 1 280 8) (.lit 31)) (.load 1 280 8) (.lit 0))
      (.load 0 112 8)).eval
      (Env.ofMachine st.data [(base m0 2032, 2032), (cA m0, 768)]) = false := by
    rw [sb_cmp, ult_apply, hI, l112, hLn, hpk]
    exact decide_eq_false (by omega)
  have x1v : st1.data.regs.X1.toNat = L - P := by
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1'.regs .X1 _ rfl, iteF hc2, ev_bin, hI, l112, sub_toNat, hLn, hpk]
    omega
  have x0v : st1.data.regs.X0.toBitVec = cA m0 + BitVec.ofNat 64 (288 + 16 * P) := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1'.regs .X0 _ rfl, iteF hc2, addShl (iteT hc1) (by rw [l112, hpk]), ev_bin, l136,
      ev_lit, add_apply, NativeRustcVm.addr_add_add]
    rfl
  have x2v : st1.data.regs.X2.toBitVec = loc m0 904 := by
    show (st1.data.regs.getXReg .X2).toBitVec = _
    rw [hm1'.regs .X2 _ rfl, ev_ptr]
    rfl
  have x3v : st1.data.regs.X3.toNat = 4 := by
    show (st1.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm1'.regs .X3 _ rfl, litN 4]
  have x19v : (st1.data.regs.getXReg .X19).toBitVec = cA m0 + BitVec.ofNat 64 288 := by
    rw [hm1'.regs .X19 _ rfl, ev_bin, l136, ev_lit, add_apply]
  have k1 : Bus.KeepRegs [.X20, .X21, .X22, .X25] st.data st1.data :=
    Bus.KeepRegs.of_block hm1' rfl
  have hek2 : eqKernelStack ≤ 1616 := by have := le_ek; rw [stack_eq] at this; omega
  have := g.hc; have := g.hcs; have := g.hN; have := Geo.sp_lt m0
  -- `eq_kernel`: the segment kernel into the frame at `904`.
  refine local_call h le_ek (X := InRange (loc m0 904) 64) (o := 904) (n := 64) (by omega)
    (fun q hq ↦ .inr hq) hek hfb1 hpc1 ⟨hfb1.stackOk hS rfl le_ek, by rw [x1v]; omega,
      ⟨by rw [x0v, x1v]; exact readable_cl h hfb1 (by omega) (by omega),
        by rw [x0v, x1v]; exact offStack_cl h hfb1 (by omega) (by omega) hek2⟩,
      ⟨by rw [x2v, x3v]; exact readable_loc h hfb1 (by omega),
        by rw [x2v, x3v]; exact offStack_loc h hfb1 (by omega) hek2⟩,
      by
        rw [x0v, x1v, x2v, x3v]
        unfold Apart
        rw [g.ca (by omega), g.fa (by omega)]
        omega⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
        rw [x2v, x3v] at hq'; exact hq'.elim .inr .inl, hq.2.2⟩)
    fun m2 hfb2 hq2 hcs2 hs2 ↦ ?_
  obtain ⟨hk2, -, hsv⟩ := hq2
  have hpow : 2 ^ (L - P) ≤ 4 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hP2) (by decide : 2 ^ 2 ≤ 4)
  rw [x1v, x3v, ite_eq_left hpow] at hk2
  obtain ⟨x0r, -, hseg2⟩ := hk2
  -- the slice `eq_kernel` read: the point's coordinates past the pack's.
  have hc1' := claimAt_fb h hfb1
  have hp1 : NativeRustcVm.EWsAt st1.data.dmem (cA m0 + BitVec.ofNat 64 288) c.point.toList := by
    have := hc1'.2.2.2.2
    rwa [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.KeccakGkr.off,
      NativeRustcVm.KeccakGkr.pointOff, NativeRustcVm.addr_add_add] at this
  have hd := hp1.drop P
  rw [NativeRustcVm.addr_add_add] at hd
  have e := NativeRustcVm.ewsOf_of_ewsAt hd
  rw [List.length_drop, Array.length_toList, hL0] at e
  have hslice : slice st1.data st1.data.regs.X0 st1.data.regs.X1 =
      c.point.extract (m0.regs.X1.toNat - 4) c.point.size := by
    unfold slice
    rw [x0v, x1v, e, hP0]
    apply Array.ext'
    rw [List.toList_toArray, extract_toList]
  rw [x2v, hslice] at hseg2
  have hseg3 : NativeRustcVm.EWsAt m2.dmem (loc m0 904) (segK m0 c).toList := hseg2
  have hsz : 2 ≤ (segK m0 c).toList.length := by
    show 2 ≤ (eqKernel (c.point.extract (m0.regs.X1.toNat - 4) c.point.size)).toList.length
    rw [Array.length_toList, NativeVm.Math.Keccak.eqKernel_size, Array.size_extract, Nat.min_self,
      hL0, hP0]
    exact Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
  have w0 := ew_words hseg3 (i := 0) (by omega)
  have w1 := ew_words hseg3 (i := 1) (by omega)
  rw [← getD_toList, show loc m0 904 = base m0 2032 + BitVec.ofNat 64 904 from rfl,
    NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add] at w0 w1
  have hfm2 : FM m0 a s1 p m2.dmem :=
    FM.call h hfb1.sp hek2 (o := 904) (n := 64) (by omega) (by omega) hs2 hsv.2.2 hfm1
  -- `b16`: `eq_kernel` succeeded.
  refine Fr.runBlock hS N_ge rfl hfb2 (blk hp b16_in_code (by simp [b16])) e16 rfl rfl
    (by decide) (by decide) fun st3 hfb3 hd3 hm3 hpc3 ↦ ?_
  have hc16 : SBool.eval (Env.ofMachine m2 [(base m0 2032, 2032)])
      (.not (.cmp .eq .W64 (.reg .X0) (.lit 1))) = false := by
    rw [sb_not, sb_cmp, eq_apply, ev_regU, litN 1, show m2.regs.getXReg .X0 = 1 from x0r]
    rfl
  have hpc3' := pc_false hpc3 hc16
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b16Offset + b16.length = k + NativeRustcVmArm.Vm.VerifyLayer.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b16_next]] at hpc3'
  have k3 : Bus.KeepRegs [.X19, .X21, .X22, .X25] m2 st3.data := Bus.KeepRegs.of_block hm3 rfl
  refine cont st3 hpc3' ⟨hfb3, by rw [hd3]; exact hfm2, ?_, ?_, ?_, by rw [hd3]; exact w0.1,
    by rw [hd3]; exact w0.2, by rw [hd3]; exact w1.1, by rw [hd3]; exact w1.2⟩
  · show (st3.data.regs.getXReg .X25).toNat = _
    rw [kg k3 .X25, hcs2 .X25 rfl, kg k1 .X25]
    exact hi.x25
  · show (⟨st3.data.regs.getXReg .X21, st3.data.regs.getXReg .X22⟩ : EW) = _
    rw [kg k3 .X21, kg k3 .X22, hcs2 .X21 rfl, hcs2 .X22 rfl, kg k1 .X21, kg k1 .X22]
    exact hi.acc
  · show (st3.data.regs.getXReg .X19).toBitVec = _
    rw [kg k3 .X19, hcs2 .X19 rfl]
    exact x19v

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
