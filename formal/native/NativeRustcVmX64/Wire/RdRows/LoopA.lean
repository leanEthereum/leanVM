module

public import NativeRustcVmX64.Wire.RdRows.RowA
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names

/-!
# `rd_rows`' loop over rows of `rw > 0` words (x86-64)

From the call (`CallA`): `Reader::words` reads row `i` (`b8`); `None` (`b9`, `b1`: the return with
`2`), or the row's first word checked and the next leaf (`b10`): the loop's head again or the
return (`b11`): `callA_step`; the loop over the leaves (`loopA`).
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk)
open NativeRustcVm.Transcript (off off_zero off_add off_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 toNat_add64)

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem lit_add_off (b : BitVec 64) (o a : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 a) (off b o) = off b (o + a) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.add_comm]
  exact off_add b o a

theorem toNat_off_mod (b : BitVec 64) {x : Nat} (hx : x < 2 ^ 64) :
    (off b x).toNat = (b.toNat + x) % 2 ^ 64 := by
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- Two addresses of the leaves are equal exactly when their offsets are. -/
theorem Geo.off_eq {L : Nat} (g : Geo m0 bp L) {x y : Nat} (hx : x ≤ 512 * nr m0)
    (hy : y ≤ 512 * nr m0) : (off (lv m0) x).toNat = (off (lv m0) y).toNat ↔ x = y := by
  have := g.lvNw
  have := g.n256
  have := (lv m0).isLt
  rw [toNat_off_mod _ (by omega), toNat_off_mod _ (by omega)]
  omega

/-- BL after `movzbl %bl, %ebx; cmovnel %eax, %ebx` (EAX zero): the flag with one more row. -/
theorem bl_next (x : BitVec 64) (b : Bool) :
    (if b = true then BitVec.ofNat 64 0 else UnOp.apply (.zext .W8) .W32 x).toNat % 256 =
      if b = true then 0 else x.toNat % 256 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, UnOp.apply, ext, low, BitVec.toNat_setWidth,
      Width.bits]
    omega
  · rfl

/-- The result after all the rows. -/
theorem res_some {rows : List (List K)} {ci : Nat} {d : Mem 64}
    (h : Kp m0 bp B c (nr m0) rows ci d) {v : Nat} (hv : v = flag rows) : Res m0 bp B c v d := by
  unfold Res
  rw [h.hrows]
  exact ⟨hv, h.hlvs, h.hrd⟩

/-- The result when row `i` cannot be read. -/
theorem res_none {rows : List (List K)} {i ci : Nat} {d d' : Mem 64}
    (h : Kp m0 bp B c i rows ci d) (hn : rdWords B (rw m0) ci = none) (hi : i < nr m0) {v : Nat}
    (hv : v = 2) : Res m0 bp B c v d' := by
  unfold Res
  rw [rdRows_none h.hrows hn hi]
  exact hv

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length)
  (hw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost)
  (hR0 : ReaderAt m0.dmem (rdr m0) bp B c)
include hp g hw hR0

/-- **A row** (`b8`, the call, `b9`, `b10`): the return, or the loop's head at the next leaf. -/
theorem callA_step {i : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : CallA k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ ∃ rows' ci',
      HeadA k m0 bp B c (i + 1) rows' ci' st') st := by
  have hli := hI.ra.lt
  have hr0 := hI.ra.rw0
  have h64 := g.lw64
  have hrl := g.rwlw
  have hlv := g.lvNw
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  have hS := g.lvS
  have hrW := g.rW
  have hrS := g.rS
  have h0 := g.s0
  obtain ⟨hmid8, hlow8, hrdi8, hrsi8, hrdx8, hr13, hK8⟩ := ok_b8
  have hin : 512 * i + 8 * zc m0 + 8 * rw m0 ≤ 512 * nr m0 := by omega
  refine call_block hp hw g (j := NativeRustcVmX64.Vm.RdRows.b8Offset) b8_in_code (by simp [b8]) exit_b8 hmid8 hlow8 hrdi8 hrsi8
    hrdx8 hI.pc hI.ra.fr hI.kp.hloc hI.kp.hrd hin (by
      show BinOp.apply .add .W64 (reg st.data .r14) (reg st.data .r15) = _
      rw [hI.ra.r14, hI.ra.r15]
      exact off_add' _ _ _) (by
      show (reg st.data .rbp).toNat = _
      rw [hI.ra.rbp]) fun m2 hf2 hreg2 hs2 hres2 ↦ ?_
  have hk2 : ∀ x ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15], reg m2 x = reg st.data x :=
    fun x hx ↦ hreg2 x _ (keeps_of hK8 x hx) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl)
  have h13 : reg m2 .r13 = off (lv m0) (512 * i + 8 * zc m0) := by
    rw [hreg2 .r13 _ hr13 rfl]
    show BinOp.apply .add .W64 (reg st.data .r14) (reg st.data .r15) = _
    rw [hI.ra.r14, hI.ra.r15]
    exact off_add' _ _ _
  have hra2 : RA m0 i rows m2 := hI.ra.keep hf2 hk2
  -- What the call changed.
  have hcall : ∀ q, (((lv m0).toNat + (512 * i + 8 * zc m0) ≤ q.toNat ∧
      q.toNat < (lv m0).toNat + (512 * i + 8 * zc m0) + 8 * rw m0) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
      ((rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 72)) →
      Mov m0 i q ∨ ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) := by
    intro q hq
    unfold Mov
    omega
  have hchg2 : Chg m0 m2.dmem := chg_trans hI.kp.hchg hs2 fun q hq ↦ by
    rcases hcall q hq with h | h
    · rw [g.Stk_iff, g.W_iff]; unfold Mov at h; omega
    · exact .inr (.inl ((g.cur_iff).mpr h))
  -- `b9`: the tag.
  obtain ⟨hok9, hK9⟩ := ok_b9
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b9Offset) b9_in_code (by simp [b9]) exit_b9 nofun hok9 rfl hf2
    fun s9 hf9 hd9 hr9 hpc9 ↦ ?_
  have hk9 := regs_kept hK9 hr9
  have hpc9' := pc_cond hpc9 (P := boolRet m2 = 0) (by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg m2 .rax) (reg m2 .rax))
      (BitVec.ofNat 64 0) = _
    rw [al_zero]; rfl)
  cases hrd : rdWords B (rw m0) ci with
  | none =>
    rw [hrd] at hres2
    rw [ite_t hres2, hp.label NativeRustcVmX64.Vm.RdRows.label_20_at] at hpc9'
    obtain ⟨hok1, hrbx1⟩ := ok_b1
    refine Eventually.mono (fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b1Offset) b1_in_code (by simp [b1]) exit_b1 nofun hok1
      hpc9' hf9 fun s1 hf1 hd1 hr1 hpc1 ↦ ?_) fun _ h ↦ .inl h
    simp only [PcOk] at hpc1
    refine fin hp g hR0 hpc1 hf1 (res_none hI.kp hrd hli ?_) (by rw [hd1, hd9]; exact hchg2)
    rw [hr1 .rbx _ hrbx1]
    exact merge_val _ (by decide)
  | some p =>
    obtain ⟨ws, c'⟩ := p
    rw [hrd] at hres2
    obtain ⟨hb1, hws, hR2⟩ := hres2
    have hlen : ws.length = rw m0 := rdWords_length hrd
    rw [ite_f (by omega)] at hpc9'
    obtain ⟨w0, rest, rfl⟩ : ∃ w0 rest, ws = w0 :: rest :=
      List.exists_cons_of_ne_nil (by rintro rfl; simp at hlen; omega)
    have hw0 : WordAt m2.dmem (off (lv m0) (512 * i + 8 * zc m0)) w0.lane := by
      rw [List.map_cons, NativeRustcVm.wordsAt_cons_iff] at hws
      exact hws.1
    -- `b10`: the flag, the next leaf.
    obtain ⟨hmid10, hmem10, hrbx10, hr14_10, hK10⟩ := ok_b10
    have hin8 : 512 * i + 8 * zc m0 + 8 ≤ 512 * nr m0 := by omega
    refine rg_step hp g (j := NativeRustcVmX64.Vm.RdRows.b10Offset) (y := .reg .r13) (sz := 8) b10_in_code (by simp [b10])
      exit_b10 nofun hmid10 (fun w hw ↦ by
        have h' : w ∈ (after b10 rowS).mem := hw
        rw [hmem10] at h'
        cases h') (o := 512 * i + 8 * zc m0) (by decide) hin8 rfl
      (hpc9'.trans (congrArg Host.addrOf rfl)) hf9 (by
        show reg s9.data .r13 = _
        rw [hk9 .r13 (by simp [loopRegs]), h13]) fun s10 hf10 _ hm10 hd10 hpc10 ↦ ?_
    have hd10' : s10.data.dmem = m2.dmem := (hd10 hmem10).trans hd9
    have hload : (frameEnv m0 s9.data 80 [(off (lv m0) (512 * i + 8 * zc m0), 8)]).load 1 0 8 =
        w0.lane.toBitVec :=
      Wire.load_word (by
        show WordAt s9.data.dmem (off (lv m0) (512 * i + 8 * zc m0) + BitVec.ofNat 64 0) _
        rw [NativeRustcVm.addr_add_zero, hd9]
        exact hw0)
    have hk10 : ∀ x ∈ [Reg64.rbp, .r12, .r15], reg s10.data x = reg s9.data x :=
      regs_kept hK10 fun r v h ↦ hm10.regs r v h
    have hkk : ∀ x ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15], reg s9.data x = reg st.data x :=
      fun x hx ↦ (hk9 x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp only [loopRegs]
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)).trans (hk2 x hx)
    have hbl : (reg s10.data .rbx).toNat % 256 = flag (rows ++ [w0 :: rest]) := by
      rw [show reg s10.data .rbx = _ from hm10.regs .rbx _ hrbx10]
      show (if (!(CmpOp.apply .eq .W64 ((frameEnv m0 s9.data 80
        [(off (lv m0) (512 * i + 8 * zc m0), 8)]).load 1 0 8) (BitVec.ofNat 64 0))) = true then
        BitVec.ofNat 64 0 else UnOp.apply (.zext .W8) .W32 (reg s9.data .rbx)).toNat % 256 = _
      rw [bl_next, hload, eq64, hkk .rbx (by simp), hI.ra.bl, flag_snoc, List.getD_cons_zero,
        UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.zero_mod]
      have e : w0.lane.toNat = 0 ↔ w0 = 0 := by
        rw [← lane_eq_zero]
        exact ⟨fun h ↦ UInt64.toNat_inj.mp h, fun h ↦ by rw [h]; rfl⟩
      by_cases hz : w0 = 0
      · rw [ite_f (show ¬((!decide (w0.lane.toNat = 0)) = true) by simp [e.mpr hz]), ite_t hz]
      · have hz' : ¬w0.lane.toNat = 0 := fun h ↦ hz (e.mp h)
        rw [ite_t (show (!decide (w0.lane.toNat = 0)) = true by simp [hz']), ite_f hz]
    have hr14 : reg s10.data .r14 = off (lv m0) (512 * (i + 1)) := by
      rw [show reg s10.data .r14 = _ from hm10.regs .r14 _ hr14_10]
      show BinOp.apply .add .W64 (BitVec.ofNat 64 512) (reg s9.data .r14) = _
      rw [hkk .r14 (by simp), hI.ra.r14, lit_add_off]
      rw [show 512 * i + 512 = 512 * (i + 1) by omega]
    have hleaf : WordsAt m2.dmem (off (lv m0) (512 * i))
        ((paddedLeaf (w0 :: rest) (lw m0)).map K.lane) := by
      rw [map_lane_paddedLeaf, hlen, NativeRustcVm.wordsAt_append_iff, List.length_replicate,
        off_add]
      refine ⟨g.words_keep (by simp; omega) hI.zs hs2 fun q hq ↦ ?_, hws⟩
      simp only [List.length_replicate]
      omega
    have hkp : Kp m0 bp B c (i + 1) (rows ++ [w0 :: rest]) c' s10.data.dmem := by
      rw [hd10']
      exact Kp.succ g hI.kp hli hrd hs2 hcall hR2 hleaf
    have hpc11 := pc_cond hpc10 (P := i + 1 ≠ nr m0) (by
      show (!(CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 512)
        (reg s9.data .r14)) (reg s9.data .r12))) = _
      rw [hkk .r14 (by simp), hkk .r12 (by simp), hI.ra.r14, hI.ra.r12, lit_add_off, eq64,
        Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      rw [g.off_eq (by omega) (by omega)]
      omega)
    by_cases hlast : i + 1 ≠ nr m0
    · rw [ite_t hlast, hp.label NativeRustcVmX64.Vm.RdRows.label_4_at] at hpc11
      exact .done _ (.inr ⟨_, _, hpc11, ⟨hf10, hr14,
        (hk10 .r12 (by simp)).trans ((hkk .r12 (by simp)).trans hI.ra.r12),
        (hk10 .rbp (by simp)).trans ((hkk .rbp (by simp)).trans hI.ra.rbp),
        (hk10 .r15 (by simp)).trans ((hkk .r15 (by simp)).trans hI.ra.r15), hbl, by omega, hr0⟩,
        hkp⟩)
    · rw [ite_f hlast] at hpc11
      have hn : i + 1 = nr m0 := by omega
      obtain ⟨hok11, hK11⟩ := ok_b11
      refine Eventually.mono (fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b11Offset) b11_in_code (by simp [b11]) exit_b11 nofun
        hok11 (hpc11.trans (congrArg Host.addrOf rfl)) hf10 fun s11 hf11 hd11 hr11 hpc12 ↦ ?_)
        fun _ h ↦ .inl h
      simp only [PcOk] at hpc12
      rw [hp.label NativeRustcVmX64.Vm.RdRows.label_21_at] at hpc12
      rw [hn] at hkp
      refine fin hp g hR0 hpc12 hf11 (res_some (by rw [hd11]; exact hkp) ?_)
        (by rw [hd11, hd10']; exact hchg2)
      rw [regs_kept hK11 hr11 .rbx (by simp)]
      exact hbl

/-- **The loop over the leaves** of rows of `rw > 0` words. -/
theorem loopA {i : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : HeadA k m0 bp B c i rows ci st) : Eventually (step1 Host.exe) (Post m0) st := by
  refine Sym.loop (fun n st ↦ ∃ i rows ci, n = nr m0 - i ∧ HeadA k m0 bp B c i rows ci st)
    (fun n st ⟨i, rows, ci, hn, hI⟩ ↦ ?_) ⟨i, rows, ci, rfl, hI⟩
  subst hn
  refine Eventually.bind (toCall hp g hI) fun st' hC ↦ Eventually.mono (callA_step hp g hw hR0 hC)
    fun st'' h ↦ ?_
  rcases h with h | ⟨rows', ci', hH⟩
  · exact .inl h
  · exact .inr ⟨nr m0 - (i + 1), by have := hI.ra.lt; omega, i + 1, rows', ci', rfl, hH⟩

end

end

end NativeRustcVmX64.Wire.RdRows
