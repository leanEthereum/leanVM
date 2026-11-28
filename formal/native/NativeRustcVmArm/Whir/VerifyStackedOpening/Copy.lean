module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Final

/-!
# `verify_stacked_opening`: the levels copied

`copy_b32`: from `b32` (`AtB32`), `memcpy` copies the ladder's levels from the frame's byte 264 to
byte 112; `b33` reads their count (at most `6`, never `7`): at `b34` (`AtB34`). Helpers: levels
over bytes a step keeps (`levelsAt_keep`), the writes of a block in one region (`written_r`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open LeanVM.Parameters

@[expose] public section

/-- **At `b34`**: the levels at the frame's byte 112, their count in X5. -/
structure AtB34 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (ls : List Whir.Level) (m0 st : MachineData) :
    Prop where
  com : Common a s layout cs m0 st
  fwb : FW st.dmem m0 (basisWords layout cs m0)
  lad : Whir.ladder layout.stackLog m0.regs.X2.toNat = some ls
  len : ls.length ≤ 6
  lv : LevelsAt st.dmem (loc m0 112) ls
  x5 : st.regs.X5 = ls.length.toUInt64
  x21 : st.regs.getXReg .X21 = layout.stackLog.toUInt64
  claim : (⟨st.regs.getXReg .X28, st.regs.getXReg .X29⟩ : EW) +
    ⟨st.regs.getXReg .X27, st.regs.getXReg .X26⟩ = claimOf s layout target cs value

end

public section

/-- **Levels over bytes a step keeps.** -/
theorem levelsAt_keep {d d' : Mem 64} {p : BitVec 64} {ls : List Whir.Level}
    (hl : LevelsAt d p ls) (hlen : ls.length ≤ 6) {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) (hR : ∀ j < 144, ¬R (p + BitVec.ofNat 64 j)) :
    LevelsAt d' p ls := fun i hi ↦ by
  obtain ⟨h1, h2, h3, h4⟩ := hl i hi
  refine ⟨h1, h2, h3, NativeRustcVm.BytesAt.of_sameOutside h4 hs fun j hj hq ↦
    hR (levelBytes * i + j) ?_ ?_⟩
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      NativeRustcVm.length_wordBytes] at hj
    simp only [levelBytes]
    omega
  · rwa [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] at hq

/-- A block whose writes are all in region `r` writes only there. -/
theorem written_r {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {F : Nat} (hwf : env.WF)
    (h0 : env.regions[r]? = some (b, F)) (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ F)
    {q : BitVec 64} (hq : Written env S q) : InRange b F q := by
  obtain ⟨w, hw, b', sz, hb, h1, h2⟩ := hq
  obtain ⟨hr, hle⟩ := hS w hw
  rw [hr, h0] at hb
  cases hb
  rw [Sym.inRange_iff (hwf.noWrap r b F h0)]
  omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData} {ls : List Whir.Level}

/-- **From `b32`** to `b34`: the levels copied, their count checked. -/
theorem copy_b32 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {R : MachineState → Prop}
    (cont : ∀ st, AtB34 a s layout target cs value ls m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b34Offset)⟩)
    {st : MachineData} (hb : AtB32 a s layout target cs value ls m0 st) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b32Offset)⟩ := by
  have hc := hb.com
  have hS := h.hS
  -- `b32`
  obtain ⟨hwf, hm⟩ := h.frame_env hc.fr
  have hk32 : b32.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b32Offset) := b32_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk32 run_b32 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : VFr m0 st1.data := Fr.ofBlock hc.fr hm hm1 hwf rfl rfl rfl (by simp)
  have hd1 : st1.data.dmem = st.dmem := hm1.dmem_eq hwf rfl
  have k1 : ∀ r, calleeSaved r = true → st1.data.regs.getXReg r = st.regs.getXReg r :=
    fun r hr ↦ (rv hm1 (v := .reg r) (by
      cases r <;> first | rfl | exact absurd hr (by decide))).trans rfl
  have e0 : st1.data.regs.X0.toBitVec = loc m0 112 :=
    (hm1.regs .X0 _ rfl).trans (by show base m0 512 + BitVec.ofInt 64 112 = _; rfl)
  have e1 : st1.data.regs.X1.toBitVec = loc m0 264 := by
    refine (hm1.regs .X1 _ rfl).trans ?_
    sym_simp
    show (st.regs.getXReg .X19).toBitVec + BitVec.ofNat 64 8 = _
    rw [hb.x19, NativeRustcVm.addr_add_add]
  have e2 : st1.data.regs.X2.toNat = 144 := by
    rw [show st1.data.regs.X2 = 144 from (rv hm1 (r := .X2) rfl).trans rfl]; rfl
  have hpre : MemcpyPre st1.data := by
    have r0 := h.loc_readable hf1 (o := 112) (n := 144) (by omega)
    have r1 := h.loc_readable hf1 (o := 264) (n := 144) (by omega)
    simp only [MemcpyPre]
    rw [e0, e1, e2]
    refine ⟨r0.1, r1.1, r0.2, r1.2, ?_⟩
    unfold Apart
    rw [h.loc_toNat (by omega), h.loc_toNat (by omega)]
    omega
  refine Fr.leafIn (N' := 0) (lo := 112) (n := 144) hf1 h.hN (by rw [stack_eq]; decide)
    (by omega) (fun _ h ↦ by cases h) (by decide) h.ctx.frame_outs hmemcpy hpc1 hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ .inr (.inl (by
      have : InRange st1.data.regs.X0.toBitVec st1.data.regs.X2.toNat q := hq'
      rw [e0, e2] at this
      exact this)), hq.2.2.2⟩)
    fun m2 hf2 hq2 hcs2 ↦ ?_
  obtain ⟨-, hcp, hch, hsv⟩ := hq2
  have hcp' : NativeRustcVm.BytesAt m2.dmem (loc m0 112)
      (NativeRustcArm.bytesOf st1.data.dmem (loc m0 264) 144) := by
    have : NativeRustcVm.BytesAt m2.dmem st1.data.regs.X0.toBitVec
        (NativeRustcArm.bytesOf st1.data.dmem st1.data.regs.X1.toBitVec
          st1.data.regs.X2.toNat) := hcp
    rwa [e0, e1, e2] at this
  have hch' : SameOutside st1.data.dmem m2.dmem (InRange (loc m0 112) 144) := by
    refine NativeRustcVm.SameOutside.mono hch fun q hq ↦ ?_
    have : InRange st1.data.regs.X0.toBitVec st1.data.regs.X2.toNat q := hq
    rwa [e0, e2] at this
  have hc1 : Common a s layout cs m0 st1.data := hc.same hf1 hd1 fun r hr ↦ k1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl)
  have hc2 : Common a s layout cs m0 m2 :=
    hc1.win h hf2 (by omega) (by omega) hch' hsv.2.2 fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hcs2 _ rfl
  have hwb2 := fw_win h hf1 (o' := 112) (n' := 144) (L := basisWords layout cs m0) (by omega) hch'
    (fun p hp ↦ by simp only [basisWords, List.mem_cons, List.not_mem_nil, or_false] at hp
                   rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by rw [hd1]; exact hb.fwb)
  have hlv2 : LevelsAt m2.dmem (loc m0 112) ls :=
    levelsAt_copy hcp' (by rw [hd1]; exact hb.lv) hb.len
  have hcnt2 : NativeRustcVm.WordAt m2.dmem (loc m0 408) ls.length.toUInt64 :=
    Fr.bytes_keep (N' := 0) (o' := 112) (n' := 144) hf1 h.hN h.ctx.frame_outs
      (by rw [stack_eq]; decide) (by omega)
      (NativeRustcVm.SameOutside.mono hch' fun q hq ↦ .inr (.inl hq)) (o := 408)
      (bs := NativeRustcVm.wordBytes _) (by rw [NativeRustcVm.length_wordBytes]; omega)
      (.inr (by omega)) (by rw [hd1]; exact hb.cnt)
  -- `b33`
  obtain ⟨hwf3, hm3⟩ := h.frame_env hf2
  have hk33 : b33.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b33Offset) := b33_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at (st := ⟨m2, _⟩) hk33 run_b33 hwf3 rfl hm3 fun st3 hm3' hpc3 ↦ ?_
  have hl408 : (Env.ofMachine m2 [(base m0 512, 512)]).load 0 408 8 =
      ls.length.toUInt64.toBitVec := Ring.load_word hcnt2
  have hc3 : Common a s layout cs m0 st3.data := hc2.blk hm3 hm3' hwf3 rfl rfl (by decide)
  have hd3 : st3.data.dmem = m2.dmem := hm3'.dmem_eq hwf3 rfl
  have k3 : ∀ r, r ≠ .X5 → st3.data.regs.getXReg r = m2.regs.getXReg r :=
    fun r h5 ↦ (rv hm3' (v := .reg r) (by cases r <;> first | rfl | exact absurd rfl h5)).trans rfl
  have hlen := hb.len
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [hl408, toBitVec_ult_ofNat (by decide), natCast_toUInt64_toNat (by omega)] at hpc3
  simp only [show decide (ls.length < 7) = true from decide_eq_true (by omega), Bool.not_true,
    Bool.false_eq_true, ↓reduceIte] at hpc3
  have hb33 : b33.length = NativeRustcVmArm.Vm.VerifyStackedOpening.b33Length := NativeRustcVmArm.Vm.VerifyStackedOpening.b33_length
  rw [hb33] at hpc3
  obtain ⟨d3, pc3⟩ := st3
  simp only at hpc3
  subst hpc3
  have kk : ∀ r, calleeSaved r = true → d3.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    rw [k3 r (by rintro rfl; exact absurd hr (by decide)), hcs2 r hr, k1 r hr]
  refine cont d3 ⟨hc3, by rw [hd3]; exact hwb2, hb.lad, hb.len, by rw [hd3]; exact hlv2,
    (rv hm3' (r := .X5) rfl).trans (by
      show UInt64.ofBitVec ((Env.ofMachine m2 [(base m0 512, 512)]).load 0 408 8) = _
      rw [hl408]), by rw [kk .X21 rfl]; exact hb.x21, ?_⟩
  rw [kk .X28 rfl, kk .X29 rfl, kk .X27 rfl, kk .X26 rfl]
  exact hb.claim

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
