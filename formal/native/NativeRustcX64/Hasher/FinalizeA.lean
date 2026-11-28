module

public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names

public import NativeRustcX64.Hasher.FinalizeInv

/-!
# `Hasher::finalize` (x86-64): the state and the buffer copied to the frame

From the entry, the prologue (`b0`) pushes the callee-saved registers (the frame's bytes 352 to
383, `Pro`) and copies the state's 200 bytes to the frame's byte 152 (`memcpy`); `b1`, `b2` check
`buf_len < 136` (the branches to the panics fail); `b3` zeroes the block, the frame's bytes 16 to
151 (`memset`), and `b4` copies the `buf_len` buffered bytes over their start (`memcpy`):
`Stage2`, `stage2_spec`.
-/

namespace NativeRustcX64.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Finalize

@[expose] public section

/-- `buf_len` at the entry. -/
def lenOf (m0 : MachineData) : Nat := bufLen (hbytes m0)

/-- The buffered bytes at the entry. -/
def tailOf (m0 : MachineData) : List UInt8 := ((hbytes m0).drop 200).take (lenOf m0)

/-- What the prologue leaves: memory as at the entry but in the frame below the return address,
the callee-saved registers in their slots. -/
structure Pro (m0 m1 : MachineData) : Prop where
  same : SameOutside m0.dmem m1.dmem (InRange (frAt m0) 384)
  slots : ∀ p ∈ slots, BytesAt m1.dmem (frAt m0 + BitVec.ofNat 64 p.1)
    ((List.range 8).map (byteOf (reg m0 p.2)))

/-- After the second `memcpy`: the buffered bytes and zeros, then the state, in the frame from
its byte 16. -/
structure Stage2 (m0 m1 m : MachineData) : Prop where
  fr : Fr m0 m1 m
  r14 : (reg m .r14).toNat = lenOf m0
  bytes : bytesOf m.dmem (frAt m0 + BitVec.ofNat 64 16) 336 =
    (tailOf m0 ++ List.replicate (136 - lenOf m0) 0) ++ (hbytes m0).take 200

end

public section

theorem lenOf_lt [Labels] {m0 : MachineData} (hpre : FinalizePre m0) : lenOf m0 < 136 := by
  obtain ⟨a, ha⟩ := hpre.2.2.1
  rw [lenOf, hbytes, hAt, bufLen_of_holds ha]
  exact Nat.mod_lt _ (by omega)

theorem length_hbytes (m0 : MachineData) : (hbytes m0).length = 344 := length_bytesOf ..

theorem length_tailOf {m0 : MachineData} (h : lenOf m0 < 136) : (tailOf m0).length = lenOf m0 := by
  simp [tailOf, length_hbytes]
  omega

theorem getD_stage2 (T A : List UInt8) {L : Nat} (hT : T.length = L) (hL : L ≤ 136) {j : Nat} :
    ((T ++ List.replicate (136 - L) 0) ++ A).getD j 0 =
      if j < L then T.getD j 0 else if j < 136 then 0 else A.getD (j - 136) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : j < L
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega),
      ite_pos' h1]
  · rw [ite_neg' h1]
    by_cases h2 : j < 136
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hT,
        List.getElem?_replicate, ite_pos' h2, ite_pos' (by omega)]
      rfl
    · rw [List.getElem?_append_right (by simp; omega), ite_neg' h2]
      simp only [List.length_append, List.length_replicate, hT]
      rw [show L + (136 - L) = 136 by omega]

theorem stack_frame {s : BitVec 64} {i : Nat} :
    s - BitVec.ofNat 64 672 + BitVec.ofNat 64 (288 + i) = s - 384#64 + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.isLt
  omega

/-- The frame is data memory at the entry. -/
theorem mapped_frame [Labels] {m0 : MachineData} (hpre : FinalizePre m0) :
    Mapped m0.dmem (frAt m0) 392 := fun i hi => by
  have := hpre.1.2.2 (288 + i) (by show 288 + i < 672 + 8; omega)
  rwa [show rspOf m0 - BitVec.ofNat 64 finalizeStack + BitVec.ofNat 64 (288 + i) =
    frAt m0 + BitVec.ofNat 64 i from stack_frame] at this

/-- A memory-call block adds its loader slot to the ordinary frame/input regions. -/
theorem wf_got [Labels] {m0 m : MachineData} (hpre : FinalizePre m0)
    (hk : Kept m0.dmem m.dmem) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    {vs : Nat → BitVec 64} {ret : BitVec 64} :
    (Env.ofMachine m (gotRegions m0 l) vs ret).WF := by
  have g := geo_of hpre
  have hs0 := g.s
  have hs8 := g.s8
  have hf := frAt_toNat g
  obtain ⟨_, hn, hs, ha⟩ := (got_of hpre).1 l hl
  have hh := ha (hAt m0, 344) (by simp)
  have hb := stackBelow_toNat g.s
  change Apart (gotAddr l) 8 (stackBelow m0 finalizeStack) (finalizeStack + 8) at hs
  change (stackBelow m0 finalizeStack).toNat = (spAt m0).toNat - 672 at hb
  unfold Apart at hs hh
  rw [hb] at hs
  change _ ≤ _ ∨ (spAt m0).toNat - 672 + (672 + 8) ≤ _ at hs
  have hfh : Apart (frAt m0) 392 (hAt m0) 344 := by
    unfold Apart
    rw [hf]
    have := g.hs
    omega
  have hfg : Apart (frAt m0) 392 (gotAddr l) 8 := by
    unfold Apart
    rw [hf]
    omega
  have hhg : Apart (hAt m0) 344 (gotAddr l) 8 := hh.symm
  refine Env.wf_of ⟨⟨fun i hi => hk _ (mapped_frame hpre i hi), ?_⟩,
    ⟨fun i hi => hk _ (hpre.2.2.2.1 i hi), g.h⟩,
    ⟨fun i hi => hk _ ((got_of hpre).mapped hl i hi), hn⟩, trivial⟩ ?_
  · change (frAt m0).toNat + 392 ≤ 2 ^ 64
    rw [hf]
    omega
  · apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_pair.mpr hhg⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hfh
    · exact hfg

variable [Host] {k : Nat}

set_option linter.unusedSimpArgs false in
/-- **The prologue and the copies to the frame.** -/
theorem stage2_spec (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmemset : Spec (Labels.label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost) {m0 : MachineData}
    (hpre : FinalizePre m0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + NativeRustcX64.Common.Finalize.b5Offset) ∧ ∃ m1, Pro m0 m1 ∧ Stage2 m0 m1 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcX64.Common.Finalize.b0Offset)⟩ := by
  have g := geo_of hpre
  have hs := g.s
  have hs8 := g.s8
  have hf := frAt_toNat g
  have hL := lenOf_lt hpre
  have hmapH : Mapped m0.dmem (hAt m0) 344 := hpre.2.2.2.1
  have hmapF := mapped_frame hpre
  have hFnw : (frAt m0).toNat + 392 ≤ 2 ^ 64 := by rw [hf]; omega
  have hFo : ∀ o, o < 392 → (frAt m0 + BitVec.ofNat 64 o).toNat = (frAt m0).toNat + o :=
    fun o ho => toNat_add_ofNat' (by omega)
  have hHo : ∀ o, o < 344 → (hAt m0 + BitVec.ofNat 64 o).toNat = (hAt m0).toNat + o :=
    fun o ho => toNat_add_ofNat' (by have := g.h; omega)
  -- The prologue.
  let env0 := Env.ofMachine m0 (gotRegions m0 "memcpy") (fun _ => 0)
    (Host.addrOf (k + NativeRustcX64.Common.Finalize.b0Offset + b0.length)).toBitVec
  have hwf0 : env0.WF := wf_got hpre (fun _ h => h) (by simp)
  have hbF0 : env0.base 0 = frAt m0 := rfl
  have hknown0 : ∀ w ∈ knownGot "memcpy", ∀ i < w.n,
      env0.mem0.get? (env0.base w.r + BitVec.ofNat 64 (w.off + i)) =
        some (byteOf (w.v.eval env0) i) := by
    intro w hw i hi
    simp only [knownGot, List.mem_singleton] at hw
    subst w
    simpa [env0, gotRegions, Env.base, Sym.eval] using
      (got_of hpre).byte (l := "memcpy") (by simp) hi
  have hm0base := match_ofMachine (m := m0) (regions := gotRegions m0 "memcpy")
    (vars := fun _ => 0)
    (ret := (Host.addrOf (k + NativeRustcX64.Common.Finalize.b0Offset + b0.length)).toBitVec)
    (sregions := [392, 344, 8]) (known := [(.rsp, .ptr 0 384)])
    (labels := []) (bounds := []) (aliases := [(.gotSlot "memcpy", 2, 0)])
    ⟨rfl, rfl, rfl, trivial⟩
    ⟨by
      simp only [Sym.eval, hbF0]
      show spAt m0 = spAt m0 - 384#64 + 384#64
      exact (BitVec.sub_add_cancel _ _).symm, trivial⟩ trivial trivial
    ⟨(BitVec.add_zero _).symm, trivial⟩
  have hm0 : Match env0 entryS m0 :=
    hm0base.withKnownBytes (r := 2) (off := 0) (n := 8) (v := .label "memcpy")
      (hknown0 ⟨2, 0, 8, .label "memcpy"⟩ (by simp [knownGot]))
  refine exec_then (hb0 hp) run_b0 hwf0 (fun _ _ => rfl) hm0 fun st1 hm1 hpc1 => ?_
  have hl0 := b0_mem
  rw [after_eq run_b0] at hl0
  have hsl0 := b0_slots
  rw [after_eq run_b0] at hsl0
  have h01 : SameOutside m0.dmem st1.data.dmem (InRange (frAt m0) 384) := fun p hp =>
    hm1.get?_mem0 hwf0 fun hw => hp ((inRange_iff (by omega)).mpr
      (written_lim (r := 0) rfl hl0 hw))
  have hpro : Pro m0 st1.data := ⟨h01, fun p hpm => hm1.bytesAt_write (r := 0) (o := p.1) (n := 8)
    (sz := 392) rfl (by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
      rcases hpm with h | h | h | h <;> rw [h] <;> decide) (hsl0 p hpm)⟩
  have hk1 := hm1.kept hwf0
  have hH1 : ∀ i < 344, st1.data.dmem.get? (hAt m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (hAt m0 + BitVec.ofNat 64 i) := fun i hi => h01 _ (by
    rw [frame_iff g, hHo i (by omega)]; have := g.hs; omega)
  have hX : ∀ r v, (after b0 entryS).reg r = some v → reg st1.data r =
      v.eval env0 := fun r v h => by
    rw [after_eq run_b0] at h
    exact hm1.regs r v h
  have hrdi1 : reg st1.data .rdi = frAt m0 + BitVec.ofNat 64 152 := by
    rw [hX .rdi _ (by rw [after_eq run_b0]; rfl)]; simp only [Sym.eval, hbF0]; rfl
  have hrsi1 : reg st1.data .rsi = hAt m0 := hX .rsi (.reg .rsi) (by rw [after_eq run_b0]; rfl)
  have hatom : ∀ r v, (r, v) ∈ [(Reg64.rbx, Reg64.rdi), (.rbp, .rbp), (.r13, .r13), (.r15, .rsi)] →
      reg st1.data r = reg m0 v := by
    intro r v h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hX .rbx (.reg .rdi) (by rw [after_eq run_b0]; rfl)
    · exact hX .rbp (.reg .rbp) (by rw [after_eq run_b0]; rfl)
    · exact hX .r13 (.reg .r13) (by rw [after_eq run_b0]; rfl)
    · exact hX .r15 (.reg .rsi) (by rw [after_eq run_b0]; rfl)
  have hrdx1 : (reg st1.data .rdx).toNat = 200 := by
    rw [hX .rdx _ (by rw [after_eq run_b0]; rfl)]; rfl
  have hrsp1 : st1.data.regs.get64 .rsp = frAt m0 := by
    show reg st1.data .rsp = _
    rw [hX .rsp _ (by rw [after_eq run_b0]; rfl)]; simp only [Sym.eval, hbF0]; simp
  -- The first `memcpy`: the state.
  refine call_then hpc1 hmemcpy ?pre1 fun st2 hpc2 hrsp2 hpost2 => ?_
  case pre1 =>
    refine ⟨⟨Nat.zero_le _, by rw [rspOf, hrsp1]; omega, fun i hi => ?_⟩, fun i hi => ?_,
      fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · rw [rspOf, hrsp1, BitVec.sub_zero]; exact hk1 _ (hmapF i (by omega))
    · rw [hrdi1, add_ofNat_add]; rw [hrdx1] at hi; exact hk1 _ (hmapF _ (by omega))
    · rw [hrsi1]; rw [hrdx1] at hi; exact hk1 _ (hmapH i (by omega))
    · show (reg st1.data .rdi).toNat + (reg st1.data .rdx).toNat ≤ _
      rw [hrdi1, hrdx1, hFo _ (by omega)]; omega
    · show (reg st1.data .rsi).toNat + (reg st1.data .rdx).toNat ≤ _
      rw [hrsi1, hrdx1]; have := g.h; omega
    · show (reg st1.data .rdi).toNat + (reg st1.data .rdx).toNat ≤ (reg st1.data .rsi).toNat ∨
        (reg st1.data .rsi).toNat + (reg st1.data .rdx).toNat ≤ (reg st1.data .rdi).toNat
      rw [hrdi1, hrsi1, hrdx1, hFo _ (by omega), hf]; have := g.hs; omega
    · show (reg st1.data .rdi).toNat + (reg st1.data .rdx).toNat ≤ (rspOf st1.data).toNat ∨
        (rspOf st1.data).toNat + 8 ≤ (reg st1.data .rdi).toNat
      rw [rspOf, hrsp1, hrdi1, hrdx1, hFo _ (by omega)]; omega
  obtain ⟨-, hbytes2, hsame2, hsaved2⟩ := hpost2
  rw [hrdi1, hrsi1, hrdx1] at hbytes2
  rw [hrdi1, hrdx1] at hsame2
  have hsrc1 : bytesOf st1.data.dmem (hAt m0) 200 = (hbytes m0).take 200 := by
    rw [bytesOf_take _ _ (show 200 ≤ 344 by omega), hbytes]
    exact congrArg _ (bytesOf_congr hH1)
  rw [hsrc1] at hbytes2
  have hfr2 : Fr m0 st1.data st2.data := by
    refine ⟨?_, ?_, fun r hr => ?_, fun p hp => ?_, fun p hp => hsaved2.2 p (hk1 p hp)⟩
    · show rspOf st2.data = _
      rw [hrsp2, rspOf, hrsp1]
    · show st2.data.regs.get64 .rbx = _
      rw [hsaved2.1 .rbx rfl]
      exact hatom .rbx .rdi (by simp)
    · have hc : calleeSaved r = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> rfl
      show st2.data.regs.get64 r = _
      rw [hsaved2.1 r hc]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hatom .rbp .rbp (by simp)
      · exact hatom .r13 .r13 (by simp)
    · exact hsame2 p fun h => hp (by
        rw [inRange_iff (by rw [hFo _ (by omega)]; omega), hFo _ (by omega)] at h
        rw [chgF_iff g]; rw [hf] at h; have := g.s; omega)
  have hH2 : ∀ i < 344, st2.data.dmem.get? (hAt m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (hAt m0 + BitVec.ofNat 64 i) := fun i hi => hasher_same g hfr2 h01 hi
  have hr15 : reg st2.data .r15 = hAt m0 := by
    show st2.data.regs.get64 .r15 = _
    rw [hsaved2.1 .r15 rfl]
    exact hatom .r15 .rsi (by simp)
  -- `b1`, `b2`, `b3`.
  obtain ⟨d2, pc2⟩ := st2
  have hpc2' : pc2 = Host.addrOf (k + NativeRustcX64.Common.Finalize.b1Offset) := by rw [show pc2 = _ from hpc2]; rfl
  subst hpc2'
  let env2 := Env.ofMachine d2 (gotRegions m0 "memset") (fun _ => 0)
    (Host.addrOf (k + NativeRustcX64.Common.Finalize.b3Offset + b3.length)).toBitVec
  have hwf2 : env2.WF := wf_got hpre hfr2.kept (by simp)
  have hbF : env2.base 0 = frAt m0 := rfl
  have hbH : env2.base 1 = hAt m0 := rfl
  have hknown2 : ∀ i < 8, env2.mem0.get? (env2.base 2 + BitVec.ofNat 64 (0 + i)) =
      some (byteOf ((Sym.label "memset").eval env2) i) := by
    intro i hi
    simp only [Nat.zero_add]
    change d2.dmem.get? (gotAddr "memset" + BitVec.ofNat 64 i) = _
    rw [got_same hpre hfr2 h01 (l := "memset") (by simp) hi]
    exact (got_of hpre).byte (l := "memset") (by simp) hi
  have hm2base := match_ofMachine (m := d2) (regions := gotRegions m0 "memset")
    (vars := fun _ => 0) (ret := (Host.addrOf (k + NativeRustcX64.Common.Finalize.b3Offset + b3.length)).toBitVec)
    (sregions := [392, 344, 8]) (known := [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]) (labels := [])
    (bounds := []) (aliases := [(.gotSlot "memset", 2, 0)]) ⟨rfl, rfl, rfl, trivial⟩
    ⟨by simp only [Sym.eval, hbF]; exact hfr2.rsp,
      by
        simp only [Sym.eval, hbH]
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact hr15,
      trivial⟩ trivial trivial ⟨(BitVec.add_zero _).symm, trivial⟩
  have hm2 : Match env2 copyS d2 := hm2base.withKnownBytes hknown2
  have hload : env2.load 1 336 8 =
      BitVec.ofInt 64 (Int.ofBytes ((hbytes m0).drop 336)) := by
    rw [load_eq_bytesOf _ hbH (N := 344) (by omega) (fun i hi => hfr2.kept _ (hmapH i hi)),
      List.take_of_length_le (by simp [length_bytesOf])]
    congr 3
    exact bytesOf_congr hH2
  have hLv : (BitVec.ofInt 64 (Int.ofBytes ((hbytes m0).drop 336))).toNat = lenOf m0 :=
    bufLen_ofBytes (length_hbytes m0)
  refine exec_then (hb1 hp) run_b1 hwf2 (fun _ h => nomatch h) hm2 fun st3 hm3 hpc3 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hload] at hpc3
  simp only [Nat.add_assoc, NativeRustcX64.Common.Finalize.b1_next] at hpc3
  rw [ite_neg' (by simp [BitVec.ult, hLv]; omega)] at hpc3
  refine exec_at (hb2 hp) (exec_after run_b1 run_b2) hwf2 (fun _ h => nomatch h) hpc3 hm3
    fun st4 hm4 hpc4 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hload] at hpc4
  simp only [Nat.add_assoc, NativeRustcX64.Common.Finalize.b2_next] at hpc4
  rw [ite_neg' (by
    simp only [beq_iff_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [hLv] at this
    simp at this
    omega)] at hpc4
  have hr3 := run_b3
  rw [after_eq run_b1, after_eq (exec_after run_b1 run_b2)] at hr3
  refine exec_at (hb3 hp) (exec_after (exec_after run_b1 run_b2) run_b3) hwf2 (fun _ _ => rfl)
    hpc4 hm4 fun st5 hm5 hpc5 => ?_
  have hl3 := b3_mem
  rw [after_eq run_b1, after_eq (exec_after run_b1 run_b2),
    after_eq (exec_after (exec_after run_b1 run_b2) run_b3)] at hl3
  have hrdi5 : reg st5.data .rdi = frAt m0 + BitVec.ofNat 64 16 := by
    unfold reg; rw [hm5.regs .rdi _ rfl]; simp only [Sym.eval, hbF]; rfl
  have hrsi5 : reg st5.data .rsi = 0#64 := by unfold reg; rw [hm5.regs .rsi _ rfl]; rfl
  have hrdx5 : (reg st5.data .rdx).toNat = 136 := by unfold reg; rw [hm5.regs .rdx _ rfl]; rfl
  have hrsp5 : st5.data.regs.get64 .rsp = frAt m0 := by
    rw [hm5.regs .rsp _ rfl]; simp only [Sym.eval, hbF]; simp
  have hr14 : (reg st5.data .r14).toNat = lenOf m0 := by
    unfold reg; rw [hm5.regs .r14 _ rfl]; simp only [Sym.eval, hload]; exact hLv
  have hr12 : reg st5.data .r12 = frAt m0 + BitVec.ofNat 64 16 := by
    unfold reg; rw [hm5.regs .r12 _ rfl]; simp only [Sym.eval, hbF]; rfl
  have hr15' : reg st5.data .r15 = hAt m0 + BitVec.ofNat 64 200 := by
    unfold reg; rw [hm5.regs .r15 _ rfl]; simp only [Sym.eval, hbH]; rfl
  -- `memset`: the block zeroed.
  refine call_then hpc5 hmemset ?pre5 fun st6 hpc6 hrsp6 hpost6 => ?_
  case pre5 =>
    refine ⟨⟨Nat.zero_le _, by rw [rspOf, hrsp5]; omega, fun i hi => ?_⟩, fun i hi => ?_, ?_, ?_⟩
    · rw [rspOf, hrsp5, BitVec.sub_zero]
      exact hm5.kept hwf2 _ (hfr2.kept _ (hmapF i (by omega)))
    · rw [hrdi5, add_ofNat_add]; rw [hrdx5] at hi
      exact hm5.kept hwf2 _ (hfr2.kept _ (hmapF _ (by omega)))
    · show (reg st5.data .rdi).toNat + (reg st5.data .rdx).toNat ≤ _
      rw [hrdi5, hrdx5, hFo _ (by omega)]; omega
    · show (reg st5.data .rdi).toNat + (reg st5.data .rdx).toNat ≤ (rspOf st5.data).toNat ∨
        (rspOf st5.data).toNat + 8 ≤ (reg st5.data .rdi).toNat
      rw [rspOf, hrsp5, hrdi5, hrdx5, hFo _ (by omega)]; omega
  obtain ⟨-, hbytes6, hsame6, hsaved6⟩ := hpost6
  rw [hrdi5, hrsi5, hrdx5] at hbytes6
  rw [hrdi5, hrdx5] at hsame6
  have hfr6 : Fr m0 st1.data st6.data := hfr2.after_call hm5 hwf2 hbF rfl
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rfl)
    (fun p hw => by
      have h8 : (frAt m0).toNat ≤ p.toNat ∧ p.toNat < (frAt m0).toNat + 8 :=
        written_lim (r := 0) (h := frAt m0) (sz := 392) rfl (lim := 8) (fun w hw => by
          rw [hl3] at hw; simp only [List.mem_singleton] at hw; subst hw; decide) hw
      exact chg_of_frame g (o := 0) (n := 8) (by decide) ⟨by simpa using h8.1, by simpa using h8.2⟩)
    hrsp6 hsaved6 hsame6 (fun p h => by
      rw [inRange_iff (by rw [hFo _ (by omega)]; omega), hFo _ (by omega)] at h
      exact chg_of_frame g (o := 16) (n := 136) (by decide) h)
  have hr12' : reg st6.data .r12 = frAt m0 + BitVec.ofNat 64 16 := by
    unfold reg; rw [hsaved6.1 .r12 rfl]; exact hr12
  have hr15'' : reg st6.data .r15 = hAt m0 + BitVec.ofNat 64 200 := by
    unfold reg; rw [hsaved6.1 .r15 rfl]; exact hr15'
  have hr14' : (reg st6.data .r14).toNat = lenOf m0 := by
    unfold reg; rw [hsaved6.1 .r14 rfl]; exact hr14
  -- `b4`, and the second `memcpy`: the buffered bytes.
  obtain ⟨d6, pc6⟩ := st6
  have hpc6' : pc6 = Host.addrOf (k + NativeRustcX64.Common.Finalize.b4Offset) := by rw [show pc6 = _ from hpc6]; rfl
  subst hpc6'
  let env6 := Env.ofMachine d6 (gotRegions m0 "memcpy") (fun _ => 0)
    (Host.addrOf (k + NativeRustcX64.Common.Finalize.b4Offset + b4.length)).toBitVec
  have hwf6 : env6.WF := wf_got hpre hfr6.kept (by simp)
  have hbF6 : env6.base 0 = frAt m0 := rfl
  have hbH6 : env6.base 1 = hAt m0 := rfl
  have hknown6 : ∀ i < 8, env6.mem0.get? (env6.base 2 + BitVec.ofNat 64 (0 + i)) =
      some (byteOf ((Sym.label "memcpy").eval env6) i) := by
    intro i hi
    simp only [Nat.zero_add]
    change d6.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) = _
    rw [got_same hpre hfr6 h01 (l := "memcpy") (by simp) hi]
    exact (got_of hpre).byte (l := "memcpy") (by simp) hi
  have hm6base := match_ofMachine (m := d6) (regions := gotRegions m0 "memcpy")
    (vars := fun _ => 0) (ret := (Host.addrOf (k + NativeRustcX64.Common.Finalize.b4Offset + b4.length)).toBitVec)
    (sregions := [392, 344, 8]) (known := [(.rsp, .ptr 0 8), (.r12, .ptr 0 16), (.r15, .ptr 1 200)])
    (labels := []) (bounds := []) (aliases := [(.gotSlot "memcpy", 2, 0)]) ⟨rfl, rfl, rfl, trivial⟩
    ⟨by simp only [Sym.eval, hbF6]; exact hfr6.rsp,
      by simp only [Sym.eval, hbF6]; exact hr12',
      by simp only [Sym.eval, hbH6]; exact hr15'', trivial⟩ trivial trivial
    ⟨(BitVec.add_zero _).symm, trivial⟩
  have hm6 : Match env6 setS d6 := hm6base.withKnownBytes hknown6
  refine exec_then (hb4 hp) run_b4 hwf6 (fun _ _ => rfl) hm6 fun st7 hm7 hpc7 => ?_
  have hl4 := b4_mem
  rw [after_eq run_b4] at hl4
  have hrdi7 : reg st7.data .rdi = frAt m0 + BitVec.ofNat 64 16 := by
    unfold reg; rw [hm7.regs .rdi _ rfl]; simp only [Sym.eval, hbF6]; rfl
  have hrsi7 : reg st7.data .rsi = hAt m0 + BitVec.ofNat 64 200 := by
    unfold reg; rw [hm7.regs .rsi _ rfl]; simp only [Sym.eval, hbH6]; rfl
  have hrdx7 : (reg st7.data .rdx).toNat = lenOf m0 := by
    unfold reg; rw [hm7.regs .rdx _ rfl]; exact hr14'
  have hrsp7 : st7.data.regs.get64 .rsp = frAt m0 := by
    rw [hm7.regs .rsp _ rfl]; simp only [Sym.eval, hbF6]; simp
  have hmem7 : ∀ p, ¬((frAt m0).toNat ≤ p.toNat ∧ p.toNat < (frAt m0).toNat + 8) →
      st7.data.dmem.get? p = d6.dmem.get? p := fun p hp =>
    hm7.get?_mem0 hwf6 fun hw => hp (written_lim (r := 0) (h := frAt m0) (sz := 392) rfl
      (lim := 8) (fun w hw => by
        rw [hl4] at hw; simp only [List.mem_singleton] at hw; subst hw; decide) hw)
  refine call_then hpc7 hmemcpy ?pre7 fun st8 hpc8 hrsp8 hpost8 => ?_
  case pre7 =>
    refine ⟨⟨Nat.zero_le _, by rw [rspOf, hrsp7]; omega, fun i hi => ?_⟩, fun i hi => ?_,
      fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · rw [rspOf, hrsp7, BitVec.sub_zero]
      exact hm7.kept hwf6 _ (hfr6.kept _ (hmapF i (by omega)))
    · rw [hrdi7, add_ofNat_add]; rw [hrdx7] at hi
      exact hm7.kept hwf6 _ (hfr6.kept _ (hmapF _ (by omega)))
    · rw [hrsi7, add_ofNat_add]; rw [hrdx7] at hi
      exact hm7.kept hwf6 _ (hfr6.kept _ (hmapH _ (by omega)))
    · show (reg st7.data .rdi).toNat + (reg st7.data .rdx).toNat ≤ _
      rw [hrdi7, hrdx7, hFo _ (by omega)]; omega
    · show (reg st7.data .rsi).toNat + (reg st7.data .rdx).toNat ≤ _
      rw [hrsi7, hrdx7, hHo _ (by omega)]; have := g.h; omega
    · show (reg st7.data .rdi).toNat + (reg st7.data .rdx).toNat ≤ (reg st7.data .rsi).toNat ∨
        (reg st7.data .rsi).toNat + (reg st7.data .rdx).toNat ≤ (reg st7.data .rdi).toNat
      rw [hrdi7, hrsi7, hrdx7, hFo _ (by omega), hHo _ (by omega), hf]; have := g.hs; omega
    · show (reg st7.data .rdi).toNat + (reg st7.data .rdx).toNat ≤ (rspOf st7.data).toNat ∨
        (rspOf st7.data).toNat + 8 ≤ (reg st7.data .rdi).toNat
      rw [rspOf, hrsp7, hrdi7, hrdx7, hFo _ (by omega)]; omega
  obtain ⟨-, hbytes8, hsame8, hsaved8⟩ := hpost8
  rw [hrdi7, hrsi7, hrdx7] at hbytes8
  rw [hrdi7, hrdx7] at hsame8
  have hfr8 : Fr m0 st1.data st8.data := hfr6.after_call hm7 hwf6 hbF6 rfl
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rfl)
    (fun p hw => by
      have h8 : (frAt m0).toNat ≤ p.toNat ∧ p.toNat < (frAt m0).toNat + 8 :=
        written_lim (r := 0) (h := frAt m0) (sz := 392) rfl (lim := 8) (fun w hw => by
          rw [hl4] at hw; simp only [List.mem_singleton] at hw; subst hw; decide) hw
      exact chg_of_frame g (o := 0) (n := 8) (by decide) ⟨by simpa using h8.1, by simpa using h8.2⟩)
    hrsp8 hsaved8 hsame8 (fun p h => by
      rcases Nat.eq_zero_or_pos (lenOf m0) with h0 | h0
      · rw [h0] at h; exact absurd h (Nat.not_lt_zero _)
      rw [inRange_iff (by rw [hFo _ (by omega)]; omega), hFo _ (by omega)] at h
      exact chg_of_frame g (o := 16) (n := lenOf m0) (by omega) h)
  refine Eventually.done _ ⟨by rw [hpc8]; rfl, st1.data, hpro, hfr8, ?_, ?_⟩
  · unfold reg; rw [hsaved8.1 .r14 rfl, hm7.regs .r14 _ rfl]; exact hr14'
  · have hTl := length_tailOf hL
    refine ext_getD (by simp [length_bytesOf, hTl, length_hbytes]; omega) fun j hj => ?_
    rw [length_bytesOf] at hj
    rw [getD_stage2 _ _ hTl (by omega), getD_bytesOf _ _ hj, add_ofNat_add]
    have hj16 : ¬((frAt m0).toNat ≤ (frAt m0 + BitVec.ofNat 64 (16 + j)).toNat ∧
        (frAt m0 + BitVec.ofNat 64 (16 + j)).toNat < (frAt m0).toNat + 8) := by
      rw [hFo _ (by omega)]; omega
    by_cases h1 : j < lenOf m0
    · rw [ite_pos' h1, ← add_ofNat_add, hbytes8 j (by rw [length_bytesOf]; exact h1),
        Option.getD_some, getElem_eq_getD, getD_bytesOf _ _ h1, add_ofNat_add, tailOf,
        Native.Keccak.Proof.getD_take, ite_pos' h1, Native.Keccak.Proof.getD_drop, hbytes,
        getD_bytesOf _ _ (show 200 + j < 344 by omega),
        hmem7 _ (by rw [hHo _ (by omega)]; have := g.hs; rw [hf]; omega)]
      exact congrArg (·.getD 0) (hasher_same g hfr6 h01 (i := 200 + j) (by omega))
    · rw [ite_neg' h1, hsame8 _ (fun h => h1 (by
        rcases Nat.eq_zero_or_pos (lenOf m0) with h0 | h0
        · rw [h0] at h; exact absurd h (Nat.not_lt_zero _)
        rw [inRange_iff (by rw [hFo _ (by omega)]; omega), hFo _ (by omega),
          hFo _ (by omega)] at h
        omega)), hmem7 _ hj16]
      by_cases h2 : j < 136
      · rw [ite_pos' h2, ← add_ofNat_add, hbytes6 j (by simp; omega)]
        simp only [Option.getD_some, List.getElem_replicate]
        rfl
      · rw [ite_neg' h2, hsame6 _ (fun h => h2 (by
          rw [inRange_iff (by rw [hFo _ (by omega)]; omega), hFo _ (by omega),
            hFo _ (by omega)] at h
          omega)), hm5.get?_mem0 hwf2 (fun hw => hj16 (written_lim (r := 0) (h := frAt m0)
            (sz := 392) rfl (lim := 8) (fun w hw => by
              rw [hl3] at hw; simp only [List.mem_singleton] at hw; subst hw; decide) hw)),
          Env.ofMachine_mem0, show 16 + j = 152 + (j - 136) by omega, ← add_ofNat_add,
          hbytes2 (j - 136) (by simp [length_hbytes]; omega), Option.getD_some, getElem_eq_getD]
