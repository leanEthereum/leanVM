module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names

public import NativeRustcX64.Hasher.FinalizeC

/-!
# `Hasher::finalize` on x86-64

**`finalize_spec`**: rustc's `Hasher::finalize`, placed anywhere in the program, meets its
contract (`FinalizePre`, `FinalizePost`) given the contracts of `memcpy`, `memset` and `keccak_f`:
the copies to the frame (`stage2_spec`), the padding (`stage3_spec`), the permutation
(`stage4_spec`), then `b6` copies the state's first 32 bytes to the output (`Keccak.finalize`),
pops the callee-saved registers and returns.
-/

namespace NativeRustcX64.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Finalize

public section

theorem frame_top {s : BitVec 64} {i : Nat} :
    s - 384#64 + BitVec.ofNat 64 (384 + i) = s + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.isLt
  omega

variable [Host] {k : Nat}

set_option linter.unusedSimpArgs false in
/-- **`Hasher::finalize` meets its contract.** -/
theorem finalize_spec (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmemset : Spec (Labels.label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hkf : Spec (Labels.label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (Labels.label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre
      FinalizePost := by
  intro m0 hpre
  have g := geo_of hpre
  have hf := frAt_toNat g
  have hs := g.s
  have hs8 := g.s8
  have hFnw : (frAt m0).toNat + 392 ≤ 2 ^ 64 := by rw [hf]; omega
  rw [lbl_entry hp]
  refine NativeRustcX64.Eventually.bind (stage2_spec hp hmemcpy hmemset hpre)
    fun st ⟨hpc, m1, hpro, hs2⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine NativeRustcX64.Eventually.bind (stage3_spec hp hpre hs2) fun st ⟨hpc, hs3⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine NativeRustcX64.Eventually.bind (stage4_spec hp hkf hpre hpro hs3)
    fun st ⟨hpc, hs4⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  -- The epilogue.
  have hfr := hs4.fr
  have hmapF : Mapped d.dmem (frAt m0) 392 := fun i hi => hfr.kept _ (mapped_frame hpre i hi)
  have hmapO : Mapped d.dmem (oAt m0) 32 := fun i hi => hfr.kept _ (hpre.2.2.2.2.2.1 i hi)
  have hwf : (Env.ofMachine d [(frAt m0, 392), (oAt m0, 32)]).WF :=
    Env.wf_of ⟨⟨hmapF, hFnw⟩, ⟨hmapO, g.o⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        show (frAt m0).toNat + 392 ≤ (oAt m0).toNat ∨ (oAt m0).toNat + 32 ≤ (frAt m0).toNat
        rw [hf]; have := g.os; omega))
  have hbF : (Env.ofMachine d [(frAt m0, 392), (oAt m0, 32)]).base 0 = frAt m0 :=
    Env.base_ofMachine d _ _ _ rfl
  have hbO : (Env.ofMachine d [(frAt m0, 392), (oAt m0, 32)]).base 1 = oAt m0 :=
    Env.base_ofMachine d _ _ _ rfl
  have hm := match_ofMachine (m := d) (regions := [(frAt m0, 392), (oAt m0, 32)])
    (vars := fun _ => 0) (ret := 0) (sregions := [392, 32])
    (known := [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]) (labels := []) (bounds := []) (aliases := [])
    ⟨rfl, rfl, trivial⟩
    ⟨by simp only [Sym.eval, hbF]; exact hfr.rsp,
      by
        simp only [Sym.eval, hbO]
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact hfr.rbx, trivial⟩ trivial trivial trivial
  -- The bytes above the frame's 352nd are as after the prologue, and above 384 as at the entry.
  have hhi : ∀ i < 392, 352 ≤ i → d.dmem.get? (frAt m0 + BitVec.ofNat 64 i) =
      m1.dmem.get? (frAt m0 + BitVec.ofNat 64 i) := fun i hi h352 =>
    hfr.same _ (by
      rw [chgF_iff g, toNat_add_ofNat' (by omega), hf]
      omega)
  have hslot : ∀ p ∈ slots, (Env.ofMachine d [(frAt m0, 392), (oAt m0, 32)]).load 0 p.1 8 =
      reg m0 p.2 := by
    intro p hpm
    have hle : 352 ≤ p.1 ∧ p.1 + 8 ≤ 384 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
      rcases hpm with h | h | h | h <;> rw [h] <;> decide
    rw [Env.load_of_bytesAt (bs := (List.range 8).map (byteOf (reg m0 p.2)))
      (by simp) ?_, ofInt_ofBytes_byteOf]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [hbF, add_ofNat_add, Env.ofMachine_mem0, hhi _ (by omega) (by omega), ← add_ofNat_add,
      hpro.slots p hpm i (by simp [hi])]
  refine exec_then (hb6 hp) run_b6 hwf (fun _ h => nomatch h) hm fun st hm' hpc' => ?_
  have hl := b6_mem
  rw [after_eq run_b6] at hl
  have hlo := b6_out
  rw [after_eq run_b6] at hlo
  have hreg : ∀ p ∈ slots, reg st.data p.2 = reg m0 p.2 := by
    intro p hpm
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl
    · unfold reg; rw [hm'.regs .rbx _ rfl]; exact hslot (352, .rbx) (by simp [slots])
    · unfold reg; rw [hm'.regs .r12 _ rfl]; exact hslot (360, .r12) (by simp [slots])
    · unfold reg; rw [hm'.regs .r14 _ rfl]; exact hslot (368, .r14) (by simp [slots])
    · unfold reg; rw [hm'.regs .r15 _ rfl]; exact hslot (376, .r15) (by simp [slots])
  have hmem' : ∀ p, ¬((oAt m0).toNat ≤ p.toNat ∧ p.toNat < (oAt m0).toNat + 32) →
      st.data.dmem.get? p = d.dmem.get? p := fun p hp =>
    hm'.get?_mem0 hwf fun hw => hp (written_in (r := 1) rfl hl hw)
  -- The return address.
  have hmapR : Mapped m0.dmem (spAt m0) 8 := fun i hi => by
    have := mapped_frame hpre (384 + i) (by omega)
    rwa [frAt, frame_top] at this
  have hret : ∀ i < 8, d.dmem.get? (frAt m0 + BitVec.ofNat 64 (384 + i)) =
      m0.dmem.get? (spAt m0 + BitVec.ofNat 64 i) := fun i hi => by
    rw [hhi _ (by omega) (by omega), hpro.same _ (by
      rw [frame_iff g, toNat_add_ofNat' (by omega), hf]; omega), frAt, frame_top]
  have hpcR : st.pc = retOf m0 := by
    simp only [PcOk, Sym.eval] at hpc'
    rw [hpc', retOf, loadInt_of_get? _ _ 8 (fun i => (m0.dmem.get? (spAt m0 + BitVec.ofNat 64 i)).getD 0)
      (fun i hi => by
        have := hmapR i hi
        revert this
        cases h : m0.dmem.get? (spAt m0 + BitVec.ofNat 64 i) with
        | none => simp
        | some v => intro _; exact h)]
    unfold Env.load
    rw [hbF]
    simp only [Env.ofMachine_mem0, Option.getD_some]
    congr 3
    apply List.map_congr_left
    intro i hi
    rw [hret i (List.mem_range.mp hi)]
  have hs672 : (stackBelow m0 finalizeStack).toNat = (spAt m0).toNat - 672 :=
    stackBelow_toNat (by show 672 ≤ (spAt m0).toNat; omega)
  refine Eventually.done _ ⟨hpcR, ?_, ?_, ?_, ?_⟩
  · -- RSP 8 above.
    show st.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ rfl]
    simp only [Sym.eval, hbF]
    show frAt m0 + BitVec.ofInt 64 392 = spAt m0 + 8#64
    apply BitVec.eq_of_toNat_eq
    simp only [frAt, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show BitVec.ofInt 64 392 = 392#64 from rfl]
    simp only [BitVec.toNat_ofNat]
    omega
  · -- The digest.
    intro j hj
    have hlen : (finalize (bytesOf m0.dmem (reg m0 .rsi) 344)).length = 32 := by
      rw [finalize, digestOf, List.length_take, absorb, keccakF, length_stateBytes]
      rfl
    rw [hlen] at hj
    show st.data.dmem.get? (oAt m0 + BitVec.ofNat 64 j) = _
    rw [hm'.mem 1 (oAt m0) 32 rfl j hj]
    unfold memByte
    rw [hlo j hj]
    simp only [Sym.eval]
    rw [byteOf_load (by omega) (by omega), hbF, Env.ofMachine_mem0,
      show 152 + 8 * (j / 8) + j % 8 = 152 + j by omega]
    have hget := congrArg (·.getD j 0) hs4.state
    simp only at hget
    rw [getD_bytesOf _ _ (show j < 200 by omega), add_ofNat_add] at hget
    rw [hget, getElem_eq_getD]
    have e : finalize (bytesOf m0.dmem (reg m0 .rsi) 344) =
        (absorb ((hbytes m0).take 200) (finalBlock (tailOf m0))).take 32 := by
      simp only [finalize, digestOf, tailOf, lenOf, hbytes, hAt]
    rw [e, Native.Keccak.Proof.getD_take, ite_pos' hj]
  · -- Memory outside the output and the stack.
    intro p hp
    change ¬(InRange (oAt m0) 32 p ∨ InRange (stackBelow m0 finalizeStack) 672 p) at hp
    rw [inRange_iff g.o, inRange_iff (by rw [hs672]; omega), hs672] at hp
    rw [hmem' p (by omega), hfr.same p (by rw [chgF_iff g]; omega),
      hpro.same p (by rw [frame_iff g]; omega)]
  · -- The registers kept.
    refine ⟨fun r hr => ?_, fun p hp => ?_⟩
    · cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr
      · exact hreg (352, .rbx) (by simp [slots])
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .rbp (by simp))
      · exact hreg (360, .r12) (by simp [slots])
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .r13 (by simp))
      · exact hreg (368, .r14) (by simp [slots])
      · exact hreg (376, .r15) (by simp [slots])
    · by_cases hpo : (oAt m0).toNat ≤ p.toNat ∧ p.toNat < (oAt m0).toNat + 32
      · exact hm'.kept hwf p (hfr.kept p hp)
      · rw [hmem' p hpo]
        exact hfr.kept p hp

end

end NativeRustcX64.Hasher.Finalize
