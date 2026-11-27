module

public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.Hasher.UpdateAbsorb

/-!
# `Hasher::update`'s loop (x86-64)

After `keccak_f`, `b8` stores `0` into `buf_len` and jumps to `.LUpdate_5`: the hasher is the
turn's (`updateStep` of a full buffer, `empty_spec`). `.LUpdate_5` (`b2`) counts the bytes a turn
took (R12) off the remaining ones (RBX) and on the input pointer (R15), then leaves the loop
(`.LUpdate_6`) when none remain, else falls through to the loop head `.LUpdate_1` (`next_spec`).
A turn from the loop head (`turn_spec`), and the loop (`loop_spec`): from the loop head, out of the
loop with the whole input absorbed.
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustc NativeRustc.Keccak LeanVM.Protocol.KeccakHash NativeRustcX64.Sym
open NativeRustcX64.Common.Update NativeRustcX64.KeccakF NativeRustcX64.Hasher

public section

theorem sub_ofNat_ofNat {n c t : Nat} (h : t ≤ n - c) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - c) - BitVec.ofNat 64 t = BitVec.ofNat 64 (n - (c + t)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x == 0#64) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h
    subst h
    rfl

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **Emptying the buffer.** -/
theorem empty_spec (hp : PlacedIn code sec k) {m0 m : MachineData} (hpre : UpdatePre m0) {c : Nat}
    {Hc : List UInt8} (hab : Absorbed m0 c Hc m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b2Offset) ∧ Mid m0 c (takeN m0 c Hc) st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b8Offset)⟩ := by
  have g := geo_of hpre
  let env := Env.ofMachine m [(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)]
  have hwf : env.WF := wf_head hpre hab.frame
  have hm : Match env headS m := match_headS hpre hab.frame
  have hA := hab.bytes
  generalize hAdef : writeAt (counted m0 c Hc) 0 (absorb ((counted m0 c Hc).take 200)
    (((counted m0 c Hc).drop 200).take 136)) = A at hA
  have hstep : (updateStep Hc ((input m0).drop c)).1 = writeAt A 336 (wordBytes 0) := by
    rw [updateStep_eq, ite_pos' hab.full, hAdef]
  have hlenA : A.length = 344 := by rw [← hA]; exact length_bytesOf ..
  refine exec_then_elf (hb8 hp) run_b8 hwf nofun hm fun st8 hm8 hpc8 => ?_
  simp only [PcOk, lbl_5 hp] at hpc8
  have hmem8 : ∀ j < 344, st8.data.dmem.get? (hAt m0 + BitVec.ofNat 64 j) =
      if 336 ≤ j then some 0 else m.dmem.get? (hAt m0 + BitVec.ofNat 64 j) := by
    intro j hj
    rw [hm8.mem 0 (hAt m0) 344 rfl j hj]
    by_cases h : 336 ≤ j
    · simp only [memByte, findWrite, h, show j < 336 + 8 by omega, and_self, ↓reduceIte, Sym.eval]
      simp [byteOf]
    · simp only [memByte, findWrite, h, false_and, and_false, ↓reduceIte]
      rfl
  have hbytes : hasher m0 st8.data = writeAt A 336 (wordBytes 0) := by
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by simp [length_wordBytes,
      hlenA]), hlenA]) fun j hj => ?_
    rw [hasher, length_bytesOf] at hj
    rw [hasher, getD_bytesOf _ _ hj, hmem8 j hj, getD_writeAt _ _ _ _ (by
      simp [length_wordBytes, hlenA]), length_wordBytes]
    by_cases h : 336 ≤ j
    · rw [ite_pos' h, ite_pos' ⟨h, by omega⟩]
      rw [show wordBytes (0 : UInt64) = List.replicate 8 0 from rfl, List.getD_eq_getElem?_getD,
        List.getElem?_replicate]
      split <;> rfl
    · rw [ite_neg' h, ite_neg' (by omega), ← hA, hasher, getD_bytesOf _ _ hj]
  have hfr : Frame m0 st8.data := by
    refine hab.frame.update g (Match.reg_eq hm hm8 rfl rfl) (Match.reg_eq hm hm8 rfl rfl)
      (Match.reg_eq hm hm8 rfl rfl) (fun p hp => hm8.get?_mem0 hwf fun hw => hp ?_)
      (hm8.kept hwf) (hm8.regs .rbp (.label "memcpy") rfl)
    rw [chgL_iff g]
    left
    exact written_hasher (by decide) hw
  have hL := hab.lt
  have hfull := hab.full
  have hle := hab.le
  have ht : takeN m0 c Hc ≤ nOf m0 - c := by unfold takeN; omega
  refine Eventually.done _ ⟨hpc8, hfr, by omega, Or.inl (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Match.reg_atom hm8 rfl).trans hab.rbx
  · exact (Match.reg_atom hm8 rfl).trans hab.r15
  · exact (Match.reg_atom hm8 rfl).trans hab.r12
  · rw [show reg st8.data .rdi = _ from hm8.regs .rdi _ rfl, hbytes, bufLen_writeAt hlenA]
    rfl
  · rw [hbytes, ← hstep]
    exact holds_turn hle hab.holds

/-- **The end of a turn**: back to the loop head with `c + t` bytes absorbed if input remains,
else to the loop's exit with all of it. -/
theorem next_spec (hp : PlacedIn code sec k) {m0 m : MachineData} {c t : Nat}
    (hmid : Mid m0 c t m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => (st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset) ∧ Inv m0 (c + t) st.data ∧ 0 < t) ∨
        (st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b9Offset) ∧ Inv m0 (nOf m0) st.data))
      ⟨m, ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b2Offset)⟩ := by
  let env := Env.ofMachine m []
  have hwf : env.WF := Env.wf_of trivial List.Pairwise.nil
  have hm : Match env regsS m := match_ofMachine trivial trivial trivial trivial trivial
  have henv : ∀ r, env.regs r = reg m r := fun _ => rfl
  refine exec_then_elf (hb2 hp) run_b2 hwf nofun hm fun st hm' hpc => ?_
  have hmem : ∀ p, st.data.dmem.get? p = m.dmem.get? p := fun p =>
    hm'.get?_mem0 hwf fun ⟨_, hw, _⟩ => by simp at hw
  have hn : nOf m0 < 2 ^ 64 := BitVec.isLt _
  have hrbx : reg st.data .rbx = BitVec.ofNat 64 (nOf m0 - (c + t)) := by
    rw [show reg st.data .rbx = _ from hm'.regs .rbx _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, henv, hmid.rbx, hmid.r12]
    exact sub_ofNat_ofNat (by have := hmid.le; omega) hn
  have hr15 : reg st.data .r15 = dAt m0 + BitVec.ofNat 64 (c + t) := by
    rw [show reg st.data .r15 = _ from hm'.regs .r15 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, henv, hmid.r15, hmid.r12]
    rw [BitVec.add_comm, add_ofNat_add]
  have hfr : Frame m0 st.data := by
    refine ⟨(Match.reg_atom hm' rfl).trans hmid.frame.r14,
      (Match.reg_atom hm' rfl).trans hmid.frame.r13,
      (Match.reg_atom hm' rfl).trans hmid.frame.rsp, ?_, fun p hp => ?_, fun p hp => ?_,
      (Match.reg_atom hm' rfl).trans hmid.frame.rbp⟩
    · have hs := hmid.frame.saved
      simp only [AllOf, pushSlots] at hs ⊢
      obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hs
      have key : ∀ {a w : BitVec 64}, WordAt m.dmem a w → WordAt st.data.dmem a w :=
        fun hw i hi => by rw [hmem]; exact hw i hi
      exact ⟨key s0, key s1, key s2, key s3, key s4, key s5, trivial⟩
    · rw [hmem]
      exact hmid.frame.same p hp
    · rw [hmem]
      exact hmid.frame.kept p hp
  have hH : hasher m0 st.data = hasher m0 m := hasher_congr hmem
  have hx0 : (reg st.data .rdi).toNat = bufLen (hasher m0 st.data) := by
    rw [show reg st.data .rdi = reg m .rdi from Match.reg_atom hm' rfl, hH]
    exact hmid.rdi
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, henv,
    BitVec.and_self] at hpc
  rw [hmid.rbx, hmid.r12, Nat.add_assoc, NativeRustcX64.Common.Update.b2_next, sub_ofNat_ofNat (by have := hmid.le; omega) hn, ofNat_beq_zero (by omega)] at hpc
  refine Eventually.done _ ?_
  by_cases hend : c + t = nOf m0
  · right
    rw [ite_pos' (by simp; omega), lbl_6 hp] at hpc
    refine ⟨hpc, hfr, le_rfl, ?_, ?_, hx0, ?_⟩
    · rw [hrbx, hend, Nat.sub_self]
    · rw [hr15, hend]
    · rw [hH, ← hend]
      exact hmid.holds
  · left
    rw [ite_neg' (by simp; have := hmid.le; omega)] at hpc
    refine ⟨hpc, ⟨hfr, hmid.le, hrbx, hr15, hx0, by rw [hH]; exact hmid.holds⟩, ?_⟩
    rcases hmid.pos with h | h
    · exact h
    · omega

/-- **A turn of the loop.** -/
theorem turn_spec (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : ElfSpec (Labels.label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m : MachineData} (hpre : UpdatePre m0) {c : Nat} (hinv : Inv m0 c m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => (st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b9Offset) ∧ Inv m0 (nOf m0) st.data) ∨
        ∃ n' < nOf m0 - c, st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset) ∧
          ∃ c', nOf m0 - c' = n' ∧ Inv m0 c' st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset)⟩ := by
  have fin : ∀ (t : Nat) (st : MachineState),
      st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b2Offset) →
      Mid m0 c t st.data →
      Eventually (elfStep1 ElfHost.exe)
        (fun st => (st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b9Offset) ∧ Inv m0 (nOf m0) st.data) ∨
          ∃ n' < nOf m0 - c, st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset) ∧
            ∃ c', nOf m0 - c' = n' ∧ Inv m0 c' st.data) st := by
    intro t st hpc hmid
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    refine NativeRustcX64.Eventually.mono_elf (next_spec hp hmid) fun st h => ?_
    rcases h with ⟨hpc, hinv', ht⟩ | h
    · exact Or.inr ⟨nOf m0 - (c + t), by have := hinv'.le; omega, hpc, c + t, rfl, hinv'⟩
    · exact Or.inl h
  refine NativeRustcX64.Eventually.bind_elf (copy_spec hp hmemcpy hpre hinv) fun st ⟨hpc, hcp⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine NativeRustcX64.Eventually.bind_elf (count_spec hp hpre hcp) fun st h => ?_
  rcases h with ⟨hpc, hmid⟩ | ⟨hpc, hfu⟩
  · exact fin _ st hpc hmid
  · obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    refine NativeRustcX64.Eventually.bind_elf (absorb_spec hp hkf hpre hfu) fun st ⟨hpc, hab⟩ => ?_
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact NativeRustcX64.Eventually.bind_elf (empty_spec hp hpre hab)
      fun st ⟨hpc, hmid⟩ => fin _ st hpc hmid

/-- **The loop**: out of it with the whole input absorbed. -/
theorem loop_spec (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : ElfSpec (Labels.label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m : MachineData} (hpre : UpdatePre m0) {c : Nat} (hinv : Inv m0 c m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b9Offset) ∧ Inv m0 (nOf m0) st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset)⟩ := by
  refine Sym.loop (fun n st => st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset) ∧
      ∃ c', nOf m0 - c' = n ∧ Inv m0 c' st.data) (fun n st ⟨hpc, c', hn, hi⟩ => ?_)
    ⟨rfl, c, rfl, hinv⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hn
  exact turn_spec hp hmemcpy hkf hpre hi

end

end NativeRustcX64.Hasher.Update
