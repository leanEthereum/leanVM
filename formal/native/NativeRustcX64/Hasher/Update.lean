module

public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.Hasher.UpdateLoop

/-!
# `Hasher::update` on x86-64

**`update_spec`**: rustc's `Hasher::update`, placed anywhere in the program, meets its contract
(`UpdatePre`, `UpdatePost`) given the contracts of `memcpy` and `keccak_f`. The prologue (`b0`)
pushes the callee-saved registers and enters the loop (`loop_spec`) with nothing absorbed; the
epilogue (`b9`) pops them and returns the hasher.
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Update
open NativeRustcX64.KeccakF NativeRustcX64.Hasher

public section

theorem frm_add {m0 : MachineData} (n : Nat) (h : n ≤ 112) :
    frm m0 + BitVec.ofInt 64 (n : Int) = spAt m0 - BitVec.ofNat 64 (112 - n) := by
  rw [frm, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (spAt m0).isLt
  omega

/-- The return address: the frame's bytes 112 to 119, the entry's 8 bytes at RSP. -/
theorem load_ret {env : Env} {m0 m : MachineData} (g : Geo m0) (hm0 : Mapped m0.dmem (frm m0) 120)
    (hsame : SameOutside m0.dmem m.dmem (Chg m0)) (hb : env.base 0 = frm m0)
    (hd : env.mem0 = m.dmem) :
    env.load 0 112 8 = BitVec.ofInt 64 ((Mem.loadInt m0.dmem (rspOf m0) 8).getD 0) := by
  have hfrN := frm_toNat g
  have haddr : ∀ j, frm m0 + BitVec.ofNat 64 (112 + j) = rspOf m0 + BitVec.ofNat 64 j :=
    fun j => by
      rw [← add_ofNat_add]
      congr 1
      rw [frm]
      exact BitVec.sub_add_cancel _ _
  have hget : ∀ j < 8, m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      some ((m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)).getD 0) := fun j hj => by
    have := hm0 (112 + j) (by omega)
    rw [haddr] at this
    revert this
    cases m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) <;> simp
  rw [loadInt_of_get? _ _ 8 _ hget, Option.getD_some]
  unfold Env.load
  congr 2
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [hb, hd, haddr, hsame]
  rw [chg_iff g, toNat_add_ofNat' (by have := g.s8; show (spAt m0).toNat + j < _; omega)]
  have := g.hs
  have := g.s8
  have e : (spAt m0).toNat = (rspOf m0).toNat := rfl
  omega

theorem toBitVec_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  simp

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **`Hasher::update` meets its contract** under `ElfHost`. -/
theorem update_spec_elf (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : ElfSpec (Labels.label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    ElfSpec (Labels.label NativeRustcX64.Common.Update.entryLabel) UpdatePre
      UpdatePost := by
  intro m0 hpre
  have g := geo_of hpre
  have hfrN := frm_toNat g
  rw [lbl_entry hp]
  -- The prologue.
  let env0 := Env.ofMachine m0 [(frm m0, 120), (hAt m0, 344), (gotAddr "memcpy", 8)]
  obtain ⟨hhg, hfg⟩ := got_apart hpre
  have hfh : Apart (frm m0) 120 (hAt m0) 344 := by
    unfold Apart
    rw [hfrN]
    have := g.hs
    have := g.s
    omega
  have hwf0 : env0.WF := by
    refine Env.wf_of ⟨⟨frm_mapped hpre, ?_⟩,
      ⟨hpre.2.2.2.1, g.h⟩,
      ⟨(got_of hpre).mapped (by simp),
        ((got_of hpre).1 "memcpy" (by simp)).2.1⟩, trivial⟩ ?_
    · show (frm m0).toNat + 120 ≤ _
      rw [hfrN]
      have := g.s8
      have := g.s
      omega
    · apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_pair.mpr hhg⟩
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hfh
      · exact hfg
  have hm0 : Match env0 entryS m0 := by
    have hm := match_ofMachine (m := m0)
      (regions := [(frm m0, 120), (hAt m0, 344), (gotAddr "memcpy", 8)])
      (vars := fun _ => 0) (ret := 0) (sregions := [120, 344, 8])
      (known := [(.rsp, .ptr 0 112), (.rdi, .ptr 1 0)])
      (labels := []) (bounds := []) (aliases := [(.gotSlot "memcpy", 2, 0)])
      ⟨rfl, rfl, rfl, trivial⟩
      ⟨show rspOf m0 = (spAt m0 - 112#64) + BitVec.ofInt 64 112 by
          rw [show BitVec.ofInt 64 112 = 112#64 from rfl]
          exact (BitVec.sub_add_cancel _ _).symm,
        (BitVec.add_zero _).symm, trivial⟩ trivial trivial
      ⟨(BitVec.add_zero _).symm, trivial⟩
    apply hm.withKnownBytes (r := 2) (off := 0) (n := 8) (v := .label "memcpy")
    intro i hi
    simpa [Env.base, Sym.eval] using (got_of hpre).byte (l := "memcpy") (by simp) hi
  refine exec_then_elf (hb0 hp) run_b0 hwf0 nofun hm0 fun m1s hm1 hpc1 => ?_
  obtain ⟨m1, pc1⟩ := m1s
  simp only [PcOk, lbl_1 hp] at hpc1
  subst hpc1
  have hl0 := b0_mem
  rw [after_eq run_b0] at hl0
  have hw1 : ∀ p, ¬((spAt m0).toNat - 48 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat) →
      m1.dmem.get? p = m0.dmem.get? p := fun p hp =>
    hm1.get?_mem0 hwf0 fun ⟨w, hw, b, sz, hb, h1, h2⟩ => hp (by
      obtain ⟨hr, ho, hn⟩ := hl0 w hw
      change ([(frm m0, 120), (hAt m0, 344), (gotAddr "memcpy", 8)] :
        List (BitVec 64 × Nat))[w.r]? = some (b, sz) at hb
      rw [hr] at hb
      obtain ⟨rfl, rfl⟩ : frm m0 = b ∧ 120 = sz := by simpa using hb
      rw [hfrN] at h1 h2
      have := g.s
      omega)
  have hH1 : hasher m0 m1 = hasher m0 m0 := bytesOf_congr fun i hi => hw1 _ (by
    rw [toNat_add_ofNat' (by have := g.h; omega)]
    have := g.hs
    omega)
  have hb1 : env0.base 1 = hAt m0 := rfl
  have hinv : Inv m0 0 m1 := by
    refine ⟨⟨?_, ?_, ?_, ?_, fun p hp => hw1 p ?_, ?_, ?_⟩, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
    · exact (hm1.regs .r14 _ rfl).trans (BitVec.add_zero _)
    · exact (hm1.regs .r13 _ rfl).trans rfl
    · exact (hm1.regs .rsp _ rfl).trans rfl
    · simp only [AllOf, pushSlots]
      exact ⟨wordAt_write (v := .reg .rbx) (r := 0) (sz := 120) hm1 rfl (by decide) rfl,
        wordAt_write (v := .reg .r12) (r := 0) (sz := 120) hm1 rfl (by decide) rfl,
        wordAt_write (v := .reg .r13) (r := 0) (sz := 120) hm1 rfl (by decide) rfl,
        wordAt_write (v := .reg .r14) (r := 0) (sz := 120) hm1 rfl (by decide) rfl,
        wordAt_write (v := .reg .r15) (r := 0) (sz := 120) hm1 rfl (by decide) rfl,
        wordAt_write (v := .reg .rbp) (r := 0) (sz := 120) hm1 rfl (by decide) rfl, trivial⟩
    · rw [chg_iff g] at hp
      have := g.s
      omega
    · exact hm1.kept hwf0
    · exact hm1.regs .rbp (.label "memcpy") rfl
    · rw [show reg m1 .rbx = _ from hm1.regs .rbx _ rfl, Nat.sub_zero]
      exact toBitVec_eq_ofNat _
    · rw [show reg m1 .r15 = _ from hm1.regs .r15 _ rfl]
      exact (BitVec.add_zero _).symm
    · rw [show reg m1 .rdi = _ from hm1.regs .rdi _ rfl, hH1]
      simp only [Sym.eval]
      rw [load_eq_bytesOf _ hb1 (N := 344) (by omega) hpre.2.2.2.1, List.take_of_length_le
        (by simp [length_bytesOf]), bufLen_ofBytes (length_bytesOf ..)]
      rfl
    · intro a ha
      rw [List.take_zero, List.append_nil, hH1]
      exact ha
  -- The loop.
  refine NativeRustcX64.Eventually.bind_elf (loop_spec hp hmemcpy hkf hpre hinv)
    fun st ⟨hpc, hfin⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  -- The epilogue.
  have hfr := hfin.frame
  let env9 := Env.ofMachine d [(frm m0, 120)]
  have hwf9 : env9.WF :=
    Env.wf_of ⟨⟨fun i hi => hfr.kept _ (frm_mapped hpre i hi),
      by show (frm m0).toNat + 120 ≤ _; rw [hfrN]; have := g.s8; have := g.s; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm9 : Match env9 exitS d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hfr.rsp.trans rfl, trivial⟩ trivial trivial trivial
  have hsv := hfr.saved
  simp only [AllOf, pushSlots] at hsv
  obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hsv
  have t64 : env9.load 0 64 8 = reg m0 .rbx := load_of_wordAt (r := 0) s0
  have t72 : env9.load 0 72 8 = reg m0 .r12 := load_of_wordAt (r := 0) s1
  have t80 : env9.load 0 80 8 = reg m0 .r13 := load_of_wordAt (r := 0) s2
  have t88 : env9.load 0 88 8 = reg m0 .r14 := load_of_wordAt (r := 0) s3
  have t96 : env9.load 0 96 8 = reg m0 .r15 := load_of_wordAt (r := 0) s4
  have t104 : env9.load 0 104 8 = reg m0 .rbp := load_of_wordAt (r := 0) s5
  refine exec_then_elf (hb9 hp) run_b9 hwf9 nofun hm9 fun st hm' hpc' => ?_
  have hmem' : ∀ p, st.data.dmem.get? p = d.dmem.get? p := fun p =>
    hm'.get?_mem0 hwf9 fun ⟨_, hw, _⟩ => by simp at hw
  refine Eventually.done _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [Sym.eval]
    rw [retOf, load_ret g (frm_mapped hpre) hfr.same rfl rfl]
  · show reg st.data .rsp = _
    rw [show reg st.data .rsp = _ from hm'.regs .rsp _ rfl]
    show frm m0 + BitVec.ofInt 64 (120 : Nat) = _
    rw [frm, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (spAt m0).isLt
    show _ = ((spAt m0).toNat + 8) % _
    omega
  · -- RAX: the hasher.
    exact (hm'.regs .rax _ rfl).trans hfr.r14
  · -- The hasher absorbed the input.
    intro a ha
    have := hfin.holds a ha
    rw [List.take_of_length_le (by rw [length_input])] at this
    show HasherHolds (hasher m0 st.data) (a ++ input m0)
    rwa [show hasher m0 st.data = hasher m0 d from bytesOf_congr fun i _ => hmem' _]
  · -- Memory outside the hasher and the stack.
    intro p hp
    rw [hmem' p]
    exact hfr.same p hp
  · -- The registers kept.
    refine ⟨fun r hr => ?_, fun p hp => ?_⟩
    · cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr
      · exact (hm'.regs .rbx _ rfl).trans t64
      · exact (hm'.regs .rbp _ rfl).trans t104
      · exact (hm'.regs .r12 _ rfl).trans t72
      · exact (hm'.regs .r13 _ rfl).trans t80
      · exact (hm'.regs .r14 _ rfl).trans t88
      · exact (hm'.regs .r15 _ rfl).trans t96
    · rw [hmem' p]
      exact hfr.kept p hp

end

private theorem spec_to_elfSpec [h : Host]
    {entry : [Labels] → Int64} {P : [Labels] → MachineData → Prop}
    {Q : [Labels] → MachineData → MachineData → Prop}
    (hs : Spec (@entry _) (@P _) (@Q _)) :
    @ElfSpec (Host.toElfHost h) (@entry (@instLabelsElfHost (Host.toElfHost h)))
      (@P (@instLabelsElfHost (Host.toElfHost h))) (@Q (@instLabelsElfHost (Host.toElfHost h))) := by
  intro m hP
  have hL : @instLabelsElfHost (Host.toElfHost h) = (inferInstance : Labels) := toElfHost_labels h
  rw [elfStep1_toElfHost h]
  rw [hL] at hP ⊢
  exact hs m hP

public section

/-- **`Hasher::update` meets its contract.** -/
theorem update_spec [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : Spec (Labels.label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (Labels.label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost :=
  ElfSpec.toSpec (entry := fun [Labels] => Labels.label NativeRustcX64.Common.Update.entryLabel)
    (P := fun [Labels] => UpdatePre) (Q := fun [Labels] => UpdatePost)
    (@update_spec_elf (Host.toElfHost _) 0 k hp.toPlacedIn
      (spec_to_elfSpec (entry := fun [Labels] => Labels.label NativeRustcX64.Common.Memcpy.entryLabel)
        (P := fun [Labels] => MemcpyPre) (Q := fun [Labels] => MemcpyPost) hmemcpy)
      (spec_to_elfSpec (entry := fun [Labels] => Labels.label NativeRustcX64.Common.KeccakF.entryLabel)
        (P := fun [Labels] => KeccakFPre) (Q := fun [Labels] => KeccakFPost) hkf))

end

end NativeRustcX64.Hasher.Update
