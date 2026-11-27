module

public import NativeRustcX64.Code.Common.KeccakF.Names

public import NativeRustcX64.Hasher.FinalizeB

/-!
# `Hasher::finalize` (x86-64): the final block absorbed

From `Stage3`, `b5b` XORs `PAD_LAST` into the block's last byte and the block's 17 lanes into the
state's (`b5b_byte`: the state is `xorBlock` of the hasher's state and the final block) and calls
`keccak_f` on the state (`Stage4`, `stage4_spec`).
-/

namespace NativeRustcX64.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Finalize

@[expose] public section

/-- After `keccak_f`: the state absorbed the final block. -/
structure Stage4 (m0 m1 m : MachineData) : Prop where
  fr : Fr m0 m1 m
  state : bytesOf m.dmem (frAt m0 + BitVec.ofNat 64 152) 200 =
    absorb ((hbytes m0).take 200) (finalBlock (tailOf m0))

end

public section

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **The final block absorbed.** -/
theorem stage4_spec (hp : PlacedIn code sec k)
    (hkf : ElfSpec (Labels.label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m1 m : MachineData} (hpre : FinalizePre m0) (hpro : Pro m0 m1) (hs3 : Stage3 m0 m1 m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Finalize.b6Offset) ∧ Stage4 m0 m1 st.data)
      ⟨m, ElfHost.addrOf sec (k + (NativeRustcX64.Common.Finalize.b5Offset + b5a.length))⟩ := by
  have g := geo_of hpre
  have gr := geoRc_of hpre
  have hf := frAt_toNat g
  have hs := g.s
  have hs8 := g.s8
  have hL := lenOf_lt hpre
  have hfr := hs3.fr
  have hFnw : (frAt m0).toNat + 392 ≤ 2 ^ 64 := by rw [hf]; omega
  have hFo : ∀ o, o < 392 → (frAt m0 + BitVec.ofNat 64 o).toNat = (frAt m0).toNat + o :=
    fun o ho => toNat_add_ofNat' (by omega)
  have hmapF : Mapped m.dmem (frAt m0) 392 := fun i hi => hfr.kept _ (mapped_frame hpre i hi)
  have hwf : (Env.ofMachine m [(frAt m0, 392)] (fun _ => 0)
      (ElfHost.addrOf sec (k + (NativeRustcX64.Common.Finalize.b5Offset + b5a.length) + b5b.length)).toBitVec).WF :=
    Env.wf_of ⟨⟨hmapF, hFnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hbF : (Env.ofMachine m [(frAt m0, 392)] (fun _ => 0)
      (ElfHost.addrOf sec (k + (NativeRustcX64.Common.Finalize.b5Offset + b5a.length) + b5b.length)).toBitVec).base 0 = frAt m0 :=
    Env.base_ofMachine m _ _ _ rfl
  have hmx := match_ofMachine (m := m) (regions := [(frAt m0, 392)]) (vars := fun _ => 0)
    (ret := (ElfHost.addrOf sec (k + (NativeRustcX64.Common.Finalize.b5Offset + b5a.length) + b5b.length)).toBitVec) (sregions := [392])
    (known := [(.rsp, .ptr 0 8)]) (labels := []) (bounds := []) (aliases := []) ⟨rfl, trivial⟩
    ⟨by simp only [Sym.eval, hbF]; exact hfr.rsp, trivial⟩ trivial trivial trivial
  refine exec_then_elf (hb5b hp) run_b5b hwf (fun _ _ => rfl) hmx fun st5 hm5 hpc5 => ?_
  have hl := b5b_mem
  rw [after_eq run_b5b] at hl
  have hTl := length_tailOf hL
  -- The state XOR the final block.
  have hxor : bytesOf st5.data.dmem (frAt m0 + BitVec.ofNat 64 152) 200 =
      NativeRustc.Keccak.xorBlock ((hbytes m0).take 200) (finalBlock (tailOf m0)) := by
    refine ext_getD (by simp [length_bytesOf, NativeRustc.Keccak.xorBlock, length_stateBytes])
      fun j hj => ?_
    rw [length_bytesOf] at hj
    rw [getD_bytesOf _ _ hj, add_ofNat_add, b5b_byte hm5 hwf rfl hl hj, getD_xorBlock _ _ hj]
    have hA := hs3.bytes (136 + j) (by omega)
    unfold frByte at hA
    rw [ite_neg' (by omega), show 136 + j - 136 = j by omega,
      show 16 + (136 + j) = 152 + j by omega] at hA
    simp only [Env.ofMachine_mem0]
    rw [hA]
    by_cases h1 : j < 136
    · have hB := hs3.bytes j (by omega)
      unfold frByte at hB
      rw [ite_pos' h1] at hB
      rw [ite_pos' h1, ite_pos' h1, hB, getD_finalBlock (by omega) h1, hTl]
    · rw [ite_neg' h1, ite_neg' h1]
  -- `keccak_f`.
  have hrsp5 : st5.data.regs.get64 .rsp = frAt m0 := by
    rw [hm5.regs .rsp _ rfl]; simp only [Sym.eval, hbF]; simp
  have hspN : (rspOf st5.data).toNat = (spAt m0).toNat - 384 := by rw [rspOf, hrsp5, hf]
  have hsb : stackBelow st5.data keccakFStack = frAt m0 - 288#64 := by
    rw [stackBelow, rspOf, hrsp5]; rfl
  have hS288 : (frAt m0 - 288#64).toNat = (spAt m0).toNat - 672 := chg_base g
  have hrdi : reg st5.data .rdi = frAt m0 + BitVec.ofNat 64 152 := by
    unfold reg; rw [hm5.regs .rdi _ rfl]; simp only [Sym.eval, hbF]; rfl
  have hmapS : Mapped m0.dmem (frAt m0 - 288#64) 680 := fun i hi => by
    have := hpre.1.2.2 i (by show i < 672 + 8; omega)
    rwa [show rspOf m0 - BitVec.ofNat 64 finalizeStack = frAt m0 - 288#64 by
      apply BitVec.eq_of_toNat_eq
      have hfs : finalizeStack = 672 := rfl
      rw [hfs, toNat_sub_ofNat' (by have := g.s; unfold spAt at this; omega), hS288]
      rfl] at this
  have hk5 : Kept m.dmem st5.data.dmem := hm5.kept hwf
  refine call_then_elf hpc5 hkf ?pre fun st6 hpc6 hrsp6 hpost6 => ?_
  case pre =>
    simp only [KeccakFPre, keccakFStack]
    refine ⟨⟨by rw [hspN]; omega, by rw [hspN]; omega, fun i hi => ?_⟩,
      ⟨fun i hi => ?_, gr.nw, ?_⟩, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [show rspOf st5.data - BitVec.ofNat 64 288 = frAt m0 - 288#64 by
        rw [rspOf, hrsp5]]
      exact hk5 _ (hfr.kept _ (hmapS i (by omega)))
    · have hrcl : rcBytes.length = 192 := by
        rw [rcBytes, List.length_flatMap]
        simp only [length_wordBytes]
        rfl
      rw [hrcl] at hi
      rw [hm5.get?_mem0 hwf (fun hw => by
          have := written_lim (r := 0) (h := frAt m0) (sz := 392) rfl (lim := 352)
            (fun w hw => by rw [hl] at hw; exact finMem_bounds w hw) hw
          rw [toNat_add_ofNat' (by have := gr.nw; omega), hf] at this
          have := gr.rs
          omega),
        Env.ofMachine_mem0, rc_same g gr hfr hpro.same hi]
      exact hpre.2.1.1 i (by rw [hrcl]; exact hi)
    · show _ + 192 ≤ (stackBelow st5.data 288).toNat ∨ (stackBelow st5.data 288).toNat + 296 ≤ _
      rw [show stackBelow st5.data 288 = frAt m0 - 288#64 from hsb, hS288]
      have := gr.rs
      omega
    · rw [hrdi, add_ofNat_add]
      exact hk5 _ (hfr.kept _ (mapped_frame hpre _ (by omega)))
    · show (reg st5.data .rdi).toNat + 200 ≤ _
      rw [hrdi, hFo _ (by omega)]; omega
    · show (reg st5.data .rdi).toNat + 200 ≤ (stackBelow st5.data 288).toNat ∨
        (stackBelow st5.data 288).toNat + 296 ≤ (reg st5.data .rdi).toNat
      rw [hrdi, show stackBelow st5.data 288 = frAt m0 - 288#64 from hsb, hS288, hFo _ (by omega),
        hf]
      omega
    · show (reg st5.data .rdi).toNat + 200 ≤ rcAddr.toNat ∨
        rcAddr.toNat + 192 ≤ (reg st5.data .rdi).toNat
      rw [hrdi, hFo _ (by omega), hf]
      have := gr.rs
      omega
  obtain ⟨hbytesK, hsameK, hsavedK⟩ := hpost6
  have hrdi' : reg st5.data .rdi = _ := hrdi
  rw [hrdi', hxor] at hbytesK
  rw [hrdi', hsb, show keccakFStack = 288 from rfl] at hsameK
  have hfr6 : Fr m0 m1 st6.data := hfr.after_call hm5 hwf hbF rfl
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rfl)
    (fun p hw => by
      have := written_lim (r := 0) (h := frAt m0) (sz := 392) rfl (lim := 352)
        (fun w hw => by rw [hl] at hw; exact finMem_bounds w hw) hw
      exact chg_of_frame g (o := 0) (n := 352) (by decide) ⟨by simpa using this.1, by simpa using this.2⟩)
    hrsp6 hsavedK hsameK (fun p h => by
      rcases h with h | h
      · rw [inRange_iff (by rw [hFo _ (by omega)]; omega), hFo _ (by omega)] at h
        exact chg_of_frame g (o := 152) (n := 200) (by decide) h
      · unfold ChgF
        rw [inRange_iff (by rw [hS288]; omega), hS288] at h
        rw [inRange_iff (by rw [hS288]; omega), hS288]
        omega)
  refine Eventually.done _ ⟨by rw [hpc6]; rfl, hfr6, ?_⟩
  have := bytesOf_of_bytesAt hbytesK
  rwa [keccakF, length_stateBytes, ← keccakF] at this

end

end NativeRustcX64.Hasher.Finalize
