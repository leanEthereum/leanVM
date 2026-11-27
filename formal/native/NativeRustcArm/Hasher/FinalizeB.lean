module

public import NativeRustcArm.Hasher.FinalizeA

/-!
# `Hasher::finalize`: the padding and the permutation

From `Stage2`, `b4a` XORs `PAD_FIRST` into the byte after the buffered ones (`Stage3`); `b4b` XORs
`PAD_LAST` into the block's last byte and the block's 17 lanes into the state's, the final block
(`finalBlock`) absorbed (`xorBlock`), and calls `keccak_f`: the state is `absorb` of the hasher's
state and the final block (`Stage4`, `stage4_spec`).
-/

namespace NativeRustcArm.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Finalize NativeRustcArm

@[expose] public section

/-- The frame's byte `i` in `m`. -/
def frByte (m0 m : MachineData) (i : Nat) : UInt8 :=
  (m.dmem.get? (frAt m0 + BitVec.ofNat 64 i)).getD 0

/-- After `PAD_FIRST`: the state, then the buffered bytes and zeros, `PAD_FIRST` after them. -/
structure Stage3 (m0 m1 m : MachineData) : Prop where
  fr : Fr m0 m1 m
  bytes : ∀ i < 336, frByte m0 m i = if i < 200 then ((hbytes m0).take 200).getD i 0 else
    (if i - 200 < lenOf m0 then (tailOf m0).getD (i - 200) 0 else 0) ^^^
      (if i = 200 + lenOf m0 then 1 else 0)

/-- After `keccak_f`: the state absorbed the final block. -/
structure Stage4 (m0 m1 m : MachineData) : Prop where
  fr : Fr m0 m1 m
  state : bytesOf m.dmem (frAt m0) 200 =
    absorb ((hbytes m0).take 200) (finalBlock (tailOf m0))

end

public section

theorem byteOf_eorW64 (x y : BitVec 64) (t : Nat) :
    byteOf (BinOp.apply .eor .W64 x y) t = byteOf x t ^^^ byteOf y t := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact byteOf_xor x y t

theorem byteOf_ofNat_lt (c : Nat) (hc : c < 256) : byteOf (BitVec.ofNat 64 c) 0 = UInt8.ofNat c := by
  simp only [byteOf, BitVec.toNat_ofNat, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  congr 1
  omega

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **`PAD_FIRST`.** -/
theorem stage3_spec (hp : PlacedIn code sec k) {m0 m1 m : MachineData} (hpre : FinalizePre m0)
    (hs2 : Stage2 m0 m1 m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => st.pc = ElfHost.addrOf sec (k + (NativeRustcArm.Common.Finalize.b4Offset + b4a.length)) ∧ Stage3 m0 m1 st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcArm.Common.Finalize.b4Offset)⟩ := by
  have g := geo_of hpre
  have hf := frAt_toNat g
  have hs := g.s
  have hL := lenOf_lt hpre
  have hfr := hs2.fr
  have hmapF : Mapped m.dmem (frAt m0) 384 := fun i hi => hfr.kept _ (by
    have := hpre.1.2.2 (192 + i) (by show 192 + i < 576; omega)
    rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 finalizeStack + BitVec.ofNat 64 (192 + i) =
      frAt m0 + BitVec.ofNat 64 i from stack_frame] at this)
  have hFnw : (frAt m0).toNat + 384 ≤ 2 ^ 64 := by rw [hf]; have := (spAt m0).isLt; omega
  have hpos : (frAt m0 + BitVec.ofNat 64 (200 + lenOf m0)).toNat = (frAt m0).toNat + 200 + lenOf m0 :=
    by rw [toNat_add_ofNat' (by omega)]; omega
  have hwf : (Env.ofMachine m [(frAt m0 + BitVec.ofNat 64 (200 + lenOf m0), 1)]).WF :=
    Env.wf_of ⟨⟨fun i hi => by rw [add_ofNat_add]; exact hmapF _ (by omega),
      by show _ + 1 ≤ _; rw [hpos]; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hb : (Env.ofMachine m [(frAt m0 + BitVec.ofNat 64 (200 + lenOf m0), 1)]).base 0 =
      frAt m0 + BitVec.ofNat 64 (200 + lenOf m0) := Env.base_ofMachine m _ _ rfl
  have hma : Match (Env.ofMachine m [(frAt m0 + BitVec.ofNat 64 (200 + lenOf m0), 1)]) padS m :=
    match_ofMachine ⟨rfl, by simp, trivial⟩ rfl trivial trivial trivial ⟨by
      simp only [padAddr, Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64, Env.ofMachine_regs,
        hb, hs2.x21, BitVec.apply_mem_extend, BitVec.unsigned]
      rw [hs2.x20, BitVec.ofInt_natCast]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt, MemWidth.bits]
      omega, trivial⟩
  refine exec_then_elf (hb4a hp) run_b4a hwf hma fun st hm' hpc => ?_
  have hl := b4a_mem
  rw [after_eq run_b4a] at hl
  have hmem : ∀ p, ¬p = frAt m0 + BitVec.ofNat 64 (200 + lenOf m0) →
      st.data.dmem.get? p = m.dmem.get? p := fun p hp =>
    hm'.get?_mem0 hwf fun hw => hp (by
      have := written_hasher (fun w hw => by rw [hl] at hw; simp at hw; subst hw; simp) hw
      apply BitVec.eq_of_toNat_eq
      omega)
  have hpad : st.data.dmem.get? (frAt m0 + BitVec.ofNat 64 (200 + lenOf m0)) =
      some ((m.dmem.get? (frAt m0 + BitVec.ofNat 64 (200 + lenOf m0))).getD 0 ^^^ 1) := by
    have := hm'.mem 0 _ 1 rfl 0 (by omega)
    rw [BitVec.add_zero] at this
    rw [this, hl]
    simp only [memByte, findWrite, Nat.le_refl, Nat.zero_add, Nat.zero_lt_one, and_self, ↓reduceIte,
      Nat.sub_zero, Sym.eval, true_and]
    rw [byteOf_eorW32, byteOf_load (by omega) (by omega), hb, Env.ofMachine_mem0,
      Nat.add_zero, BitVec.add_zero, byteOf_ofNat_lt 1 (by omega)]
    rfl
  have hfr' : Fr m0 m1 st.data := hfr.update
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hma hm' rfl rfl)
    (Match.sp_eq hma hm' rfl)
    (fun p hp => hmem p fun h => hp (Or.inl (by
      rw [h, inRange_iff (by omega), hpos]; omega)))
    (hm'.kept hwf)
  refine Eventually.done _ ⟨by rw [hpc]; rfl, hfr', fun i hi => ?_⟩
  have h2 := hs2.bytes
  have hTl := length_tailOf hL
  have hget : frByte m0 m i = ((hbytes m0).take 200 ++
      (tailOf m0 ++ List.replicate (136 - lenOf m0) 0)).getD i 0 := by
    rw [← h2, getD_bytesOf _ _ hi]
    rfl
  rw [getD_stage2 _ _ (by simp [length_hbytes]) hTl] at hget
  unfold frByte at hget ⊢
  by_cases hi2 : i = 200 + lenOf m0
  · subst hi2
    rw [hpad, Option.getD_some, hget, ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_pos' rfl]
  · rw [hmem _ fun h => hi2 (by
      have := congrArg BitVec.toNat h
      rw [hpos, toNat_add_ofNat' (by omega)] at this
      omega), hget, ite_neg' hi2, UInt8.xor_zero]
    by_cases h1 : i < 200
    · rw [ite_pos' h1, ite_pos' h1]
    · rw [ite_neg' h1, ite_neg' h1]
      by_cases h3 : i < 200 + lenOf m0
      · rw [ite_pos' h3, ite_pos' (by omega)]
      · rw [ite_neg' h3, ite_neg' (by omega)]

end

end NativeRustcArm.Hasher.Finalize
