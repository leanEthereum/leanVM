module

public import NativeRustcX64.Hasher.FinalizeA

/-!
# `Hasher::finalize` (x86-64): the padding

From `Stage2`, `b5a` (`xorb $1, 8(%rsp,%r14)`) XORs `PAD_FIRST` into the byte after the buffered
ones (`Stage3`, `stage3_spec`); the byte of the state after `b5b`'s `PAD_LAST` and lane XORs
(`b5b_byte`).
-/

namespace NativeRustcX64.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Finalize

@[expose] public section

/-- The frame's byte `i` in `m`. -/
def frByte (m0 m : MachineData) (i : Nat) : UInt8 :=
  (m.dmem.get? (frAt m0 + BitVec.ofNat 64 i)).getD 0

/-- After `PAD_FIRST`: the buffered bytes and zeros, `PAD_FIRST` after them, then the state. -/
structure Stage3 (m0 m1 m : MachineData) : Prop where
  fr : Fr m0 m1 m
  bytes : ∀ i < 336, frByte m0 m (16 + i) = if i < 136 then
    ((if i < lenOf m0 then (tailOf m0).getD i 0 else 0) ^^^ (if i = lenOf m0 then 1 else 0))
    else ((hbytes m0).take 200).getD (i - 136) 0

end

public section

/-- The writes `[padW]` give byte `j` of the frame. -/
theorem findWrite_padW (j : Nat) : findWrite 0 j [padW] =
    if j = 151 then some (padW.v, 0) else none := by
  by_cases h : j = 151
  · subst h; rfl
  · simp only [findWrite, padW, h, ↓reduceIte]
    rw [ite_neg' (by omega)]

variable [Host] {k : Nat}

set_option linter.unusedSimpArgs false in
/-- **`PAD_FIRST`.** -/
theorem stage3_spec (hp : Placed code k) {m0 m1 m : MachineData} (hpre : FinalizePre m0)
    (hs2 : Stage2 m0 m1 m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf (k + (NativeRustcX64.Common.Finalize.b5Offset + b5a.length)) ∧ Stage3 m0 m1 st.data)
      ⟨m, Host.addrOf (k + NativeRustcX64.Common.Finalize.b5Offset)⟩ := by
  have g := geo_of hpre
  have hf := frAt_toNat g
  have hs := g.s
  have hs8 := g.s8
  have hL := lenOf_lt hpre
  have hfr := hs2.fr
  have hmapF : Mapped m.dmem (frAt m0) 392 := fun i hi => hfr.kept _ (mapped_frame hpre i hi)
  have hFnw : (frAt m0).toNat + 392 ≤ 2 ^ 64 := by rw [hf]; omega
  have hpos : (frAt m0 + BitVec.ofNat 64 (16 + lenOf m0)).toNat = (frAt m0).toNat + 16 + lenOf m0 :=
    by rw [toNat_add_ofNat' (by omega)]; omega
  have hwf : (Env.ofMachine m [(frAt m0 + BitVec.ofNat 64 (16 + lenOf m0), 1)]).WF :=
    Env.wf_of ⟨⟨fun i hi => by rw [add_ofNat_add]; exact hmapF _ (by omega),
      by show _ + 1 ≤ _; rw [hpos]; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hb : (Env.ofMachine m [(frAt m0 + BitVec.ofNat 64 (16 + lenOf m0), 1)]).base 0 =
      frAt m0 + BitVec.ofNat 64 (16 + lenOf m0) := Env.base_ofMachine m _ _ _ rfl
  have hma : Match (Env.ofMachine m [(frAt m0 + BitVec.ofNat 64 (16 + lenOf m0), 1)]) padS m :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      simp only [padAddr, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hb]
      have hrsp := hfr.rsp
      unfold reg at hrsp
      rw [hrsp]
      apply BitVec.eq_of_toNat_eq
      have h14 := hs2.r14
      unfold reg at h14
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h14,
        show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
      omega, trivial⟩
  refine exec_then (hb5a hp) run_b5a hwf (fun _ h => nomatch h) hma fun st hm' hpc => ?_
  have hl := b5a_mem
  rw [after_eq run_b5a] at hl
  have hmem : ∀ p, ¬p = frAt m0 + BitVec.ofNat 64 (16 + lenOf m0) →
      st.data.dmem.get? p = m.dmem.get? p := fun p hp =>
    hm'.get?_mem0 hwf fun hw => hp (by
      have := written_lim (r := 0) (h := frAt m0 + BitVec.ofNat 64 (16 + lenOf m0)) (sz := 1)
        rfl (lim := 1) (fun w hw => by
          rw [hl] at hw; simp only [List.mem_singleton] at hw; subst hw; decide) hw
      apply BitVec.eq_of_toNat_eq
      omega)
  have hpad : st.data.dmem.get? (frAt m0 + BitVec.ofNat 64 (16 + lenOf m0)) =
      some ((m.dmem.get? (frAt m0 + BitVec.ofNat 64 (16 + lenOf m0))).getD 0 ^^^ 1) := by
    have := hm'.mem 0 _ 1 rfl 0 (by omega)
    rw [BitVec.add_zero] at this
    rw [this, hl]
    simp only [memByte, findWrite, Nat.le_refl, Nat.zero_add, Nat.zero_lt_one, and_self,
      ↓reduceIte, Nat.sub_zero, Sym.eval, true_and]
    rw [byteOf_xorW8, byteOf_load (by omega) (by omega), hb, Env.ofMachine_mem0,
      Nat.add_zero, BitVec.add_zero, byteOf_ofNat_lt 1 (by omega)]
    rfl
  have hfr' : Fr m0 m1 st.data := hfr.after_block hma hm' hwf
    (fun r hr => ⟨.reg r, by
      have h5 := after_eq run_b5a
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by rw [← h5]; rfl⟩⟩)
    (fun p hw => by
      have := written_lim (r := 0) (h := frAt m0 + BitVec.ofNat 64 (16 + lenOf m0)) (sz := 1)
        rfl (lim := 1) (fun w hw => by
          rw [hl] at hw; simp only [List.mem_singleton] at hw; subst hw; decide) hw
      exact chg_of_frame g (o := 16 + lenOf m0) (n := 1) (by omega) (by omega))
  refine Eventually.done _ ⟨by rw [hpc]; rfl, hfr', fun i hi => ?_⟩
  have h2 := hs2.bytes
  have hTl := length_tailOf hL
  have hget : frByte m0 m (16 + i) = ((tailOf m0 ++ List.replicate (136 - lenOf m0) 0) ++
      (hbytes m0).take 200).getD i 0 := by
    rw [← h2, getD_bytesOf _ _ hi, add_ofNat_add]
    rfl
  rw [getD_stage2 _ _ hTl (by omega)] at hget
  unfold frByte at hget ⊢
  by_cases hi2 : i = lenOf m0
  · subst hi2
    rw [hpad, Option.getD_some, hget, ite_neg' (by omega), ite_pos' (by omega),
      ite_pos' (show lenOf m0 < 136 by omega), ite_neg' (by omega), ite_pos' rfl]
  · rw [hmem _ fun h => hi2 (by
      have := congrArg BitVec.toNat h
      rw [hpos, toNat_add_ofNat' (by omega)] at this
      omega), hget, ite_neg' hi2, UInt8.xor_zero]
    by_cases h1 : i < lenOf m0
    · rw [ite_pos' h1, ite_pos' (by omega), ite_pos' h1]
    · rw [ite_neg' h1, ite_neg' h1]

section
omit [Host]
variable [Labels]

/-- **A byte of the state after `b5b`**, from the frame's bytes before it. -/
theorem b5b_byte {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) (hwf : env.WF)
    {fr : BitVec 64} (hr : env.regions[0]? = some (fr, 392)) (hS : S.mem = finMem) {j : Nat}
    (hj : j < 200) :
    (m.dmem.get? (fr + BitVec.ofNat 64 (152 + j))).getD 0 =
      if j < 136 then (env.mem0.get? (fr + BitVec.ofNat 64 (152 + j))).getD 0 ^^^
        ((env.mem0.get? (fr + BitVec.ofNat 64 (16 + j))).getD 0 ^^^ (if j = 135 then 0x80 else 0))
      else (env.mem0.get? (fr + BitVec.ofNat 64 (152 + j))).getD 0 := by
  have hb : env.base 0 = fr := Env.base_eq hr
  rw [hm.mem 0 fr 392 hr (152 + j) (by omega), hS]
  unfold memByte
  rw [findWrite_finMem j hj]
  by_cases h1 : j < 128
  · rw [ite_pos' h1, ite_pos' (by omega)]
    simp only [Option.getD_some, laneW, Sym.eval]
    rw [byteOf_xorW64, byteOf_load (by omega) (by omega), byteOf_load (by omega) (by omega), hb,
      show 152 + 8 * (j / 8) + j % 8 = 152 + j by omega,
      show 16 + 8 * (j / 8) + j % 8 = 16 + j by omega, ite_neg' (by omega), UInt8.xor_zero]
  · rw [ite_neg' h1]
    by_cases h2 : j < 136
    · rw [ite_pos' h2, ite_pos' h2]
      simp only [Option.getD_some, lane16, Sym.eval]
      rw [byteOf_xorW64, byteOf_load (by omega) (by omega), hb, eval_assemble hb,
        byteOf_ofNat_ofBytes _ (by simp), show 280 + (j - 128) = 152 + j by omega]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range
        (show j - 128 < 8 by omega), Option.map_some, Option.getD_some]
      have hmb := memByte_eq (ws := [padW]) hwf hr (j := 144 + (j - 128)) (by omega)
      unfold memByte at hmb
      rw [findWrite_padW] at hmb
      by_cases h3 : j = 135
      · subst h3
        rw [ite_pos' rfl] at hmb
        simp only [Option.some.injEq] at hmb
        rw [← hmb, ite_pos' rfl]
        simp only [padW, Sym.eval]
        rw [byteOf_xorW8, byteOf_load (by omega) (by omega), hb]
        rfl
      · rw [ite_neg' (by omega)] at hmb
        rw [ite_neg' h3, UInt8.xor_zero, show 144 + (j - 128) = 16 + j by omega] at *
        have : (env.mem0.get? (fr + BitVec.ofNat 64 (16 + j))).isSome :=
          hwf.mapped 0 fr 392 hr (16 + j) (by omega)
        revert hmb this
        cases env.mem0.get? (fr + BitVec.ofNat 64 (16 + j)) <;> simp
        exact fun h => h.symm
    · rw [ite_neg' h2, ite_neg' h2]

end

end

end NativeRustcX64.Hasher.Finalize
