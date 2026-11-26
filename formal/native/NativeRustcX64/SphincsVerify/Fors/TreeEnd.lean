module

public import NativeRustcX64.SphincsVerify.Fors.NodeTail

/-!
# A FORS tree's end (x86-64)

At a tree's end (`AtRoot`, `b87` at directive 1078): `b87` stores the root at `12396 + 16 c`,
advances RSI and points R14 at `PK.seed`; on to the next tree's head (`AtTree r (c + 1)` at `b49`)
or after the 24th to `b88` (`AtForsKey`) (**`tree_end`**). `b87` runs in the frame with a window
(`Run.envW`): region 0 the frame's first 12396 bytes, region 2 the root's slot.
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash
open NativeRustcX64.Sphincs.SphincsVerify

public section

variable [Host] {r : Run}

omit [Host] in
/-- The root slot's alias: RSP plus `16 c` is the slot less 12396. -/
theorem rootAlias [Labels] {m : MachineData} {c : Nat} (hpre : r.Pre)
    (h13 : r.WordAt m 88 c.toUInt64) :
    rootSym.eval (r.envW 12396 (12396 + 16 * c) m (fun _ ↦ 0) 0) =
      (r.envW 12396 (12396 + 16 * c) m (fun _ ↦ 0) 0).base 2 + BitVec.ofInt 64 (-12396) := by
  have hb := r.base_toNat hpre
  show (r.base + BitVec.ofInt 64 0) + BinOp.apply .shl .W64
    ((r.envW 12396 (12396 + 16 * c) m (fun _ ↦ 0) 0).load 0 88 8)
    (BitVec.ofNat 64 4) = r.off (12396 + 16 * c) + BitVec.ofInt 64 (-12396)
  rw [load_wordW h13, Chains.toBitVec_toUInt64, shl4 c, show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.add_zero, Run.off,
    show BitVec.ofInt 64 (-12396) = -BitVec.ofNat 64 12396 by decide,
    show BitVec.ofNat 64 (12396 + 16 * c) = BitVec.ofNat 64 12396 + BitVec.ofNat 64 (16 * c) from
      BitVec.ofNat_add _ _]
  bv_omega

/-- **A tree's end**: from `AtRoot r c` at `b87`, the next tree's head or `b88`. -/
theorem tree_end (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {c : Nat}
    {m : MachineData} (h : AtRoot r c m) :
    Eventually (step1 Host.exe) (fun st ↦ (c + 1 < 24 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b49Offset ∧
      AtTree r (c + 1) st.data) ∨ (c + 1 = 24 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b88Offset ∧ r.AtForsKey st.data))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b87Offset⟩ := by
  obtain ⟨⟨hF, hB⟩, h13, h12, h15, hbp, hroot, hbx⟩ := h
  have hc24 := hB.hc
  have h13' := load_wordW (n0 := 12396) (o2 := 12396 + 16 * c) (vars := fun _ ↦ 0) (ret := 0) h13
  have hwf := r.wfW hpre hF.2.2.2 (n0 := 12396) (o2 := 12396 + 16 * c) (by omega) (by omega)
    (fun _ ↦ 0) 0
  have hm : Match (r.envW 12396 (12396 + 16 * c) m (fun _ ↦ 0) 0) s96 m :=
    r.matchW hF (known := []) (bounds := []) (aliases := [(rootSym, 2, -12396)]) trivial trivial
      ⟨rootAlias hpre h13, trivial⟩
  refine Chains.blk r hp b87_in_code (List.cons_ne_nil _ _) run_b87 hwf (fun _ h ↦ nomatch h) hm
    fun st₁ hm₁ hpc₁ ↦ .done _ ?_
  change Match _ s96e st₁.data at hm₁
  have hww : winWrites s96e 12396 = true := by decide +kernel
  have hF₁ := Run.Frame.of_matchW r hpre hF (by decide) (by omega) hm₁ hwf rfl hww
  have kw := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (hd : o + bs.length ≤ 12396 + 16 * c ∨ 12396 + 16 * c + 16 ≤ o)
      (h : BytesAt m.dmem (r.off o) bs) (hn : noWriteW s96e o bs.length = true) ↦
    r.bytesAt_keptW hpre (by omega) hm₁ hwf ho hd h hn
  have hrl := length_rootsUpTo r (c := c) (by omega)
  have hsig := Chains.length_sigMemR r
  have hroots : BytesAt st₁.data.dmem (r.off 12396) (rootsUpTo r (c + 1)) := by
    rw [rootsUpTo_succ]
    refine Chains.BytesAt.cat (kw (by rw [hrl]; omega) (by rw [hrl]; omega) hB.roots
      (noWriteW_of_winWrites hww _)) ?_ (by rw [hrl])
    have := write16 hm₁ (j := 2) rfl (o := 0) (by decide) (v₁ := .load 0 8296 8)
      (v₂ := .load 0 8304 8) (by decide +kernel) (by decide +kernel) rfl rfl
      (Digest.length_forsRoot r c) hroot
    exact Chains.BytesAt.of_add_zero this
  have W := NativeRustc.length_wordBytes
  have hI : r.Inputs st₁.data :=
    ⟨kw (by flen) (by flen) hB.inputs.1 (by rw [Chains.length_pkBytes]; decide +kernel),
      kw (by rw [hsig]; omega) (by rw [hsig]; omega) hB.inputs.2 (by rw [hsig]; decide +kernel)⟩
  have g176 := kw (by flen) (by flen) hB.w176 (by rw [W]; decide +kernel)
  have g568 := kw (by flen) (by flen) hB.w568 (by rw [W]; decide +kernel)
  have g80 := kw (by flen) (by flen) hB.w80 (by rw [length_be64']; decide +kernel)
  have g60 := kw (by flen) (by flen) hB.w60 (by rw [length_be32']; decide +kernel)
  have gl := kw (by flen) (by flen) hB.leaves (by rw [length_leavesBytes]; decide +kernel)
  have r15 : reg st₁.data .r13 = reg m .r13 := hm₁.regs .r13 _ rfl
  have rbp : reg st₁.data .rbp = reg m .rbp := hm₁.regs .rbp _ rfl
  have hpc := Chains.pc_cond hpc₁
  have hcnd : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.load 0 88 8) (.lit 1)) (.lit 24))).eval
      (r.envW 12396 (12396 + 16 * c) m (fun _ ↦ 0) 0) = decide (c + 1 < 24) := by
    show (!(CmpOp.apply .eq .W64 (BinOp.apply .add .W64 ((r.envW 12396 (12396 + 16 * c) m (fun _ ↦ 0) 0).load 0 88 8) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 24))) = _
    rw [h13', Chains.toBitVec_toUInt64]
    interval_cases c <;> decide
  rw [hcnd] at hpc
  by_cases hlt : c + 1 < 24
  · simp only [hlt, decide_true, ite_true] at hpc
    rw [Chains.labelAt r hp b49_in_code rfl] at hpc
    refine Or.inl ⟨hlt, hpc, ⟨hF₁, hlt, hI, g176, g568, g80, g60, gl, hroots⟩,
      ?_, ?_, ?_, ?_, ?_, Chains.regIs_reg hm₁ rfl hbx, ?_⟩
    · unfold Run.RegIs reg
      rw [hm₁.regs .rsi _ rfl]
      show BinOp.apply .add .W64 ((r.envW 12396 (12396 + 16 * c) m (fun _ ↦ 0) 0).load 0 88 8) (BitVec.ofNat 64 1) = _
      rw [h13', Chains.toBitVec_toUInt64]
      simp only [BinOp.apply, low_W64, ext_W64]
      exact (BitVec.ofNat_add c 1).symm
    · exact (hm₁.regs .r12 _ rfl).trans h12
    · unfold Run.RegIs reg
      rw [hm₁.regs .r14 _ rfl]
      rfl
    · rw [r15]; exact h15
    · rw [rbp]; exact hbp
    · unfold Run.RegIs reg
      rw [hm₁.regs .r15 _ rfl]
      rfl
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false] at hpc
    have h24 : c + 1 = 24 := by omega
    refine Or.inr ⟨h24, hpc, hF₁, hI, by rw [r15]; exact h15, by rw [rbp]; exact hbp, ?_, g568,
      g176⟩
    rw [← h24]
    exact hroots

end

end NativeRustcX64.SphincsVerifyProof.Fors
