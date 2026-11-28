module

public import NativeRustcArm.SphincsVerify.Tree.Entry

/-!
# Region 5c: a layer's tree

From the fold's end (`AtFold`, the layer's root at `12864`): `b170` and `b172` copy the root to
`20032` (the next layer's message) and to hasher A, update spill `408` to the next layer's address,
then go back to the layer loop `b92` for the next layer (`l < 2`), or, after the last, `b173`
compares the root with `PK.root` and returns it through the epilogue. With `toFold` this is
`tree_spec : TreeSpec`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

/-! ## Comparing 16-byte values by their words -/

/-- A 64-bit value is determined by its 8 bytes. -/
theorem eq_of_bytes {x y : BitVec 64}
    (h : (List.range 8).map (byteOf x) = (List.range 8).map (byteOf y)) : x = y := by
  rw [bytes_word, bytes_word] at h
  have := congrArg (fun b ↦ littleEndianLane b 0) h
  simp only [littleEndianLane_wordBytes] at this
  have := congrArg UInt64.toBitVec this
  simpa using this

/-- **Two 16-byte values are equal** when their words are. -/
theorem beq_eq_words {a b : List UInt8}
    {A B C D : BitVec 64} (hA : (List.range 8).map (byteOf A) = a.take 8)
    (hC : (List.range 8).map (byteOf C) = a.drop 8) (hB : (List.range 8).map (byteOf B) = b.take 8)
    (hD : (List.range 8).map (byteOf D) = b.drop 8) : (a == b) = (A == B && C == D) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    subst h
    exact ⟨eq_of_bytes (hA.trans hB.symm), eq_of_bytes (hC.trans hD.symm)⟩
  · rintro ⟨rfl, rfl⟩
    rw [← List.take_append_drop 8 a, ← List.take_append_drop 8 b, ← hA, ← hC, ← hB, ← hD]

theorem pkRoot_at {r : Run} {m : MachineData} (h : r.Inputs m) :
    BytesAt m.dmem (r.off 464) r.pk.root := by
  have h1 := h.1
  rw [← List.take_append_drop 16 r.pkBytes] at h1
  have := bytesAt_append_right h1
  rwa [List.length_take, r.hpk, Run.off_add] at this

theorem length_pkRoot (r : Run) : r.pk.root.length = 16 := by
  show (r.pkBytes.drop 16).length = 16
  rw [List.length_drop, r.hpk]

/-! ## The region's end -/

variable [Host] {r : Run}

/-- **The layer loop's next turn, or the comparison**: from the fold's end. -/
theorem fold_end (hp : Placed code r.k) (hpre : r.Pre) {l : Nat} {e : List (List UInt8)}
    {m : MachineData} (h : AtFold r l e m) :
    Eventually (step1 Host.exe) (fun st ↦
      if l = 2 then r.Done (r.layerRoot l e == r.pk.root) st
      else st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b92Offset ∧ r.AtLayer (l + 1) (r.layerRoot l e) st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b170Offset⟩ := by
  obtain ⟨hB, hV⟩ := h
  have hl := hB.1
  rw [← layerRoot_eq r hl] at hV
  have hlen : (r.layerRoot l e).length = 16 := by
    rw [layerRoot_eq r hl]; exact length_foldUpTo r l e _
  have hIn := hB.2.2.1.1
  obtain ⟨h8, h16, h24, -, -, -, h400, -⟩ := hB.2.2.1.2
  have hld8 : (r.env m).load 0 8 8 = (r.addr 19009).toBitVec := load_word h8
  have hld16 : (r.env m).load 0 16 8 = (l + 1).toUInt64.toBitVec := load_word h16
  have hld24 : (r.env m).load 0 24 8 = (4656 + 1028 * (l + 1)).toUInt64.toBitVec := load_word h24
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then (hb170 hp) run_b170 hwf (match_base hpre hB) fun st1 hm1 hpc1 ↦ ?_
  have hpc1' : st1.pc = Host.addrOf (r.k + NativeRustcArm.Sphincs.SphincsVerify.b172Offset) := hpc1.trans (lbl_77 hp)
  refine exec_at (hb172 hp) (exec_after run_b170 run_b172) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hlo := load_lo (vars := fun _ ↦ 0) hV hlen
  have hhi := load_hi (vars := fun _ ↦ 0) hV hlen
  have hS20 : BytesAt st2.data.dmem (r.off 20032) (r.layerRoot l e) := by
    rw [← List.take_append_drop 8 (r.layerRoot l e)]
    refine bytesAt_cat (n := 8) (by simp [hlen]) (write_eval hm2 (o := 20032)
      (v := .load 0 12864 8) (by decide) (by decide) rfl hlo) ?_
    exact write_eval hm2 (o := 20040) (v := .load 0 12872 8) (by decide) (by decide) rfl hhi
  by_cases h2 : l = 2
  · subst h2
    simp only [↓reduceIte]
    have hpc2' := pc_cond (b := false) hpc2 (by sym_simp; rw [hld24]; decide)
    rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b172_next]
      at hpc2'
    refine exec_at (hb173 hp) (exec_after run_b172 run_b173) hwf hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
    have hF3 := Run.Frame.of_match r hpre hB.2.1 hm3 hwf rfl rfl (by decide)
    have hpc3' : st3.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b179Offset := hpc3.trans (lbl_84 hp)
    have hroot := pkRoot_at hIn
    have hcmp := beq_eq_words hlo hhi
      (load_lo (vars := fun _ ↦ 0) hroot (length_pkRoot r))
      (load_hi (vars := fun _ ↦ 0) hroot (length_pkRoot r))
    have hx0 := hm3.regs .X0 _ rfl
    sym_simp at hx0
    obtain ⟨d, pc⟩ := st3
    simp only at hpc3'
    subst hpc3'
    refine done_of_epilogue r hp hpre d hF3 ?_
    rw [hcmp]
    apply UInt64.toBitVec_inj.mp
    show (d.regs.getXReg .X0).toBitVec = _
    rw [hx0]
    generalize (r.env m).load 0 12864 8 = A
    generalize (r.env m).load 0 464 8 = B
    generalize (r.env m).load 0 12872 8 = C
    generalize (r.env m).load 0 472 8 = D
    cases (A == B) <;> cases (C == D) <;> rfl
  · simp only [h2, ↓reduceIte]
    have hl2 : l < 2 := by omega
    have hpc2' := pc_cond (b := true) hpc2 (by
      sym_simp; rw [hld24]; rcases l_cases hl with rfl | rfl | rfl <;> first | decide | omega)
    rw [Sym.ite_pos (rfl : true = true), lbl_32 hp] at hpc2'
    have hF2 := Run.Frame.of_match r hpre hB.2.1 hm2 hwf rfl rfl (by decide)
    have hIn2 : r.Inputs st2.data :=
      ⟨r.bytesAt_kept hpre hm2 hwf (by rw [r.hpk]; decide) hIn.1 (by rw [r.hpk]; decide),
        r.bytesAt_kept hpre hm2 hwf (by rw [Run.sig, length_sigMem r.hsig]; decide) hIn.2.1
          (by rw [Run.sig, length_sigMem r.hsig]; decide),
        r.bytesAt_kept hpre hm2 hwf (by rw [length_wordBytes]; decide) hIn.2.2
          (by rw [length_wordBytes]; decide)⟩
    have h408 : r.WordAt st2.data 408 (r.addr (5140 + 1028 * (l + 1))) := by
      refine write_eval hm2 (o := 408) (n := 8) (v := .bin .add .W64 (.ptr 0 484) (.load 0 24 8))
        (w := r.off (5140 + 1028 * (l + 1))) (by decide) (by decide) ?_ (bytes_word _)
      sym_simp
      simp only [hld24, Run.env_base]
      show r.base + BitVec.ofInt 64 484 + _ = r.base + BitVec.ofNat 64 _
      refine (BitVec.add_assoc _ _ _).trans (congrArg (r.base + ·) ?_)
      have h12 : ∀ n : Nat, n < 2 ^ 32 → BitVec.ofInt 64 484 + n.toUInt64.toBitVec =
          BitVec.ofNat 64 (484 + n) := fun n hn ↦ by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat',
          BitVec.toNat_ofNat]
        rw [show BitVec.ofInt 64 484 = BitVec.ofNat 64 484 from rfl, BitVec.toNat_ofNat]
        omega
      exact (h12 _ (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
    refine .done _ ⟨hpc2', by omega, hlen, hF2, hIn2,
      (hm2.regs .X10 _ rfl).trans hld16, hm2.regs .X8 _ rfl,
      (hm2.regs .X11 _ rfl).trans hld24, hm2.regs .X12 _ rfl, hm2.regs .X23 _ rfl,
      hm2.regs .X13 _ rfl, (hm2.regs .X22 _ rfl).trans (eval_ptr 15936),
      hm2.regs .X19 _ rfl, (hm2.regs .X21 _ rfl).trans (eval_ptr 19208),
      (hm2.regs .X24 _ rfl).trans hld8, (hm2.regs .X25 _ rfl).trans (eval_ptr 8840),
      (hm2.regs .X27 _ rfl).trans (eval_ptr 19008), hS20,
      r.bytesAt_kept hpre hm2 hwf (by rw [length_wordBytes]; decide) h8
        (by rw [length_wordBytes]; decide),
      r.bytesAt_kept hpre hm2 hwf (by rw [length_wordBytes]; decide) h400
        (by rw [length_wordBytes]; decide),
      h408⟩

/-- **Region 5c, a layer's tree**: from `b134`, layer `l`'s chain ends `e`, to the next layer at
`b92` with the layer's root, or, after the last, returned the comparison with `PK.root`. -/
theorem tree_spec : TreeSpec := by
  intro l e r hp hc hpre m h
  exact Eventually.bind (toFold hp hc hpre h) (at_pc fun m h ↦ fold_end hp hpre h)

end

end NativeRustcArm.SphincsVerifyProof.Tree
