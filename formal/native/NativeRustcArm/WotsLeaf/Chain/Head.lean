module

public import NativeRustcArm.WotsLeaf.Chain.Ends

/-!
# A chain: its head, its steps, its end

`b14` reads chain `i`'s digit `d` (the codeword's byte `380 + i`) and value (the chain values'
bytes `16 i ..`, region 1) into `1384`; a digit above 2 goes straight to `b13`, otherwise the
`3 - d` steps and `b41` to `b13`, which stores the chain's end (`seg_b14`): chain `i`'s end is
`Run.chainEnd`, `chain` from its digit.
-/

namespace NativeRustcArm.WotsLeafProof.Chain

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

@[expose] public section

/-- Chain `i`'s end for the codeword `x`, as `wots_leaf` computes it. -/
def _root_.NativeRustcArm.WotsLeafProof.Run.chainEnd (r : Run) (x : List UInt8) (i : Nat) :
    List UInt8 :=
  chain r.pp r.layer r.e i (x.getD i 0).toNat (3 - (x.getD i 0).toNat) (r.values.getD i [])

end

public section

theorem memExt0 (y : BitVec 64) : UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 y = y := by
  simp [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned]

theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he ↦ h (by
      have := congrArg BitVec.toNat he
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
        at this)
    simp [h, this]

theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem digit_cond (d : Nat) : (!decide (d < 2) && !decide (d = 2)) = decide (2 < d) := by
  by_cases h1 : d < 2
  · simp [h1, show ¬2 < d by omega]
  · by_cases h2 : d = 2
    · subst h2
      decide
    · simp [h1, h2, show 2 < d by omega]

theorem shl4 {i : Nat} (hi : i < 2 ^ 59) :
    BitVec.ofNat 64 i <<< 4 = BitVec.ofNat 64 (16 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  congr 1
  omega

theorem drop_take_one {x : List UInt8} {i : Nat} (hi : i < x.length) :
    (x.drop i).take 1 = [x.getD i 0] := by
  rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem load_one [Labels] {env : Env} {r off : Nat} {b : UInt8}
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 off) [b]) :
    env.load r off 1 = BitVec.ofNat 64 b.toNat := by
  rw [Env.load_of_bytesAt (n := 1) rfl h]
  show BitVec.ofInt 64 (0 * 256 + (b.toNat : Int)) = _
  simp

/-- Chain `i`'s value: the bytes at entry of the chain values' `16 i ..`. -/
theorem values_getD (r : Run) {i : Nat} (hi : i < 58) :
    r.values.getD i [] =
      bytesOf r.m0.dmem (r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i)) 16 := by
  simp [Run.values, WotsLeafPre.values, List.getD_eq_getElem?_getD, hi]

theorem length_values_getD (r : Run) {i : Nat} (hi : i < 58) :
    (r.values.getD i []).length = 16 := by
  rw [values_getD r hi, length_bytesOf]

theorem length_chainEnd (r : Run) (x : List UInt8) {i : Nat} (hi : i < 58) :
    (r.chainEnd x i).length = 16 :=
  length_chain _ _ _ _ _ _ (length_values_getD r hi)

variable [NativeRustcArm.Host] {r : Run}

/-- **`b14`**: chain `i`'s digit and value; then its steps and its end stored. -/
theorem seg_b14 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {i : Nat} (hi : i < 58) {R : MachineState → Prop} {m : MachineData}
    (hA : r.AtChain x i E m)
    (cont : ∀ m', r.AtChain x (i + 1) (E ++ r.chainEnd x i) m' →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if i + 1 = 58 then r.pc NativeRustcArm.Xmss.WotsLeaf.b44Offset else r.pc NativeRustcArm.Xmss.WotsLeaf.b14Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b14Offset⟩ := by
  obtain ⟨-, hEl, hKc, h28, h9, h19, h21, h23, h20, h22⟩ := hA
  rw [chainSlots_eq] at hKc
  have hK : r.CK x E m := ⟨⟨hKc.1, allOf_left hKc.2⟩, (allOf_right hKc.2).1.2.2, by omega⟩
  have hx := CK.length_x hK
  have hF := hK.1.1
  have hin := Run.Input.sub r (r.pre_values hpre) (o := 16 * i) (n' := 16) (by omega) (by omega)
  have hwf : (r.envR m [(r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i), 16)]).WF := by
    refine r.frame_wfR hpre hF (rest := [(r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i), 16)])
      ⟨⟨r.input_mapped hF.2.2.2.2 hin, hin.2.1⟩, trivial⟩ ?_ (List.pairwise_singleton _ _) _
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    have := r.apart_input hpre (a := 0) (n' := 2752) (by decide) hin
    rwa [Run.off_zero] at this
  have hm := r.match_frameR hpre hF (vars := fun _ ↦ 0)
    (rest := [(r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i), 16)]) (srest := [(16, false)])
    (known := (.X29, .ptr 0 2656) :: (.X9, .ptr 0 380) :: keptK) (labels := [])
    (bounds := [(.reg .X28, 58)]) (aliases := [(.bin .add .W64 (.reg .X22) (sh4 .X28), 1, 0)])
    ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩
    ⟨hF.2.1.trans (eval_ptr0R m _ _ 2656).symm, h9.trans (eval_ptr0R m _ _ 380).symm, h19,
      h21.trans (eval_ptr0R m _ _ 1976).symm, h23.trans (eval_ptr0R m _ _ 1632).symm, trivial⟩
    trivial
    ⟨by
      show (m.regs.getXReg .X28).toBitVec.toNat < 58
      rw [h28, BitVec.toNat_ofNat]
      omega, trivial⟩
    ⟨by
      show BinOp.apply .add .W64 (m.regs.getXReg .X22).toBitVec
        (UnOp.apply (.shift .LSL 4) .W64 (m.regs.getXReg .X28).toBitVec) =
          r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 0
      rw [h22, h28]
      sym_simp
      rw [shl4 (by omega)]
      simp, trivial⟩
  refine blk r hp b14_in_code (List.cons_ne_nil _ _) run_b14 hwf hm fun st hm1 hpc ↦ ?_
  have hK1 := CK.of_blockR hpre hK hm1 hwf (by decide +kernel) (by decide +kernel) rfl rfl
    (by decide +kernel)
  have hv := length_values_getD r hi
  have hval0 : BytesAt m.dmem (r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 0) (r.values.getD i []) := by
    rw [values_getD r hi]
    simpa using r.input_bytes hpre hF hin
  have hcell : BytesAt st.data.dmem (r.off 1384) (r.values.getD i []) :=
    copy16_gen hm1 (k := 0) (b := r.base) rfl (o := 1384) (by decide) (k' := 1) (o' := 0)
      (by decide +kernel) (by decide +kernel) hv hval0
  have hdig : BytesAt m.dmem (r.off (380 + i)) [x.getD i 0] := by
    have := BytesAt.slice (CK.slot380 hK) i 1
    rwa [drop_take_one (by omega), r.off_add] at this
  have hD : (Sym.loadx 0 380 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X28)) 1).eval
      (r.envR m [(r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i), 16)]) =
        BitVec.ofNat 64 (x.getD i 0).toNat := by
    show Env.load _ 0 (380 + (UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64
      (m.regs.getXReg .X28).toBitVec).toNat) 1 = _
    rw [memExt0, h28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact load_one hdig
  have hR1 : r.SRegs st.data (x.getD i 0).toNat i := by
    refine ⟨regIs_lit hm1 rfl, regIs_reg hm1 rfl h20, regIs_ptrR hm1 rfl, regIs_ptrR hm1 rfl, ?_,
      regIs_reg hm1 rfl h28⟩
    unfold Run.RegIs
    rw [hm1.regs .X22 _ rfl]
    exact hD
  have hcond : (SBool.and
      (.not (.cmp .ult .W64 (.loadx 0 380 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X28)) 1)
        (.lit 2)))
      (.not (.cmp .eq .W64 (.loadx 0 380 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X28)) 1)
        (.lit 2)))).eval (r.envR m [(r.m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i), 16)]) =
      decide (2 < (x.getD i 0).toNat) := by
    show (!(CmpOp.apply .ult .W64 (Sym.eval _ (.loadx 0 380 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64
      (.reg .X28)) 1)) (BitVec.ofNat 64 2)) && !(CmpOp.apply .eq .W64 (Sym.eval _ (.loadx 0 380
      (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X28)) 1)) (BitVec.ofNat 64 2))) = _
    have hlt := (x.getD i 0).toNat_lt
    rw [hD]
    simp only [CmpOp.apply, low_W64]
    rw [ult_ofNat (by omega) (by decide), beq_ofNat (by omega) (by decide)]
    exact digit_cond _
  have hpc' := pc_cond hpc hcond
  by_cases hd : (x.getD i 0).toNat ≤ 2
  · have hp' : st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b15Offset := by
      rw [hpc', decide_eq_false (by omega : ¬2 < (x.getD i 0).toNat)]
      rfl
    refine pc_at hp' (steps hp hc hpre (2 - (x.getD i 0).toNat) (x.getD i 0).toNat (by omega) hv
      hK1 hR1 hcell fun m' g1 g2 g3 ↦ ?_)
    refine seg_b41 hp hpre (length_chain _ _ _ _ _ _ hv) g1 g2 g3 fun m'' f1 f2 f3 ↦ ?_
    refine seg_b13 hp hpre hi hEl (length_chain _ _ _ _ _ _ hv) f1 f2.1 f2.2.1 f2.2.2.1 f2.2.2.2.1
      f2.2.2.2.2.2 f3 fun m3 hA3 ↦ cont m3 ?_
    unfold Run.chainEnd
    rw [show 3 - (x.getD i 0).toNat = 2 - (x.getD i 0).toNat + 1 by omega]
    exact hA3
  · have hp' : st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b13Offset := by
      rw [hpc', decide_eq_true (by omega : 2 < (x.getD i 0).toNat)]
      exact Run.label_of_block r hp b13_in_code rfl
    refine pc_at hp' (seg_b13 hp hpre hi hEl hv hK1 hR1.1 hR1.2.1 hR1.2.2.1 hR1.2.2.2.1
      hR1.2.2.2.2.2 hcell fun m3 hA3 ↦ cont m3 ?_)
    unfold Run.chainEnd
    rw [show 3 - (x.getD i 0).toNat = 0 by omega, chain_zero]
    exact hA3

end

end NativeRustcArm.WotsLeafProof.Chain
