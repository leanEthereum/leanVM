module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Chains.Ends

/-!
# Region 5b: a layer's chains

`b114` reads chain `i`'s digit `d` and value (`seg_b114`); a digit above 2 goes straight to
`b113`, otherwise `b115` and the `3 - d` steps (`seg_b115`); `b113` stores the chain's end and goes
on with chain `i + 1` (`chains_loop`, by induction on the chains left). From `AtChains l x` at
`b114`, the machine reaches `b143` with the 64 ends `chainEnds l x` at `28208`: **`chainsSpec`**.
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

public section

theorem drop_take_one {x : List UInt8} {i : Nat} (hi : i < x.length) :
    (x.drop i).take 1 = [x.getD i 0] := by
  rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem load_one {env : Env} {r off : Nat} {b : UInt8}
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 off) [b]) :
    env.load r off 1 = BitVec.ofNat 64 b.toNat := by
  rw [Env.load_of_bytesAt (n := 1) rfl h]
  show BitVec.ofInt 64 (0 * 256 + (b.toNat : Int)) = _
  simp

/-- The ends of the chains before `i`: 16 bytes each. -/
theorem length_ends (r : Run) {l : Nat} (hl : l < 3) (x : List UInt8) {i : Nat} (hi : i ≤ 64) :
    ((List.range i).map (chainEnd r l x)).flatten.length = 16 * i := by
  rw [length_flatten_uniform _ (fun e he ↦ by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    exact length_chain _ _ _ _ _ (r.length_wots_getD hl (by simp at hj; omega)))]
  simp

theorem ends_succ (r : Run) (l : Nat) (x : List UInt8) (i : Nat) :
    ((List.range (i + 1)).map (chainEnd r l x)).flatten =
      ((List.range i).map (chainEnd r l x)).flatten ++ chainEnd r l x i := by
  rw [List.range_succ, List.map_append, List.flatten_append]
  simp

theorem digit_cond (d : Nat) : (!decide (d < 2) && !decide (d = 2)) = decide (2 < d) := by
  by_cases h1 : d < 2
  · simp [h1, show ¬2 < d by omega]
  · by_cases h2 : d = 2
    · subst h2
      decide
    · simp [h1, h2, show 2 < d by omega]

variable [NativeRustcArm.Host] {r : Run}

/-- **`b114`**: chain `i`'s digit and value; then its steps, and `b113`. -/
theorem seg_b114 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hl : l < 3) (hx : x.length = 64) {i : Nat} (hi : i < 64)
    (hEl : E.length = 16 * i) {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m)
    (h0 : Run.RegIs m .X0 (BitVec.ofNat 64 i)) (h8 : Run.RegIs m .X8 (r.off (12900 + 1028 * l)))
    (cont : ∀ m', Keep r l x E m' → Run.RegIs m' .X28 (BitVec.ofNat 64 i) →
      BytesAt m'.dmem (r.off 29248) (chainEnd r l x i) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', r.pc NativeRustcArm.Sphincs.SphincsVerify.b113Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b114Offset⟩ := by
  have hF := hK.1
  have hv := r.length_wots_getD hl hi
  have hval : BytesAt m.dmem (r.off (12900 + 1028 * l + 16 * i)) ((r.layerSig l).wots.getD i []) := by
    have := BytesAt.slice hK.2.1.2.1 (4656 + 1028 * l + 16 * i) 16
    rwa [r.off_add, r.sigMem_wots hl hi,
      show 8244 + (4656 + 1028 * l + 16 * i) = 12900 + 1028 * l + 16 * i by omega] at this
  have hdig : BytesAt m.dmem (r.off 22672 + BitVec.ofNat 64 i) [x.getD i 0] := by
    have := BytesAt.slice hK.2.2.2.2.2.2.1 i 1
    rwa [drop_take_one (by omega)] at this
  obtain ⟨m0, w0⟩ := r.frame_mapped hpre hF (a := 22672) (n := 64) (by decide)
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := 12900 + 1028 * l + 16 * i) (n := 16) (by omega)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := 29248) (n := 16) (by decide)
  have hwf : (Env.ofMachine m [(r.off 22672, 64), (r.off (12900 + 1028 * l + 16 * i), 16),
      (r.off 29248, 16)]).WF :=
    Env.wf_of ⟨⟨m0, w0⟩, ⟨m1, w1⟩, ⟨m2, w2⟩, trivial⟩
      (List.Pairwise.cons (fun e he ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl
          · exact apart_regions hpre (by decide) (by omega) (by omega)
          · exact apart_regions hpre (by decide) (by decide) (by omega))
        (List.Pairwise.cons (fun e he ↦ by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            subst he
            exact apart_regions hpre (by omega) (by decide) (by omega))
          (List.Pairwise.cons (fun _ h ↦ nomatch h) List.Pairwise.nil)))
  have hm : Match (Env.ofMachine m [(r.off 22672, 64), (r.off (12900 + 1028 * l + 16 * i), 16),
      (r.off 29248, 16)]) s114 m := by
    refine match_ofMachine ⟨rfl, fun h ↦ Bool.noConfusion h, rfl, fun h ↦ Bool.noConfusion h, rfl,
      fun h ↦ Bool.noConfusion h, trivial⟩ ?_ ⟨?_, trivial⟩ trivial ⟨?_, trivial⟩ ⟨?_, trivial⟩
    · show m.regs.SP.toBitVec = r.off 22672 + BitVec.ofInt 64 (-22672)
      rw [off_add_ofInt 22672 (b := 0) (by omega), Run.off_zero]
      exact hF.1
    · show (m.regs.getXReg .X29).toBitVec = r.off 29248 + BitVec.ofInt 64 32
      rw [off_add_ofInt 29248 (b := 29280) (by omega)]
      exact hF.2.1
    · show (m.regs.getXReg .X0).toBitVec.toNat < 64
      rw [h0, BitVec.toNat_ofNat]
      omega
    · show BinOp.apply .add .W64 (m.regs.getXReg .X8).toBitVec
        (UnOp.apply (.shift .LSL 4) .W64 (m.regs.getXReg .X0).toBitVec) =
          r.off (12900 + 1028 * l + 16 * i) + BitVec.ofInt 64 0
      rw [h8, h0]
      sym_simp
      rw [shl4 (by omega), r.off_add, off_add_ofInt _ (b := 12900 + 1028 * l + 16 * i) (by simp)]
  refine blk r hp b114_in_code (List.cons_ne_nil _ _) run_b114 hwf hm fun st hm1 hpc ↦ ?_
  have hD : (Sym.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X0)) 1).eval
      (Env.ofMachine m [(r.off 22672, 64), (r.off (12900 + 1028 * l + 16 * i), 16),
        (r.off 29248, 16)]) = BitVec.ofNat 64 (x.getD i 0).toNat := by
    show Env.load _ 0 (0 + (UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64
      (m.regs.getXReg .X0).toBitVec).toNat) 1 = _
    rw [memExt0, h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.zero_add]
    exact load_one hdig
  have h19 : Run.RegIs st.data .X19 (BitVec.ofNat 64 (x.getD i 0).toNat) := by
    unfold Run.RegIs
    rw [hm1.regs .X19 _ rfl]
    exact hD
  have h28 : Run.RegIs st.data .X28 (BitVec.ofNat 64 i) := by
    unfold Run.RegIs
    rw [hm1.regs .X28 _ rfl]
    exact h0
  have h22 : Run.RegIs st.data .X22 (r.off 21648) := by
    unfold Run.RegIs
    rw [hm1.regs .X22 _ rfl]
    exact off_add_ofInt 22672 (by omega)
  have hsp : st.data.regs.SP.toBitVec = r.base := by
    rw [hm1.sp]
    show r.off 22672 + BitVec.ofInt 64 (-22672) = r.base
    rw [off_add_ofInt 22672 (b := 0) (by omega), Run.off_zero]
  have h29 : Run.RegIs st.data .X29 (r.off 29280) := by
    unfold Run.RegIs
    rw [hm1.regs .X29 _ rfl]
    exact off_add_ofInt 29248 (by omega)
  have hK1 := Keep.of_change hpre hx (by omega) hK (a := 29248) (n := 16) (by decide)
    (Or.inr (Or.inr (by omega))) hsp h29 (reg_same hm1 rfl) (reg_same hm1 rfl) (reg_same hm1 rfl)
    (sameOutside_region hm1 hwf (k := 2) rfl (by decide +kernel)) (hm1.kept hwf)
  have hcell : BytesAt st.data.dmem (r.off 29248) ((r.layerSig l).wots.getD i []) := by
    have := copy16_gen hm1 (k := 2) (b := r.off 29248) rfl (o := 0) (by decide) (k' := 1) (o' := 0)
      (by decide +kernel) (by decide +kernel) hv (bytesAt_add_zero hval)
    simpa using this
  have hcond : (SBool.and
      (.not (.cmp .ult .W64 (.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X0)) 1) (.lit 2)))
      (.not (.cmp .eq .W64 (.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X0)) 1)
        (.lit 2)))).eval (Env.ofMachine m [(r.off 22672, 64),
          (r.off (12900 + 1028 * l + 16 * i), 16), (r.off 29248, 16)]) =
      decide (2 < (x.getD i 0).toNat) := by
    show (!(CmpOp.apply .ult .W64 (Sym.eval _ (.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64
      (.reg .X0)) 1)) (BitVec.ofNat 64 2)) && !(CmpOp.apply .eq .W64 (Sym.eval _ (.loadx 0 0
      (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X0)) 1)) (BitVec.ofNat 64 2))) = _
    have hlt := (x.getD i 0).toNat_lt
    rw [hD]
    simp only [CmpOp.apply, low_W64]
    rw [ult_ofNat (by omega) (by decide), beq_ofNat (by omega) (by decide)]
    exact digit_cond _
  have hpc' : st.pc = if decide (2 < (x.getD i 0).toNat) = true then Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_44
      else r.pc (NativeRustcArm.Sphincs.SphincsVerify.b114Offset + b114.length) := by
    rw [← hcond]
    exact pc_cond hpc
  by_cases hd : (x.getD i 0).toNat ≤ 2
  · have hp' : st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b115Offset := by
      rw [hpc']
      split
      next h =>
        simp only [decide_eq_true_eq] at h
        omega
      next => rfl
    exact pc_at hp' (seg_b115 hp hc hpre hx (by omega) hi hd hv hK1 h19 h28 h22 hcell
      fun m' g1 g2 g3 ↦ cont m' g1 g2 g3)
  · have hp' : st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b113Offset := by
      rw [hpc']
      split
      next => exact labelAt r hp b113_in_code rfl
      next h =>
        simp only [decide_eq_true_eq] at h
        omega
    refine pc_at hp' (cont _ hK1 h28 ?_)
    unfold chainEnd
    rw [show 3 - (x.getD i 0).toNat = 0 by omega]
    exact hcell

/-- **The chains from chain `i`**: the ends of chains `i .. 63` after those before. -/
theorem chains_loop (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x : List UInt8} (hl : l < 3) (hx : x.length = 64) :
    ∀ (n i : Nat) {m : MachineData}, i + n = 64 → 0 < n →
      Keep r l x ((List.range i).map (chainEnd r l x)).flatten m →
      Run.RegIs m .X0 (BitVec.ofNat 64 i) → Run.RegIs m .X8 (r.off (12900 + 1028 * l)) →
      Eventually (step1 NativeRustcArm.Host.exe)
        (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b143Offset ∧ r.AtWotsPk l (r.chainEnds l x) st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b114Offset⟩
  | 0, _, _, _, hn, _, _, _ => absurd hn (by decide)
  | n + 1, i, m, hin, _, hK, h0, h8 => by
    have hi : i < 64 := by omega
    have hEl := length_ends r hl x (i := i) (by omega)
    refine seg_b114 hp hc hpre hl hx hi hEl hK h0 h8 fun m1 k1 g28 gcell ↦ ?_
    refine seg_b113 hp hpre hx hi hEl
      (length_chain _ _ _ _ _ (r.length_wots_getD hl hi)) k1 g28 gcell fun m2 k2 g0 g8 ↦ ?_
    have k2' : Keep r l x ((List.range (i + 1)).map (chainEnd r l x)).flatten m2 := by
      rw [ends_succ]
      exact k2
    by_cases h : i + 1 = 64
    · simp only [h, ↓reduceIte]
      rw [h] at k2'
      refine .done _ ⟨rfl, hl, k2'.1, k2'.2.1, k2'.2.2.1, k2'.2.2.2.1, k2'.2.2.2.2.1, k2'.2.2.2.2.2.1,
        k2'.2.2.2.2.2.2.2, ?_⟩
      rw [chainEnds_eq]
      exact length_ends r hl x (le_refl _)
    · simp only [h, ↓reduceIte]
      exact chains_loop hp hc hpre hl hx n (i + 1) (by omega) (by omega) k2' g0 g8

/-- **Region 5b, a layer's chains**: from `AtChains l x` at `b114` to `AtWotsPk l (chainEnds l x)`
at `b143`. -/
theorem chainsSpec : ChainsSpec := by
  intro l x r hp hc hpre m ⟨hl, hx, hF, hI, hLS, h0, h8, h21, h25, h26, hxa⟩
  exact chains_loop hp hc hpre hl hx 64 0 rfl (by decide)
    ⟨hF, hI, hLS, h21, h25, h26, hxa, fun _ h ↦ absurd h (by simp)⟩ h0 h8

end

end NativeRustcArm.SphincsVerifyProof.Chains
