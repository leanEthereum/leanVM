module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Chains.Ends

/-!
# Region 5b: a layer's chains

`b105` reads chain `i`'s digit `d` and value (`seg_b105`); a digit above 2 goes straight to
`b104`, otherwise `b106` and the `3 - d` steps (`seg_b106`); `b104` stores the chain's end and goes
on with chain `i + 1` (`chains_loop`, by induction on the chains left). From `AtChains l x` at
`b105`, the machine reaches `b134` with the 64 ends `chainEnds l x` at `20464`: **`chainsSpec`**.
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

variable [ElfHost] {r : Run}

/-- **`b105`**: chain `i`'s digit and value; then its steps, and `b104`. -/
theorem seg_b105 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hl : l < 3) (hx : x.length = 64) {i : Nat} (hi : i < 64)
    (hEl : E.length = 16 * i) {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m)
    (h1 : Run.RegIs m .X1 (BitVec.ofNat 64 i))
    (cont : ∀ m', Keep r l x E m' → r.WordAt m' 416 i.toUInt64 →
      BytesAt m'.dmem (r.off 8224) (chainEnd r l x i) →
      Eventually (elfStep1 ElfHost.exe) R ⟨m', r.pc NativeRustcArm.Sphincs.SphincsVerify.b104Offset⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b105Offset⟩ := by
  have hF := hK.1
  have hv := r.length_wots_getD hl hi
  have hval : BytesAt m.dmem (r.off (5140 + 1028 * l + 16 * i)) ((r.layerSig l).wots.getD i []) := by
    have := BytesAt.slice hK.2.1.2.1 (4656 + 1028 * l + 16 * i) 16
    rwa [r.off_add, r.sigMem_wots hl hi,
      show 484 + (4656 + 1028 * l + 16 * i) = 5140 + 1028 * l + 16 * i by omega] at this
  have hdig : BytesAt m.dmem (r.off 15936 + BitVec.ofNat 64 i) [x.getD i 0] := by
    have := BytesAt.slice hK.2.2.2.2.2.2.2.1 i 1
    rwa [drop_take_one (by omega)] at this
  obtain ⟨m0, w0⟩ := r.frame_mapped hpre hF (a := 15936) (n := 64) (by decide)
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := 5140 + 1028 * l + 16 * i) (n := 16) (by omega)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := 8224) (n := 16) (by decide)
  obtain ⟨m3, w3⟩ := r.frame_mapped hpre hF (a := 408) (n := 16) (by decide)
  let regs : List (BitVec 64 × Nat) :=
    [(r.off 15936, 64), (r.off (5140 + 1028 * l + 16 * i), 16), (r.off 8224, 16), (r.off 408, 16)]
  have hwf : (Env.ofMachine m regs).WF :=
    Env.wf_of ⟨⟨m0, w0⟩, ⟨m1, w1⟩, ⟨m2, w2⟩, ⟨m3, w3⟩, trivial⟩
      (List.Pairwise.cons (fun e he ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl
          · exact apart_regions hpre (by decide) (by omega) (by omega)
          · exact apart_regions hpre (by decide) (by decide) (by omega)
          · exact apart_regions hpre (by decide) (by decide) (by omega))
        (List.Pairwise.cons (fun e he ↦ by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl
            · exact apart_regions hpre (by omega) (by decide) (by omega)
            · exact apart_regions hpre (by omega) (by decide) (by omega))
          (List.Pairwise.cons (fun e he ↦ by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              subst he
              exact apart_regions hpre (by decide) (by decide) (by omega))
            (List.Pairwise.cons (fun _ h ↦ nomatch h) List.Pairwise.nil))))
  obtain ⟨-, -, -, -, -, -, -, s408, -, -, -⟩ := hK.2.2.1
  have hld408 : (Env.ofMachine m regs).load 3 0 8 = r.off (5140 + 1028 * l) := by
    have hb408 : BytesAt m.dmem (r.off 408) _ := s408
    rw [Env.load_of_bytesAt (NativeRustc.length_wordBytes _) (bytesAt_add_zero hb408),
      ofInt_ofBytes_wordBytes]
    rfl
  have hm : Match (Env.ofMachine m regs) s105 m := by
    refine match_ofMachine ⟨rfl, fun _ ↦ ?_, rfl, fun h ↦ Bool.noConfusion h, rfl,
      fun h ↦ Bool.noConfusion h, rfl, fun h ↦ Bool.noConfusion h, trivial⟩ ?_ ⟨?_, trivial⟩ trivial
      ⟨?_, trivial⟩ ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [r.off_toNat hpre (by decide)]
      have := r.base_aligned hpre
      omega
    · show m.regs.SP.toBitVec = r.off 15936 + BitVec.ofInt 64 (-15936)
      rw [off_add_ofInt 15936 (b := 0) (by omega), Run.off_zero]
      exact hF.1
    · show (m.regs.getXReg .X29).toBitVec = r.off 8224 + BitVec.ofInt 64 13296
      rw [off_add_ofInt 8224 (b := 21520) (by omega)]
      exact hF.2.1
    · show (m.regs.getXReg .X1).toBitVec.toNat < 64
      rw [h1, BitVec.toNat_ofNat]
      omega
    · show r.off 15936 + BitVec.ofInt 64 (-15528) = r.off 408 + BitVec.ofInt 64 0
      rw [off_add_ofInt 15936 (b := 408) (by omega), off_add_ofInt 408 (b := 408) (by omega)]
    · show r.off 15936 + BitVec.ofInt 64 (-15520) = r.off 408 + BitVec.ofInt 64 8
      rw [off_add_ofInt 15936 (b := 416) (by omega), off_add_ofInt 408 (b := 416) (by omega)]
    · show BinOp.apply .add .W64 ((Env.ofMachine m regs).load 3 0 8)
        (UnOp.apply (.shift .LSL 4) .W64 (m.regs.getXReg .X1).toBitVec) =
          r.off (5140 + 1028 * l + 16 * i) + BitVec.ofInt 64 0
      rw [hld408, h1]
      sym_simp
      rw [shl4 (by omega), r.off_add, off_add_ofInt _ (b := 5140 + 1028 * l + 16 * i) (by simp)]
    · show r.off 15936 + BitVec.ofInt 64 (-7712) = r.off 8224 + BitVec.ofInt 64 0
      rw [off_add_ofInt 15936 (b := 8224) (by omega), off_add_ofInt 8224 (b := 8224) (by omega)]
    · show r.off 15936 + BitVec.ofInt 64 (-7704) = r.off 8224 + BitVec.ofInt 64 8
      rw [off_add_ofInt 15936 (b := 8232) (by omega), off_add_ofInt 8224 (b := 8232) (by omega)]
  refine blk r hp b105_in_code (List.cons_ne_nil _ _) run_b105 hwf hm fun st hm1 hpc ↦ ?_
  have hD : (Sym.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X1)) 1).eval
      (Env.ofMachine m regs) = BitVec.ofNat 64 (x.getD i 0).toNat := by
    show Env.load _ 0 (0 + (UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64
      (m.regs.getXReg .X1).toBitVec).toNat) 1 = _
    rw [memExt0, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.zero_add]
    exact load_one hdig
  have h20 : Run.RegIs st.data .X20 (BitVec.ofNat 64 (x.getD i 0).toNat) := by
    unfold Run.RegIs
    rw [hm1.regs .X20 _ rfl]
    exact hD
  have hsp : st.data.regs.SP.toBitVec = r.base := by
    rw [hm1.sp]
    show r.off 15936 + BitVec.ofInt 64 (-15936) = r.base
    rw [off_add_ofInt 15936 (b := 0) (by omega), Run.off_zero]
  have h29 : Run.RegIs st.data .X29 (r.off 21520) := by
    unfold Run.RegIs
    rw [hm1.regs .X29 _ rfl]
    exact off_add_ofInt 8224 (by omega)
  have hout := sameOutside_regions2 hm1 hwf (k1 := 2) (k2 := 3) (o2 := 8) (n2 := 8) rfl rfl
    (by decide) (by decide +kernel)
  rw [r.off_add] at hout
  have hK1 := Keep.of_change_b105 hpre hx (by omega) hK hsp h29 (reg_same hm1 rfl)
    (reg_same hm1 rfl) (reg_same hm1 rfl) (reg_same hm1 rfl) hout (hm1.kept hwf)
  have hw416 : r.WordAt st.data 416 i.toUInt64 := by
    have hw := bytesAt_write_val hm1 (r := 3) (b := r.off 408) (sz := 16) rfl (o := 8) (n := 8)
      (by decide) (v := .reg .X1) (by decide +kernel)
    rw [r.off_add] at hw
    rw [show Sym.eval (Env.ofMachine m regs) (.reg .X1) = BitVec.ofNat 64 i from h1, bytes_word] at hw
    exact hw
  have hcell : BytesAt st.data.dmem (r.off 8224) ((r.layerSig l).wots.getD i []) := by
    have := copy16_gen hm1 (k := 2) (b := r.off 8224) rfl (o := 0) (by decide) (k' := 1) (o' := 0)
      (by decide +kernel) (by decide +kernel) hv (bytesAt_add_zero hval)
    simpa using this
  have hcond : (SBool.and
      (.not (.cmp .ult .W64 (.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X1)) 1) (.lit 2)))
      (.not (.cmp .eq .W64 (.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X1)) 1)
        (.lit 2)))).eval (Env.ofMachine m regs) =
      decide (2 < (x.getD i 0).toNat) := by
    show (!(CmpOp.apply .ult .W64 (Sym.eval _ (.loadx 0 0 (.un (.memExtend ⟨.UXTX, .E0⟩) .W64
      (.reg .X1)) 1)) (BitVec.ofNat 64 2)) && !(CmpOp.apply .eq .W64 (Sym.eval _ (.loadx 0 0
      (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg .X1)) 1)) (BitVec.ofNat 64 2))) = _
    have hlt := (x.getD i 0).toNat_lt
    rw [hD]
    simp only [CmpOp.apply, low_W64]
    rw [ult_ofNat (by omega) (by decide), beq_ofNat (by omega) (by decide)]
    exact digit_cond _
  have hpc' : st.pc = if decide (2 < (x.getD i 0).toNat) = true then Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_36
      else r.pc (NativeRustcArm.Sphincs.SphincsVerify.b105Offset + b105.length) := by
    rw [← hcond]
    exact pc_cond hpc
  by_cases hd : (x.getD i 0).toNat ≤ 2
  · have hp' : st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b106Offset := by
      rw [hpc']
      split
      next h =>
        simp only [decide_eq_true_eq] at h
        omega
      next => rfl
    exact pc_at hp' (seg_b106 hp hc hpre hx (by omega) hi hd hv hK1 h20 hw416 hcell
      fun m' g1 g2 g3 ↦ cont m' g1 g2 g3)
  · have hp' : st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b104Offset := by
      rw [hpc']
      split
      next => exact labelAt r hp b104_in_code rfl
      next h =>
        simp only [decide_eq_true_eq] at h
        omega
    refine pc_at hp' (cont _ hK1 hw416 ?_)
    unfold chainEnd
    rw [show 3 - (x.getD i 0).toNat = 0 by omega]
    exact hcell

/-- **The chains from chain `i`**: the ends of chains `i .. 63` after those before. -/
theorem chains_loop (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x : List UInt8} (hl : l < 3) (hx : x.length = 64) :
    ∀ (n i : Nat) {m : MachineData}, i + n = 64 → 0 < n →
      Keep r l x ((List.range i).map (chainEnd r l x)).flatten m →
      Run.RegIs m .X1 (BitVec.ofNat 64 i) →
      Eventually (elfStep1 ElfHost.exe)
        (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b134Offset ∧ r.AtWotsPk l (r.chainEnds l x) st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b105Offset⟩
  | 0, _, _, _, hn, _, _ => absurd hn (by decide)
  | n + 1, i, m, hin, _, hK, h1 => by
    have hi : i < 64 := by omega
    have hEl := length_ends r hl x (i := i) (by omega)
    refine seg_b105 hp hc hpre hl hx hi hEl hK h1 fun m1 k1 gw416 gcell ↦ ?_
    refine seg_b104 hp hpre hx hi hEl
      (length_chain _ _ _ _ _ (r.length_wots_getD hl hi)) k1 gw416 gcell fun m2 k2 g1 ↦ ?_
    have k2' : Keep r l x ((List.range (i + 1)).map (chainEnd r l x)).flatten m2 := by
      rw [ends_succ]
      exact k2
    by_cases h : i + 1 = 64
    · simp only [h, ↓reduceIte]
      rw [h] at k2'
      refine .done _ ⟨rfl, hl, k2'.1, k2'.2.1, k2'.2.2.1, k2'.2.2.2.1, k2'.2.2.2.2.1, k2'.2.2.2.2.2.1,
        k2'.2.2.2.2.2.2.1, k2'.2.2.2.2.2.2.2.2, ?_⟩
      rw [chainEnds_eq]
      exact length_ends r hl x (le_refl _)
    · simp only [h, ↓reduceIte]
      exact chains_loop hp hc hpre hl hx n (i + 1) (by omega) (by omega) k2' g1

/-- **Region 5b, a layer's chains**: from `AtChains l x` at `b105` to `AtWotsPk l (chainEnds l x)`
at `b134`. -/
theorem chainsSpec : ChainsSpec := by
  intro l x r hp hc hpre m ⟨hl, hx, hF, hI, hLS, h1, h19, h21, h25, h27, hxa⟩
  exact chains_loop hp hc hpre hl hx 64 0 rfl (by decide)
    ⟨hF, hI, hLS, h19, h21, h25, h27, hxa, fun _ h ↦ absurd h (by simp)⟩ h1

end

end NativeRustcArm.SphincsVerifyProof.Chains
