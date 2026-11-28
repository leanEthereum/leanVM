module

public import NativeRustcX64.WotsLeaf.Chain.Ends

/-!
# The chains' loop

At `b15` (`.LWotsLeaf_5`, directive 177, `Run.AtChain i`): chain `i`'s digit and value (`b15`,
the value through region 4, the alias of `values + (i << 4)`); with digit 3 straight to `b14`,
else `i` at `464` (`b16`), the steps to position 3 (`steps`), `b48`; then `b14` stores the end
(`seg_b14`). From chain 0 the loop leaves the 58 ends at `1080` and reaches `b51` (directive 525)
(`chains_region`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Chain

@[expose] public section

/-- **At chain `i`** (`b15`): the loop's slots, RDX `i`, R12 the frame's byte `112`. -/
def Run.AtChain [Labels] (r : Run) (i : Nat) (m : MachineData) : Prop :=
  Keep r (r.outerSlots i) m ∧ Run.RegIs m .rdx (BitVec.ofNat 64 i) ∧ Run.RegIs m .r12 (r.off 112) ∧
    Run.RegIs m .r13 (Labels.label "memcpy").toBitVec ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec

end

public section

theorem shl4 {i : Nat} (hi : i < 2 ^ 59) :
    BinOp.apply .shl .W64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * i) := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := by decide
  simp only [BinOp.apply, low_W64, ext_W64, hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  congr 1
  omega

/-- A byte zero-extended. -/
theorem zext8 {n : Nat} (hn : n < 256) :
    UnOp.apply (.zext .W8) .W32 (BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h8 : Width.W8.bits = 8 := rfl
  have h32 : Width.W32.bits = 32 := rfl
  simp only [UnOp.apply, ext, Sym.low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h8, h32]
  omega

theorem digit_le (r : Run) {j : Nat} (hj : j < 58) : r.digit j ≤ 3 := by
  simp only [Run.digit, Run.digitsPre, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some, UInt8.toNat_ofNat']
  have := Nat.and_le_right (n := r.dNum >>> (2 * j)) (m := 3)
  omega

/-- Chain `j`'s digit, the byte at `614 + j`. -/
theorem digits_slice (r : Run) {j : Nat} (hj : j < 58) :
    ((r.digitsPre 58).drop j).take 1 = [(r.digitsPre 58).getD j 0] := by
  have h : j < (r.digitsPre 58).length := by rw [length_digitsPre]; exact hj
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    Option.getD_some]
  rfl

/-- Chain `j`'s value. -/
theorem values_getD (r : Run) {j : Nat} (hj : j < 58) :
    r.values.getD j [] =
      bytesOf r.m0.dmem (WotsLeafPre.valuesPtr r.m0 + BitVec.ofNat 64 (16 * j)) 16 := by
  simp [Run.values, WotsLeafPre.values, List.getD_eq_getElem?_getD, hj]

theorem length_values (r : Run) {j : Nat} (hj : j < 58) : (r.values.getD j []).length = 16 := by
  rw [values_getD r hj, length_bytesOf]

theorem length_endOf (r : Run) {j : Nat} (hj : j < 58) : (r.endOf j).length = 16 :=
  length_chain r j _ _ (length_values r hj)

theorem endsPre_succ (r : Run) (i : Nat) : r.endsPre (i + 1) = r.endsPre i ++ r.endOf i := by
  simp [Run.endsPre, List.range_succ]

/-- With digit 3 the chain's end is its value. -/
theorem endOf_three (r : Run) {j : Nat} (h : r.digit j = 3) : r.endOf j = r.values.getD j [] := by
  rw [Run.endOf, h]
  rfl

theorem ofInt_ofBytes_one (b : UInt8) :
    BitVec.ofInt 64 (Int.ofBytes [b]) = BitVec.ofNat 64 b.toNat := by
  rw [Sym.ofBytes_natCast, BitVec.ofInt_natCast, natOfBytes_eq_leNat]
  simp [leNat]

variable [Host] {r : Run}
/-- **`b48`**: back to `b14`. -/
theorem seg_b48 (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {i : Nat} {e : List UInt8}
    (he : e.length = 16) {R : MachineState → Prop} {m : MachineData} (hA : r.AtStep i 3 e m)
    (cont : ∀ m', Keep r (r.endSlots i) m' → BytesAt m'.dmem (r.off 80) e →
      Run.RegIs m' .rdx (BitVec.ofNat 64 i) → Run.RegIs m' .r12 (r.off 112) →
      Run.RegIs m' .r13 (Labels.label "memcpy").toBitVec →
      Run.RegIs m' .rbx (Labels.label "memset").toBitVec →
      Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Xmss.WotsLeaf.b14Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b48Offset⟩ := by
  obtain ⟨hK, h80, -, hdx, h12, h13, hbx⟩ := hA
  refine frameStep r hp hpre b48_in_code (List.cons_ne_nil _ _) run_b48 (by decide) rfl hK
    trivial extraOK_nil trivial trivial trivial fun st hm hK1 hkb hpc ↦ ?_
  exact pc_at (hpc.trans (Run.label_of_block r hp b14_in_code rfl))
    (cont _ hK1.left (hkb 80 e (by omega) (by rw [he]; decide) h80) (regIs_reg hm rfl hdx)
      (regIs_reg hm rfl h12) (regIs_reg hm rfl h13) (regIs_reg hm rfl hbx))

/-- **Chain `i`**: `b15`, then `b14` (digit 3) or `b16`, the steps, `b48`, `b14`; on to chain
`i + 1` or `b51`. -/
theorem chain_one (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i : Nat}
    (hi : i < 58) {R : MachineState → Prop} {m : MachineData} (hA : r.AtChain i m)
    (cont : ∀ m', Keep r (r.outerSlots (i + 1)) m' →
      Run.RegIs m' .rdx (BitVec.ofNat 64 (i + 1)) → Run.RegIs m' .r12 (r.off 112) →
      Run.RegIs m' .r13 (Labels.label "memcpy").toBitVec →
      Run.RegIs m' .rbx (Labels.label "memset").toBitVec →
      Eventually (step1 Host.exe) R ⟨m', if i + 1 = 58 then r.pc NativeRustcX64.Xmss.WotsLeaf.b51Offset else r.pc NativeRustcX64.Xmss.WotsLeaf.b15Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b15Offset⟩ := by
  obtain ⟨hK, hdx, h12, h13, hbx⟩ := hA
  have hin : WotsLeafPre.Input r.m0 (WotsLeafPre.valuesPtr r.m0 + BitVec.ofNat 64 (16 * i)) 16 :=
    Run.Input.sub r (r.pre_values hpre) (by omega) (by omega)
  have hs : SameOutside r.m0.dmem m.dmem r.Changed := SameOutside.mono hK.1.2.2.1 fun _ h ↦ Or.inr h
  have s614 : BytesAt m.dmem (r.off 614) (r.digitsPre 58) :=
    (allOf_left hK.2).2.2.2.2.2.1.2.2
  have hbyte : BytesAt m.dmem (r.off (614 + i)) [(r.digitsPre 58).getD i 0] := by
    rw [← digits_slice r hi]
    exact BytesAt.sub s614 i 1
  have hd3 := digit_le r hi
  have hdx' : m.regs.get64 .rdx = BitVec.ofNat 64 i := hdx
  have hti : (m.regs.get64 .rdx).toNat = i := by
    have := congrArg BitVec.toNat hdx'
    simp only [BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl] at this
    omega
  refine frameStep r hp hpre b15_in_code (List.cons_ne_nil _ _) run_b15 (by decide) rfl hK
    (extra := [(WotsLeafPre.valuesPtr r.m0 + BitVec.ofNat 64 (16 * i), 16)]) ⟨rfl, trivial⟩
    (r.extraOK_input hpre hK.1.2.2.2 hin (fun l hl => by
      have hv := (r.pre_values hpre).2.1
      have haddr :
          (WotsLeafPre.valuesPtr r.m0 + BitVec.ofNat 64 (16 * i)).toNat =
            (WotsLeafPre.valuesPtr r.m0).toNat + 16 * i :=
        Sym.toNat_add_ofNat _ _ (by unfold NoWrap at hv; omega)
      apply apart_of_sub
        (((r.got hpre).1 l hl).2.2.2 (WotsLeafPre.valuesPtr r.m0, 16 * 58) (by simp))
      · dsimp only
        rw [haddr]
        omega
      · dsimp only
        rw [haddr]
        omega)) trivial ⟨by
      show (m.regs.get64 .rdx).toNat < 58
      omega, trivial⟩ ⟨by
      show BinOp.apply .add .W64 ((r.envR m _ _).load 0 2776 8)
        (BinOp.apply .shl .W64 (m.regs.get64 .rdx) (BitVec.ofNat 64 4)) =
          WotsLeafPre.valuesPtr r.m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 0
      rw [r.load_valuesPtr hpre hs, hdx', shl4 (by omega)]
      simp only [BinOp.apply, low_W64, ext_W64]
      simp, trivial⟩ fun st hm hK1 hkb hpc ↦ ?_
  -- The chain's value at `80`, `16 i` at `456`, the digit in R14.
  have h80 : BytesAt st.data.dmem (r.off 80) (r.values.getD i []) :=
    copy16 hm (k := 0) (b := r.base) (sz := 2784) rfl (o := 80) (k' := 4) (o' := 0) (by decide)
      (by decide +kernel) (by decide +kernel) (length_values r hi) (by
        rw [BitVec.add_zero, values_getD r hi]
        exact r.input_bytes hpre ((r.frame_iff m).1 hK.1) hin)
  have h456 : BytesAt st.data.dmem (r.off 456) (regBytes (BitVec.ofNat 64 (16 * i))) := by
    have := frame_covers hm (o := 456) (n := 8) (v := .bin .shl .W64 (.reg .rdx) (.lit 4))
      (by decide) (by decide +kernel)
    rw [show (Sym.bin .shl .W64 (.reg .rdx) (.lit 4)).eval (r.envR m _ _) =
      BitVec.ofNat 64 (16 * i) by
        show BinOp.apply .shl .W64 (m.regs.get64 .rdx) (BitVec.ofNat 64 4) = _
        rw [hdx', shl4 (by omega)]] at this
    exact this
  have hx14 : (Sym.un (.zext .W8) .W32 (.loadx 0 614 (.reg .rdx) 1)).eval
      (r.envR m [(WotsLeafPre.valuesPtr r.m0 + BitVec.ofNat 64 (16 * i), 16)]
        (r.pc (NativeRustcX64.Xmss.WotsLeaf.b15Offset + b15.length)).toBitVec) = BitVec.ofNat 64 (r.digit i) := by
    show UnOp.apply (.zext .W8) .W32 ((r.envR m _ _).load 0 (614 + (m.regs.get64 .rdx).toNat) 1) = _
    rw [hti, Env.load_of_bytesAt (env := r.envR m [(WotsLeafPre.valuesPtr r.m0 +
      BitVec.ofNat 64 (16 * i), 16)] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b15Offset + b15.length)).toBitVec) (r := 0) (off := 614 + i)
      (n := 1) (bs := [(r.digitsPre 58).getD i 0]) rfl hbyte, ofInt_ofBytes_one,
      zext8 (by have := hd3; unfold Run.digit at this; omega)]
    rfl
  have h14 : Run.RegIs st.data .r14 (BitVec.ofNat 64 (r.digit i)) := regIs_eval hm rfl hx14
  have hdx1 : Run.RegIs st.data .rdx (BitVec.ofNat 64 i) := regIs_reg hm rfl hdx
  have h12' : Run.RegIs st.data .r12 (r.off 112) := regIs_reg hm rfl h12
  have h13' : Run.RegIs st.data .r13 (Labels.label "memcpy").toBitVec := regIs_reg hm rfl h13
  have hbx' : Run.RegIs st.data .rbx (Labels.label "memset").toBitVec := regIs_reg hm rfl hbx
  have hK15 : Keep r (r.endSlots i) st.data :=
    hK1.add ⟨⟨length_regBytes _, by norm_num, h456⟩, trivial⟩
  have hcond := pc_cond hpc (b := decide (r.digit i = 3)) (by
    show (!(CmpOp.apply .ult .W64 ((Sym.un (.zext .W8) .W32 (.loadx 0 614 (.reg .rdx) 1)).eval
      (r.envR m _ _)) (BitVec.ofNat 64 2)) && !(CmpOp.apply .eq .W64
      ((Sym.un (.zext .W8) .W32 (.loadx 0 614 (.reg .rdx) 1)).eval (r.envR m _ _))
      (BitVec.ofNat 64 2))) = _
    rw [hx14]
    generalize r.digit i = d at hd3 ⊢
    interval_cases d <;> decide)
  -- The end stored.
  have fin : ∀ m', Keep r (r.endSlots i) m' → BytesAt m'.dmem (r.off 80) (r.endOf i) →
      Run.RegIs m' .rdx (BitVec.ofNat 64 i) → Run.RegIs m' .r12 (r.off 112) →
      Run.RegIs m' .r13 (Labels.label "memcpy").toBitVec →
      Run.RegIs m' .rbx (Labels.label "memset").toBitVec →
      Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Xmss.WotsLeaf.b14Offset⟩ := fun m' g1 g2 g3 g4 g5 g6 ↦
    seg_b14 hp hpre hi (length_endOf r hi) g1 g2 g3 g4 g5 g6 fun m'' k1 k2 k3 k4 k5 ↦
      cont m'' (by rw [Run.outerSlots, endsPre_succ]; exact k1) k2 k3 k4 k5
  by_cases h3 : r.digit i = 3
  · rw [decide_eq_true h3, Sym.ite_pos rfl, Run.label_of_block r hp b14_in_code rfl] at hcond
    exact pc_at hcond (fin _ hK15 (by rw [endOf_three r h3]; exact h80) hdx1 h12' h13' hbx')
  rw [decide_eq_false h3] at hcond
  refine pc_at hcond ?_
  -- `b16`: `i` at `464`; the steps.
  refine frameStep r hp hpre b16_in_code (List.cons_ne_nil _ _) run_b16 (by decide) rfl hK15
    trivial extraOK_nil trivial trivial trivial fun st2 hm2 hK2 hkb2 hpc2 ↦ ?_
  have h464 : BytesAt st2.data.dmem (r.off 464) (regBytes (BitVec.ofNat 64 i)) := by
    have := frame_covers hm2 (o := 464) (n := 8) (v := .reg .rdx) (by decide) (by decide +kernel)
    rwa [show (Sym.reg .rdx).eval (r.envR st.data [] _) = BitVec.ofNat 64 i from hdx1] at this
  have hAt : r.AtStep i (r.digit i) (r.values.getD i []) st2.data :=
    ⟨hK2.add ⟨⟨length_regBytes _, by norm_num, h464⟩, trivial⟩,
      hkb2 80 _ (by rw [length_values r hi]; omega) (by rw [length_values r hi]; decide) h80,
      regIs_reg hm2 rfl h14, regIs_reg hm2 rfl hdx1, regIs_reg hm2 rfl h12',
      regIs_reg hm2 rfl h13', regIs_reg hm2 rfl hbx'⟩
  refine pc_at hpc2 ?_
  refine steps hp hc hpre (2 - r.digit i) (r.digit i) (by omega) (length_values r hi) hAt
    fun m' h ↦ seg_b48 hp hpre (length_chain r i _ _ (length_values r hi)) h fun m'' g1 g2 g3 g4 g5 g6 ↦
      fin m'' g1 ?_ g3 g4 g5 g6
  rwa [Run.endOf, show 3 - r.digit i = 2 - r.digit i + 1 by omega]

/-- **The chains from chain `i`**: on to `b51` with the 58 ends. -/
theorem chains_loop (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {R : MachineState → Prop} :
    ∀ (n i : Nat) {m : MachineData}, i + (n + 1) = 58 → r.AtChain i m →
      (∀ m', Keep r (r.outerSlots 58) m' → Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Xmss.WotsLeaf.b51Offset⟩) →
      Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b15Offset⟩
  | 0, i, m, h, hA, cont =>
    chain_one hp hc hpre (by omega) hA fun m' hK _ _ _ _ ↦ by
      obtain rfl : i = 57 := by omega
      exact cont m' hK
  | n + 1, i, m, h, hA, cont =>
    chain_one hp hc hpre (by omega) hA fun m' hK hdx h12 h13 hbx ↦ by
      rw [ite_neg (show ¬(i + 1 = 58) by omega)]
      exact chains_loop hp hc hpre n (i + 1) (by omega) ⟨hK, hdx, h12, h13, hbx⟩ cont

/-- **Region 3, the chains**: from `b15` with chain 0, the 58 ends at `1080` at `b51`. -/
theorem chains_region (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {R : MachineState → Prop} {m : MachineData} (hA : r.AtChains0 m)
    (cont : ∀ m', Keep r (r.outerSlots 58) m' → Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Xmss.WotsLeaf.b51Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b15Offset⟩ :=
  chains_loop hp hc hpre 57 0 rfl
    ⟨hA.1.add ⟨⟨rfl, by norm_num, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩, trivial⟩, hA.2.1,
      hA.2.2⟩ cont

end

end NativeRustcX64.WotsLeafProof
