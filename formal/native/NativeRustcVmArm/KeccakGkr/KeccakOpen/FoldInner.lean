module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldStep

/-!
# `keccak_open`'s fold: the inner loops

At entry `j` of an inner loop (`Inner`): the known registers `ks`, the counter `16 j`, the two
buffers, the rows. A turn (`innerStep`): the load block and `EW::mul` (`stepL`), the store block
(`stepS`), the rows' entry `n0` folded. The loops of the unrolled rounds, storing through X21
(`innerD_run`), and of the looped rounds, storing through X24 (`innerL_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- **An inner loop at entry `j`**. -/
structure Inner [Labels] (c : Cx) (m0 : MachineData) (vars : Nat → BitVec 64)
    (ks : List (XReg × Sym)) (CT : XReg) (fa fb G : Nat → EW) (j : Nat) (st : MachineData) :
    Prop where
  mid : Mid c m0 st
  kat : KAt m0 vars ks st
  ct : (st.regs.getXReg CT).toBitVec = BitVec.ofNat 64 (16 * j)
  bufA : ElemsAt st.dmem (fbA m0 + BitVec.ofNat 64 80) fa 64
  bufB : ElemsAt st.dmem (fbA m0 + BitVec.ofNat 64 1104) fb 64
  rows : ElemsAt st.dmem (rwA m0) G 4096

/-- A block keeps the registers of `ks`. -/
def keepK (ks : List (XReg × Sym)) (S : SState) : Bool :=
  ks.all fun p ↦ S.reg p.1 == some (.reg p.1)

/-- An inner loop's test: the counter is not `1024`. -/
def notEnd (CT : XReg) : SBool := .not (.cmp .eq .W64 (.reg CT) (.lit 1024))

/-- A store block's writes. -/
def stW (lo0 lo1 : XReg) (C : Nat) : List Write :=
  [⟨0, C + 8, 8, .bin .eor .W64 (.reg .X1) (.reg lo1)⟩,
    ⟨0, C, 8, .bin .eor .W64 (.reg .X0) (.reg lo0)⟩]

end

public section

theorem ofInt0 : BitVec.ofInt 64 0 = BitVec.ofNat 64 0 := rfl

theorem keepK_reg {ks : List (XReg × Sym)} {S : SState} (h : keepK ks S = true)
    {p : XReg × Sym} (hp : p ∈ ks) : S.reg p.1 = some (.reg p.1) :=
  beq_iff_eq.mp (List.all_eq_true.mp h p hp)

theorem wfK_callee {ks : List (XReg × Sym)} (h : wfK ks = true) {p : XReg × Sym} (hp : p ∈ ks) :
    calleeSaved p.1 = true := by
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true] at this
  exact this.1

theorem add_off (b : BitVec 64) (x y : Nat) :
    BinOp.apply .add .W64 (b + BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      b + BitVec.ofNat 64 (x + y) + BitVec.ofInt 64 0 := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [ofInt0, NativeRustcVm.addr_add_zero, NativeRustcVm.addr_add_add]

section
variable [Labels] {m0 st : MachineData} {vars : Nat → BitVec 64} {ks : List (XReg × Sym)}
  {r : XReg}

theorem KAt.regP (hk : KAt m0 vars ks st) (h : (r, P) ∈ ks) :
    (st.regs.getXReg r).toBitVec = rwA m0 := by
  rw [hk.reg h]
  show rwA m0 + BitVec.ofInt 64 0 = rwA m0
  rw [ofInt0, NativeRustcVm.addr_add_zero]

theorem KAt.regA (hk : KAt m0 vars ks st) (h : (r, A0) ∈ ks) :
    (st.regs.getXReg r).toBitVec = fbA m0 + BitVec.ofNat 64 80 := by
  rw [hk.reg h]
  show fbA m0 + BitVec.ofInt 64 80 = _
  rw [show BitVec.ofInt 64 80 = BitVec.ofNat 64 80 by decide]

theorem KAt.regB (hk : KAt m0 vars ks st) (h : (r, B0) ∈ ks) :
    (st.regs.getXReg r).toBitVec = fbA m0 + BitVec.ofNat 64 1104 := by
  rw [hk.reg h]
  show fbA m0 + BitVec.ofInt 64 1104 = _
  rw [show BitVec.ofInt 64 1104 = BitVec.ofNat 64 1104 by decide]

/-- The loads' symbolic state describes the machine at entry `j`. -/
theorem match_loS (hk : KAt m0 vars ks st) {A B CT : XReg} (hA : (A, A0) ∈ ks)
    (hB : (B, B0) ∈ ks) {j : Nat}
    (hct : (st.regs.getXReg CT).toBitVec = BitVec.ofNat 64 (16 * j)) :
    Match (Env.ofMachine st (bufR m0 j)) (loS A B CT) st :=
  match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl trivial trivial trivial
    ⟨by
      show BinOp.apply .add .W64 (st.regs.getXReg A).toBitVec (st.regs.getXReg CT).toBitVec =
        fbA m0 + BitVec.ofNat 64 (80 + 16 * j) + BitVec.ofInt 64 0
      rw [hk.regA hA, hct]
      exact add_off _ _ _,
    by
      show BinOp.apply .add .W64 (st.regs.getXReg B).toBitVec (st.regs.getXReg CT).toBitVec =
        fbA m0 + BitVec.ofNat 64 (1104 + 16 * j) + BitVec.ofInt 64 0
      rw [hk.regB hB, hct]
      exact add_off _ _ _, trivial⟩

end

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData}

/-- **A turn of an inner loop**: entry `n0` of the rows folded. -/
theorem innerStep (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (ok : Ok c.a m0) {vars : Nat → BitVec 64} {ks : List (XReg × Sym)} (hw : wfK ks = true)
    {A B CT : XReg} (hA : (A, A0) ∈ ks) (hB : (B, B0) ∈ ks) (h22 : (XReg.X22, V0) ∈ ks)
    (h23 : (XReg.X23, V1) ∈ ks) {cc : EW} (hv0 : vars 0 = cc.c0.toBitVec)
    (hv1 : vars 1 = cc.c1.toBitVec)
    {bL : List Directive} {kL : Nat} (hinL : bL.IsInfixAt code kL) (hneL : bL ≠ [])
    {SL : SState} (hxL : exec bL (loS A B CT) = some (SL, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    {lo0 lo1 aux : XReg} {auxv : Sym} (hshL : LSh .X22 .X23 lo0 lo1 (loS A B CT) SL = true)
    (hLx : SL.reg aux = some auxv)
    (hLct : SL.reg CT = some (.bin .add .W64 (.reg CT) (.lit 16)))
    (hLk : keepK ks SL = true) (hcx : calleeSaved aux = true) (hcc : calleeSaved CT = true)
    {bS : List Directive} {kS kE : Nat} (hkS : kL + bL.length = kS)
    (hinS : bS.IsInfixAt code kS) (hneS : bS ≠ []) {S0 SS : SState} {lbl : Label}
    (hxS : exec bS S0 = some (SS, .cond (notEnd CT) lbl))
    (hlbl : Labels.label lbl = Host.addrOf (k + kL)) (hkE : kS + bS.length = kE)
    {C : Nat} (hmem : SS.mem = stW lo0 lo1 C) (hsp : SS.sp = S0.sp)
    (hSk : keepK ks SS = true) (hSct : SS.reg CT = some (.reg CT))
    {j o n0 : Nat} (hj : j < 64) (hn0 : o + C = 16 * n0) (hn0' : n0 < 4096)
    {auxVal : BitVec 64}
    (haux : ∀ st : MachineData, KAt m0 vars ks st →
      (st.regs.getXReg CT).toBitVec = BitVec.ofNat 64 (16 * j) →
      auxv.eval (Env.ofMachine st (bufR m0 j)) = auxVal)
    (hmS : ∀ st : MachineData, KAt m0 vars ks st → (st.regs.getXReg aux).toBitVec = auxVal →
      Match (Env.ofMachine st [(rwA m0 + BitVec.ofNat 64 o, C + 16)]) S0 st)
    {fa fb G G' : Nat → EW} (hG : G' = fun n ↦ if n = n0 then foldE cc fa fb j else G n)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + kL))
    (hI : Inner c m0 vars ks CT fa fb G j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      (j + 1 < 64 ∧ s'.pc = Host.addrOf (k + kL) ∧
        Inner c m0 vars ks CT fa fb G' (j + 1) s'.data) ∨
      (j + 1 = 64 ∧ s'.pc = Host.addrOf (k + kE) ∧
        Inner c m0 vars ks CT fa fb G' (j + 1) s'.data)) s := by
  have hn := ok.nums
  have hN := hn.hN
  have hrS := hn.rS
  have hrW := hn.rW
  have hsl := spN_lt m0
  have hk := hI.kat
  have hmL := match_loS hk hA hB hI.ct
  refine (stepL hp hmul ok hinL hneL hxL hshL hj hpc hI.mid hmL hI.bufA hI.bufB).bind
    fun s2 ⟨hpc2, hmid2, hso2, hprod, hlo0, hlo1, hreg2⟩ ↦ ?_
  have hk2' : ∀ p ∈ ks, s2.data.regs.getXReg p.1 = s.data.regs.getXReg p.1 := fun p hp ↦
    UInt64.toBitVec_inj.mp (hreg2 p.1 _ (wfK_callee hw hp) (keepK_reg hLk hp))
  have hk2 : KAt m0 vars ks s2.data :=
    KAt.of_reg hmid2.body.sp fun ⟨r, v⟩ hp ↦ by rw [hk2' _ hp]; exact hk.reg hp
  have hct2 : (s2.data.regs.getXReg CT).toBitVec = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [hreg2 CT _ hcc hLct]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hI.ct]
    rw [show 16 * (j + 1) = 16 * j + 16 by omega, BitVec.ofNat_add]
  have hx2 : (s2.data.regs.getXReg aux).toBitVec = auxVal := by
    rw [hreg2 aux _ hcx hLx]
    exact haux _ hk hI.ct
  refine (stepS hp ok hinS hneS hxS (lo0 := lo0) (lo1 := lo1) (C := C) hmem hsp (o := o)
    (by omega) (by rw [hpc2, Nat.add_assoc, hkS]) hmid2 (hmS _ hk2 hx2)).bind
    fun s3 ⟨hm3, hpc3, hmid3, hso3, hew3⟩ ↦ ?_
  have hk3' : ∀ p ∈ ks, s3.data.regs.getXReg p.1 = s2.data.regs.getXReg p.1 := fun p hp ↦
    UInt64.toBitVec_inj.mp (hm3.regs p.1 _ (keepK_reg hSk hp))
  have hk3 : KAt m0 vars ks s3.data :=
    KAt.of_reg hmid3.body.sp fun ⟨r, v⟩ hp ↦ by rw [hk3' _ hp, hk2' _ hp]; exact hk.reg hp
  have hct3 : (s3.data.regs.getXReg CT).toBitVec = BitVec.ofNat 64 (16 * (j + 1)) :=
    (hm3.regs CT _ hSct).trans hct2
  have keepF : ∀ {o' : Nat} {f : Nat → EW}, o' + 1024 ≤ 2224 → 56 ≤ o' →
      ElemsAt s.data.dmem (fbA m0 + BitVec.ofNat 64 o') f 64 →
      ElemsAt s3.data.dmem (fbA m0 + BitVec.ofNat 64 o') f 64 := fun {o' f} ho1 ho2 h ↦ by
    have e := fbA_add hn (o := o') (by omega)
    refine ElemsAt.keepN (ElemsAt.keepN h hso2 (by rw [e]; omega) fun q hq ↦ ?_) hso3
      (by rw [e]; omega) fun q hq ↦ ?_
    · unfold MulR at hq
      rw [e]
      omega
    · rw [e]
      omega
  have hrows : ElemsAt s3.data.dmem (rwA m0) G' 4096 := by
    rw [hG]
    refine ElemsAt.setN (ElemsAt.keepN hI.rows hso2 (by omega) fun q hq ↦ ?_) (by omega) hn0'
      hso3 (fun q hq ↦ by omega) ?_
    · unfold MulR at hq
      omega
    · rw [← hn0]
      have e0 : s.data.regs.getXReg .X22 = cc.c0 :=
        UInt64.toBitVec_inj.mp ((hk.reg h22).trans hv0)
      have e1 : s.data.regs.getXReg .X23 = cc.c1 :=
        UInt64.toBitVec_inj.mp ((hk.reg h23).trans hv1)
      rw [e0, e1] at hprod
      rw [← foldE_eq hprod hlo0 hlo1]
      exact hew3
  have hI3 : Inner c m0 vars ks CT fa fb G' (j + 1) s3.data :=
    ⟨hmid3, hk3, hct3, keepF (by decide) (by decide) hI.bufA,
      keepF (by decide) (by decide) hI.bufB, hrows⟩
  have hc : SBool.eval (Env.ofMachine s2.data [(rwA m0 + BitVec.ofNat 64 o, C + 16)])
      (notEnd CT) = decide (j + 1 < 64) := by
    simp only [notEnd, SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs, hct2]
    rcases Nat.lt_or_ge (j + 1) 64 with hl | hl
    · have : (BitVec.ofNat 64 (16 * (j + 1)) == BitVec.ofNat 64 1024) = false := by
        rw [beq_eq_false_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
        omega
      simp only [this, Bool.not_false, decide_eq_true hl]
    · rw [show j + 1 = 64 by omega]
      decide
  simp only [PcOk] at hpc3
  rw [hc] at hpc3
  rcases Nat.lt_or_ge (j + 1) 64 with hl | hl
  · simp only [hl, decide_true, ↓reduceIte] at hpc3
    exact .done _ (Or.inl ⟨hl, hpc3.trans hlbl, hI3⟩)
  · simp only [show ¬j + 1 < 64 by omega, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
    exact .done _ (Or.inr ⟨by omega, by rw [hpc3]; congr 1; omega, hI3⟩)

/-- **An unrolled round's inner loop** (stores through X21 = `D` + counter, at `1024 i`). -/
theorem innerD_run (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (ok : Ok c.a m0) {vars : Nat → BitVec 64} {ks : List (XReg × Sym)} (hw : wfK ks = true)
    {A B CT D : XReg} (hA : (A, A0) ∈ ks) (hB : (B, B0) ∈ ks) (h22 : (XReg.X22, V0) ∈ ks)
    (h23 : (XReg.X23, V1) ∈ ks) (hD : (D, P) ∈ ks) {cc : EW} (hv0 : vars 0 = cc.c0.toBitVec)
    (hv1 : vars 1 = cc.c1.toBitVec)
    {bL : List Directive} {kL : Nat} (hinL : bL.IsInfixAt code kL) (hneL : bL ≠ [])
    {SL : SState} (hxL : exec bL (loS A B CT) = some (SL, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hshL : LSh .X22 .X23 .X19 .X20 (loS A B CT) SL = true)
    (hLx : SL.reg .X21 = some (.bin .add .W64 (.reg D) (.reg CT)))
    (hLct : SL.reg CT = some (.bin .add .W64 (.reg CT) (.lit 16)))
    (hLk : keepK ks SL = true) (hcc : calleeSaved CT = true)
    {bS : List Directive} {kS kE : Nat} (hkS : kL + bL.length = kS)
    (hinS : bS.IsInfixAt code kS) (hneS : bS ≠ []) {SS : SState} {lbl : Label} {i : Nat}
    (hxS : exec bS (dstS (1024 * i)) = some (SS, .cond (notEnd CT) lbl))
    (hlbl : Labels.label lbl = Host.addrOf (k + kL)) (hkE : kS + bS.length = kE)
    (hmem : SS.mem = stW .X19 .X20 (1024 * i)) (hsp : SS.sp = .sp)
    (hSk : keepK ks SS = true) (hSct : SS.reg CT = some (.reg CT)) (hi : i < 64)
    {fa fb : Nat → EW} {G : Nat → Nat → EW}
    (hG : ∀ j < 64, G (j + 1) = fun n ↦ if n = 64 * i + j then foldE cc fa fb j else G j n)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + kL))
    (hI : Inner c m0 vars ks CT fa fb (G 0) 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + kE) ∧
      Inner c m0 vars ks CT fa fb (G 64) 64 s'.data) s :=
  loopN (P := fun j st ↦ Inner c m0 vars ks CT fa fb (G j) j st)
    (fun j _ hj hpc hI ↦ innerStep hp hmul ok hw hA hB h22 h23 hv0 hv1 hinL hneL hxL hshL hLx
      hLct hLk rfl hcc hkS hinS hneS hxS hlbl hkE hmem hsp hSk hSct (o := 16 * j)
      (n0 := 64 * i + j) hj (by omega) (by omega)
      (fun st hk hct ↦ by
        show BinOp.apply .add .W64 (st.regs.getXReg D).toBitVec (st.regs.getXReg CT).toBitVec =
          rwA m0 + BitVec.ofNat 64 (16 * j)
        rw [hk.regP hD, hct]
        simp only [BinOp.apply, low_W64, ext_W64])
      (fun st _ h21 ↦ match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
        ⟨by
          show (st.regs.getXReg .X21).toBitVec =
            rwA m0 + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 0
          rw [h21, ofInt0, NativeRustcVm.addr_add_zero], trivial⟩)
      (hG j hj) hpc hI)
    (by decide) hpc hI

/-- **A looped round's inner loop** (stores through X24 = row `i` plus the counter `OC`). -/
theorem innerL_run (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (ok : Ok c.a m0) {vars : Nat → BitVec 64} {ks : List (XReg × Sym)} (hw : wfK ks = true)
    {A B CT OC : XReg} (hA : (A, A0) ∈ ks) (hB : (B, B0) ∈ ks) (h22 : (XReg.X22, V0) ∈ ks)
    (h23 : (XReg.X23, V1) ∈ ks) (h24 : (XReg.X24, .bin .add .W64 P (.var 3)) ∈ ks) {cc : EW}
    (hv0 : vars 0 = cc.c0.toBitVec) (hv1 : vars 1 = cc.c1.toBitVec) {i : Nat}
    (hv3 : vars 3 = BitVec.ofNat 64 (1024 * i))
    {bL : List Directive} {kL : Nat} (hinL : bL.IsInfixAt code kL) (hneL : bL ≠ [])
    {SL : SState} (hxL : exec bL (loS A B CT) = some (SL, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hshL : LSh .X22 .X23 .X20 .X21 (loS A B CT) SL = true)
    (hLx : SL.reg OC = some (.reg CT))
    (hLct : SL.reg CT = some (.bin .add .W64 (.reg CT) (.lit 16)))
    (hLk : keepK ks SL = true) (hco : calleeSaved OC = true) (hcc : calleeSaved CT = true)
    {bS : List Directive} {kS kE : Nat} (hkS : kL + bL.length = kS)
    (hinS : bS.IsInfixAt code kS) (hneS : bS ≠ []) {SS : SState} {lbl : Label}
    (hxS : exec bS (lstS OC) = some (SS, .cond (notEnd CT) lbl))
    (hlbl : Labels.label lbl = Host.addrOf (k + kL)) (hkE : kS + bS.length = kE)
    (hmem : SS.mem = stW .X20 .X21 0) (hsp : SS.sp = .sp)
    (hSk : keepK ks SS = true) (hSct : SS.reg CT = some (.reg CT)) (hi : i < 64)
    {fa fb : Nat → EW} {G : Nat → Nat → EW}
    (hG : ∀ j < 64, G (j + 1) = fun n ↦ if n = 64 * i + j then foldE cc fa fb j else G j n)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + kL))
    (hI : Inner c m0 vars ks CT fa fb (G 0) 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + kE) ∧
      Inner c m0 vars ks CT fa fb (G 64) 64 s'.data) s :=
  loopN (P := fun j st ↦ Inner c m0 vars ks CT fa fb (G j) j st)
    (fun j _ hj hpc hI ↦ innerStep hp hmul ok hw hA hB h22 h23 hv0 hv1 hinL hneL hxL hshL hLx
      hLct hLk hco hcc hkS hinS hneS hxS hlbl hkE hmem hsp hSk hSct (o := 1024 * i + 16 * j)
      (n0 := 64 * i + j) hj (by omega) (by omega) (fun _ _ hct ↦ hct)
      (fun st hk hoc ↦ by
        have e24 : (st.regs.getXReg .X24).toBitVec = rwA m0 + BitVec.ofNat 64 (1024 * i) := by
          rw [hk.reg h24]
          show BinOp.apply .add .W64 (rwA m0 + BitVec.ofInt 64 0) (vars 3) = _
          rw [hv3, ofInt0, NativeRustcVm.addr_add_zero]
          simp only [BinOp.apply, low_W64, ext_W64]
        refine match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
          ⟨?_, ?_, trivial⟩
        · show BinOp.apply .add .W64 (st.regs.getXReg .X24).toBitVec
            (UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 (st.regs.getXReg OC).toBitVec) =
              rwA m0 + BitVec.ofNat 64 (1024 * i + 16 * j) + BitVec.ofInt 64 0
          rw [memExtend_uxtx0, e24, hoc]
          exact add_off _ _ _
        · show BinOp.apply .add .W64 (st.regs.getXReg .X24).toBitVec
            (st.regs.getXReg OC).toBitVec =
              rwA m0 + BitVec.ofNat 64 (1024 * i + 16 * j) + BitVec.ofInt 64 0
          rw [e24, hoc]
          exact add_off _ _ _)
      (hG j hj) hpc hI)
    (by decide) hpc hI

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
