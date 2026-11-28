module

public import NativeRustcArm.XmssVerify.TopBlocks
public import NativeRustcArm.XmssVerify.BotTurn

/-!
# `xmss_verify`: a turn of the top path loop

`TopAt w m₀ m z cur`: at block 18 before turn `z`, the current node `cur` in `x9`, `x8`. A turn
(`topTurn`): block 18, `memset`, the node's hash (`hashNode` with block 19), block 24: the next
node `topStep w cur z` (`pathStep` of the top layer), at block 18 again or, after the last turn,
at block 25.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss
  NativeRustc.Keccak

set_option Elab.async false

@[expose] public section

/-- At the top path loop's head before turn `z`, the current node `cur` in `x9`, `x8`. -/
structure TopAt (w : Nat → UInt64) (m₀ m : MachineData) (z : Nat) (cur : List UInt8) : Prop where
  common : Common m₀ m
  x19 : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 (li1 w).toNat
  x20 : (m.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 (z + 1)
  x21 : (m.regs.getXReg .X21).toBitVec = ad m₀ (fb + 5392)
  x22 : (m.regs.getXReg .X22).toBitVec = ad m₀ (fb + 3692 + 16 * z)
  x23 : (m.regs.getXReg .X23).toBitVec = ad m₀ (fb + 5016)
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 1
  x25 : (m.regs.getXReg .X25).toBitVec = ad m₀ (fb + 4976)
  x26 : (m.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 3
  x27 : (m.regs.getXReg .X27).toBitVec = ad m₀ (fb + 2448)
  node : regBytes (m.regs.getXReg .X9).toBitVec ++ regBytes (m.regs.getXReg .X8).toBitVec = cur
  pk : BytesAt m.dmem (ad m₀ (fb + 2448)) (pkB w)
  top : BytesAt m.dmem (ad m₀ (fb + 3692)) (topL w).memBytes

/-- The top layer's path step. -/
def topStep (w : Nat → UInt64) (cur : List UInt8) (z : Nat) : List UInt8 :=
  pathStep (pp w) 1 (li1 w).toNat (topL w).path cur z

end

public section

theorem li1_lt (w : Nat → UInt64) : (li1 w).toNat < 2 ^ 64 := by
  have := (li1 w).toNat_lt
  omega

theorem topL_memBytes (w : Nat → UInt64) : (topL w).memBytes.length = 1200 :=
  length_memBytes (by rw [length_sigB])

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **A turn of the top path loop.** -/
theorem topTurn {k : Nat} (hp : Placed code k) (Cs : Callees) (P : Pre w m₀) {z : Nat}
    (hz : z < 16) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b18Offset)) {cur : List UInt8}
    (hl : cur.length = 16) (h : TopAt w m₀ st.data z cur) :
    Eventually (step1 Host.exe) (fun st' =>
      (z + 1 < 16 ∧ st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b18Offset) ∧ TopAt w m₀ st'.data (z + 1) (topStep w cur z)) ∨
      (z + 1 = 16 ∧ st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b25Offset) ∧ TopAt w m₀ st'.data 16 (topStep w cur z))) st := by
  have C := h.common
  -- Block 18.
  have hwf := frame_wf P C (fun _ => BitVec.ofNat 64 (16 * z))
  have hm := match_initL P C (known := knownT) (z := z) (by omega)
    ⟨h.x21.trans (eval_ptr0 _).symm, h.x25.trans (eval_ptr0 _).symm,
      h.x23.trans (eval_ptr0 _).symm, h.x27.trans (eval_ptr0 _).symm,
      h.x22.trans (eval_pathPtr _ _).symm, h.x24, h.x26, trivial⟩
  obtain ⟨g0, g1, g2, gsp, g29₀, g29, gw, gsave, gk, gr, gk1, gk2⟩ := st18_facts
  refine call_step (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) b18_exec' hwf hpc hm
    fun st1 hpc1 hm1 => ?_
  change Match _ st18 st1.data at hm1
  have C1 := Common.block P C hwf hm hm1 (by rw [gsp]; rfl) g29₀ g29 gw gsave
  have hreg1 : ∀ {r : XReg} {v : Sym}, st18.reg r = some v →
      (st1.data.regs.getXReg r).toBitVec =
        v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) :=
    fun hr => hm1.regs _ _ hr
  -- The children and the address.
  have hsib : BytesAt st.data.dmem (ad m₀ (fb + 3692 + 16 * z)) ((topL w).path.getD z []) := by
    have := layer_path (w := w) (c := 1204) (by decide) h.top hz
    rwa [ad_add] at this
  have hsl : ((topL w).path.getD z []).length = 16 := length_path_getD (by decide) hz
  have hChl : (if (li1 w).toNat >>> z &&& 1 = 0 then cur ++ (topL w).path.getD z []
      else (topL w).path.getD z [] ++ cur).length = 32 := by
    split <;> rw [List.length_append, hl, hsl]
  have hc18 := c18_eval (env := Env.ofMachine st.data [(ad m₀ fb, 5872)]
    fun _ => BitVec.ofNat 64 (16 * z)) hz (li1_lt w) h.x20 h.x19
  obtain ⟨ch0, ch1, ch2, ch3⟩ := st18_children
  have hloadx : ∀ o, (Sym.loadx 0 o (.var 0) 8).eval
      (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) =
      (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)).load 0
        (o + 16 * z) 8 := by
    intro o
    simp only [Sym.eval]
    congr 2
    show (BitVec.ofNat 64 (16 * z)).toNat = 16 * z
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hCh := childrenAt hm1 ch0 ch1 ch2 ch3 (cur := cur) (sib := (topL w).path.getD z [])
    h.node
    (by
      rw [hloadx, hloadx, regBytes_frame (bs := ((topL w).path.getD z []).take 8)
          (by rw [List.length_take, hsl]; rfl) (by rw [← Nat.add_assoc]; exact hsib.take 8),
        regBytes_frame (bs := ((topL w).path.getD z []).drop 8)
          (by rw [List.length_drop, hsl])
          (by
            have := hsib.drop (n := 8) (by rw [hsl]; decide)
            rwa [ad_add, show fb + 3692 + 16 * z + 8 = fb + (3700 + 16 * z) by omega] at this),
        List.take_append_drop])
  rw [hc18] at hCh
  simp only [decide_eq_true_eq] at hCh
  obtain ⟨a1, a2, a3, a4, a5⟩ := st18_addr
  have hA := addrAt hm1 a1 a2 a3 a4 a5 (hi := layerHi 1 (z + 1).toUInt32)
    (lo18_toNat hz (li1_lt w) h.x20 h.x19) (by
      show [UInt8.ofNat (st.data.regs.getXReg .X20).toBitVec.toNat,
        UInt8.ofNat ((st.data.regs.getXReg .X20).toBitVec.toNat / 256),
        UInt8.ofNat (UnOp.apply (.ubfm 16 31) .W32 (BinOp.apply .orr .W32
          (st.data.regs.getXReg .X20).toBitVec (BitVec.ofNat 64 8388608))).toNat] = _
      rw [h.x20]
      exact hiTop z hz)
  -- `memset` of the hasher.
  have e0 : st1.data.regs.X0.toBitVec = ad m₀ (fb + 5408) := (hreg1 g0).trans (eval_ptr0 _)
  have e2 : st1.data.regs.X2.toNat = 344 := toNat_lit (hreg1 g2) (by decide)
  have e1 : st1.data.regs.X1.toUInt8 = 0 := by
    have := toNat_lit (hreg1 g1) (by decide)
    apply UInt8.toNat_inj.mp
    rw [UInt64.toNat_toUInt8]
    rw [show st1.data.regs.X1.toNat = (st1.data.regs.getXReg .X1).toNat from rfl, this]
    rfl
  refine memsetCall Cs.memset P hpc1.1 hpc1.2 C1 (dst := 5408) e0 e2 (by omega)
    fun st2 hpc2 C2 hs2 hb2 hsm2 => ?_
  rw [e1] at hb2
  have k2 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5408 →
      BytesAt st1.data.dmem (ad m₀ (fb + o)) bs → BytesAt st2.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hb => keep_callR P C1 (Nat.zero_le _) (by decide) hsm2 hb (by omega) (Or.inl ho)
  have k1 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5872 →
      firstOverlap 0 o bs.length st18.mem = none →
      BytesAt st.data.dmem (ad m₀ (fb + o)) bs → BytesAt st1.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hc hb => frameKeep hm1 ho hc hb
  have hpk1 := k1 (by rw [length_pkB]; decide) (by rw [length_pkB]; exact gk1) h.pk
  have htop1 := k1 (by rw [topL_memBytes]; decide) (by rw [topL_memBytes]; exact gk2) h.top
  have g27 : st18.reg .X27 = some (.ptr 0 2448) := gk (.X27, .ptr 0 2448) (by simp [knownT])
  -- The node's hash.
  refine hashNode Cs P (j9 := k + NativeRustcArm.Xmss.XmssVerify.b19Offset) (j := k + NativeRustcArm.Xmss.XmssVerify.b20Offset) (ds9 := b19)
    (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) rfl b19_exec' st19_facts (hashPos_top hp)
    (hpc2.trans rfl) C2 ⟨(congrArg UInt64.toBitVec (hs2.1 .X27 rfl)).trans
      ((hreg1 g27).trans ((eval_ptr0 _).trans (eval_ptr0 _).symm)), trivial⟩
    (length_pp w) (length_address _ _) hChl hb2
    (k2 (by rw [length_pp]; decide) (pp_at hpk1)) (k2 (by rw [length_address]) hA)
    (k2 (by rw [hChl]; decide) hCh) fun st3 hpc3 C3 hs3 hD hk3 => ?_
  -- Block 24.
  have hs13 := hs2.trans hs3
  have hx3 : ∀ {r : XReg} {v : Sym}, calleeSaved r = true → st18.reg r = some v →
      (st3.data.regs.getXReg r).toBitVec =
        v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) :=
    fun hc hr => by rw [hs13.1 _ hc]; exact hreg1 hr
  have hwf3 := frame_wf P C3
  have hm3 := match_stF0 P C3 (known := []) trivial
  obtain ⟨f_sp, f29, fmem, fk, f20, f22, f9, f8⟩ := st24_facts
  refine exec_at (b24_in_code.trans hp.1 (List.cons_ne_nil _ _)) b24_exec' hwf3 (hpc3.trans rfl)
    hm3 fun st4 hm4 hpc4 => .done _ ?_
  have C4 := Common.block P C3 hwf3 hm3 hm4 (by rw [f_sp]; rfl) rfl f29
    (by simp [writesIn, fmem]) (fun x _ _ => by rw [fmem]; rfl)
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 fmem
  have hk4 : ∀ {r : XReg}, r ∈ [XReg.X19, .X21, .X23, .X24, .X25, .X26, .X27] →
      st4.data.regs.getXReg r = st3.data.regs.getXReg r :=
    fun hr => UInt64.toBitVec_inj.mp (hm4.regs _ _ (fk _ hr))
  have kAll : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5016 →
      BytesAt st1.data.dmem (ad m₀ (fb + o)) bs → BytesAt st4.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hb => hd4 ▸ hk3 _ _ ho (k2 (by omega) hb)
  have h20 : (st3.data.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 (z + 1) := by
    rw [hx3 rfl (gr .X20 (by simp))]
    exact h.x20
  -- The next node.
  set D := hashBytes (pp w ++ address (tweak 3 (layerHi 1 (z + 1).toUInt32)
    ((li1 w).toNat >>> (z + 1)).toUInt32) ++
    (if (li1 w).toNat >>> z &&& 1 = 0 then cur ++ (topL w).path.getD z []
      else (topL w).path.getD z [] ++ cur)) with hDdef
  have hDl : D.length = 32 := length_hashBytes _
  have n0 : regBytes (st4.data.regs.getXReg .X9).toBitVec = D.take 8 := by
    rw [hm4.regs _ _ f9]
    exact regBytes_frame (bs := D.take 8) (by simp [hDl]) (hD.take 8)
  have n1 : regBytes (st4.data.regs.getXReg .X8).toBitVec = (D.drop 8).take 8 := by
    rw [hm4.regs _ _ f8]
    exact regBytes_frame (bs := (D.drop 8).take 8) (by simp [hDl])
      (by have := (hD.drop (n := 8) (by omega)).take 8; rwa [ad_add] at this)
  have hnext : topStep w cur z = D.take 8 ++ (D.drop 8).take 8 := by
    rw [← List.take_add]
    rfl
  have hc : c24.eval (Env.ofMachine st3.data [(ad m₀ fb, 5872)]) = decide (z + 1 ≠ 16) := by
    simp only [c24, SBool.eval, CmpOp.apply, Sym.eval, binAdd64, low_W64, Env.ofMachine_regs, h20]
    by_cases h16 : z + 1 = 16
    · rw [h16]; decide
    · simp only [h16, ne_eq, not_false_eq_true, decide_true, Bool.not_eq_true',
        beq_eq_false_iff_ne]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show z + 1 < 2 ^ 64 by omega)] at this
      omega
  have B : TopAt w m₀ st4.data (z + 1) (topStep w cur z) := by
    refine ⟨C4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [n0, n1, hnext], ?_, ?_⟩
    · rw [hk4 (by simp), hx3 rfl (gr .X19 (by simp))]
      exact h.x19
    · rw [hm4.regs _ _ f20]
      simp only [Sym.eval, binAdd64, Env.ofMachine_regs, h20]
      rw [← BitVec.ofNat_add]
    · rw [hk4 (by simp), hx3 rfl (gk (.X21, .ptr 0 5392) (by simp [knownT]))]
      exact eval_ptr0 _
    · rw [hm4.regs _ _ f22]
      have g22 : st18.reg .X22 = some (.bin .add .W64 (.ptr 0 3692) (.var 0)) :=
        gk (.X22, .bin .add .W64 (.ptr 0 3692) (.var 0)) (by simp [knownT])
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [hx3 rfl g22, show (Sym.bin .add .W64 (.ptr 0 3692) (.var 0)).eval
          (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) =
          ad m₀ (fb + 3692 + 16 * z) from eval_pathPtr _ _, ad_add,
        show fb + 3692 + 16 * z + 16 = fb + 3692 + 16 * (z + 1) by omega]
    · rw [hk4 (by simp), hx3 rfl (gk (.X23, .ptr 0 5016) (by simp [knownT]))]
      exact eval_ptr0 _
    · rw [hk4 (by simp), hx3 rfl (gk (.X24, .lit 1) (by simp [knownT]))]
      rfl
    · rw [hk4 (by simp), hx3 rfl (gk (.X25, .ptr 0 4976) (by simp [knownT]))]
      exact eval_ptr0 _
    · rw [hk4 (by simp), hx3 rfl (gk (.X26, .lit 3) (by simp [knownT]))]
      rfl
    · rw [hk4 (by simp), hx3 rfl g27]
      exact eval_ptr0 _
    · exact kAll (by rw [length_pkB]; decide) hpk1
    · exact kAll (by rw [topL_memBytes]; decide) htop1
  simp only [PcOk, hc] at hpc4
  by_cases h16 : z + 1 = 16
  · simp only [h16, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false] at hpc4
    exact Or.inr ⟨h16, hpc4.trans rfl, h16 ▸ B⟩
  · simp only [h16, ne_eq, not_false_eq_true, decide_true, ite_true] at hpc4
    exact Or.inl ⟨by omega, hpc4.trans (hp.label NativeRustcArm.Xmss.XmssVerify.label_7_at), B⟩

end

end NativeRustcArm.Xmss.XmssVerify
