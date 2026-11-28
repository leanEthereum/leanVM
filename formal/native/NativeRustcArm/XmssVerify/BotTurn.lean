module

public import NativeRustcArm.XmssVerify.BotBlocks
public import NativeRustcArm.XmssVerify.Layer

/-!
# `xmss_verify`: a turn of the bottom path loop

`BotAt w m₀ m z cur`: at block 8 before turn `z`, the current node `cur` at `4954`. A turn
(`botTurn`): block 8, `memset`, the node's hash (`hashNode` with block 9), block 14: the next
node `botStep w cur z` (`pathStep` of the bottom layer), at block 8 again or, after the last
turn, at block 15.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss
  NativeRustc.Keccak

set_option Elab.async false

@[expose] public section

/-- At the bottom path loop's head before turn `z`, the current node `cur` at `4954`. -/
structure BotAt (w : Nat → UInt64) (m₀ m : MachineData) (z : Nat) (cur : List UInt8) : Prop where
  common : Common m₀ m
  x19 : (m.regs.getXReg .X19).toBitVec = ad m₀ (fb + 4976)
  x20 : (m.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 3
  x21 : (m.regs.getXReg .X21).toBitVec = ad m₀ (fb + 5392)
  x22 : (m.regs.getXReg .X22).toBitVec = ad m₀ (fb + 3692)
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (li w).toNat
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 z
  x25 : (m.regs.getXReg .X25).toBitVec = ad m₀ (fb + 4896)
  x26 : (m.regs.getXReg .X26).toBitVec = ad m₀ (fb + 5016)
  x27 : (m.regs.getXReg .X27).toBitVec = ad m₀ (fb + 2492 + 16 * z)
  x28 : (m.regs.getXReg .X28).toBitVec = BitVec.ofNat 64 1
  cur : BytesAt m.dmem (ad m₀ (fb + 4954)) cur
  word : BytesAt m.dmem (ad m₀ (fb + 0)) (wordBytes (w 8))
  pk : BytesAt m.dmem (ad m₀ (fb + 2448)) (pkB w)
  layers : BytesAt m.dmem (ad m₀ (fb + 2492)) ((bottomL w).memBytes ++ (topL w).memBytes)

/-- The bottom layer's path step. -/
def botStep (w : Nat → UInt64) (cur : List UInt8) (z : Nat) : List UInt8 :=
  pathStep (pp w) 0 (li w).toNat (bottomL w).path cur z

end

public section

theorem length_pp (w : Nat → UInt64) : (pp w).length = 16 := by
  rw [pp, List.length_drop, length_pkB]

theorem length_address (hi lo : UInt32) : (address (tweak 3 hi lo)).length = 16 := by
  simp [address, tweak, NativeRustc.length_u32Bytes]

theorem bottomL_memBytes (w : Nat → UInt64) : (bottomL w).memBytes.length = 1200 :=
  length_memBytes (by rw [length_sigB]; decide)

theorem pp_at {d : DataMem} {m₀ : MachineData} {w : Nat → UInt64}
    (h : BytesAt d (ad m₀ (fb + 2448)) (pkB w)) : BytesAt d (ad m₀ (fb + 2464)) (pp w) := by
  have := h.drop (n := 16) (by rw [length_pkB]; decide)
  rwa [ad_add] at this

theorem li_lt (w : Nat → UInt64) : (li w).toNat < 2 ^ 64 := by
  have := (li w).toNat_lt
  omega

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **A turn of the bottom path loop.** -/
theorem botTurn {k : Nat} (hp : Placed code k) (Cs : Callees) (P : Pre w m₀) {z : Nat}
    (hz : z < 16) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b8Offset)) {cur : List UInt8}
    (hl : cur.length = 16) (h : BotAt w m₀ st.data z cur) :
    Eventually (step1 Host.exe) (fun st' =>
      (z + 1 < 16 ∧ st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b8Offset) ∧ BotAt w m₀ st'.data (z + 1) (botStep w cur z)) ∨
      (z + 1 = 16 ∧ st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b15Offset) ∧ BotAt w m₀ st'.data 16 (botStep w cur z))) st := by
  have C := h.common
  -- Block 8.
  have hwf := frame_wf P C (fun _ => BitVec.ofNat 64 (16 * z))
  have hm := match_initL P C (known := knownB) (z := z) (by omega)
    ⟨h.x21.trans (eval_ptr0 _).symm, h.x25.trans (eval_ptr0 _).symm,
      h.x26.trans (eval_ptr0 _).symm, h.x19.trans (eval_ptr0 _).symm,
      h.x27.trans (eval_pathPtr _ _).symm, h.x28, h.x20, trivial⟩
  obtain ⟨g0, g1, g2, gsp, g29₀, g29, gw, gsave, g24, gk, gr, gk0, gk1, gk2⟩ := st8_facts
  refine call_step (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) b8_exec' hwf hpc hm
    fun st1 hpc1 hm1 => ?_
  change Match _ st8 st1.data at hm1
  have C1 := Common.block P C hwf hm hm1 (by rw [gsp]; rfl) g29₀ g29 gw gsave
  have hreg1 : ∀ {r : XReg} {v : Sym}, st8.reg r = some v →
      (st1.data.regs.getXReg r).toBitVec =
        v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) :=
    fun hr => hm1.regs _ _ hr
  -- The children and the address.
  have hsib : BytesAt st.data.dmem (ad m₀ (fb + 2492 + 16 * z)) ((bottomL w).path.getD z []) := by
    have := layer_path (w := w) (c := 4) (by decide) h.layers.left hz
    rwa [ad_add] at this
  have hsl : ((bottomL w).path.getD z []).length = 16 := length_path_getD (by decide) hz
  have hChl : (if (li w).toNat >>> z &&& 1 = 0 then cur ++ (bottomL w).path.getD z []
      else (bottomL w).path.getD z [] ++ cur).length = 32 := by
    split <;> rw [List.length_append, hl, hsl]
  have hc8 := c8_eval (env := Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z))
    hz (li_lt w) h.x24 h.x23
  obtain ⟨ch0, ch1, ch2, ch3⟩ := st8_children
  have hloadx : ∀ o, (Sym.loadx 0 o (.var 0) 8).eval
      (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) =
      (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)).load 0
        (o + 16 * z) 8 := by
    intro o
    simp only [Sym.eval]
    congr 2
    show (BitVec.ofNat 64 (16 * z)).toNat = 16 * z
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hCh := childrenAt hm1 ch0 ch1 ch2 ch3 (cur := cur) (sib := (bottomL w).path.getD z [])
    (by
      show regBytes ((Env.ofMachine _ _ _).load 0 4954 8) ++
        regBytes ((Env.ofMachine _ _ _).load 0 4962 8) = cur
      rw [regBytes_frame (o := 4954) (by rw [List.length_take, hl]; rfl) (h.cur.take 8),
        regBytes_frame (o := 4962) (bs := cur.drop 8) (by rw [List.length_drop, hl])
          (by have := h.cur.drop (n := 8) (by omega); rwa [ad_add] at this),
        List.take_append_drop])
    (by
      rw [hloadx, hloadx, regBytes_frame (bs := ((bottomL w).path.getD z []).take 8)
          (by rw [List.length_take, hsl]; rfl) (by rw [← Nat.add_assoc]; exact hsib.take 8),
        regBytes_frame (bs := ((bottomL w).path.getD z []).drop 8)
          (by rw [List.length_drop, hsl])
          (by
            have := hsib.drop (n := 8) (by rw [hsl]; decide)
            rwa [ad_add, show fb + 2492 + 16 * z + 8 = fb + (2500 + 16 * z) by omega] at this),
        List.take_append_drop])
  rw [hc8] at hCh
  simp only [decide_eq_true_eq] at hCh
  obtain ⟨a1, a2, a3, a4, a5⟩ := st8_addr
  have hlvl := lvl8_toNat (env := Env.ofMachine st.data [(ad m₀ fb, 5872)]
    fun _ => BitVec.ofNat 64 (16 * z)) hz h.x24
  have hA := addrAt hm1 a1 a2 a3 a4 a5 (hi := layerHi 0 (z + 1).toUInt32)
    (lo8_toNat hz (li_lt w) h.x24 h.x23) (by
      rw [hlvl]
      show [_, _, UInt8.ofNat (UnOp.apply (.ubfm 16 31) .W32 (lvl8.eval _)).toNat] = _
      rw [ubfm16_toNat, hlvl]
      exact hiBytes_bottom z hz)
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
      firstOverlap 0 o bs.length st8.mem = none →
      BytesAt st.data.dmem (ad m₀ (fb + o)) bs → BytesAt st1.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hc hb => frameKeep hm1 ho hc hb
  have hpk1 := k1 (by rw [length_pkB]; decide) (by rw [length_pkB]; exact gk1) h.pk
  -- The node's hash.
  refine hashNode Cs P (j9 := k + NativeRustcArm.Xmss.XmssVerify.b9Offset) (j := k + NativeRustcArm.Xmss.XmssVerify.b10Offset) (ds9 := b9)
    (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) rfl b9_exec' st9_facts (hashPos_bottom hp)
    (hpc2.trans rfl) C2 trivial (length_pp w) (length_address _ _)
    hChl hb2 (k2 (by rw [length_pp]; decide) (pp_at hpk1))
    (k2 (by rw [length_address]) hA)
    (k2 (by rw [hChl]; decide) hCh) fun st3 hpc3 C3 hs3 hD hk3 => ?_
  -- Block 14.
  have hs13 := hs2.trans hs3
  have hx3 : ∀ {r : XReg} {v : Sym}, calleeSaved r = true → st8.reg r = some v →
      (st3.data.regs.getXReg r).toBitVec =
        v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) :=
    fun hc hr => by rw [hs13.1 _ hc]; exact hreg1 hr
  have hwf3 := frame_wf P C3
  have hm3 := match_stF0 P C3 (known := [(.X25, .ptr 0 4896)])
    ⟨(hx3 rfl (gk (.X25, .ptr 0 4896) (by simp [knownB]))).trans
      ((eval_ptr0 _).trans (eval_ptr0 _).symm), trivial⟩
  obtain ⟨f_sp, f29, fw, fsave, fk, f25, f27, fn0, fn1, fk0, fk1, fk2⟩ := st14_facts
  refine exec_at (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) b14_exec' hwf3 (hpc3.trans rfl)
    hm3 fun st4 hm4 hpc4 => .done _ ?_
  have C4 := Common.block P C3 hwf3 hm3 hm4 (by rw [f_sp]; rfl) rfl f29 fw fsave
  have hk4 : ∀ {r : XReg}, r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X26, .X28] →
      st4.data.regs.getXReg r = st3.data.regs.getXReg r :=
    fun hr => UInt64.toBitVec_inj.mp (hm4.regs _ _ (fk _ hr))
  have k4 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5872 →
      firstOverlap 0 o bs.length st14.mem = none →
      BytesAt st3.data.dmem (ad m₀ (fb + o)) bs → BytesAt st4.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hc hb => frameKeep hm4 ho hc hb
  have kAll : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5016 →
      BytesAt st1.data.dmem (ad m₀ (fb + o)) bs → BytesAt st3.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hb => hk3 _ _ ho (k2 (by omega) hb)
  have h24 : (st3.data.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (z + 1) := by
    rw [hx3 rfl g24]
    apply BitVec.eq_of_toNat_eq
    rw [hlvl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- The next node.
  set D := hashBytes (pp w ++ address (tweak 3 (layerHi 0 (z + 1).toUInt32)
    ((li w).toNat >>> (z + 1)).toUInt32) ++
    (if (li w).toNat >>> z &&& 1 = 0 then cur ++ (bottomL w).path.getD z []
      else (bottomL w).path.getD z [] ++ cur)) with hDdef
  have hDl : D.length = 32 := length_hashBytes _
  have n0 := frameWrite hm4 (o := 4954) (by omega) fn0
  have n1 := frameWrite hm4 (o := 4962) (by omega) fn1
  rw [show (Sym.load 0 5408 8).eval (Env.ofMachine st3.data [(ad m₀ fb, 5872)]) =
      (Env.ofMachine st3.data [(ad m₀ fb, 5872)]).load 0 5408 8 from rfl,
    regBytes_frame (bs := D.take 8) (by simp [hDl]) (hD.take 8)] at n0
  rw [show (Sym.load 0 5416 8).eval (Env.ofMachine st3.data [(ad m₀ fb, 5872)]) =
      (Env.ofMachine st3.data [(ad m₀ fb, 5872)]).load 0 5416 8 from rfl,
    regBytes_frame (bs := (D.drop 8).take 8) (by simp [hDl])
      (by have := (hD.drop (n := 8) (by omega)).take 8; rwa [ad_add] at this)] at n1
  have hnext : botStep w cur z = D.take 8 ++ (D.drop 8).take 8 := by
    rw [← List.take_add]
    rfl
  have hcur4 : BytesAt st4.data.dmem (ad m₀ (fb + 4954)) (botStep w cur z) := by
    rw [hnext]
    exact BytesAt.append_ad n0 (by simp [hDl]; exact n1)
  have hc : c14.eval (Env.ofMachine st3.data [(ad m₀ fb, 5872)]) = decide (z + 1 ≠ 16) := by
    simp only [c14, SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs, h24]
    by_cases h16 : z + 1 = 16
    · rw [h16]; decide
    · simp only [h16, ne_eq, not_false_eq_true, decide_true, Bool.not_eq_true',
        beq_eq_false_iff_ne]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at this
      exact h16 this
  have B : BotAt w m₀ st4.data (z + 1) (botStep w cur z) := by
    refine ⟨C4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcur4, ?_, ?_, ?_⟩
    · rw [hk4 (by simp), hx3 rfl (gk (.X19, .ptr 0 4976) (by simp [knownB]))]
      exact eval_ptr0 _
    · rw [hk4 (by simp), hx3 rfl (gk (.X20, .lit 3) (by simp [knownB]))]
      rfl
    · rw [hk4 (by simp), hx3 rfl (gk (.X21, .ptr 0 5392) (by simp [knownB]))]
      exact eval_ptr0 _
    · rw [hk4 (by simp), hx3 rfl (gr .X22 (by simp))]
      exact h.x22
    · rw [hk4 (by simp), hx3 rfl (gr .X23 (by simp))]
      exact h.x23
    · rw [hk4 (by simp)]
      exact h24
    · rw [hm4.regs _ _ f25]
      exact eval_ptr0 _
    · rw [hk4 (by simp), hx3 rfl (gk (.X26, .ptr 0 5016) (by simp [knownB]))]
      exact eval_ptr0 _
    · rw [hm4.regs _ _ f27]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      have g27 : st8.reg .X27 = some (.bin .add .W64 (.ptr 0 2492) (.var 0)) :=
        gk (.X27, .bin .add .W64 (.ptr 0 2492) (.var 0)) (by simp [knownB])
      rw [hx3 rfl g27, show (Sym.bin .add .W64 (.ptr 0 2492) (.var 0)).eval
          (Env.ofMachine st.data [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) =
          ad m₀ (fb + 2492 + 16 * z) from eval_pathPtr _ _, ad_add,
        show fb + 2492 + 16 * z + 16 = fb + 2492 + 16 * (z + 1) by omega]
    · rw [hk4 (by simp), hx3 rfl (gk (.X28, .lit 1) (by simp [knownB]))]
      rfl
    · exact k4 (by rw [NativeRustc.length_wordBytes]; decide)
        (by rw [NativeRustc.length_wordBytes]; exact fk0)
        (kAll (by rw [NativeRustc.length_wordBytes]; decide)
          (k1 (by rw [NativeRustc.length_wordBytes]; decide)
            (by rw [NativeRustc.length_wordBytes]; exact gk0) h.word))
    · exact k4 (by rw [length_pkB]; decide) (by rw [length_pkB]; exact fk1)
        (kAll (by rw [length_pkB]; decide) hpk1)
    · have hl2 : ((bottomL w).memBytes ++ (topL w).memBytes).length = 2400 := by
        rw [List.length_append, bottomL_memBytes, topL,
          length_memBytes (by rw [length_sigB])]
      exact k4 (by rw [hl2]; decide) (by rw [hl2]; exact fk2)
        (kAll (by rw [hl2]; decide) (k1 (by rw [hl2]; decide) (by rw [hl2]; exact gk2) h.layers))
  simp only [PcOk, hc] at hpc4
  by_cases h16 : z + 1 = 16
  · simp only [h16, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false] at hpc4
    exact Or.inr ⟨h16, hpc4.trans rfl, h16 ▸ B⟩
  · simp only [h16, ne_eq, not_false_eq_true, decide_true, ite_true] at hpc4
    exact Or.inl ⟨by omega, hpc4.trans (hp.label NativeRustcArm.Xmss.XmssVerify.label_4_at), B⟩

end

end NativeRustcArm.Xmss.XmssVerify
