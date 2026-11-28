module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names
public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify.BotTurn
public import NativeRustcArm.XmssVerify.Leaf
meta import NativeRustcArm.Code.Xmss.XmssVerify
public meta import NativeRustcArm.XmssVerify.Parse

/-!
# `xmss_verify`: the bottom layer

Block 5: `wots_leaf` of the message on layer `0` with the leaf index; block 6: its tag, to the
rejection if `0`; block 7: the leaf to `4954`, the leaf index's word to `0`, the path loop's
registers. The path loop (`botLoop`: 16 turns of `botTurn`). `bottom`: from `Parsed` at block 5
to the rejection if the bottom layer has no root, else to block 15 with its root at `4954`.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

/-- The registers block 5 knows. -/
def known5 : List (XReg × Sym) :=
  [(.X19, .ptr 0 2492), (.X20, .ptr 0 2448), (.X21, .ptr 0 5392)]

sym_block b5_exec := exec b5 (stF0 known5)

/-- The symbolic state after block 5. -/
def st5 : SState := ((exec b5 (stF0 known5)).getD (stF0 [], .fall)).1

theorem b5_exec' : exec b5 (stF0 known5) = some (st5, .call NativeRustcArm.Xmss.WotsLeaf.entryLabel) := by
  rw [b5_exec]
  rfl

theorem st5_facts : st5.reg .X0 = some (.ptr 0 5408) ∧ st5.reg .X1 = some (.ptr 0 2464) ∧
    st5.reg .X2 = some (.lit 0) ∧ st5.reg .X3 = some (.un .trunc .W32 (.reg .X24)) ∧
    st5.reg .X4 = some (.ptr 0 8) ∧ st5.reg .X5 = some (.lit 32) ∧
    st5.reg .X6 = some (.ptr 0 3676) ∧ st5.reg .X7 = some (.ptr 0 2748) ∧ st5.sp = .ptr 0 0 ∧
    st5.reg .X29 = some (.reg .X29) ∧ writesIn st5 [0] = true ∧
    (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st5.mem = none) ∧
    (∀ r ∈ [XReg.X22, .X23, .X24], st5.reg r = some (.reg r)) ∧
    st5.reg .X21 = some (.ptr 0 5392) ∧ firstOverlap 0 8 32 st5.mem = none ∧
    firstOverlap 0 2448 32 st5.mem = none ∧ firstOverlap 0 2492 2400 st5.mem = none := by
  decide +kernel

sym_block b6_exec := exec b6 (stF0 [(.X21, .ptr 0 5392)])

/-- The symbolic state after block 6. -/
def st6 : SState := ((exec b6 (stF0 [(.X21, .ptr 0 5392)])).getD (stF0 [], .fall)).1

theorem b6_exec' : exec b6 (stF0 [(.X21, .ptr 0 5392)]) =
    some (st6, .cond (.cmp .eq .W32 (.load 0 5408 1) (.lit 0)) NativeRustcArm.Xmss.XmssVerify.label_9) := by
  rw [b6_exec]
  rfl

theorem st6_facts : st6.mem = [] ∧ st6.sp = .ptr 0 0 ∧ st6.reg .X29 = some (.reg .X29) ∧
    st6.reg .X21 = some (.ptr 0 5392) ∧
    (∀ r ∈ [XReg.X22, .X23, .X24], st6.reg r = some (.reg r)) := by
  decide +kernel

sym_block b7_exec := exec b7 (stF0 [(.X21, .ptr 0 5392)])

/-- The symbolic state after block 7. -/
def st7 : SState := ((exec b7 (stF0 [(.X21, .ptr 0 5392)])).getD (stF0 [], .fall)).1

theorem b7_exec' : exec b7 (stF0 [(.X21, .ptr 0 5392)]) = some (st7, .fall) := by
  rw [b7_exec]
  rfl

/-- The registers block 7 sets for the bottom path loop. -/
def known7 : List (XReg × Sym) :=
  [(.X19, .ptr 0 4976), (.X20, .lit 3), (.X21, .ptr 0 5392), (.X24, .lit 0), (.X25, .ptr 0 4896),
    (.X26, .ptr 0 5016), (.X27, .ptr 0 2492), (.X28, .lit 1)]

theorem st7_facts : st7.sp = .ptr 0 0 ∧ st7.reg .X29 = some (.reg .X29) ∧
    writesIn st7 [0] = true ∧ (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st7.mem = none) ∧
    (∀ p ∈ known7, st7.reg p.1 = some p.2) ∧
    (∀ r ∈ [XReg.X22, .X23], st7.reg r = some (.reg r)) ∧
    (∀ t < 8, findWrite 0 (0 + t) st7.mem = some (.reg .X24, t)) ∧
    (∀ i < 16, copiedFrom (4954 + i) st7.mem = some (5467 + i)) ∧
    firstOverlap 0 2448 32 st7.mem = none ∧ firstOverlap 0 2492 2400 st7.mem = none := by
  decide +kernel

end

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **The bottom path loop**: from its head with the leaf, after 16 turns at block 15 with the
root. -/
theorem botLoop {k : Nat} (hp : Placed code k) (Cs : Callees) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b8Offset)) {lf : List UInt8} (hl : lf.length = 16)
    (h : BotAt w m₀ st.data 0 lf) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b15Offset) ∧
      BotAt w m₀ st'.data 16 (fold (pp w) 0 (li w).toNat (bottomL w).path lf 16)) st :=
  Sym.loop (I := fun n s => ∃ z, z + n = 16 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b8Offset) ∧
      BotAt w m₀ s.data z (fold (pp w) 0 (li w).toNat (bottomL w).path lf z))
    (fun n s ⟨z, hn, hn0, hpc, h⟩ => NativeRustcArm.Eventually.mono
      (botTurn hp Cs P (by omega) hpc (length_fold hl z) h) fun s' h' => by
        rcases h' with ⟨hlt, hpc', h'⟩ | ⟨heq, hpc', h'⟩
        · exact Or.inr ⟨n - 1, by omega, z + 1, by omega, by omega, hpc', by
            rw [fold_succ]; exact h'⟩
        · refine Or.inl ⟨hpc', ?_⟩
          obtain rfl : z = 15 := by omega
          rw [show fold (pp w) 0 (li w).toNat (bottomL w).path lf 16 =
            botStep w (fold (pp w) 0 (li w).toNat (bottomL w).path lf 15) 15 from fold_succ 15]
          exact h')
    (n := 16) ⟨0, rfl, by decide, hpc, h⟩

/-- **The bottom layer**: from block 5, the rejection if the bottom layer has no root, else
block 15 with the root. -/
theorem bottom {k : Nat} (hp : Placed code k) (Cs : Callees) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b5Offset)) (h : Parsed w m₀ st.data) {R : MachineState → Prop}
    (hnone : layerRoot (pp w) 0 (li w) (msgB w) (bottomL w) = none →
      ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b26Offset) → Common m₀ st'.data →
        Eventually (step1 Host.exe) R st')
    (hsome : ∀ x r0, layerRoot (pp w) 0 (li w) (msgB w) (bottomL w) = some (x, r0) →
      ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b15Offset) → BotAt w m₀ st'.data 16 r0 →
        Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  -- Block 5.
  have hwf := frame_wf P C
  have hm := match_stF0 P C (known := known5) ⟨h.x19.trans (eval_ptr0 _).symm,
    h.x20.trans (eval_ptr0 _).symm, h.x21.trans (eval_ptr0 _).symm, trivial⟩
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, gsp, g29, gw, gsave, gr, g21, gk0, gk1, gk2⟩ := st5_facts
  refine call_step (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) b5_exec' hwf hpc hm
    fun st1 hpc1 hm1 => ?_
  change Match _ st5 st1.data at hm1
  have C1 := Common.block P C hwf hm hm1 (by rw [gsp]; rfl) rfl g29 gw gsave
  have hreg1 : ∀ {r : XReg} {v : Sym}, st5.reg r = some v →
      (st1.data.regs.getXReg r).toBitVec = v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)]) :=
    fun hr => hm1.regs _ _ hr
  have k1 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5872 →
      firstOverlap 0 o bs.length st5.mem = none →
      BytesAt st.data.dmem (ad m₀ (fb + o)) bs → BytesAt st1.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hc hb => frameKeep hm1 ho hc hb
  have hl2 : ((bottomL w).memBytes ++ (topL w).memBytes).length = 2400 := by
    rw [List.length_append, bottomL_memBytes, topL, length_memBytes (by rw [length_sigB])]
  have hlay : BytesAt st.data.dmem (ad m₀ (fb + 2492)) ((bottomL w).memBytes ++ (topL w).memBytes) :=
    BytesAt.append_ad h.bottom (by rw [bottomL_memBytes]; exact h.top)
  have hpk1 := k1 (by rw [length_pkB]; decide) (by rw [length_pkB]; exact gk1) h.pk
  have hmsg1 := k1 (by rw [length_msgB]; decide) (by rw [length_msgB]; exact gk0) h.msg
  have hlay1 := k1 (by rw [hl2]; decide) (by rw [hl2]; exact gk2) hlay
  have h3 : st1.data.regs.X3.toUInt32 = li w := by
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, li_toNat]
    have := hreg1 g3
    simp only [Sym.eval, UnOp.apply, low_W32, ext_W32, Env.ofMachine_regs] at this
    rw [show st1.data.regs.X3.toNat = (st1.data.regs.getXReg .X3).toBitVec.toNat from rfl, this,
      BitVec.toNat_setWidth, BitVec.toNat_setWidth, h.x24]
    have : (w 8).toNat = (w 8).toBitVec.toNat := rfl
    omega
  have hrand : BytesAt st1.data.dmem (ad m₀ (fb + 3676)) (bottomL w).randomizer := by
    have := layer_rand (w := w) (c := 4) (by decide) hlay1.left
    rwa [ad_add] at this
  have hvals := layer_values (w := w) (c := 4) (by decide) hlay1.left
  rw [ad_add, show fb + 2492 + 256 = fb + 2748 by rw [Nat.add_assoc]] at hvals
  change _ = (bottomL w).chainValues at hvals
  -- `wots_leaf` of the message.
  refine wotsCall Cs P hpc1.1 hpc1.2 C1 (o4 := 8) (o6 := 3676) (o7 := 2748)
    ((hreg1 g0).trans (eval_ptr0 _)) ((hreg1 g1).trans (eval_ptr0 _))
    (toNat_lit (hreg1 g2) (by decide)) h3 ((hreg1 g4).trans (eval_ptr0 _))
    (toNat_lit (hreg1 g5) (by decide)) ((hreg1 g6).trans (eval_ptr0 _))
    ((hreg1 g7).trans (eval_ptr0 _)) (by decide) (by decide) (by decide) (by decide)
    (pp_at hpk1) (length_pp w) hmsg1 (length_msgB w) hrand (length_rand (by decide)) hvals
    fun st2 hpc2 C2 hs2 hout hsm2 => ?_
  have k2 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5408 →
      BytesAt st1.data.dmem (ad m₀ (fb + o)) bs → BytesAt st2.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hb => keep_callR P C1 le_rfl (by decide) hsm2 hb (by omega) (Or.inl ho)
  have hreg2 : ∀ {r : XReg}, r ∈ [XReg.X21, .X22, .X23, .X24] →
      st2.data.regs.getXReg r = st1.data.regs.getXReg r := fun hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hs2.1 _ rfl
  have hkept : ∀ {r : XReg}, r ∈ [XReg.X22, .X23, .X24] →
      st1.data.regs.getXReg r = st.data.regs.getXReg r := fun hr =>
    UInt64.toBitVec_inj.mp (hreg1 (gr _ hr))
  -- Block 6: the tag.
  have x21_2 : (st2.data.regs.getXReg .X21).toBitVec = ad m₀ (fb + 5392) := by
    rw [hreg2 (by simp)]
    exact (hreg1 g21).trans (eval_ptr0 _)
  have hmap : Mapped st2.data.dmem (ad m₀ (fb + 5408)) 75 := C2.mapped P (by fbo)
  obtain ⟨m6, sp6, z6, s21, sr⟩ := st6_facts
  cases hW : wotsLeaf (pp w) 0 (li w) (msgB w) (bottomL w).randomizer (bottomL w).chainValues with
  | none =>
    rw [hW] at hout
    obtain ⟨rest, hb⟩ := out_none hmap hout
    refine tagBlock P (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) b6_exec' m6 sp6 z6 rfl
      (hpc2.trans rfl) C2 ⟨x21_2.trans (eval_ptr0 _).symm, trivial⟩ hb
      fun st3 hpc3 C3 _ _ => ?_
    simp only [ite_true] at hpc3
    exact hnone (by rw [layerRoot_eq, hW]; rfl) st3
      (hpc3.trans (hp.label NativeRustcArm.Xmss.XmssVerify.label_9_at)) C3
  | some xl =>
    obtain ⟨x, lf⟩ := xl
    rw [hW] at hout
    obtain ⟨hxl, hll⟩ := wotsLeaf_some hW
    obtain ⟨tag, htag, hb⟩ := out_some hmap hout
    refine tagBlock P (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) b6_exec' m6 sp6 z6 rfl
      (hpc2.trans rfl) C2 ⟨x21_2.trans (eval_ptr0 _).symm, trivial⟩ hb
      fun st3 hpc3 C3 hd3 hr3 => ?_
    simp only [htag, ite_false] at hpc3
    have hreg3 : ∀ {r : XReg}, r ∈ [XReg.X22, .X23, .X24] →
        st3.data.regs.getXReg r = st2.data.regs.getXReg r := fun hr =>
      UInt64.toBitVec_inj.mp (hr3 _ _ (sr _ hr))
    have hleaf : BytesAt st3.data.dmem (ad m₀ (fb + 5467)) lf := by
      have h1 : BytesAt st2.data.dmem (ad m₀ (fb + 5409)) (x ++ lf) := by
        have := hb.drop (n := 1) (by simp)
        rwa [ad_add] at this
      have h2 := h1.drop (n := 58) (by simp [hxl])
      rw [List.drop_left' hxl, ad_add] at h2
      rw [hd3]
      exact h2
    -- Block 7.
    have hwf3 := frame_wf P C3
    have hm3 := match_stF0 P C3 (known := [(.X21, .ptr 0 5392)])
      ⟨(hr3 _ _ s21).trans ((eval_ptr0 _).trans (eval_ptr0 _).symm),
        trivial⟩
    obtain ⟨f_sp, f29, fw, fsave, fk, fr, fword, fleaf, fk1, fk2⟩ := st7_facts
    refine fall_step (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) b7_exec' hwf3
      (hpc3.trans rfl) hm3 fun st4 hpc4 hm4 => ?_
    change Match _ st7 st4.data at hm4
    have C4 := Common.block P C3 hwf3 hm3 hm4 (by rw [f_sp]; rfl) rfl f29 fw fsave
    have hk7 : ∀ {p : XReg × Sym}, p ∈ known7 →
        (st4.data.regs.getXReg p.1).toBitVec = p.2.eval (Env.ofMachine st3.data [(ad m₀ fb, 5872)]) :=
      fun hp' => hm4.regs _ _ (fk _ hp')
    have hold : ∀ {r : XReg}, r ∈ [XReg.X22, .X23] →
        st4.data.regs.getXReg r = st.data.regs.getXReg r := fun {r} hr => by
      have h4 : st4.data.regs.getXReg r = st3.data.regs.getXReg r :=
        UInt64.toBitVec_inj.mp (hm4.regs _ _ (fr _ hr))
      rw [h4]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [hreg3 (by simp), hreg2 (by simp), hkept (by simp)]
    have B : BotAt w m₀ st4.data 0 lf := by
      refine ⟨C4, (hk7 (p := (.X19, .ptr 0 4976)) (by simp [known7])).trans (eval_ptr0 _),
        hk7 (p := (.X20, .lit 3)) (by simp [known7]),
        (hk7 (p := (.X21, .ptr 0 5392)) (by simp [known7])).trans (eval_ptr0 _), ?_, ?_,
        hk7 (p := (.X24, .lit 0)) (by simp [known7]),
        (hk7 (p := (.X25, .ptr 0 4896)) (by simp [known7])).trans (eval_ptr0 _),
        (hk7 (p := (.X26, .ptr 0 5016)) (by simp [known7])).trans (eval_ptr0 _),
        (hk7 (p := (.X27, .ptr 0 2492)) (by simp [known7])).trans (eval_ptr0 _),
        hk7 (p := (.X28, .lit 1)) (by simp [known7]), ?_, ?_, ?_, ?_⟩
      · rw [hold (by simp)]
        exact h.x22
      · rw [hold (by simp)]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, li_toNat, Nat.mod_eq_of_lt (by omega)]
        exact h.x23
      · exact bytesAt_copied hm4 (o := 4954) (s := 5467) (by rw [hll]; decide)
          (fun i hi => fleaf i (by rw [hll] at hi; exact hi)) hleaf
      · have := frameWrite hm4 (o := 0) (by omega) fword
        rw [show (Sym.reg .X24).eval (Env.ofMachine st3.data [(ad m₀ fb, 5872)]) =
            (st3.data.regs.getXReg .X24).toBitVec from rfl,
          hreg3 (by simp), hreg2 (by simp), hkept (by simp), h.x24, regBytes_eq_wordBytes] at this
        exact this
      · exact frameKeep hm4 (by rw [length_pkB]; decide) (by rw [length_pkB]; exact fk1)
          (hd3 ▸ k2 (by rw [length_pkB]; decide) hpk1)
      · exact frameKeep hm4 (by rw [hl2]; decide) (by rw [hl2]; exact fk2)
          (hd3 ▸ k2 (by rw [hl2]; decide) hlay1)
    refine NativeRustcArm.Eventually.bind (botLoop hp Cs P (hpc4.trans rfl) hll B)
      fun s ⟨hpcs, hs⟩ => hsome x _ ?_ s hpcs hs
    rw [layerRoot_eq, hW]
    simp only [Option.map_some]
    rw [show (bottomL w).path.length = 16 from length_path w 4]

end

end NativeRustcArm.Xmss.XmssVerify
