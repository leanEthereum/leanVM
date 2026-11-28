module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names
public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify.TopTurn
public import NativeRustcArm.XmssVerify.BotLeaf
meta import NativeRustcArm.Code.Xmss.XmssVerify
public meta import NativeRustcArm.XmssVerify.Parse

/-!
# `xmss_verify`: the top layer

Block 15: `wots_leaf` of the bottom root on layer `1` with the leaf index shifted by 16; block 16:
its tag, to the rejection if `0`; block 17: the leaf into `x9`, `x8`, the path loop's registers.
The path loop (`topLoop`: 16 turns of `topTurn`). `top`: from block 15 with the bottom root to the
rejection if the top layer has no root, else to block 25 with its root.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

sym_block b15_exec := exec b15 (stF0 [(.X25, .ptr 0 4896)])

/-- The symbolic state after block 15. -/
def st15 : SState := ((exec b15 (stF0 [(.X25, .ptr 0 4896)])).getD (stF0 [], .fall)).1

theorem b15_exec' : exec b15 (stF0 [(.X25, .ptr 0 4896)]) = some (st15, .call NativeRustcArm.Xmss.WotsLeaf.entryLabel) := by
  rw [b15_exec]
  rfl

/-- The top layer's key index: bits 16 to 31 of the leaf index's word at `0`. -/
def li1Sym : Sym := .un (.ubfm 16 31) .W32 (.load 0 0 8)

theorem st15_facts : st15.reg .X0 = some (.ptr 0 5408) ∧ st15.reg .X1 = some (.ptr 0 2464) ∧
    st15.reg .X2 = some (.lit 1) ∧ st15.reg .X3 = some li1Sym ∧
    st15.reg .X4 = some (.ptr 0 4954) ∧ st15.reg .X5 = some (.lit 16) ∧
    st15.reg .X6 = some (.ptr 0 4876) ∧ st15.reg .X7 = some (.ptr 0 3948) ∧
    st15.reg .X19 = some li1Sym ∧ st15.sp = .ptr 0 0 ∧ st15.reg .X29 = some (.reg .X29) ∧
    st15.mem = [] ∧ (∀ r ∈ [XReg.X21, .X22], st15.reg r = some (.reg r)) := by
  decide +kernel

sym_block b16_exec := exec b16 (stF0 [(.X21, .ptr 0 5392)])

/-- The symbolic state after block 16. -/
def st16 : SState := ((exec b16 (stF0 [(.X21, .ptr 0 5392)])).getD (stF0 [], .fall)).1

theorem b16_exec' : exec b16 (stF0 [(.X21, .ptr 0 5392)]) =
    some (st16, .cond (.cmp .eq .W32 (.load 0 5408 1) (.lit 0)) NativeRustcArm.Xmss.XmssVerify.label_9) := by
  rw [b16_exec]
  rfl

theorem st16_facts : st16.mem = [] ∧ st16.sp = .ptr 0 0 ∧ st16.reg .X29 = some (.reg .X29) ∧
    st16.reg .X21 = some (.ptr 0 5392) ∧ st16.reg .X27 = some (.ptr 0 2448) ∧
    (∀ r ∈ [XReg.X19, .X22], st16.reg r = some (.reg r)) := by
  decide +kernel

sym_block b17_exec := exec b17 (stF0 [(.X21, .ptr 0 5392)])

/-- The symbolic state after block 17. -/
def st17 : SState := ((exec b17 (stF0 [(.X21, .ptr 0 5392)])).getD (stF0 [], .fall)).1

theorem b17_exec' : exec b17 (stF0 [(.X21, .ptr 0 5392)]) = some (st17, .fall) := by
  rw [b17_exec]
  rfl

/-- The registers block 17 sets for the top path loop. -/
def known17 : List (XReg × Sym) :=
  [(.X20, .lit 1), (.X21, .ptr 0 5392), (.X23, .ptr 0 5016), (.X24, .lit 1), (.X25, .ptr 0 4976),
    (.X26, .lit 3)]

theorem st17_facts : st17.sp = .ptr 0 0 ∧ st17.reg .X29 = some (.reg .X29) ∧ st17.mem = [] ∧
    (∀ p ∈ known17, st17.reg p.1 = some p.2) ∧
    (∀ r ∈ [XReg.X19, .X22, .X27], st17.reg r = some (.reg r)) ∧
    st17.reg .X9 = some (.load 0 5467 8) ∧ st17.reg .X8 = some (.load 0 5475 8) := by
  decide +kernel

end

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **The top path loop**: from its head with the leaf, after 16 turns at block 25 with the
root. -/
theorem topLoop {k : Nat} (hp : Placed code k) (Cs : Callees) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b18Offset)) {lf : List UInt8} (hl : lf.length = 16)
    (h : TopAt w m₀ st.data 0 lf) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b25Offset) ∧
      TopAt w m₀ st'.data 16 (fold (pp w) 1 (li1 w).toNat (topL w).path lf 16)) st :=
  Sym.loop (I := fun n s => ∃ z, z + n = 16 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b18Offset) ∧
      TopAt w m₀ s.data z (fold (pp w) 1 (li1 w).toNat (topL w).path lf z))
    (fun n s ⟨z, hn, hn0, hpc, h⟩ => NativeRustcArm.Eventually.mono
      (topTurn hp Cs P (by omega) hpc (length_fold hl z) h) fun s' h' => by
        rcases h' with ⟨hlt, hpc', h'⟩ | ⟨heq, hpc', h'⟩
        · exact Or.inr ⟨n - 1, by omega, z + 1, by omega, by omega, hpc', by
            rw [fold_succ]; exact h'⟩
        · refine Or.inl ⟨hpc', ?_⟩
          obtain rfl : z = 15 := by omega
          rw [show fold (pp w) 1 (li1 w).toNat (topL w).path lf 16 =
            topStep w (fold (pp w) 1 (li1 w).toNat (topL w).path lf 15) 15 from fold_succ 15]
          exact h')
    (n := 16) ⟨0, rfl, by decide, hpc, h⟩

omit [Host] in
theorem regBytes_inj {a b : BitVec 64} (h : regBytes a = regBytes b) : a = b := by
  rw [← ofBytes_regBytes a, h, ofBytes_regBytes]

/-- **The top layer**: from block 15 with the bottom root, the rejection if the top layer has no
root, else block 25 with the root. -/
theorem top {k : Nat} (hp : Placed code k) (Cs : Callees) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b15Offset)) {r0 : List UInt8} (hl0 : r0.length = 16)
    (h : BotAt w m₀ st.data 16 r0) {R : MachineState → Prop}
    (hnone : layerRoot (pp w) 1 (li1 w) r0 (topL w) = none →
      ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b26Offset) → Common m₀ st'.data →
        Eventually (step1 Host.exe) R st')
    (hsome : ∀ x r, layerRoot (pp w) 1 (li1 w) r0 (topL w) = some (x, r) →
      ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b25Offset) → TopAt w m₀ st'.data 16 r →
        Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  -- Block 15.
  have hwf := frame_wf P C
  have hm := match_stF0 P C (known := [(.X25, .ptr 0 4896)]) ⟨h.x25.trans (eval_ptr0 _).symm, trivial⟩
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g19, gsp, g29, gmem, gr⟩ := st15_facts
  refine call_step (b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) b15_exec' hwf hpc hm
    fun st1 hpc1 hm1 => ?_
  change Match _ st15 st1.data at hm1
  have C1 := Common.block P C hwf hm hm1 (by rw [gsp]; rfl) rfl g29 (by simp [writesIn, gmem])
    (fun x _ _ => by rw [gmem]; rfl)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf gmem
  have hreg1 : ∀ {r : XReg} {v : Sym}, st15.reg r = some v →
      (st1.data.regs.getXReg r).toBitVec = v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)]) :=
    fun hr => hm1.regs _ _ hr
  have hword : (Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 0 8 = (w 8).toBitVec := by
    apply regBytes_inj
    rw [regBytes_frame (o := 0) (by rw [NativeRustc.length_wordBytes]) h.word,
      regBytes_eq_wordBytes]
  have hli1 : (li1Sym.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)])).toNat = (li1 w).toNat := by
    rw [li1_toNat]
    show (UnOp.apply (.ubfm 16 31) .W32 ((Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 0 8)).toNat = _
    rw [ubfm16_toNat, hword]
    rfl
  have h3 : st1.data.regs.X3.toUInt32 = li1 w := by
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32,
      show st1.data.regs.X3.toNat = (st1.data.regs.getXReg .X3).toBitVec.toNat from rfl,
      hreg1 g3, hli1]
    have := (li1 w).toNat_lt
    omega
  have hrand : BytesAt st1.data.dmem (ad m₀ (fb + 4876)) (topL w).randomizer := by
    have := layer_rand (w := w) (c := 1204) (by decide) h.layers.right
    rw [bottomL_memBytes, ad_add, ad_add] at this
    rw [hd1]
    exact this
  have hvals := layer_values (w := w) (c := 1204) (by decide) h.layers.right
  rw [bottomL_memBytes, ad_add, ad_add,
    show fb + 2492 + 1200 + 256 = fb + 3948 by rw [Nat.add_assoc, Nat.add_assoc]] at hvals
  change _ = (topL w).chainValues at hvals
  rw [← hd1] at hvals
  -- `wots_leaf` of the bottom root.
  refine wotsCall Cs P hpc1.1 hpc1.2 C1 (o4 := 4954) (o6 := 4876) (o7 := 3948)
    ((hreg1 g0).trans (eval_ptr0 _)) ((hreg1 g1).trans (eval_ptr0 _))
    (toNat_lit (hreg1 g2) (by decide)) h3 ((hreg1 g4).trans (eval_ptr0 _))
    (toNat_lit (hreg1 g5) (by decide)) ((hreg1 g6).trans (eval_ptr0 _))
    ((hreg1 g7).trans (eval_ptr0 _)) (by decide) (by decide) (by decide) (by decide)
    (hd1 ▸ pp_at h.pk) (length_pp w) (hd1 ▸ h.cur) hl0 hrand
    (length_rand (by decide)) hvals fun st2 hpc2 C2 hs2 hout hsm2 => ?_
  have k2 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5408 →
      BytesAt st1.data.dmem (ad m₀ (fb + o)) bs → BytesAt st2.data.dmem (ad m₀ (fb + o)) bs :=
    fun ho hb => keep_callR P C1 le_rfl (by decide) hsm2 hb (by omega) (Or.inl ho)
  have hreg2 : ∀ {r : XReg}, r ∈ [XReg.X19, .X21, .X22] →
      st2.data.regs.getXReg r = st1.data.regs.getXReg r := fun hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hs2.1 _ rfl
  -- Block 16: the tag.
  have x21_2 : (st2.data.regs.getXReg .X21).toBitVec = ad m₀ (fb + 5392) := by
    rw [hreg2 (by simp), hreg1 (gr .X21 (by simp))]
    exact h.x21
  have hmap : Mapped st2.data.dmem (ad m₀ (fb + 5408)) 75 := C2.mapped P (by fbo)
  obtain ⟨m6, sp6, z6, s21, s27, sr⟩ := st16_facts
  cases hW : wotsLeaf (pp w) 1 (li1 w) r0 (topL w).randomizer (topL w).chainValues with
  | none =>
    rw [hW] at hout
    obtain ⟨rest, hb⟩ := out_none hmap hout
    refine tagBlock P (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) b16_exec' m6 sp6 z6 rfl
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
    refine tagBlock P (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) b16_exec' m6 sp6 z6 rfl
      (hpc2.trans rfl) C2 ⟨x21_2.trans (eval_ptr0 _).symm, trivial⟩ hb
      fun st3 hpc3 C3 hd3 hr3 => ?_
    simp only [htag, ite_false] at hpc3
    have hleaf : BytesAt st3.data.dmem (ad m₀ (fb + 5467)) lf := by
      have h1 : BytesAt st2.data.dmem (ad m₀ (fb + 5409)) (x ++ lf) := by
        have := hb.drop (n := 1) (by simp)
        rwa [ad_add] at this
      have h2 := h1.drop (n := 58) (by simp [hxl])
      rw [List.drop_left' hxl, ad_add] at h2
      rw [hd3]
      exact h2
    -- Block 17.
    have hwf3 := frame_wf P C3
    have hm3 := match_stF0 P C3 (known := [(.X21, .ptr 0 5392)])
      ⟨(hr3 _ _ s21).trans ((eval_ptr0 _).trans (eval_ptr0 _).symm), trivial⟩
    obtain ⟨f_sp, f29, fmem, fk, fr, f9, f8⟩ := st17_facts
    refine fall_step (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) b17_exec' hwf3
      (hpc3.trans rfl) hm3 fun st4 hpc4 hm4 => ?_
    change Match _ st17 st4.data at hm4
    have C4 := Common.block P C3 hwf3 hm3 hm4 (by rw [f_sp]; rfl) rfl f29
      (by simp [writesIn, fmem]) (fun x _ _ => by rw [fmem]; rfl)
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 fmem
    have hk17 : ∀ {p : XReg × Sym}, p ∈ known17 →
        (st4.data.regs.getXReg p.1).toBitVec = p.2.eval (Env.ofMachine st3.data [(ad m₀ fb, 5872)]) :=
      fun hp' => hm4.regs _ _ (fk _ hp')
    have hold : ∀ {r : XReg}, r ∈ [XReg.X19, .X22, .X27] →
        st4.data.regs.getXReg r = st3.data.regs.getXReg r := fun hr =>
      UInt64.toBitVec_inj.mp (hm4.regs _ _ (fr _ hr))
    have hl3 : ∀ {r : XReg}, r ∈ [XReg.X19, .X22] →
        st3.data.regs.getXReg r = st2.data.regs.getXReg r := fun hr =>
      UInt64.toBitVec_inj.mp (hr3 _ _ (sr _ hr))
    have B : TopAt w m₀ st4.data 0 lf := by
      refine ⟨C4, ?_, hk17 (p := (.X20, .lit 1)) (by simp [known17]),
        (hk17 (p := (.X21, .ptr 0 5392)) (by simp [known17])).trans (eval_ptr0 _), ?_,
        (hk17 (p := (.X23, .ptr 0 5016)) (by simp [known17])).trans (eval_ptr0 _),
        hk17 (p := (.X24, .lit 1)) (by simp [known17]),
        (hk17 (p := (.X25, .ptr 0 4976)) (by simp [known17])).trans (eval_ptr0 _),
        hk17 (p := (.X26, .lit 3)) (by simp [known17]), ?_, ?_, ?_, ?_⟩
      · rw [hold (by simp), hl3 (by simp), hreg2 (by simp)]
        apply BitVec.eq_of_toNat_eq
        rw [hreg1 g19, hli1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (li1_lt w)]
      · rw [hold (by simp), hl3 (by simp), hreg2 (by simp), hreg1 (gr .X22 (by simp))]
        exact h.x22
      · rw [hold (by simp)]
        exact (hr3 _ _ s27).trans (eval_ptr0 _)
      · rw [hm4.regs _ _ f9, hm4.regs _ _ f8]
        show regBytes ((Env.ofMachine st3.data [(ad m₀ fb, 5872)]).load 0 5467 8) ++
          regBytes ((Env.ofMachine st3.data [(ad m₀ fb, 5872)]).load 0 5475 8) = lf
        rw [regBytes_frame (bs := lf.take 8) (by rw [List.length_take, hll]; rfl) (hleaf.take 8),
          regBytes_frame (bs := lf.drop 8) (by rw [List.length_drop, hll])
            (by have := hleaf.drop (n := 8) (by omega); rwa [ad_add] at this),
          List.take_append_drop]
      · rw [hd4, hd3]
        exact k2 (by rw [length_pkB]; decide) (hd1 ▸ h.pk)
      · rw [hd4, hd3]
        have := h.layers.right
        rw [bottomL_memBytes, ad_add] at this
        exact k2 (by rw [topL_memBytes]; decide) (hd1 ▸ this)
    refine NativeRustcArm.Eventually.bind (topLoop hp Cs P (hpc4.trans rfl) hll B)
      fun s ⟨hpcs, hs⟩ => hsome x _ ?_ s hpcs hs
    rw [layerRoot_eq, hW]
    simp only [Option.map_some]
    rw [show (topL w).path.length = 16 from length_path w 1204]

end

end NativeRustcArm.Xmss.XmssVerify
