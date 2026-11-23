module

public import NativeRustcX64.Code.Xmss.WotsLeaf.Names

public import NativeRustcX64.XmssVerify.Top

/-!
# `xmss_verify`: from the bottom root to the loop over the top layer's path (x86-64)

`top`: blocks 16 to 18 with the call of `wots_leaf` between them
(`NativeRustcX64.XmssVerify.Top`): from `TreeAt0` at level `16` (the bottom root at `592`) to the
failure (`FailAt` at block 27) if the top layer's one-time leaf is `None`, else to `TreeAt1` at
level `0` from its leaf.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

public section

/-- Bits 16 to 31 of a word loaded from `80`. -/
theorem hi16_eval [Labels] {env : Env} {x : UInt64} (h : env.load 0 80 8 = x.toBitVec) :
    (Sym.bin .shr .W32 (.load 0 80 8) (.lit 16)).eval env =
      BitVec.ofNat 64 (x.toNat % 2 ^ 32 / 2 ^ 16) := by
  apply BitVec.eq_of_toNat_eq
  show (BinOp.apply .shr .W32 (env.load 0 80 8) (BitVec.ofNat 64 16)).toNat = _
  rw [shr16_toNat, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toNat % 2 ^ 32 / 2 ^ 16 < 2 ^ 64
    by omega)]
  rfl

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

set_option linter.unusedSimpArgs false in
/-- **The top layer's one-time leaf**: from block 16 to the failure, or to the loop over the top
layer's path from the leaf. -/
public theorem top {k : Nat} (hp : Placed code k)
    (hwots : Spec (label NativeRustcX64.Xmss.WotsLeaf.entryLabel) WotsLeafPre WotsLeafPost) (P : Pre w m₀)
    {x leaf : List UInt8} (hl0 : leaf0 w = some (x, leaf)) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b16Offset)) (h : TreeAt0 w m₀ leaf st.data 16)
    {R : MachineState → Prop}
    (hfail : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b27Offset) → FailAt w m₀ st'.data →
      Eventually (step1 Host.exe) R st')
    (hok : ∀ (st' : MachineState) (x' leaf' : List UInt8),
      leaf1 w (root0 w leaf) = some (x', leaf') → st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b19Offset) →
      TreeAt1 w m₀ leaf' st'.data 0 → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hleaf : leaf.length = 16 := (wotsLeaf_length hl0).2
  -- Block 16.
  let env := Env.ofMachine st.data (frameRs m₀) (fun _ => 0)
    (Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b16Offset + b16.length)).toBitVec
  have hwf : env.WF := frameG_wf P C.kept
  have hm0 : Match env (stF []) st.data :=
    match_stG P C.same h.rsp trivial
  obtain ⟨h0, h1, h2, h3, hbx, h8, h9, hsp, h12, hw, h6w, h7w⟩ := st16_facts
  refine call_step (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b16 hwf rfl hpc hm0
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ (after b16 (stF [])) st₁.data at hm₁
  have C₁ := Common.block P C hwf hm₁ hw
  have hx : ∀ {r : Reg64} {o : Nat}, (after b16 (stF [])).reg r = some (.ptr 0 o) →
      reg st₁.data r = ad m₀ (fr + o) := fun hr => (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₁ : rspOf st₁.data = ad m₀ (fr + 0) := hx hsp
  have hk₁ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 5816 → BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hle => frame_keep P hwf hm₁ hw hb h24 hle
  have hlen1 : (topL w).memBytes.length = 1200 := length_memBytes (by simp [length_sigB])
  have hroot : (root0 w leaf).length = 16 := length_pf _ _ _ _ hleaf 16
  have hpk₁ := hk₁ h.pk (by omega) (by simp [length_pkB])
  have hcur₁ : BytesAt st₁.data.dmem (ad m₀ (fr + 592)) (root0 w leaf) :=
    hk₁ h.cur (by omega) (by rw [hroot]; omega)
  have htop₁ := hk₁ h.top (by omega) (by simp [hlen1])
  have h6 : BytesAt st₁.data.dmem (ad m₀ (fr + 8)) (regBytes (ad m₀ (fr + 5740))) := by
    have := hm₁.bytesAt_write (r := 0) rfl (by omega) h6w
    have e : (Sym.ptr 0 5740).eval env = ad m₀ (fr + 5740) := eval_ptr0 5740
    rwa [e, ad_add] at this
  have h7 : BytesAt st₁.data.dmem (ad m₀ (fr + 16)) (regBytes (ad m₀ (fr + 4812))) := by
    have := hm₁.bytesAt_write (r := 0) rfl (by omega) h7w
    have e : (Sym.ptr 0 4812).eval env = ad m₀ (fr + 4812) := eval_ptr0 4812
    rwa [e, ad_add] at this
  have h9' : (reg st₁.data .r9).toNat = 16 := by
    rw [show reg st₁.data .r9 = _ from hm₁.regs _ _ h9]
    rfl
  have hw8 : env.load 0 80 8 = (w 8).toBitVec := by
    rw [Env.load_of_bytesAt (length_regBytes _) (by
      rw [show env.base 0 + BitVec.ofNat 64 80 = ad m₀ (fr + 80) from ad_add _ _ _]
      exact h.w8), ofBytes_regBytes]
  -- `wots_leaf` of the top layer.
  have hpre₁ : WotsLeafPre st₁.data :=
    wotsLeafPre P C₁ hrsp₁ (o := 184) (o1 := 56) (o4 := 592) (o6 := 5740) (o7 := 4812)
      (hx h0) (hx h1) (hx h8) h9' h6 h7 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine call_then hpc₁ hwots hpre₁ fun st₂ hpc₂ hrsp₂ hpost₂ => ?_
  obtain ⟨hout₂, hsame₂, hs₂⟩ := hpost₂
  have hpp : WotsLeafPre.pp st₁.data = pp w := by
    unfold WotsLeafPre.pp
    rw [hx h1]
    have hsub := bytesAt_sub hpk₁ (k := 16) (ys := (pkB w).drop 16) fun t ht => by
      rw [← List.getElem?_eq_getElem, List.getElem?_drop]
    have hb := hsub.bytesOf
    rw [List.length_drop, length_pkB, ad_add] at hb
    exact hb
  have hlayer : WotsLeafPre.layer st₁.data = 1 := by
    unfold WotsLeafPre.layer
    rw [show reg st₁.data .rdx = _ from hm₁.regs _ _ h2]
    rfl
  have he : WotsLeafPre.e st₁.data = li1 w := by
    unfold WotsLeafPre.e
    rw [show reg st₁.data .rcx = _ from hm₁.regs _ _ h3, hi16_eval hw8]
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_ofBitVec, BitVec.toNat_setWidth, BitVec.toNat_ofNat, li1_toNat]
    omega
  have hmsg : WotsLeafPre.message st₁.data = root0 w leaf := by
    unfold WotsLeafPre.message
    rw [hx h8, h9']
    have := hcur₁.bytesOf
    rwa [hroot] at this
  have hrnd : WotsLeafPre.randomizer st₁.data = (topL w).randomizer := by
    unfold WotsLeafPre.randomizer WotsLeafPre.rndPtr
    rw [show rspOf st₁.data + 8#64 = ad m₀ (fr + 8) by rw [hrsp₁, ad_add], ptrAt_of h6]
    have hr := layer_rnd (bs := sigB w) (c := 1204) (by simp [length_sigB]) htop₁
    have hl : (topL w).randomizer.length = 16 := by
      simp only [topL, takeLayer]
      exact length_slice (by rw [length_sigB]; omega)
    have := hr.bytesOf
    rw [ad_add] at this
    unfold topL at hl
    rw [hl] at this
    exact this
  have hvals : WotsLeafPre.values st₁.data = (topL w).chainValues := by
    unfold WotsLeafPre.values WotsLeafPre.valuesPtr
    rw [show rspOf st₁.data + 16#64 = ad m₀ (fr + 16) by rw [hrsp₁, ad_add], ptrAt_of h7]
    exact values_of (bs := sigB w) (c := 1204) (o := 4556) (by simp [length_sigB]) htop₁
  rw [hpp, hlayer, he, hmsg, hrnd, hvals, hx h0] at hout₂
  change WotsLeafOut1 _ (leaf1 w (root0 w leaf)) at hout₂
  rw [hx h0] at hsame₂
  change SameOutside _ _ (CallR m₀ st₁.data 184 75 wotsLeafStack) at hsame₂
  have C₂ := C₁.callR P hs₂ hrsp₁ (by decide) (by decide) (by decide) hsame₂
  have hrsp₂' : rspOf st₂.data = ad m₀ (fr + 8) := by rw [hrsp₂, hrsp₁, ad_add]
  have hk₂ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs →
      x + bs.length ≤ 5816 → (x + bs.length ≤ 184 ∨ 259 ≤ x) →
      BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb hle h1 => keep_callR P hrsp₁ (by decide) (by decide) hsame₂ hb hle (Nat.zero_le _) h1
  have hpk₂ := hk₂ hpk₁ (by rw [length_pkB]; omega) (by rw [length_pkB]; omega)
  have htop₂ := hk₂ htop₁ (by rw [hlen1]; omega) (by omega)
  have hr12₂ : reg st₂.data .r12 = BitVec.ofNat 64 1 :=
    (hs₂.1 .r12 rfl).trans (hm₁.regs _ _ h12)
  have hrbx₂ : reg st₂.data .rbx = BitVec.ofNat 64 ((w 8).toNat % 2 ^ 32 / 2 ^ 16) :=
    (hs₂.1 .rbx rfl).trans ((hm₁.regs _ _ hbx).trans (hi16_eval hw8))
  -- Block 17.
  let env₂ := Env.ofMachine st₂.data [frR m₀] (fun _ => 0) 0
  have hwf₂ : env₂.WF := frame_wf P C₂.kept
  have hm₂ : Match env₂ stR st₂.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hrsp₂'.trans (ad_int m₀ 8).symm, trivial⟩ trivial trivial
      trivial
  obtain ⟨g24, gmem, gk⟩ := st17_facts
  have hmap₂ : Mapped st₂.data.dmem (ad m₀ (fr + 184)) 75 := C₂.mapped P (by fro)
  have hd₂ : bytesOf st₂.data.dmem (ad m₀ (fr + 184)) 75 =
      (st₂.data.dmem.get? (ad m₀ (fr + 184))).getD 0 ::
        bytesOf st₂.data.dmem (ad m₀ (fr + 185)) 74 := by
    rw [bytesOf_succ, ad_add, show fr + 184 + 1 = fr + 185 by omega]
  have hget : ∀ b, (st₂.data.dmem.get? (ad m₀ (fr + 184))).getD 0 = b →
      st₂.data.dmem.get? (ad m₀ (fr + 184)) = some b := fun b hb => by
    have := hmap₂ 0 (by omega)
    rw [show ad m₀ (fr + 184) + BitVec.ofNat 64 0 = ad m₀ (fr + 184) from BitVec.add_zero _]
      at this
    revert hb this
    cases st₂.data.dmem.get? (ad m₀ (fr + 184)) <;> simp
  refine exec_at (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b17' hwf₂
    (fun _ h => nomatch h) (hpc₂.trans rfl) hm₂ fun st₃ hm₃ hpc₃ => ?_
  have hd₃ : st₃.data.dmem = st₂.data.dmem := hm₃.dmem_eq hwf₂ gmem
  have C₃ := C₂.congr hd₃
  have hrsp₃ : rspOf st₃.data = ad m₀ (fr + 24) := (hm₃.regs _ _ g24).trans (eval_ptr0 _)
  have hreg₃ : ∀ r ∈ [Reg64.rbx, .r12], reg st₃.data r = reg st₂.data r :=
    fun r hr => hm₃.regs _ _ (gk r hr)
  have hload : ∀ b, (st₂.data.dmem.get? (ad m₀ (fr + 184))).getD 0 = b →
      env₂.load 0 184 1 = BitVec.ofNat 64 b.toNat := fun b hb =>
    load_one (by
      rw [show env₂.base 0 + BitVec.ofNat 64 184 = ad m₀ (fr + 184) from ad_add _ _ _]
      exact hget b hb)
  have hcond : ∀ b : UInt8, (b = 0 ∨ b = 1) →
      (st₂.data.dmem.get? (ad m₀ (fr + 184))).getD 0 = b →
      (SBool.not (.cmp .eq .W8 (.load 0 184 1) (.lit 1))).eval env₂ = !(b == 1) := by
    intro b hb01 hb
    simp only [SBool.eval, CmpOp.apply, Sym.eval]
    rw [hload b hb]
    rcases hb01 with rfl | rfl <;> decide
  cases hl : leaf1 w (root0 w leaf) with
  | none =>
    rw [hl] at hout₂
    have h0b : (st₂.data.dmem.get? (ad m₀ (fr + 184))).getD 0 = 0 := by
      have := hout₂
      simp only [WotsLeafOut1, hd₂, List.head?_cons, Option.some.injEq] at this
      exact this
    simp only [PcOk, hcond 0 (.inl rfl) h0b] at hpc₃
    have hfalse : xmssVerify w = false := by
      rw [xmssVerify_eq]
      simp only [layerRoot0 hl0, layerRoot1_none hl]
    refine hfail st₃ ?_ ⟨C₃, hrsp₃, hfalse⟩
    rw [hpc₃, Sym.ite_pos (by decide)]
    exact hp.label NativeRustcX64.Xmss.XmssVerify.label_10_at
  | some xl =>
    obtain ⟨x', leaf'⟩ := xl
    rw [hl] at hout₂
    have hlens := wotsLeaf_length hl
    have hout' := hout₂
    simp only [WotsLeafOut1] at hout'
    rw [List.take_of_length_le (by rw [length_bytesOf]), hd₂, List.cons.injEq] at hout'
    obtain ⟨h1b, hrest⟩ := hout'
    simp only [PcOk, hcond 1 (.inr rfl) h1b] at hpc₃
    have hpc₃' : st₃.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b18Offset) := by
      rw [hpc₃, Sym.ite_neg (by decide)]
      rfl
    have hxl₂ : BytesAt st₂.data.dmem (ad m₀ (fr + 185)) (x' ++ leaf') := by
      rw [← hrest]
      exact bytesAt_bytesOf (C₂.mapped P (by fro))
    have hleaf₃ : BytesAt st₃.data.dmem (ad m₀ (fr + 243)) leaf' := by
      have := bytes_drop hxl₂ 58
      rw [List.drop_left' hlens.1, show fr + 185 + 58 = fr + 243 by omega] at this
      rw [hd₃]
      exact this
    -- Block 18.
    let env₃ := Env.ofMachine st₃.data (frameRs m₀) (fun _ => 0) 0
    have hwf₃ : env₃.WF := frameG_wf P C₃.kept
    have hm₃' : Match env₃ (stF []) st₃.data :=
      match_stG P C₃.same hrsp₃ trivial
    obtain ⟨e1, e2, e3, esp, ebp, e13, e14, e15, e12, emem⟩ := st18_facts
    refine fall_step (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b18 hwf₃ hpc₃' hm₃'
      fun st₄ hpc₄ hm₄ => hok st₄ x' leaf' hl (hpc₄.trans rfl) ?_
    change Match _ (after b18 (stF [])) st₄.data at hm₄
    have hd₄ : st₄.data.dmem = st₃.data.dmem := hm₄.dmem_eq hwf₃ emem
    have hh := halves hleaf₃
    have l1 : (leaf'.take 8).length = 8 := by rw [List.length_take, hlens.2]; rfl
    have l2 : ((leaf'.drop 8).take 8).length = 8 := by
      rw [List.length_take, List.length_drop, hlens.2]; rfl
    refine ⟨C₃.congr (hd₄.trans rfl), (hm₄.regs _ _ esp).trans (eval_ptr0 _), ?_, ?_,
      (hm₄.regs _ _ e13).trans (eval_ptr0 _), (hm₄.regs _ _ e14).trans (eval_ptr0 _),
      (hm₄.regs _ _ ebp).trans (eval_ptr0 _), (hm₄.regs _ _ e15).trans (eval_ptr0 _),
      hd₄ ▸ hd₃ ▸ hpk₂, hd₄ ▸ hd₃ ▸ htop₂, ?_⟩
    · exact (hm₄.regs _ _ e12).trans ((hreg₃ .r12 (by simp)).trans hr12₂)
    · rw [show reg st₄.data .rbx = _ from hm₄.regs _ _ e3]
      apply BitVec.eq_of_toNat_eq
      show (UnOp.apply .trunc .W32 (reg st₃.data .rbx)).toNat = _
      rw [trunc_toNat, hreg₃ .rbx (by simp), hrbx₂, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        li1_toNat]
      show (w 8).toNat % 2 ^ 32 / 2 ^ 16 % 2 ^ 64 % 2 ^ 32 = _
      omega
    · have hh2 : BytesAt st₃.data.dmem (ad m₀ (fr + 251)) ((leaf'.drop 8).take 8) := by
        rw [show fr + 251 = fr + 243 + 8 from rfl]
        exact hh.2
      have r0 : regBytes ((Sym.load 0 243 8).eval env₃) = leaf'.take 8 := regBytes_frame l1 hh.1
      have r1 : regBytes ((Sym.load 0 251 8).eval env₃) = (leaf'.drop 8).take 8 :=
        regBytes_frame l2 hh2
      rw [show reg st₄.data .rcx = _ from hm₄.regs _ _ e1,
        show reg st₄.data .rdx = _ from hm₄.regs _ _ e2, r0, r1, ← List.take_add,
        List.take_of_length_le (by rw [hlens.2]), pf_zero]

end NativeRustcX64.Xmss.XmssVerify
