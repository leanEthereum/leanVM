module

public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Xmss.WotsLeaf.Names

public import NativeRustcX64.XmssVerify.WotsCall

/-!
# `xmss_verify`: from the parsed layers to the loop over the bottom layer's path (x86-64)

`bottom`: blocks 5 to 8 with the calls of `wots_leaf` and `memcpy` between them
(`NativeRustcX64.XmssVerify.Bottom`): from `Parsed` to the failure (`FailAt` at block 27) if the
bottom layer's one-time leaf is `None`, else to `TreeAt0` at level `0` from its leaf.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc.Xmss

set_option Elab.async false

public section

/-- The bytes from `a`: the first, then the rest. -/
theorem bytesOf_succ (d : DataMem) (a : BitVec 64) (n : Nat) :
    bytesOf d a (n + 1) = (d.get? a).getD 0 :: bytesOf d (a + 1#64) n := by
  apply List.ext_getElem (by simp [bytesOf])
  intro i h1 h2
  cases i with
  | zero => simp [bytesOf]
  | succ i =>
    simp only [bytesOf, List.getElem_map, List.getElem_range, List.getElem_cons_succ]
    rw [show a + BitVec.ofNat 64 (i + 1) = a + 1#64 + BitVec.ofNat 64 i by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]]

/-- An environment's load of one byte. -/
theorem load_one {env : Env} {r off : Nat} {b : UInt8}
    (h : env.mem0.get? (env.base r + BitVec.ofNat 64 off) = some b) :
    env.load r off 1 = BitVec.ofNat 64 b.toNat := by
  rw [Env.load_of_bytesAt (bs := [b]) (n := 1) rfl (fun i hi => by
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    simpa using h)]
  simp [Int.ofBytes]

/-- `Common` is a fact of memory. -/
theorem Common.congr {m₀ m m' : MachineData} (C : Common m₀ m) (h : m'.dmem = m.dmem) :
    Common m₀ m' := by
  obtain ⟨hs, hsm, hk⟩ := C
  exact ⟨fun j hj => h ▸ hs j hj, h ▸ hsm, h ▸ hk⟩

theorem li_eq (x : UInt64) :
    UInt32.ofBitVec ((BitVec.setWidth 64 (BitVec.setWidth Width.W32.bits x.toBitVec)).setWidth 32) =
      x.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofBitVec, BitVec.toNat_setWidth, UInt64.toNat_toUInt32,
    show Width.W32.bits = 32 from rfl]
  have := x.toBitVec.isLt
  rw [Nat.mod_eq_of_lt (a := x.toBitVec.toNat % 2 ^ 32) (by omega)]
  simp

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

set_option linter.unusedSimpArgs false in
/-- **The bottom layer's one-time leaf**: from block 5 to the failure, or to the loop over the
bottom layer's path from the leaf. -/
public theorem bottom {k : Nat} (hp : Placed code k)
    (hwots : Spec (label NativeRustcX64.Xmss.WotsLeaf.entryLabel) WotsLeafPre WotsLeafPost)
    (hmemcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) (P : Pre w m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b5Offset)) (h : Parsed w m₀ st.data)
    {R : MachineState → Prop}
    (hfail : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b27Offset) → FailAt w m₀ st'.data →
      Eventually (step1 Host.exe) R st')
    (hok : ∀ (st' : MachineState) (x leaf : List UInt8), leaf0 w = some (x, leaf) →
      st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b9Offset) → TreeAt0 w m₀ leaf st'.data 0 →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  -- Block 5.
  let env := Env.ofMachine st.data (frameRs m₀) (fun _ => 0) (Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b5Offset + b5.length)).toBitVec
  have hwf : env.WF := frameG_wf P C.kept
  have hm0 : Match env st5 st.data :=
    match_stG P C.same h.rsp ⟨h.r15.trans (ad_int m₀ 56).symm, trivial⟩
  obtain ⟨h0, h1, h2, h3, h8, h9, hsp, hk, hw, h6w, h7w, -⟩ := st5_facts
  refine call_step (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b5 hwf rfl hpc hm0
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ (after b5 st5) st₁.data at hm₁
  have C₁ := Common.block P C hwf hm₁ hw
  have hx : ∀ {r : Reg64} {o : Nat}, (after b5 st5).reg r = some (.ptr 0 o) →
      reg st₁.data r = ad m₀ (fr + o) := fun hr => (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₁ : rspOf st₁.data = ad m₀ (fr + 0) := hx hsp
  have hk₁ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 5756 → BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hle => frame_keep2 P hwf hm₁ st5_low hb h24 hle (by omega)
  have hpk₁ := hk₁ h.pk (by omega) (by simp [length_pkB])
  have hmsg₁ := hk₁ h.msg (by omega) (by simp [length_msgB])
  have hli₁ : reg st₁.data .rbp = u32W (w 8) :=
    (hm₁.regs .rbp _ (hk .rbp (by simp))).trans h.rbp
  have hlen0 : (bottomL w).memBytes.length = 1200 :=
    length_memBytes (by simp [length_sigB])
  have hlen1 : (topL w).memBytes.length = 1200 :=
    length_memBytes (by simp [length_sigB])
  have hbot₁ := hk₁ h.bottom (by omega) (by simp [hlen0])
  have htop₁ := hk₁ h.top (by omega) (by simp [hlen1])
  have h6 : BytesAt st₁.data.dmem (ad m₀ (fr + 8)) (regBytes (ad m₀ (fr + 4540))) := by
    have := hm₁.bytesAt_write (r := 0) rfl (by omega) h6w
    have e : (Sym.ptr 0 4540).eval env = ad m₀ (fr + 4540) := eval_ptr0 4540
    rwa [e, ad_add] at this
  have h7 : BytesAt st₁.data.dmem (ad m₀ (fr + 16)) (regBytes (ad m₀ (fr + 3612))) := by
    have := hm₁.bytesAt_write (r := 0) rfl (by omega) h7w
    have e : (Sym.ptr 0 3612).eval env = ad m₀ (fr + 3612) := eval_ptr0 3612
    rwa [e, ad_add] at this
  have h9' : (reg st₁.data .r9).toNat = 32 := by
    rw [show reg st₁.data .r9 = _ from hm₁.regs _ _ h9]
    rfl
  -- `wots_leaf` of the bottom layer.
  have hpre₁ : WotsLeafPre st₁.data :=
    wotsLeafPre P C₁ hrsp₁ (o := 184) (o1 := 56) (o4 := 152) (o6 := 4540) (o7 := 3612)
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
  have hlayer : WotsLeafPre.layer st₁.data = 0 := by
    unfold WotsLeafPre.layer
    rw [show reg st₁.data .rdx = _ from hm₁.regs _ _ h2]
    rfl
  have he : WotsLeafPre.e st₁.data = li w := by
    unfold WotsLeafPre.e
    rw [show reg st₁.data .rcx = _ from hm₁.regs _ _ h3]
    simp only [Sym.eval, UnOp.apply, ext, Sym.low]
    rw [show env.regs .r13 = reg st.data .r13 from rfl, h.r13]
    exact li_eq _
  have hmsg : WotsLeafPre.message st₁.data = msgB w := by
    unfold WotsLeafPre.message
    rw [hx h8, h9']
    have := hmsg₁.bytesOf
    rwa [length_msgB] at this
  have hrnd : WotsLeafPre.randomizer st₁.data = (bottomL w).randomizer := by
    unfold WotsLeafPre.randomizer WotsLeafPre.rndPtr
    rw [show rspOf st₁.data + 8#64 = ad m₀ (fr + 8) by rw [hrsp₁, ad_add], ptrAt_of h6]
    have hr := layer_rnd (bs := sigB w) (c := 4) (by rw [length_sigB]; omega) hbot₁
    have hl : (bottomL w).randomizer.length = 16 := by
      simp only [bottomL, takeLayer]
      exact length_slice (by rw [length_sigB]; omega)
    have := hr.bytesOf
    rw [ad_add] at this
    unfold bottomL at hl
    rw [hl] at this
    exact this
  have hvals : WotsLeafPre.values st₁.data = (bottomL w).chainValues := by
    unfold WotsLeafPre.values WotsLeafPre.valuesPtr
    rw [show rspOf st₁.data + 16#64 = ad m₀ (fr + 16) by rw [hrsp₁, ad_add], ptrAt_of h7]
    exact values_of (bs := sigB w) (c := 4) (o := 3356) (by rw [length_sigB]; omega) hbot₁
  rw [hpp, hlayer, he, hmsg, hrnd, hvals, hx h0] at hout₂
  change WotsLeafOut1 _ (leaf0 w) at hout₂
  rw [hx h0] at hsame₂
  change SameOutside _ _ (CallR m₀ st₁.data 184 75 wotsLeafStack) at hsame₂
  have C₂ := C₁.callR P hs₂ hrsp₁ (by decide) (by decide) (by decide) hsame₂
  have hrsp₂' : rspOf st₂.data = ad m₀ (fr + 8) := by rw [hrsp₂, hrsp₁, ad_add]
  have hk₂ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs →
      x + bs.length ≤ 5816 → (x + bs.length ≤ 184 ∨ 259 ≤ x) →
      BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb hle h1 => keep_callR P hrsp₁ (by decide) (by decide) hsame₂ hb hle (Nat.zero_le _) h1
  have hpk₂ := hk₂ hpk₁ (by rw [length_pkB]; omega) (by rw [length_pkB]; omega)
  have hli₂ : reg st₂.data .rbp = u32W (w 8) := (hs₂.1 .rbp rfl).trans hli₁
  have hbot₂ := hk₂ hbot₁ (by rw [hlen0]; omega) (by omega)
  have htop₂ := hk₂ htop₁ (by rw [hlen1]; omega) (by omega)
  have hr12₂ : reg st₂.data .r12 = ad m₀ (fr + 3356) :=
    (hs₂.1 .r12 rfl).trans ((hm₁.regs _ _ (hk .r12 (by simp))).trans h.r12)
  have hr13₂ : reg st₂.data .r13 = (w 8).toBitVec :=
    (hs₂.1 .r13 rfl).trans ((hm₁.regs _ _ (hk .r13 (by simp))).trans h.r13)
  -- Block 6.
  let env₂ := Env.ofMachine st₂.data [frR m₀] (fun _ => 0) 0
  have hwf₂ : env₂.WF := frame_wf P C₂.kept
  have hm₂ : Match env₂ stR st₂.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hrsp₂'.trans (ad_int m₀ 8).symm, trivial⟩ trivial trivial
      trivial
  obtain ⟨g24, gmem, gk⟩ := st6_facts
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
  refine exec_at (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b6' hwf₂ (fun _ h => nomatch h)
    (hpc₂.trans rfl) hm₂ fun st₃ hm₃ hpc₃ => ?_
  have hd₃ : st₃.data.dmem = st₂.data.dmem := hm₃.dmem_eq hwf₂ gmem
  have C₃ := C₂.congr hd₃
  have hrsp₃ : rspOf st₃.data = ad m₀ (fr + 24) := (hm₃.regs _ _ g24).trans (eval_ptr0 _)
  have hreg₃ : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r15], reg st₃.data r = reg st₂.data r :=
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
  cases hl : leaf0 w with
  | none =>
    rw [hl] at hout₂
    have h0b : (st₂.data.dmem.get? (ad m₀ (fr + 184))).getD 0 = 0 := by
      have := hout₂
      simp only [WotsLeafOut1, hd₂, List.head?_cons, Option.some.injEq] at this
      exact this
    simp only [PcOk, hcond 0 (.inl rfl) h0b] at hpc₃
    have hfalse : xmssVerify w = false := by
      rw [xmssVerify_eq]
      unfold layerRoot
      rw [show wotsLeaf (pp w) 0 (li w) (msgB w) (bottomL w).randomizer (bottomL w).chainValues =
        none from hl]
    refine hfail st₃ ?_ ⟨C₃, hrsp₃, hfalse⟩
    rw [hpc₃, Sym.ite_pos (by decide)]
    exact hp.label NativeRustcX64.Xmss.XmssVerify.label_10_at
  | some xl =>
    obtain ⟨x, leaf⟩ := xl
    rw [hl] at hout₂
    have hlens := wotsLeaf_length hl
    have hout' := hout₂
    simp only [WotsLeafOut1] at hout'
    rw [List.take_of_length_le (by rw [length_bytesOf]), hd₂, List.cons.injEq] at hout'
    obtain ⟨h1b, hrest⟩ := hout'
    simp only [PcOk, hcond 1 (.inr rfl) h1b] at hpc₃
    have hpc₃' : st₃.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b7Offset) := by
      rw [hpc₃, Sym.ite_neg (by decide)]
      rfl
    have hxl₂ : BytesAt st₂.data.dmem (ad m₀ (fr + 185)) (x ++ leaf) := by
      rw [← hrest]
      exact bytesAt_bytesOf (C₂.mapped P (by fro))
    -- Block 7.
    let env₃ := Env.ofMachine st₃.data (frameRs m₀) (fun _ => 0)
      (Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b7Offset + b7.length)).toBitVec
    have hwf₃ : env₃.WF := frameG_wf P C₃.kept
    have hm₃' : Match env₃ (stF []) st₃.data :=
      match_stG P C₃.same hrsp₃ trivial
    obtain ⟨f0, f1, f2, fsp, fk, f80, fw, flow⟩ := st7_facts
    refine call_step (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b7 hwf₃ rfl hpc₃'
      hm₃' fun st₄ hpc₄ hm₄ => ?_
    change Match _ (after b7 (stF [])) st₄.data at hm₄
    have C₄ := Common.block P C₃ hwf₃ hm₄ fw
    have hy : ∀ {r : Reg64} {o : Nat}, (after b7 (stF [])).reg r = some (.ptr 0 o) →
        reg st₄.data r = ad m₀ (fr + o) := fun hr => (hm₄.regs _ _ hr).trans (eval_ptr0 _)
    have hrsp₄ : rspOf st₄.data = ad m₀ (fr + 16) := hy fsp
    have hk₄ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs →
        88 ≤ x → x + bs.length ≤ 5816 → BytesAt st₄.data.dmem (ad m₀ (fr + x)) bs :=
      fun hb h88 hle => frame_keep P hwf₃ hm₄ fw (hd₃ ▸ hb) h88 hle
    have hxl₄ := hk₄ hxl₂ (by omega) (by simp [hlens.1, hlens.2])
    have hpk₄ : BytesAt st₄.data.dmem (ad m₀ (fr + 40)) (pkB w) :=
      frame_keep2 P hwf₃ hm₄ flow (hd₃ ▸ hpk₂) (by omega) (by simp [length_pkB]) (by simp [length_pkB])
    have hw8₄ : BytesAt st₄.data.dmem (ad m₀ (fr + 80)) (regBytes (w 8).toBitVec) := by
      have := hm₄.bytesAt_write (r := 0) rfl (by omega) f80
      have e : (Sym.reg .r13).eval env₃ = (w 8).toBitVec :=
        (hreg₃ .r13 (by simp)).trans hr13₂
      rw [ad_add, e] at this
      exact this
    have hli₄ : reg st₄.data .rbp = u32W (w 8) :=
      (hm₄.regs .rbp _ (fk .rbp (by simp))).trans ((hreg₃ .rbp (by simp)).trans hli₂)
    have hbot₄ := hk₄ hbot₂ (by omega) (by simp [hlen0])
    have htop₄ := hk₄ htop₂ (by omega) (by simp [hlen1])
    have hn74 : (reg st₄.data .rdx).toNat = 74 := by
      rw [show reg st₄.data .rdx = _ from hm₄.regs _ _ f2]
      rfl
    -- `memcpy` of the codeword and the leaf.
    refine call_then hpc₄ hmemcpy (memcpyPre P C₄ hrsp₄ (o := fr + 534) (o' := fr + 185)
      (n := 74) (by omega) (hy f0) (hy f1) hn74 (by omega) (by fro) (by fro) (by omega)
      (by omega)) fun st₅ hpc₅ hrsp₅ hpost₅ => ?_
    obtain ⟨-, hbytes₅, hsame₅, hs₅⟩ := hpost₅
    rw [hy f0, hy f1, hn74] at hbytes₅
    rw [hy f0, hn74] at hsame₅
    have hb185 := hxl₄.bytesOf
    rw [List.length_append, hlens.1, hlens.2] at hb185
    rw [hb185] at hbytes₅
    have C₅ : Common m₀ st₅.data := C₄.call hs₅ hsame₅ (fun p hp => P.inRange_lo (by fro) hp)
      fun x hx hx' => P.not_inRange_ad (o := fr + 534) (s := 74) (by fro) (by fro) (by omega)
    have hk₅ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₄.data.dmem (ad m₀ (fr + x)) bs →
        x + bs.length ≤ 5816 → (x + bs.length ≤ 534 ∨ 608 ≤ x) →
        BytesAt st₅.data.dmem (ad m₀ (fr + x)) bs :=
      fun hb hle h1 => keep_ad hsame₅ hb fun t ht => by
        rw [Nat.add_assoc]
        exact P.not_inRange_ad (o := fr + 534) (s := 74) (by fro) (by fro) (by omega)
    have hleaf₅ : BytesAt st₅.data.dmem (ad m₀ (fr + 592)) leaf := by
      have := bytesAt_sub hbytes₅ (k := 58) (ys := leaf) fun t ht => by
        rw [← List.getElem?_eq_getElem, List.getElem?_append_right (by omega), hlens.1,
          Nat.add_sub_cancel_left]
      rwa [ad_add] at this
    have hrsp₅' : rspOf st₅.data = ad m₀ (fr + 24) := by rw [hrsp₅, hrsp₄, ad_add]
    -- Block 8.
    let env₅ := Env.ofMachine st₅.data (frameRs m₀) (fun _ => 0) 0
    have hwf₅ : env₅.WF := frameG_wf P C₅.kept
    have hm₅ : Match env₅ (stF []) st₅.data :=
      match_stG P C₅.same hrsp₅' trivial
    obtain ⟨e3, ebp, e15, esp, e12, emem⟩ := st8_facts
    refine fall_step (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b8 hwf₅ (hpc₅.trans rfl)
      hm₅ fun st₆ hpc₆ hm₆ => hok st₆ x leaf hl (hpc₆.trans rfl) ?_
    change Match _ (after b8 (stF [])) st₆.data at hm₆
    have hd₆ : st₆.data.dmem = st₅.data.dmem := hm₆.dmem_eq hwf₅ emem
    have hli₅ : reg st₅.data .rbp = u32W (w 8) := (hs₅.1 .rbp rfl).trans hli₄
    refine ⟨C₅.congr hd₆, (hm₆.regs _ _ esp).trans (eval_ptr0 _), ?_, ?_, ?_,
      (hm₆.regs _ _ e15).trans (eval_ptr0 _), hd₆ ▸ hk₅ hpk₄ (by simp [length_pkB])
        (by simp [length_pkB]),
      hd₆ ▸ hk₅ hw8₄ (by simp [length_regBytes]) (by simp [length_regBytes]),
      hd₆ ▸ hk₅ hbot₄ (by simp [hlen0]) (by simp),
      hd₆ ▸ hk₅ htop₄ (by simp [hlen1]) (by simp), ?_⟩
    · exact (hm₆.regs _ _ ebp).trans rfl
    · exact (hm₆.regs .rbx _ e3).trans hli₅
    · refine (hm₆.regs _ _ e12).trans ?_
      show reg st₅.data .r12 = _
      exact (hs₅.1 .r12 rfl).trans ((hm₄.regs _ _ (fk .r12 (by simp))).trans
        ((hreg₃ .r12 (by simp)).trans hr12₂))
    · rw [hd₆, pf_zero]
      exact hleaf₅

end NativeRustcX64.Xmss.XmssVerify