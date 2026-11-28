module

public import NativeRustcX64.Code.Xmss.LayerRead.Names
public import NativeRustcX64.XmssVerify.Parse

/-! # Two calls to the slice-cursor layer parser -/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc.Xmss

set_option Elab.async false

public section

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

@[expose] def ReadR (m₀ m : MachineData) (o oc : Nat) (p : BitVec 64) : Prop :=
  InRange (ad m₀ (fr + o)) 1200 p ∨ InRange (ad m₀ (fr + oc)) 16 p ∨
    InRange (stackBelow m layerReadStack) layerReadStack p

theorem not_readR (P : Pre w m₀) (hrsp : rspOf m = ad m₀ (fr + 16)) {o oc x : Nat}
    (ho : o + 1200 ≤ 5816) (hoc : oc + 16 ≤ 5816) (hx16 : 16 ≤ x) (hx : x < 5816)
    (h1 : x < o ∨ o + 1200 ≤ x) (h2 : x < oc ∨ oc + 16 ≤ x) :
    ¬ReadR m₀ m o oc (ad m₀ (fr + x)) := by
  rintro (hp | hp | hp)
  · exact P.not_inRange_ad (by fro) (by fro) (by omega) hp
  · exact P.not_inRange_ad (by fro) (by fro) (by omega) hp
  · exact not_stack P hrsp (by decide) hx16 hx hp

theorem keep_readR (P : Pre w m₀) (hrsp : rspOf m = ad m₀ (fr + 16)) {o oc : Nat}
    (ho : o + 1200 ≤ 5816) (hoc : oc + 16 ≤ 5816) {d d' : DataMem}
    (hsame : SameOutside d d' (ReadR m₀ m o oc)) {x : Nat} {bs : List UInt8}
    (h : BytesAt d (ad m₀ (fr + x)) bs) (hx16 : 16 ≤ x) (hx : x + bs.length ≤ 5816)
    (h1 : x + bs.length ≤ o ∨ o + 1200 ≤ x) (h2 : x + bs.length ≤ oc ∨ oc + 16 ≤ x) :
    BytesAt d' (ad m₀ (fr + x)) bs :=
  keep_ad hsame h fun t ht => by
    rw [Nat.add_assoc]
    exact not_readR P hrsp ho hoc (by omega) (by omega) (by omega) (by omega)

theorem Common.readR (P : Pre w m₀) (C : Common m₀ m) {m' : MachineData} (hs : Saved m m')
    (hrsp : rspOf m = ad m₀ (fr + 16)) {o oc : Nat} (ho : o + 1200 ≤ 5760)
    (hoc : oc + 16 ≤ 5760) (hsame : SameOutside m.dmem m'.dmem (ReadR m₀ m o oc)) :
    Common m₀ m' :=
  C.call hs hsame
    (fun p hp => by
      rcases hp with hp | hp | hp
      · exact P.inRange_lo (by fro) hp
      · exact P.inRange_lo (by fro) hp
      · rw [stackBelow_at hrsp (by decide)] at hp
        exact P.inRange_lo (by decide) hp)
    fun x hx hx' => by
      have := not_readR P hrsp (x := x - fr) (o := o) (oc := oc) (by omega) (by omega) (by fro)
        (by fro) (by fro) (by fro)
      rwa [show fr + (x - fr) = x by omega] at this

omit [Labels] in
theorem slice_input {oc ob : Nat} (hsi : reg m .rsi = ad m₀ (fr + oc))
    (hc : BytesAt m.dmem (ad m₀ (fr + oc)) (wordBytes (UInt64.ofBitVec (ad m₀ (fr + ob))))) :
    LayerReadPre.input m = ad m₀ (fr + ob) := by
  have hb := hc.bytesOf
  rw [NativeRustc.length_wordBytes] at hb
  unfold LayerReadPre.input
  rw [hsi, hb, leNat_wordBytes]
  exact BitVec.ofNat_toNat 64 _

omit [Labels] in
theorem slice_length {oc n : Nat} (hsi : reg m .rsi = ad m₀ (fr + oc))
    (hc : BytesAt m.dmem (ad m₀ (fr + oc + 8)) (wordBytes n.toUInt64)) (hn : n < 2 ^ 64) :
    LayerReadPre.remaining m = n := by
  have hb := hc.bytesOf
  rw [NativeRustc.length_wordBytes] at hb
  unfold LayerReadPre.remaining
  rw [hsi, ad_add, hb, leNat_wordBytes]
  simpa [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem layerReadPre (P : Pre w m₀) (C : Common m₀ m) (hrsp : rspOf m = ad m₀ (fr + 16))
    {o oc ob n : Nat} (h0 : reg m .rdi = ad m₀ (fr + o)) (h1 : reg m .rsi = ad m₀ (fr + oc))
    (hinput : LayerReadPre.input m = ad m₀ (fr + ob)) (hlen : LayerReadPre.remaining m = n)
    (ho : 24 ≤ o) (hoc : 24 ≤ oc) (hob : 24 ≤ ob)
    (h : o + 1200 ≤ 5816) (hc : oc + 16 ≤ 5816) (hb : ob + 1200 ≤ 5816)
    (hd1 : o + 1200 ≤ oc ∨ oc + 16 ≤ o) (hd2 : o + 1200 ≤ ob ∨ ob + 1200 ≤ o)
    (hd3 : oc + 16 ≤ ob ∨ ob + 1200 ≤ oc) (hn : 1200 ≤ n) (hn' : n < 2 ^ 64) :
    LayerReadPre m := by
  have hbuf : ∀ {x s : Nat}, 24 ≤ x → x + s ≤ 5816 → 0 < s →
      LayerReadPre.Buf m (ad m₀ (fr + x)) s := fun hx hs hs0 =>
    ⟨C.mapped P (by fro), P.ad_nw (by fro),
      apart_at P hrsp (by decide) (by fro) (by omega) (by fro) hs0⟩
  unfold LayerReadPre
  rw [h0, h1, hinput, hlen]
  refine ⟨stackOk_at P C hrsp (by omega) (by decide), hn, hn',
    hbuf ho h (by omega), hbuf hoc hc (by omega), hbuf hob hb (by omega),
    P.apart_ad (by omega) (by fro) (by fro) (by omega) (by omega),
    P.apart_ad (by omega) (by fro) (by fro) (by omega) (by omega),
    P.apart_ad (by omega) (by fro) (by fro) (by omega) (by omega), ?_⟩
  apply gotAt_at P C hrsp (by omega) (by decide) (by decide)
  intro l hl a ha
  have hl' : l ∈ ["memcpy", "memset"] := by
    simp only [List.mem_singleton] at hl
    simp [hl]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact got_apart P hl' (by fro) (by dsimp; decide)
  · exact got_apart P hl' (by fro) (by dsimp; decide)
  · exact got_apart P hl' (by fro) (by dsimp; decide)

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

theorem parse {k : Nat} (hp : Placed code k)
    (hread : Spec (label NativeRustcX64.Xmss.LayerRead.entryLabel) LayerReadPre LayerReadPost)
    (P : Pre w m₀) {st : MachineState} (hpc : st.pc = Host.addrOf (k + b3Offset))
    (h : LoopAt w m₀ st.data 50) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + b5Offset) → Parsed w m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hsig := sig_of h
  have hmsg := msg_of h
  let env := Env.ofMachine st.data (frameRs m₀) (fun _ => 0)
    (Host.addrOf (k + b3Offset + b3.length)).toBitVec
  have hwf : env.WF := frameG_wf P C.kept
  have hm0 : Match env st3 st.data := match_stG P C.same h.rsp
    ⟨h.rbx.trans (eval_ptr0 _).symm, trivial⟩
  obtain ⟨h0, h1, hsp, hbx, h15, hbp, h12, h13, hw, hov1, hov3⟩ := st3_facts
  refine call_step (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b3 hwf rfl hpc hm0
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ (after b3 st3) st₁.data at hm₁
  have C₁ := Common.block P C hwf hm₁ hw
  have hx : ∀ {r : Reg64} {o : Nat}, (after b3 st3).reg r = some (.ptr 0 o) →
      reg st₁.data r = ad m₀ (fr + o) := fun hr => (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₁ : rspOf st₁.data = ad m₀ (fr + 16) := hx hsp
  have hcur₁ : BytesAt st₁.data.dmem (ad m₀ (fr + 184))
      (wordBytes (UInt64.ofBitVec (ad m₀ (fr + 956)))) := by
    have hc := hm₁.bytesAt_write (r := 0) rfl (by omega) st3_cursor
    change BytesAt st₁.data.dmem (ad m₀ fr + 184#64)
      (regBytes ((Sym.ptr 0 956).eval env)) at hc
    have he : (Sym.ptr 0 956).eval env = ad m₀ (fr + 956) := eval_ptr0 _
    rw [ad_add, he, regBytes_eq_wordBytes] at hc
    exact hc
  have hlen₁ : BytesAt st₁.data.dmem (ad m₀ (fr + 192)) (wordBytes (2400 : Nat).toUInt64) := by
    have hl := hm₁.bytesAt_write (r := 0) rfl (by omega) st3_length
    rw [ad_add] at hl
    rw [← regBytes_eq_wordBytes]
    exact hl
  have hinput₁ := slice_input (hx h1) hcur₁
  have hremaining₁ := slice_length (hx h1) hlen₁ (by decide)
  have hpk₁ : BytesAt st₁.data.dmem (ad m₀ (fr + 40)) (pkB w) := by
    unfold pkB NativeRustc.Xmss.pkBytes
    rw [wordsBytes_map]
    refine bytesAt_flatten 4 (fun _ _ => NativeRustc.length_wordBytes _) fun j hj => ?_
    have hb := hm₁.bytesAt_write (r := 0) (o := 40 + 8 * j) rfl (by omega) (st3_pk j hj)
    change BytesAt st₁.data.dmem (ad m₀ fr + BitVec.ofNat 64 (40 + 8 * j))
      (regBytes ((Sym.reg ([Reg64.rax, .rcx, .rdx, .rsi].getD j .rax)).eval env)) at hb
    have he : (Sym.reg ([Reg64.rax, .rcx, .rdx, .rsi].getD j .rax)).eval env = (w j).toBitVec := by
      interval_cases j
      · exact h.rax
      · exact h.rcx
      · exact h.rdx
      · exact h.rsi
    rw [he, regBytes_eq_wordBytes, ad_add,
      show fr + (40 + 8 * j) = fr + 40 + 8 * j by omega] at hb
    rw [ad_add]
    exact hb
  have hkeep₁ : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5816 →
      firstOverlap 0 o bs.length (after b3 st3).mem = none →
      BytesAt st.data.dmem (ad m₀ (fr + o)) bs → BytesAt st₁.data.dmem (ad m₀ (fr + o)) bs :=
    fun hle hov hb => by
      have hk := hm₁.bytesAt_keep (r := 0) rfl hle hov (by rw [← ad_add] at hb; exact hb)
      rwa [ad_add] at hk
  have hmsg₁ := hkeep₁ (by rw [length_msgB]; omega) (by rw [length_msgB]; exact hov1) hmsg
  have hsig₁ := hkeep₁ (by rw [length_sigB]; omega) (by rw [length_sigB]; exact hov3) hsig
  have hpre₁ : LayerReadPre st₁.data :=
    layerReadPre P C₁ hrsp₁ (o := 3356) (oc := 184) (ob := 956)
      (hx h0) (hx h1) hinput₁ hremaining₁
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by decide)
  refine call_then hpc₁ hread hpre₁ fun st₂ hpc₂ hrsp₂ hpost₂ => ?_
  obtain ⟨hout₂, hcur₂, hlen₂, hsame₂, hs₂⟩ := hpost₂
  simp only [LayerReadPre.bytes, hinput₁, hremaining₁, hx h0, hx h1] at hout₂ hcur₂ hlen₂ hsame₂
  have hsb := bytesOf_slice hsig₁ (c := 4) (n := 1200) (by rw [length_sigB]; omega)
  rw [ad_add] at hsb
  rw [hsb, takeLayer_slice] at hout₂
  rw [ad_add] at hcur₂
  simp only [Nat.add_assoc] at hcur₂
  change SameOutside _ _ (ReadR m₀ st₁.data 3356 184) at hsame₂
  have C₂ := C₁.readR P hs₂ hrsp₁ (by decide) (by decide) hsame₂
  have hk₂ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 3356 → (x + bs.length ≤ 184 ∨ 200 ≤ x) →
      BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hx1 hx2 => keep_readR P hrsp₁ (by decide) (by decide) hsame₂ hb (by omega)
      (by omega) (Or.inl hx1) hx2
  have hpk₂ := hk₂ hpk₁ (by omega) (by rw [length_pkB]; omega) (by rw [length_pkB]; omega)
  have hmsg₂ := hk₂ hmsg₁ (by omega) (by rw [length_msgB]; omega) (by rw [length_msgB]; omega)
  have hsig₂ := hk₂ hsig₁ (by omega) (by simp [length_sigB]) (by simp [length_sigB])
  have hrsp₂' : rspOf st₂.data = ad m₀ (fr + 24) := by rw [hrsp₂, hrsp₁, ad_add]
  let env₃ := Env.ofMachine st₂.data (frameRs m₀) (fun _ => 0)
    (Host.addrOf (k + b4Offset + b4.length)).toBitVec
  have hwf₃ : env₃.WF := frameG_wf P C₂.kept
  have hm₃ : Match env₃ st4 st₂.data := match_stG P C₂.same hrsp₂'
    ⟨(hs₂.1 .rbx rfl).trans ((hx hbx).trans (eval_ptr0 _).symm), trivial⟩
  obtain ⟨g0, g1, gsp, gk, gw⟩ := st4_facts
  refine call_step (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b4 hwf₃ rfl
    (hpc₂.trans rfl) hm₃ fun st₃ hpc₃ hm₃' => ?_
  change Match _ (after b4 st4) st₃.data at hm₃'
  have C₃ := Common.block P C₂ hwf₃ hm₃' gw
  have hy : ∀ {r : Reg64} {o : Nat}, (after b4 st4).reg r = some (.ptr 0 o) →
      reg st₃.data r = ad m₀ (fr + o) := fun hr => (hm₃'.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₃ : rspOf st₃.data = ad m₀ (fr + 16) := hy gsp
  have hk₃ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 5816 → BytesAt st₃.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hle => frame_keep P hwf₃ hm₃' gw hb h24 hle
  have hcur₃ := hk₃ (x := 184) hcur₂ (by omega) (by rw [NativeRustc.length_wordBytes]; omega)
  have hlen₃ := hk₃ (x := 192) (by simpa [ad_add] using hlen₂) (by omega)
    (by rw [NativeRustc.length_wordBytes]; omega)
  have hsig₃ := hk₃ (x := 952) hsig₂ (by omega) (by rw [length_sigB]; omega)
  have hinput₃ := slice_input (oc := 184) (ob := 2156) (hy g1) hcur₃
  have hremaining₃ := slice_length (oc := 184) (n := 1200) (hy g1) hlen₃ (by decide)
  have hpre₃ : LayerReadPre st₃.data :=
    layerReadPre P C₃ hrsp₃ (o := 4556) (oc := 184) (ob := 2156)
      (hy g0) (hy g1) hinput₃ hremaining₃
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by decide)
  refine call_then hpc₃ hread hpre₃ fun st₄ hpc₄ hrsp₄ hpost₄ => cont st₄ (hpc₄.trans rfl) ?_
  obtain ⟨hout₄, -, -, hsame₄, hs₄⟩ := hpost₄
  simp only [LayerReadPre.bytes, hinput₃, hy g0, hy g1] at hout₄ hsame₄
  have hsb₃ := bytesOf_slice hsig₃ (c := 1204) (n := 1200) (by rw [length_sigB])
  rw [ad_add] at hsb₃
  rw [hsb₃, takeLayer_slice] at hout₄
  change SameOutside _ _ (ReadR m₀ st₃.data 4556 184) at hsame₄
  have C₄ := C₃.readR P hs₄ hrsp₃ (by decide) (by decide) hsame₄
  have hk₄ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 4556 → (x + bs.length ≤ 184 ∨ 200 ≤ x) →
      BytesAt st₄.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hx1 hx2 => keep_readR P hrsp₃ (by decide) (by decide) hsame₄
      (hk₃ hb h24 (by omega)) (by omega) (by omega) (Or.inl hx1) hx2
  have hreg : ∀ r ∈ [Reg64.rbp, .r12, .r13, .r15], reg st₄.data r = reg st₂.data r := by
    intro r hr
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have hcs : calleeSaved r = true := by rcases hr' with rfl | rfl | rfl | rfl <;> rfl
    exact (hs₄.1 r hcs).trans (hm₃'.regs _ _ (gk r hr))
  refine ⟨C₄, ?_, ?_, ?_, ?_,
    hk₄ hpk₂ (by omega) (by rw [length_pkB]; omega) (by rw [length_pkB]; omega),
    hk₄ hmsg₂ (by omega) (by rw [length_msgB]; omega) (by rw [length_msgB]; omega), ?_,
    hk₄ hout₂ (by omega) (by rw [bottomL, length_memBytes (by rw [length_sigB]; omega)])
      (by rw [bottomL, length_memBytes (by rw [length_sigB]; omega)]; omega), hout₄⟩
  · rw [hrsp₄, hrsp₃, ad_add]
  · exact (hreg .r15 (by simp)).trans ((hs₂.1 .r15 rfl).trans (hx h15))
  · exact (hreg .r12 (by simp)).trans ((hs₂.1 .r12 rfl).trans (hx h12))
  · exact (hreg .r13 (by simp)).trans ((hs₂.1 .r13 rfl).trans ((hm₁.regs _ _ h13).trans h.r13))
  · exact (hreg .rbp (by simp)).trans ((hs₂.1 .rbp rfl).trans ((hm₁.regs _ _ hbp).trans h.rbp))

end

end NativeRustcX64.Xmss.XmssVerify
