module

public import NativeRustcX64.Code.Common.Memset.Names

public import NativeRustcX64.XmssVerify.Head

/-!
# `xmss_verify`: from the entry to the loop copying the signature's words (x86-64)

`head`: blocks 0 and 1 and the `memset` between them (`NativeRustcX64.XmssVerify.Head`), to
`LoopAt` before the loop's first turn.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

theorem match_st0 (P : Pre w m₀) {ret : BitVec 64} :
    Match (Env.ofMachine m₀ (frameRs m₀) (fun _ => 0) ret) st0 m₀ :=
  match_stG P (fun _ _ => rfl) (sp_eq m₀).symm trivial

/-- `Common` after block 0. -/
theorem common_b0 (P : Pre w m₀) {m : MachineData} {ret : BitVec 64}
    (hm : Match (Env.ofMachine m₀ (frameRs m₀) (fun _ => 0) ret) (after b0 st0) m) : Common m₀ m := by
  have hwf := frameG_wf P (Kept.refl m₀.dmem) (m := m₀) (vs := fun _ => 0) (ret := ret)
  obtain ⟨-, -, -, -, -, -, hw⟩ := st0'_facts
  refine ⟨fun j hj => ?_, ?_, hm.kept hwf⟩
  · have := hm.bytesAt_write (r := 0) rfl (by omega) (st0'_save j hj)
    rw [show fr + 5760 + 8 * j = fr + (5760 + 8 * j) by omega, ← ad_add]
    exact this
  · refine (hm.sameOutside_below hwf hw).mono fun p ⟨rb, hrb, b, sz, hb, hin⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
    subst hrb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact P.inRange_lo (by fro) hin

set_option linter.unusedSimpArgs false in
/-- **The prologue**: from the entry to the loop copying the signature's words. -/
public theorem head {k : Nat} (hp : Placed code k)
    (hmemset : Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost) (P : Pre w m₀)
    {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b2Offset) → LoopAt w m₀ st.data 0 →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m₀, Host.addrOf k⟩ := by
  have hwf := frameG_wf P (Kept.refl m₀.dmem) (m := m₀) (vs := fun _ => 0)
    (ret := (Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b1Offset)).toBitVec)
  refine call_step (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b0 hwf rfl
    (by rw [NativeRustcX64.Xmss.XmssVerify.b0Offset, Nat.add_zero]) (match_st0 P) fun st₁ hpc₁ hm₁ => ?_
  change Match _ (after b0 st0) st₁.data at hm₁
  have C₁ := common_b0 P hm₁
  obtain ⟨h0, h2, hsp, h14, h15, hbx, -⟩ := st0'_facts
  have hrsp₁ : rspOf st₁.data = ad m₀ (fr + 16) :=
    (hm₁.regs .rsp _ hsp).trans (ad_int m₀ 16)
  have hx0 : reg st₁.data .rdi = ad m₀ (fr + 956) :=
    (hm₁.regs .rdi _ h0).trans (ad_int m₀ 956)
  have hx2 : (reg st₁.data .rdx).toNat = 2400 := by
    rw [show reg st₁.data .rdx = _ from hm₁.regs .rdx _ h2]
    rfl
  refine call_then hpc₁ hmemset (memsetPre P C₁ hrsp₁ (by omega) hx0 hx2 (by omega) (by fro)
    (by omega)) fun st₂ hpc₂ hrsp₂ hpost => ?_
  obtain ⟨-, -, hsame, hs⟩ := hpost
  rw [hx0, hx2] at hsame
  have C₂ : Common m₀ st₂.data := C₁.call hs hsame (fun p hp => P.inRange_lo (by fro) hp)
    fun x hx hx' => P.not_inRange_ad (by fro) (by fro) (by omega)
  have hrsp₂ : rspOf st₂.data = ad m₀ (fr + 24) := by
    rw [hrsp₂, hrsp₁, ad_add]
  have h14₂ : reg st₂.data .r14 = reg m₀ .rdi :=
    (hs.1 .r14 rfl).trans (hm₁.regs .r14 _ h14)
  have h15₂ : reg st₂.data .r15 = 0#64 := (hs.1 .r15 rfl).trans (hm₁.regs .r15 _ h15)
  have hbx₂ : reg st₂.data .rbx = ad m₀ (fr + 956) :=
    (hs.1 .rbx rfl).trans ((hm₁.regs .rbx _ hbx).trans (ad_int m₀ 956))
  have hwf₂ := in_wf P C₂.kept (m := st₂.data) (vs := fun _ => 0) (ret := 0)
  have hm₂ : Match (Env.ofMachine st₂.data (inR m₀) (fun _ => 0) 0) st1 st₂.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hrsp₂.trans (ad_int m₀ 24).symm, h14₂.trans (inp_eq m₀).symm, trivial⟩
      trivial trivial trivial
  refine fall_step (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b1 hwf₂
    (hpc₂.trans rfl) hm₂ fun st₃ hpc₃ hm₃ => cont st₃ (hpc₃.trans rfl) ?_
  change Match _ (after b1 st1) st₃.data at hm₃
  obtain ⟨hax, hcx, hdx, hsi, h13, hsp₃, h14₃, h15₃, hbx₃, hw⟩ := st1'_facts
  have hword : ∀ {r : Reg64} {i : Nat}, i < 309 → (after b1 st1).reg r = some (.load 1 (8 * i) 8) →
      reg st₃.data r = (w i).toBitVec := fun hi h =>
    (hm₃.regs _ _ h).trans (load_word P C₂.same hi rfl)
  have h13' := hword (i := 8) (by omega) h13
  refine ⟨Common.block P C₂ hwf₂ hm₃ hw, (hm₃.regs .rsp _ hsp₃).trans (ad_int m₀ 24),
    (hm₃.regs .r14 _ h14₃).trans (inp_eq m₀), (hm₃.regs .r15 _ h15₃).trans h15₂,
    hword (i := 0) (by omega) hax, hword (i := 1) (by omega) hcx, hword (i := 2) (by omega) hdx,
    hword (i := 3) (by omega) hsi, h13', (hm₃.regs .rbx _ hbx₃).trans hbx₂,
    fun k hk => ?_, ?_, ?_, fun k hk => absurd hk (by omega)⟩
  · have := copy_word P hm₃ (rd := 0) (od := 152 + 8 * k) rfl (by omega) (i := 4 + k) (by omega)
      (rs := 1) (os := 8 * (4 + k)) (fun t _ => rfl) C₂.same
      (st1'_msg k hk)
    rw [ad_add] at this
    rwa [show fr + 152 + 8 * k = fr + (152 + 8 * k) by omega]
  · have hv : (Sym.un .trunc .W32 (.load 1 64 8)).eval (Env.ofMachine st₂.data (inR m₀)
        (fun _ => 0) 0) = u32W (w 8) := by
      simp only [Sym.eval, UnOp.apply, ext, low]
      rw [load_word (env := Env.ofMachine st₂.data (inR m₀) (fun _ => 0) 0) P C₂.same (i := 8) (by omega) (by simp only [Nat.reduceMul]; rfl)]
      rfl
    exact (hm₃.regs .rbp _ st1'_rbp).trans hv
  · intro t ht
    simp only [List.length_take, NativeRustc.length_wordBytes] at ht
    rw [ad_add, show fr + 952 + t = fr + (952 + t) by omega, ← ad_add,
      hm₃.mem 0 _ 5816 rfl _ (by omega)]
    unfold memByte
    rw [st1'_li t (by omega)]
    simp only [Sym.eval, UnOp.apply, ext, low]
    rw [load_word (env := Env.ofMachine st₂.data (inR m₀) (fun _ => 0) 0) P C₂.same (i := 8) (by omega) (by simp only [Nat.reduceMul]; rfl)]
    rw [byteOf_u32 _ (by omega), List.getElem_take]
    simp [List.getD_eq_getElem?_getD, show t < (wordBytes (w 8)).length by
      rw [NativeRustc.length_wordBytes]; omega]

end NativeRustcX64.Xmss.XmssVerify
