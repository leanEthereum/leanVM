module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.Code.Xmss.LayerRead

/-! # Moving the chain values out of the path buffer -/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public def stM : SState :=
  (init [1944, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot "memcpy", 1, 0)]).withKnownBytes
    1 0 8 (.label "memcpy")
sym_block b5_execM := exec b5 stM
@[expose] public def stM1 : SState := ((exec b5 stM).getD (stM, .fall)).1

theorem stM1_regs : stM1.reg .rdi = some (.ptr 0 960) ∧
    stM1.reg .rsi = some (.reg .rsi) ∧ stM1.reg .rdx = some (.lit 928) ∧
    stM1.reg .rsp = some (.ptr 0 0) ∧
    (∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbp, .rbx], stM1.reg r = some (.reg r)) ∧
    writesBelow stM1 [(0, 24)] = true := by decide +kernel
theorem stM1_input : ∀ t < 8, findWrite 0 (16 + t) stM1.mem = some (.reg .r11, t) := by
  decide +kernel

theorem chainBytes_at {m₀ m : MachineData} (P : Pre m₀)
    (h : ∀ j < 58, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (32 + 16 * j)) (chainSlot m₀ j)) :
    BytesAt m.dmem (base m₀ + 32#64) (chainBytes m₀) :=
  bytesAt_flatten 58 (fun j hj => P.chainSlot_length hj)
    fun j hj => by rw [addr_add_addr]; exact h j hj

public theorem length_chainBytes {m₀ : MachineData} (P : Pre m₀) :
    (chainBytes m₀).length = 928 := by
  unfold chainBytes
  rw [List.length_flatten, List.map_map]
  have : ∀ n ≤ 58, ((List.range n).map (List.length ∘ chainSlot m₀)).sum = 16 * n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp [P.chainSlot_length (j := n) (by omega)]
      omega
  exact this 58 le_rfl

theorem Pre.not_stack {m₀ : MachineData} (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1944)
    (hx : x < o ∨ o + s ≤ x) (hx' : x < 1944) :
    ¬InRange (base m₀ + BitVec.ofNat 64 o) s (base m₀ + BitVec.ofNat 64 x) := by
  rw [inRange_offsets P.baseNW hs hx']
  omega

public theorem mid [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m₀ : MachineData} (P : Pre m₀) (G : ParserGot m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + b5Offset)) (h : LoopDone m₀ st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + b6Offset) → MidAt m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hB := P.baseNW
  unfold NoWrap at hB
  let env := Env.ofMachine st.data [(base m₀, 1944), (gotAddr "memcpy", 8)]
    (fun _ => 0) (Host.addrOf (k + b6Offset)).toBitVec
  have hg := G.1 "memcpy" (by simp)
  have hwf : env.WF := Env.wf_of
    ⟨⟨P.stackMapped.kept C.kept, P.baseNW⟩,
      ⟨(G.mapped (by simp)).kept C.kept, hg.2.1⟩, trivial⟩
    (List.pairwise_pair.mpr hg.2.2.1.symm)
  have hm : Match env stM st.data := by
    apply Match.withKnownBytes
    · apply match_ofMachine
      · exact ⟨rfl, rfl, trivial⟩
      · exact ⟨C.rsp.trans (by simp [Sym.eval]), trivial⟩
      · exact trivial
      · exact trivial
      · exact ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simpa [Sym.eval, Env.base, env] using P.got_byte G (C.same.mono fun _ => Or.inl) hi
  obtain ⟨hdi, hsi, hdx, hsp, hregs, hwrites⟩ := stM1_regs
  refine call_step (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) b5_execM hwf rfl hpc hm
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ stM1 st₁.data at hm₁
  have hsame₁ : SameOutside st.data.dmem st₁.data.dmem (InRange (base m₀) 24) :=
    (hm₁.sameOutside_below hwf hwrites).mono fun p ⟨rb, hrb, b, sz, hb, hin⟩ => by
      simp only [List.mem_singleton] at hrb
      subst rb
      cases hb
      exact hin
  have hrdi : reg st₁.data .rdi = base m₀ + 960#64 :=
    (hm₁.regs .rdi _ hdi).trans (by simp [Sym.eval, env])
  have hrsi : reg st₁.data .rsi = base m₀ + 32#64 := (hm₁.regs .rsi _ hsi).trans h.rsi
  have hrdx : (reg st₁.data .rdx).toNat = 928 := by
    change (st₁.data.regs.get64 .rdx).toNat = 928
    rw [hm₁.regs .rdx _ hdx]
    rfl
  have hrsp : rspOf st₁.data = base m₀ := (hm₁.regs .rsp _ hsp).trans (by simp [Sym.eval, env])
  have hk₁ : Kept m₀.dmem st₁.data.dmem := C.kept.trans (hm₁.kept hwf)
  have hpre : MemcpyPre st₁.data := by
    refine ⟨⟨by omega, by rw [hrsp]; omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hrdi, hrsi, hrdx, hrsp]
    · rw [BitVec.sub_zero]
      simpa using (P.stackMapped.sub (i := 0) (k := 8) (by omega)).kept hk₁
    · exact (P.stackMapped.sub (by omega)).kept hk₁
    · exact (P.stackMapped.sub (by omega)).kept hk₁
    · exact P.baseNW.sub (by omega)
    · exact P.baseNW.sub (by omega)
    · exact apart_offsets P.baseNW (by omega) (by omega) (by omega) (by omega) (by omega)
    · simpa using apart_offsets (o := 960) (s := 928) (o' := 0) (s' := 8) P.baseNW
        (by omega) (by omega) (by omega) (by omega) (by omega)
  refine call_then hpc₁ hmemcpy hpre fun st₂ hpc₂ hrsp₂ hpost => cont st₂ hpc₂ ?_
  obtain ⟨-, hcopy, hsame, hs₂⟩ := hpost
  simp only [hrdi, hrsi, hrdx] at hcopy hsame
  have hstk : ∀ x, (24 ≤ x ∧ x < 960 ∨ 1888 ≤ x) → x < 1944 →
      ¬(InRange (base m₀) 24 (base m₀ + BitVec.ofNat 64 x) ∨
        InRange (base m₀ + 960#64) 928 (base m₀ + BitVec.ofNat 64 x)) := by
    intro x hx hx'
    rintro (h' | h')
    · have hn := P.not_stack (o := 0) (s := 24) (x := x) (by omega) (by omega) hx'
      simp only [BitVec.add_zero] at hn
      exact hn h'
    · exact P.not_stack (by omega) (by omega) hx' h'
  have hsame' := hsame₁.trans hsame
  have hk₂ : Kept st.data.dmem st₂.data.dmem := (hm₁.kept hwf).trans hs₂.2
  have hkeep : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbp, .rbx],
      reg st₂.data r = reg st.data r := by
    intro r hr
    have hcs : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    exact (hs₂.1 r hcs).trans (hm₁.regs r _ (hregs r hr))
  refine ⟨C.transfer hk₂
      (by rw [show reg st₂.data .rsp = rspOf st₂.data from rfl, hrsp₂, hrsp]) hsame'
      (fun p hp => hp.elim (fun h => P.stack_scratch (o := 0) (s := 24) (by omega)
        (by simpa using h)) (P.stack_scratch (by omega)))
      (fun j hj t ht => by rw [addr_add_addr]; exact hstk _ (by omega) (by omega))
      (fun t ht => by rw [addr_add_addr]; exact hstk _ (by omega) (by omega)),
    (hkeep .r14 (by simp)).trans h.r14, (hkeep .r12 (by simp)).trans h.r12,
    (hkeep .r13 (by simp)).trans h.r13, (hkeep .r15 (by simp)).trans h.r15,
    (hkeep .rbx (by simp)).trans h.rbx, (hkeep .rbp (by simp)).trans h.rbp, ?_, ?_⟩
  · have hin := hm₁.bytesAt_write (r := 0) rfl (by omega) stM1_input
    change BytesAt st₁.data.dmem (base m₀ + 16#64) (regBytes (reg st.data .r11)) at hin
    rw [h.r11] at hin
    exact hin.sameOutside hsame fun t ht => by
      rw [length_regBytes] at ht
      rw [addr_add_addr]
      exact P.not_stack (by omega) (by omega) (by omega)
  · have hch := chainBytes_at P h.chain
    have hch₁ := hch.sameOutside hsame₁ fun t ht => by
      rw [length_chainBytes P] at ht
      rw [addr_add_addr]
      simpa using P.not_stack (o := 0) (s := 24) (x := 32 + t)
        (by omega) (by omega) (by omega)
    have := hch₁.bytesOf
    rw [length_chainBytes P] at this
    rwa [this] at hcopy

end NativeRustcX64.Xmss.LayerRead
