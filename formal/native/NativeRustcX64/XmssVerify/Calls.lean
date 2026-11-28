module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.XmssVerify.Head

/-!
# `xmss_verify`: calls on the frame (x86-64)

The calls from RSP at the frame's offset `24` (the callee's entry RSP `16`) of `memset`,
`memcpy`, `Hasher::update` and `Hasher::finalize` on the frame's bytes (`memsetCall`,
`memcpyCall`, `updateCall`, `finalizeCall`): their preconditions from frame offsets
(`updatePre`, `finalizePre`), their postconditions in those terms, back at RSP `24`.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc

/-- `S` keeps `S₀`'s known callee-saved registers but `X`. -/
@[expose] public def keepsBut (X : Reg64) (S₀ S : SState) : Bool :=
  allRegs.all (fun r => !calleeSaved r || r == X || ((S₀.reg r).isSome && S.reg r == S₀.reg r))

/-- The callee-saved registers but `X` are kept. -/
@[expose] public def SavedBut (X : Reg64) (m m' : MachineData) : Prop :=
  ∀ r, calleeSaved r = true → r ≠ X → reg m' r = reg m r

public section

theorem Saved.savedBut {X : Reg64} {m m' : MachineData} (h : Saved m m') : SavedBut X m m' :=
  fun r hr _ => h.1 r hr

theorem SavedBut.trans {X : Reg64} {m₁ m₂ m₃ : MachineData} (h₁ : SavedBut X m₁ m₂)
    (h₂ : SavedBut X m₂ m₃) : SavedBut X m₁ m₃ :=
  fun r hr hx => (h₂ r hr hx).trans (h₁ r hr hx)

theorem Match.savedBut [Labels] {env : Env} {S S₀ : SState} {m₀ m : MachineData} {X : Reg64}
    (hm₀ : Match env S₀ m₀) (hm : Match env S m) (h : keepsBut X S₀ S = true) :
    SavedBut X m₀ m := by
  intro r hr hx
  simp only [keepsBut, List.all_eq_true] at h
  have := h r (mem_allRegs r)
  simp only [hr, Bool.not_true, Bool.false_or, Bool.or_eq_true] at this
  rcases this with h1 | h2
  · exact absurd (Reg64.eq_of_beq h1) hx
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h2
  obtain ⟨⟨v, hv⟩, hS⟩ := h2
  exact Match.reg_eq hm₀ hm hv (hS.trans hv)

end

public section

variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

omit [Labels] in
theorem rsp_ret {m m' : MachineData} (hrsp : rspOf m = ad m₀ (fr + 16))
    (h : rspOf m' = rspOf m + 8#64) : rspOf m' = ad m₀ (fr + 24) := by
  rw [h, hrsp, ad_add]

theorem updatePre (P : Pre w m₀) (C : Common m₀ m) (hrsp : rspOf m = ad m₀ (fr + 16))
    {h d n : Nat} (h0 : reg m .rdi = ad m₀ (fr + h)) (h1 : reg m .rsi = ad m₀ (fr + d))
    (h2 : (reg m .rdx).toNat = n) (hh : 24 ≤ h) (hhr : h + 344 ≤ 5816) (hd : 24 ≤ d)
    (hdr : d + n ≤ 5816) (hdis : h + 344 ≤ d ∨ d + n ≤ h) (hn : 0 < n)
    (ha : ∃ a, Keccak.HasherHolds (bytesOf m.dmem (ad m₀ (fr + h)) 344) a) : UpdatePre m := by
  unfold UpdatePre
  rw [h0, h1, h2]
  refine ⟨stackOk_at P C hrsp (by decide) (by decide), rcAt_at P C hrsp (by decide) (by decide),
    ha, C.mapped P (by fro), P.ad_nw (by fro), C.mapped P (by fro), P.ad_nw (by fro),
    P.apart_ad (by omega) (by fro) (by fro) (by decide) hn,
    apart_at P hrsp (by decide) (by fro) (by fro) (by fro) (by decide),
    apart_at P hrsp (by decide) (by fro) (by fro) (by fro) hn,
    (P.rc_apart (by fro) (by decide)).symm, ?_⟩
  apply gotAt_at P C hrsp (by decide) (by decide) (by decide)
  intro l hl a ha
  have hl' : l ∈ ["memcpy", "memset"] := by
    simp only [List.mem_singleton] at hl
    simp [hl]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact got_apart P hl' (by fro) (by dsimp; decide)
  · exact got_apart P hl' (by fro) hn

theorem finalizePre (P : Pre w m₀) (C : Common m₀ m) (hrsp : rspOf m = ad m₀ (fr + 16))
    {o h : Nat} (h0 : reg m .rdi = ad m₀ (fr + o)) (h1 : reg m .rsi = ad m₀ (fr + h))
    (ho : 24 ≤ o) (hor : o + 32 ≤ 5816) (hh : 24 ≤ h) (hhr : h + 344 ≤ 5816)
    (hdis : o + 32 ≤ h ∨ h + 344 ≤ o)
    (ha : ∃ a, Keccak.HasherHolds (bytesOf m.dmem (ad m₀ (fr + h)) 344) a) : FinalizePre m := by
  unfold FinalizePre
  rw [h0, h1]
  refine ⟨stackOk_at P C hrsp (by decide) (by decide), rcAt_at P C hrsp (by decide) (by decide),
    ha, C.mapped P (by fro), P.ad_nw (by fro), C.mapped P (by fro), P.ad_nw (by fro),
    P.apart_ad (by omega) (by fro) (by fro) (by decide) (by decide),
    apart_at P hrsp (by decide) (by fro) (by fro) (by fro) (by decide),
    apart_at P hrsp (by decide) (by fro) (by fro) (by fro) (by decide),
    (P.rc_apart (by fro) (by decide)).symm, ?_⟩
  apply gotAt_at P C hrsp (by decide) (by decide) (by decide)
  intro l hl a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact got_apart P hl (by fro) (by dsimp; decide)
  · exact got_apart P hl (by fro) (by dsimp; decide)

end

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **A block from RSP `24` ending in a call** that writes only its return address: at the
callee's entry RSP `16`, `Common`, the callee-saved registers but `X` kept, the frame's bytes from `24`
kept, the registers the block's symbolic state says. -/
theorem callBlock (P : Pre w m₀) {X : Reg64} {ds : List Directive} {j : Nat}
    {known : List (Reg64 × Sym)} {S' : SState} {l : Label} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds (stF known) = some (S', .call l))
    (hf : writesBelow S' [(0, 24)] = true ∧ keepsBut X (stF known) S' = true ∧
      S'.reg .rsp = some (.ptr 0 16))
    {st : MachineState} (hpc : st.pc = Host.addrOf j) (C : Common m₀ st.data)
    (hrsp : rspOf st.data = ad m₀ (fr + 24))
    (hknown : AllOf (fun p => reg st.data p.1 = p.2.eval (Env.ofMachine st.data (frameRs m₀)
      (fun _ => 0) (Host.addrOf (j + ds.length)).toBitVec)) known) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, PcOk (Env.ofMachine st.data (frameRs m₀) (fun _ => 0)
        (Host.addrOf (j + ds.length)).toBitVec) (.call l) (Host.addrOf (j + ds.length)) st' →
      rspOf st'.data = ad m₀ (fr + 16) → Common m₀ st'.data → SavedBut X st.data st'.data →
      (∀ {x : Nat} {bs : List UInt8}, 24 ≤ x → x + bs.length ≤ 5816 →
        BytesAt st.data.dmem (ad m₀ (fr + x)) bs → BytesAt st'.data.dmem (ad m₀ (fr + x)) bs) →
      (∀ r v, S'.reg r = some v → reg st'.data r = v.eval (Env.ofMachine st.data (frameRs m₀)
        (fun _ => 0) (Host.addrOf (j + ds.length)).toBitVec)) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨hw, hkeep, hsp⟩ := hf
  have hwf := frameG_wf P C.kept (vs := fun _ => 0)
    (ret := (Host.addrOf (j + ds.length)).toBitVec)
  have hm : Match (Env.ofMachine st.data (frameRs m₀) (fun _ => 0)
      (Host.addrOf (j + ds.length)).toBitVec) (stF known) st.data :=
    match_stG P C.same hrsp hknown
  refine call_step hk hx hwf rfl hpc hm fun st' hpc' hm' => ?_
  simp only [hx, Option.getD_some] at hm'
  exact cont st' hpc' ((hm'.regs _ _ hsp).trans (eval_ptr0 16)) (Common.block P C hwf hm' hw)
    (Match.savedBut hm hm' hkeep) (fun hx hle hb => frame_keep P hwf hm' hw hb hx hle)
    fun r v h => hm'.regs r v h

/-- **`memset`** of `n` bytes at the frame offset `dst`. -/
theorem memsetCall (hset : Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost) (P : Pre w m₀)
    {env : Env} {st : MachineState} {next : Int64} (hpc : PcOk env (.call NativeRustcX64.Common.Memset.entryLabel) next st)
    (C : Common m₀ st.data) (hrsp : rspOf st.data = ad m₀ (fr + 16)) {dst n : Nat}
    (h0 : reg st.data .rdi = ad m₀ (fr + dst)) (h2 : (reg st.data .rdx).toNat = n)
    (hd : 24 ≤ dst) (hdr : dst + n ≤ 5760) (hn : 0 < n) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → rspOf st'.data = ad m₀ (fr + 24) →
      Common m₀ st'.data → Saved st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fr + dst))
        (List.replicate n (UInt8.ofNat (reg st.data .rsi).toNat)) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := memsetPre P C (o := fr + dst) hrsp (by decide) h0 h2 (by omega) (by fro) hn
  refine call_then hpc hset pre fun st' hpc' hrsp' post => ?_
  obtain ⟨-, hb, hsame, hs⟩ := post
  rw [h0, h2] at hb hsame
  have hsame' : SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) :=
    hsame.mono fun p hp => Or.inl hp
  exact cont st' hpc' (rsp_ret hrsp hrsp')
    (C.callR P hs hrsp (by decide) (by decide) hdr hsame') hs hb hsame'

/-- **`memcpy`** of `n` bytes from the frame offset `src` to `dst`. -/
theorem memcpyCall (hcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) (P : Pre w m₀)
    {env : Env} {st : MachineState} {next : Int64} (hpc : PcOk env (.call NativeRustcX64.Common.Memcpy.entryLabel) next st)
    (C : Common m₀ st.data) (hrsp : rspOf st.data = ad m₀ (fr + 16)) {dst src n : Nat}
    (h0 : reg st.data .rdi = ad m₀ (fr + dst)) (h1 : reg st.data .rsi = ad m₀ (fr + src))
    (h2 : (reg st.data .rdx).toNat = n) (hd : 24 ≤ dst) (hdr : dst + n ≤ 5760)
    (hsr : src + n ≤ 5816) (hdis : dst + n ≤ src ∨ src + n ≤ dst) (hn : 0 < n)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → rspOf st'.data = ad m₀ (fr + 24) →
      Common m₀ st'.data → Saved st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fr + dst)) (bytesOf st.data.dmem (ad m₀ (fr + src)) n) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := memcpyPre P C (o := fr + dst) (o' := fr + src) hrsp (by decide) h0 h1 h2
    (by omega) (by fro) (by fro) (by omega) hn
  refine call_then hpc hcpy pre fun st' hpc' hrsp' post => ?_
  obtain ⟨-, hb, hsame, hs⟩ := post
  rw [h0, h1, h2] at hb
  rw [h0, h2] at hsame
  have hsame' : SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) :=
    hsame.mono fun p hp => Or.inl hp
  exact cont st' hpc' (rsp_ret hrsp hrsp')
    (C.callR P hs hrsp (by decide) (by decide) hdr hsame') hs hb hsame'

/-- **`Hasher::update`** of the hasher at the frame offset `h` with the bytes `data` at `d`. -/
theorem updateCall (hupd : Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost) (P : Pre w m₀)
    {env : Env} {st : MachineState} {next : Int64} (hpc : PcOk env (.call NativeRustcX64.Common.Update.entryLabel) next st)
    (C : Common m₀ st.data) (hrsp : rspOf st.data = ad m₀ (fr + 16)) {h d : Nat}
    {a data : List UInt8} (h0 : reg st.data .rdi = ad m₀ (fr + h))
    (h1 : reg st.data .rsi = ad m₀ (fr + d)) (h2 : (reg st.data .rdx).toNat = data.length)
    (hh : Keccak.HasherHolds (bytesOf st.data.dmem (ad m₀ (fr + h)) 344) a)
    (hdat : BytesAt st.data.dmem (ad m₀ (fr + d)) data) (hhl : 24 ≤ h) (hhr : h + 344 ≤ 5760)
    (hdl : 24 ≤ d) (hdr : d + data.length ≤ 5816)
    (hdis : h + 344 ≤ d ∨ d + data.length ≤ h) (hn : 0 < data.length) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → rspOf st'.data = ad m₀ (fr + 24) →
      Common m₀ st'.data → Saved st.data st'.data →
      Keccak.HasherHolds (bytesOf st'.data.dmem (ad m₀ (fr + h)) 344) (a ++ data) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data h 344 updateStack) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := updatePre P C hrsp h0 h1 h2 hhl (by omega) hdl hdr hdis hn ⟨a, hh⟩
  refine call_then hpc hupd pre fun st' hpc' hrsp' post => ?_
  obtain ⟨-, hh', hsame, hs⟩ := post
  rw [h0, h1, h2] at hh'
  rw [h0] at hsame
  have := hh' a hh
  rw [hdat.bytesOf] at this
  exact cont st' hpc' (rsp_ret hrsp hrsp')
    (C.callR P hs hrsp (by decide) (by decide) hhr hsame) hs this hsame

/-- **`Hasher::finalize`** of the hasher at the frame offset `h` to the 32 bytes at `o`. -/
theorem finalizeCall (hfin : Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost)
    (P : Pre w m₀) {env : Env} {st : MachineState} {next : Int64}
    (hpc : PcOk env (.call NativeRustcX64.Common.Finalize.entryLabel) next st) (C : Common m₀ st.data)
    (hrsp : rspOf st.data = ad m₀ (fr + 16)) {o h : Nat} {a : List UInt8}
    (h0 : reg st.data .rdi = ad m₀ (fr + o)) (h1 : reg st.data .rsi = ad m₀ (fr + h))
    (hh : Keccak.HasherHolds (bytesOf st.data.dmem (ad m₀ (fr + h)) 344) a) (hol : 24 ≤ o)
    (hor : o + 32 ≤ 5760) (hhl : 24 ≤ h) (hhr : h + 344 ≤ 5816)
    (hdis : o + 32 ≤ h ∨ h + 344 ≤ o) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → rspOf st'.data = ad m₀ (fr + 24) →
      Common m₀ st'.data → Saved st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fr + o)) (Keccak.hashBytes a) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data o 32 finalizeStack) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := finalizePre P C hrsp h0 h1 hol (by omega) hhl hhr hdis ⟨a, hh⟩
  refine call_then hpc hfin pre fun st' hpc' hrsp' post => ?_
  obtain ⟨hb, hsame, hs⟩ := post
  rw [h0, h1, Keccak.finalize_eq hh] at hb
  rw [h0] at hsame
  exact cont st' hpc' (rsp_ret hrsp hrsp')
    (C.callR P hs hrsp (by decide) (by decide) hor hsame) hs hb hsame

end

end NativeRustcX64.Xmss.XmssVerify
