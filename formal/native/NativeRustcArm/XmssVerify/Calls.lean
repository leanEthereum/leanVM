module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Common.Update.Names
public import NativeRustcArm.Code.Xmss.LayerRead.Names
public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.XmssVerify.Frame
public import NativeRustcArm.XmssVerify.Callee

/-!
# `xmss_verify`: calls on the frame

The callees' contracts `xmss_verify` uses (`Callees`). A block that only sets a call's arguments
(`callBlock`: no write, the callee-saved registers and SP kept). What a callee with an output in
the frame and a stack below it may change (`CallR`), the frame's bytes it keeps (`keep_callR`) and
`Common` after it (`Common.callR`). The calls of `memset`, `memcpy`, `Hasher::update` and
`Hasher::finalize` on the frame's bytes (`memsetCall`, `memcpyCall`, `updateCall`,
`finalizeCall`): their preconditions from frame offsets, their postconditions in those terms.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc

@[expose] public section




/-- The contracts of `xmss_verify`'s callees. -/
structure Callees [Host] : Prop where
  memset : Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost
  memcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost
  update : Spec (label NativeRustcArm.Common.Update.entryLabel) UpdatePre UpdatePost
  finalize : Spec (label NativeRustcArm.Common.Finalize.entryLabel) FinalizePre FinalizePost
  wots : Spec (label NativeRustcArm.Xmss.WotsLeaf.entryLabel) WotsLeafPre WotsLeafPost
  layerRead : Spec (label NativeRustcArm.Xmss.LayerRead.entryLabel) LayerReadPre LayerReadPost

/-- What a callee with `n` bytes of output at frame offset `a` and `s` bytes of stack may
change. -/
def CallR (m₀ m : MachineData) (a n s : Nat) (p : BitVec 64) : Prop :=
  InRange (ad m₀ (fb + a)) n p ∨ InRange (stackBelow m s) s p

end

public section

variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

theorem not_callR (P : Pre w m₀) (C : Common m₀ m) {a n s x : Nat} (hs : s ≤ fb)
    (ha : a + n ≤ 5872) (hx : x < 5872) (h : x < a ∨ a + n ≤ x) :
    ¬CallR m₀ m a n s (ad m₀ (fb + x)) := by
  rintro (hp | hp)
  · exact P.not_inRange_ad (by fbo) (by fbo) (by omega) hp
  · exact not_inRange_stack P C hs (by omega) (by fbo) hp

/-- **The frame's bytes a call keeps**: those apart from its output. -/
theorem keep_callR (P : Pre w m₀) (C : Common m₀ m) {d d' : DataMem} {a n s : Nat}
    (hs : s ≤ fb) (ha : a + n ≤ 5872) (hsame : SameOutside d d' (CallR m₀ m a n s)) {o : Nat}
    {bs : List UInt8} (h : BytesAt d (ad m₀ (fb + o)) bs) (ho : o + bs.length ≤ 5872)
    (hd : o + bs.length ≤ a ∨ a + n ≤ o) : BytesAt d' (ad m₀ (fb + o)) bs :=
  keep_ad hsame h fun t ht => by
    rw [Nat.add_assoc]
    exact not_callR P C hs ha (by omega) (by omega)

/-- **`Common` after a call** with its output in the frame below the save area. -/
theorem Common.callR (P : Pre w m₀) (C : Common m₀ m) {m' : MachineData} (hs : Saved m m')
    {a n s : Nat} (hsf : s ≤ fb) (ha : a + n ≤ 5776)
    (hsame : SameOutside m.dmem m'.dmem (CallR m₀ m a n s)) : Common m₀ m' :=
  C.call hs hsame (fun p hp => hp.elim (fun h => P.inRange_lo (by fbo) h)
    (fun h => inRange_stack P C hsf h)) fun x hx hx' => by
    have := not_callR P C (a := a) (n := n) (x := x - fb) hsf (by omega) (by fbo) (by fbo)
    rwa [show fb + (x - fb) = x by omega] at this

/-- `SameOutside` composed over two calls with outputs in the frame. -/
theorem keep_callR₂ (P : Pre w m₀) (C : Common m₀ m) {m' : MachineData} (C' : Common m₀ m')
    {d d' d'' : DataMem} {a n s a' n' s' : Nat} (hs : s ≤ fb) (ha : a + n ≤ 5872) (hs' : s' ≤ fb)
    (ha' : a' + n' ≤ 5872) (hsame : SameOutside d d' (CallR m₀ m a n s))
    (hsame' : SameOutside d' d'' (CallR m₀ m' a' n' s')) {o : Nat} {bs : List UInt8}
    (h : BytesAt d (ad m₀ (fb + o)) bs) (ho : o + bs.length ≤ 5872)
    (hd : o + bs.length ≤ a ∨ a + n ≤ o) (hd' : o + bs.length ≤ a' ∨ a' + n' ≤ o) :
    BytesAt d'' (ad m₀ (fb + o)) bs :=
  keep_callR P C' hs' ha' hsame' (keep_callR P C hs ha hsame h ho hd) ho hd'

end

/-! ## Blocks and calls -/

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **A block that only sets a call's arguments**: no write, the callee-saved registers and SP
kept; at the callee's entry, the registers the block's symbolic state says. -/
theorem callBlock (P : Pre w m₀) {ds : List Directive} {j : Nat} {known : List (XReg × Sym)}
    {S' : SState} {l : Label} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds (stF0 known) = some (S', .call l)) (hmem : S'.mem = [])
    (hkeep : keeps (stF0 known) S' = true) {st : MachineState} (hpc : st.pc = Host.addrOf j)
    (C : Common m₀ st.data)
    (hknown : AllOf (fun p => (st.data.regs.getXReg p.1).toBitVec =
      p.2.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)])) known) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Labels.label l →
      retOf st'.data = Host.addrOf (j + ds.length) →
      Common m₀ st'.data → Saved st.data st'.data → st'.data.dmem = st.data.dmem →
      (∀ r v, S'.reg r = some v →
        (st'.data.regs.getXReg r).toBitVec = v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)])) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := frame_wf P C (vars := fun _ => 0)
  have hm := match_stF0 P C hknown
  refine call_step hk hx hwf hpc hm fun st' hpc' hm' => ?_
  simp only [hx, Option.getD_some] at hm'
  have hd := hm'.dmem_eq hwf hmem
  have hs := Match.saved hm hm' hwf rfl hkeep
  exact cont st' hpc'.1 hpc'.2 (C.call hs (R := fun _ => False) (fun p _ => by rw [hd]; rfl)
    (fun _ h => h.elim) fun _ _ _ h => h) hs hd fun r v h => hm'.regs r v h

/-- **`memset`** of `n` bytes at frame offset `dst`. -/
theorem memsetCall (hset : Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost) (P : Pre w m₀)
    {st : MachineState} {next : Int64} (hpc : st.pc = Labels.label NativeRustcArm.Common.Memset.entryLabel)
    (hret : retOf st.data = next) (C : Common m₀ st.data) {dst n : Nat}
    (h0 : st.data.regs.X0.toBitVec = ad m₀ (fb + dst)) (h2 : st.data.regs.X2.toNat = n)
    (hdr : dst + n ≤ 5776) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → Common m₀ st'.data → Saved st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fb + dst)) (List.replicate n st.data.regs.X1.toUInt8) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := memsetPre P C (o := fb + dst) h0 h2 (by fbo)
  refine call_then (env := Env.ofMachine st.data []) ⟨hpc, hret⟩ hset pre fun st' hpc' post => ?_
  obtain ⟨-, hb, hsame, hs⟩ := post
  rw [h0, h2] at hb hsame
  have hsame' : SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) :=
    hsame.mono fun p hp => Or.inl hp
  exact cont st' hpc' (C.callR P hs (Nat.zero_le _) hdr hsame') hs hb hsame'

/-- **`memcpy`** of `n` bytes from frame offset `src` to `dst`. -/
theorem memcpyCall (hcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) (P : Pre w m₀)
    {st : MachineState} {next : Int64} (hpc : st.pc = Labels.label NativeRustcArm.Common.Memcpy.entryLabel)
    (hret : retOf st.data = next) (C : Common m₀ st.data) {dst src n : Nat}
    (h0 : st.data.regs.X0.toBitVec = ad m₀ (fb + dst))
    (h1 : st.data.regs.X1.toBitVec = ad m₀ (fb + src)) (h2 : st.data.regs.X2.toNat = n)
    (hdr : dst + n ≤ 5776) (hsr : src + n ≤ 5776) (hdis : dst + n ≤ src ∨ src + n ≤ dst)
    (hn : 0 < n) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → Common m₀ st'.data → Saved st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fb + dst)) (bytesOf st.data.dmem (ad m₀ (fb + src)) n) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := memcpyPre P C (o := fb + dst) (o' := fb + src) h0 h1 h2 (by fbo) (by fbo)
    (by omega) hn
  refine call_then (env := Env.ofMachine st.data []) ⟨hpc, hret⟩ hcpy pre fun st' hpc' post => ?_
  obtain ⟨-, hb, hsame, hs⟩ := post
  rw [h0, h1, h2] at hb
  rw [h0, h2] at hsame
  have hsame' : SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data dst n 0) :=
    hsame.mono fun p hp => Or.inl hp
  exact cont st' hpc' (C.callR P hs (Nat.zero_le _) hdr hsame') hs hb hsame'

/-- **`Hasher::update`** of the hasher at frame offset `h` with the bytes `data` at `d`. -/
theorem updateCall (hupd : Spec (label NativeRustcArm.Common.Update.entryLabel) UpdatePre UpdatePost) (P : Pre w m₀)
    {st : MachineState} {next : Int64} (hpc : st.pc = Labels.label NativeRustcArm.Common.Update.entryLabel)
    (hret : retOf st.data = next) (C : Common m₀ st.data) {h d : Nat} {a data : List UInt8}
    (h0 : st.data.regs.X0.toBitVec = ad m₀ (fb + h))
    (h1 : st.data.regs.X1.toBitVec = ad m₀ (fb + d)) (h2 : st.data.regs.X2.toNat = data.length)
    (hh : Keccak.HasherHolds (bytesOf st.data.dmem (ad m₀ (fb + h)) 344) a)
    (hd : BytesAt st.data.dmem (ad m₀ (fb + d)) data) (hhr : h + 344 ≤ 5776)
    (hdr : d + data.length ≤ 5776) (hdis : h + 344 ≤ d ∨ d + data.length ≤ h)
    (hn : 0 < data.length) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → Common m₀ st'.data → Saved st.data st'.data →
      Keccak.HasherHolds (bytesOf st'.data.dmem (ad m₀ (fb + h)) 344) (a ++ data) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data h 344 updateStack) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := updatePre P C (o := fb + h) (o' := fb + d) h0 h1 h2 (by omega) (by omega) (by fbo)
    (by fbo) (by omega) hn ⟨a, hh⟩
  refine call_then (env := Env.ofMachine st.data []) ⟨hpc, hret⟩ hupd pre fun st' hpc' post => ?_
  obtain ⟨-, hh', hsame, hs⟩ := post
  rw [h0, h1, h2] at hh'
  rw [h0] at hsame
  have := hh' a hh
  rw [bytesOf_of hd rfl] at this
  exact cont st' hpc' (C.callR P hs (by decide) (by omega) hsame) hs this hsame

/-- **`Hasher::finalize`** of the hasher at frame offset `h` to the 32 bytes at `o`. -/
theorem finalizeCall (hfin : Spec (label NativeRustcArm.Common.Finalize.entryLabel) FinalizePre FinalizePost) (P : Pre w m₀)
    {st : MachineState} {next : Int64} (hpc : st.pc = Labels.label NativeRustcArm.Common.Finalize.entryLabel)
    (hret : retOf st.data = next) (C : Common m₀ st.data) {o h : Nat} {a : List UInt8}
    (h0 : st.data.regs.X0.toBitVec = ad m₀ (fb + o))
    (h1 : st.data.regs.X1.toBitVec = ad m₀ (fb + h))
    (hh : Keccak.HasherHolds (bytesOf st.data.dmem (ad m₀ (fb + h)) 344) a) (hor : o + 32 ≤ 5776)
    (hhr : h + 344 ≤ 5776) (hdis : o + 32 ≤ h ∨ h + 344 ≤ o) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → Common m₀ st'.data → Saved st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fb + o)) (Keccak.hashBytes a) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data o 32 finalizeStack) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := finalizePre P C (o := fb + o) (o' := fb + h) h0 h1 (by omega) (by omega) (by fbo)
    (by fbo) (by omega) ⟨a, hh⟩
  refine call_then (env := Env.ofMachine st.data []) ⟨hpc, hret⟩ hfin pre fun st' hpc' post => ?_
  obtain ⟨hb, hsame, hs⟩ := post
  rw [h0, h1, Keccak.finalize_eq hh] at hb
  rw [h0] at hsame
  exact cont st' hpc' (C.callR P hs (by decide) (by omega) hsame) hs hb hsame

end

end NativeRustcArm.Xmss.XmssVerify
