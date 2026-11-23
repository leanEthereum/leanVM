module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.XmssVerify.Turn
public import NativeRustcArm.XmssVerify.Fold

/-!
# `xmss_verify`: a call of `wots_leaf`

`wotsCall`: `wots_leaf` with its output at `5408` and its inputs in the frame, its contract in
terms of the inputs' bytes. Its output's bytes (`out_none`, `out_some`): the tag `0`, or a nonzero
tag, the codeword and the leaf.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

public section

theorem out_none {d : DataMem} {a : BitVec 64} (hm : Mapped d a 75)
    (h : WotsLeafOut (bytesOf d a 75) none) : ∃ rest, BytesAt d a (0 :: rest) := by
  have hb := bytesAt_bytesOf hm
  simp only [WotsLeafOut] at h
  obtain ⟨rest, hr⟩ := List.head?_eq_some_iff.mp h
  exact ⟨rest, hr ▸ hb⟩

theorem out_some {d : DataMem} {a : BitVec 64} (hm : Mapped d a 75) {x lf : List UInt8}
    (h : WotsLeafOut (bytesOf d a 75) (some (x, lf))) :
    ∃ tag, tag ≠ 0 ∧ BytesAt d a (tag :: (x ++ lf)) := by
  have hb := bytesAt_bytesOf hm
  obtain ⟨tag, ht, he⟩ := h
  rw [List.take_of_length_le (by rw [length_bytesOf])] at he
  exact ⟨tag, ht, he ▸ hb⟩

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **A call of `wots_leaf`** with its output at `5408`, the public parameter at `2464`, the
message's `n5` bytes at `o4`, the randomizer at `o6` and the chain values at `o7`. -/
theorem wotsCall (Cs : Callees) (P : Pre w m₀) {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcArm.Xmss.WotsLeaf.entryLabel) (hret : retOf st.data = next) (C : Common m₀ st.data)
    {o4 n5 o6 o7 layer : Nat} {e : UInt32}
    (h0 : st.data.regs.X0.toBitVec = ad m₀ (fb + 5408))
    (h1 : st.data.regs.X1.toBitVec = ad m₀ (fb + 2464)) (h2 : st.data.regs.X2.toNat = layer)
    (h3 : st.data.regs.X3.toUInt32 = e) (h4 : st.data.regs.X4.toBitVec = ad m₀ (fb + o4))
    (h5 : st.data.regs.X5.toNat = n5) (h6 : st.data.regs.X6.toBitVec = ad m₀ (fb + o6))
    (h7 : st.data.regs.X7.toBitVec = ad m₀ (fb + o7)) (ho4 : o4 + n5 ≤ 5776) (hn5 : 0 < n5)
    (ho6 : o6 + 16 ≤ 5776) (ho7 : o7 + 16 * 58 ≤ 5776) {pp msg rand : List UInt8}
    {vals : List (List UInt8)} (hpp : BytesAt st.data.dmem (ad m₀ (fb + 2464)) pp)
    (hpl : pp.length = 16) (hmsg : BytesAt st.data.dmem (ad m₀ (fb + o4)) msg)
    (hml : msg.length = n5) (hrand : BytesAt st.data.dmem (ad m₀ (fb + o6)) rand)
    (hrl : rand.length = 16)
    (hvals : (List.range 58).map (fun i =>
      bytesOf st.data.dmem (ad m₀ (fb + o7) + BitVec.ofNat 64 (16 * i)) 16) = vals)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → Common m₀ st'.data → Saved st.data st'.data →
      WotsLeafOut (bytesOf st'.data.dmem (ad m₀ (fb + 5408)) 75) (wotsLeaf pp layer e msg rand vals) →
      SameOutside st.data.dmem st'.data.dmem (CallR m₀ st.data 5408 75 wotsLeafStack) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have pre := wotsLeafPre P C (o := fb + 5408) (o1 := fb + 2464) (o4 := fb + o4) (n5 := n5)
    (o6 := fb + o6) (o7 := fb + o7) h0 h1 h4 h5 h6 h7 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by fbo) (by fbo) (by fbo) (by fbo) (by fbo) hn5
  refine call_then (env := Env.ofMachine st.data []) ⟨hpc, hret⟩ Cs.wots pre
    fun st' hpc' post => ?_
  obtain ⟨hout, hsame, hs⟩ := post
  simp only [WotsLeafPre.pp, WotsLeafPre.message, WotsLeafPre.randomizer, WotsLeafPre.values,
    h0, h1, h2, h3, h4, h5, h6, h7] at hout
  rw [bytesOf_of hpp hpl, bytesOf_of hmsg hml, bytesOf_of hrand hrl, hvals] at hout
  rw [h0] at hsame
  exact cont st' hpc' (C.callR P hs le_rfl (by omega) hsame) hs hout hsame

end

end NativeRustcArm.Xmss.XmssVerify
