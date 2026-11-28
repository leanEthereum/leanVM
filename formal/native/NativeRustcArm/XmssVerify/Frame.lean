module

public import NativeRustcArm.XmssVerify.Parse

/-!
# `xmss_verify`: the frame as a block's region

The lengths of the model's byte strings (`length_msgB`, `length_pkB`, `length_sigB`,
`length_memBytes`); the frame as an environment's region 0 (`frame_wf`, `match_stF0`,
`eval_ptr0`); a value a block stored in the frame (`frameWrite`), the frame's bytes no write of a
block overlaps (`frameKeep`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash

public section

theorem wordsBytes_map (f : Nat → UInt64) (n : Nat) :
    Native.Keccak.wordsBytes ((List.range n).map f) =
      ((List.range n).map (fun k => wordBytes (f k))).flatten := by
  unfold Native.Keccak.wordsBytes
  rw [List.flatMap_def, List.map_map]
  rfl

theorem length_sigB (w : Nat → UInt64) : (sigB w).length = 2404 := by
  rw [sigB, NativeRustc.Xmss.sigBytes, wordsBytes_map, List.length_append,
    NativeRustc.length_u32Bytes, length_flatten_range 300 (s := 8)
      (fun _ _ => NativeRustc.length_wordBytes _)]

theorem length_msgB (w : Nat → UInt64) : (msgB w).length = 32 := by
  rw [msgB, NativeRustc.Xmss.messageBytes, wordsBytes_map,
    length_flatten_range 4 (s := 8) (fun _ _ => NativeRustc.length_wordBytes _)]

theorem length_pkB (w : Nat → UInt64) : (pkB w).length = 32 := by
  rw [pkB, NativeRustc.Xmss.pkBytes, wordsBytes_map,
    length_flatten_range 4 (s := 8) (fun _ _ => NativeRustc.length_wordBytes _)]

theorem length_slice {bs : List UInt8} {o : Nat} (h : o + 16 ≤ bs.length) :
    (NativeRustc.slice bs o 16).length = 16 := by
  simp [NativeRustc.slice]
  omega

/-- A layer's 1200 bytes. -/
theorem length_memBytes {bs : List UInt8} {c : Nat} (h : c + 1200 ≤ bs.length) :
    (NativeRustc.Xmss.takeLayer bs c).1.memBytes.length = 1200 := by
  simp only [NativeRustc.Xmss.takeLayer, NativeRustc.Xmss.LayerSignature.memBytes,
    List.length_append]
  rw [length_flatten_range 16 (s := 16) fun j hj => length_slice (by omega),
    length_flatten_range 58 (s := 16) fun j hj => length_slice (by omega), length_slice (by omega)]

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

/-- The frame as an environment's only region. -/
theorem frame_wf (P : Pre w m₀) (C : Common m₀ m) (vars : Nat → BitVec 64 := fun _ => 0) :
    (Env.ofMachine m [(ad m₀ fb, 5872)] vars).WF :=
  Env.wf_of ⟨⟨(P.mapped.sub (i := fb) (k := 5872) (by fbo)).kept C.kept,
    P.ad_nw (o := fb) (s := 5872) (by fbo)⟩, trivial⟩ (List.pairwise_singleton _ _)

theorem match_stF0 (P : Pre w m₀) (C : Common m₀ m) {known : List (XReg × Sym)}
    (hk : AllOf (fun p => (m.regs.getXReg p.1).toBitVec =
      p.2.eval (Env.ofMachine m [(ad m₀ fb, 5872)])) known) :
    Match (Env.ofMachine m [(ad m₀ fb, 5872)]) (stF0 known) m := by
  unfold stF0
  apply match_ofMachine
  · exact And.intro rfl (And.intro (fun _ => frame16 P) trivial)
  · rw [C.sp]
    simp [Sym.eval]
  · exact hk
  · exact trivial
  · exact trivial
  · exact trivial

theorem eval_ptr0 (o : Nat) {vars : Nat → BitVec 64} :
    (Sym.ptr 0 o).eval (Env.ofMachine m [(ad m₀ fb, 5872)] vars) = ad m₀ (fb + o) := by
  simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, ad_add, BitVec.ofInt_natCast]

/-- A value a block stored in the frame (region 0). -/
theorem frameWrite {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    {m' : MachineData} (hm : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S m')
    {o : Nat} (ho : o + 8 ≤ 5872) {v : Sym} (hw : ∀ t < 8, findWrite 0 (o + t) S.mem = some (v, t)) :
    BytesAt m'.dmem (ad m₀ (fb + o))
      (regBytes (v.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars))) := by
  have := hm.bytesAt_write (r := 0) (b := ad m₀ fb) (sz := 5872) rfl ho hw
  rwa [ad_add] at this

/-- Bytes of the frame (region 0) no write of a block overlaps. -/
theorem frameKeep {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    {m' : MachineData} (hm : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S m')
    {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 5872) (hc : firstOverlap 0 o bs.length S.mem = none)
    (h : BytesAt m.dmem (ad m₀ (fb + o)) bs) : BytesAt m'.dmem (ad m₀ (fb + o)) bs := by
  rw [← ad_add] at h ⊢
  exact hm.bytesAt_keep (r := 0) (b := ad m₀ fb) (sz := 5872) rfl ho hc h

omit [Labels] in
theorem toNat_X (m : MachineData) (r : XReg) : (m.regs.getXReg r).toNat = (m.regs.getXReg r).toBitVec.toNat :=
  rfl

end

end

end NativeRustcArm.Xmss.XmssVerify
