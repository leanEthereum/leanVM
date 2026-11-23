module

public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.SphincsVerify.Encode.State
public import NativeRustcX64.SphincsVerify.Bswap

/-!
# The frame's environment with `LAYER_HEIGHTS`

`b104` reads `LAYER_HEIGHTS` (the rodata label `NativeRustcX64.layerHeightsLabel`, 24 bytes): its environment has the
frame's two regions and the table as region 2 (`Run.envL`), followed by the loader's memcpy and
memset slots at regions 3 and 4. It is well formed (`Run.envL_wf`), and a seeded symbolic state
(`Run.match_frameL`), a block ending in a call that writes only the frame's places is at the call
(`Run.AtCall.of_matchL`), and keeps the bytes it does not write (`Run.bytesAt_keptL`). A word of
the frame or of the table loaded is the word (`Run.load_word`, `Run.load_height`); a block's write
is the value's bytes (`Run.write_at`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (wordBytes v)) = v.toBitVec := by
  have hw := bytes_word v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  rw [← hw, hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := v.toBitVec.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

/-- `n` bytes from byte `k` of bytes in memory. -/
theorem bytesAt_slice {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (k n : Nat) (hk : k + n ≤ bs.length) :
    BytesAt d (a + BitVec.ofNat 64 k) ((bs.drop k).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [Sym.addr_add, h (k + i) (by omega)]
  simp [List.getElem_take, List.getElem_drop]

theorem bytesAt_append_of {d : DataMem} {a : BitVec 64} {p q : List UInt8} (hp : BytesAt d a p)
    (hq : BytesAt d (a + BitVec.ofNat 64 p.length) q) : BytesAt d a (p ++ q) := by
  intro i hi
  by_cases h : i < p.length
  · rw [List.getElem_append_left h]
    exact hp i h
  · rw [List.getElem_append_right (by omega)]
    have := hq (i - p.length) (by simp at hi; omega)
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, show p.length + (i - p.length) = i by omega] at this

namespace Run

variable (r : Run) [Labels]

/-- The environment of a state of the frame, region 2 `LAYER_HEIGHTS`. -/
abbrev envL (m : MachineData) (ret : BitVec 64 := 0) : Sym.Env :=
  Sym.Env.ofMachine m [(r.base, frameRegion), (r.base - 16#64, 16),
    ((label NativeRustcX64.layerHeightsLabel).toBitVec, 24),
    (gotAddr "memcpy", 8), (gotAddr "memset", 8)] (fun _ ↦ 0) ret

omit [Labels] in
theorem length_lhBytes : lhBytes.length = 24 := by decide

/-- **The environment is well formed.** -/
theorem envL_wf (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) (ret : BitVec 64) :
    (r.envL m ret).WF := by
  have hb := r.base_toNat hpre
  have w0 := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) ret
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  have hlh := r.lh hpre hF.2.2.1
  have hw := hpre.2.2.2.1
  have hA := hpre.2.2.2.2.1
  have hbw := r.below_toNat hpre
  simp only [sphincsStack_eq] at hA hbw
  refine Sym.Env.wf_of ⟨⟨w0.mapped 0 _ _ rfl, w0.noWrap 0 _ _ rfl⟩,
    ⟨w0.mapped 1 _ _ rfl, w0.noWrap 1 _ _ rfl⟩, ⟨fun i hi ↦ ?_, hw⟩,
    ⟨w0.mapped 2 _ _ rfl, w0.noWrap 2 _ _ rfl⟩,
    ⟨w0.mapped 3 _ _ rfl, w0.noWrap 3 _ _ rfl⟩, trivial⟩ ?_
  · show (m.dmem.get? ((label NativeRustcX64.layerHeightsLabel).toBitVec + BitVec.ofNat 64 i)).isSome
    rw [hlh i (by rw [length_lhBytes]; exact hi)]
    rfl
  · have h01 := w0.disjoint 0 1 _ _ _ _ (by decide) rfl rfl
    have h02 : Apart r.base frameRegion (label NativeRustcX64.layerHeightsLabel).toBitVec 24 := by
      unfold Apart at *
      rw [frameRegion_eq]
      omega
    have h12 : Apart (r.base - 16#64) 16 (label NativeRustcX64.layerHeightsLabel).toBitVec 24 := by
      unfold Apart at *
      rw [hlo]
      omega
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ?_))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact h01
      · exact h02
      · exact (r.got_apart_frame hpre (by simp)).symm
      · exact (r.got_apart_frame hpre (by simp)).symm
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact h12
      · exact (r.got_apart_below hpre (by simp)).symm
      · exact (r.got_apart_below hpre (by simp)).symm
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact (r.got_apart_lh hpre (by simp)).symm
      · exact (r.got_apart_lh hpre (by simp)).symm
    · simpa using (r.got hpre).2

omit [Labels] in
/-- Keep the height table at region 2; loader slots occupy regions 3 and 4. -/
def frameStateL (known : List (Reg64 × Sym))
    (aliases : List (Sym × Nat × Int) := []) : Sym.SState :=
  ((Sym.init [frameRegion, 16, 24, 8, 8] ((.rsp, .ptr 0 0) :: known)
    [(NativeRustcX64.layerHeightsLabel, 2)] []
    (frameAliases ++ [(.gotSlot "memcpy", 3, 0), (.gotSlot "memset", 4, 0)] ++ aliases)).withKnownBytes
      3 0 8 (.label "memcpy")).withKnownBytes 4 0 8 (.label "memset")

/-- **A fresh symbolic state** for a state of the frame, `LAYER_HEIGHTS` at region 2. -/
theorem match_frameL (hpre : r.Pre) {m : MachineData} {ret : BitVec 64} (hF : r.Frame m)
    {known : List (Reg64 × Sym)}
    {aliases : List (Sym × Nat × Int)}
    (hknown : Sym.AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.envL m ret)) known)
    (haliases : Sym.AllOf (fun p ↦ p.1.eval (r.envL m ret) =
      (r.envL m ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Sym.Match (r.envL m ret) (frameStateL known aliases) m := by
  apply Sym.Match.withKnownBytes
  · apply Sym.Match.withKnownBytes
    · apply Sym.match_ofMachine
      · exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      · exact ⟨by
          show rspOf m = r.base + BitVec.ofInt 64 0
          simp only [BitVec.ofInt_ofNat, BitVec.add_zero]
          exact hF.1, hknown⟩
      · exact ⟨rfl, trivial⟩
      · trivial
      · refine ⟨alias8 r, ?_, ?_, ?_, haliases⟩
        · change r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
          rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
          bv_omega
        · simp [Sym.eval, Sym.Env.base, gotAddr]
        · simp [Sym.eval, Sym.Env.base, gotAddr]
    · intro i hi
      simpa [Sym.eval, Sym.Env.base, envL] using
        r.got_byte hpre hF.2.2.1 (by simp : "memcpy" ∈ _) hi
  · intro i hi
    simpa [Sym.eval, Sym.Env.base, envL] using
      r.got_byte hpre hF.2.2.1 (by simp : "memset" ∈ _) hi

/-- The places a block's writes (`frameWrites`) cover are in the stack area off the saved
registers. -/
theorem written_areaL (hpre : r.Pre) {m : MachineData} {ret : BitVec 64} {S : Sym.SState}
    (hw : frameWrites S = true) :
    ∀ p, Sym.Written (r.envL m ret) S p → r.StackArea p ∧ ¬InRange (r.off 29352) 48 p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1, h2⟩
  simp only [frameWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    cases hr
    exact r.inRange_off hpre (a := 0) (n := 29352) (by decide) (by
      rw [show r.off 0 = r.base by simp [off], Sym.inRange_iff (by omega)]
      omega)
  · rw [hw1] at hr
    cases hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    have hs := r.off_toNat hpre (a := 29352) (by decide)
    rw [hlo] at h1 h2
    rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
    omega

/-- **At a call after a block** run in this environment: RSP 8 below the base. -/
theorem AtCall.of_matchL (hpre : r.Pre) {m m' : MachineData} {ret : BitVec 64} (hF : r.Frame m)
    {S : Sym.SState}
    (hm : Sym.Match (r.envL m ret) S m') (hwf : (r.envL m ret).WF)
    (hsp : S.reg .rsp = some (.ptr 0 (-8))) (hw : frameWrites S = true) : r.AtCall m' := by
  have hF' := Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 (m' := { m' with regs := m.regs }) hF.1
    (hm.sameOutside hwf) (r.written_areaL hpre hw) (hm.kept hwf)
  refine ⟨?_, hF'.2.1, hF'.2.2.1, hF'.2.2.2⟩
  rw [rspOf, hm.regs .rsp _ hsp]
  show r.base + BitVec.ofInt 64 (-8) + 8#64 = r.base
  rw [show BitVec.ofInt 64 (-8) = -8#64 by decide]
  bv_omega

/-- **Bytes a block does not write are kept**, in this environment. -/
theorem bytesAt_keptL (hpre : r.Pre) {m m' : MachineData} {ret : BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.envL m ret) S m') (hwf : (r.envL m ret).WF) {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 29400) (h : BytesAt m.dmem (r.off o) bs)
    (hn : noWriteIn S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hn
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2
  rcases hn w hwm with ⟨hw0, hw⟩ | ⟨hw1, hw⟩
  · rw [hw0] at hr
    cases hr
    omega
  · rw [hw1] at hr
    cases hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    rw [hlo] at h1 h2
    omega

omit [Labels] in
/-- A word of the frame, loaded. -/
theorem load_word {env : Sym.Env} {m : MachineData} (hb : env.base 0 = r.base)
    (hmem : env.mem0 = m.dmem) {o : Nat} {v : UInt64} (h : r.WordAt m o v) :
    env.load 0 o 8 = v.toBitVec := by
  rw [Sym.Env.load_of_bytesAt (length_wordBytes v) (by rw [hb, hmem]; exact h),
    ofInt_ofBytes_wordBytes]

omit [Labels] in
theorem lh_slice {l : Nat} (hl : l < 3) :
    (lhBytes.drop (8 * l)).take 8 = wordBytes (layerHeights.getD l 0).toUInt64 := by
  interval_cases l <;> decide

/-- **Layer `l`'s height**, loaded from `LAYER_HEIGHTS`. -/
theorem load_height (hpre : r.Pre) {m : MachineData} (ret : BitVec 64) (hF : r.Frame m) {l : Nat}
    (hl : l < 3) :
    (r.envL m ret).load 2 (8 * l) 8 = BitVec.ofNat 64 (layerHeights.getD l 0) := by
  have h := bytesAt_slice (r.lh hpre hF.2.2.1) (8 * l) 8 (by rw [length_lhBytes]; omega)
  rw [lh_slice hl] at h
  rw [Sym.Env.load_of_bytesAt (length_wordBytes _) h, ofInt_ofBytes_wordBytes]
  rfl

/-- A frame pointer's value. -/
theorem ptr_evalL (m : MachineData) (ret : BitVec 64) (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (r.envL m ret) = r.off o := by
  show r.base + BitVec.ofInt 64 (o : Int) = r.base + BitVec.ofNat 64 o
  rw [BitVec.ofInt_natCast]

/-- A frame pointer's value. -/
theorem ptr_eval (m : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (r.env m vars ret) = r.off o := by
  show r.base + BitVec.ofInt 64 (o : Int) = r.base + BitVec.ofNat 64 o
  rw [BitVec.ofInt_natCast]

omit [Labels] in
theorem bytesAt_app_off {d : DataMem} {o o' : Nat} {p q : List UInt8} (hp : BytesAt d (r.off o) p)
    (hq : BytesAt d (r.off o') q) (ho : o' = o + p.length) : BytesAt d (r.off o) (p ++ q) :=
  bytesAt_append_of hp (by rw [off_add, ← ho]; exact hq)

end Run

end

end NativeRustcX64.SphincsVerifyProof
