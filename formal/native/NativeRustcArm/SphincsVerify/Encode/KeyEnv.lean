module

public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.SphincsVerify.Encode.State

/-!
# The frame's environment with `LAYER_HEIGHTS`

`b101` reads `LAYER_HEIGHTS` (the rodata label `NativeRustcArm.layerHeightsLabel`, 24 bytes): its environment has the
frame as region 0 and the table as region 1 (`Run.envL`). It is well formed (`Run.envL_wf`), a
fresh symbolic state with the label at region 1 describes a state of the frame
(`Run.match_frameL`), and a block that writes only the frame below the saved registers keeps the
frame's invariant (`Run.Frame.of_matchL`) and the bytes it does not write (`Run.bytesAt_keptL`).
A word of the frame or of the table loaded is the word (`Run.load_word`, `Run.load_height`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash

@[expose] public section

namespace Run

variable (r : Run) [Labels]

/-- The environment of a state of the frame, region 0 the frame, region 1 `LAYER_HEIGHTS`. -/
abbrev envL (m : MachineData) : Sym.Env :=
  Sym.Env.ofMachine m [(r.base, 29376), ((label NativeRustcArm.layerHeightsLabel).toBitVec, 24)]

omit [Labels] in
theorem length_lhBytes : lhBytes.length = 24 := by decide

/-- **The environment is well formed.** -/
theorem envL_wf (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) : (r.envL m).WF := by
  have h := r.frame_mapped hpre hF (a := 0) (n := 29376) (by decide)
  rw [off_zero] at h
  have hlh := r.lh hpre hF
  have hw := hpre.2.2.2.1
  have hA := hpre.2.2.2.2.1
  have hb := r.below_toNat hpre
  refine Sym.Env.wf_of ⟨h, ⟨fun i hi ↦ ?_, hw⟩, trivial⟩ ?_
  · show (m.dmem.get? ((label NativeRustcArm.layerHeightsLabel).toBitVec + BitVec.ofNat 64 i)).isSome
    rw [hlh i (by rw [length_lhBytes]; exact hi)]
    rfl
  · refine List.pairwise_cons.mpr ⟨fun e he ↦ ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton] at he
    subst he
    simp only [sphincsStack_eq] at hA hb
    have := apart_of_sub hA (y := r.base) (n' := 29376) (by omega) (by omega)
    unfold Apart at this ⊢
    dsimp only
    omega

/-- **A fresh symbolic state** for a state of the frame, `LAYER_HEIGHTS` at region 1. -/
theorem match_frameL (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {known : List (XReg × Sym)}
    (hknown : Sym.AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.envL m)) known) :
    Sym.Match (r.envL m)
      (Sym.init [(29376, true), (24, false)] (.ptr 0 0) known [(NativeRustcArm.layerHeightsLabel, 1)]) m :=
  Sym.match_ofMachine ⟨rfl, fun _ ↦ r.base_aligned hpre, rfl, fun h ↦ absurd h (by decide),
    trivial⟩
    (by show m.regs.SP.toBitVec = r.base + BitVec.ofInt 64 0; simp only [BitVec.ofInt_ofNat,
      BitVec.add_zero]; exact hF.1)
    hknown ⟨rfl, trivial⟩ trivial trivial

/-- **The invariant after a block** in this environment. -/
theorem Frame.of_matchL (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {S : Sym.SState}
    (hm : Sym.Match (r.envL m) S m') (hwf : (r.envL m).WF)
    (hsp : S.sp = .ptr 0 0) (hx29 : S.reg .X29 = some (.ptr 0 29280))
    (hw : frameWrites S = true) : r.Frame m' := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  refine hF.of_block ?_ ?_ (hm.sameOutside hwf) ?_ (hm.kept hwf)
  · rw [hm.sp, hsp]
    show r.base + BitVec.ofInt 64 0 = r.base
    simp
  · rw [hm.regs .X29 _ hx29]
    rfl
  · rintro p ⟨w, hwm, b, sz, hr, h1, h2⟩
    simp only [frameWrites, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hw
    obtain ⟨hw0, hwn⟩ := hw w hwm
    rw [hw0] at hr
    cases hr
    exact r.inRange_off hpre (a := 0) (n := 29280) (by decide) (by
      rw [off_zero, Sym.inRange_iff (by omega)]
      omega)

/-- **Bytes a block does not write are kept**, in this environment. -/
theorem bytesAt_keptL (hpre : r.Pre) {m m' : MachineData} {S : Sym.SState}
    (hm : Sym.Match (r.envL m) S m') (hwf : (r.envL m).WF) (hfw : frameWrites S = true) {o : Nat}
    {bs : List UInt8} (ho : o + bs.length ≤ 29376) (h : BytesAt m.dmem (r.off o) bs)
    (hn : noWriteIn S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hn
  simp only [frameWrites, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hfw
  have hw := hn w hwm
  have hw0 := (hfw w hwm).1
  rw [hw0] at hr hw
  cases hr
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2
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
theorem load_height (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {l : Nat} (hl : l < 3) :
    (r.envL m).load 1 (8 * l) 8 = BitVec.ofNat 64 (layerHeights.getD l 0) := by
  have h := bytesAt_slice (r.lh hpre hF) (8 * l) 8 (by rw [length_lhBytes]; omega)
  rw [lh_slice hl] at h
  rw [Sym.Env.load_of_bytesAt (length_wordBytes _) h, ofInt_ofBytes_wordBytes]
  rfl

end Run

end

end NativeRustcArm.SphincsVerifyProof
