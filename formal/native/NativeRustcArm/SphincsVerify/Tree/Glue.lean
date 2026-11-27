module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Calls
public import NativeRustcArm.SphincsVerify.Rev
public import NativeRustcArm.SphincsVerify.Epilogue
public import NativeRustcArm.SphincsVerify.Tree.Model
public import NativeRustcArm.SphincsVerify.Tree.Exec
public import NativeRustcArm.Hasher.Bytes

/-!
# The tree region's glue

The blocks' places in the program (`hb134`, ...) and the labels they branch to; what every state
of the region keeps below the scratch (`Tree.Keep`: the inputs and the layer loop's spills other
than `432`, all in the frame's first 8224 bytes off `432 .. 440`) and how it survives a block or a
call (`Tree.LowKept`, `Tree.lowKept_of_match`, `Tree.lowKept_of_call`, `Tree.Keep.of_low`); reading
the environment's loads of known bytes (`Tree.bytes_load`, `Tree.load_word`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

/-! ## Lengths -/

theorem length_wots {sig : List UInt8} (hsig : sig.length = 7740) {l : Nat} (hl : l < 3) :
    ((Signature.fromBytes sig).layers.getD l ⟨0, []⟩).wots.flatten.length = 1024 := by
  rw [length_flatten_const (k := 16)]
  · simp [Signature.fromBytes, hl]
  intro x hx
  simp only [Signature.fromBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hl, Option.map_some, Option.getD_some, List.mem_map,
    List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  apply length_slice
  rw [hsig]
  interval_cases l <;> simp [sigLayerOff] <;> omega

theorem randomizer_fromBytes' (b : List UInt8) : (Signature.fromBytes b).randomizer = slice b 0 16 :=
  rfl

/-- The parsed signature in memory is 7740 bytes. -/
theorem length_sigMem {sig : List UInt8} (hsig : sig.length = 7740) :
    (sigMem (Signature.fromBytes sig)).length = 7740 := by
  rw [sigMem, List.length_append, length_forsMem hsig, List.length_append,
    length_flatten_const (k := 16) (fun x hx ↦ length_of_mem_paths hsig hx), length_paths,
    List.length_append, length_flatten_const (k := 1028)]
  · rw [randomizer_fromBytes',
      length_slice (b := sig) (off := 0) (len := 16) (by rw [hsig]; omega)]
    have h3 : (Signature.fromBytes sig).layers.length = 3 := by
      simp only [Signature.fromBytes, List.length_map, List.length_range]
    rw [List.length_map, h3]
  intro x hx
  simp only [Signature.fromBytes, List.map_map, List.mem_map, List.mem_range,
    Function.comp_def] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  have := length_wots hsig hl
  simp only [Signature.fromBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hl, Option.map_some, Option.getD_some] at this
  rw [layerMem, List.length_append, this]
  rfl

variable (r : Run)

/-! ## Below the scratch -/

/-- The frame's bytes below `8224`, off the path-pointer spill `432 .. 440`, are as in `m`. -/
@[expose] def LowKept (m m' : MachineData) : Prop :=
  ∀ i, (i < 432 ∨ (440 ≤ i ∧ i < 8224)) → m'.dmem.get? (r.off i) = m.dmem.get? (r.off i)

variable {r}

theorem LowKept.refl (m : MachineData) : LowKept r m m := fun _ _ ↦ rfl

theorem LowKept.trans {m₁ m₂ m₃ : MachineData} (h₁ : LowKept r m₁ m₂) (h₂ : LowKept r m₂ m₃) :
    LowKept r m₁ m₃ := fun i hi ↦ (h₂ i hi).trans (h₁ i hi)

theorem LowKept.bytesAt {m m' : MachineData} (hk : LowKept r m m') {o : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off o) bs) (ho : o + bs.length ≤ 432 ∨ (440 ≤ o ∧ o + bs.length ≤ 8224)) :
    BytesAt m'.dmem (r.off o) bs :=
  fun i hi ↦ by
    rw [Run.off_add, hk _ (by omega), ← Run.off_add]
    exact h i hi

variable (r)

/-- The layer loop's spills other than `432` (which `b143` reuses for the layer's path pointer). -/
@[expose] def TreeSpills (l : Nat) (m : MachineData) : Prop :=
  r.WordAt m 8 (r.addr 19009) ∧ r.WordAt m 16 (l + 1).toUInt64 ∧
    r.WordAt m 24 (4656 + 1028 * (l + 1)).toUInt64 ∧ r.WordAt m 32 l.toUInt64 ∧
    r.WordAt m 40 (r.key l).leaf.toUInt64 ∧ r.WordAt m 48 (layerHeights.getD l 0).toUInt64 ∧
    r.WordAt m 400 r.idx ∧ r.WordAt m 408 (r.addr (5140 + 1028 * l)) ∧
    BytesAt m.dmem (r.off 424) (be32 (r.key l).leaf) ∧
    BytesAt m.dmem (r.off 440) (be64 (r.key l).tree)

/-- **What the tree region keeps**: the inputs and layer `l`'s spills other than `432`. -/
@[expose] def Keep (l : Nat) (m : MachineData) : Prop := r.Inputs m ∧ TreeSpills r l m

variable {r}

theorem TreeSpills.of_layerSpills {l : Nat} {m : MachineData} (h : r.LayerSpills l m) :
    TreeSpills r l m :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

theorem Keep.of_low {l : Nat} {m m' : MachineData} (hK : Keep r l m) (hk : LowKept r m m') :
    Keep r l m' := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14⟩ := hK
  have hw : ∀ v : UInt64, (wordBytes v).length = 8 := fun v ↦ length_wordBytes v
  refine ⟨⟨hk.bytesAt h1 (Or.inr ⟨by decide, by rw [r.hpk]; omega⟩),
    hk.bytesAt h2 (Or.inr ⟨by decide, by rw [Run.sig, length_sigMem r.hsig]⟩),
    hk.bytesAt h3 (Or.inl (by rw [hw]; omega))⟩,
    hk.bytesAt h4 (Or.inl (by rw [hw]; omega)), hk.bytesAt h5 (Or.inl (by rw [hw]; omega)),
    hk.bytesAt h6 (Or.inl (by rw [hw]; omega)), hk.bytesAt h7 (Or.inl (by rw [hw]; omega)),
    hk.bytesAt h8 (Or.inl (by rw [hw]; omega)), hk.bytesAt h9 (Or.inl (by rw [hw]; omega)),
    hk.bytesAt h10 (Or.inl (by rw [hw]; omega)), hk.bytesAt h11 (Or.inl (by rw [hw]; omega)),
    hk.bytesAt h12 (Or.inl (by simp [be32])),
    hk.bytesAt h14 (Or.inr ⟨by decide, by simp [be64]⟩)⟩

variable [Labels]

/-- **A block that writes off `0 .. 432` and `440 .. 8224`** keeps them. -/
theorem lowKept_of_match (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m')
    (hwf : (r.env m vars).WF) (hn1 : Run.noWriteIn S 0 432 = true)
    (hn2 : Run.noWriteIn S 440 7784 = true) : LowKept r m m' := by
  intro i hi
  have hmap : (m.dmem.get? (r.off i)).isSome := by
    simpa using (r.frame_mapped hpre hF (a := i) (n := 1) (by omega)).1 0 (by omega)
  have hb : BytesAt m.dmem (r.off i) [(m.dmem.get? (r.off i)).get hmap] := by
    intro j hj
    simp only [List.length_singleton] at hj
    have : j = 0 := by omega
    subst this
    simp
  have hb' := r.bytesAt_kept hpre hm hwf (o := i) (by simp; omega) hb
    (by
      simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        List.length_singleton] at hn1 hn2 ⊢
      intro w hw
      rcases hi with hi | ⟨hi1, hi2⟩
      · rcases hn1 w hw with (h | h) | h
        · exact Or.inl (Or.inl h)
        · by_cases h' : w.off + w.n ≤ i
          · exact Or.inl (Or.inr h')
          · exact Or.inr (by omega)
        · omega
      · rcases hn2 w hw with (h | h) | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (by omega))
        · exact Or.inr (by omega))
  have := hb' 0 (by simp)
  simp only [BitVec.add_zero, List.getElem_cons_zero] at this
  rw [this, Option.some_get]

/-- **A call that writes above the inputs** keeps them. -/
theorem lowKept_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : 8224 ≤ a) (han : a + n ≤ 21616) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : LowKept r m m' :=
  fun i hi ↦ hout _ (r.not_callOut hpre hF han hN (by omega) (Or.inl (by omega)))

/-! ## Loads of known bytes -/

omit [Labels] in
/-- The bytes of a load of known bytes. -/
theorem bytes_load {m : MachineData} {vars : Nat → BitVec 64} {o n : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off o) bs) (hl : bs.length = n) (hn : n ≤ 8) :
    (List.range n).map (byteOf ((r.env m vars).load 0 o n)) = bs := by
  subst hl
  apply List.ext_getElem (by simp)
  intro t h1 h2
  rw [List.getElem_map, List.getElem_range, byteOf_load h2 hn]
  show (m.dmem.get? (r.base + BitVec.ofNat 64 (o + t))).getD 0 = _
  rw [show r.base + BitVec.ofNat 64 (o + t) = r.off o + BitVec.ofNat 64 t by
    rw [Run.off_add]; rfl, h t h2]
  rfl

omit [Labels] in
/-- A load of a word's bytes is the word. -/
theorem load_word {m : MachineData} {vars : Nat → BitVec 64} {o : Nat} {v : UInt64}
    (h : r.WordAt m o v) : (r.env m vars).load 0 o 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (bs := wordBytes v) (length_wordBytes v)
    (by show BytesAt m.dmem (r.base + BitVec.ofNat 64 o) _; exact h)]
  exact ofInt_ofBytes_wordBytes v

/-- A region pointer of the frame's environment is the frame's byte. -/
theorem eval_ptr {m : MachineData} {vars : Nat → BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (r.env m vars) = r.off o := by
  show r.base + BitVec.ofInt 64 (o : Int) = r.base + BitVec.ofNat 64 o
  simp

/-! ## The registers every state keeps -/

variable (r)

/-- **What every state of the region has**: the layer, the frame, the inputs and spills, `136`,
the hashers' buffers and X27. -/
@[expose] def Base (l : Nat) (m : MachineData) : Prop :=
  l < 3 ∧ r.Frame m ∧ Keep r l m ∧ Run.RegIs m .X19 136 ∧ Run.RegIs m .X21 (r.off 19208) ∧
    Run.RegIs m .X25 (r.off 8840) ∧ Run.RegIs m .X27 (r.off 19008)

variable {r}

/-- The kept registers' symbolic values hold in a state of the region. -/
theorem allOf_keptRegs {l : Nat} {m : MachineData} (hB : Base r l m) (vars : Nat → BitVec 64) :
    AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) keptRegs :=
  ⟨hB.2.2.2.1, hB.2.2.2.2.1.trans (eval_ptr 19208).symm,
    hB.2.2.2.2.2.1.trans (eval_ptr 8840).symm, hB.2.2.2.2.2.2.trans (eval_ptr 19008).symm,
    hB.2.1.2.1.trans (eval_ptr 21520).symm, trivial⟩

/-- **A fresh state** of the region, the kept registers known. -/
theorem match_base (hpre : r.Pre) {l : Nat} {m : MachineData} (hB : Base r l m) :
    Match (r.env m) (init [(21616, true)] (.ptr 0 0) keptRegs) m :=
  r.match_frame hpre hB.2.1 (allOf_keptRegs hB _) trivial trivial trivial

/-- **After a block** that keeps the registers and writes off `0 .. 432` and `440 .. 8224`, below
the saved registers. -/
theorem Base.of_match (hpre : r.Pre) {l : Nat} {m m' : MachineData} (hB : Base r l m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m')
    (hwf : (r.env m vars).WF) (hsp : S.sp = .ptr 0 0) (h29 : S.reg .X29 = some (.ptr 0 21520))
    (hw : Run.frameWrites S = true) (hn1 : Run.noWriteIn S 0 432 = true)
    (hn2 : Run.noWriteIn S 440 7784 = true)
    (h19 : S.reg .X19 = some (.lit 136)) (h21 : S.reg .X21 = some (.ptr 0 19208))
    (h25 : S.reg .X25 = some (.ptr 0 8840)) (h27 : S.reg .X27 = some (.ptr 0 19008)) :
    Base r l m' :=
  ⟨hB.1, Run.Frame.of_match r hpre hB.2.1 hm hwf hsp h29 hw,
    hB.2.2.1.of_low (lowKept_of_match hpre hB.2.1 hm hwf hn1 hn2),
    hm.regs _ _ h19, (hm.regs _ _ h21).trans (eval_ptr 19208),
    (hm.regs _ _ h25).trans (eval_ptr 8840), (hm.regs _ _ h27).trans (eval_ptr 19008)⟩

/-- **After a call** that changed the frame's bytes `a .. a + n` above the inputs and its stack. -/
theorem Base.of_call (hpre : r.Pre) {l : Nat} {m m' : MachineData} (hB : Base r l m)
    (hS : Saved m m') {a n N : Nat} (ha : 8224 ≤ a) (han : a + n ≤ 21520) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Base r l m' :=
  ⟨hB.1, r.frame_of_call hpre hB.2.1 hS han hN hout,
    hB.2.2.1.of_low (lowKept_of_call hpre hB.2.1 ha (by omega) hN hout),
    by unfold Run.RegIs; rw [hS.1 .X19 rfl]; exact hB.2.2.2.1,
    by unfold Run.RegIs; rw [hS.1 .X21 rfl]; exact hB.2.2.2.2.1,
    by unfold Run.RegIs; rw [hS.1 .X25 rfl]; exact hB.2.2.2.2.2.1,
    by unfold Run.RegIs; rw [hS.1 .X27 rfl]; exact hB.2.2.2.2.2.2⟩

end

/-! ## Places and labels -/

public section
variable [ElfHost] {sec k : Nat}

theorem placed_infix {b : List Directive} {j : Nat} (hp : PlacedIn code sec k) (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt (ElfHost.sectionProg sec) (k + j) :=
  hb.trans hp.1 hne

theorem hb134 (hp : PlacedIn code sec k) : b134.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b134Offset) :=
  placed_infix hp b134_in_code (by simp [b134])
theorem hb135 (hp : PlacedIn code sec k) : b135.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b135Offset) :=
  placed_infix hp b135_in_code (by simp [b135])
theorem hb136 (hp : PlacedIn code sec k) : b136.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b136Offset) :=
  placed_infix hp b136_in_code (by simp [b136])
theorem hb137 (hp : PlacedIn code sec k) : b137.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b137Offset) :=
  placed_infix hp b137_in_code (by simp [b137])
theorem hb138 (hp : PlacedIn code sec k) : b138.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b138Offset) :=
  placed_infix hp b138_in_code (by simp [b138])
theorem hb139 (hp : PlacedIn code sec k) : b139.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b139Offset) :=
  placed_infix hp b139_in_code (by simp [b139])
theorem hb140 (hp : PlacedIn code sec k) : b140.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b140Offset) :=
  placed_infix hp b140_in_code (by simp [b140])
theorem hb141 (hp : PlacedIn code sec k) : b141.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b141Offset) :=
  placed_infix hp b141_in_code (by simp [b141])
theorem hb142 (hp : PlacedIn code sec k) : b142.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b142Offset) :=
  placed_infix hp b142_in_code (by simp [b142])
theorem hb143 (hp : PlacedIn code sec k) : b143.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b143Offset) :=
  placed_infix hp b143_in_code (by simp [b143])
theorem hb144 (hp : PlacedIn code sec k) : b144.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b144Offset) :=
  placed_infix hp b144_in_code (by simp [b144])
theorem hb145 (hp : PlacedIn code sec k) : b145.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b145Offset) :=
  placed_infix hp b145_in_code (by simp [b145])
theorem hb148 (hp : PlacedIn code sec k) : b148.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b148Offset) :=
  placed_infix hp b148_in_code (by simp [b148])
theorem hb149 (hp : PlacedIn code sec k) : b149.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b149Offset) :=
  placed_infix hp b149_in_code (by simp [b149])
theorem hb150 (hp : PlacedIn code sec k) : b150.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b150Offset) :=
  placed_infix hp b150_in_code (by simp [b150])
theorem hb151 (hp : PlacedIn code sec k) : b151.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b151Offset) :=
  placed_infix hp b151_in_code (by simp [b151])
theorem hb152 (hp : PlacedIn code sec k) : b152.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b152Offset) :=
  placed_infix hp b152_in_code (by simp [b152])
theorem hb153 (hp : PlacedIn code sec k) : b153.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b153Offset) :=
  placed_infix hp b153_in_code (by simp [b153])
theorem hb156 (hp : PlacedIn code sec k) : b156.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b156Offset) :=
  placed_infix hp b156_in_code (by simp [b156])
theorem hb157 (hp : PlacedIn code sec k) : b157.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b157Offset) :=
  placed_infix hp b157_in_code (by simp [b157])
theorem hb158 (hp : PlacedIn code sec k) : b158.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b158Offset) :=
  placed_infix hp b158_in_code (by simp [b158])
theorem hb159 (hp : PlacedIn code sec k) : b159.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b159Offset) :=
  placed_infix hp b159_in_code (by simp [b159])
theorem hb160 (hp : PlacedIn code sec k) : b160.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b160Offset) :=
  placed_infix hp b160_in_code (by simp [b160])
theorem hb161 (hp : PlacedIn code sec k) : b161.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b161Offset) :=
  placed_infix hp b161_in_code (by simp [b161])
theorem hb162 (hp : PlacedIn code sec k) : b162.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b162Offset) :=
  placed_infix hp b162_in_code (by simp [b162])
theorem hb165 (hp : PlacedIn code sec k) : b165.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b165Offset) :=
  placed_infix hp b165_in_code (by simp [b165])
theorem hb166 (hp : PlacedIn code sec k) : b166.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b166Offset) :=
  placed_infix hp b166_in_code (by simp [b166])
theorem hb167 (hp : PlacedIn code sec k) : b167.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b167Offset) :=
  placed_infix hp b167_in_code (by simp [b167])
theorem hb168 (hp : PlacedIn code sec k) : b168.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b168Offset) :=
  placed_infix hp b168_in_code (by simp [b168])
theorem hb169 (hp : PlacedIn code sec k) : b169.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b169Offset) :=
  placed_infix hp b169_in_code (by simp [b169])
theorem hb170 (hp : PlacedIn code sec k) : b170.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b170Offset) :=
  placed_infix hp b170_in_code (by simp [b170])
theorem hb172 (hp : PlacedIn code sec k) : b172.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b172Offset) :=
  placed_infix hp b172_in_code (by simp [b172])
theorem hb173 (hp : PlacedIn code sec k) : b173.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Sphincs.SphincsVerify.b173Offset) :=
  placed_infix hp b173_in_code (by simp [b173])

theorem lbl_59 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_59 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b144Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_59_at
theorem lbl_61 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_61 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b148Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_61_at
theorem lbl_62 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_62 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b149Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_62_at
theorem lbl_63 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_63 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b150Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_63_at
theorem lbl_67 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_67 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b156Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_67_at
theorem lbl_68 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_68 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b158Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_68_at
theorem lbl_69 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_69 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b159Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_69_at
theorem lbl_73 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_73 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b165Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_73_at
theorem lbl_77 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_77 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b172Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_77_at
theorem lbl_32 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_32 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b92Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_32_at
theorem lbl_84 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_84 = ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b179Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_84_at

end

end NativeRustcArm.SphincsVerifyProof.Tree
