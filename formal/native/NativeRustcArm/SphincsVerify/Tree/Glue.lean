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

The blocks' places in the program (`hb143`, ...) and the labels they branch to; what every state
of the region keeps below the scratch (`Tree.Keep`: the inputs and the layer loop's spills, all in
the frame's first 15984 bytes) and how it survives a block or a call that writes above them
(`Tree.LowKept`, `Tree.lowKept_of_match`, `Tree.lowKept_of_call`, `Tree.Keep.of_low`); reading
the environment's loads of known bytes (`Tree.bytes_load`, `Tree.load_word`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

/-! ## Lengths -/

theorem length_wots (w : Nat → UInt64) {l : Nat} (hl : l < 3) :
    ((Signature.fromBytes (sigBytes w)).layers.getD l ⟨0, []⟩).wots.flatten.length = 1024 := by
  rw [length_flatten_const (k := 16)]
  · simp [Signature.fromBytes, hl]
  intro x hx
  simp only [Signature.fromBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hl, Option.map_some, Option.getD_some, List.mem_map,
    List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  apply length_slice
  rw [length_sigBytes]
  interval_cases l <;> simp [sigLayerOff] <;> omega

theorem randomizer_fromBytes' (b : List UInt8) : (Signature.fromBytes b).randomizer = slice b 0 16 :=
  rfl

/-- The parsed signature in memory is 7740 bytes. -/
theorem length_sigMem (w : Nat → UInt64) :
    (sigMem (Signature.fromBytes (sigBytes w))).length = 7740 := by
  rw [sigMem, List.length_append, length_forsMem, List.length_append,
    length_flatten_const (k := 16) (fun x hx ↦ length_of_mem_paths w hx), length_paths,
    List.length_append, length_flatten_const (k := 1028)]
  · rw [randomizer_fromBytes',
      length_slice (b := sigBytes w) (off := 0) (len := 16) (by rw [length_sigBytes]; omega)]
    have h3 : (Signature.fromBytes (sigBytes w)).layers.length = 3 := by
      simp only [Signature.fromBytes, List.length_map, List.length_range]
    rw [List.length_map, h3]
  intro x hx
  simp only [Signature.fromBytes, List.map_map, List.mem_map, List.mem_range,
    Function.comp_def] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  have := length_wots w hl
  simp only [Signature.fromBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hl, Option.map_some, Option.getD_some] at this
  rw [layerMem, List.length_append, this]
  rfl

theorem length_pkBytes (w : Nat → UInt64) : (pkBytes w).length = 32 := by
  rw [pkBytes, Proof.length_wordsBytes]
  simp

variable (r : Run)

/-! ## Below the scratch -/

/-- The frame's first 15984 bytes (the inputs and the spills) are as in `m`. -/
@[expose] def LowKept (m m' : MachineData) : Prop :=
  ∀ i < 15984, m'.dmem.get? (r.off i) = m.dmem.get? (r.off i)

variable {r}

theorem LowKept.refl (m : MachineData) : LowKept r m m := fun _ _ ↦ rfl

theorem LowKept.trans {m₁ m₂ m₃ : MachineData} (h₁ : LowKept r m₁ m₂) (h₂ : LowKept r m₂ m₃) :
    LowKept r m₁ m₃ := fun i hi ↦ (h₂ i hi).trans (h₁ i hi)

theorem LowKept.bytesAt {m m' : MachineData} (hk : LowKept r m m') {o : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off o) bs) (ho : o + bs.length ≤ 15984) : BytesAt m'.dmem (r.off o) bs :=
  fun i hi ↦ by
    rw [Run.off_add, hk _ (by omega), ← Run.off_add]
    exact h i hi

variable (r)

/-- **What the tree region keeps**: the inputs and layer `l`'s spills. -/
@[expose] def Keep (l : Nat) (m : MachineData) : Prop := r.Inputs m ∧ r.LayerSpills l m

variable {r}

theorem Keep.of_low {l : Nat} {m m' : MachineData} (hK : Keep r l m) (hk : LowKept r m m') :
    Keep r l m' := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hK
  have hw : ∀ v : UInt64, (wordBytes v).length = 8 := fun v ↦ length_wordBytes v
  refine ⟨⟨hk.bytesAt h1 (by rw [length_pkBytes]; omega),
    hk.bytesAt h2 (by rw [Run.sig, length_sigMem]), hk.bytesAt h3 (by rw [hw]; omega)⟩,
    hk.bytesAt h4 (by rw [hw]; omega), hk.bytesAt h5 (by rw [hw]; omega),
    hk.bytesAt h6 (by rw [hw]; omega), hk.bytesAt h7 (by rw [hw]; omega),
    hk.bytesAt h8 (by rw [hw]; omega), hk.bytesAt h9 (by rw [hw]; omega),
    hk.bytesAt h10 (by rw [hw]; omega), hk.bytesAt h11 (by rw [hw]; omega),
    hk.bytesAt h12 (by simp [be32]), hk.bytesAt h13 (by simp [be32]),
    hk.bytesAt h14 (by simp [be64])⟩

variable [Labels]

/-- **A block that writes above the inputs** keeps them. -/
theorem lowKept_of_match (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m')
    (hwf : (r.env m vars).WF) (hn : Run.noWriteIn S 0 15984 = true) : LowKept r m m' := by
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
        List.length_singleton] at hn ⊢
      intro w hw
      rcases hn w hw with (h | h) | h
      · exact Or.inl (Or.inl h)
      · by_cases h' : w.off + w.n ≤ i
        · exact Or.inl (Or.inr h')
        · exact Or.inr (by omega)
      · omega)
  have := hb' 0 (by simp)
  simp only [BitVec.add_zero, List.getElem_cons_zero] at this
  rw [this, Option.some_get]

/-- **A call that writes above the inputs** keeps them. -/
theorem lowKept_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : 15984 ≤ a) (han : a + n ≤ 29376) (hN : N ≤ finalizeStack)
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

/-- **What every state of the region has**: the layer, the frame, the inputs and spills, the
hashers' buffers and `136`. -/
@[expose] def Base (l : Nat) (m : MachineData) : Prop :=
  l < 3 ∧ r.Frame m ∧ Keep r l m ∧ Run.RegIs m .X21 (r.off 26968) ∧ Run.RegIs m .X25 (r.off 16600) ∧
    Run.RegIs m .X26 136

variable {r}

/-- The kept registers' symbolic values hold in a state of the region. -/
theorem allOf_keptRegs {l : Nat} {m : MachineData} (hB : Base r l m) (vars : Nat → BitVec 64) :
    AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) keptRegs :=
  ⟨hB.2.2.2.1.trans (eval_ptr 26968).symm, hB.2.2.2.2.1.trans (eval_ptr 16600).symm,
    hB.2.2.2.2.2, hB.2.1.2.1.trans (eval_ptr 29280).symm, trivial⟩

/-- **A fresh state** of the region, the kept registers known. -/
theorem match_base (hpre : r.Pre) {l : Nat} {m : MachineData} (hB : Base r l m) :
    Match (r.env m) (init [(29376, true)] (.ptr 0 0) keptRegs) m :=
  r.match_frame hpre hB.2.1 (allOf_keptRegs hB _) trivial trivial trivial

/-- **After a block** that keeps the registers and writes above the inputs, below the saved
registers. -/
theorem Base.of_match (hpre : r.Pre) {l : Nat} {m m' : MachineData} (hB : Base r l m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m')
    (hwf : (r.env m vars).WF) (hsp : S.sp = .ptr 0 0) (h29 : S.reg .X29 = some (.ptr 0 29280))
    (hw : Run.frameWrites S = true) (hn : Run.noWriteIn S 0 15984 = true)
    (h21 : S.reg .X21 = some (.ptr 0 26968)) (h25 : S.reg .X25 = some (.ptr 0 16600))
    (h26 : S.reg .X26 = some (.lit 136)) : Base r l m' :=
  ⟨hB.1, Run.Frame.of_match r hpre hB.2.1 hm hwf hsp h29 hw,
    hB.2.2.1.of_low (lowKept_of_match hpre hB.2.1 hm hwf hn),
    (hm.regs _ _ h21).trans (eval_ptr 26968), (hm.regs _ _ h25).trans (eval_ptr 16600),
    hm.regs _ _ h26⟩

/-- **After a call** that changed the frame's bytes `a .. a + n` above the inputs and its stack. -/
theorem Base.of_call (hpre : r.Pre) {l : Nat} {m m' : MachineData} (hB : Base r l m)
    (hS : Saved m m') {a n N : Nat} (ha : 15984 ≤ a) (han : a + n ≤ 29280) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Base r l m' :=
  ⟨hB.1, r.frame_of_call hpre hB.2.1 hS han hN hout,
    hB.2.2.1.of_low (lowKept_of_call hpre hB.2.1 ha (by omega) hN hout),
    by unfold Run.RegIs; rw [hS.1 .X21 rfl]; exact hB.2.2.2.1,
    by unfold Run.RegIs; rw [hS.1 .X25 rfl]; exact hB.2.2.2.2.1,
    by unfold Run.RegIs; rw [hS.1 .X26 rfl]; exact hB.2.2.2.2.2⟩

end

/-! ## Places and labels -/

public section
variable [Host] {k : Nat}

theorem placed_infix {b : List Directive} {j : Nat} (hp : Placed code k) (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

theorem hb143 (hp : Placed code k) : b143.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b143Offset) :=
  placed_infix hp b143_in_code (by simp [b143])
theorem hb144 (hp : Placed code k) : b144.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b144Offset) :=
  placed_infix hp b144_in_code (by simp [b144])
theorem hb145 (hp : Placed code k) : b145.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b145Offset) :=
  placed_infix hp b145_in_code (by simp [b145])
theorem hb146 (hp : Placed code k) : b146.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b146Offset) :=
  placed_infix hp b146_in_code (by simp [b146])
theorem hb147 (hp : Placed code k) : b147.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b147Offset) :=
  placed_infix hp b147_in_code (by simp [b147])
theorem hb148 (hp : Placed code k) : b148.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b148Offset) :=
  placed_infix hp b148_in_code (by simp [b148])
theorem hb149 (hp : Placed code k) : b149.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b149Offset) :=
  placed_infix hp b149_in_code (by simp [b149])
theorem hb150 (hp : Placed code k) : b150.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b150Offset) :=
  placed_infix hp b150_in_code (by simp [b150])
theorem hb151 (hp : Placed code k) : b151.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b151Offset) :=
  placed_infix hp b151_in_code (by simp [b151])
theorem hb152 (hp : Placed code k) : b152.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b152Offset) :=
  placed_infix hp b152_in_code (by simp [b152])
theorem hb153 (hp : Placed code k) : b153.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b153Offset) :=
  placed_infix hp b153_in_code (by simp [b153])
theorem hb154 (hp : Placed code k) : b154.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b154Offset) :=
  placed_infix hp b154_in_code (by simp [b154])
theorem hb157 (hp : Placed code k) : b157.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b157Offset) :=
  placed_infix hp b157_in_code (by simp [b157])
theorem hb158 (hp : Placed code k) : b158.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b158Offset) :=
  placed_infix hp b158_in_code (by simp [b158])
theorem hb159 (hp : Placed code k) : b159.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b159Offset) :=
  placed_infix hp b159_in_code (by simp [b159])
theorem hb160 (hp : Placed code k) : b160.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b160Offset) :=
  placed_infix hp b160_in_code (by simp [b160])
theorem hb161 (hp : Placed code k) : b161.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b161Offset) :=
  placed_infix hp b161_in_code (by simp [b161])
theorem hb162 (hp : Placed code k) : b162.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b162Offset) :=
  placed_infix hp b162_in_code (by simp [b162])
theorem hb165 (hp : Placed code k) : b165.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b165Offset) :=
  placed_infix hp b165_in_code (by simp [b165])
theorem hb166 (hp : Placed code k) : b166.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b166Offset) :=
  placed_infix hp b166_in_code (by simp [b166])
theorem hb167 (hp : Placed code k) : b167.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b167Offset) :=
  placed_infix hp b167_in_code (by simp [b167])
theorem hb168 (hp : Placed code k) : b168.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b168Offset) :=
  placed_infix hp b168_in_code (by simp [b168])
theorem hb169 (hp : Placed code k) : b169.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b169Offset) :=
  placed_infix hp b169_in_code (by simp [b169])
theorem hb170 (hp : Placed code k) : b170.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b170Offset) :=
  placed_infix hp b170_in_code (by simp [b170])
theorem hb171 (hp : Placed code k) : b171.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b171Offset) :=
  placed_infix hp b171_in_code (by simp [b171])
theorem hb174 (hp : Placed code k) : b174.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b174Offset) :=
  placed_infix hp b174_in_code (by simp [b174])
theorem hb175 (hp : Placed code k) : b175.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b175Offset) :=
  placed_infix hp b175_in_code (by simp [b175])
theorem hb176 (hp : Placed code k) : b176.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b176Offset) :=
  placed_infix hp b176_in_code (by simp [b176])
theorem hb177 (hp : Placed code k) : b177.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b177Offset) :=
  placed_infix hp b177_in_code (by simp [b177])
theorem hb178 (hp : Placed code k) : b178.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b178Offset) :=
  placed_infix hp b178_in_code (by simp [b178])
theorem hb179 (hp : Placed code k) : b179.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b179Offset) :=
  placed_infix hp b179_in_code (by simp [b179])
theorem hb181 (hp : Placed code k) : b181.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b181Offset) :=
  placed_infix hp b181_in_code (by simp [b181])
theorem hb182 (hp : Placed code k) : b182.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b182Offset) :=
  placed_infix hp b182_in_code (by simp [b182])

theorem lbl_67 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_67 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b153Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_67_at
theorem lbl_69 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_69 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b157Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_69_at
theorem lbl_70 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_70 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b158Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_70_at
theorem lbl_71 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_71 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b159Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_71_at
theorem lbl_75 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_75 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b165Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_75_at
theorem lbl_76 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_76 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b167Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_76_at
theorem lbl_77 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_77 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b168Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_77_at
theorem lbl_81 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_81 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b174Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_81_at
theorem lbl_85 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_85 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b181Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_85_at
theorem lbl_40 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_40 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b101Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_40_at
theorem lbl_92 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_92 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b188Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_92_at

end

end NativeRustcArm.SphincsVerifyProof.Tree
