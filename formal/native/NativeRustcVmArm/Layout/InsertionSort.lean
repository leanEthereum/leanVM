module

public import NativeRustcVmArm.Code.Vm.InsertionSortOfStackOffsets.Names
public import NativeRustcVmArm.Layout.InsertionSort.Exec
public import NativeRustcVmArm.Layout.Body

/-!
# `insertion_sort` (with `stack_offsets`' order) on AArch64

**`insertionSort_spec`**: rustc's `insertion_sort(order, |i, j| …)` (the closure's `sizes` in X2,
X3), placed anywhere in the program, meets `InsertionSortPre`/`InsertionSortPost`: `order` ends as
the model's `insertionSort (sortLt size) order`. A leaf: every block keeps the callee-saved
registers, SP and X0-X3 (`Base`), and writes only `order`.

The outer loop (`.L3`, `Outer`) holds `acc i`, the model's fold after `i` elements; `b4` takes
`a = order[i]` and the inner loop (`.L5`, `Inner`) swaps it down: `b5` loads `b = order[j - 1]`,
`b6`-`b14` decide `lt a b` (`Q`, by `sortLt` of the sizes, `0` past `sizes`), `b15` swaps,
`b16` goes on with `j - 1`. Either exit is `.L2` with `acc (i + 1)` (`AtL2`).
-/

namespace NativeRustcVmArm.Layout.InsertionSort

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InsertionSortOfStackOffsets
open NativeVm.Model NativeRustcArm NativeRustcVm.Layout
open NativeRustcVmArm.Arrays (pc_cond toNat_add_ofNat' load8_eq inRange_mono)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt wordOf_of_wordAt wordOf_congr)

public section

/-! ## The model -/

/-- `order`. -/
abbrev ord (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec
/-- `|order|`. -/
abbrev n (m : MachineData) : Nat := m.regs.X1.toNat
/-- `sizes`. -/
abbrev szs (m : MachineData) : BitVec 64 := m.regs.X2.toBitVec
/-- `|sizes|`. -/
abbrev ns (m : MachineData) : Nat := m.regs.X3.toNat
/-- A block's size, `0` past `sizes`. -/
def sz (m : MachineData) (t : Nat) : Nat := (natsOf m m.regs.X2 (ns m)).getD t 0
/-- The order. -/
abbrev lt (m : MachineData) : Nat → Nat → Bool := sortLt (sz m)
/-- `order` at the entry. -/
abbrev xs0 (m : MachineData) : Array Nat := natsOf m m.regs.X0 (n m)

/-- The model's fold after `i` elements. -/
def acc (m : MachineData) (i : Nat) : Array Nat :=
  (List.range i).foldl (fun a i ↦ swapDown (lt m) a i) (xs0 m)

theorem acc_succ (m : MachineData) (i : Nat) : acc m (i + 1) = swapDown (lt m) (acc m i) i := by
  simp [acc, List.range_succ, List.foldl_append]

theorem size_natsOf (m : MachineData) (a : UInt64) (k : Nat) : (natsOf m a k).size = k := by
  simp [natsOf, wordsOf]

theorem insertionSort_eq (m : MachineData) : insertionSort (lt m) (xs0 m) = acc m (n m) := by
  unfold insertionSort acc
  rw [size_natsOf]

theorem swapDown_succ {lt' : Nat → Nat → Bool} (xs : Array Nat) (j : Nat) :
    swapDown lt' xs (j + 1) = if lt' xs[j + 1]! xs[j]! then
      swapDown lt' (xs.swapIfInBounds (j + 1) j) j else xs := rfl

theorem sz_ge {m : MachineData} {t : Nat} (h : ns m ≤ t) : sz m t = 0 := by
  have : ¬t < (natsOf m m.regs.X2 (ns m)).size := by rw [size_natsOf]; omega
  simp [sz, Array.getD, this]

theorem sz_lt {m : MachineData} {t : Nat} (h : t < ns m) :
    sz m t = (wordOf m.dmem (szs m + BitVec.ofNat 64 (8 * t))).toNat :=
  natsOf_getD m m.regs.X2 h

/-! ## The frame -/

/-- The registers every block keeps. -/
def keepRegs : List XReg :=
  [.X0, .X1, .X2, .X3, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29, .X30]

/-- **The frame**: X0-X3, the callee-saved registers, X30 and SP the entry's; memory the entry's
but in `order`, every byte still mapped. -/
structure Base (m0 st : MachineData) : Prop where
  regs : ∀ r ∈ keepRegs, st.regs.getXReg r = m0.regs.getXReg r
  sp : st.regs.SP = m0.regs.SP
  same : SameOutside m0.dmem st.dmem (InRange (ord m0) (8 * n m0))
  kept : Kept m0.dmem st.dmem

theorem Base.x0 {m0 st : MachineData} (h : Base m0 st) : st.regs.X0 = m0.regs.X0 :=
  h.regs .X0 (by simp [keepRegs])
theorem Base.x1 {m0 st : MachineData} (h : Base m0 st) : st.regs.X1 = m0.regs.X1 :=
  h.regs .X1 (by simp [keepRegs])
theorem Base.x2 {m0 st : MachineData} (h : Base m0 st) : st.regs.X2 = m0.regs.X2 :=
  h.regs .X2 (by simp [keepRegs])
theorem Base.x3 {m0 st : MachineData} (h : Base m0 st) : st.regs.X3 = m0.regs.X3 :=
  h.regs .X3 (by simp [keepRegs])

/-- **A block** keeping the registers and SP, writing only in `order`, keeps the frame. -/
theorem Base.step [Labels] {m0 st st' : MachineData} {rs : List (BitVec 64 × Nat)} {S0 S1 : SState}
    (hb : Base m0 st) (hm0 : Match (Env.ofMachine st rs) S0 st)
    (hm : Match (Env.ofMachine st rs) S1 st') (hwf : (Env.ofMachine st rs).WF)
    (hk : (keepRegs.all fun r ↦ (S0.reg r).isSome && S1.reg r == S0.reg r) = true)
    (hsp : S1.sp = S0.sp)
    (hw : ∀ p, ¬InRange (ord m0) (8 * n m0) p → st'.dmem.get? p = st.dmem.get? p) :
    Base m0 st' := by
  have he := Arrays.regs_eq_of hm0 hm keepRegs hk
  exact ⟨fun r hr ↦ (he r hr).trans (hb.regs r hr), (Match.sp_eq hm0 hm hsp).trans hb.sp,
    fun p hp ↦ (hw p hp).trans (hb.same p hp), fun p hp ↦ hm.kept hwf p (hb.kept p hp)⟩

/-- **The sorted array so far** in `order`: its numbers, words. -/
structure Arr (m0 : MachineData) (cur : Array Nat) (d : Mem 64) : Prop where
  size : cur.size = n m0
  lt64 : ∀ t (h : t < cur.size), cur[t] < 2 ^ 64
  words : WordsAt d (ord m0) (natWords cur)

theorem Arr.word {m0 : MachineData} {cur : Array Nat} {d : Mem 64} (h : Arr m0 cur d) {t : Nat}
    (ht : t < cur.size) : WordAt d (ord m0 + BitVec.ofNat 64 (8 * t)) cur[t].toUInt64 := by
  have := NativeRustcVm.WordsAt.getElem h.words (i := t) (by simp [natWords]; exact ht)
  simpa [natWords] using this

theorem add_ofNat_zero' (a : BitVec 64) : a + BitVec.ofNat 64 0 = a := by simp

theorem toNat_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-! ## Blocks -/

/-- `[p, i, lsl #3]`'s address. -/
theorem idx_eval [Labels] (env : Env) (p i : XReg) :
    (idx p i).eval env = env.regs p + BitVec.ofNat 64 (8 * (env.regs i).toNat) := by
  rw [show idx p i = .bin .add .W64 (.reg p) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg i)) from rfl]
  sym_simp
  congr 1
  simp only [BitVec.apply_mem_extend, BitVec.unsigned]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat, Int.shiftLeft_eq,
    show ((2 : Int) ^ 3) = ((8 : Nat) : Int) from rfl, ← Int.natCast_mul, ← Int.natCast_emod,
    Int.toNat_natCast, Nat.mul_comm]

/-- `p + (i << 3)`. -/
theorem shl3_eval [Labels] (env : Env) (p i : XReg) :
    (shl3 p i).eval env = env.regs p + BitVec.ofNat 64 (8 * (env.regs i).toNat) := by
  simp only [shl3]
  sym_simp
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : MemWidth.W64.bits = 64 := rfl
  simp only [this]
  omega

variable [Host] {k : Nat}

/-- A block without memory, from a fresh state. -/
theorem run_regs {ds : List Directive} {kk : Nat} {S1 : SState} {x : Exit}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds regsS = some (S1, x)) (hmem : S1.mem = [])
    {st : MachineState} (hpc : st.pc = Host.addrOf kk) {R : MachineState → Prop}
    (cont : ∀ st', Match (Env.ofMachine st.data []) S1 st'.data →
      PcOk (Env.ofMachine st.data []) x (Host.addrOf (kk + ds.length)) st' →
      st'.data.dmem = st.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx (Env.wf_nil _) hpc (match_nil _) fun st' hm hpc' ↦
    cont st' hm hpc' (hm.dmem_eq (Env.wf_nil _) hmem)

theorem reg_of {st st' : MachineData} {rs : List (BitVec 64 × Nat)} {S1 : SState}
    (hm : Match (Env.ofMachine st rs) S1 st') {r : XReg} {v : Sym} (h : S1.reg r = some v) :
    st'.regs.getXReg r = UInt64.ofBitVec (v.eval (Env.ofMachine st rs)) :=
  Arrays.reg_of hm h

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.entryOffset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.entry_at
theorem lbl_2 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_2_at
theorem lbl_3 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b3Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b3Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_3_at
theorem lbl_5 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_5_at
theorem lbl_7 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b7Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b7Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_7_at
theorem lbl_8 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b8Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b8Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_8_at
theorem lbl_9 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b9Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b9Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_9_at
theorem lbl_10 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b10Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b10Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_10_at
theorem lbl_12 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_12 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b13Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b13Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_12_at
theorem lbl_13 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b14Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b14Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_13_at
theorem lbl_14 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b15Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b15Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_14_at
theorem lbl_16 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_16 = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b18Offset) := hp.label (j := NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b18Offset) NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.label_16_at

/-! ## The comparison `lt a b` (`b5`-`b14`) -/

/-- The registers the comparison keeps. -/
def cmpRegs : List XReg := keepRegs ++ [.X8, .X9, .X10, .X11, .X12]

/-- **During the comparison** of `a` (X9) with `b = order[j - 1]` (X12): memory `D`. -/
structure Cmp (m0 : MachineData) (D : Mem 64) (i j : Nat) (a b : UInt64) (st : MachineData) :
    Prop where
  base : Base m0 st
  dmem : st.dmem = D
  x8 : st.regs.X8.toNat = i
  x9 : st.regs.X9 = a
  x10 : st.regs.X10.toNat = j
  x11 : st.regs.X11.toBitVec = ord m0 + BitVec.ofNat 64 (8 * j)
  x12 : st.regs.X12 = b

omit [Host] in
theorem Cmp.step [Labels] {m0 st st' : MachineData} {D : Mem 64} {i j : Nat} {a b : UInt64}
    {rs : List (BitVec 64 × Nat)} {S0 S1 : SState} (hc : Cmp m0 D i j a b st)
    (hm0 : Match (Env.ofMachine st rs) S0 st) (hm : Match (Env.ofMachine st rs) S1 st')
    (hwf : (Env.ofMachine st rs).WF)
    (hk : (cmpRegs.all fun r ↦ (S0.reg r).isSome && S1.reg r == S0.reg r) = true)
    (hsp : S1.sp = S0.sp) (hmem : S1.mem = []) : Cmp m0 D i j a b st' := by
  have he := Arrays.regs_eq_of hm0 hm cmpRegs hk
  have hk' : (keepRegs.all fun r ↦ (S0.reg r).isSome && S1.reg r == S0.reg r) = true := by
    simp only [cmpRegs, List.all_append, Bool.and_eq_true] at hk; exact hk.1
  have hd : st'.dmem = st.dmem := hm.dmem_eq hwf hmem
  refine ⟨hc.base.step hm0 hm hwf hk' hsp fun p _ ↦ by rw [hd], hd.trans hc.dmem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show st'.regs.X8 = st.regs.X8 from he .X8 (by simp [cmpRegs])]; exact hc.x8
  · exact (he .X9 (by simp [cmpRegs])).trans hc.x9
  · rw [show st'.regs.X10 = st.regs.X10 from he .X10 (by simp [cmpRegs])]; exact hc.x10
  · rw [show st'.regs.X11 = st.regs.X11 from he .X11 (by simp [cmpRegs])]; exact hc.x11
  · exact (he .X12 (by simp [cmpRegs])).trans hc.x12

/-- Where the comparison ends: `.L2` when `lt a b` fails, the swap `b15` when it holds. -/
def Q (k : Nat) (m0 : MachineData) (D : Mem 64) (i j : Nat) (a b : UInt64) (s : MachineState) :
    Prop :=
  (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2Offset) ∧ Cmp m0 D i j a b s.data ∧ lt m0 a.toNat b.toNat = false) ∨
  (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b15Offset) ∧ Cmp m0 D i j a b s.data ∧ lt m0 a.toNat b.toNat = true)

omit [Host] in
theorem lt_def (m0 : MachineData) (a b : Nat) : lt m0 a b =
    (decide (sz m0 b < sz m0 a) || (decide (sz m0 a = sz m0 b) && decide (a < b))) := rfl

omit [Host] in
/-- A size read in a comparison: `sizes[t]`'s word, the entry's. -/
theorem size_word {m0 st : MachineData} (hpre : InsertionSortPre m0) (hb : Base m0 st) {t : Nat}
    (ht : t < ns m0) :
    Readable st (szs m0 + BitVec.ofNat 64 (8 * t)) 8 ∧
      (wordOf st.dmem (szs m0 + BitVec.ofNat 64 (8 * t))).toNat = sz m0 t := by
  obtain ⟨hro, hrs, hap⟩ := hpre
  have hns : ns m0 = m0.regs.X3.toNat := rfl
  refine ⟨readable_sub hrs hb.kept (by omega), ?_⟩
  rw [sz_lt ht, wordOf_congr fun q hq ↦ hb.same _ ?_]
  rw [NativeRustcVm.addr_add]
  exact Arrays.not_inRange_of_apart (Or.symm hap) hrs.2 hro.2 (by omega)

/-- A load at `[p, r, lsl #3]`: region 0 the word. -/
theorem ld_match {st : MachineData} {p r : XReg} {base : BitVec 64} {t : Nat}
    (hp' : (st.regs.getXReg p).toBitVec = base) (hr : (st.regs.getXReg r).toNat = t)
    (hrd : Readable st (base + BitVec.ofNat 64 (8 * t)) 8) :
    (Env.ofMachine st [(base + BitVec.ofNat 64 (8 * t), 8)]).WF ∧
      Match (Env.ofMachine st [(base + BitVec.ofNat 64 (8 * t), 8)]) (ldS p r) st := by
  refine ⟨Arrays.wf_one hrd.1 hrd.2, match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial
    trivial ⟨?_, trivial⟩⟩
  show (idx p r).eval _ = _
  rw [idx_eval]
  simp only [Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, ofInt_zero, BitVec.add_zero, hp']
  show _ = base + BitVec.ofNat 64 (8 * t)
  rw [show (st.regs.getXReg r).toBitVec.toNat = t from hr]

omit [Host] in
theorem load0 {st : MachineData} {a : BitVec 64} {sz' : Nat} :
    (Env.ofMachine st [(a, sz')]).load 0 0 8 = (wordOf st.dmem a).toBitVec := by
  rw [load8_eq]
  simp

/-- `b12`: `lt a b` fails. -/
theorem l12 (hp : Placed code k) {m0 : MachineData} {D : Mem 64} {i j : Nat} {a b : UInt64}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b12Offset)) (hc : Cmp m0 D i j a b st.data)
    (hlt : lt m0 a.toNat b.toNat = false) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st :=
  run_regs (infix_of b12_in_code (by simp [b12]) hp) run_b12 rfl hpc fun st' hm hpc' _ ↦
    .done _ (Or.inl ⟨by simp only [PcOk] at hpc'; exact hpc'.trans (lbl_2 hp),
      hc.step (match_nil _) hm (Env.wf_nil _) rfl rfl rfl, hlt⟩)

/-- `b14`: `a < b`, the sizes compared for equality. -/
theorem l14 (hp : Placed code k) {m0 : MachineData} {D : Mem 64} {i j : Nat} {a b : UInt64}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b14Offset)) (hc : Cmp m0 D i j a b st.data)
    (h13 : st.data.regs.X13.toNat = sz m0 a.toNat) (h14 : st.data.regs.X14.toNat = sz m0 b.toNat)
    (hns : ¬sz m0 b.toNat < sz m0 a.toNat) (hab : a.toNat < b.toNat) :
    Eventually (step1 Host.exe) (Q k m0 D i j a b) st :=
  run_regs (infix_of b14_in_code (by simp [b14]) hp) run_b14 rfl hpc fun st' hm hpc' _ ↦ by
    have hc' := hc.step (match_nil _) hm (Env.wf_nil _) rfl rfl rfl
    simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b14_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b14Length] at hpc'
    sym_simp at hpc'
    obtain ⟨hy, hn⟩ := pc_ne' hpc'
    simp only [Env.ofMachine_regs] at hy hn
    by_cases he : sz m0 a.toNat = sz m0 b.toNat
    · exact .done _ (Or.inr ⟨hn (by
        show st.data.regs.X13.toNat = st.data.regs.X14.toNat; rw [h13, h14, he]), hc',
        by rw [lt_def, decide_eq_false hns, decide_eq_true he, decide_eq_true hab]; rfl⟩)
    · exact .done _ (Or.inl ⟨(hy (by
        show st.data.regs.X13.toNat ≠ st.data.regs.X14.toNat; rw [h13, h14]; exact he)).trans
        (lbl_2 hp), hc', by rw [lt_def, decide_eq_false hns, decide_eq_false he]; rfl⟩)

/-- `b13`: `b` past `sizes`, `a` compared with `b`. -/
theorem l13 (hp : Placed code k) {m0 : MachineData} {D : Mem 64} {i j : Nat} {a b : UInt64}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b13Offset)) (hc : Cmp m0 D i j a b st.data)
    (h13 : st.data.regs.X13.toNat = sz m0 a.toNat) (hns : ¬sz m0 b.toNat < sz m0 a.toNat)
    (hbn : ns m0 ≤ b.toNat) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st :=
  run_regs (infix_of b13_in_code (by simp [b13]) hp) run_b13 rfl hpc fun st' hm hpc' _ ↦ by
    have hc' := hc.step (match_nil _) hm (Env.wf_nil _) rfl rfl rfl
    simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b13_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b13Length] at hpc'
    sym_simp at hpc'
    obtain ⟨hy, hn⟩ := pc_nult hpc'
    simp only [Env.ofMachine_regs] at hy hn
    have h9 : (st.data.regs.getXReg .X9).toBitVec.toNat = a.toNat := by
      show st.data.regs.X9.toNat = _; rw [hc.x9]
    have h12 : (st.data.regs.getXReg .X12).toBitVec.toNat = b.toNat := by
      show st.data.regs.X12.toNat = _; rw [hc.x12]
    rw [h9, h12] at hy hn
    by_cases hab : a.toNat < b.toNat
    · refine l14 hp (hn hab) hc' ?_ ?_ hns hab
      · rw [show st'.data.regs.X13 = st.data.regs.X13 from Match.reg_eq (match_nil _) hm (r := .X13) rfl rfl]
        exact h13
      · rw [sz_ge hbn]
        exact congrArg UInt64.toNat (UInt64.toBitVec_inj.mp (hm.regs .X14 _ rfl))
    · exact .done _ (Or.inl ⟨(hy hab).trans (lbl_2 hp), hc', by rw [lt_def, decide_eq_false hns, decide_eq_false hab]; simp⟩)

/-- `b11`: `b` in `sizes`, its size read, `a` compared with `b`. -/
theorem l11 (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {D : Mem 64}
    {i j : Nat} {a b : UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b11Offset))
    (hc : Cmp m0 D i j a b st.data) (h13 : st.data.regs.X13.toNat = sz m0 a.toNat)
    (hns : ¬sz m0 b.toNat < sz m0 a.toNat) (hbn : b.toNat < ns m0) :
    Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  obtain ⟨hrd, hw⟩ := size_word hpre hc.base hbn
  obtain ⟨hwf, hm⟩ := ld_match (p := .X2) (r := .X12) (st := st.data)
    (congrArg UInt64.toBitVec hc.base.x2) (by show st.data.regs.X12.toNat = _; rw [hc.x12]) hrd
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hc' := hc.step hm hm' hwf rfl rfl rfl
  simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b11_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b11Length] at hpc'
  sym_simp at hpc'
  obtain ⟨hy, hn⟩ := pc_ult hpc'
  simp only [Env.ofMachine_regs] at hy hn
  have h9 : (st.data.regs.getXReg .X9).toBitVec.toNat = a.toNat := by
    show st.data.regs.X9.toNat = _; rw [hc.x9]
  have h12 : (st.data.regs.getXReg .X12).toBitVec.toNat = b.toNat := by
    show st.data.regs.X12.toNat = _; rw [hc.x12]
  rw [h9, h12] at hy hn
  by_cases hab : a.toNat < b.toNat
  · refine l14 hp ((hy hab).trans (lbl_13 hp)) hc' ?_ ?_ hns hab
    · rw [show st'.data.regs.X13 = st.data.regs.X13 from Match.reg_eq hm hm' (r := .X13) rfl rfl]
      exact h13
    · rw [← hw, show st'.data.regs.X14 = st'.data.regs.getXReg .X14 from rfl,
        reg_of hm' (r := .X14) rfl]
      simp only [Sym.eval, load0, UInt64.toNat_ofBitVec]
      rfl
  · exact l12 hp (hn hab) hc' (by rw [lt_def, decide_eq_false hns, decide_eq_false hab]; simp)

omit [Host] in
theorem x9_toNat {m0 st : MachineData} {D : Mem 64} {i j : Nat} {a b : UInt64}
    (hc : Cmp m0 D i j a b st) : (st.regs.getXReg .X9).toBitVec.toNat = a.toNat := by
  show st.regs.X9.toNat = _; rw [hc.x9]

omit [Host] in
theorem x12_toNat {m0 st : MachineData} {D : Mem 64} {i j : Nat} {a b : UInt64}
    (hc : Cmp m0 D i j a b st) : (st.regs.getXReg .X12).toBitVec.toNat = b.toNat := by
  show st.regs.X12.toNat = _; rw [hc.x12]

omit [Host] in
theorem x3_toNat {m0 st : MachineData} {D : Mem 64} {i j : Nat} {a b : UInt64}
    (hc : Cmp m0 D i j a b st) : (st.regs.getXReg .X3).toBitVec.toNat = ns m0 := by
  show st.regs.X3.toNat = _; rw [hc.base.x3]

/-- `b10`: is `b` in `sizes`? -/
theorem l10 (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {D : Mem 64}
    {i j : Nat} {a b : UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b10Offset))
    (hc : Cmp m0 D i j a b st.data) (h13 : st.data.regs.X13.toNat = sz m0 a.toNat)
    (hns : ¬sz m0 b.toNat < sz m0 a.toNat) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st :=
  run_regs (infix_of b10_in_code (by simp [b10]) hp) run_b10 rfl hpc fun st' hm hpc' _ ↦ by
    have hc' := hc.step (match_nil _) hm (Env.wf_nil _) rfl rfl rfl
    have h13' : st'.data.regs.X13.toNat = sz m0 a.toNat := by
      rw [show st'.data.regs.X13 = st.data.regs.X13 from
        Match.reg_eq (match_nil _) hm (r := .X13) rfl rfl]; exact h13
    simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b10_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b10Length] at hpc'
    sym_simp at hpc'
    obtain ⟨hy, hn⟩ := pc_nult hpc'
    simp only [Env.ofMachine_regs, x12_toNat hc, x3_toNat hc] at hy hn
    by_cases hb : b.toNat < ns m0
    · exact l11 hp hpre (hn hb) hc' h13' hns hb
    · exact l13 hp ((hy hb).trans (lbl_12 hp)) hc' h13' hns (by omega)

/-- `b9`: `a` in `sizes`, its size read, compared with `b`'s. -/
theorem l9 (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {D : Mem 64}
    {i j : Nat} {a b : UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b9Offset))
    (hc : Cmp m0 D i j a b st.data) (h14 : st.data.regs.X14.toNat = sz m0 b.toNat)
    (han : a.toNat < ns m0) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  obtain ⟨hrd, hw⟩ := size_word hpre hc.base han
  obtain ⟨hwf, hm⟩ := ld_match (p := .X2) (r := .X9) (st := st.data)
    (congrArg UInt64.toBitVec hc.base.x2) (x9_toNat hc) hrd
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hc' := hc.step hm hm' hwf rfl rfl rfl
  have h13 : st'.data.regs.X13.toNat = sz m0 a.toNat := by
    rw [← hw, show st'.data.regs.X13 = st'.data.regs.getXReg .X13 from rfl,
      reg_of hm' (r := .X13) rfl]
    simp only [Sym.eval, load0, UInt64.toNat_ofBitVec]
    rfl
  simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b9_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b9Length] at hpc'
  sym_simp at hpc'
  obtain ⟨hy, hn⟩ := pc_ult hpc'
  simp only [Env.ofMachine_regs, load0] at hy hn
  have e14 : (st.data.regs.getXReg .X14).toBitVec.toNat = sz m0 b.toNat := h14
  have e13 : (wordOf st.data.dmem (szs m0 + BitVec.ofNat 64 (8 * a.toNat))).toBitVec.toNat =
      sz m0 a.toNat := hw
  rw [e14, e13] at hy hn
  by_cases hs : sz m0 b.toNat < sz m0 a.toNat
  · exact .done _ (Or.inr ⟨(hy hs).trans (lbl_14 hp), hc',
      by rw [lt_def, decide_eq_true hs]; rfl⟩)
  · exact l10 hp hpre (hn hs) hc' h13 hs

/-- `b7`: `a` past `sizes`, its size `0`. -/
theorem l7 (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {D : Mem 64}
    {i j : Nat} {a b : UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b7Offset))
    (hc : Cmp m0 D i j a b st.data) (han : ns m0 ≤ a.toNat) :
    Eventually (step1 Host.exe) (Q k m0 D i j a b) st :=
  run_regs (infix_of b7_in_code (by simp [b7]) hp) run_b7 rfl hpc fun st' hm hpc' _ ↦ by
    have hc' := hc.step (match_nil _) hm (Env.wf_nil _) rfl rfl rfl
    simp only [PcOk] at hpc'
    refine l10 hp hpre (hpc'.trans (lbl_10 hp)) hc' ?_ (by rw [sz_ge han]; omega)
    rw [sz_ge han]
    exact congrArg UInt64.toNat (UInt64.toBitVec_inj.mp (hm.regs .X13 _ rfl))

/-- `b8`: `b` past `sizes`, its size `0`; is `a` in `sizes`? -/
theorem l8 (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {D : Mem 64}
    {i j : Nat} {a b : UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b8Offset))
    (hc : Cmp m0 D i j a b st.data) (hbn : ns m0 ≤ b.toNat) :
    Eventually (step1 Host.exe) (Q k m0 D i j a b) st :=
  run_regs (infix_of b8_in_code (by simp [b8]) hp) run_b8 rfl hpc fun st' hm hpc' _ ↦ by
    have hc' := hc.step (match_nil _) hm (Env.wf_nil _) rfl rfl rfl
    simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b8_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b8Length] at hpc'
    sym_simp at hpc'
    obtain ⟨hy, hn⟩ := pc_nult hpc'
    simp only [Env.ofMachine_regs, x9_toNat hc, x3_toNat hc] at hy hn
    by_cases ha : a.toNat < ns m0
    · refine l9 hp hpre (hn ha) hc' ?_ ha
      rw [sz_ge hbn]
      exact congrArg UInt64.toNat (UInt64.toBitVec_inj.mp (hm.regs .X14 _ rfl))
    · exact l7 hp hpre ((hy ha).trans (lbl_7 hp)) hc' (by omega)

/-- `b6`: `b` in `sizes`, its size read; is `a` in `sizes`? -/
theorem l6 (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {D : Mem 64}
    {i j : Nat} {a b : UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b6Offset))
    (hc : Cmp m0 D i j a b st.data) (hbn : b.toNat < ns m0) :
    Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  obtain ⟨hrd, hw⟩ := size_word hpre hc.base hbn
  obtain ⟨hwf, hm⟩ := ld_match (p := .X2) (r := .X12) (st := st.data)
    (congrArg UInt64.toBitVec hc.base.x2) (x12_toNat hc) hrd
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hc' := hc.step hm hm' hwf rfl rfl rfl
  have h14 : st'.data.regs.X14.toNat = sz m0 b.toNat := by
    rw [← hw, show st'.data.regs.X14 = st'.data.regs.getXReg .X14 from rfl,
      reg_of hm' (r := .X14) rfl]
    simp only [Sym.eval, load0, UInt64.toNat_ofBitVec]
    rfl
  simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b6_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b6Length] at hpc'
  sym_simp at hpc'
  obtain ⟨hy, hn⟩ := pc_ult hpc'
  simp only [Env.ofMachine_regs, x9_toNat hc, x3_toNat hc] at hy hn
  by_cases ha : a.toNat < ns m0
  · exact l9 hp hpre ((hy ha).trans (lbl_9 hp)) hc' h14 ha
  · exact l7 hp hpre (hn ha) hc' (by omega)

/-! ## The inner loop -/

/-- **The inner loop's head** `.L5`: `a = cur[j]` being swapped down, the result the model's. -/
structure Inner (m0 : MachineData) (i j : Nat) (cur : Array Nat) (st : MachineData) : Prop where
  base : Base m0 st
  x8 : st.regs.X8.toNat = i
  x9 : st.regs.X9 = cur[j]!.toUInt64
  x10 : st.regs.X10.toNat = j
  pos : 1 ≤ j
  le : j ≤ i
  ilt : i < n m0
  arr : Arr m0 cur st.dmem
  goal : swapDown (lt m0) (acc m0 i) i = swapDown (lt m0) cur j

/-- **At `.L2`**: element `i` placed. -/
structure Done (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  x8 : st.regs.X8.toNat = i
  ilt : i < n m0
  arr : Arr m0 (acc m0 (i + 1)) st.dmem

/-- `b5`: `b = order[j - 1]` loaded, on to the comparison. -/
theorem l5 (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {i j : Nat}
    {cur : Array Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Offset))
    (hI : Inner m0 i j cur st.data) :
    Eventually (step1 Host.exe) (Q k m0 st.data.dmem i j cur[j]!.toUInt64
      (cur[j - 1]!.toUInt64)) st := by
  have hsz := hI.arr.size
  have hj1 : j - 1 < cur.size := by have := hI.le; have := hI.ilt; omega
  have hro := hpre.1
  have hrd : Readable st.data (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) 8 :=
    readable_sub hro hI.base.kept (by have := hI.le; have := hI.ilt; have : n m0 = m0.regs.X1.toNat := rfl; omega)
  have hwf := Arrays.wf_one hrd.1 hrd.2 (m := st.data)
  have hm : Match (Env.ofMachine st.data [(ord m0 + BitVec.ofNat 64 (8 * (j - 1)), 8)]) prevS
      st.data := by
    refine match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial ⟨?_, trivial⟩
    show (shl3 .X0 .X10).eval _ = _
    rw [shl3_eval]
    simp only [Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rw [show (st.data.regs.getXReg .X0).toBitVec = ord m0 from congrArg UInt64.toBitVec hI.base.x0,
      show (st.data.regs.getXReg .X10).toBitVec.toNat = j from hI.x10,
      show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
    congr 2
    have := hI.pos
    omega
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hb := hI.arr.word hj1
  have hw : wordOf st.data.dmem (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) = cur[j - 1].toUInt64 :=
    wordOf_of_wordAt hb
  have he := Arrays.regs_eq_of hm hm' [.X8, .X9, .X10] rfl
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have h12 : st'.data.regs.X12 = cur[j - 1]!.toUInt64 := by
    rw [show st'.data.regs.X12 = st'.data.regs.getXReg .X12 from rfl, reg_of hm' (r := .X12) rfl]
    simp only [Sym.eval, load0, UInt64.ofBitVec_toBitVec, hw, getElem!_pos cur (j - 1) hj1]
  have hc : Cmp m0 st.data.dmem i j cur[j]!.toUInt64 cur[j - 1]!.toUInt64 st'.data := by
    refine ⟨hI.base.step hm hm' hwf rfl rfl fun p _ ↦ by rw [hd], hd, ?_, ?_, ?_, ?_, h12⟩
    · rw [show st'.data.regs.X8 = st.data.regs.X8 from he .X8 (by simp)]; exact hI.x8
    · rw [show st'.data.regs.X9 = st.data.regs.X9 from he .X9 (by simp)]; exact hI.x9
    · rw [show st'.data.regs.X10 = st.data.regs.X10 from he .X10 (by simp)]; exact hI.x10
    · show (st'.data.regs.getXReg .X11).toBitVec = _
      rw [hm'.regs .X11 _ rfl]
      show (shl3 .X0 .X10).eval _ = _
      rw [shl3_eval]
      simp only [Env.ofMachine_regs]
      rw [show (st.data.regs.getXReg .X0).toBitVec = ord m0 from congrArg UInt64.toBitVec hI.base.x0,
        show (st.data.regs.getXReg .X10).toBitVec.toNat = j from hI.x10]
  simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Length] at hpc'
  sym_simp at hpc'
  obtain ⟨hy, hn⟩ := pc_nult hpc'
  simp only [Env.ofMachine_regs, load0, hw] at hy hn
  rw [show (st.data.regs.getXReg .X3).toBitVec.toNat = ns m0 from
    congrArg UInt64.toNat hI.base.x3, ← getElem!_pos cur (j - 1) hj1] at hy hn
  by_cases hbn : (cur[j - 1]!.toUInt64).toNat < ns m0
  · exact l6 hp hpre (hn hbn) hc hbn
  · exact l8 hp hpre ((hy hbn).trans (lbl_8 hp)) hc (by omega)

omit [Host] in
/-- **The swap** of `cur[j - 1]` and `cur[j]` in memory. -/
theorem Arr.swap {m0 : MachineData} {cur : Array Nat} {d d' : Mem 64} (h : Arr m0 cur d)
    (hnw : NoWrap (ord m0) (8 * n m0)) {j : Nat} (hj : 1 ≤ j) (hjs : j < cur.size)
    (w0 : WordAt d' (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) cur[j].toUInt64)
    (w1 : WordAt d' (ord m0 + BitVec.ofNat 64 (8 * (j - 1)) + BitVec.ofNat 64 8)
      (cur[j - 1]'(by omega)).toUInt64)
    (hs : ∀ p, ¬InRange (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) 16 p → d'.get? p = d.get? p) :
    Arr m0 (cur.swapIfInBounds j (j - 1)) d' := by
  have hsz := h.size
  unfold NoWrap at hnw
  refine ⟨by rw [Array.size_swapIfInBounds, hsz], fun t ht ↦ ?_, ?_⟩
  · rw [Array.getElem_swapIfInBounds]
    split
    · exact h.lt64 _ _
    · split
      · exact h.lt64 _ _
      · exact h.lt64 _ _
  · rw [NativeRustcVm.wordsAt_iff]
    intro t ht
    have ht' : t < cur.size := by simpa [natWords] using ht
    simp only [natWords, List.getElem_map, Array.getElem_toList]
    rw [Array.getElem_swapIfInBounds]
    split
    · rename_i hc
      obtain ⟨rfl, -⟩ := hc
      rw [NativeRustcVm.addr_add, show 8 * (t - 1) + 8 = 8 * t by omega] at w1
      exact w1
    · split
      · rename_i _ hc
        obtain ⟨rfl, -⟩ := hc
        exact w0
      · rename_i h1 h2
        have h1' : t ≠ j := fun he ↦ h1 ⟨he, by omega⟩
        have h2' : t ≠ j - 1 := fun he ↦ h2 ⟨he, hjs⟩
        refine Arrays.bytesAt_congr (h.word ht') fun q hq ↦ hs _ fun hin ↦ ?_
        have hq8 : q < 8 := by simpa [NativeRustcVm.length_wordBytes] using hq
        have hts : t < n m0 := by omega
        rw [NativeRustcVm.addr_add, inRange_iff (by rw [toNat_add_ofNat' (by omega)]; omega),
          toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)] at hin
        omega

/-- **A turn of the inner loop**: `b` compared, swapped or not. -/
theorem inner (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {i j : Nat}
    {cur : Array Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Offset))
    (hI : Inner m0 i j cur st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2Offset) ∧ Done m0 i s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Offset) ∧ ∃ cur', Inner m0 i (j - 1) cur' s.data)) st := by
  have hsz := hI.arr.size
  have hjl : j < cur.size := by have := hI.le; have := hI.ilt; omega
  have hj1 : j - 1 < cur.size := by omega
  have hpos := hI.pos
  have ha : (cur[j]!.toUInt64).toNat = cur[j] := by
    rw [getElem!_pos cur j hjl]; exact toNat_toUInt64 (hI.arr.lt64 _ _)
  have hb : (cur[j - 1]!.toUInt64).toNat = cur[j - 1] := by
    rw [getElem!_pos cur (j - 1) hj1]; exact toNat_toUInt64 (hI.arr.lt64 _ _)
  have hsd : swapDown (lt m0) cur j = if lt m0 cur[j]! cur[j - 1]! then
      swapDown (lt m0) (cur.swapIfInBounds j (j - 1)) (j - 1) else cur := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact swapDown_succ cur j'
  have hlt : lt m0 (cur[j]!.toUInt64).toNat (cur[j - 1]!.toUInt64).toNat =
      lt m0 cur[j]! cur[j - 1]! := by
    rw [ha, hb, getElem!_pos cur j hjl, getElem!_pos cur (j - 1) hj1]
  refine Eventually.bind (l5 hp hpre hpc hI) fun s hq ↦ ?_
  rcases hq with ⟨hpc', hc, hf⟩ | ⟨hpc', hc, ht⟩
  · -- no swap: `cur` is the result
    refine .done _ (Or.inl ⟨hpc', hc.base, hc.x8, hI.ilt, ?_⟩)
    rw [acc_succ, hI.goal, hsd, ← hlt, hf, hc.dmem]
    exact hI.arr
  · -- `b15`: the swap
    have hro := hpre.1
    have hle := hI.le
    have hil := hI.ilt
    have hnn : n m0 = m0.regs.X1.toNat := rfl
    have hrd : Readable s.data (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) 16 :=
      readable_sub hro hc.base.kept (by omega)
    have hwf := Arrays.wf_one hrd.1 hrd.2 (m := s.data)
    have h8 : ord m0 + BitVec.ofNat 64 (8 * j) =
        ord m0 + BitVec.ofNat 64 (8 * (j - 1)) + BitVec.ofInt 64 8 := by
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
      congr 2; omega
    have hm : Match (Env.ofMachine s.data [(ord m0 + BitVec.ofNat 64 (8 * (j - 1)), 16)]) swapS
        s.data := by
      refine match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial ⟨?_, ?_, trivial⟩
      · show (idx .X0 .X10).eval _ = _
        rw [idx_eval]
        simp only [Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero,
          Option.map_some, Option.getD_some]
        rw [show (s.data.regs.getXReg .X0).toBitVec = ord m0 from
            congrArg UInt64.toBitVec hc.base.x0,
          show (s.data.regs.getXReg .X10).toBitVec.toNat = j from hc.x10]
        exact h8
      · show (s.data.regs.getXReg .X11).toBitVec = _
        simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show (s.data.regs.getXReg .X11).toBitVec = _ from hc.x11]
        exact h8
    refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc' hm
      fun s' hm' hpc'' ↦ ?_
    obtain ⟨hw, hv0, hv1⟩ := after_eq run_b15 ▸ b15_facts
    have hsame := same_of_region hm' hwf (r := 0) rfl hw
    have w0 := Match.wordAt_write hm' (r := 0) (o := 0) rfl (by decide) hv0
    have w1 := Match.wordAt_write hm' (r := 0) (o := 8) rfl (by decide) hv1
    simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at w0 w1
    rw [add_ofNat_zero'] at w0
    rw [show s.data.regs.getXReg .X9 = cur[j]!.toUInt64 from hc.x9,
      getElem!_pos cur j hjl] at w0
    rw [show s.data.regs.getXReg .X12 = cur[j - 1]!.toUInt64 from hc.x12,
      getElem!_pos cur (j - 1) hj1] at w1
    have harr := (hc.dmem ▸ hI.arr).swap hro.2 hpos hjl w0 w1 hsame
    have hbase : Base m0 s'.data := hc.base.step hm hm' hwf rfl rfl fun p hp' ↦ hsame p fun h ↦
      hp' (inRange_mono h (by omega))
    have he := Arrays.regs_eq_of hm hm' [.X8, .X9, .X10] rfl
    have hgoal : swapDown (lt m0) (acc m0 i) i =
        swapDown (lt m0) (cur.swapIfInBounds j (j - 1)) (j - 1) := by
      rw [hI.goal, hsd, ← hlt, ht]; rfl
    simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b15_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b15Length] at hpc''
    sym_simp at hpc''
    obtain ⟨hy, hn⟩ := pc_eq hpc''
    simp only [Env.ofMachine_regs] at hy hn
    have h10 : (s.data.regs.getXReg .X10).toBitVec.toNat = j := hc.x10
    rw [h10] at hy hn
    by_cases h1 : j = 1
    · refine .done _ (Or.inl ⟨(hy (by rw [h1]; rfl)).trans (lbl_2 hp), hbase, ?_, hI.ilt, ?_⟩)
      · rw [show s'.data.regs.X8 = s.data.regs.X8 from he .X8 (by simp)]; exact hc.x8
      · have h0 : j - 1 = 0 := by omega
        rw [acc_succ, hgoal, h0]
        rw [h0] at harr
        exact harr
    · -- `b16`: on with `j - 1`
      refine run_regs (infix_of b16_in_code (by simp [b16]) hp) run_b16 rfl
        (hn (by rw [show (BitVec.ofNat 64 1).toNat = 1 from rfl]; exact h1)) fun s2 hm2 hpc2 hd2 ↦ ?_
      have he2 := Arrays.regs_eq_of (match_nil _) hm2 [.X8, .X9] rfl
      have h12 : (s'.data.regs.getXReg .X12).toBitVec.toNat = j - 1 := by
        rw [hm'.regs .X12 _ rfl]
        sym_simp
        simp only [Env.ofMachine_regs]
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h10]; simp; omega), h10]
        rfl
      simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b16_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b16Length] at hpc2
      sym_simp at hpc2
      obtain ⟨hy2, -⟩ := pc_ult hpc2
      simp only [Env.ofMachine_regs] at hy2
      have hx10' : (s'.data.regs.getXReg .X10).toBitVec.toNat = j := by
        rw [show s'.data.regs.getXReg .X10 = s.data.regs.getXReg .X10 from he .X10 (by simp)]
        exact h10
      refine .done _ (Or.inr ⟨hy2 ?_ |>.trans (lbl_5 hp), cur.swapIfInBounds j (j - 1),
        hbase.step (match_nil _) hm2 (Env.wf_nil _) rfl rfl (fun p _ ↦ by rw [hd2]), ?_, ?_, ?_,
        by omega, by have := hI.le; omega, hI.ilt, hd2 ▸ harr, hgoal⟩)
      · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx10']; simp; omega), hx10']
        show j - 1 % 2 ^ 64 < (s'.data.regs.getXReg .X1).toBitVec.toNat
        rw [show (s'.data.regs.getXReg .X1).toBitVec.toNat = n m0 from
          congrArg UInt64.toNat hbase.x1]
        have := hI.le; have := hI.ilt
        simp; omega
      · rw [show s2.data.regs.X8 = s.data.regs.X8 from (he2 .X8 (by simp)).trans (he .X8 (by simp))]
        exact hc.x8
      · rw [show s2.data.regs.X9 = s.data.regs.X9 from (he2 .X9 (by simp)).trans (he .X9 (by simp)),
          hc.x9, getElem!_pos cur j hjl,
          getElem!_pos _ (j - 1) (by rw [Array.size_swapIfInBounds]; exact hj1),
          Array.getElem_swapIfInBounds]
        split
        · rename_i hc'; omega
        · split
          · rfl
          · rename_i h2; exact absurd ⟨rfl, hjl⟩ h2
      · show (s2.data.regs.getXReg .X10).toBitVec.toNat = _
        rw [hm2.regs .X10 _ rfl]
        exact h12

/-- **The inner loop**, to `.L2`. -/
theorem innerLoop (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {i j : Nat}
    {cur : Array Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Offset))
    (hI : Inner m0 i j cur st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2Offset) ∧ Done m0 i s.data) st := by
  refine Sym.loop (fun j s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b5Offset) ∧ ∃ cur, Inner m0 i j cur s.data)
    (fun j s ⟨hpc, cur, hI⟩ ↦ ?_) ⟨hpc, cur, hI⟩
  refine Eventually.mono (inner hp hpre hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', cur', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨j - 1, by have := hI.pos; omega, hpc', cur', hI'⟩

/-- **The outer loop's head** `.L3`: `i` elements placed. -/
structure Outer (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  x8 : st.regs.X8.toNat = i
  ilt : i < n m0
  arr : Arr m0 (acc m0 i) st.dmem

/-- `b3`, `b4`: element `i` taken, swapped down. -/
theorem outer (hp : Placed code k) {m0 : MachineData} (hpre : InsertionSortPre m0) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b3Offset)) (hO : Outer m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2Offset) ∧ Done m0 i s.data) st := by
  refine run_regs (infix_of b3_in_code (by simp [b3]) hp) run_b3 rfl hpc fun s1 hm1 hpc1 hd1 ↦ ?_
  have hb1 := hO.base.step (match_nil _) hm1 (Env.wf_nil _) rfl rfl fun p _ ↦ by rw [hd1]
  have h8 : s1.data.regs.X8 = st.data.regs.X8 := Match.reg_eq (match_nil _) hm1 (r := .X8) rfl rfl
  simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b3_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b3Length] at hpc1
  sym_simp at hpc1
  obtain ⟨hy, hn⟩ := pc_eq hpc1
  have hx8 : (st.data.regs.getXReg .X8).toBitVec.toNat = i := hO.x8
  simp only [Env.ofMachine_regs, hx8] at hy hn
  by_cases h0 : i = 0
  · refine .done _ ⟨(hy (by rw [h0]; rfl)).trans (lbl_2 hp), hb1, by rw [h8]; exact hO.x8, hO.ilt, ?_⟩
    rw [acc_succ, h0, hd1]
    rw [h0] at hO
    exact hO.arr
  · have hpc2 := hn (by rw [show (BitVec.ofNat 64 0).toNat = 0 from rfl]; exact h0)
    have hsz := hO.arr.size
    have hil := hO.ilt
    have hnn : n m0 = m0.regs.X1.toNat := rfl
    have hrd : Readable s1.data (ord m0 + BitVec.ofNat 64 (8 * i)) 8 :=
      readable_sub hpre.1 hb1.kept (by omega)
    obtain ⟨hwf, hm⟩ := ld_match (p := .X0) (r := .X8) (st := s1.data)
      (congrArg UInt64.toBitVec hb1.x0) (by show s1.data.regs.X8.toNat = i; rw [h8]; exact hO.x8) hrd
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hpc2 hm fun s2 hm2 hpc3 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b4_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b4Length] at hpc3
    have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf rfl
    have hil' : i < (acc m0 i).size := by omega
    refine innerLoop hp hpre hpc3 ⟨hb1.step hm hm2 hwf rfl rfl fun p _ ↦ by rw [hd2], ?_, ?_, ?_,
      Nat.one_le_iff_ne_zero.mpr h0, le_refl _, hO.ilt, by rw [hd2, hd1]; exact hO.arr, rfl⟩
    · rw [show s2.data.regs.X8 = s1.data.regs.X8 from Match.reg_eq hm hm2 (r := .X8) rfl rfl, h8]
      exact hO.x8
    · rw [show s2.data.regs.X9 = s2.data.regs.getXReg .X9 from rfl, reg_of hm2 (r := .X9) rfl]
      simp only [Sym.eval, load0, UInt64.ofBitVec_toBitVec, hd1]
      rw [getElem!_pos _ i hil']
      exact wordOf_of_wordAt (hO.arr.word hil')
    · show (s2.data.regs.getXReg .X10).toBitVec.toNat = i
      rw [hm2.regs .X10 _ rfl]
      show (s1.data.regs.X8).toNat = i
      rw [h8]; exact hO.x8

/-- `insertion_sort`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ InsertionSortPost m0 s.data

/-- `b18`: the return. -/
theorem finish (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b18Offset)) (hb : Base m0 st.data)
    (ha : Arr m0 (acc m0 (n m0)) st.data.dmem) : Eventually (step1 Host.exe) (Post m0) st :=
  run_regs (infix_of b18_in_code (by simp [b18]) hp) run_b18 rfl hpc fun s hm hpc' hd ↦ by
    have hb' := hb.step (match_nil _) hm (Env.wf_nil _) rfl rfl fun p _ ↦ by rw [hd]
    refine .done _ ⟨?_, ?_, fun p hp' ↦ hb'.same p fun h ↦ hp' (Or.inl h), ?_⟩
    · simp only [PcOk] at hpc'
      rw [hpc']
      simp only [retOf]
      rw [show s.data.regs.X30 = m0.regs.X30 from hb'.regs .X30 (by simp [keepRegs])]
    · show WordsAt _ _ (natWords (insertionSort (lt m0) (xs0 m0)))
      rw [insertionSort_eq, hd]; exact ha.words
    · exact ⟨fun r hr ↦ hb'.regs r (by cases r <;> simp_all [calleeSaved, keepRegs]), hb'.sp,
        hb'.kept⟩

omit [Host] in
/-- `order` at the entry. -/
theorem arr0 {m0 : MachineData} (hpre : InsertionSortPre m0) : Arr m0 (acc m0 0) m0.dmem := by
  refine ⟨size_natsOf _ _ _, fun t ht ↦ ?_, ?_⟩
  · simp [acc, xs0, natsOf]
    exact UInt64.toNat_lt _
  · have : natWords (acc m0 0) = wordsOf m0.dmem (ord m0) (n m0) := by
      simp [acc, xs0, natsOf, natWords, List.map_map, Function.comp_def]
    rw [this]
    exact NativeRustcVm.wordsAt_of_mapped hpre.1.1

/-- **`insertion_sort` meets its contract.** -/
theorem insertionSort_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.entryLabel) InsertionSortPre InsertionSortPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hb0 : Base m0 m0 := ⟨fun _ _ ↦ rfl, rfl, fun _ _ ↦ rfl, fun _ h ↦ h⟩
  refine run_regs (st := ⟨m0, _⟩) (infix_of b0_in_code (by simp [b0]) hp) run_b0 rfl rfl
    fun s hm hpc hd ↦ ?_
  have hb := hb0.step (match_nil _) hm (Env.wf_nil _) rfl rfl fun p _ ↦ by rw [hd]
  simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b0_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b0Length] at hpc
  sym_simp at hpc
  obtain ⟨hy, hn⟩ := pc_eq hpc
  simp only [Env.ofMachine_regs] at hy hn
  have hx1 : (m0.regs.getXReg .X1).toBitVec.toNat = n m0 := rfl
  rw [hx1] at hy hn
  by_cases h0 : n m0 = 0
  · refine finish hp ((hy (by rw [h0]; rfl)).trans (lbl_16 hp)) hb ?_
    rw [h0, hd]; exact arr0 hpre
  · refine run_regs (infix_of b1_in_code (by simp [b1]) hp) run_b1 rfl
      (hn (by rw [show (BitVec.ofNat 64 0).toNat = 0 from rfl]; exact h0)) fun s1 hm1 hpc1 hd1 ↦ ?_
    simp only [PcOk] at hpc1
    have hb1 := hb.step (match_nil _) hm1 (Env.wf_nil _) rfl rfl fun p _ ↦ by rw [hd1]
    have hO : Outer m0 0 s1.data := ⟨hb1, by
      show (s1.data.regs.getXReg .X8).toBitVec.toNat = 0
      rw [hm1.regs .X8 _ rfl]; rfl, by omega, by rw [hd1, hd]; exact arr0 hpre⟩
    refine Sym.loop (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b3Offset) ∧ ∃ i, n m0 - i = r ∧ Outer m0 i s.data)
      (fun r s ⟨hpc, i, hr, hO⟩ ↦ ?_) ⟨hpc1.trans (lbl_3 hp), 0, rfl, hO⟩
    refine Eventually.bind (outer hp hpre hpc hO) fun s2 ⟨hpc2, hD⟩ ↦ ?_
    -- `b2`: the next element, or the end
    refine run_regs (infix_of b2_in_code (by simp [b2]) hp) run_b2 rfl hpc2 fun s3 hm3 hpc3 hd3 ↦ ?_
    have hb3 := hD.base.step (match_nil _) hm3 (Env.wf_nil _) rfl rfl fun p _ ↦ by rw [hd3]
    have hx8 : (s3.data.regs.getXReg .X8).toBitVec.toNat = i + 1 := by
      rw [hm3.regs .X8 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs, BitVec.toNat_add,
        show (s2.data.regs.getXReg .X8).toBitVec.toNat = i from hD.x8]
      have := hD.ilt
      simp; omega
    simp only [PcOk, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2_length, NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.b2Length] at hpc3
    sym_simp at hpc3
    obtain ⟨hy3, hn3⟩ := pc_eq hpc3
    simp only [Env.ofMachine_regs] at hy3 hn3
    have hx8' : ((s2.data.regs.getXReg .X8).toBitVec + BitVec.ofNat 64 1).toNat = i + 1 := by
      rw [BitVec.toNat_add, show (s2.data.regs.getXReg .X8).toBitVec.toNat = i from hD.x8]
      have := hD.ilt
      simp; omega
    rw [hx8', show (s2.data.regs.getXReg .X1).toBitVec.toNat = n m0 from
      congrArg UInt64.toNat hD.base.x1] at hy3 hn3
    by_cases hlast : i + 1 = n m0
    · exact Eventually.mono (finish hp ((hy3 hlast).trans (lbl_16 hp)) hb3
        (by rw [← hlast, hd3]; exact hD.arr)) fun _ h ↦ Or.inl h
    · exact .done _ (Or.inr ⟨n m0 - (i + 1), by have := hD.ilt; omega, hn3 hlast, i + 1, rfl,
        hb3, hx8, by have := hD.ilt; omega, by rw [hd3]; exact hD.arr⟩)

end

end NativeRustcVmArm.Layout.InsertionSort
