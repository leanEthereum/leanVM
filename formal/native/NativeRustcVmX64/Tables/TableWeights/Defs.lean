module

public import NativeRustcVmX64.Tables.TableWeights.Exec
public import NativeRustcVmX64.Spec.Tables
public import NativeRustcVm.Tables.Weights

/-!
# `table_weights`'s states and the facts they rest on (x86-64)

From the entry `m0` (`out` RDI, the heights RSI, `equality_point` RDX, RCX, `point` R8, R9): the
frame's base `fb m0` (`256` below the entry's RSP, `Field.frameEnv`'s region 0) and its words
(`fw`); the words the loop keeps (`kf`, `Fixed`); the weights' words (`wE`). The states: the
loop head `NativeRustcVmX64.Vm.TableWeights.label_3` after `c` coordinates (`It`), `NativeRustcVmX64.Vm.TableWeights.label_5` with coordinate
`c`'s factor parts (`Pre3`), the return of the multiplication of weight `j - 1` (`Mid`), of
weight `5` (`Done`), the exit `NativeRustcVmX64.Vm.TableWeights.label_6` (`Fin`).
-/

namespace NativeRustcVmX64.Tables.TableWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVm (wordOf wordsOf ewsOf ewOf)

@[expose] public section

variable (m0 : MachineData)

/-- The frame's base. -/
def fb : BitVec 64 := stackBelow m0 256

/-- The frame's word at `o`. -/
def fw (st : MachineData) (o : Nat) : BitVec 64 :=
  (wordOf st.dmem (fb m0 + BitVec.ofNat 64 o)).toBitVec

/-- Height `j`'s word. -/
def hword (j : Nat) : BitVec 64 :=
  (wordOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (8 * j))).toBitVec

/-- The heights. -/
def H : Array Nat := heightsOf m0.dmem (reg m0 .rsi)
/-- The equality point. -/
def E : Array EW := slice m0 (reg m0 .rdx) (reg m0 .rcx)
/-- The point. -/
def P : Array EW := slice m0 (reg m0 .r8) (reg m0 .r9)
/-- The point's length. -/
def n : Nat := (reg m0 .r9).toNat

/-- The weights after `c` coordinates. -/
def W (c : Nat) : Array EW := twPrefix (H m0) (E m0) (P m0) c

/-- Coordinate `c`'s challenge. -/
def ch (c : Nat) : EW := (P m0).getD c 0

/-- Coordinate `c`'s factor in a table taller than `c`. -/
def fac (c : Nat) : EW := 1 + (E m0).getD c 0 + ch m0 c

/-- The point's end. -/
def endp : BitVec 64 := reg m0 .r8 + reg m0 .r9 <<< 4

/-- The frame's words the loop keeps, and their values. -/
def kf : List (Nat × BitVec 64) :=
  [(96, reg m0 .rdi), (104, reg m0 .rdx), (176, reg m0 .rcx), (152, hword m0 0),
    (144, hword m0 1), (136, hword m0 2), (128, hword m0 3), (120, hword m0 4),
    (112, hword m0 5), (168, endp m0), (160, reg m0 .r8)]

/-- The kept words hold their values. -/
def Fixed (st : MachineData) : Prop := ∀ p ∈ kf m0, fw m0 st p.1 = p.2

/-- Weight `i < 5` in the frame. -/
def wE (st : MachineData) (i : Nat) : EW := ewArg (fw m0 st (wlo i)) (fw m0 st (whi i))

/-- A body of the function. -/
abbrev Bd (st : MachineData) : Prop := Body m0 256 tableWeightsStack slots 0 0 st

/-- **The loop head** `NativeRustcVmX64.Vm.TableWeights.label_3`, `c` coordinates done, weight `5` in RAX, RDX. -/
structure It (c : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  lt : c < n m0
  rbx : reg st .rbx = BitVec.ofNat 64 c
  rbp : reg st .rbp = BitVec.ofNat 64 (16 * c)
  r8 : reg st .r8 = reg m0 .r8
  fixed : Fixed m0 st
  w : ∀ i < 5, wE m0 st i = (W m0 c).getD i 0
  w5 : ewRet st = (W m0 c).getD 5 0

/-- Coordinate `c`'s counters and factor parts: R14 the challenge's high limb, R15 and R13 with the
challenge's low limb the factor of a taller table. -/
structure Co (c : Nat) (st : MachineData) : Prop where
  rbx : reg st .rbx = BitVec.ofNat 64 c
  rbp : reg st .rbp = BitVec.ofNat 64 (16 * c)
  r14 : reg st .r14 = (ch m0 c).c1.toBitVec
  tall : ewArg (reg st .r15 ^^^ (ch m0 c).c0.toBitVec) (reg st .r13) = fac m0 c

/-- **`NativeRustcVmX64.Vm.TableWeights.label_5`**: coordinate `c`'s factor parts, weight `5` in the frame. -/
structure Pre3 (c : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  lt : c < n m0
  co : Co m0 c st
  r8 : reg st .r8 = reg m0 .r8
  fixed : Fixed m0 st
  w : ∀ i < 5, wE m0 st i = (W m0 c).getD i 0
  w5 : ewArg (fw m0 st 200) (fw m0 st 192) = (W m0 c).getD 5 0

/-- **After the multiplication of weight `j - 1`** of coordinate `c` (`1 ≤ j ≤ 5`). -/
structure Mid (c j : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  lt : c < n m0
  co : Co m0 c st
  r12 : reg st .r12 = (ch m0 c).c0.toBitVec
  fixed : Fixed m0 st
  cur : fw m0 st 184 = reg m0 .r8 + BitVec.ofNat 64 (16 * c)
  w5 : ewArg (fw m0 st 200) (fw m0 st 192) = (W m0 c).getD 5 0
  done : ∀ i < j - 1, wE m0 st i = (W m0 (c + 1)).getD i 0
  prod : ewRet st = (W m0 (c + 1)).getD (j - 1) 0
  todo : ∀ i, j ≤ i → i < 5 → wE m0 st i = (W m0 c).getD i 0

/-- **After the multiplication of weight `5`** of coordinate `c`. -/
structure Done (c : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  lt : c < n m0
  rbx : reg st .rbx = BitVec.ofNat 64 c
  rbp : reg st .rbp = BitVec.ofNat 64 (16 * c)
  fixed : Fixed m0 st
  cur : fw m0 st 184 = reg m0 .r8 + BitVec.ofNat 64 (16 * c)
  w : ∀ i < 5, wE m0 st i = (W m0 (c + 1)).getD i 0
  w5 : ewRet st = (W m0 (c + 1)).getD 5 0

/-- **The exit** `NativeRustcVmX64.Vm.TableWeights.label_6`: the weights after the whole point. -/
structure Fin (st : MachineData) : Prop where
  body : Bd m0 st
  out : fw m0 st 96 = reg m0 .rdi
  w : ∀ i < 5, wE m0 st i = (W m0 (n m0)).getD i 0
  w5 : ewRet st = (W m0 (n m0)).getD 5 0

end

/-! ## The model -/

public section

variable {m0 : MachineData}

theorem size_H : (H m0).size = 6 := by simp [H, heightsOf, nTables]

theorem size_P : (P m0).size = n m0 := by simp [P, slice, n]

theorem size_E : (E m0).size = (reg m0 .rcx).toNat := by simp [E, slice]

theorem H_getD {j : Nat} (hj : j < 6) : (H m0).getD j 0 = (hword m0 j).toNat := by
  simp [H, heightsOf, hword, nTables, Array.getD, hj, wordsOf]

theorem getD_of_lt {α : Type} {a : Array α} {j : Nat} {d : α} (h : j < a.size) :
    a.getD j d = a[j] := by
  simp [Array.getD, h]

theorem W_succ {c j : Nat} (hc : c < n m0) (hj : j < 6) :
    (W m0 (c + 1)).getD j 0 =
      (W m0 c).getD j 0 * (if c < (H m0).getD j 0 then fac m0 c else ch m0 c) := by
  have hcP : c < (P m0).size := by rw [size_P]; exact hc
  have hW : (twPrefix (H m0) (E m0) (P m0) c).size = 6 := by rw [size_twPrefix, size_H]
  have hs' : (twStep (H m0) (E m0) (twPrefix (H m0) (E m0) (P m0) c) ((P m0)[c], c)).size = 6 := by
    rw [size_twStep _ _ _ _ (by rw [size_twPrefix]), size_H]
  unfold W fac ch
  rw [twPrefix_succ _ _ _ hcP, getD_of_lt (by omega), getElem_twStep,
    getD_of_lt (a := twPrefix (H m0) (E m0) (P m0) c) (by omega),
    getD_of_lt (a := H m0) (by rw [size_H]; omega), getD_of_lt (a := P m0) hcP]

theorem W_succ' {c j : Nat} (hc : c < n m0) (hj : j < 6) :
    (W m0 (c + 1)).getD j 0 =
      EW.mul ((W m0 c).getD j 0) (if c < (H m0).getD j 0 then fac m0 c else ch m0 c) :=
  W_succ hc hj

theorem W_zero {i : Nat} (hi : i < 6) : (W m0 0).getD i 0 = 1 := by
  unfold W
  rw [twPrefix_zero, getD_of_lt (by simp [size_H]; omega)]
  simp

theorem W_size (c : Nat) : (W m0 c).size = 6 := by
  unfold W; rw [size_twPrefix, size_H]

theorem tableWeights_W : tableWeights (H m0) (E m0) (P m0) = W m0 (n m0) := by
  rw [tableWeights_eq, size_P]; rfl

theorem ch_eq {c : Nat} (hc : c < n m0) :
    ch m0 c = (ewsOf m0.dmem (reg m0 .r8) (n m0))[c]'(by simp; exact hc) := by
  have hc' : c < (reg m0 .r9).toNat := hc
  simp only [ch, P, slice, n, getD_of_lt (show c < (ewsOf m0.dmem (reg m0 .r8) (reg m0 .r9).toNat).toArray.size by simpa using hc'), List.getElem_toArray]

theorem E_getD {c : Nat} (hc : c < (reg m0 .rcx).toNat) :
    (E m0).getD c 0 = (ewsOf m0.dmem (reg m0 .rdx) (reg m0 .rcx).toNat)[c]'(by simp; exact hc) := by
  simp only [E, slice, getD_of_lt (show c < (ewsOf m0.dmem (reg m0 .rdx) (reg m0 .rcx).toNat).toArray.size by simpa using hc), List.getElem_toArray]

theorem E_getD_ge {c : Nat} (hc : (reg m0 .rcx).toNat ≤ c) : (E m0).getD c 0 = 0 := by
  unfold E slice
  simp [Array.getD, show ¬ c < (reg m0 .rcx).toNat by omega]

/-! ## Values -/

theorem ewArg_one : ewArg (BitVec.ofNat 64 1) (BitVec.ofNat 64 0) = 1 := rfl

/-- The factor a block passes: a taller table's or the challenge. -/
theorem factor_eq {b : Bool} {r15 r13 r14 p0 : BitVec 64} {fa cc : EW}
    (htall : ewArg (r15 ^^^ p0) r13 = fa) (hshort : ewArg p0 r14 = cc) :
    ewArg ((if b = true then r15 else BitVec.ofNat 64 0) ^^^ p0) (if b = true then r13 else r14) =
      if b = true then fa else cc := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [show BitVec.ofNat 64 0 ^^^ p0 = p0 from BitVec.zero_xor]
    exact hshort
  · simpa using htall

theorem ch_split (x : EW) : ewArg x.c0.toBitVec x.c1.toBitVec = x := rfl

/-- `1 + 0 + p`'s limbs. -/
theorem fac_ge (p : EW) :
    ewArg (BitVec.ofNat 64 1 ^^^ p.c0.toBitVec) p.c1.toBitVec = 1 + 0 + p := by
  rw [BitVec.xor_comm, one_add_ewArg]
  rfl

/-- `1 + e + p`'s limbs. -/
theorem fac_lt (e p : EW) :
    ewArg ((e.c0.toBitVec ^^^ BitVec.ofNat 64 1) ^^^ p.c0.toBitVec)
      (e.c1.toBitVec ^^^ p.c1.toBitVec) = 1 + e + p := by
  rw [ewArg_xor, one_add_ewArg]
  rfl

/-! ## The frame's words -/

variable [Labels]

omit [Labels] in
/-- **A frame word** the environment loads. -/
theorem load_fw {env : Env} {st : MachineData} (h0 : env.regions[0]? = some (fb m0, 264))
    (hd : env.mem0 = st.dmem) (o : Nat) : env.load 0 o 8 = fw m0 st o := by
  rw [load8_eq, Env.base_eq h0, hd]; rfl

/-- **A frame word a block wrote.** -/
theorem fw_write {env : Env} {st' : MachineData} {S : SState} (hm : Match env S st')
    (h0 : env.regions[0]? = some (fb m0, 264)) {o : Nat} (ho : o + 8 ≤ 264) {v : Sym}
    (hw : ∀ t < 8, findWrite 0 (o + t) S.mem = some (v, t)) : fw m0 st' o = v.eval env := by
  have := wordAt_of_write hm h0 ho hw
  unfold fw
  rw [NativeRustcVm.wordOf_of_wordAt this]

/-- **A frame word a block did not write.** -/
theorem fw_keep {env : Env} {st st' : MachineData} {S : SState} (hm : Match env S st')
    (h0 : env.regions[0]? = some (fb m0, 264)) (hd : env.mem0 = st.dmem) {o : Nat}
    (ho : o + 8 ≤ 264) (h : firstOverlap 0 o 8 S.mem = none) : fw m0 st' o = fw m0 st o := by
  unfold fw
  rw [NativeRustcVm.wordOf_congr fun i hi ↦ ?_]
  rw [addr_add, hm.mem 0 (fb m0) 264 h0 (o + i) (by omega)]
  unfold memByte
  rw [findWrite_none h (Nat.le_add_right o i) (by omega), ← addr_add, hd]

omit [Labels] in
/-- A frame word across a call that kept the frame. -/
theorem fw_call {st st' : MachineData} {o : Nat} (ho : o + 8 ≤ 264)
    (h : ∀ j < 256 + 8, st'.dmem.get? (stackBelow m0 256 + BitVec.ofNat 64 j) =
      st.dmem.get? (stackBelow m0 256 + BitVec.ofNat 64 j)) : fw m0 st' o = fw m0 st o := by
  unfold fw
  rw [NativeRustcVm.wordOf_congr fun i hi ↦ ?_]
  rw [addr_add]
  exact h _ (by omega)

omit [Labels] in
/-- A frame word where memory is the same. -/
theorem fw_of_dmem {st st' : MachineData} (h : st'.dmem = st.dmem) (o : Nat) :
    fw m0 st' o = fw m0 st o := by
  unfold fw; rw [h]

/-- `cmp`'s unsigned below of two words. -/
theorem eval_ult (env : Env) (a b : Sym) :
    (SBool.cmp .ult .W64 a b).eval env = decide ((a.eval env).toNat < (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.ult]

/-- `rbx < [h]` for the counter `c` and height `j`'s word. -/
theorem eval_ltH {env : Env} {c j : Nat} (hc : c < 2 ^ 64) (hj : j < 6)
    (hx : env.regs .rbx = BitVec.ofNat 64 c) (hh : env.load 0 (hoff j) 8 = hword m0 j) :
    (ltH (hoff j)).eval env = decide (c < (H m0).getD j 0) := by
  simp only [ltH, SBool.eval, CmpOp.apply, low_W64, BitVec.ult, Sym.eval, hx, hh, H_getD hj,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem eval_facLo (env : Env) (h : Nat) (p : Sym) :
    (facLo h p).eval env =
      (if (ltH h).eval env = true then env.regs .r15 else BitVec.ofNat 64 0) ^^^ p.eval env := by
  simp only [facLo, Sym.eval, xor_eval]

theorem eval_facHi (env : Env) (h : Nat) :
    (facHi h).eval env = if (ltH h).eval env = true then env.regs .r13 else env.regs .r14 := by
  simp only [facHi, Sym.eval]

theorem eval_facLo8 (env : Env) :
    (Sym.bin .xor .W64 (.ite (.not (ltH 112)) (.lit 0) (.reg .r15)) (.reg .r12)).eval env =
      (if (ltH 112).eval env = true then env.regs .r15 else BitVec.ofNat 64 0) ^^^ env.regs .r12 := by
  rcases Bool.eq_false_or_eq_true ((ltH 112).eval env) with h | h <;>
    simp only [Sym.eval, SBool.eval, xor_eval, h] <;> rfl

/-- **The factor** block `j` passes, from coordinate `c`'s parts. -/
theorem factor_block {st : MachineData} {c j : Nat} (hco : Co m0 c st) (hc : c < 2 ^ 64)
    (hj : j < 6) {env : Env} (hregs : env.regs = fun r ↦ reg st r)
    (hh : env.load 0 (hoff j) 8 = hword m0 j) {p0 : BitVec 64}
    (hp0 : p0 = (ch m0 c).c0.toBitVec) :
    ewArg ((if (ltH (hoff j)).eval env = true then env.regs .r15 else BitVec.ofNat 64 0) ^^^ p0)
        (if (ltH (hoff j)).eval env = true then env.regs .r13 else env.regs .r14) =
      if c < (H m0).getD j 0 then fac m0 c else ch m0 c := by
  have hx : env.regs .rbx = BitVec.ofNat 64 c := by rw [hregs]; exact hco.rbx
  rw [eval_ltH hc hj hx hh, hregs]
  have := factor_eq (b := decide (c < (H m0).getD j 0)) (r15 := reg st .r15) (r13 := reg st .r13)
    (r14 := reg st .r14) (p0 := p0) (fa := fac m0 c) (cc := ch m0 c) (by rw [hp0]; exact hco.tall)
    (by rw [hp0, hco.r14]; rfl)
  simpa using this

end

/-! ## Offsets -/

public section

theorem wlo_le (i : Nat) : wlo i ≤ 88 := by unfold wlo; split <;> omega
theorem whi_le (i : Nat) : whi i ≤ 80 := by unfold whi; split <;> omega

theorem mem_wOthers {i j : Nat} (hi : i < 5) (hij : i ≠ j) :
    wlo i ∈ wOthers j ∧ whi i ∈ wOthers j := by
  unfold wOthers
  constructor <;> exact List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr
    ⟨List.mem_range.mpr hi, by simpa using hij⟩, by simp⟩

theorem mem_wAll {i : Nat} (hi : i < 5) : wlo i ∈ wAll ∧ whi i ∈ wAll := by
  unfold wAll
  constructor <;> exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, by simp⟩

theorem kf_fst (m0 : MachineData) : (kf m0).map (·.1) = kfo := by simp [kf, kfo]

theorem kfo_le : ∀ o ∈ kfo, o + 8 ≤ 264 := by decide

variable {m0 : MachineData}

theorem Fixed.get {st : MachineData} (h : Fixed m0 st) {o : Nat} {v : BitVec 64}
    (hp : (o, v) ∈ kf m0) : fw m0 st o = v := by
  have := h (o, v) hp
  exact this

theorem Fixed.hoff {st : MachineData} (h : Fixed m0 st) {j : Nat} (hj : j < 6) :
    fw m0 st (hoff j) = hword m0 j := by
  match j, hj with
  | 0, _ => exact h.get (by simp [kf, TableWeights.hoff])
  | 1, _ => exact h.get (by simp [kf, TableWeights.hoff])
  | 2, _ => exact h.get (by simp [kf, TableWeights.hoff])
  | 3, _ => exact h.get (by simp [kf, TableWeights.hoff])
  | 4, _ => exact h.get (by simp [kf, TableWeights.hoff])
  | 5, _ => exact h.get (by simp [kf, TableWeights.hoff])

/-- **The kept words** across a block that does not write them. -/
theorem Fixed.keep [Labels] {st st' : MachineData} (h : Fixed m0 st) {env : Env} {S : SState}
    (hm : Match env S st') (h0 : env.regions[0]? = some (fb m0, 264)) (hd : env.mem0 = st.dmem)
    (hk : ∀ o ∈ kfo, firstOverlap 0 o 8 S.mem = none) : Fixed m0 st' := by
  intro p hp
  have ho : p.1 ∈ kfo := kf_fst m0 ▸ List.mem_map_of_mem hp
  rw [fw_keep hm h0 hd (kfo_le _ ho) (hk _ ho)]
  exact h p hp

/-- The kept words across a call that kept the frame. -/
theorem Fixed.call {st st' : MachineData} (h : Fixed m0 st)
    (hf : ∀ j < 256 + 8, st'.dmem.get? (stackBelow m0 256 + BitVec.ofNat 64 j) =
      st.dmem.get? (stackBelow m0 256 + BitVec.ofNat 64 j)) : Fixed m0 st' := by
  intro p hp
  have ho : p.1 ∈ kfo := kf_fst m0 ▸ List.mem_map_of_mem hp
  rw [fw_call (kfo_le _ ho) hf]
  exact h p hp

/-- A frame region's description. -/
theorem fr0 (st : MachineData) (rs : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64)
    (ret : BitVec 64) :
    (Env.ofMachine st ((stackBelow m0 256, 256 + 8) :: rs) vars ret).regions[0]? =
      some (fb m0, 264) := rfl

/-- The weights' words of a frame across a call. -/
theorem wE_call {st st' : MachineData} {i : Nat}
    (hf : ∀ j < 256 + 8, st'.dmem.get? (stackBelow m0 256 + BitVec.ofNat 64 j) =
      st.dmem.get? (stackBelow m0 256 + BitVec.ofNat 64 j)) : wE m0 st' i = wE m0 st i := by
  unfold wE
  rw [fw_call (by have := wlo_le i; omega) hf, fw_call (by have := whi_le i; omega) hf]

/-- The weights' words of a frame a block did not write. -/
theorem wE_keep [Labels] {st st' : MachineData} {env : Env} {S : SState}
    (hm : Match env S st') (h0 : env.regions[0]? = some (fb m0, 264)) (hd : env.mem0 = st.dmem)
    {i : Nat} (hlo : firstOverlap 0 (wlo i) 8 S.mem = none)
    (hhi : firstOverlap 0 (whi i) 8 S.mem = none) : wE m0 st' i = wE m0 st i := by
  unfold wE
  rw [fw_keep hm h0 hd (by have := wlo_le i; omega) hlo,
    fw_keep hm h0 hd (by have := whi_le i; omega) hhi]

end

end NativeRustcVmX64.Tables.TableWeights
