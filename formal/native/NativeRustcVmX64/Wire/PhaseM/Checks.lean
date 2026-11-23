module

public import NativeRustcVmX64.Wire.PhaseM.Sort

/-!
# `phase_m`: the size checks (x86-64)

`sizes_run`: from the size checks (`Chk`, `b19`), the last position and the height (`b19`), the
leaf width (`b20`), the row width (`b21`), the last position below `2 ^ height` (`b22`), to
`rd_rows`' call (`Pre23`) or to `None`.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk load_ofMachine)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off)
open NativeRustcVmX64.Wire.Decode (eqv_eval ult_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The leaves of the rows. -/
abbrev leavesOf (lw : Nat) (rows : List (List K)) : List (List K) :=
  rows.map fun r ↦ paddedLeaf r lw

/-- The first level's nodes. -/
abbrev nodes0 (qs : List Nat) (lw : Nat) (rows : List (List K)) : List (Nat × Digest) :=
  (sortD qs).zip ((leavesOf lw rows).map fun leaf ↦ keccak256 (leaf.flatMap K.toBytes))

/-- The phase from the climb on. -/
def climbFin (B : List UInt8) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c : Nat) :
    Option (PhaseOut × Nat) :=
  match climbM B height (nodes0 qs lw rows) c with
  | none => none
  | some (sibs, c) =>
    some (⟨height, lw, qs.map (openingAt (sortD qs) (leavesOf lw rows) sibs height)⟩, c)

/-- **At `rd_rows`' call** (`b23`): the sizes checked. -/
structure Pre23 [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw rw c5 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b23Offset)
  chk : Chk m0 bp B c k count qs height lw rw c5 ⟨st.data, Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b19Offset)⟩
  h32 : height ≤ 32
  lw64 : lw ≤ 64
  rwlw : rw ≤ lw
  last : (sortD qs).getLastD 0 < 2 ^ height

end

public section

theorem tail_none_of {B : List UInt8} {qs : List Nat} {height lw rw c : Nat}
    (h : ¬(height ≤ wireMaxHeight ∧ lw ≤ wireMaxLeafWords ∧ rw ≤ lw ∧ sortD qs ≠ [] ∧
      (sortD qs).getLastD 0 < 2 ^ height)) : tail B qs height lw rw c = none := by
  unfold tail
  split
  · rfl
  · contradiction

theorem tail_ok {B : List UInt8} {qs : List Nat} {height lw rw c : Nat}
    (h : height ≤ wireMaxHeight ∧ lw ≤ wireMaxLeafWords ∧ rw ≤ lw ∧ sortD qs ≠ [] ∧
      (sortD qs).getLastD 0 < 2 ^ height) : tail B qs height lw rw c =
    match rdRows B rw (sortD qs).length c with
    | none => none
    | some (rows, c) =>
      if 0 < rw ∧ ∀ r ∈ rows, r.getD 0 0 = 0 then none else climbFin B qs height lw rows c := by
  unfold tail climbFin
  split
  · contradiction
  · rfl

theorem getLastD_eq {l : List Nat} (h : 0 < l.length) :
    l.getLastD 0 = l[l.length - 1] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rfl

/-- `x > y`. -/
theorem gtC_eval [Labels] (env : Sym.Env) (x y : Sym) :
    (gtC x y).eval env = decide ((y.eval env).toNat < (x.eval env).toNat) := by
  simp only [gtC, SBool.eval]
  rw [ult_eval, eqv_eval]
  by_cases h : (y.eval env).toNat < (x.eval env).toNat
  · rw [decide_eq_true h, decide_eq_false (by omega), decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h]
    by_cases h' : (x.eval env).toNat < (y.eval env).toNat
    · rw [decide_eq_true h']; rfl
    · rw [decide_eq_false h', decide_eq_true (by omega)]; rfl

theorem shr_small (x y : BitVec 64) (hy : y.toNat ≤ 32) :
    (BinOp.apply .shr .W64 x y).toNat = x.toNat / 2 ^ y.toNat := by
  have hs : shiftCount .W64 y = y.toNat := by
    unfold shiftCount shiftMask
    rw [toNat_low, show Width.W8.bits = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)
  simp only [BinOp.apply, low_W64, ext_W64, hs]
  show (x >>> y.toNat).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem and_self_apply (x : BitVec 64) : BinOp.apply .and .W64 x x = x := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The size checks** (`b19` to `b22`). -/
theorem sizes_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count : Nat} {qs : List Nat}
    {height lw rw c5 : Nat} {st : MachineState} (h : Chk m0 bp B c k count qs height lw rw c5 st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      Pre23 m0 bp B c k count qs height lw rw c5 st') st := by
  obtain ⟨hpc, hbod, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hps0, hps256, hf40, hf32, hf16,
    hf24, hbp, hdi, hbx, h15, hqW, hpW, hrd⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hne : sortD qs ≠ [] := List.ne_nil_of_length_pos hps0
  -- `b19`: the last position, shifted by the height.
  have hon : 2048 + 8 * ((sortD qs).length - 1) + 8 ≤ 483584 := by omega
  have hwl : (wa m0 (2048 + 8 * ((sortD qs).length - 1))).toNat =
      (WK m0).toNat + (2048 + 8 * ((sortD qs).length - 1)) := G.wa (by omega)
  have hw2 : (wa m0 2048).toNat = (WK m0).toNat + 2048 := G.wa (by omega)
  have hm19 : Match (aEnv m0 st.data (2048 + 8 * ((sortD qs).length - 1)) 8
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b19Offset + b19.length)).toBitVec) lastS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st.data .rdi)
            (BinOp.apply .mul .W64 (reg st.data .rbp) (BitVec.ofNat 64 8)) =
          wa m0 (2048 + 8 * ((sortD qs).length - 1)) + BitVec.ofInt 64 8
        rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul,
          BitVec.toNat_ofNat, hdi, hbp, hw2, hwl]
        omega, trivial⟩
  have hwf19 := aEnv_wf G hbod.fr.kept (o := 2048 + 8 * ((sortD qs).length - 1)) (n := 8) hon
    (by omega) (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b19Offset + b19.length)).toBitVec
  obtain ⟨hmid19, hmem19, hax19, hk19⟩ := ok_b19
  refine ablk hp G b19_in_code (by simp [b19]) exit_b19 hon (by omega) hmid19
    (fun w hw ↦ by rw [hmem19] at hw; simp at hw)
    (hk19 .r12 (by simp)) (hk19 .r14 (by simp)) hpc hbod hm19
    fun s1 hb1 _ _ _ hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf19 hmem19
  have hl32 : (aEnv m0 st.data (2048 + 8 * ((sortD qs).length - 1)) 8
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b19Offset + b19.length)).toBitVec).load 0 32 8 = height.toUInt64.toBitVec :=
    load_ofMachine (o := 32) rfl hf32
  have hh : height.toUInt64.toBitVec.toNat = height := by
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hlast : (aEnv m0 st.data (2048 + 8 * ((sortD qs).length - 1)) 8
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b19Offset + b19.length)).toBitVec).load 1 0 8 =
      ((sortD qs).getLastD 0).toUInt64.toBitVec := by
    refine load_ofMachine (o := 0) (b := wa m0 (2048 + 8 * ((sortD qs).length - 1))) rfl ?_
    rw [off_zero, getLastD_eq hps0]
    have := NativeRustcVm.WordsAt.getElem hpW (i := (sortD qs).length - 1) (by simp; omega)
    simpa [wa, off_off] using this
  have hlt : (sortD qs).getLastD 0 < 2 ^ 32 := by
    rw [getLastD_eq hps0]
    exact sortD_lt hqlt _ (List.getElem_mem _)
  have hc19 : (gtC (.load 0 32 8) (.lit 32)).eval (aEnv m0 st.data
      (2048 + 8 * ((sortD qs).length - 1)) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b19Offset + b19.length)).toBitVec) =
      decide (32 < height) := by
    rw [gtC_eval]
    exact decide_eq_decide.mpr (by simp only [Sym.eval]; rw [hl32, hh]; exact Iff.rfl)
  simp only [PcOk, hc19] at hpc1
  by_cases h1 : 32 < height
  · simp only [h1, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc1
    refine Eventually.mono (none_run hp G hR0 hpc1 hb1 ?_) fun _ h ↦ .inl h
    rw [hmod]; exact tail_none_of (by unfold wireMaxHeight; omega)
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hrax1 : reg s1.data .rax = BinOp.apply .shr .W64 ((sortD qs).getLastD 0).toUInt64.toBitVec
      height.toUInt64.toBitVec := by
    rw [show reg s1.data .rax = _ from hm1.regs .rax _ hax19]
    simp only [Sym.eval]
    rw [hlast, hl32]
  -- `b20`: the leaf width.
  obtain ⟨hok20, hk20⟩ := ok_b20
  refine fblk hp G b20_in_code (by simp [b20]) exit_b20 nofun hok20 (hk20 .r12 (by simp))
    (hk20 .r14 (by simp)) (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b19_next)) hb1
    fun s2 hb2 hd2 hm2 hpc2 ↦ ?_
  have hl16 : (frameEnv m0 s1.data 160 []).load 0 16 8 = lw.toUInt64.toBitVec :=
    load_ofMachine (o := 16) rfl (by rw [hd1]; exact hf16)
  have hlw : lw.toUInt64.toBitVec.toNat = lw := by
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hc20 : (gtC (.load 0 16 8) (.lit 64)).eval (frameEnv m0 s1.data 160 []) =
      decide (64 < lw) := by
    rw [gtC_eval]
    exact decide_eq_decide.mpr (by simp only [Sym.eval]; rw [hl16, hlw]; exact Iff.rfl)
  simp only [PcOk, hc20] at hpc2
  by_cases h2 : 64 < lw
  · simp only [h2, decide_true, ↓reduceIte] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc2
    refine Eventually.mono (none_run hp G hR0 hpc2 hb2 ?_) fun _ h ↦ .inl h
    rw [hmod]; exact tail_none_of (by unfold wireMaxLeafWords; omega)
  simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
  -- `b21`: the row width.
  obtain ⟨hok21, hk21⟩ := ok_b21
  refine fblk hp G b21_in_code (by simp [b21]) exit_b21 nofun hok21 (hk21 .r12 (by simp))
    (hk21 .r14 (by simp)) (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b20_next)) hb2
    fun s3 hb3 hd3 hm3 hpc3 ↦ ?_
  have rk2 : ∀ x ∈ [Reg64.rax, .rdi, .rbp, .r15], reg s2.data x = reg s1.data x := fun x hx ↦
    hm2.regs x _ (hk20 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp))
  have rk1 : ∀ x ∈ [Reg64.rdi, .rbp, .r15], reg s1.data x = reg st.data x := fun x hx ↦
    hm1.regs x _ (hk19 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp))
  have hc21 : (gtC (.reg .r15) (.load 0 16 8)).eval (frameEnv m0 s2.data 160 []) =
      decide (lw < rw) := by
    rw [gtC_eval]
    refine decide_eq_decide.mpr ?_
    simp only [Sym.eval]
    rw [load_ofMachine (o := 16) rfl (by rw [hd2, hd1]; exact hf16), hlw]
    show lw < (reg s2.data .r15).toNat ↔ _
    rw [rk2 .r15 (by simp), rk1 .r15 (by simp), h15]
  simp only [PcOk, hc21] at hpc3
  by_cases h3 : lw < rw
  · simp only [h3, decide_true, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [hmod]; exact tail_none_of (by omega)
  simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `b22`: the last position below `2 ^ height`.
  obtain ⟨hok22, hk22⟩ := ok_b22
  refine fblk hp G b22_in_code (by simp [b22]) exit_b22 nofun hok22 (hk22 .r12 (by simp))
    (hk22 .r14 (by simp)) (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b21_next)) hb3
    fun s4 hb4 hd4 hm4 hpc4 ↦ ?_
  have rk3 : ∀ x ∈ [Reg64.rax, .rdi, .rbp, .r15], reg s3.data x = reg s2.data x := fun x hx ↦
    hm3.regs x _ (hk21 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp))
  have rk4 : ∀ x ∈ [Reg64.rdi, .rbp, .r15], reg s4.data x = reg s3.data x := fun x hx ↦
    hm4.regs x _ (hk22 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp))
  have hrax3 : (reg s3.data .rax).toNat = (sortD qs).getLastD 0 / 2 ^ height := by
    rw [rk3 .rax (by simp), rk2 .rax (by simp), hrax1, shr_small _ _ (by rw [hh]; omega), hh,
      UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hc22 : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rax) (.reg .rax)) (.lit 0)).not.eval
      (frameEnv m0 s3.data 160 []) = !decide ((sortD qs).getLastD 0 < 2 ^ height) := by
    show (!CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg s3.data .rax) (reg s3.data .rax))
      (BitVec.ofNat 64 0)) = _
    rw [and_self_apply, eqv_eval]
    have e : (reg s3.data .rax).toNat = (BitVec.ofNat 64 0).toNat ↔
        (sortD qs).getLastD 0 < 2 ^ height := by
      rw [hrax3, BitVec.toNat_ofNat, Nat.zero_mod]
      exact Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)
    simp only [e]
  simp only [PcOk, hc22] at hpc4
  by_cases h4 : (sortD qs).getLastD 0 < 2 ^ height
  · simp only [h4, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    have hd : s4.data.dmem = st.data.dmem := hd4.trans (hd3.trans (hd2.trans hd1))
    have hbx4 : reg s4.data .rbx = reg st.data .rbx := by
      rw [show reg s4.data .rbx = reg s3.data .rbx from hm4.regs .rbx (.reg .rbx) (by decide +kernel),
        show reg s3.data .rbx = reg s2.data .rbx from hm3.regs .rbx (.reg .rbx) (by decide +kernel),
        show reg s2.data .rbx = reg s1.data .rbx from hm2.regs .rbx (.reg .rbx) (by decide +kernel)]
      exact hm1.regs .rbx (.reg .rbx) (by decide +kernel)
    have rk : ∀ x ∈ [Reg64.rdi, .rbp, .r15], reg s4.data x = reg st.data x := fun x hx ↦ by
      rw [rk4 x hx, rk3 x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl <;> simp), rk2 x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl <;> simp), rk1 x hx]
    exact .done _ (.inr ⟨hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b22_next),
      ⟨rfl, hb4, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hps0, hps256,
        by rw [hd]; exact hf40, by rw [hd]; exact hf32, by rw [hd]; exact hf16,
        by rw [hd]; exact hf24, by rw [rk .rbp (by simp)]; exact hbp,
        by rw [rk .rdi (by simp)]; exact hdi, by rw [hbx4]; exact hbx,
        by rw [rk .r15 (by simp)]; exact h15, by rw [hd]; exact hqW, by rw [hd]; exact hpW,
        by rw [hd]; exact hrd⟩, by omega, by omega, by omega, h4⟩)
  · simp only [h4, decide_false, Bool.not_false, ↓reduceIte] at hpc4
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc4
    refine Eventually.mono (none_run hp G hR0 hpc4 hb4 ?_) fun _ h ↦ .inl h
    rw [hmod]; exact tail_none_of fun ⟨_, _, _, _, h⟩ ↦ h4 h

end

end NativeRustcVmX64.Wire.PhaseM
