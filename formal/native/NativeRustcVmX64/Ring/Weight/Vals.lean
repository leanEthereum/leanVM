module

public import NativeRustcVmX64.Ring.Weight.Basic
public import NativeRustcVmX64.Arrays.Common

/-!
# `ring_weight`: the values its blocks compute (x86-64)

The symbolic values of `NativeRustcVmX64.Ring.Weight.Exec` (`sumX`, `and25`, `end15`, `min16`, `k16`,
`fA`, `fB`, …) and the branch conditions, evaluated: numbers below `37` by the kernel over each
value (`shl4_eval`, `and25_eval`, `odd_eval`), the rest by `BitVec` arithmetic. The arguments'
elements (`re`, `qe`, `ce`) loaded from a window (`win_c0`, `win_c1`); the model's side: a factor's
limbs (`fac_eq`); the links' values (`wv`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Arrays (add_eval xor_eval beq_ofNat beq_add_left)

public section

/-! ## Small numbers -/

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem shl4_eval (x : BitVec 64) (hx : x.toNat ≤ 36) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  have h : ∀ n < 37, BinOp.apply .shl .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (16 * n) := by decide +kernel
  have := h x.toNat (by omega)
  rwa [ofNat_toNat'] at this

theorem and25_eval (x : BitVec 64) (hx : x.toNat ≤ 36) :
    BinOp.apply .and .W32 (UnOp.apply .trunc .W32 x) (BitVec.ofNat 64 62) =
      BitVec.ofNat 64 (x.toNat / 2 * 2) := by
  have h : ∀ n < 37, BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 n))
      (BitVec.ofNat 64 62) = BitVec.ofNat 64 (n / 2 * 2) := by decide +kernel
  have := h x.toNat (by omega)
  rwa [ofNat_toNat'] at this

theorem odd_eval (x : BitVec 64) (hx : x.toNat ≤ 36) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) =
      decide (x.toNat % 2 = 0) := by
  have h : ∀ n < 37, CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BitVec.ofNat 64 n)
      (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) = decide (n % 2 = 0) := by decide +kernel
  have := h x.toNat (by omega)
  rwa [ofNat_toNat'] at this

theorem beq_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  rw [beq_ofNat _ hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-! ## Symbolic values -/

section
variable [Labels] (env : Env)

theorem ev_shl4 {a : Sym} {x : BitVec 64} (ha : a.eval env = x) (hx : x.toNat ≤ 36) :
    (Sym.bin .shl .W64 a (.lit 4)).eval env = BitVec.ofNat 64 (16 * x.toNat) := by
  show BinOp.apply .shl .W64 (a.eval env) (BitVec.ofNat 64 4) = _
  rw [ha, shl4_eval x hx]

theorem ev_and25 {x : BitVec 64} (ha : env.vars 11 = x) (hx : x.toNat ≤ 36) :
    and25.eval env = BitVec.ofNat 64 (x.toNat / 2 * 2) := by
  show BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (env.vars 11)) (BitVec.ofNat 64 62) = _
  rw [ha, and25_eval x hx]

theorem ev_end15 {b : BitVec 64} {n : Nat} (hb : env.base 0 = b)
    (h14 : env.vars 14 = BitVec.ofNat 64 n) :
    end15.eval env = b + BitVec.ofNat 64 (48 + n) := by
  show BinOp.apply .add .W64 (BitVec.ofNat 64 40)
    (BinOp.apply .add .W64 (env.base 0 + BitVec.ofInt 64 8) (env.vars 14)) = _
  rw [add_eval, add_eval, hb, h14, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
  bv_omega

theorem ev_min16 {x y : BitVec 64} (h11 : env.vars 11 = x) (h13 : env.vars 13 = y) :
    min16.eval env = BitVec.ofNat 64 (min x.toNat y.toNat) := by
  show (if CmpOp.apply .ult .W64 (env.vars 13) (env.vars 11) then env.vars 13 else env.vars 11) = _
  rw [h11, h13]
  simp only [CmpOp.apply, low_W64]
  apply BitVec.eq_of_toNat_eq
  split <;> rename_i h <;> simp only [BitVec.ult_iff_lt, BitVec.lt_def] at h <;>
    simp only [BitVec.toNat_ofNat] <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega

theorem ev_k16 {k : Nat} (h19 : env.vars 19 = BitVec.ofNat 64 (16 * k)) :
    k16.eval env = BitVec.ofNat 64 (16 * (k + 1)) := by
  show BinOp.apply .add .W64 (BitVec.ofNat 64 16) (env.vars 19) = _
  rw [add_eval, h19]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ev_xor (a b : Sym) : (Sym.bin .xor .W64 a b).eval env = a.eval env ^^^ b.eval env :=
  xor_eval _ _

theorem ev_shl4' {a : Sym} {n : Nat} (ha : a.eval env = BitVec.ofNat 64 n) (hn : n ≤ 36) :
    (Sym.bin .shl .W64 a (.lit 4)).eval env = BitVec.ofNat 64 (16 * n) := by
  rw [ev_shl4 env ha (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ev_fA (i : Nat) : (fA i).eval env =
    (env.load 0 (48 + 16 * i) 8 ^^^ env.load 1 (16 * i) 8) ^^^ BitVec.ofNat 64 1 := by
  simp only [fA, ev_xor]
  rfl

theorem ev_fB (i : Nat) : (fB i).eval env = env.load 1 (16 * i + 8) 8 ^^^ env.load 0 (56 + 16 * i) 8 := by
  simp only [fB, ev_xor]
  rfl

theorem ev_t20 : t20.eval env = env.vars 20 ^^^ env.vars 24 := ev_xor env _ _
theorem ev_t21 : t21.eval env = env.vars 21 ^^^ env.vars 23 := ev_xor env _ _

/-- A coefficient's window's alias. -/
theorem ev_kal {a : BitVec 64} {n : Nat} (h9 : env.vars 9 = a)
    (h19 : env.vars 19 = BitVec.ofNat 64 (16 * n)) (hb : env.base 1 = a + BitVec.ofNat 64 (16 * n)) :
    (Sym.bin .add .W64 (.var 9) (.var 19)).eval env = env.base 1 + BitVec.ofInt 64 0 := by
  show BinOp.apply .add .W64 (env.vars 9) (env.vars 19) = _
  rw [add_eval, h9, h19, hb]
  simp

/-! ## Conditions -/

theorem cv_test (v : Sym) {n : Nat} (hv : (v.eval env).toNat = n) :
    (SBool.cmp .eq .W64 (.bin .and .W64 v v) (.lit 0)).eval env = decide (n = 0) := by
  rw [NativeRustcVmX64.Arrays.eval_test, beq_ofNat _ (by decide), hv]

theorem cv_ne {a : Sym} {x c : Nat} (ha : a.eval env = BitVec.ofNat 64 x) (hx : x < 2 ^ 64)
    (hc : c < 2 ^ 64) :
    (SBool.not (.cmp .eq .W64 a (.lit c))).eval env = decide (x ≠ c) := by
  rw [NativeRustcVmX64.Arrays.eval_not, NativeRustcVmX64.Arrays.eval_cmp_eq, ha]
  show (!(BitVec.ofNat 64 x == BitVec.ofNat 64 c)) = _
  rw [beq_nat hx hc, decide_not]

theorem cv_odd {x : BitVec 64} (h11 : env.vars 11 = x) (hx : x.toNat ≤ 36) :
    (SBool.cmp .eq .W8 (.bin .and .W8 (.var 11) (.lit 1)) (.lit 0)).eval env =
      decide (x.toNat % 2 = 0) := by
  show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (env.vars 11) (BitVec.ofNat 64 1))
    (BitVec.ofNat 64 0) = _
  rw [h11, odd_eval x hx]

theorem cv_slot {b : BitVec 64} {j n : Nat} (hb : env.base 0 = b)
    (h15 : env.vars 15 = b + BitVec.ofNat 64 (48 + 16 * n)) (hj : j < 36) (hn : n ≤ 36) :
    (SBool.not (.cmp .eq .W64 (.ptr 0 ((64 + 16 * j : Nat) : Int)) (.var 15))).eval env =
      decide (j + 1 ≠ n) := by
  rw [NativeRustcVmX64.Arrays.eval_not, NativeRustcVmX64.Arrays.eval_cmp_eq]
  show (!(env.base 0 + BitVec.ofInt 64 ((64 + 16 * j : Nat) : Int) == env.vars 15)) = _
  rw [hb, h15, BitVec.ofInt_natCast, beq_add_left, beq_nat (by omega) (by omega), decide_not]
  congr 1
  exact decide_eq_decide.mpr (by omega)

end

/-! ## The arguments' elements -/

section
variable {m0 : MachineData}

/-- Element `i` of `r`, of `r'`, of the coefficients. -/
abbrev re (m0 : MachineData) (i : Nat) : EW :=
  NativeRustcVm.ewOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * i))
abbrev qe (m0 : MachineData) (i : Nat) : EW :=
  NativeRustcVm.ewOf m0.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * i))
abbrev ce (m0 : MachineData) (i : Nat) : EW :=
  NativeRustcVm.ewOf m0.dmem (reg m0 .r9 + BitVec.ofNat 64 (16 * i))

theorem rL_getD {i : Nat} (hi : i < nR m0) : (rL m0).getD i 0 = re m0 i := getD_slice _ _ _ hi
theorem qL_getD {i : Nat} (hi : i < nQ m0) : (qL m0).getD i 0 = qe m0 i := getD_slice _ _ _ hi
theorem cL_getD {i : Nat} (hi : i < 64) : (cL m0).getD i 0 = ce m0 i :=
  getD_arr _ _ (n := coeffCount) hi

theorem size_rL : (rL m0).size = nR m0 := by simp [slice]
theorem size_qL : (qL m0).size = nQ m0 := by simp [slice]
theorem size_cL : (cL m0).size = 64 := by simp [arr, coeffCount]

/-- **An element's limb `0`** loaded from an argument's window. -/
theorem win_c0 [Labels] (hst : StackOk m0 NW) {a : BitVec 64} {n : Nat} (hr : Readable m0 a n)
    (hs : OffStack m0 a n NW) {o s : Nat} {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 672 NW [(a + BitVec.ofNat 64 o, s)] noWr T vals m) {j i : Nat}
    (hji : o + j = 16 * i) (hi : 16 * i + 16 ≤ n) {ret : BitVec 64} :
    (Sym.load 1 j 8).eval (envS m0 m 672 [(a + BitVec.ofNat 64 o, s)] vals ret) =
      c0 (NativeRustcVm.ewOf m0.dmem (a + BitVec.ofNat 64 (16 * i))) := by
  show (envS m0 m 672 [(a + BitVec.ofNat 64 o, s)] vals ret).load 1 j 8 = _
  rw [win_load hst hr hs hB (by omega), hji]
  rfl

/-- **An element's limb `1`** loaded from an argument's window. -/
theorem win_c1 [Labels] (hst : StackOk m0 NW) {a : BitVec 64} {n : Nat} (hr : Readable m0 a n)
    (hs : OffStack m0 a n NW) {o s : Nat} {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 672 NW [(a + BitVec.ofNat 64 o, s)] noWr T vals m) {j i : Nat}
    (hji : o + j = 16 * i + 8) (hi : 16 * i + 16 ≤ n) {ret : BitVec 64} :
    (Sym.load 1 j 8).eval (envS m0 m 672 [(a + BitVec.ofNat 64 o, s)] vals ret) =
      c1 (NativeRustcVm.ewOf m0.dmem (a + BitVec.ofNat 64 (16 * i))) := by
  show (envS m0 m 672 [(a + BitVec.ofNat 64 o, s)] vals ret).load 1 j 8 = _
  rw [win_load hst hr hs hB (by omega), hji]
  exact (ew_words _ _ _).2

/-- A window's base is its alias. -/
theorem al0 (x : BitVec 64) : x = x + BitVec.ofNat 64 0 + BitVec.ofInt 64 0 := by simp

end

/-! ## The model's side -/

theorem ew_eta (x : EW) : (⟨.ofBitVec (c0 x), .ofBitVec (c1 x)⟩ : EW) = x := rfl

/-- A factor's limbs, as `b13` computes them. -/
theorem fac_eq (P r : EW) :
    (⟨.ofBitVec ((c0 P ^^^ c0 r) ^^^ BitVec.ofNat 64 1), .ofBitVec (c1 r ^^^ c1 P)⟩ : EW) =
      1 + P + r := by
  show (⟨(P.c0 ^^^ r.c0) ^^^ 1, r.c1 ^^^ P.c1⟩ : EW) = ⟨(1 ^^^ P.c0) ^^^ r.c0, (0 ^^^ P.c1) ^^^ r.c1⟩
  congr 1
  · ac_rfl
  · rw [UInt64.zero_xor, UInt64.xor_comm]


theorem fac_c0 (P r : EW) : c0 (1 + P + r) = (c0 P ^^^ c0 r) ^^^ BitVec.ofNat 64 1 := by
  rw [← fac_eq]

theorem fac_c1 (P r : EW) : c1 (1 + P + r) = c1 r ^^^ c1 P := by
  rw [← fac_eq]

theorem getElem_getD {P : Array EW} {i : Nat} (hi : i < P.size) : P[i] = P.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

theorem getD_map_sq {P : Array EW} {l : Nat} (hl : l < P.size) :
    (P.map fun v ↦ v * v).getD l 0 = P.getD l 0 * P.getD l 0 := by
  simp [Array.getD, hl]

theorem if_dt {p : Prop} [Decidable p] {α : Type} {a b : α} (h : p) :
    (if decide p = true then a else b) = a := by simp [h]

theorem if_df {p : Prop} [Decidable p] {α : Type} {a b : α} (h : ¬p) :
    (if decide p = true then a else b) = b := by simp [h]


end

/-- The links' values: the variables', registers', literals' and `vv`'s unfolded (so that the
kept ones close); the others are left for the caller. -/
macro "wv" : tactic => `(tactic|
  (simp only [List.cons_append, List.nil_append, List.forall_mem_cons, oL, ocL, ockL, pL, sL, s2L,
      qkL, q2L, cpL, ev_var, ev_reg, ev_lit, vv]
   try and_intros
   all_goals (first
     | exact fun _ h ↦ nomatch h
     | exact trivial
     | skip)))

end NativeRustcVmX64.Ring.Weight
