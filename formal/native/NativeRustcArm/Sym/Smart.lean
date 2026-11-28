module

public import NativeRustcArm.Sym.Lemmas

/-!
# The smart constructors are sound

Each smart constructor of the symbolic executor has the value of the plain constructor it
simplifies: `eval_mkBin`, `eval_mkUn`, `eval_mkBytes`, `eval_mkIte`, `eval_mkCmp`, ... .
-/

namespace NativeRustcArm.Sym

public section

/-! ## Bit vectors -/

theorem bv_sub_eq_zero {w : Nat} (a b : BitVec w) : a - b = 0#w ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· + b) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this
    exact this
  · intro h
    subst h
    exact BitVec.sub_self a

theorem bv_add_left_cancel {w : Nat} (b x y : BitVec w) : b + x = b + y ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun z => z - b) h
    simp only [BitVec.add_comm b, BitVec.add_sub_cancel] at this
    exact this
  · intro h
    rw [h]

theorem rotateRight_zero' {w : Nat} (x : BitVec w) : x.rotateRight 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateRight, hi]

theorem shiftW_zero {n : Nat} (k : ShiftType) (x : BitVec n) : shiftW k x 0 = x := by
  cases k
  · exact BitVec.shiftLeft_zero x
  · exact BitVec.ushiftRight_zero x
  · exact BitVec.sshiftRight_zero
  · exact rotateRight_zero' x

theorem extr_self {n : Nat} (x : BitVec n) (lsb : Nat) :
    (if lsb % n == 0 then x else (x <<< (n - lsb % n)) ||| (x >>> (lsb % n))) = x.rotateRight lsb := by
  unfold BitVec.rotateRight BitVec.rotateRightAux
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    rw [h, BitVec.ushiftRight_zero, Nat.sub_zero, BitVec.shiftLeft_eq_zero (Nat.le_refl n),
      BitVec.or_zero]
  · rw [BitVec.or_comm]

theorem page_add_lo12 (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 pageMask) + (x &&& 0xFFF#64) = x := by
  have h1 : BitVec.ofNat 64 pageMask = 0xFFFFFFFFFFFFF000#64 := rfl
  rw [h1, BitVec.add_eq_or_of_and_eq_zero]
  · rw [← BitVec.and_or_distrib_left]
    have : (0xFFFFFFFFFFFFF000#64 ||| 0xFFF#64) = BitVec.allOnes 64 := by decide
    rw [this, BitVec.and_allOnes]
  · have : (0xFFFFFFFFFFFFF000#64 &&& 0xFFF#64) = 0#64 := by decide
    rw [BitVec.and_assoc, BitVec.and_comm (0xFFFFFFFFFFFFF000#64), ← BitVec.and_assoc,
      ← BitVec.and_assoc, BitVec.and_self, BitVec.and_assoc, BitVec.and_comm (0xFFF#64), this,
      BitVec.and_zero]

theorem ofInt_litInt (c : Nat) : BitVec.ofInt 64 (litInt c) = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, litInt]
  split <;> omega

theorem lt32_of_ext (v : BitVec 32) : (ext .W32 v).toNat < 2 ^ 32 := by
  rw [ext_W32, BitVec.toNat_setWidth]
  have := v.isLt
  omega

theorem ext_low_W32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) : ext .W32 (low .W32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [ext_W32, low_W32, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  omega

@[simp] theorem low_zero (w : RegWidth) : low w (BitVec.ofNat 64 0) = 0#w.bits := by
  cases w <;> rfl

/-! ## Values -/

variable [Labels] (env : Env)

@[simp] theorem eval_lit_toNat (x : BitVec 64) : (Sym.lit x.toNat).eval env = x := by
  simp [Sym.eval, BitVec.ofNat_toNat]

omit [Labels] in
theorem asLit_eq {a : Sym} {n : Nat} (h : a.asLit = some n) : a = .lit n := by
  cases a <;> cases h <;> rfl

omit [Labels] in
theorem asPtr_eq {a : Sym} {r : Nat} {o : Int} (h : a.asPtr = some (r, o)) : a = .ptr r o := by
  cases a <;> cases h <;> rfl

omit [Labels] in
theorem asPage_eq {a x : Sym} (h : a.asPage = some x) :
    a = .bin .and .W64 x (.lit pageMask) := by
  unfold asPage at h
  split at h
  · split at h
    · rename_i hn
      cases h
      rw [hn.1]
    · cases h
  · cases h

omit [Labels] in
theorem asAddLit_eq {a x : Sym} {c : Nat} (h : a.asAddLit = some (x, c)) :
    a = .bin .add .W64 x (.lit c) := by
  unfold asAddLit at h
  split at h
  · cases h
    rfl
  · cases h

omit [Labels] in
theorem asIte_eq {a x y : Sym} {c : SBool} (h : a.asIte = some (c, x, y)) : a = .ite c x y := by
  cases a <;> cases h <;> rfl

omit [Labels] in
theorem asLo12_eq {a x : Sym} (h : a.asLo12 = some x) :
    a = .bin .and .W64 x (.lit 0xFFF) := by
  unfold asLo12 at h
  split at h
  · split at h
    · rename_i hn
      cases h
      rw [hn.1]
    · cases h
  · cases h

theorem clean32_lt {a : Sym} (h : a.clean32 = true) : (a.eval env).toNat < 2 ^ 32 := by
  cases a with
  | lit n =>
    have h : n < 2 ^ 32 := of_decide_eq_true h
    simp only [Sym.eval, BitVec.toNat_ofNat]
    omega
  | load r o n =>
    have h : n ≤ 4 := of_decide_eq_true h
    simp only [Sym.eval, Env.load, BitVec.toNat_ofInt]
    have h0 := Int.ofBytes_ge_zero ((List.range n).map fun i =>
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (o + i))).getD 0)
    have h1 := Int.ofBytes_lt ((List.range n).map fun i =>
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (o + i))).getD 0)
    simp only [List.length_map, List.length_range] at h1
    have h2 : (256 : Int) ^ n ≤ 2 ^ 32 :=
      (show ∀ k, k ≤ 4 → (256 : Int) ^ k ≤ 2 ^ 32 by decide) n h
    omega
  | bin op w x y =>
    cases w
    · simp only [Sym.eval]
      cases op <;> exact lt32_of_ext _
    · exact absurd h Bool.false_ne_true
  | un op w x =>
    cases op with
    | memExtend e => exact absurd h Bool.false_ne_true
    | bytes t n =>
      have h : n ≤ 4 := of_decide_eq_true h
      simp only [Sym.eval, UnOp.apply, bytesOf, BitVec.toNat_ofNat]
      have : 2 ^ (8 * n) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
      have := Nat.mod_lt ((x.eval env).toNat / 2 ^ (8 * t)) (Nat.two_pow_pos (8 * n))
      omega
    | _ =>
      cases w
      · exact lt32_of_ext _
      · exact absurd h Bool.false_ne_true
  | _ => exact absurd h Bool.false_ne_true

theorem eval_truncTo (w : RegWidth) (a : Sym) :
    (truncTo w a).eval env = ext w (low w (a.eval env)) := by
  cases w
  · simp only [truncTo]
    by_cases hc : a.clean32 = true
    · simp only [hc, ↓reduceIte]
      exact (ext_low_W32 (clean32_lt env hc)).symm
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rfl
  · exact (ext_low_W64 _).symm

theorem eval_addLit (x : Sym) (d : Nat) :
    (addLit x d).eval env = x.eval env + BitVec.ofNat 64 d := by
  unfold addLit
  split
  · rename_i r o hx
    rw [asPtr_eq hx]
    simp only [Sym.eval, BitVec.ofInt_add, ofInt_litInt, BitVec.add_assoc]
  · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

theorem eval_mkAdd64 (a b : Sym) :
    (mkAdd64 a b).eval env = a.eval env + b.eval env := by
  unfold mkAdd64
  split
  · rename_i r o c ha hb
    rw [asPtr_eq ha, asLit_eq hb]
    simp only [Sym.eval, BitVec.ofInt_add, ofInt_litInt, BitVec.add_assoc]
  · split
    · rename_i c r o ha hb
      rw [asLit_eq ha, asPtr_eq hb]
      simp only [Sym.eval, BitVec.ofInt_add, ofInt_litInt]
      rw [BitVec.add_comm (BitVec.ofNat 64 c), BitVec.add_assoc]
    · split
      · rename_i x x' ha hb
        rw [asPage_eq ha, asLo12_eq hb]
        split
        · subst_vars
          simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
          exact (page_add_lo12 _).symm
        · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      · split
        · rename_i x c d ha hb
          rw [asAddLit_eq ha, asLit_eq hb]
          simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, MemWidth.bits]
          omega
        · split
          · subst_vars
            simp [Sym.eval]
          · split
            · subst_vars
              simp [Sym.eval]
            · split
              · rename_i c x y d ha hb
                rw [asIte_eq ha, asLit_eq hb]
                simp only [Sym.eval, eval_addLit]
                split <;> rfl
              · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

theorem eval_mkSub64 (a b : Sym) :
    (mkSub64 a b).eval env = a.eval env - b.eval env := by
  unfold mkSub64
  split
  · rename_i r o c ha hb
    rw [asPtr_eq ha, asLit_eq hb]
    simp only [Sym.eval, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, ofInt_litInt,
      BitVec.add_assoc, BitVec.sub_eq_add_neg]
  · split
    · rename_i r o r' o' ha hb
      rw [asPtr_eq ha, asPtr_eq hb]
      split
      · subst_vars
        rw [eval_lit_toNat]
        simp only [Sym.eval]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt]
        omega
      · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    · split
      · rename_i x c d ha hb
        rw [asAddLit_eq ha, asLit_eq hb]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, MemWidth.bits]
        omega
      · split
        · subst_vars
          simp [Sym.eval]
        · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

omit [Labels] in
theorem apply_orr_zero_left (w : RegWidth) (y : BitVec 64) :
    BinOp.apply .orr w (BitVec.ofNat 64 0) y = ext w (low w y) := by
  simp only [BinOp.apply, low_zero, BitVec.zero_or]

omit [Labels] in
theorem apply_orr_zero_right (w : RegWidth) (x : BitVec 64) :
    BinOp.apply .orr w x (BitVec.ofNat 64 0) = ext w (low w x) := by
  simp only [BinOp.apply, low_zero, BitVec.or_zero]

omit [Labels] in
theorem apply_eor_zero_right (w : RegWidth) (x : BitVec 64) :
    BinOp.apply .eor w x (BitVec.ofNat 64 0) = ext w (low w x) := by
  simp only [BinOp.apply, low_zero, BitVec.xor_zero]

@[simp] theorem eval_mkUn (op : UnOp) (w : RegWidth) (a : Sym) :
    (mkUn op w a).eval env = op.apply w (a.eval env) := by
  unfold mkUn
  split
  · rename_i x ha
    rw [asLit_eq ha, eval_lit_toNat]
    rfl
  · split
    · exact eval_truncTo env w a
    · rw [eval_truncTo]
      simp only [UnOp.apply, shiftW_zero]
    · simp only [UnOp.apply, bytesOf, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      have := (a.eval env).isLt
      omega
    · rfl

@[simp] theorem eval_mkBin (op : BinOp) (w : RegWidth) (a b : Sym) :
    (mkBin op w a b).eval env = op.apply w (a.eval env) (b.eval env) := by
  unfold mkBin
  split
  · rename_i x y ha hb
    rw [asLit_eq ha, asLit_eq hb, eval_lit_toNat]
    rfl
  · split
    · rw [eval_mkAdd64]
      simp only [BinOp.apply, low_W64, ext_W64]
    · rw [eval_mkSub64]
      simp only [BinOp.apply, low_W64, ext_W64]
    · split
      · subst_vars
        rw [eval_truncTo]
        exact (apply_orr_zero_left _ _).symm
      · split
        · subst_vars
          rw [eval_truncTo]
          exact (apply_orr_zero_right _ _).symm
        · rfl
    · split
      · subst_vars
        rw [eval_truncTo]
        exact (apply_eor_zero_right _ _).symm
      · rfl
    · split
      · subst_vars
        rw [eval_mkUn]
        simp only [UnOp.apply, BinOp.apply, shiftW, extr_self]
      · rfl
    · rfl

omit [Labels] in
theorem bytesOf_eq_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 32) : bytesOf x 0 4 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [bytesOf, BitVec.toNat_ofNat, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

@[simp] theorem eval_mkBytes (v : Sym) (t n : Nat) :
    (mkBytes v t n).eval env = bytesOf (v.eval env) t n := by
  unfold mkBytes
  split
  · rename_i h
    obtain ⟨rfl, rfl, hc⟩ := h
    exact (bytesOf_eq_of_lt (clean32_lt env hc)).symm
  · rw [eval_mkUn]
    rfl

@[simp] theorem eval_mkIte (c : SBool) (a b : Sym) :
    (mkIte c a b).eval env = if c.eval env then a.eval env else b.eval env := by
  unfold mkIte
  split
  · rfl
  · rfl
  · split
    · subst_vars
      simp
    · rfl

/-! ## Booleans -/

@[simp] theorem eval_mkNot (b : SBool) : (mkNot b).eval env = !b.eval env := by
  unfold mkNot
  split
  · rfl
  · simp [SBool.eval]
  · rfl

@[simp] theorem eval_mkAnd (b c : SBool) : (mkAnd b c).eval env = (b.eval env && c.eval env) := by
  unfold mkAnd
  split <;> simp [SBool.eval]

@[simp] theorem eval_mkOr (b c : SBool) : (mkOr b c).eval env = (b.eval env || c.eval env) := by
  unfold mkOr
  split <;> simp [SBool.eval]

@[simp] theorem eval_mkBeq (b c : SBool) : (mkBeq b c).eval env = (b.eval env == c.eval env) := by
  unfold mkBeq
  split <;> rfl

@[simp] theorem eval_mkIteB (c a b : SBool) :
    (mkIteB c a b).eval env = if c.eval env then a.eval env else b.eval env := by
  unfold mkIteB
  split
  · rfl
  · rfl
  · split
    · subst_vars
      simp
    · rfl

@[simp] theorem eval_mkCmp (op : CmpOp) (w : RegWidth) (a b : Sym) :
    (mkCmp op w a b).eval env = op.apply w (a.eval env) (b.eval env) := by
  unfold mkCmp
  split
  · rename_i x y ha hb
    rw [asLit_eq ha, asLit_eq hb]
    rfl
  · split
    · rename_i r o r' o' ha hb
      rw [asPtr_eq ha, asPtr_eq hb]
      split
      · subst_vars
        simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, bv_add_left_cancel]
      · rfl
    · rfl

@[simp] theorem eval_mkMsb (w : RegWidth) (a : Sym) :
    (mkMsb w a).eval env = (low w (a.eval env)).msb := by
  unfold mkMsb
  split
  · rename_i x ha
    rw [asLit_eq ha]
    rfl
  · rfl

@[simp] theorem eval_mkBit (w : RegWidth) (a : Sym) (n : Nat) :
    (mkBit w a n).eval env = (low w (a.eval env)).getLsbD n := by
  unfold mkBit
  split
  · rename_i x ha
    rw [asLit_eq ha]
    rfl
  · rfl

end

end NativeRustcArm.Sym
