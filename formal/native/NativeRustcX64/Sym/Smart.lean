module

public import NativeRustcX64.Sym.Lemmas

/-!
# The smart constructors are sound

Each smart constructor of the symbolic executor has the value of the plain constructor it
simplifies: `eval_mkBin`, `eval_mkUn`, `eval_mkBytes`, `eval_mkIte`, `eval_mkCmp`, ... .
-/

namespace NativeRustcX64.Sym

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

theorem ofInt_litInt (c : Nat) : BitVec.ofInt 64 (litInt c) = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, litInt]
  split <;> omega

theorem ext_lt32 (w : Width) (hw : w ≠ .W64) (v : w.type) : (ext w v).toNat < 2 ^ 32 := by
  rw [toNat_ext]
  have := v.isLt
  have : 2 ^ w.bits ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by cases w <;> simp_all)
  omega

theorem ext_low_W32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) : ext .W32 (low .W32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ext, toNat_low]
  show x.toNat % 2 ^ 32 = x.toNat
  omega

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
theorem asIte_eq {a x y : Sym} {c : SBool} (h : a.asIte = some (c, x, y)) : a = .ite c x y := by
  unfold asIte at h
  split at h <;> simp_all

theorem eval_asAddLit {a x : Sym} {c : Nat} (h : a.asAddLit = some (x, c)) :
    a.eval env = x.eval env + BitVec.ofNat 64 c := by
  unfold asAddLit at h
  split at h
  · cases h
    simp [Sym.eval, BinOp.apply]
  · cases h
    simp [Sym.eval]
  · cases h

theorem clean32_lt {a : Sym} (h : a.clean32 = true) : (a.eval env).toNat < 2 ^ 32 := by
  have hw : ∀ w : Width, (w != .W64) = true → w ≠ .W64 := fun w h e => by
    subst e
    exact absurd h (by decide)
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
  | loadx r o i n =>
    have h : n ≤ 4 := of_decide_eq_true h
    simp only [Sym.eval, Env.load, BitVec.toNat_ofInt]
    have h0 := Int.ofBytes_ge_zero ((List.range n).map fun j =>
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (o + (i.eval env).toNat + j))).getD 0)
    have h1 := Int.ofBytes_lt ((List.range n).map fun j =>
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (o + (i.eval env).toNat + j))).getD 0)
    simp only [List.length_map, List.length_range] at h1
    have h2 : (256 : Int) ^ n ≤ 2 ^ 32 :=
      (show ∀ k, k ≤ 4 → (256 : Int) ^ k ≤ 2 ^ 32 by decide) n h
    omega
  | bin op w x y =>
    simp only [Sym.eval]
    cases op with
    | merge => exact absurd h Bool.false_ne_true
    | _ => exact ext_lt32 w (hw w h) _
  | un op w x =>
    simp only [Sym.eval]
    cases op with
    | bswap => exact absurd h Bool.false_ne_true
    | bytes t n =>
      have h : n ≤ 4 := of_decide_eq_true h
      simp only [UnOp.apply, bytesOf, BitVec.toNat_ofNat]
      have : 2 ^ (8 * n) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
      have := Nat.mod_lt ((x.eval env).toNat / 2 ^ (8 * t)) (Nat.two_pow_pos (8 * n))
      omega
    | _ => exact ext_lt32 w (hw w h) _
  | tern op w x y z =>
    simp only [Sym.eval]
    cases op <;> simp only [TernOp.apply] <;> split <;> exact ext_lt32 w (hw w h) _
  | _ => exact absurd h Bool.false_ne_true

theorem eval_truncTo (w : Width) (a : Sym) :
    (truncTo w a).eval env = ext w (low w (a.eval env)) := by
  cases a
  case lit n =>
    cases w
    case W64 => simp [truncTo]
    all_goals exact eval_lit_toNat env _
  all_goals
    cases w with
    | W64 => simp [truncTo]
    | W32 =>
      simp only [truncTo]
      split
      · rename_i hc
        exact (ext_low_W32 (clean32_lt env hc)).symm
      · rfl
    | W8 => rfl
    | W16 => rfl

theorem eval_addLit (x : Sym) (d : Nat) :
    (addLit x d).eval env = x.eval env + BitVec.ofNat 64 d := by
  unfold addLit
  split
  · rename_i r o h
    rw [asPtr_eq h]
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
      · subst_vars
        simp [Sym.eval]
      · split
        · subst_vars
          simp [Sym.eval]
        · split
          · rename_i x y ha hb
            rw [asLit_eq ha, asLit_eq hb]
            simp only [Sym.eval]
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
            omega
          · split
            · rename_i x c c' ha hb
              rw [eval_asAddLit env ha, asLit_eq hb]
              simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits]
              omega
            · split
              · rename_i c x c' ha hb
                rw [asLit_eq ha, eval_asAddLit env hb]
                simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits]
                omega
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
      · subst_vars
        simp [Sym.eval]
      · split
        · rename_i x y ha hb
          rw [asLit_eq ha, asLit_eq hb]
          simp only [Sym.eval]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
          omega
        · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

@[simp] theorem eval_mkUn (op : UnOp) (w : Width) (a : Sym) :
    (mkUn op w a).eval env = op.apply w (a.eval env) := by
  unfold mkUn
  split
  · rename_i x ha
    rw [asLit_eq ha, eval_lit_toNat]
    rfl
  · split
    · exact eval_truncTo env w a
    · simp only [UnOp.apply, bytesOf, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      have := (a.eval env).isLt
      omega
    · rfl

omit [Labels] in
theorem low_lit_one (w : Width) (x : BitVec 64) :
    ext w (low w x * low w (BitVec.ofNat 64 1)) = ext w (low w x) := by
  rw [low_one, BitVec.mul_one]

@[simp] theorem eval_mkBin (op : BinOp) (w : Width) (a b : Sym) :
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
        simp only [BinOp.apply, Sym.eval, low_zero, BitVec.zero_or]
      · split
        · subst_vars
          rw [eval_truncTo]
          simp only [BinOp.apply, Sym.eval, low_zero, BitVec.or_zero]
        · rfl
    · split
      · subst_vars
        simp only [Sym.eval, BinOp.apply, BitVec.xor_self]
        cases w <;> rfl
      · split
        · subst_vars
          rw [eval_truncTo]
          simp only [BinOp.apply, Sym.eval, low_zero, BitVec.xor_zero]
        · rfl
    · split
      · subst_vars
        rw [eval_truncTo]
        simp only [BinOp.apply, Sym.eval, low_one, BitVec.mul_one]
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

@[simp] theorem eval_mkCmp (op : CmpOp) (w : Width) (a b : Sym) :
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

@[simp] theorem eval_mkMsb (w : Width) (a : Sym) :
    (mkMsb w a).eval env = (low w (a.eval env)).msb := by
  unfold mkMsb
  split
  · rename_i x ha
    rw [asLit_eq ha]
    rfl
  · rfl

end

end NativeRustcX64.Sym
