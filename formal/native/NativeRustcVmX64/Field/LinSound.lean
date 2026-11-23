module

public import NativeRustcVmX64.Field.Lin

/-!
# `Lin.check` is sound (x86-64)

`lin_sound`: a form `lin` computes is the value's (`Sound`: each bit the parity of the key bits of
its entry), given the products' forms are their factors' (`Valid`). `eval_eq_of_check`: values
`check` accepts are equal; `eval_eq_of_checkRev`: of values `checkRev` accepts, the first is the
second bit-reversed.
-/

namespace NativeRustcVmX64.Field.Lin

open NativeRustcX64 NativeRustcX64.Sym

public section

/-! ## Parities -/

theorem par_eq (val : Nat → Bool) (k n : Nat) :
    par val k n = (((n % 2 == 1) && val k) ^^ par val (k + 1) (n / 2)) := by
  rw [par]
  by_cases h : n = 0
  · subst h
    rw [ite_eq_left rfl, par, ite_eq_left (by decide)]
    rfl
  · rw [ite_eq_right h]

theorem par_zero (val : Nat → Bool) (k : Nat) : par val k 0 = false := by
  rw [par, ite_eq_left rfl]

theorem mod_two_xor (a b : Nat) : ((a ^^^ b) % 2 == 1) = ((a % 2 == 1) ^^ (b % 2 == 1)) := by
  have h := @Nat.xor_mod_two_eq_one a b
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  have hab := Nat.mod_two_eq_zero_or_one (a ^^^ b)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp_all

theorem par_xor_le (val : Nat → Bool) :
    ∀ N a b k, a + b ≤ N → par val k (a ^^^ b) = (par val k a ^^ par val k b) := by
  intro N
  induction N with
  | zero =>
    intro a b k h
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp [par_zero]
  | succ N ih =>
    intro a b k h
    rw [par_eq val k (a ^^^ b), par_eq val k a, par_eq val k b, Nat.xor_div_two,
      ih (a / 2) (b / 2) (k + 1) (by omega), mod_two_xor]
    generalize (a % 2 == 1) = x
    generalize (b % 2 == 1) = y
    generalize val k = v
    generalize par val (k + 1) (a / 2) = p
    generalize par val (k + 1) (b / 2) = q
    cases x <;> cases y <;> cases v <;> cases p <;> cases q <;> rfl

theorem par_xor (val : Nat → Bool) (k a b : Nat) :
    par val k (a ^^^ b) = (par val k a ^^ par val k b) :=
  par_xor_le val (a + b) a b k (Nat.le_refl _)

theorem par_two_pow (val : Nat → Bool) (j k : Nat) : par val k (2 ^ j) = val (k + j) := by
  induction j generalizing k with
  | zero =>
    rw [par_eq]
    simp [par_zero]
  | succ j ih =>
    rw [par_eq, show 2 ^ (j + 1) % 2 = 0 by rw [Nat.pow_succ]; omega,
      show 2 ^ (j + 1) / 2 = 2 ^ j by rw [Nat.pow_succ]; omega, ih, Nat.add_assoc,
      Nat.add_comm 1 j]
    simp

/-! ## The forms' entries -/

theorem getD_map_range (g : Nat → Nat) {i : Nat} (hi : i < 64) :
    ((List.range 64).map g).getD i 0 = g i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem length_map_range (g : Nat → Nat) : ((List.range 64).map g).length = 64 := by simp

theorem getD_xorF {f g : Form} (hf : f.length = 64) (hg : g.length = 64) {i : Nat} (hi : i < 64) :
    (xorF f g).getD i 0 = f.getD i 0 ^^^ g.getD i 0 := by
  simp [xorF, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem
    (show i < f.length by omega), List.getElem?_eq_getElem (show i < g.length by omega)]

theorem length_xorF {f g : Form} (hf : f.length = 64) (hg : g.length = 64) :
    (xorF f g).length = 64 := by
  simp [xorF, hf, hg]

theorem getD_andCF (n : Nat) {f : Form} (hf : f.length = 64) {i : Nat} (hi : i < 64) :
    (andCF n f).getD i 0 = if n.testBit i then f.getD i 0 else 0 := by
  simp [andCF, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_range hi,
    List.getElem?_eq_getElem (show i < f.length by omega)]

theorem length_andCF (n : Nat) {f : Form} (hf : f.length = 64) : (andCF n f).length = 64 := by
  simp [andCF, hf]

theorem orOk_getD {f g : Form} (hf : f.length = 64) (hg : g.length = 64) (h : orOk f g = true)
    {i : Nat} (hi : i < 64) : f.getD i 0 = 0 ∨ g.getD i 0 = 0 := by
  simp only [orOk, List.all_eq_true, id_eq] at h
  have hm := h _ (List.getElem_mem (l := List.zipWith (fun x y ↦ x == 0 || y == 0) f g)
    (n := i) (by simp [hf, hg, hi]))
  simp only [List.getElem_zipWith, Bool.or_eq_true, beq_iff_eq] at hm
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < f.length by omega),
    List.getElem?_eq_getElem (show i < g.length by omega), Option.getD_some]
  exact hm

theorem getD_shlF {k : Nat} {f : Form} {i : Nat} (hi : i < 64) :
    (shlF k f).getD i 0 = if k ≤ i then f.getD (i - k) 0 else 0 := by
  simp only [shlF, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi]
  by_cases h : k ≤ i
  · rw [ite_eq_left h, List.getElem?_append_right (by simp; omega)]
    simp
  · rw [ite_eq_right h, List.getElem?_append_left (by simp; omega)]
    simp [show i < k by omega]

theorem length_shlF {k : Nat} {f : Form} (hf : f.length = 64) :
    (shlF k f).length = 64 := by
  simp [shlF, hf]

theorem getD_shrF {k : Nat} {f : Form} (hf : f.length = 64) {i : Nat}
    (_hi : i < 64) : (shrF k f).getD i 0 = if i + k < 64 then f.getD (i + k) 0 else 0 := by
  simp only [shrF, List.getD_eq_getElem?_getD]
  by_cases h : i + k < 64
  · rw [ite_eq_left h, List.getElem?_append_left (by simp; omega), List.getElem?_drop,
      Nat.add_comm k i]
  · rw [ite_eq_right h, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
    split <;> rfl

theorem length_shrF {k : Nat} (hk : k ≤ 64) {f : Form} (hf : f.length = 64) :
    (shrF k f).length = 64 := by
  simp [shrF, hf]
  omega

theorem getD_reverse {f : Form} (hf : f.length = 64) {i : Nat} (hi : i < 64) :
    f.reverse.getD i 0 = f.getD (63 - i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_reverse (show i < f.length by omega), hf]

/-! ## The operations' bits -/

theorem getLsbD_lit (n : Nat) {i : Nat} (hi : i < 64) :
    (BitVec.ofNat 64 n).getLsbD i = n.testBit i := by
  rw [BitVec.getLsbD_ofNat]
  simp [hi]

theorem and_apply (x y : BitVec 64) : BinOp.apply .and .W64 x y = x &&& y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem or_apply (x y : BitVec 64) : BinOp.apply .or .W64 x y = x ||| y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem xor_apply (x y : BitVec 64) : BinOp.apply .xor .W64 x y = x ^^^ y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem add_apply (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem mul_apply (x y : BitVec 64) : BinOp.apply .mul .W64 x y = x * y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem shiftCount_lit {k : Nat} (hk : k < 64) : shiftCount .W64 (BitVec.ofNat 64 k) = k := by
  unfold shiftCount shiftMask
  rw [toNat_low]
  show (BitVec.ofNat 64 k).toNat % 2 ^ 8 &&& 0x3f = k
  rw [BitVec.toNat_ofNat, show (0x3f : Nat) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shl_apply (x : BitVec 64) {k : Nat} (hk : k < 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 k) = x <<< k := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount_lit hk]

theorem shr_apply (x : BitVec 64) {k : Nat} (hk : k < 64) :
    BinOp.apply .shr .W64 x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount_lit hk, BitVec.ushiftRight_eq]

theorem mul_two_pow (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 (2 ^ k) = x <<< k := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat]

theorem bswap_apply (x : BitVec 64) : UnOp.apply .bswap .W64 x = bswap64 x := by
  simp only [UnOp.apply, bswapW, low_W64, ext_W64]

theorem getLsbD_bswap64 (x : BitVec 64) {i : Nat} (hi : i < 64) :
    (bswap64 x).getLsbD i = x.getLsbD (bswapIdx i) := by
  iterate 64
    rcases i with _ | i
    · simp only [bswap64, BitVec.take, BitVec.drop, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', bswapIdx]
      simp
  omega

theorem getD_bswapF {f : Form} {i : Nat} (hi : i < 64) :
    (bswapF f).getD i 0 = f.getD (bswapIdx i) 0 := by
  rw [bswapF, getD_map_range _ hi]

/-! ## Keys -/

section
variable [Labels] {env : Env} {tbl : List Entry}

theorem par_atom (key : Nat) {i : Nat} (hi : i < 64) :
    par (val env tbl) 0 (2 ^ (64 * key + i)) = (keyVal env tbl key).getLsbD i := by
  rw [par_two_pow, Nat.zero_add, val, show (64 * key + i) / 64 = key by omega,
    show (64 * key + i) % 64 = i by omega]

theorem sound_atom (key : Nat) : Sound env tbl (keyVal env tbl key) (atomF key) :=
  ⟨length_map_range _, fun i hi ↦ by rw [atomF, getD_map_range _ hi, par_atom key hi]⟩

theorem keyVal_reg (r : Reg64) : keyVal env tbl (r.idx + 1) = env.regs r := by
  have h := allRegs_idx r
  have hr : r.idx < 16 := by cases r <;> decide
  rw [keyVal, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel, h]

theorem keyVal_var {i : Nat} (hi : i < 15) : keyVal env tbl (17 + i) = env.vars i := by
  rw [keyVal, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    Nat.add_sub_cancel_left]

theorem keyVal_prod {t : Nat} {e : Entry} (h : tbl[t]? = some e) :
    keyVal env tbl (32 + t) = e.a.eval env * e.b.eval env := by
  rw [keyVal, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show 32 + t - 32 = t by omega, h]

theorem sound_lit (n : Nat) : Sound env tbl (BitVec.ofNat 64 n) (litF n) := by
  refine ⟨length_map_range _, fun i hi ↦ ?_⟩
  rw [litF, getD_map_range _ hi, getLsbD_lit n hi]
  by_cases h : n.testBit i
  · rw [ite_eq_left h, h, show 2 ^ i = 2 ^ (64 * 0 + i) by rw [Nat.mul_zero, Nat.zero_add],
      par_atom 0 hi, keyVal, ite_eq_left rfl, BitVec.getLsbD_allOnes]
    simp [hi]
  · rw [ite_eq_right h, par_zero]
    exact Bool.eq_false_iff.mpr h

theorem Sound.bit {x : BitVec 64} {f : Form} (h : Sound env tbl x f) {i : Nat} (hi : i < 64) :
    x.getLsbD i = par (val env tbl) 0 (f.getD i 0) := h.2 i hi

theorem Sound.xor {x y : BitVec 64} {f g : Form} (hx : Sound env tbl x f)
    (hy : Sound env tbl y g) : Sound env tbl (x ^^^ y) (xorF f g) :=
  ⟨length_xorF hx.1 hy.1, fun i hi ↦ by
    rw [BitVec.getLsbD_xor, getD_xorF hx.1 hy.1 hi, par_xor, hx.bit hi, hy.bit hi]⟩

theorem Sound.or {x y : BitVec 64} {f g : Form} (hx : Sound env tbl x f)
    (hy : Sound env tbl y g) (hok : orOk f g = true) : Sound env tbl (x ||| y) (xorF f g) :=
  ⟨length_xorF hx.1 hy.1, fun i hi ↦ by
    rw [BitVec.getLsbD_or, getD_xorF hx.1 hy.1 hi, par_xor, hx.bit hi, hy.bit hi]
    rcases orOk_getD hx.1 hy.1 hok hi with h | h <;> rw [h, par_zero] <;> simp⟩

theorem Sound.add {x y : BitVec 64} {f g : Form} (hx : Sound env tbl x f)
    (hy : Sound env tbl y g) (hok : orOk f g = true) : Sound env tbl (x + y) (xorF f g) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · exact hx.or hy hok
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, hx.bit hi, hy.bit hi, BitVec.getLsbD_zero]
    rcases orOk_getD hx.1 hy.1 hok hi with h | h <;> rw [h, par_zero] <;> simp

theorem Sound.and {x : BitVec 64} {f : Form} (hx : Sound env tbl x f) (n : Nat) :
    Sound env tbl (x &&& BitVec.ofNat 64 n) (andCF n f) :=
  ⟨length_andCF n hx.1, fun i hi ↦ by
    rw [BitVec.getLsbD_and, getD_andCF n hx.1 hi, getLsbD_lit n hi, hx.bit hi]
    by_cases h : n.testBit i
    · rw [ite_eq_left h, h, Bool.and_true]
    · rw [ite_eq_right h, par_zero, Bool.eq_false_iff.mpr h, Bool.and_false]⟩

theorem Sound.shl {x : BitVec 64} {f : Form} (hx : Sound env tbl x f) {k : Nat} (hk : k ≤ 64) :
    Sound env tbl (x <<< k) (shlF k f) :=
  ⟨length_shlF hx.1, fun i hi ↦ by
    rw [BitVec.getLsbD_shiftLeft, getD_shlF hi]
    by_cases h : k ≤ i
    · rw [ite_eq_left h, ← hx.bit (by omega)]
      simp [hi, show ¬i < k by omega]
    · rw [ite_eq_right h, par_zero]
      simp [show i < k by omega]⟩

theorem Sound.shr {x : BitVec 64} {f : Form} (hx : Sound env tbl x f) {k : Nat} (hk : k ≤ 64) :
    Sound env tbl (x >>> k) (shrF k f) :=
  ⟨length_shrF hk hx.1, fun i hi ↦ by
    rw [BitVec.getLsbD_ushiftRight, getD_shrF hx.1 hi]
    by_cases h : i + k < 64
    · rw [ite_eq_left h, ← hx.bit h, Nat.add_comm]
    · rw [ite_eq_right h, par_zero]
      exact BitVec.getLsbD_of_ge x _ (by omega)⟩

theorem Sound.bswap {x : BitVec 64} {f : Form} (hx : Sound env tbl x f) :
    Sound env tbl (bswap64 x) (bswapF f) :=
  ⟨length_map_range _, fun i hi ↦ by
    rw [getLsbD_bswap64 x hi, getD_bswapF hi, hx.bit (by unfold bswapIdx; omega)]⟩

theorem Sound.rev {x : BitVec 64} {f : Form} (hx : Sound env tbl x f) :
    Sound env tbl x.reverse f.reverse :=
  ⟨by rw [List.length_reverse, hx.1], fun i hi ↦ by
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, getD_reverse hx.1 hi,
      ← hx.bit (by omega), decide_eq_true hi, Bool.true_and]⟩

/-- Values with one form are equal. -/
theorem Sound.eq {x y : BitVec 64} {f : Form} (hx : Sound env tbl x f) (hy : Sound env tbl y f) :
    x = y :=
  BitVec.eq_of_getLsbD_eq fun i hi ↦ by rw [hx.bit hi, hy.bit hi]

omit [Labels] in
theorem add_self (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1
  omega

end

/-! ## Products -/

theorem find_spec {fa fb : Form} :
    ∀ {tbl : List Entry} {s t : Nat}, find fa fb tbl s = some t →
      s ≤ t ∧ ∃ e, tbl[t - s]? = some e ∧ ((e.fa = fa ∧ e.fb = fb) ∨ (e.fa = fb ∧ e.fb = fa))
  | [], _, _, h => by simp [find] at h
  | e :: es, s, t, h => by
    simp only [find] at h
    split at h
    · rename_i hc
      cases h
      refine ⟨Nat.le_refl _, e, by simp, ?_⟩
      simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using hc
    · obtain ⟨hst, e', he', hc⟩ := find_spec h
      refine ⟨by omega, e', ?_, hc⟩
      rw [show t - s = (t - (s + 1)) + 1 by omega]
      simpa using he'

section
variable [Labels]

/-- The products' forms are their factors'. -/
def Valid (env : Env) (tbl : List Entry) : Prop :=
  ∀ e ∈ tbl, Sound env [] (e.a.eval env) e.fa ∧ Sound env [] (e.b.eval env) e.fb

theorem valid_nil (env : Env) : Valid env [] := fun _ h ↦ by cases h

theorem two_pow_log2 {n : Nat} (h : 2 ^ n.log2 = n) (env : Env) :
    (Sym.lit n).eval env = BitVec.ofNat 64 (2 ^ n.log2) := by
  rw [h]
  rfl

/-- **`lin` is sound.** -/
theorem lin_sound (env : Env) :
    ∀ (fuel : Nat) (tbl : List Entry) (s : Sym) (f : Form), Valid env tbl →
      lin tbl fuel s = some f → Sound env tbl (s.eval env) f := by
  intro fuel
  induction fuel with
  | zero => intro tbl s f _ h; simp [lin] at h
  | succ fuel ih =>
    intro tbl s f hv h
    simp only [lin] at h
    split at h
    · cases h; exact sound_lit _
    · rename_i r
      cases h
      show Sound env tbl (env.regs r) _
      rw [← keyVal_reg (tbl := tbl) r]
      exact sound_atom _
    · rename_i i
      split at h
      · rename_i hi
        cases h
        show Sound env tbl (env.vars i) _
        rw [← keyVal_var (tbl := tbl) hi]
        exact sound_atom _
      · cases h
    · rename_i a n
      obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      show Sound env tbl (BinOp.apply .and .W64 (a.eval env) (BitVec.ofNat 64 n)) _
      rw [and_apply]; exact (ih tbl a fa hv ha).and n
    · rename_i n a _
      obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      show Sound env tbl (BinOp.apply .and .W64 (BitVec.ofNat 64 n) (a.eval env)) _
      rw [and_apply, BitVec.and_comm]; exact (ih tbl a fa hv ha).and n
    · rename_i a b
      split at h
      · rename_i fa fb ha hb
        cases h
        show Sound env tbl (BinOp.apply .xor .W64 (a.eval env) (b.eval env)) _
        rw [xor_apply]
        exact (ih tbl a fa hv ha).xor (ih tbl b fb hv hb)
      · cases h
    · rename_i a b
      split at h
      · rename_i fa fb ha hb
        split at h
        · rename_i hok
          cases h
          show Sound env tbl (BinOp.apply .or .W64 (a.eval env) (b.eval env)) _
          rw [or_apply]
          exact (ih tbl a fa hv ha).or (ih tbl b fb hv hb) hok
        · cases h
      · cases h
    · rename_i a b
      split at h
      · rename_i fa fb ha hb
        show Sound env tbl (BinOp.apply .add .W64 (a.eval env) (b.eval env)) _
        rw [add_apply]
        split at h
        · rename_i hok
          cases h
          exact (ih tbl a fa hv ha).add (ih tbl b fb hv hb) hok
        · split at h
          · rename_i heq
            cases h
            have hsa := ih tbl a fa hv ha
            have hsb := ih tbl b fb hv hb
            rw [beq_iff_eq] at heq
            subst heq
            rw [← hsa.eq hsb, add_self]
            exact hsa.shl (by decide)
          · cases h
      · cases h
    · rename_i a n
      split at h
      · rename_i hc
        obtain ⟨hpow, h64⟩ := hc
        obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        show Sound env tbl (BinOp.apply .mul .W64 (a.eval env) ((Sym.lit n).eval env)) _
        rw [mul_apply, two_pow_log2 hpow env, mul_two_pow _ _]
        exact (ih tbl a fa hv ha).shl (by omega)
      · cases h
    · rename_i a b _
      split at h
      · rename_i fa fb ha hb
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨-, e, he, hc⟩ := find_spec ht
        rw [Nat.sub_zero] at he
        have hsa := ih [] a fa (valid_nil env) ha
        have hsb := ih [] b fb (valid_nil env) hb
        obtain ⟨hea, heb⟩ := hv e (List.mem_of_getElem? he)
        have hval : (Sym.bin .mul .W64 a b).eval env = keyVal env tbl (32 + t) := by
          rw [keyVal_prod he]
          show BinOp.apply .mul .W64 (a.eval env) (b.eval env) = _
          rw [mul_apply]
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [hsa.eq (h1 ▸ hea), hsb.eq (h2 ▸ heb)]
          · rw [hsa.eq (h2 ▸ heb), hsb.eq (h1 ▸ hea), BitVec.mul_comm]
        rw [hval]
        exact sound_atom _
      · cases h
    · rename_i a k
      split at h
      · rename_i hk
        obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        show Sound env tbl (BinOp.apply .shl .W64 (a.eval env) (BitVec.ofNat 64 k)) _
        rw [shl_apply _ hk]; exact (ih tbl a fa hv ha).shl (by omega)
      · cases h
    · rename_i a k
      split at h
      · rename_i hk
        obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        show Sound env tbl (BinOp.apply .shr .W64 (a.eval env) (BitVec.ofNat 64 k)) _
        rw [shr_apply _ hk]; exact (ih tbl a fa hv ha).shr (by omega)
      · cases h
    · rename_i a
      obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      show Sound env tbl (UnOp.apply .bswap .W64 (a.eval env)) _
      rw [bswap_apply]; exact (ih tbl a fa hv ha).bswap
    · cases h

theorem valid_of_table (env : Env) {fuel : Nat} {a b : Sym} {tbl : List Entry}
    (h : table fuel a b = some tbl) : Valid env tbl := by
  simp only [table] at h
  split at h
  · rename_i hall
    cases h
    intro e he
    have := List.all_eq_true.mp hall e he
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨lin_sound env fuel [] e.a e.fa (valid_nil env) this.1,
      lin_sound env fuel [] e.b e.fb (valid_nil env) this.2⟩
  · cases h

/-- **A successful check makes the values equal.** -/
theorem eval_eq_of_check {fuel : Nat} {a b : Sym} (h : check fuel a b = true) (env : Env) :
    a.eval env = b.eval env := by
  simp only [check] at h
  split at h
  · rename_i tbl ht
    have hv := valid_of_table env ht
    split at h
    · rename_i f g ha hb
      simp only [beq_iff_eq] at h
      subst h
      exact (lin_sound env fuel _ a f hv ha).eq (lin_sound env fuel _ b f hv hb)
    · cases h
  · cases h

/-- **A successful reversal check makes the first value the second reversed.** -/
theorem eval_eq_of_checkRev {fuel : Nat} {a b : Sym} (h : checkRev fuel a b = true) (env : Env) :
    a.eval env = (b.eval env).reverse := by
  simp only [checkRev] at h
  split at h
  · rename_i tbl ht
    have hv := valid_of_table env ht
    split at h
    · rename_i f g ha hb
      simp only [beq_iff_eq] at h
      subst h
      exact (lin_sound env fuel _ a _ hv ha).eq (lin_sound env fuel _ b g hv hb).rev
    · cases h
  · cases h

end

end

end NativeRustcVmX64.Field.Lin
