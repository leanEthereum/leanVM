module

public import NativeRustcVmArm.Field.Lin

/-!
# `Lin.check` is sound

`lin_sound`: a form `lin` computes is the value's (`Sound`: each bit the parity of the key bits of
its entry), given the products' forms are their factors' (`Valid`). `eval_eq_of_check`: values
`check` accepts are equal.
-/

namespace NativeRustcVmArm.Field.Lin

open NativeRustcArm NativeRustcArm.Sym

public section

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

theorem getD_bfmF {d s : Form} (hd : d.length = 64) {i : Nat} (hi : i < 64) :
    (bfmF d s).getD i 0 = if i = 0 then s.getD 63 0 else d.getD i 0 := by
  cases i with
  | zero => simp [bfmF]
  | succ i =>
    simp only [bfmF, List.getD_cons_succ, Nat.add_one_ne_zero, ite_false]
    cases d with
    | nil => simp at hd
    | cons x d => simp

theorem length_bfmF {d s : Form} (hd : d.length = 64) : (bfmF d s).length = 64 := by
  cases d with
  | nil => simp at hd
  | cons x d => simpa [bfmF] using hd

/-! ## The operations' bits -/

theorem getLsbD_lit (n : Nat) {i : Nat} (hi : i < 64) :
    (BitVec.ofNat 64 n).getLsbD i = n.testBit i := by
  rw [BitVec.getLsbD_ofNat]
  simp [hi]

theorem ubfm_lsl (x : BitVec 64) {immr imms : Nat} (h : imms + 1 = immr) (h64 : immr < 64) :
    UnOp.apply (.ubfm immr imms) .W64 x = x <<< (64 - immr) := by
  simp only [UnOp.apply, low_W64, ext_W64, evalUBFM]
  rw [ite_eq_right (by show ¬(imms % 64 ≥ immr % 64); omega)]
  show BitVec.zeroExtend 64 (x.take (imms % 64 + 1)) <<< (64 - immr % 64) = x <<< (64 - immr)
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt (show imms < 64 by omega)]
  ext i hi
  by_cases hlt : i < 64 - immr
  · simp [hlt]
  · have h1 : i - (64 - immr) < imms + 1 := by omega
    simp [hlt, BitVec.take, h1]
    exact BitVec.getLsbD_eq_getElem (by omega)

theorem bfm_eq (d s : BitVec 64) :
    BinOp.apply (.bfm 63 63) .W64 d s = (d &&& ~~~1#64) ||| ((s >>> 63) &&& 1#64) := by
  simp only [BinOp.apply, low_W64, ext_W64, evalBFM, maskOfLen]
  rfl

theorem getLsbD_bfm (d s : BitVec 64) {i : Nat} (hi : i < 64) :
    (BinOp.apply (.bfm 63 63) .W64 d s).getLsbD i =
      if i = 0 then s.getLsbD 63 else d.getLsbD i := by
  rw [bfm_eq]
  cases i with
  | zero => simp
  | succ i =>
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat,
      BitVec.getLsbD_ushiftRight, Nat.add_one_ne_zero, ite_false]
    rw [show Nat.testBit 1 (i + 1) = false from
      Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))]
    simp [hi]

/-! ## Keys -/

section
variable [Labels] {env : Env} {tbl : List Entry}

theorem par_atom (key : Nat) {i : Nat} (hi : i < 64) :
    par (val env tbl) 0 (2 ^ (64 * key + i)) = (keyVal env tbl key).getLsbD i := by
  rw [par_two_pow, Nat.zero_add, val, show (64 * key + i) / 64 = key by omega,
    show (64 * key + i) % 64 = i by omega]

theorem sound_atom (key : Nat) : Sound env tbl (keyVal env tbl key) (atomF key) :=
  ⟨length_map_range _, fun i hi ↦ by rw [atomF, getD_map_range _ hi, par_atom key hi]⟩

theorem keyVal_reg (r : XReg) : keyVal env tbl (r.idx + 1) = env.regs r := by
  have h := allXRegs_idx r
  have hr : r.idx < 31 := by cases r <;> decide
  rw [keyVal, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel, h]

theorem keyVal_prod {t : Nat} {e : Entry} (h : tbl[t]? = some e) :
    keyVal env tbl (32 + t) = e.a.eval env * e.b.eval env := by
  rw [keyVal, ite_eq_right (by omega), ite_eq_right (by omega), show 32 + t - 32 = t by omega, h]

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

theorem Sound.rev {x : BitVec 64} {f : Form} (hx : Sound env tbl x f) :
    Sound env tbl x.reverse f.reverse :=
  ⟨by rw [List.length_reverse, hx.1], fun i hi ↦ by
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, getD_reverse hx.1 hi,
      ← hx.bit (by omega), decide_eq_true hi, Bool.true_and]⟩

theorem Sound.bfm {d s : BitVec 64} {fd fs : Form} (hd : Sound env tbl d fd)
    (hs : Sound env tbl s fs) : Sound env tbl (BinOp.apply (.bfm 63 63) .W64 d s) (bfmF fd fs) :=
  ⟨length_bfmF hd.1, fun i hi ↦ by
    rw [getLsbD_bfm d s hi, getD_bfmF hd.1 hi]
    by_cases h : i = 0
    · rw [ite_eq_left h, ite_eq_left h, hs.bit (by decide)]
    · rw [ite_eq_right h, ite_eq_right h, hd.bit hi]⟩

/-- Values with one form are equal. -/
theorem Sound.eq {x y : BitVec 64} {f : Form} (hx : Sound env tbl x f) (hy : Sound env tbl y f) :
    x = y :=
  BitVec.eq_of_getLsbD_eq fun i hi ↦ by rw [hx.bit hi, hy.bit hi]

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

theorem eval_and (env : Env) (a : Sym) (n : Nat) :
    (Sym.bin .and .W64 a (.lit n)).eval env = a.eval env &&& BitVec.ofNat 64 n := and_apply _ _

theorem eval_and' (env : Env) (a : Sym) (n : Nat) :
    (Sym.bin .and .W64 (.lit n) a).eval env = a.eval env &&& BitVec.ofNat 64 n := by
  rw [show (Sym.bin .and .W64 (.lit n) a).eval env = BitVec.ofNat 64 n &&& a.eval env from
    and_apply _ _, BitVec.and_comm]

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
    · rename_i a n
      obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [eval_and]; exact (ih tbl a fa hv ha).and n
    · rename_i n a _
      obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [eval_and']; exact (ih tbl a fa hv ha).and n
    · rename_i a b
      split at h
      · rename_i fa fb ha hb
        cases h
        show Sound env tbl (BinOp.apply .eor .W64 (a.eval env) (b.eval env)) _
        rw [eor_apply]
        exact (ih tbl a fa hv ha).xor (ih tbl b fb hv hb)
      · cases h
    · rename_i a b
      split at h
      · rename_i fa fb ha hb
        split at h
        · rename_i hok
          cases h
          show Sound env tbl (BinOp.apply .orr .W64 (a.eval env) (b.eval env)) _
          rw [orr_apply]
          exact (ih tbl a fa hv ha).or (ih tbl b fb hv hb) hok
        · cases h
      · cases h
    · rename_i a b
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
    · rename_i d a
      split at h
      · rename_i fd fa hd ha
        cases h
        exact (ih tbl d fd hv hd).bfm (ih tbl a fa hv ha)
      · cases h
    · rename_i a
      obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      show Sound env tbl (UnOp.apply .rbit .W64 (a.eval env)) _
      rw [rbit_apply]; exact (ih tbl a fa hv ha).rev
    · rename_i k a
      split at h
      · rename_i hk
        obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        show Sound env tbl (UnOp.apply (.shift .LSL k) .W64 (a.eval env)) _
        rw [lsl_apply]; exact (ih tbl a fa hv ha).shl hk
      · cases h
    · rename_i k a
      split at h
      · rename_i hk
        obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        show Sound env tbl (UnOp.apply (.shift .LSR k) .W64 (a.eval env)) _
        rw [lsr_apply]; exact (ih tbl a fa hv ha).shr hk
      · cases h
    · rename_i immr imms a
      show Sound env tbl (UnOp.apply (.ubfm immr imms) .W64 (a.eval env)) _
      split at h
      · rename_i hc
        obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, h64⟩ := hc
        rw [ubfm_lsr _ _ h64]; exact (ih tbl a fa hv ha).shr (by omega)
      · split at h
        · rename_i hc
          obtain ⟨fa, ha, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨h1, h64⟩ := hc
          rw [ubfm_lsl _ h1 h64]; exact (ih tbl a fa hv ha).shl (by omega)
        · cases h
    · cases h

theorem valid_of_check (env : Env) {fuel : Nat} {tbl : List Entry}
    (h : tbl.all (fun e ↦ lin [] fuel e.a == some e.fa && lin [] fuel e.b == some e.fb) = true) :
    Valid env tbl := by
  intro e he
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨lin_sound env fuel [] e.a e.fa (valid_nil env) this.1,
    lin_sound env fuel [] e.b e.fb (valid_nil env) this.2⟩

/-- **A successful check makes the values equal.** -/
theorem eval_eq_of_check {fuel : Nat} {a b : Sym} (h : check fuel a b = true) (env : Env) :
    a.eval env = b.eval env := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨hv, h⟩ := h
  have hv := valid_of_check env hv
  split at h
  · rename_i f g ha hb
    simp only [beq_iff_eq] at h
    subst h
    exact (lin_sound env fuel _ a f hv ha).eq (lin_sound env fuel _ b f hv hb)
  · cases h

end

end

end NativeRustcVmArm.Field.Lin
