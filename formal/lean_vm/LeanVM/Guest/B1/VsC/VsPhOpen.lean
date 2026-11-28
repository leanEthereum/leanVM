/-
  LeanVM.Guest.B1.VsC.VsPhOpen

  `wC`'s windows `38 ..< 43`: the claims after the ring claim by Horner in `lam`, `open_stacked`, the stream bound,
  `check_stack_terminal`, the export.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh10
public import LeanVM.Guest.B1.VerifySub.PhOpenT
public import LeanVM.Guest.B1.VerifySub.PhOpenLib
public import LeanVM.Guest.B1.Whir.Sound

/-!
# `wC`'s windows `38 ..< 43`

* `vsC_w38` (statements `3914 ..< 4094`): the batched claim `open_stacked` takes, by Horner in `lam` from the
  out-of-domain value (`.n 23`'s word `0`) over the Keccak word, the public input's two limbs, the first `55` sent
  values (`.n 1076`'s words `54` down to `0`) and the memory word, added to the merged ring claim's target
  (`vsVal_3986`, `vsOpenTarget`); the stream's cursor `.n 2920 · g`, the window tables `.n 4 · g^178`. No store, no
  asking atom.
* `vsC_w39` (statement `4094`): `open_stacked__L{sl - 16}` (the dispatch at `.n 489 = g^(sl - 16)`), at a given end.
* `vsC_w40` (statements `4095 ..< 4111`): the stream bound `log(cursor / stream) ≤ 256 · chunks` (`.n 4009`, a
  division by the stream's pointer `.n 55`, its range check against `.n 42^256`), `.n 4014 = y · .n 802`.
* `vsC_w41` (statement `4111`): `check_stack_terminal`, at a given end.
* `vsC_w42` (statements `4112 ..< 4222`): the export, `.n 12`'s first `19` words then `.n 14`'s first `36` stored
  into `.n 5`.

`vsPhOpen_wins` (windows `38 ..< 42`) and `vsPhExport_wins` (window `42`) from numeric hypotheses, `vsPhEnd_wins`
both (`wC.drop 38`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The statements -/

/-- Horner's step `j`: `acc ← (acc + sent[54 - j]) · lam`. -/
def hornA (j : ℕ) : List Atom :=
  [.load (.n (3819 + 3 * j)) (.n 1076) (54 - j), .add (.n (3820 + 3 * j)) (.n (3818 + 3 * j)) (.n (3819 + 3 * j)),
    .mul (.n (3821 + 3 * j)) (.n (3820 + 3 * j)) (.n 3027)]

/-- Statements `3914 ..< 3922`: the out-of-domain value, then the Keccak word and the public input's two limbs. -/
def vsC38pre : List Atom :=
  [.load (.n 3811) (.n 23) 0, .mul (.n 3812) (.n 3811) (.n 3027), .add (.n 3813) (.n 3812) (.n 2921),
    .mul (.n 3814) (.n 3813) (.n 3027), .add (.n 3815) (.n 3814) (.n 2908), .mul (.n 3816) (.n 3815) (.n 3027),
    .add (.n 3817) (.n 3816) (.n 2905), .mul (.n 3818) (.n 3817) (.n 3027)]

/-- Statements `4087 ..< 4094`: the memory word, the ring claim's target, the cursor, the window tables. -/
def vsC38post : List Atom :=
  [.add (.n 3984) (.n 3983) (.n 779), .mul (.n 3985) (.n 3984) (.n 3027), .add (.n 3986) (.n 3810) (.n 3985),
    .const (.n 3987) (word 2 0), .mul (.n 3988) (.n 2920) (.n 3987),
    .const (.n 3989) (word 365917469723852800 0), .mul (.n 3990) (.n 4) (.n 3989)]

/-- Statements `3914 ..< 4094`. -/
def vsC38a : List Atom := vsC38pre ++ (List.range 55).flatMap hornA ++ vsC38post

/-- Statements `4095 ..< 4111`. -/
def vsC40a : List Atom :=
  [.mul (.n 3997) (.n 42) (.n 42), .mul (.n 3998) (.n 3997) (.n 3997), .mul (.n 3999) (.n 3998) (.n 3998),
    .mul (.n 4000) (.n 3999) (.n 3999), .mul (.n 4001) (.n 4000) (.n 4000), .mul (.n 4002) (.n 4001) (.n 4001),
    .mul (.n 4003) (.n 4002) (.n 4002), .mul (.n 4004) (.n 4003) (.n 4003), .const (.n 4005) (word 2 0),
    .mul (.n 4006) (.n 4004) (.n 4005), .const (.n 4007) (word 9223372036854775821 0),
    .mul (.n 4008) (.n 4006) (.n 4007), .mul (.n 3996) (.n 4009) (.n 55),
    .rangeCheck (.n 4009) (.n 4010) (.n 4011) (.n 4012) (.n 4008), .const (.n 4013) (word 0 1),
    .mul (.n 4014) (.n 4013) (.n 802)]

/-- Statements `4112 ..< 4222`: `.n 12`'s first `19` words, then `.n 14`'s first `36`, into `.n 5`. -/
def vsC42a : List Atom :=
  (List.range 19).flatMap (fun j => [.load (.n (4015 + j)) (.n 12) j, .load (.n (4015 + j)) (.n 5) j]) ++
    (List.range 36).flatMap (fun j => [.load (.n (4034 + j)) (.n 14) j, .load (.n (4034 + j)) (.n 5) (19 + j)])

set_option maxRecDepth 200000 in
theorem vsC38_eq : (vsC.drop 3486).take 180 = vsC38a.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC39_eq : (vsC.drop 3666).take 1 = [VerifySub.vsOsDispatch] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC40_eq : (vsC.drop 3667).take 16 = vsC40a.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC41_eq : (vsC.drop 3683).take 1 = [VerifySub.vsCstCall] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC42_eq : (vsC.drop 3684).take 110 = vsC42a.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem vsC_w39_eq : vsC_w39 = .call VerifySub.vsOsDispatch := by rw [vsC_w39, headD_of_take_one vsC39_eq]

theorem vsC_w41_eq : vsC_w41 = .call VerifySub.vsCstCall := by rw [vsC_w41, headD_of_take_one vsC41_eq]

set_option maxRecDepth 200000 in
/-- The fresh loads of windows `38` and `42` are no stores. -/
theorem vsC_fresh_38_42 :
    ((!vsSL.contains (.load (.n 3811) (.n 23) 0)) &&
      (List.range 55).all (fun j => !vsSL.contains (.load (.n (3819 + 3 * j)) (.n 1076) (54 - j))) &&
      (List.range 19).all (fun j => !vsSL.contains (.load (.n (4015 + j)) (.n 12) j)) &&
      (List.range 36).all (fun j => !vsSL.contains (.load (.n (4034 + j)) (.n 14) j))) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem stC42_eq : stC42 = (List.range 19).map (fun j => Atom.load (.n (4015 + j)) (.n 5) j) ++
    (List.range 36).map (fun j => Atom.load (.n (4034 + j)) (.n 5) (19 + j)) := by decide +kernel

theorem not_mem_of_contains {S : List Atom} {a : Atom} (h : (!S.contains a) = true) : a ∉ S :=
  fun hS => absurd h (by simpa using hS)

theorem wC_drop38 : wC.drop 38 = [vsC_w38, vsC_w39, vsC_w40, vsC_w41, vsC_w42] := rfl

/-! ## The values -/

theorem ptrAt_mul_pow (q n : ℕ) : ptrAt q * gen ^ n = ptrAt (q + n) := by
  show ofK (addressOfIndex q) * gen ^ n = ofK (addressOfIndex (q + n))
  rw [← Value.gen_pow_eq_ofK, ← Value.gen_pow_eq_ofK, pow_add]

theorem ptrAt_eq_pow (q : ℕ) : ptrAt q = gen ^ q := (Value.gen_pow_eq_ofK q).symm

set_option maxRecDepth 100000 in
/-- `g^178`, as the data writes it. -/
theorem word_g178' : word 365917469723852800 0 = gen ^ 178 := by
  rw [word_eOfNat, Value.gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

/-- `g^-1`, as the data writes it. -/
theorem winv1_mul : gen * word 9223372036854775821 0 = 1 := by
  rw [← word_gen, show word 2 0 = ofK (K.ofBits 2) from word_eOfNat _,
    show word 9223372036854775821 0 = ofK (K.ofBits 9223372036854775821) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 2 * K.ofBits 9223372036854775821 = 1 by decide +kernel]
  exact map_one (algebraMap K E)

/-- **The batched claim `open_stacked` takes**: the merged ring claim's target `rt`, then by Horner in `lam` the
memory word `m1`, the first `55` sent values, the public input's two limbs `p0`, `p1`, the Keccak word `kw` and the
out-of-domain value `ood`. -/
def vsOpenTarget (rt lam m1 p0 p1 kw ood : E) (sent : List E) : E :=
  rt + (lam * Stack.hornerL lam (sent.take 55 ++ [p0, p1, kw, ood]) + m1) * lam

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

theorem vsC38_good (ha : args.length = 6) : ∀ x ∈ vsC38a, Good rd0 vsSL w (vsVal rd0 w args) x := fun x hx =>
  vsC_atoms_good ha 3486 180 x (by rw [vsC38_eq, atomsOf_map]; exact hx)

/-- **`.n 3986`, `.n 3988`, `.n 3990`**: the batched claim, the cursor past `.n 2920`, the window tables. -/
theorem vsVal_open (ha : args.length = 6) {b23 bm ic0 qt : ℕ} {xs23 xm : List E}
    (h23 : vsVal rd0 w args (.n 23) = ptrAt b23) (hl23 : 1 ≤ xs23.length) (r23 : ReadsAt rd0 (ptrAt b23) xs23)
    (h1076 : vsVal rd0 w args (.n 1076) = ptrAt bm) (hlm : 55 ≤ xm.length) (rm : ReadsAt rd0 (ptrAt bm) xm)
    (h2920 : vsVal rd0 w args (.n 2920) = ptrAt ic0) (h4 : vsVal rd0 w args (.n 4) = ptrAt qt) :
    vsVal rd0 w args (.n 3986) = vsOpenTarget (vsVal rd0 w args (.n 3810)) (vsVal rd0 w args (.n 3027))
      (vsVal rd0 w args (.n 779)) (vsVal rd0 w args (.n 2905)) (vsVal rd0 w args (.n 2908))
      (vsVal rd0 w args (.n 2921)) (xs23.getD 0 0) xm ∧
    vsVal rd0 w args (.n 3988) = ptrAt (ic0 + 1) ∧ vsVal rd0 w args (.n 3990) = ptrAt (qt + 178) := by
  have hg := vsC38_good (rd0 := rd0) (w := w) ha
  set σ := vsVal rd0 w args with hσ
  have mpre : ∀ x ∈ vsC38pre, x ∈ vsC38a := fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)
  have mpost : ∀ x ∈ vsC38post, x ∈ vsC38a := fun x hx => List.mem_append_right _ hx
  have mblk : ∀ j < 55, ∀ x ∈ hornA j, x ∈ vsC38a := fun j hj x hx =>
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩))
  have hfr := vsC_fresh_38_42
  simp only [Bool.and_eq_true] at hfr
  obtain ⟨⟨⟨f0, f1⟩, -⟩, -⟩ := hfr
  -- the pre-chain
  have e3811 : σ (.n 3811) = xs23.getD 0 0 :=
    good_load_get? (not_mem_of_contains f0) (hg _ (mpre _ (by simp [vsC38pre]))) h23 r23
      (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem?_eq_getElem (by omega))
  have m3812 := good_mulF (hg (.mul (.n 3812) (.n 3811) (.n 3027)) (mpre _ (by simp [vsC38pre]))) (by omega) (by omega)
  have a3813 : σ (.n 3813) = σ (.n 3812) + σ (.n 2921) := hg (.add (.n 3813) (.n 3812) (.n 2921)) (mpre _ (by simp [vsC38pre]))
  have m3814 := good_mulF (hg (.mul (.n 3814) (.n 3813) (.n 3027)) (mpre _ (by simp [vsC38pre]))) (by omega) (by omega)
  have a3815 : σ (.n 3815) = σ (.n 3814) + σ (.n 2908) := hg (.add (.n 3815) (.n 3814) (.n 2908)) (mpre _ (by simp [vsC38pre]))
  have m3816 := good_mulF (hg (.mul (.n 3816) (.n 3815) (.n 3027)) (mpre _ (by simp [vsC38pre]))) (by omega) (by omega)
  have a3817 : σ (.n 3817) = σ (.n 3816) + σ (.n 2905) := hg (.add (.n 3817) (.n 3816) (.n 2905)) (mpre _ (by simp [vsC38pre]))
  have m3818 := good_mulF (hg (.mul (.n 3818) (.n 3817) (.n 3027)) (mpre _ (by simp [vsC38pre]))) (by omega) (by omega)
  -- the sent values
  have hsv : ∀ j < 55, σ (.n (3819 + 3 * j)) = xm.getD (54 - j) 0 := fun j hj => by
    have hS := not_mem_of_contains (List.all_eq_true.mp f1 j (List.mem_range.mpr hj))
    exact good_load_get? hS (hg _ (mblk j hj _ (by simp [hornA]))) h1076 rm
      (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem?_eq_getElem (by omega))
  have hchain := VerifySub.horner_chain (fun j => σ (.n (3818 + 3 * j))) (fun j => σ (.n (3819 + 3 * j)))
    (σ (.n 3027)) [σ (.n 2905), σ (.n 2908), σ (.n 2921), σ (.n 3811)] 55
    (by
      show σ (.n 3818) = _
      simp only [Stack.hornerL]
      rw [m3818, a3817, m3816, a3815, m3814, a3813, m3812]
      ring)
    (fun j hj => by
      have a1 : σ (.n (3820 + 3 * j)) = σ (.n (3818 + 3 * j)) + σ (.n (3819 + 3 * j)) :=
        hg (.add (.n (3820 + 3 * j)) (.n (3818 + 3 * j)) (.n (3819 + 3 * j))) (mblk j hj _ (by simp [hornA]))
      have a2 := good_mulF (hg (.mul (.n (3821 + 3 * j)) (.n (3820 + 3 * j)) (.n 3027))
        (mblk j hj _ (by simp [hornA]))) (by omega) (by omega)
      show σ (.n (3818 + 3 * (j + 1))) = _
      rw [show 3818 + 3 * (j + 1) = 3821 + 3 * j by ring, a2, a1]) 55 le_rfl
  have huL : VerifySub.uL (fun j => σ (.n (3819 + 3 * j))) 55 = xm.take 55 := by
    apply List.ext_getElem (by rw [VerifySub.uL_length, List.length_take]; omega)
    intro i h1 h2
    rw [VerifySub.uL_length] at h1
    rw [VerifySub.uL_getElem, List.getElem_take, show 55 - 1 - i = 54 - i by omega, hsv _ (by omega),
      show 54 - (54 - i) = i by omega, List.getD_eq_getElem _ _ (by omega)]
  have a3984 : σ (.n 3984) = σ (.n 3983) + σ (.n 779) := hg (.add (.n 3984) (.n 3983) (.n 779)) (mpost _ (by simp [vsC38post]))
  have m3985 := good_mulF (hg (.mul (.n 3985) (.n 3984) (.n 3027)) (mpost _ (by simp [vsC38post]))) (by omega) (by omega)
  have a3986 : σ (.n 3986) = σ (.n 3810) + σ (.n 3985) := hg (.add (.n 3986) (.n 3810) (.n 3985)) (mpost _ (by simp [vsC38post]))
  have c3987 : σ (.n 3987) = word 2 0 := hg (.const (.n 3987) (word 2 0)) (mpost _ (by simp [vsC38post]))
  have m3988 := good_mulF (hg (.mul (.n 3988) (.n 2920) (.n 3987)) (mpost _ (by simp [vsC38post]))) (by omega) (by omega)
  have c3989 : σ (.n 3989) = word 365917469723852800 0 := hg (.const (.n 3989) (word 365917469723852800 0)) (mpost _ (by simp [vsC38post]))
  have m3990 := good_mulF (hg (.mul (.n 3990) (.n 4) (.n 3989)) (mpost _ (by simp [vsC38post]))) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [a3986, m3985, a3984, show σ (.n 3983) = σ (.n (3818 + 3 * 55)) from rfl, hchain, huL, e3811]
    rfl
  · rw [m3988, c3987, h2920, word_gen, ← pow_one gen, ptrAt_mul_pow]
  · rw [m3990, c3989, h4, word_g178', ptrAt_mul_pow]

theorem vsC40_good (ha : args.length = 6) : ∀ x ∈ vsC40a, Good rd0 vsSL w (vsVal rd0 w args) x := fun x hx =>
  vsC_atoms_good ha 3667 16 x (by rw [vsC40_eq, atomsOf_map]; exact hx)

/-- **The stream bound's values**: `.n 4009 = g^c` (the cursor `c` words past the stream), `.n 4010 = g^(256 p - c)`
(`.n 42 = g^p`, `p` chunks), `.n 4014 = y · .n 802`. -/
theorem vsVal_bound (ha : args.length = 6) {s0 c p : ℕ} (hc : c ≤ 256 * p)
    (h3996 : vsVal rd0 w args (.n 3996) = ptrAt (s0 + c)) (h55 : vsVal rd0 w args (.n 55) = ptrAt s0)
    (h42 : vsVal rd0 w args (.n 42) = gen ^ p) :
    vsVal rd0 w args (.n 4009) = gen ^ c ∧ vsVal rd0 w args (.n 4010) = gen ^ (256 * p - c) ∧
      vsVal rd0 w args (.n 4014) = word 0 1 * vsVal rd0 w args (.n 802) := by
  have hg := vsC40_good (rd0 := rd0) (w := w) ha
  set σ := vsVal rd0 w args with hσ
  have sq : ∀ d x : ℕ, Atom.mul (.n d) (.n x) (.n x) ∈ vsC40a → x < d → σ (.n d) = σ (.n x) * σ (.n x) :=
    fun d x h hx => good_mulF (hg _ h) hx hx
  have e4004 : σ (.n 4004) = gen ^ (256 * p) := by
    rw [sq 4004 4003 (by simp [vsC40a]) (by omega), sq 4003 4002 (by simp [vsC40a]) (by omega),
      sq 4002 4001 (by simp [vsC40a]) (by omega), sq 4001 4000 (by simp [vsC40a]) (by omega),
      sq 4000 3999 (by simp [vsC40a]) (by omega), sq 3999 3998 (by simp [vsC40a]) (by omega),
      sq 3998 3997 (by simp [vsC40a]) (by omega), sq 3997 42 (by simp [vsC40a]) (by omega), h42]
    ring
  have c4005 : σ (.n 4005) = word 2 0 := hg (.const (.n 4005) (word 2 0)) (by simp [vsC40a])
  have c4007 : σ (.n 4007) = word 9223372036854775821 0 :=
    hg (.const (.n 4007) (word 9223372036854775821 0)) (by simp [vsC40a])
  have e4008 : σ (.n 4008) = gen ^ (256 * p) := by
    rw [good_mulF (hg (.mul (.n 4008) (.n 4006) (.n 4007)) (by simp [vsC40a])) (by omega) (by omega),
      good_mulF (hg (.mul (.n 4006) (.n 4004) (.n 4005)) (by simp [vsC40a])) (by omega) (by omega), c4005, c4007,
      e4004, word_gen, mul_assoc, winv1_mul, mul_one]
  have e4009 : σ (.n 4009) = gen ^ c := by
    rw [good_mulD (hg (.mul (.n 3996) (.n 4009) (.n 55)) (by simp [vsC40a])) (by omega), h3996, h55,
      ptrAt_eq_pow, ptrAt_eq_pow, gen_div (Nat.le_add_right s0 c), Nat.add_sub_cancel_left]
  have e4010 : σ (.n 4010) = gen ^ (256 * p - c) := by
    rw [good_rcY (hg (.rangeCheck (.n 4009) (.n 4010) (.n 4011) (.n 4012) (.n 4008)) (by simp [vsC40a])) (by omega),
      e4008, e4009, gen_div hc]
  have c4013 : σ (.n 4013) = word 0 1 := hg (.const (.n 4013) (word 0 1)) (by simp [vsC40a])
  exact ⟨e4009, e4010, by
    rw [good_mulF (hg (.mul (.n 4014) (.n 4013) (.n 802)) (by simp [vsC40a])) (by omega) (by omega), c4013]⟩

end

/-- `check_stack_terminal`'s arguments: `verify_sub`'s values, `open_stacked`'s returns (the oracle's words) and
`y · below_mem`. -/
def cstArgsOf (σ : Val) (w : ℕ → E) : List E :=
  [σ (.n 4), σ (.n 112), σ (.n 486), σ (.n 487), σ (.n 485), σ (.n 15), σ (.n 408), σ (.n 12), σ (.n 101),
    σ (.n 1287), σ (.n 20), σ (.n 17), σ (.n 3040), σ (.n 3026), σ (.n 3027), σ (.n 802), word 0 1 * σ (.n 802),
    w 3992, w 3993, w 3994, w 3995, w 3991, σ (.n 22)]

theorem osNames_get {sl : ℕ} (h16 : 16 ≤ sl) (h30 : sl ≤ 30) :
    VerifySub.vsOsNames[sl - 16]! = Whir.openName sl := by
  have hl : sl - 16 < VerifySub.vsOsNames.length := by
    show sl - 16 < 15
    omega
  rw [getElem!_pos VerifySub.vsOsNames (sl - 16) hl, VerifySub.vsOsNames_get _ hl,
    Whir.openName_eq (by show sl - 16 < 15; omega)]

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `38 ..< 42`' hypotheses**: the out-of-domain value's buffer `.n 23` (`xs23`, at least one word) and
the sent values' `.n 1076` (`xm`, at least `55`), held on the evaluation memory and on every memory with `Pre` and
the words held, in the region; the stack log `16 ≤ sl ≤ 30` (`.n 489 = g^(sl - 16)`); `open_stacked__L{sl - 16}`'s
arguments (`.n 96 = a96`, the capacity `fsv`, the batched claim `vsOpenTarget`, the root's halves, the cursor
`.n 2920 · g`, the window tables `.n 4 · g^178`) and its `CallAtA` at the callees' cursor, returning the oracle's
words `3991 ..< 3997`, ending at `eo`; the stream's bound (`w 3996` the cursor `c` words past the stream `.n 55`,
`.n 42 = g^p`, `c ≤ 256 p < 2^k`); `check_stack_terminal`'s `CallAtA` at `eo` on `cstArgsOf`, ending at `ec`; each
callee's region and precondition from the window's; `K` at `ec`. -/
theorem vsPhOpen_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    {b23 bm : ℕ} {xs23 xm : List E}
    (h23 : vsVal rd0 w args (.n 23) = ptrAt b23) (hl23 : 1 ≤ xs23.length) (r23 : ReadsAt rd0 (ptrAt b23) xs23)
    (hO23 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b23) xs23) (hc23 : Own b23 ∨ R b23 ∨ st.D b23)
    (h1076 : vsVal rd0 w args (.n 1076) = ptrAt bm) (hlm : 55 ≤ xm.length) (rm : ReadsAt rd0 (ptrAt bm) xm)
    (hOm : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt bm) xm)
    (hcm : ∀ j < 55, Own (bm + j) ∨ R (bm + j) ∨ st.D (bm + j))
    {sl ic0 qt : ℕ} (h16 : 16 ≤ sl) (h30 : sl ≤ 30) (h489 : vsVal rd0 w args (.n 489) = gen ^ (sl - 16))
    {a96 h1 h2 : E} {fsv : List E}
    (h96 : vsVal rd0 w args (.n 96) = a96)
    (hfsv : [vsVal rd0 w args (.n 3033), vsVal rd0 w args (.n 3034), vsVal rd0 w args (.n 3035),
      vsVal rd0 w args (.n 3036), vsVal rd0 w args (.n 3037)] = fsv)
    (h134 : vsVal rd0 w args (.n 134) = h1) (h137 : vsVal rd0 w args (.n 137) = h2)
    (h2920 : vsVal rd0 w args (.n 2920) = ptrAt ic0) (h4 : vsVal rd0 w args (.n 4) = ptrAt qt)
    {Ro Do : ℕ → Prop} {Oo Po : Reader → Prop} {Qo : Reader → Tree → Prop} {Bo eo : ℕ}
    (hos : CallAtA fs al cert k (Whir.openName sl)
      (a96 :: fsv ++ [vsOpenTarget (vsVal rd0 w args (.n 3810)) (vsVal rd0 w args (.n 3027))
        (vsVal rd0 w args (.n 779)) (vsVal rd0 w args (.n 2905)) (vsVal rd0 w args (.n 2908))
        (vsVal rd0 w args (.n 2921)) (xs23.getD 0 0) xm, h1, h2, ptrAt (ic0 + 1), ptrAt (qt + 178)])
      [w 3991, w 3992, w 3993, w 3994, w 3995, w 3996] Ro Do Oo Po Qo Bo
      (allocBase (al (Whir.openName sl)) st.kc) (allocBase (al (Whir.openName sl)) st.kc + Bo) eo)
    (hRo : ∀ i, Ro i → (R i ∨ Own i) ∨ st.D i) (hPo : ∀ rd, Pre rd ∧ st.O rd → Po rd)
    {s0 c p : ℕ} (hc : c ≤ 256 * p) (hpk : 256 * p < 2 ^ k)
    (hw3996 : w 3996 = ptrAt (s0 + c)) (h55 : vsVal rd0 w args (.n 55) = ptrAt s0)
    (h42 : vsVal rd0 w args (.n 42) = gen ^ p)
    {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop} {Qc : Reader → Tree → Prop} {Bc ec : ℕ}
    (hcs : CallAtA fs al cert k "check_stack_terminal" (cstArgsOf (vsVal rd0 w args) w) [] Rc Dc Oc Pc Qc Bc
      (allocBase (al "check_stack_terminal") eo) (allocBase (al "check_stack_terminal") eo + Bc) ec)
    (hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ (st.D i ∨ Do i)) (hPc : ∀ rd, Pre rd ∧ (st.O rd ∧ Oo rd) → Pc rd)
    (hK : K ⟨st.a, ec, fun rd => (st.O rd ∧ Oo rd) ∧ Oc rd, fun i => (st.D i ∨ Do i) ∨ Dc i, st.Qs ++ [Qo, Qc]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w38, vsC_w39, vsC_w40, vsC_w41] st K := by
  obtain ⟨e3986, e3988, e3990⟩ := vsVal_open (rd0 := rd0) (w := w) ha h23 hl23 r23 h1076 hlm rm h2920 h4
  have ret39 : ∀ v ∈ [V.n 3991, .n 3992, .n 3993, .n 3994, .n 3995, .n 3996], vsVal rd0 w args v = w v.idx :=
    vsVal_retC ha vsC39_eq
  obtain ⟨e4009, e4010, e4014⟩ := vsVal_bound (rd0 := rd0) (w := w) ha hc
    ((ret39 (.n 3996) (by simp)).trans hw3996) h55 h42
  have hg38 : ∀ x ∈ atomsOf ((vsC.drop 3486).take 180), Good rd0 vsSL w (vsVal rd0 w args) x :=
    vsC_atoms_good ha 3486 180
  have hg40 : ∀ x ∈ atomsOf ((vsC.drop 3667).take 16), Good rd0 vsSL w (vsVal rd0 w args) x :=
    vsC_atoms_good ha 3667 16
  set σ := vsVal rd0 w args with hσ
  -- window `38`
  let bs : ℕ → ℕ := fun v => if v = 23 then b23 else bm
  let xs : ℕ → List E := fun v => if v = 23 then xs23 else xm
  have hsp : ∀ q ∈ spC38, q = (23, 1) ∨ q = (1076, 55) := fun q hq => by simpa [spC38] using hq
  rw [vsC_w38]
  refine winsHyp_run_bufs vsC_w38_bufs hg38 bs xs
    (fun q hq => by rcases hsp q hq with rfl | rfl; exacts [by simpa [bs] using h23, by simpa [bs] using h1076])
    (fun q hq => by rcases hsp q hq with rfl | rfl; exacts [by simpa [xs] using hl23, by simpa [xs] using hlm])
    (fun q hq => by rcases hsp q hq with rfl | rfl; exacts [by simpa [bs, xs] using r23, by simpa [bs, xs] using rm])
    (fun q hq j hj => by
      rcases hsp q hq with rfl | rfl
      · have : j = 0 := by simpa using hj
        subst this; simpa [bs] using hc23
      · simpa [bs] using hcm j hj)
    (fun rd hpr ho q hq => by
      rcases hsp q hq with rfl | rfl
      · simpa [bs, xs] using hO23 rd hpr ho
      · simpa [bs, xs] using hOm rd hpr ho)
    (fun x hx => by simp [stC38] at hx)
    (fun x hx => by rw [vsC_w38_pure] at hx; simp [pureC38] at hx) ?_
  -- window `39`: `open_stacked`
  have hargs39 : (argsOf VerifySub.vsOsDispatch).map σ = a96 :: fsv ++
      [vsOpenTarget (σ (.n 3810)) (σ (.n 3027)) (σ (.n 779)) (σ (.n 2905)) (σ (.n 2908)) (σ (.n 2921))
        (xs23.getD 0 0) xm, h1, h2, ptrAt (ic0 + 1), ptrAt (qt + 178)] := by
    rw [← hfsv, ← h96, ← h134, ← h137, ← e3986, ← e3988, ← e3990]
    rfl
  have hrets39 : (retsOf VerifySub.vsOsDispatch).map σ = [w 3991, w 3992, w 3993, w 3994, w 3995, w 3996] := by
    show [σ (.n 3991), σ (.n 3992), σ (.n 3993), σ (.n 3994), σ (.n 3995), σ (.n 3996)] = _
    rw [ret39 (.n 3991) (by simp), ret39 (.n 3992) (by simp),
      ret39 (.n 3993) (by simp), ret39 (.n 3994) (by simp),
      ret39 (.n 3995) (by simp), ret39 (.n 3996) (by simp)]
  rw [← hargs39, ← hrets39] at hos
  rw [vsC_w39_eq]
  refine winsHyp_call_at (g := Whir.openName sl)
    ⟨sl - 16, by show sl - 16 < 15; omega, by rw [h489, Value.gen_pow_eq_ofK], osNames_get h16 h30⟩
    hos hRo hPo ?_
  -- window `40`: the stream's bound
  rw [vsC_w40]
  refine winsHyp_run_bufs vsC_w40_bufs hg40 (fun _ => 0) (fun _ => [])
    (fun q hq => by simp [spC40] at hq) (fun q hq => by simp [spC40] at hq) (fun q hq => by simp [spC40] at hq)
    (fun q hq => by simp [spC40] at hq) (fun _ _ _ q hq => by simp [spC40] at hq) (fun x hx => by simp [stC40] at hx)
    (fun x hx => by
      rw [vsC_w40_pure] at hx
      simp only [pureC40, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact pureF_div (by rw [h55, ptrAt_eq_pow]; exact pow_ne)
      · exact ⟨by rw [e4009]; exact lowW_pow (by omega), by rw [e4010]; exact lowW_pow (by omega)⟩) ?_
  -- window `41`: `check_stack_terminal`
  have hargs41 : (argsOf VerifySub.vsCstCall).map σ = cstArgsOf σ w := by
    show [σ (.n 4), σ (.n 112), σ (.n 486), σ (.n 487), σ (.n 485), σ (.n 15), σ (.n 408), σ (.n 12), σ (.n 101),
      σ (.n 1287), σ (.n 20), σ (.n 17), σ (.n 3040), σ (.n 3026), σ (.n 3027), σ (.n 802), σ (.n 4014),
      σ (.n 3992), σ (.n 3993), σ (.n 3994), σ (.n 3995), σ (.n 3991), σ (.n 22)] = _
    rw [e4014, ret39 (.n 3991) (by simp), ret39 (.n 3992) (by simp),
      ret39 (.n 3993) (by simp), ret39 (.n 3994) (by simp),
      ret39 (.n 3995) (by simp)]
    rfl
  rw [← hargs41, show ([] : List E) = (retsOf VerifySub.vsCstCall).map σ from rfl] at hcs
  rw [vsC_w41_eq]
  refine winsHyp_call_at (g := "check_stack_terminal") rfl hcs hRc hPc ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => Iff.rfl) (fun i => Iff.rfl) (by simp)

/-- **`wC`'s window `42`' hypotheses**, the export: `.n 12` (`xs12`, at least `19` words), `.n 14` (`xs14`, at least
`36`) and `.n 5` (`xs5`, `.n 12`'s first `19` then `.n 14`'s first `36`), held on the evaluation memory and on every
memory with `Pre` and the words held, in the region; `K` at the same state. -/
theorem vsPhExport_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    {b5 b12 b14 : ℕ} {xs5 xs12 xs14 : List E}
    (h12 : vsVal rd0 w args (.n 12) = ptrAt b12) (hl12 : 19 ≤ xs12.length) (r12 : ReadsAt rd0 (ptrAt b12) xs12)
    (hO12 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b12) xs12)
    (hc12 : ∀ j < 19, Own (b12 + j) ∨ R (b12 + j) ∨ st.D (b12 + j))
    (h14 : vsVal rd0 w args (.n 14) = ptrAt b14) (hl14 : 36 ≤ xs14.length) (r14 : ReadsAt rd0 (ptrAt b14) xs14)
    (hO14 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b14) xs14)
    (hc14 : ∀ j < 36, Own (b14 + j) ∨ R (b14 + j) ∨ st.D (b14 + j))
    (h5 : vsVal rd0 w args (.n 5) = ptrAt b5) (hx5 : xs5 = xs12.take 19 ++ xs14.take 36)
    (r5 : ReadsAt rd0 (ptrAt b5) xs5) (hO5 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b5) xs5)
    (hc5 : ∀ j < 55, Own (b5 + j) ∨ R (b5 + j) ∨ st.D (b5 + j)) (hK : K st) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w42] st K := by
  have hg42 : ∀ x ∈ atomsOf ((vsC.drop 3684).take 110), Good rd0 vsSL w (vsVal rd0 w args) x :=
    vsC_atoms_good ha 3684 110
  set σ := vsVal rd0 w args with hσ
  have hl5 : xs5.length = 55 := by rw [hx5]; simp; omega
  let bs : ℕ → ℕ := fun v => if v = 12 then b12 else if v = 5 then b5 else b14
  let xs : ℕ → List E := fun v => if v = 12 then xs12 else if v = 5 then xs5 else xs14
  have hsp : ∀ q ∈ spC42, q = (12, 19) ∨ q = (5, 55) ∨ q = (14, 36) := fun q hq => by simpa [spC42] using hq
  have m42 : ∀ x ∈ vsC42a, x ∈ atomsOf ((vsC.drop 3684).take 110) := fun x hx => by
    rw [vsC42_eq, atomsOf_map]; exact hx
  have hfr := vsC_fresh_38_42
  simp only [Bool.and_eq_true] at hfr
  obtain ⟨⟨-, f12⟩, f14⟩ := hfr
  have hst : ∀ x ∈ stC42, MemF rd0 σ x := by
    intro x hx
    rw [stC42_eq, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hj' := List.mem_range.mp hj
      have v := good_load_get? (not_mem_of_contains (List.all_eq_true.mp f12 j hj))
        (hg42 _ (m42 _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, hj, by simp⟩)))) h12 r12
        (List.getElem?_eq_getElem (by omega))
      show LoadHolds rd0 (σ (.n 5)) j (σ (.n (4015 + j)))
      rw [h5, v]
      refine loadHolds_of_get? r5 ?_
      rw [hx5, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj',
        List.getElem?_eq_getElem (by omega)]
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hj' := List.mem_range.mp hj
      have v := good_load_get? (not_mem_of_contains (List.all_eq_true.mp f14 j hj))
        (hg42 _ (m42 _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, hj, by simp⟩)))) h14 r14
        (List.getElem?_eq_getElem (by omega))
      show LoadHolds rd0 (σ (.n 5)) (19 + j) (σ (.n (4034 + j)))
      rw [h5, v]
      refine loadHolds_of_get? r5 ?_
      rw [hx5, List.getElem?_append_right (by simp), List.length_take, Nat.min_eq_left hl12,
        show 19 + j - 19 = j by omega, List.getElem?_take_of_lt hj', List.getElem?_eq_getElem (by omega)]
  rw [vsC_w42]
  refine winsHyp_run_bufs vsC_w42_bufs hg42 bs xs
    (fun q hq => by
      rcases hsp q hq with rfl | rfl | rfl
      · simpa [bs] using h12
      · simpa [bs] using h5
      · simpa [bs] using h14)
    (fun q hq => by
      rcases hsp q hq with rfl | rfl | rfl
      · simpa [xs] using hl12
      · simpa [xs] using hl5.ge
      · simpa [xs] using hl14)
    (fun q hq => by
      rcases hsp q hq with rfl | rfl | rfl
      · simpa [bs, xs] using r12
      · simpa [bs, xs] using r5
      · simpa [bs, xs] using r14)
    (fun q hq j hj => by
      rcases hsp q hq with rfl | rfl | rfl
      · simpa [bs] using hc12 j hj
      · simpa [bs] using hc5 j hj
      · simpa [bs] using hc14 j hj)
    (fun rd hpr ho q hq => by
      rcases hsp q hq with rfl | rfl | rfl
      · simpa [bs, xs] using hO12 rd hpr ho
      · simpa [bs, xs] using hO5 rd hpr ho
      · simpa [bs, xs] using hO14 rd hpr ho)
    hst (fun x hx => by rw [vsC_w42_pure] at hx; simp [pureC42] at hx) ?_
  rw [WinsHyp]
  exact hK

end

end
end LeanVM.Guest.B1.VsC
