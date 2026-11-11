/-
  LeanVM.Guest.B1.Gkr.VbgOdd

  `verify_bus_gkr`'s evaluation list, and its root-most layer, completely: from the roots, one
  step of one level (an odd depth) or two (an even one), its words at the cursor and the slot it
  leads to, the layer's arm holds on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7Complete
public import LeanVM.Guest.B1.Gkr.Holds

/-!
# The root-most layer, completely (G:1960-2019)

`vbgEvL`: `verify_bus_gkr`'s body as the forward evaluator walks it (its `ite`'s arms in order,
the checked inverse as its product, `fixNe`); `vb_good`, `rt_goodB`: the statements of the body
and of the root-most layer's arms satisfy their equations.

* `chc_read`, `chc_val`: a child's read and a tree's new value at two coordinates, on their
  equations (shared with `__loop6`'s templates `chT`, `chValT`);
* `rtc_two`: the binary arm (`rtTwo`, an odd depth): six children, one coordinate, the slot of
  `L = 1`;
* `rtc_four`: the radix-four arm (`rtFour`, an even depth): twelve children, two coordinates, the
  slot of `L = 2`.

Both start from the body's combiner `σ 59`, the claim `σ 63`, the capacity after the combiner
`σ 54 .. σ 58` and the zeros `σ 42 .. σ 45`, the children past the roots at `σ 5·g^2`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The evaluation list -/

/-- `verify_bus_gkr`'s evaluation list. -/
noncomputable def vbgEvL : List Stmt := (flatIte vbgPre).map fixNe

theorem vb_chk : (chk 9 vbgEvL).isSome = true := by decide +kernel

/-- `verify_bus_gkr`'s stores. -/
noncomputable def vbgS : List Atom := storesOf 9 vbgEvL

/-- Not an `assertNe`. -/
def noNeB : Stmt → Bool
  | .atom (.assertNe ..) => false
  | _ => true

theorem fixNe_of_noNe {s : Stmt} (h : noNeB s = true) : fixNe s = s := by
  cases s with
  | atom a => cases a <;> first | rfl | simp [noNeB] at h
  | _ => rfl

theorem rtArms_noNe : (rtFour ++ rtTwo).all noNeB = true := by decide +kernel

theorem tb_mem_of_slice {pre : List Stmt} {n : ℕ} {blk : List Stmt}
    (h : tbStmtsEqb blk ((pre.drop n).take blk.length) = true) : ∀ s ∈ blk, s ∈ pre := by
  intro s hs
  rw [tbStmtsEqb_sound h] at hs
  exact List.mem_of_mem_drop (List.mem_of_mem_take hs)

/-! ## The arms, as lists -/

/-- A tree's new value at one coordinate `y = σ 357` (`lo + y·(lo + hi)`), stored at `off`. -/
def rtVal (b u v off : ℕ) : List Stmt :=
  [.atom (.add (.n b) (.n u) (.n v)), .atom (.mul (.n (b + 1)) (.n 357) (.n b)),
    .atom (.add (.n (b + 2)) (.n u) (.n (b + 1))), .atom (.load (.n (b + 2)) (.n 16) off)]

/-- The binary arm. -/
def rtTwoL : List Stmt :=
  ((List.range 4).map (chT (.n 5) 2 297)).flatten ++
  [keccakA (chRate 297 0 ++ lyCap 46) (lyOuts 313)] ++
  chT (.n 5) 2 297 4 ++ chT (.n 5) 2 297 5 ++
  [.atom (.mul (.n 334) (.n 329) (.n 333)), .atom (.const (.n 335) (word 0 0)),
    .atom (.mul (.n 336) (.n 59) (.n 335)), .atom (.add (.n 337) (.n 334) (.n 336)),
    .atom (.mul (.n 338) (.n 308) (.n 312)), .atom (.mul (.n 339) (.n 59) (.n 337)),
    .atom (.add (.n 340) (.n 338) (.n 339)), .atom (.mul (.n 341) (.n 300) (.n 304)),
    .atom (.mul (.n 342) (.n 59) (.n 340)), .atom (.add (.n 343) (.n 341) (.n 342)),
    .atom (.assertEq (.n 63) (.n 343)),
    keccakA ([.n 327, .n 328, .n 331, .n 332, .n 42, .n 43, .n 44, .n 45] ++ lyCap 313)
      (lyOuts 344)] ++
  challengeT (.n 344) 357 ++
  [.atom (.load (.n 357) (.n 18) 40)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (352 + k)) (.n 16) (13 + k))) ++
  [.atom (.const (.n 358) (word 256 0)), .atom (.mul (.n 359) (.n 5) (.n 358)),
    .atom (.load (.n 359) (.n 16) 18)] ++
  rtVal 360 300 304 19 ++ rtVal 363 308 312 20 ++ rtVal 366 329 333 21 ++
  [.atom (.const (.n 369) (word 1099511627776 0)), .atom (.mul (.n 370) (.n 18) (.n 369)),
    .atom (.load (.n 370) (.n 16) 22), .atom (.const (.n 371) (word 2 0)),
    .atom (.load (.n 371) (.n 16) 23), .atom (.const (.n 372) (word 1 0)),
    .atom (.load (.n 372) (.n 16) 24), .atom (.const (.n 373) (word 1 0)),
    .atom (.load (.n 373) (.n 16) 25)]

set_option maxRecDepth 10000 in
theorem rtTwo_eq : rtTwo = rtTwoL := tbStmtsEqb_sound (by decide +kernel)

/-- The radix-four arm. -/
def rtFourL : List Stmt :=
  ((List.range 4).map (chT (.n 5) 2 145)).flatten ++
  [keccakA (chRate 145 0 ++ lyCap 46) (lyOuts 161)] ++
  ((List.range 4).map fun i ↦ chT (.n 5) 2 145 (4 + i)).flatten ++
  [keccakA (chRate 145 1 ++ lyCap 161) (lyOuts 190)] ++
  ((List.range 4).map fun i ↦ chT (.n 5) 2 145 (8 + i)).flatten ++
  [.atom (.mul (.n 219) (.n 206) (.n 210)), .atom (.mul (.n 220) (.n 219) (.n 214)),
    .atom (.mul (.n 221) (.n 220) (.n 218)), .atom (.const (.n 222) (word 0 0)),
    .atom (.mul (.n 223) (.n 59) (.n 222)), .atom (.add (.n 224) (.n 221) (.n 223)),
    .atom (.mul (.n 225) (.n 177) (.n 181)), .atom (.mul (.n 226) (.n 225) (.n 185)),
    .atom (.mul (.n 227) (.n 226) (.n 189)), .atom (.mul (.n 228) (.n 59) (.n 224)),
    .atom (.add (.n 229) (.n 227) (.n 228)), .atom (.mul (.n 230) (.n 148) (.n 152)),
    .atom (.mul (.n 231) (.n 230) (.n 156)), .atom (.mul (.n 232) (.n 231) (.n 160)),
    .atom (.mul (.n 233) (.n 59) (.n 229)), .atom (.add (.n 234) (.n 232) (.n 233)),
    .atom (.assertEq (.n 63) (.n 234)),
    keccakA (chRate 145 2 ++ lyCap 190) (lyOuts 235)] ++
  challengeT (.n 235) 248 ++
  [keccakA ([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++ lyCap 235) (lyOuts 249)] ++
  challengeT (.n 249) 262 ++
  [.atom (.load (.n 248) (.n 18) 40), .atom (.load (.n 262) (.n 18) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (257 + k)) (.n 16) (26 + k))) ++
  [.atom (.const (.n 263) (word 16384 0)), .atom (.mul (.n 264) (.n 5) (.n 263)),
    .atom (.load (.n 264) (.n 16) 31)] ++
  chValT 145 248 262 16 0 265 32 ++ chValT 145 248 262 16 1 274 33 ++
  chValT 145 248 262 16 2 283 34 ++
  [.atom (.const (.n 292) (word 1099511627776 0)), .atom (.mul (.n 293) (.n 18) (.n 292)),
    .atom (.load (.n 293) (.n 16) 35), .atom (.const (.n 294) (word 2 0)),
    .atom (.load (.n 294) (.n 16) 36), .atom (.const (.n 295) (word 1 0)),
    .atom (.load (.n 295) (.n 16) 37), .atom (.const (.n 296) (word 2 0)),
    .atom (.load (.n 296) (.n 16) 38)]

set_option maxRecDepth 10000 in
theorem rtFour_eq : rtFour = rtFourL := tbStmtsEqb_sound (by decide +kernel)

section Eval

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {kret : List E → Prop}

/-- A statement of the body satisfies its equations. -/
theorem vb_good (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vbgPre.drop n).take 1) = true)
    (hfix : fixNe (.atom a) = .atom a) : Good rd vbgS w σ a := by
  have h := good_slice (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) n [.atom a] heq rfl _ List.mem_cons_self
  rw [hfix] at h
  exact h

/-- The statements of the root-most layer's arms satisfy their equations. -/
theorem rt_goodArms (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) :
    ∀ t ∈ rtFour ++ rtTwo, GoodS rd vbgS w σ t := by
  have h := good_ite (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) 196 (.n 144) rtFour rtTwo (by decide +kernel)
  intro t ht
  have := h t ht
  rwa [fixNe_of_noNe (List.all_eq_true.mp rtArms_noNe t ht)] at this

/-- A block of the binary arm satisfies its equations. -/
theorem rt2_goodB (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((rtTwo.drop n).take blk.length) = true) :
    ∀ s ∈ blk, GoodS rd vbgS w σ s :=
  fun s hs => rt_goodArms hG s (List.mem_append_right _ (tb_mem_of_slice heq s hs))

/-- A block of the radix-four arm satisfies its equations. -/
theorem rt4_goodB (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((rtFour.drop n).take blk.length) = true) :
    ∀ s ∈ blk, GoodS rd vbgS w σ s :=
  fun s hs => rt_goodArms hG s (List.mem_append_left _ (tb_mem_of_slice heq s hs))

/-- **A child's read on its equations**: its word, packed and copied. -/
theorem chc_read {cur o b0 i : ℕ} (gb : ∀ s ∈ chT (.n cur) o b0 i, GoodS rd S w σ s)
    (hk : some (chB b0 i, cur, o + i) ∉ S.map loadKey) {v : E}
    (hl : LoadHolds rd (σ (.n cur)) (o + i) v) :
    σ (.n (chB b0 i)) = v ∧ σ (.n (chB b0 i + 3)) = σ (.n (chB b0 i)) ∧
      FsPackOk σ (.n (chB b0 i)) (chB b0 i + 1) dsObserve ∧
      ∀ s ∈ chT (.n cur) o b0 i, SHolds C rd σ s := by
  obtain ⟨e0, -, hfs⟩ := fsNextT_good (C := C) (kret := fun _ => True)
    (fun s hs => gb s (by unfold chT; exact List.mem_append_left _ hs)) hk hl
  have cp : σ (.n (chB b0 i + 3)) = σ (.n (chB b0 i)) :=
    gb (.atom (.copy (.n (chB b0 i + 3)) (.n (chB b0 i)))) (by simp [chT])
  obtain ⟨⟨hld, hok⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs
  refine ⟨e0, cp, hok, ?_⟩
  simp only [chT, fsNextT, fsPackT, List.forall_mem_append, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
  exact ⟨hld, hok.1, hok.2, cp⟩

/-- **A tree's new value on its equations**: its four children's multilinear value at the two
coordinates `c0`, `c1`, stored at `off`. -/
theorem chc_val {b0 c0 c1 slot t b off : ℕ}
    (gb : ∀ s ∈ chValT b0 c0 c1 slot t b off, GoodS rd S w σ s) (hc0 : c0 < b) (hc1 : c1 < b)
    (cp : ∀ i < 4, σ (.n (chB b0 (4 * t + i) + 3)) = σ (.n (chB b0 (4 * t + i))))
    (hl : LoadHolds rd (σ (.n slot)) off (multilinearEval (chWords σ b0 t) [σ (.n c0), σ (.n c1)])) :
    ∀ s ∈ chValT b0 c0 c1 slot t b off, SHolds C rd σ s := by
  have a0 : σ (.n b) = σ (.n (chB b0 (4 * t + 0) + 3)) + σ (.n (chB b0 (4 * t + 1) + 3)) :=
    gb (.atom (.add (.n b) _ _)) (by simp [chValT])
  have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n c0) (.n b))) (by simp [chValT]))
    (by omega) (by omega)
  have a2 : σ (.n (b + 2)) = σ (.n (chB b0 (4 * t + 0) + 3)) + σ (.n (b + 1)) :=
    gb (.atom (.add (.n (b + 2)) _ _)) (by simp [chValT])
  have a3 : σ (.n (b + 3)) = σ (.n (chB b0 (4 * t + 2) + 3)) + σ (.n (chB b0 (4 * t + 3) + 3)) :=
    gb (.atom (.add (.n (b + 3)) _ _)) (by simp [chValT])
  have m4 := good_mulS (gb (.atom (.mul (.n (b + 4)) (.n c0) (.n (b + 3)))) (by simp [chValT]))
    (by omega) (by omega)
  have a5 : σ (.n (b + 5)) = σ (.n (chB b0 (4 * t + 2) + 3)) + σ (.n (b + 4)) :=
    gb (.atom (.add (.n (b + 5)) _ _)) (by simp [chValT])
  have a6 : σ (.n (b + 6)) = σ (.n (b + 2)) + σ (.n (b + 5)) :=
    gb (.atom (.add (.n (b + 6)) _ _)) (by simp [chValT])
  have m7 := good_mulS (gb (.atom (.mul (.n (b + 7)) (.n c1) (.n (b + 6)))) (by simp [chValT]))
    (by omega) (by omega)
  have a8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7)) :=
    gb (.atom (.add (.n (b + 8)) _ _)) (by simp [chValT])
  have e8 : σ (.n (b + 8)) = multilinearEval (chWords σ b0 t) [σ (.n c0), σ (.n c1)] := by
    rw [a8, m7, a6, a5, m4, a3, a2, m1, a0, cp 0 (by omega), cp 1 (by omega),
      cp 2 (by omega), cp 3 (by omega), chWords_eq]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    ring_nf
  simp only [chValT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨a0, m1, a2, a3, m4, a5, a6, m7, a8,
    show LoadHolds rd (σ (.n slot)) off (σ (.n (b + 8))) by rw [e8]; exact hl⟩

end Eval

theorem tb_list2_eq {l : List E} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem tb_list4_eq {l : List E} (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

section Arms

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val} {kret : List E → Prop}

/-- **The binary arm, completely** (an odd depth): from the sponge `s` the roots wait in, one
step of one level (no point), its six words past the roots, and the slot of `L = 1`. -/
theorem rtc_two (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) {s : Fs} {st : GkrState}
    (hpt : st.point = [])
    (h59 : σ (.n 59) = s.squeeze.1) (h63 : σ (.n 63) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0)
    {D : GkStepD} (hD : D.Ok s st 1) (hx : TbReadsAt rd (σ (.n 5) * gen ^ 2) D.xs)
    (hS' : GkSlot rd (σ (.n 16)) 1 (D.s' s st 1) (σ (.n 5) * gen ^ 2 * gen ^ D.xs.length)
      (D.st' s st 1) (σ (.n 18) * gen ^ 40) gen 1 1) :
    Stmt.HoldsList C rd σ rtTwo True kret := by
  obtain ⟨-, hcap', -, hcur', -, hval', hrow', -, hpt', hpos', hhalf', hpar'⟩ := hS'
  obtain ⟨cs, ch0, ch1, ch2⟩ := D
  obtain ⟨hl, -, h0, h1, h2, hchk⟩ := hD
  simp only at hl h0 h1 h2 hchk
  rw [hpt] at hl
  rw [show (2 : ℕ) ^ 1 = 2 from rfl] at h0 h1 h2
  obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero hl
  obtain ⟨w0, w1, rfl⟩ := tb_list2_eq h0
  obtain ⟨w2, w3, rfl⟩ := tb_list2_eq h1
  obtain ⟨w4, w5, rfl⟩ := tb_list2_eq h2
  have hxs : GkStepD.xs ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ = [w0, w1, w2, w3, w4, w5] := rfl
  rw [hxs] at hx hcur'
  -- the children
  have hk : ∀ i < 6, some (chB 297 i, 5, 2 + i) ∉ vbgS.map loadKey := by decide +kernel
  have ch : ∀ i < 6, LoadHolds rd (σ (.n 5)) (2 + i) ([w0, w1, w2, w3, w4, w5].getD i 0) := by
    intro i hi
    have := hx i (by simp; omega)
    rw [tb_loadHolds_mul_gen_pow] at this
    rwa [← List.getD_eq_getElem _ 0] at this
  have EV : ∀ i < 6, _ := fun i hi => chc_read (C := C)
    (rt2_goodB hG (rtPos i) (chT (.n 5) 2 297 i) (rtTwo_check i hi)) (hk i hi) (ch i hi)
  have ev : ∀ i < 6, ∀ v, [w0, w1, w2, w3, w4, w5].getD i 0 = v → σ (.n (chB 297 i)) = v :=
    fun i hi v hv => (EV i hi).1.trans hv
  have q : ∀ i < 6, ∀ v, [w0, w1, w2, w3, w4, w5].getD i 0 = v → σ (.n (chB 297 i + 3)) = v :=
    fun i hi v hv => (EV i hi).2.1.trans ((EV i hi).1.trans hv)
  have hp : ∀ i < 6, FsPackOk σ (.n (chB 297 i)) (chB 297 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.2.1
  have q0 : σ (.n 300) = w0 := q 0 (by omega) w0 rfl
  have q1 : σ (.n 304) = w1 := q 1 (by omega) w1 rfl
  have q2 : σ (.n 308) = w2 := q 2 (by omega) w2 rfl
  have q3 : σ (.n 312) = w3 := q 3 (by omega) w3 rfl
  have q4 : σ (.n 329) = w4 := q 4 (by omega) w4 rfl
  have q5 : σ (.n 333) = w5 := q 5 (by omega) w5 rfl
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((rtTwo.drop n).take 1) = true →
      Good rd vbgS w σ a := fun n a heq => rt2_goodB hG n [.atom a] heq (.atom a) List.mem_cons_self
  -- the first four children's permutation
  obtain ⟨k16, -⟩ := keccak_good (g 16 (.keccak (chRate 297 0 ++ lyCap 46) (lyOuts 313) false false)
    (by decide +kernel))
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k16
  rw [hcap] at B0
  have hw0 : chWords σ 297 0 = [w0, w1, w2, w3] := by
    rw [chWords_eq]
    simp only [show 4 * 0 = 0 from rfl, Nat.zero_add]
    rw [ev 0 (by omega) w0 rfl, ev 1 (by omega) w1 rfl, ev 2 (by omega) w2 rfl,
      ev 3 (by omega) w3 rfl]
  rw [hw0] at B0
  -- the check
  have m334 := good_mul (g 25 (.mul (.n 334) (.n 329) (.n 333)) (by decide +kernel)) (by omega)
    (by omega)
  have c335 : σ (.n 335) = word 0 0 := g 26 (.const (.n 335) (word 0 0)) (by decide +kernel)
  have m336 := good_mul (g 27 (.mul (.n 336) (.n 59) (.n 335)) (by decide +kernel)) (by omega)
    (by omega)
  have a337 : σ (.n 337) = σ (.n 334) + σ (.n 336) :=
    g 28 (.add (.n 337) (.n 334) (.n 336)) (by decide +kernel)
  have m338 := good_mul (g 29 (.mul (.n 338) (.n 308) (.n 312)) (by decide +kernel)) (by omega)
    (by omega)
  have m339 := good_mul (g 30 (.mul (.n 339) (.n 59) (.n 337)) (by decide +kernel)) (by omega)
    (by omega)
  have a340 : σ (.n 340) = σ (.n 338) + σ (.n 339) :=
    g 31 (.add (.n 340) (.n 338) (.n 339)) (by decide +kernel)
  have m341 := good_mul (g 32 (.mul (.n 341) (.n 300) (.n 304)) (by decide +kernel)) (by omega)
    (by omega)
  have m342 := good_mul (g 33 (.mul (.n 342) (.n 59) (.n 340)) (by decide +kernel)) (by omega)
    (by omega)
  have a343 : σ (.n 343) = σ (.n 341) + σ (.n 342) :=
    g 34 (.add (.n 343) (.n 341) (.n 342)) (by decide +kernel)
  have e343 : σ (.n 343) = polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]]
      s.squeeze.1 := by
    rw [a343, m342, a340, m339, a337, m336, c335, tb_word_zero, m334, m338, m341, q0, q1, q2, q3,
      q4, q5, h59]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  have hrun : (GkStepD.run ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st).2.1 =
      polyEval st.values s.squeeze.1 := by
    rw [GkStepD.run, hpt]; rfl
  rw [hrun] at hchk
  -- the new coordinate
  obtain ⟨e327, e328⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 4 (by omega)))
  obtain ⟨e331, e332⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 5 (by omega)))
  norm_num [chB] at e327 e328 e331 e332
  rw [show σ (.n 326) = w4 from ev 4 (by omega) w4 rfl] at e327 e328
  rw [show σ (.n 330) = w5 from ev 5 (by omega) w5 rfl] at e331 e332
  set P2 := Fs.perm ⟨capOf s.perm, [w0, w1, w2, w3].map (·, dsObserve)⟩ with hP2
  have hr2 : (([.n 327, .n 328, .n 331, .n 332, .n 42, .n 43, .n 44, .n 45] ++ lyCap 313 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ capOf P2 := by
    rw [List.map_append, B0, rateOf_eq_cells _ (by simp)]
    simp [pendCells, e327, e328, e331, e332, z42, z43, z44, z45]
  obtain ⟨k36, hP3, hC3⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := w)
    (g 36 (.keccak ([.n 327, .n 328, .n 331, .n 332, .n 42, .n 43, .n 44, .n 45] ++
      lyCap 313) (lyOuts 344) false false) (by decide +kernel))
  rw [hr2] at hP3 hC3
  have hco := challengeT_good (rt2_goodB hG 37 (challengeT (.n 344) 357) (by decide +kernel))
  have e357 : σ (.n 357) = challengeOf (permOf (rateOf [(w4, dsObserve), (w5, dsObserve)] ++
      capOf P2)) := challengeT_value hco (hP3 0 (by omega))
  -- the sponge after the children
  have hsb : GkStepD.sb ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st =
      ⟨capOf P2, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
    show (((GkStepD.run ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st).2.2.absorbAll [w0, w1]
      dsObserve).absorbAll [w2, w3] dsObserve).absorbAll [w4, w5] dsObserve = _
    rw [show (GkStepD.run ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st).2.2 = s.squeeze.2 by
      rw [GkStepD.run, hpt]; rfl]
    have e1 : s.squeeze.2.absorbAll [w0, w1] dsObserve =
        ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ := by
      rw [absorbAll_short _ _ _ (by simp [Fs.squeeze])]; rfl
    have e2 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll [w2, w3]
        dsObserve = ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
          (w3, dsObserve)]⟩ := by
      rw [absorbAll_short _ _ _ (by simp)]; rfl
    have e3 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
        (w3, dsObserve)]⟩ : Fs).absorbAll [w4, w5] dsObserve =
          ⟨capOf P2, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
      rw [tb_absorbAll_full' _ (by simp) _ (by simp) (by simp)]; rfl
    rw [e1, e2, e3]
  have hy : GkStepD.ys ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = [σ (.n 357)] := by
    rw [e357]; show ((GkStepD.sb _ s st).squeezeN 1).1 = _; rw [hsb]; rfl
  have hs' : GkStepD.s' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = ⟨(lyCap 344).map σ, []⟩ := by
    rw [hC3]; show ((GkStepD.sb _ s st).squeezeN 1).2 = _; rw [hsb]; rfl
  -- the slot of `L = 1`
  have hpt1 : (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).point = [σ (.n 357)] := by
    show GkStepD.ys _ s st 1 ++ (GkStepD.run _ s st).1 = _
    rw [hy, GkStepD.run, hpt]; rfl
  have hval1 : ∀ t < 3, (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).values.getD t 0 =
      multilinearEval ([[w0, w1], [w2, w3], [w4, w5]].getD t []) [σ (.n 357)] := by
    intro t ht
    show ([[w0, w1], [w2, w3], [w4, w5]].map (multilinearEval · (GkStepD.ys _ s st 1))).getD t 0 = _
    rw [hy]
    interval_cases t <;> rfl
  have s357 : LoadHolds rd (σ (.n 18)) 40 (σ (.n 357)) := by
    have := hpt' 0 (by rw [hpt1]; simp)
    simp only [hpt1, List.getElem_cons_zero] at this
    rw [tb_loadHolds_mul_gen_pow] at this
    exact this
  have s352 : ∀ k < 5, LoadHolds rd (σ (.n 16)) (13 + k) (σ (.n (352 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simpa [lyCap, List.getD_eq_getElem?_getD, hk, show 344 + 8 + k = 352 + k by omega] using this
  have c358 : σ (.n 358) = word 256 0 := g 44 (.const (.n 358) (word 256 0)) (by decide +kernel)
  have m359 := good_mul (g 45 (.mul (.n 359) (.n 5) (.n 358)) (by decide +kernel)) (by omega)
    (by omega)
  have w8 : word 256 0 = gen ^ 8 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)]
  have s359 : LoadHolds rd (σ (.n 16)) 18 (σ (.n 359)) := by
    rw [m359, c358, w8, show (8 : ℕ) = 2 + 6 by rfl, pow_add, ← mul_assoc]
    exact hcur'
  have VAL : ∀ t < 3, ∀ (b u v off : ℕ), u < b → v < b → 357 < b →
      (∀ s ∈ rtVal b u v off, GoodS rd vbgS w σ s) →
      LoadHolds rd (σ (.n 16)) off (σ (.n u) + σ (.n 357) * (σ (.n u) + σ (.n v))) →
      ∀ s ∈ rtVal b u v off, SHolds C rd σ s := by
    intro t _ b u v off hu hv h3 gb hl
    have a0 : σ (.n b) = σ (.n u) + σ (.n v) := gb (.atom (.add (.n b) _ _)) (by simp [rtVal])
    have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 357) (.n b))) (by simp [rtVal]))
      (by omega) (by omega)
    have a2 : σ (.n (b + 2)) = σ (.n u) + σ (.n (b + 1)) :=
      gb (.atom (.add (.n (b + 2)) _ _)) (by simp [rtVal])
    simp only [rtVal, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    exact ⟨a0, m1, a2, show LoadHolds rd (σ (.n 16)) off (σ (.n (b + 2))) by
      rw [a2, m1, a0]; exact hl⟩
  have hv' : ∀ t < 3, ∀ u v, [[w0, w1], [w2, w3], [w4, w5]].getD t [] = [σ (.n u), σ (.n v)] →
      LoadHolds rd (σ (.n 16)) (19 + t) (σ (.n u) + σ (.n 357) * (σ (.n u) + σ (.n v))) := by
    intro t ht u v huv
    have h := hval' t ht
    rw [hval1 t ht, huv, show 13 * 1 + 6 + t = 19 + t by ring] at h
    convert h using 1
    simp [multilinearEval, foldPairs]
    ring
  have V0 := VAL 0 (by omega) 360 300 304 19 (by omega) (by omega) (by omega)
    (rt2_goodB hG 47 _ (by decide +kernel)) (hv' 0 (by omega) 300 304 (by rw [q0, q1]; rfl))
  have V1 := VAL 1 (by omega) 363 308 312 20 (by omega) (by omega) (by omega)
    (rt2_goodB hG 51 _ (by decide +kernel)) (hv' 1 (by omega) 308 312 (by rw [q2, q3]; rfl))
  have V2 := VAL 2 (by omega) 366 329 333 21 (by omega) (by omega) (by omega)
    (rt2_goodB hG 55 _ (by decide +kernel)) (hv' 2 (by omega) 329 333 (by rw [q4, q5]; rfl))
  have c369 : σ (.n 369) = word 1099511627776 0 :=
    g 59 (.const (.n 369) (word 1099511627776 0)) (by decide +kernel)
  have m370 := good_mul (g 60 (.mul (.n 370) (.n 18) (.n 369)) (by decide +kernel)) (by omega)
    (by omega)
  have w40 : word 1099511627776 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  have c371 : σ (.n 371) = word 2 0 := g 62 (.const (.n 371) (word 2 0)) (by decide +kernel)
  have c372 : σ (.n 372) = word 1 0 := g 64 (.const (.n 372) (word 1 0)) (by decide +kernel)
  have c373 : σ (.n 373) = word 1 0 := g 66 (.const (.n 373) (word 1 0)) (by decide +kernel)
  rw [rtTwo_eq]
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [rtTwoL, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA, challengeT]
  refine ⟨forall_flatten_range fun i hi => (EV i (by omega)).2.2.2, k16, (EV 4 (by omega)).2.2.2,
    (EV 5 (by omega)).2.2.2, m334, c335, m336, a337, m338, m339, a340, m341, m342, a343,
    show σ (.n 63) + σ (.n 343) = 0 by rw [h63, e343, ← hchk, e_add_self], k36, hco, s357,
    fun k hk => s352 k hk, c358, m359, s359, V0, V1, V2, c369, m370,
    show LoadHolds rd (σ (.n 16)) 22 (σ (.n 370)) by rw [m370, c369, w40]; exact hrow',
    c371, show LoadHolds rd (σ (.n 16)) 23 (σ (.n 371)) by rw [c371, tb_word_gen]; exact hpos',
    c372, show LoadHolds rd (σ (.n 16)) 24 (σ (.n 372)) by rw [c372, tb_word_one]; exact hhalf',
    c373, show LoadHolds rd (σ (.n 16)) 25 (σ (.n 373)) by rw [c373, tb_word_one]; exact hpar'⟩

/-- **The radix-four arm, completely** (an even depth): from the sponge `s` the roots wait in,
one step of two levels (no point), its twelve words past the roots, and the slot of `L = 2`. -/
theorem rtc_four (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) {s : Fs} {st : GkrState}
    (hpt : st.point = [])
    (h59 : σ (.n 59) = s.squeeze.1) (h63 : σ (.n 63) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0)
    {D : GkStepD} (hD : D.Ok s st 2) (hx : TbReadsAt rd (σ (.n 5) * gen ^ 2) D.xs)
    (hS' : GkSlot rd (σ (.n 16)) 2 (D.s' s st 2) (σ (.n 5) * gen ^ 2 * gen ^ D.xs.length)
      (D.st' s st 2) (σ (.n 18) * gen ^ 40) gen 1 gen) :
    Stmt.HoldsList C rd σ rtFour True kret := by
  obtain ⟨-, hcap', -, hcur', -, hval', hrow', -, hpt', hpos', hhalf', hpar'⟩ := hS'
  obtain ⟨hl, -, h0, h1, h2, hchk⟩ := hD
  rw [hpt] at hl
  have hcs : D.cs = [] := List.eq_nil_of_length_eq_zero hl
  rw [show (2 : ℕ) ^ 2 = 4 from rfl] at h0 h1 h2
  have hxs : D.xs = D.ch0 ++ (D.ch1 ++ D.ch2) := by simp [GkStepD.xs, hcs]
  have hxl : D.xs.length = 12 := by simp [hxs, h0, h1, h2]
  rw [hxs] at hx
  have hrun : D.run s st = ([], polyEval st.values s.squeeze.1, s.squeeze.2) := by
    rw [GkStepD.run, hcs, hpt]; rfl
  -- the children
  have hk : ∀ i < 12, some (chB 145 i, 5, 2 + i) ∉ vbgS.map loadKey := by decide +kernel
  have ch : ∀ i < 12, LoadHolds rd (σ (.n 5)) (2 + i) ((D.ch0 ++ (D.ch1 ++ D.ch2)).getD i 0) := by
    intro i hi
    have := hx i (by simp [h0, h1, h2]; omega)
    rw [tb_loadHolds_mul_gen_pow] at this
    rwa [← List.getD_eq_getElem _ 0] at this
  have EV : ∀ i < 12, _ := fun i hi => chc_read (C := C)
    (rt4_goodB hG (rtPos i) (chT (.n 5) 2 145 i) (rtFour_check i hi)) (hk i hi) (ch i hi)
  have hp : ∀ i < 12, FsPackOk σ (.n (chB 145 i)) (chB 145 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.2.1
  have cp : ∀ i < 12, σ (.n (chB 145 i + 3)) = σ (.n (chB 145 i)) := fun i hi => (EV i hi).2.1
  have hcw : ∀ m < 3, chWords σ 145 m = [D.ch0, D.ch1, D.ch2].getD m [] := by
    intro m hm
    have hv : ∀ i < 12, σ (.n (chB 145 i)) = (D.ch0 ++ (D.ch1 ++ D.ch2)).getD i 0 :=
      fun i hi => (EV i hi).1
    rw [list4_eq h0, list4_eq h1, list4_eq h2] at hv ⊢
    rw [chWords_eq]
    interval_cases m
    · rw [hv (4 * 0) (by omega), hv (4 * 0 + 1) (by omega), hv (4 * 0 + 2) (by omega),
        hv (4 * 0 + 3) (by omega)]; rfl
    · rw [hv (4 * 1) (by omega), hv (4 * 1 + 1) (by omega), hv (4 * 1 + 2) (by omega),
        hv (4 * 1 + 3) (by omega)]; rfl
    · rw [hv (4 * 2) (by omega), hv (4 * 2 + 1) (by omega), hv (4 * 2 + 2) (by omega),
        hv (4 * 2 + 3) (by omega)]; rfl
  have hc0 : chWords σ 145 0 = D.ch0 := hcw 0 (by omega)
  have hc1 : chWords σ 145 1 = D.ch1 := hcw 1 (by omega)
  have hc2 : chWords σ 145 2 = D.ch2 := hcw 2 (by omega)
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((rtFour.drop n).take 1) = true →
      Good rd vbgS w σ a := fun n a heq => rt4_goodB hG n [.atom a] heq (.atom a) List.mem_cons_self
  -- the permutations of the children
  obtain ⟨k16, -⟩ := keccak_good (g 16 (.keccak (chRate 145 0 ++ lyCap 46) (lyOuts 161) false false)
    (by decide +kernel))
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k16
  rw [hcap, hc0] at B0
  obtain ⟨k33, -⟩ := keccak_good (g 33 (.keccak (chRate 145 1 ++ lyCap 161) (lyOuts 190) false false)
    (by decide +kernel))
  obtain ⟨-, B1⟩ := ch_perm_block (fun i hi => hp (4 * 1 + i) (by omega)) k33
  rw [B0, hc1] at B1
  -- the check
  have m219 := good_mul (g 50 (.mul (.n 219) (.n 206) (.n 210)) (by decide +kernel)) (by omega)
    (by omega)
  have m220 := good_mul (g 51 (.mul (.n 220) (.n 219) (.n 214)) (by decide +kernel)) (by omega)
    (by omega)
  have m221 := good_mul (g 52 (.mul (.n 221) (.n 220) (.n 218)) (by decide +kernel)) (by omega)
    (by omega)
  have c222 : σ (.n 222) = word 0 0 := g 53 (.const (.n 222) (word 0 0)) (by decide +kernel)
  have m223 := good_mul (g 54 (.mul (.n 223) (.n 59) (.n 222)) (by decide +kernel)) (by omega)
    (by omega)
  have a224 : σ (.n 224) = σ (.n 221) + σ (.n 223) :=
    g 55 (.add (.n 224) (.n 221) (.n 223)) (by decide +kernel)
  have m225 := good_mul (g 56 (.mul (.n 225) (.n 177) (.n 181)) (by decide +kernel)) (by omega)
    (by omega)
  have m226 := good_mul (g 57 (.mul (.n 226) (.n 225) (.n 185)) (by decide +kernel)) (by omega)
    (by omega)
  have m227 := good_mul (g 58 (.mul (.n 227) (.n 226) (.n 189)) (by decide +kernel)) (by omega)
    (by omega)
  have m228 := good_mul (g 59 (.mul (.n 228) (.n 59) (.n 224)) (by decide +kernel)) (by omega)
    (by omega)
  have a229 : σ (.n 229) = σ (.n 227) + σ (.n 228) :=
    g 60 (.add (.n 229) (.n 227) (.n 228)) (by decide +kernel)
  have m230 := good_mul (g 61 (.mul (.n 230) (.n 148) (.n 152)) (by decide +kernel)) (by omega)
    (by omega)
  have m231 := good_mul (g 62 (.mul (.n 231) (.n 230) (.n 156)) (by decide +kernel)) (by omega)
    (by omega)
  have m232 := good_mul (g 63 (.mul (.n 232) (.n 231) (.n 160)) (by decide +kernel)) (by omega)
    (by omega)
  have m233 := good_mul (g 64 (.mul (.n 233) (.n 59) (.n 229)) (by decide +kernel)) (by omega)
    (by omega)
  have a234 : σ (.n 234) = σ (.n 232) + σ (.n 233) :=
    g 65 (.add (.n 234) (.n 232) (.n 233)) (by decide +kernel)
  have e234 : σ (.n 234) = polyEval [prodE (chWords σ 145 0), prodE (chWords σ 145 1),
      prodE (chWords σ 145 2)] (σ (.n 59)) := by
    rw [a234, m233, a229, m228, a224, m223, c222, tb_word_zero, m221, m220, m219, m227, m226, m225,
      m232, m231, m230,
      show σ (.n 148) = σ (.n 145) from cp 0 (by omega),
      show σ (.n 152) = σ (.n 149) from cp 1 (by omega),
      show σ (.n 156) = σ (.n 153) from cp 2 (by omega),
      show σ (.n 160) = σ (.n 157) from cp 3 (by omega),
      show σ (.n 177) = σ (.n 174) from cp 4 (by omega),
      show σ (.n 181) = σ (.n 178) from cp 5 (by omega),
      show σ (.n 185) = σ (.n 182) from cp 6 (by omega),
      show σ (.n 189) = σ (.n 186) from cp 7 (by omega),
      show σ (.n 206) = σ (.n 203) from cp 8 (by omega),
      show σ (.n 210) = σ (.n 207) from cp 9 (by omega),
      show σ (.n 214) = σ (.n 211) from cp 10 (by omega),
      show σ (.n 218) = σ (.n 215) from cp 11 (by omega)]
    have hc0 : chWords σ 145 0 = [σ (.n 145), σ (.n 149), σ (.n 153), σ (.n 157)] := by
      rw [chWords_eq]; rfl
    have hc1 : chWords σ 145 1 = [σ (.n 174), σ (.n 178), σ (.n 182), σ (.n 186)] := by
      rw [chWords_eq]; rfl
    have hc2 : chWords σ 145 2 = [σ (.n 203), σ (.n 207), σ (.n 211), σ (.n 215)] := by
      rw [chWords_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  rw [hrun] at hchk
  -- the third block's permutation and the two coordinates
  obtain ⟨k67, -⟩ := keccak_good (g 67 (.keccak (chRate 145 2 ++ lyCap 190) (lyOuts 235) false false)
    (by decide +kernel))
  obtain ⟨P2, B2⟩ := ch_perm_block (fun i hi => hp (4 * 2 + i) (by omega)) k67
  rw [B1, hc2] at P2 B2
  set P1 := Fs.perm ⟨capOf (Fs.perm ⟨capOf s.perm, D.ch0.map (·, dsObserve)⟩),
    D.ch1.map (·, dsObserve)⟩ with hP1
  set Q := Fs.perm ⟨capOf P1, D.ch2.map (·, dsObserve)⟩ with hQ
  have hco2 := challengeT_good (rt4_goodB hG 68 (challengeT (.n 235) 248) (by decide +kernel))
  have e248 : σ (.n 248) = challengeOf Q := challengeT_value hco2 (P2 0 (by omega))
  have hz : (([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++ lyCap 235 :
      List V).map σ) = rateOf [] ++ capOf Q := by
    rw [ly_zero_rate z42 z43 z44 z45, B2]
  obtain ⟨k69, P3, B3⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := w)
    (g 69 (.keccak ([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++ lyCap 235)
      (lyOuts 249) false false) (by decide +kernel))
  rw [hz] at P3 B3
  have hco3 := challengeT_good (rt4_goodB hG 70 (challengeT (.n 249) 262) (by decide +kernel))
  have e262 : σ (.n 262) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value hco3 (P3 0 (by omega))
  -- the sponge after the children
  have hsb : D.sb s st = ⟨capOf P1, D.ch2.map (·, dsObserve)⟩ := by
    show (((D.run s st).2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
      dsObserve = _
    rw [hrun, show s.squeeze.2 = ⟨capOf s.perm, []⟩ from rfl,
      absorbAll_short ⟨capOf s.perm, []⟩ D.ch0 dsObserve (by simp [h0]), List.nil_append,
      tb_absorbAll_full ⟨capOf s.perm, D.ch0.map (·, dsObserve)⟩ (by simp [h0]) D.ch1 h1,
      tb_absorbAll_full _ (by simp [h1]) D.ch2 h2]
  have hys : D.ys s st 2 = [σ (.n 248), σ (.n 262)] := by
    rw [e248, e262]; show ((D.sb s st).squeezeN 2).1 = _; rw [hsb, tb_squeezeN_two]
  have hs' : D.s' s st 2 = ⟨(List.range 5).map fun k ↦ σ (.n (257 + k)), []⟩ := by
    have e : ((List.range 5).map fun k ↦ σ (.n (257 + k))) = capOf (permOf (rateOf [] ++
        capOf Q)) := by rw [← B3]; simp [lyCap]
    rw [e]; show ((D.sb s st).squeezeN 2).2 = _; rw [hsb, tb_squeezeN_two]
  -- the slot of `L = 2`
  have hpt2 : (D.st' s st 2).point = [σ (.n 248), σ (.n 262)] := by
    show D.ys s st 2 ++ (D.run s st).1 = _
    rw [hys, hrun]; rfl
  have s40 : LoadHolds rd (σ (.n 18)) 40 (σ (.n 248)) := by
    have := hpt' 0 (by rw [hpt2]; simp)
    simp only [hpt2, List.getElem_cons_zero] at this
    rwa [tb_loadHolds_mul_gen_pow] at this
  have s41 : LoadHolds rd (σ (.n 18)) 41 (σ (.n 262)) := by
    have := hpt' 1 (by rw [hpt2]; simp)
    simp only [hpt2, List.getElem_cons_succ, List.getElem_cons_zero] at this
    rwa [tb_loadHolds_mul_gen_pow] at this
  have s257 : ∀ k < 5, LoadHolds rd (σ (.n 16)) (26 + k) (σ (.n (257 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simpa [List.getD_eq_getElem?_getD, hk, show 13 * 2 + k = 26 + k by omega] using this
  have c263 : σ (.n 263) = word 16384 0 := g 78 (.const (.n 263) (word 16384 0)) (by decide +kernel)
  have m264 := good_mul (g 79 (.mul (.n 264) (.n 5) (.n 263)) (by decide +kernel)) (by omega)
    (by omega)
  have w14 : word 16384 0 = gen ^ 14 := by
    rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, tb_word_two_pow (by norm_num)]
  have s264 : LoadHolds rd (σ (.n 16)) 31 (σ (.n 264)) := by
    rw [m264, c263, w14, show (14 : ℕ) = 2 + 12 by rfl, pow_add, ← mul_assoc, ← hxl]
    exact hcur'
  have sv : ∀ t < 3, LoadHolds rd (σ (.n 16)) (32 + t)
      (multilinearEval (chWords σ 145 t) [σ (.n 248), σ (.n 262)]) := by
    intro t ht
    have h := hval' t ht
    rw [show 13 * 2 + 6 + t = 32 + t by ring] at h
    have hv : (D.st' s st 2).values.getD t 0 =
        multilinearEval (chWords σ 145 t) [σ (.n 248), σ (.n 262)] := by
      show ([D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st 2))).getD t 0 = _
      rw [hys, hcw t ht]
      interval_cases t <;> rfl
    rwa [hv] at h
  have V0 := chc_val (C := C) (rt4_goodB hG 81 (chValT 145 248 262 16 0 265 32) (by decide +kernel)) (by omega) (by omega)
    (fun i hi => cp (4 * 0 + i) (by omega)) (sv 0 (by omega))
  have V1 := chc_val (C := C) (rt4_goodB hG 91 (chValT 145 248 262 16 1 274 33) (by decide +kernel)) (by omega) (by omega)
    (fun i hi => cp (4 * 1 + i) (by omega)) (sv 1 (by omega))
  have V2 := chc_val (C := C) (rt4_goodB hG 101 (chValT 145 248 262 16 2 283 34) (by decide +kernel)) (by omega) (by omega)
    (fun i hi => cp (4 * 2 + i) (by omega)) (sv 2 (by omega))
  have c292 : σ (.n 292) = word 1099511627776 0 :=
    g 111 (.const (.n 292) (word 1099511627776 0)) (by decide +kernel)
  have m293 := good_mul (g 112 (.mul (.n 293) (.n 18) (.n 292)) (by decide +kernel)) (by omega)
    (by omega)
  have w40 : word 1099511627776 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  have c294 : σ (.n 294) = word 2 0 := g 114 (.const (.n 294) (word 2 0)) (by decide +kernel)
  have c295 : σ (.n 295) = word 1 0 := g 116 (.const (.n 295) (word 1 0)) (by decide +kernel)
  have c296 : σ (.n 296) = word 2 0 := g 118 (.const (.n 296) (word 2 0)) (by decide +kernel)
  rw [rtFour_eq]
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [rtFourL, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA, challengeT]
  refine ⟨forall_flatten_range fun i hi => (EV i (by omega)).2.2.2, k16,
    forall_flatten_range fun i hi => (EV (4 + i) (by omega)).2.2.2, k33,
    forall_flatten_range fun i hi => (EV (8 + i) (by omega)).2.2.2,
    m219, m220, m221, c222, m223, a224, m225, m226, m227, m228, a229, m230, m231, m232, m233,
    a234, show σ (.n 63) + σ (.n 234) = 0 by
      rw [h63, e234, h59, hc0, hc1, hc2, ← hchk, e_add_self],
    k67, hco2, k69, hco3, s40, s41, fun k hk => s257 k hk, c263, m264, s264, V0, V1, V2,
    c292, m293,
    show LoadHolds rd (σ (.n 16)) 35 (σ (.n 293)) by rw [m293, c292, w40]; exact hrow',
    c294, show LoadHolds rd (σ (.n 16)) 36 (σ (.n 294)) by rw [c294, tb_word_gen]; exact hpos',
    c295, show LoadHolds rd (σ (.n 16)) 37 (σ (.n 295)) by rw [c295, tb_word_one]; exact hhalf',
    c296, show LoadHolds rd (σ (.n 16)) 38 (σ (.n 296)) by rw [c296, tb_word_gen]; exact hpar'⟩

end Arms

end
end LeanVM.Guest.B1.Tables
