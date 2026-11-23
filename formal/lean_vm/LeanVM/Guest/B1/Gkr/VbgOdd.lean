/-
  LeanVM.Guest.B1.Gkr.VbgOdd

  `verify_bus_gkr`'s evaluation list, and its root-most layer, completely: from the roots, one
  step of one level (an odd depth) or two (an even one), its words at the cursor and the slot it
  leads to, the layer's arm holds on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Gkr.EvalC
public import LeanVM.Guest.B1.Gkr.SpecInv
public import LeanVM.Guest.B1.Gkr.Root
public import LeanVM.Guest.B1.Gkr.LayerTail
public import LeanVM.Guest.B1.Sumcheck.Gkr
public import LeanVM.Guest.B1.Gkr.Holds

/-!
# The root-most layer, completely

`vbgEvL`: `verify_bus_gkr`'s body as the forward evaluator walks it (its `ite`'s arms in order,
the checked inverse as its product, `fixNe`); `vb_good`, `rt_goodB`: the statements of the body
and of the root-most layer's arms satisfy their equations.

* `chc_read`, `chc_val`: a child's read and a tree's new value at two coordinates, on their
  equations (shared with `verify_bus_gkr_loop0`'s templates `chT`, `chValT`);
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
theorem forall_flatten_range {P : Stmt → Prop} {n : ℕ} {g : ℕ → List Stmt}
    (h : ∀ i < n, ∀ s ∈ g i, P s) : ∀ s ∈ ((List.range n).map g).flatten, P s := by
  intro s hs
  obtain ⟨l, hl, hs⟩ := List.mem_flatten.mp hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  exact h i (List.mem_range.mp hi) s hs

theorem tb_isInK_one : IsInK (1 : E) := by simpa using tb_gen_pow_isInK 0

theorem tb_squeezeN_two (s : Fs) : s.squeezeN 2 =
    ([challengeOf s.perm, challengeOf (permOf (rateOf [] ++ capOf s.perm))],
      ⟨capOf (permOf (rateOf [] ++ capOf s.perm)), []⟩) := rfl

noncomputable def vbgEvL : List Stmt := (flatIte vbgPre).map fixNe

theorem vb_chk : (chk 10 vbgEvL).isSome = true := by decide +kernel

/-- `verify_bus_gkr`'s stores. -/
noncomputable def vbgS : List Atom := storesOf 10 vbgEvL

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

/-- A tree's new value at one coordinate `y = σ 351` (`lo + y·(lo + hi)`), stored at the slot's
`off`. -/
def rtVal (b u v off : ℕ) : List Stmt :=
  [.atom (.add (.n b) (.n u) (.n v)), .atom (.mul (.n (b + 1)) (.n 335) (.n b)),
    .atom (.add (.n (b + 2)) (.n u) (.n (b + 1))), .atom (.load (.n (b + 2)) (.n 139) off)]

/-- The binary arm. -/
def rtTwoL : List Stmt :=
  ((List.range 4).map (chT (.n 5) 2 288)).flatten ++
  [keccakA (chRate 288 0 ++ lyCap 46) (lyOuts 304)] ++
  chT (.n 5) 2 288 4 ++ chT (.n 5) 2 288 5 ++
  [.atom (.mul (.n 325) (.n 320) (.n 324)), .atom (.const (.n 326) (word 0 0)),
    .atom (.mul (.n 327) (.n 46) (.n 326)), .atom (.add (.n 328) (.n 325) (.n 327)),
    .atom (.mul (.n 329) (.n 299) (.n 303)), .atom (.mul (.n 330) (.n 46) (.n 328)),
    .atom (.add (.n 331) (.n 329) (.n 330)), .atom (.mul (.n 332) (.n 291) (.n 295)),
    .atom (.mul (.n 333) (.n 46) (.n 331)), .atom (.add (.n 334) (.n 332) (.n 333)),
    .atom (.assertEq (.n 62) (.n 334)),
    keccakA ([.n 318, .n 319, .n 322, .n 323, .n 42, .n 43, .n 44, .n 45] ++ lyCap 304)
      (lyOuts 335)] ++
  [.atom (.load (.n 335) (.n 18) 40), .atom (.const (.n 348) (word 0 0)),
    .atom (.load (.n 348) (.n 18) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (343 + k)) (.n 139) k)) ++
  [.atom (.const (.n 349) (word 256 0)), .atom (.mul (.n 350) (.n 5) (.n 349)),
    .atom (.load (.n 350) (.n 139) 5)] ++
  rtVal 351 291 295 6 ++ rtVal 354 299 303 7 ++ rtVal 357 320 324 8 ++
  [.atom (.const (.n 360) (word 2 0)), .atom (.load (.n 360) (.n 139) 9)]

set_option maxRecDepth 10000 in
theorem rtTwoL_eq : rtTwo = rtTwoL := tbStmtsEqb_sound (by decide +kernel)

/-- The radix-four arm. -/
def rtFourL : List Stmt :=
  ((List.range 4).map (chT (.n 5) 2 142)).flatten ++
  [keccakA (chRate 142 0 ++ lyCap 46) (lyOuts 158)] ++
  ((List.range 4).map fun i ↦ chT (.n 5) 2 142 (4 + i)).flatten ++
  [keccakA (chRate 142 1 ++ lyCap 158) (lyOuts 187)] ++
  ((List.range 4).map fun i ↦ chT (.n 5) 2 142 (8 + i)).flatten ++
  [.atom (.mul (.n 216) (.n 203) (.n 207)), .atom (.mul (.n 217) (.n 216) (.n 211)),
    .atom (.mul (.n 218) (.n 217) (.n 215)), .atom (.const (.n 219) (word 0 0)),
    .atom (.mul (.n 220) (.n 46) (.n 219)), .atom (.add (.n 221) (.n 218) (.n 220)),
    .atom (.mul (.n 222) (.n 174) (.n 178)), .atom (.mul (.n 223) (.n 222) (.n 182)),
    .atom (.mul (.n 224) (.n 223) (.n 186)), .atom (.mul (.n 225) (.n 46) (.n 221)),
    .atom (.add (.n 226) (.n 224) (.n 225)), .atom (.mul (.n 227) (.n 145) (.n 149)),
    .atom (.mul (.n 228) (.n 227) (.n 153)), .atom (.mul (.n 229) (.n 228) (.n 157)),
    .atom (.mul (.n 230) (.n 46) (.n 226)), .atom (.add (.n 231) (.n 229) (.n 230)),
    .atom (.assertEq (.n 62) (.n 231)),
    keccakA (chRate 142 2 ++ lyCap 187) (lyOuts 232)] ++
  [keccakA ([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++ lyCap 232) (lyOuts 245)] ++
  [.atom (.load (.n 232) (.n 18) 40), .atom (.load (.n 245) (.n 18) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (253 + k)) (.n 139) k)) ++
  [.atom (.const (.n 258) (word 16384 0)), .atom (.mul (.n 259) (.n 5) (.n 258)),
    .atom (.load (.n 259) (.n 139) 5)] ++
  chValT 142 232 245 139 0 260 6 ++ chValT 142 232 245 139 1 269 7 ++
  chValT 142 232 245 139 2 278 8 ++
  [.atom (.const (.n 287) (word 2 0)), .atom (.load (.n 287) (.n 139) 9)]

set_option maxRecDepth 10000 in
theorem rtFourL_eq : rtFour = rtFourL := tbStmtsEqb_sound (by decide +kernel)

section Eval

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {kret : List E → Prop}

/-- A permutation's thirteen outputs from `b`, and its capacity cells, on its equations. -/
theorem lyc_keccak {ins : List V} {b : ℕ}
    (hg : Good rd S w σ (.keccak ins (lyOuts b) false false)) :
    (Atom.keccak ins (lyOuts b) false false).Holds rd σ ∧
      (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨hk, -⟩ := keccak_good hg
  obtain ⟨hP, hc⟩ := ly_keccak hk
  exact ⟨hk, hP, hc⟩

/-- A statement of the body satisfies its equations. -/
theorem vb_good (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vbgPre.drop n).take 1) = true)
    (hfix : fixNe (.atom a) = .atom a) : Good rd vbgS w σ a := by
  have h := good_slice (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) n [.atom a] heq rfl _ List.mem_cons_self
  rw [hfix] at h
  exact h

/-- A block of the binary arm satisfies its equations. -/
theorem rt2_goodB (hA : ∀ t ∈ rtFour ++ rtTwo, GoodS rd S w σ t) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((rtTwo.drop n).take blk.length) = true) :
    ∀ s ∈ blk, GoodS rd S w σ s :=
  fun s hs => hA s (List.mem_append_right _ (tb_mem_of_slice heq s hs))

/-- A block of the radix-four arm satisfies its equations. -/
theorem rt4_goodB (hA : ∀ t ∈ rtFour ++ rtTwo, GoodS rd S w σ t) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((rtFour.drop n).take blk.length) = true) :
    ∀ s ∈ blk, GoodS rd S w σ s :=
  fun s hs => hA s (List.mem_append_left _ (tb_mem_of_slice heq s hs))

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

section Arms

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val} {kret : List E → Prop}

/-- **The binary arm, completely** (an odd depth): from the sponge `s` the roots wait in, one
step of one level (no point), its six words past the roots, and the slot of `L = 1`. -/
theorem rtc_two {S : List Atom} (hA : ∀ t ∈ rtFour ++ rtTwo, GoodS rd S w σ t)
    (hk : ∀ i < 6, some (chB 288 i, 5, 2 + i) ∉ S.map loadKey) {s : Fs} {st : GkrState}
    (hpt : st.point = [])
    (h59 : σ (.n 46) = s.squeeze.1) (h63 : σ (.n 62) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0)
    {D : GkStepD} (hD : D.Ok s st 1) (hx : TbReadsAt rd (σ (.n 5) * gen ^ 2) D.xs)
    (h140 : σ (.n 139) = σ (.n 16) * gen ^ 10) (hz : LoadHolds rd (σ (.n 18)) 41 0)
    (hS' : GkSlot rd (σ (.n 16)) 1 (D.s' s st 1) (σ (.n 5) * gen ^ 2 * gen ^ D.xs.length)
      (D.st' s st 1) (σ (.n 18) * gen ^ 40) gen) :
    Stmt.HoldsList C rd σ rtTwo True kret := by
  obtain ⟨-, hcap', -, hcur', -, hval', -, hpt', hpos'⟩ := hS'
  have ld : ∀ k v, LoadHolds rd (σ (.n 16)) (10 * 1 + k) v → LoadHolds rd (σ (.n 139)) k v :=
    fun k v h => by rw [h140, tb_loadHolds_mul_gen_pow]; exact h
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
  have ch : ∀ i < 6, LoadHolds rd (σ (.n 5)) (2 + i) ([w0, w1, w2, w3, w4, w5].getD i 0) := by
    intro i hi
    have := hx i (by simp; omega)
    rw [tb_loadHolds_mul_gen_pow] at this
    rwa [← List.getD_eq_getElem _ 0] at this
  have EV : ∀ i < 6, _ := fun i hi => chc_read (C := C)
    (rt2_goodB hA (rtPos i) (chT (.n 5) 2 288 i) (rtTwo_check i hi)) (hk i hi) (ch i hi)
  have ev : ∀ i < 6, ∀ v, [w0, w1, w2, w3, w4, w5].getD i 0 = v → σ (.n (chB 288 i)) = v :=
    fun i hi v hv => (EV i hi).1.trans hv
  have q : ∀ i < 6, ∀ v, [w0, w1, w2, w3, w4, w5].getD i 0 = v → σ (.n (chB 288 i + 3)) = v :=
    fun i hi v hv => (EV i hi).2.1.trans ((EV i hi).1.trans hv)
  have hp : ∀ i < 6, FsPackOk σ (.n (chB 288 i)) (chB 288 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.2.1
  have q0 : σ (.n 291) = w0 := q 0 (by omega) w0 rfl
  have q1 : σ (.n 295) = w1 := q 1 (by omega) w1 rfl
  have q2 : σ (.n 299) = w2 := q 2 (by omega) w2 rfl
  have q3 : σ (.n 303) = w3 := q 3 (by omega) w3 rfl
  have q4 : σ (.n 320) = w4 := q 4 (by omega) w4 rfl
  have q5 : σ (.n 324) = w5 := q 5 (by omega) w5 rfl
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((rtTwo.drop n).take 1) = true →
      Good rd S w σ a := fun n a heq => rt2_goodB hA n [.atom a] heq (.atom a) List.mem_cons_self
  -- the first four children's permutation
  obtain ⟨k16, -⟩ := keccak_good (g 16 (.keccak (chRate 288 0 ++ lyCap 46) (lyOuts 304) false false)
    (by decide +kernel))
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k16
  rw [hcap] at B0
  have hw0 : chWords σ 288 0 = [w0, w1, w2, w3] := by
    rw [chWords_eq]
    simp only [show 4 * 0 = 0 from rfl, Nat.zero_add]
    rw [ev 0 (by omega) w0 rfl, ev 1 (by omega) w1 rfl, ev 2 (by omega) w2 rfl,
      ev 3 (by omega) w3 rfl]
  rw [hw0] at B0
  -- the check
  have m328 := good_mul (g 25 (.mul (.n 325) (.n 320) (.n 324)) (by decide +kernel)) (by omega)
    (by omega)
  have c329 : σ (.n 326) = word 0 0 := g 26 (.const (.n 326) (word 0 0)) (by decide +kernel)
  have m330 := good_mul (g 27 (.mul (.n 327) (.n 46) (.n 326)) (by decide +kernel)) (by omega)
    (by omega)
  have a331 : σ (.n 328) = σ (.n 325) + σ (.n 327) :=
    g 28 (.add (.n 328) (.n 325) (.n 327)) (by decide +kernel)
  have m332 := good_mul (g 29 (.mul (.n 329) (.n 299) (.n 303)) (by decide +kernel)) (by omega)
    (by omega)
  have m333 := good_mul (g 30 (.mul (.n 330) (.n 46) (.n 328)) (by decide +kernel)) (by omega)
    (by omega)
  have a334 : σ (.n 331) = σ (.n 329) + σ (.n 330) :=
    g 31 (.add (.n 331) (.n 329) (.n 330)) (by decide +kernel)
  have m335 := good_mul (g 32 (.mul (.n 332) (.n 291) (.n 295)) (by decide +kernel)) (by omega)
    (by omega)
  have m336 := good_mul (g 33 (.mul (.n 333) (.n 46) (.n 331)) (by decide +kernel)) (by omega)
    (by omega)
  have a337 : σ (.n 334) = σ (.n 332) + σ (.n 333) :=
    g 34 (.add (.n 334) (.n 332) (.n 333)) (by decide +kernel)
  have e337 : σ (.n 334) = polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]]
      s.squeeze.1 := by
    rw [a337, m336, a334, m333, a331, m330, c329, tb_word_zero, m328, m332, m335, q0, q1, q2, q3,
      q4, q5, h59]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  have hrun : (GkStepD.run ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st).2.1 =
      polyEval st.values s.squeeze.1 := by
    rw [GkStepD.run, hpt]; rfl
  rw [hrun] at hchk
  -- the new coordinate
  obtain ⟨e321, e322⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 4 (by omega)))
  obtain ⟨e325, e326⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 5 (by omega)))
  norm_num [chB] at e321 e322 e325 e326
  rw [show σ (.n 317) = w4 from ev 4 (by omega) w4 rfl] at e321 e322
  rw [show σ (.n 321) = w5 from ev 5 (by omega) w5 rfl] at e325 e326
  set P2 := Fs.perm ⟨capOf s.perm, [w0, w1, w2, w3].map (·, dsObserve)⟩ with hP2
  have hr2 : (([.n 318, .n 319, .n 322, .n 323, .n 42, .n 43, .n 44, .n 45] ++ lyCap 304 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ capOf P2 := by
    rw [List.map_append, B0, rateOf_eq_cells _ (by simp)]
    simp [pendCells, e321, e322, e325, e326, z42, z43, z44, z45]
  obtain ⟨k36, hP3, hC3⟩ := lyc_keccak (rd := rd) (σ := σ) (S := S) (w := w)
    (g 36 (.keccak ([.n 318, .n 319, .n 322, .n 323, .n 42, .n 43, .n 44, .n 45] ++
      lyCap 304) (lyOuts 335) false false) (by decide +kernel))
  rw [hr2] at hP3 hC3
  have e351 : σ (.n 335) = challengeOf (permOf (rateOf [(w4, dsObserve), (w5, dsObserve)] ++
      capOf P2)) := challengeT_value (s0 := .n 335) (b := 335) rfl (hP3 0 (by omega))
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
  have hy : GkStepD.ys ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = [σ (.n 335)] := by
    rw [e351]; show ((GkStepD.sb _ s st).squeezeN 1).1 = _; rw [hsb]; rfl
  have hs' : GkStepD.s' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = ⟨(lyCap 335).map σ, []⟩ := by
    rw [hC3]; show ((GkStepD.sb _ s st).squeezeN 1).2 = _; rw [hsb]; rfl
  -- the slot of `L = 1`
  have hpt1 : (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).point = [σ (.n 335)] := by
    show GkStepD.ys _ s st 1 ++ (GkStepD.run _ s st).1 = _
    rw [hy, GkStepD.run, hpt]; rfl
  have hval1 : ∀ t < 3, (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).values.getD t 0 =
      multilinearEval ([[w0, w1], [w2, w3], [w4, w5]].getD t []) [σ (.n 335)] := by
    intro t ht
    show ([[w0, w1], [w2, w3], [w4, w5]].map (multilinearEval · (GkStepD.ys _ s st 1))).getD t 0 = _
    rw [hy]
    interval_cases t <;> rfl
  have s351 : LoadHolds rd (σ (.n 18)) 40 (σ (.n 335)) := by
    have := hpt' 0 (by rw [hpt1]; simp)
    simp only [hpt1, List.getElem_cons_zero] at this
    rw [tb_loadHolds_mul_gen_pow] at this
    exact this
  have s346 : ∀ k < 5, LoadHolds rd (σ (.n 139)) k (σ (.n (343 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    exact ld k _ (by simpa [lyCap, List.getD_eq_getElem?_getD, hk,
      show 335 + 8 + k = 343 + k by omega] using this)
  have c352 : σ (.n 348) = word 0 0 := g 38 (.const (.n 348) (word 0 0)) (by decide +kernel)
  have c353 : σ (.n 349) = word 256 0 := g 45 (.const (.n 349) (word 256 0)) (by decide +kernel)
  have m354 := good_mul (g 46 (.mul (.n 350) (.n 5) (.n 349)) (by decide +kernel)) (by omega)
    (by omega)
  have w8 : word 256 0 = gen ^ 8 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)]
  have s354 : LoadHolds rd (σ (.n 139)) 5 (σ (.n 350)) := by
    rw [m354, c353, w8, show (8 : ℕ) = 2 + 6 by rfl, pow_add, ← mul_assoc]
    exact ld 5 _ hcur'
  have VAL : ∀ t < 3, ∀ (b u v off : ℕ), u < b → v < b → 335 < b →
      (∀ s ∈ rtVal b u v off, GoodS rd S w σ s) →
      LoadHolds rd (σ (.n 139)) off (σ (.n u) + σ (.n 335) * (σ (.n u) + σ (.n v))) →
      ∀ s ∈ rtVal b u v off, SHolds C rd σ s := by
    intro t _ b u v off hu hv h3 gb hl
    have a0 : σ (.n b) = σ (.n u) + σ (.n v) := gb (.atom (.add (.n b) _ _)) (by simp [rtVal])
    have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 335) (.n b))) (by simp [rtVal]))
      (by omega) (by omega)
    have a2 : σ (.n (b + 2)) = σ (.n u) + σ (.n (b + 1)) :=
      gb (.atom (.add (.n (b + 2)) _ _)) (by simp [rtVal])
    simp only [rtVal, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    exact ⟨a0, m1, a2, show LoadHolds rd (σ (.n 139)) off (σ (.n (b + 2))) by
      rw [a2, m1, a0]; exact hl⟩
  have hv' : ∀ t < 3, ∀ u v, [[w0, w1], [w2, w3], [w4, w5]].getD t [] = [σ (.n u), σ (.n v)] →
      LoadHolds rd (σ (.n 139)) (6 + t) (σ (.n u) + σ (.n 335) * (σ (.n u) + σ (.n v))) := by
    intro t ht u v huv
    have h := hval' t ht
    rw [hval1 t ht, huv, show 10 * 1 + 6 + t = 10 * 1 + (6 + t) by ring] at h
    have h' := ld _ _ h
    convert h' using 1
    simp [multilinearEval, foldPairs]
    ring
  have V0 := VAL 0 (by omega) 351 291 295 6 (by omega) (by omega) (by omega)
    (rt2_goodB hA 48 _ (by decide +kernel)) (hv' 0 (by omega) 291 295 (by rw [q0, q1]; rfl))
  have V1 := VAL 1 (by omega) 354 299 303 7 (by omega) (by omega) (by omega)
    (rt2_goodB hA 52 _ (by decide +kernel)) (hv' 1 (by omega) 299 303 (by rw [q2, q3]; rfl))
  have V2 := VAL 2 (by omega) 357 320 324 8 (by omega) (by omega) (by omega)
    (rt2_goodB hA 56 _ (by decide +kernel)) (hv' 2 (by omega) 320 324 (by rw [q4, q5]; rfl))
  have c364 : σ (.n 360) = word 2 0 := g 60 (.const (.n 360) (word 2 0)) (by decide +kernel)
  rw [rtTwoL_eq]
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [rtTwoL, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA]
  refine ⟨forall_flatten_range fun i hi => (EV i (by omega)).2.2.2, k16, (EV 4 (by omega)).2.2.2,
    (EV 5 (by omega)).2.2.2, m328, c329, m330, a331, m332, m333, a334, m335, m336, a337,
    show σ (.n 62) + σ (.n 334) = 0 by rw [h63, e337, ← hchk, e_add_self], k36, s351,
    c352, show LoadHolds rd (σ (.n 18)) 41 (σ (.n 348)) by rw [c352, tb_word_zero]; exact hz,
    fun k hk => s346 k hk, c353, m354, s354, V0, V1, V2,
    c364, show LoadHolds rd (σ (.n 139)) 9 (σ (.n 360)) by
      rw [c364, tb_word_gen]; exact ld 9 _ hpos'⟩

/-- **The radix-four arm, completely** (an even depth): from the sponge `s` the roots wait in,
one step of two levels (no point), its twelve words past the roots, and the slot of `L = 2`. -/
theorem rtc_four {S : List Atom} (hA : ∀ t ∈ rtFour ++ rtTwo, GoodS rd S w σ t)
    (hk : ∀ i < 12, some (chB 142 i, 5, 2 + i) ∉ S.map loadKey) {s : Fs} {st : GkrState}
    (hpt : st.point = [])
    (h59 : σ (.n 46) = s.squeeze.1) (h63 : σ (.n 62) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0)
    {D : GkStepD} (hD : D.Ok s st 2) (hx : TbReadsAt rd (σ (.n 5) * gen ^ 2) D.xs)
    (h140 : σ (.n 139) = σ (.n 16) * gen ^ 20)
    (hS' : GkSlot rd (σ (.n 16)) 2 (D.s' s st 2) (σ (.n 5) * gen ^ 2 * gen ^ D.xs.length)
      (D.st' s st 2) (σ (.n 18) * gen ^ 40) gen) :
    Stmt.HoldsList C rd σ rtFour True kret := by
  obtain ⟨-, hcap', -, hcur', -, hval', -, hpt', hpos'⟩ := hS'
  have ld : ∀ k v, LoadHolds rd (σ (.n 16)) (10 * 2 + k) v → LoadHolds rd (σ (.n 139)) k v :=
    fun k v h => by rw [h140, tb_loadHolds_mul_gen_pow]; exact h
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
  have ch : ∀ i < 12, LoadHolds rd (σ (.n 5)) (2 + i) ((D.ch0 ++ (D.ch1 ++ D.ch2)).getD i 0) := by
    intro i hi
    have := hx i (by simp [h0, h1, h2]; omega)
    rw [tb_loadHolds_mul_gen_pow] at this
    rwa [← List.getD_eq_getElem _ 0] at this
  have EV : ∀ i < 12, _ := fun i hi => chc_read (C := C)
    (rt4_goodB hA (rtPos i) (chT (.n 5) 2 142 i) (rtFour_check i hi)) (hk i hi) (ch i hi)
  have hp : ∀ i < 12, FsPackOk σ (.n (chB 142 i)) (chB 142 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.2.1
  have cp : ∀ i < 12, σ (.n (chB 142 i + 3)) = σ (.n (chB 142 i)) := fun i hi => (EV i hi).2.1
  have hcw : ∀ m < 3, chWords σ 142 m = [D.ch0, D.ch1, D.ch2].getD m [] := by
    intro m hm
    have hv : ∀ i < 12, σ (.n (chB 142 i)) = (D.ch0 ++ (D.ch1 ++ D.ch2)).getD i 0 :=
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
  have hc0 : chWords σ 142 0 = D.ch0 := hcw 0 (by omega)
  have hc1 : chWords σ 142 1 = D.ch1 := hcw 1 (by omega)
  have hc2 : chWords σ 142 2 = D.ch2 := hcw 2 (by omega)
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((rtFour.drop n).take 1) = true →
      Good rd S w σ a := fun n a heq => rt4_goodB hA n [.atom a] heq (.atom a) List.mem_cons_self
  -- the permutations of the children
  obtain ⟨k16, -⟩ := keccak_good (g 16 (.keccak (chRate 142 0 ++ lyCap 46) (lyOuts 158) false false)
    (by decide +kernel))
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k16
  rw [hcap, hc0] at B0
  obtain ⟨k33, -⟩ := keccak_good (g 33 (.keccak (chRate 142 1 ++ lyCap 158) (lyOuts 187) false false)
    (by decide +kernel))
  obtain ⟨-, B1⟩ := ch_perm_block (fun i hi => hp (4 * 1 + i) (by omega)) k33
  rw [B0, hc1] at B1
  -- the check
  have m217 := good_mul (g 50 (.mul (.n 216) (.n 203) (.n 207)) (by decide +kernel)) (by omega)
    (by omega)
  have m218 := good_mul (g 51 (.mul (.n 217) (.n 216) (.n 211)) (by decide +kernel)) (by omega)
    (by omega)
  have m219 := good_mul (g 52 (.mul (.n 218) (.n 217) (.n 215)) (by decide +kernel)) (by omega)
    (by omega)
  have c220 : σ (.n 219) = word 0 0 := g 53 (.const (.n 219) (word 0 0)) (by decide +kernel)
  have m221 := good_mul (g 54 (.mul (.n 220) (.n 46) (.n 219)) (by decide +kernel)) (by omega)
    (by omega)
  have a222 : σ (.n 221) = σ (.n 218) + σ (.n 220) :=
    g 55 (.add (.n 221) (.n 218) (.n 220)) (by decide +kernel)
  have m223 := good_mul (g 56 (.mul (.n 222) (.n 174) (.n 178)) (by decide +kernel)) (by omega)
    (by omega)
  have m224 := good_mul (g 57 (.mul (.n 223) (.n 222) (.n 182)) (by decide +kernel)) (by omega)
    (by omega)
  have m225 := good_mul (g 58 (.mul (.n 224) (.n 223) (.n 186)) (by decide +kernel)) (by omega)
    (by omega)
  have m226 := good_mul (g 59 (.mul (.n 225) (.n 46) (.n 221)) (by decide +kernel)) (by omega)
    (by omega)
  have a227 : σ (.n 226) = σ (.n 224) + σ (.n 225) :=
    g 60 (.add (.n 226) (.n 224) (.n 225)) (by decide +kernel)
  have m228 := good_mul (g 61 (.mul (.n 227) (.n 145) (.n 149)) (by decide +kernel)) (by omega)
    (by omega)
  have m229 := good_mul (g 62 (.mul (.n 228) (.n 227) (.n 153)) (by decide +kernel)) (by omega)
    (by omega)
  have m230 := good_mul (g 63 (.mul (.n 229) (.n 228) (.n 157)) (by decide +kernel)) (by omega)
    (by omega)
  have m231 := good_mul (g 64 (.mul (.n 230) (.n 46) (.n 226)) (by decide +kernel)) (by omega)
    (by omega)
  have a232 : σ (.n 231) = σ (.n 229) + σ (.n 230) :=
    g 65 (.add (.n 231) (.n 229) (.n 230)) (by decide +kernel)
  have e232 : σ (.n 231) = polyEval [prodE (chWords σ 142 0), prodE (chWords σ 142 1),
      prodE (chWords σ 142 2)] (σ (.n 46)) := by
    rw [a232, m231, a227, m226, a222, m221, c220, tb_word_zero, m219, m218, m217, m225, m224, m223,
      m230, m229, m228,
      show σ (.n 145) = σ (.n 142) from cp 0 (by omega),
      show σ (.n 149) = σ (.n 146) from cp 1 (by omega),
      show σ (.n 153) = σ (.n 150) from cp 2 (by omega),
      show σ (.n 157) = σ (.n 154) from cp 3 (by omega),
      show σ (.n 174) = σ (.n 171) from cp 4 (by omega),
      show σ (.n 178) = σ (.n 175) from cp 5 (by omega),
      show σ (.n 182) = σ (.n 179) from cp 6 (by omega),
      show σ (.n 186) = σ (.n 183) from cp 7 (by omega),
      show σ (.n 203) = σ (.n 200) from cp 8 (by omega),
      show σ (.n 207) = σ (.n 204) from cp 9 (by omega),
      show σ (.n 211) = σ (.n 208) from cp 10 (by omega),
      show σ (.n 215) = σ (.n 212) from cp 11 (by omega)]
    have hc0 : chWords σ 142 0 = [σ (.n 142), σ (.n 146), σ (.n 150), σ (.n 154)] := by
      rw [chWords_eq]; rfl
    have hc1 : chWords σ 142 1 = [σ (.n 171), σ (.n 175), σ (.n 179), σ (.n 183)] := by
      rw [chWords_eq]; rfl
    have hc2 : chWords σ 142 2 = [σ (.n 200), σ (.n 204), σ (.n 208), σ (.n 212)] := by
      rw [chWords_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  rw [hrun] at hchk
  -- the third block's permutation and the two coordinates
  obtain ⟨k67, -⟩ := keccak_good (g 67 (.keccak (chRate 142 2 ++ lyCap 187) (lyOuts 232) false false)
    (by decide +kernel))
  obtain ⟨P2, B2⟩ := ch_perm_block (fun i hi => hp (4 * 2 + i) (by omega)) k67
  rw [B1, hc2] at P2 B2
  set P1 := Fs.perm ⟨capOf (Fs.perm ⟨capOf s.perm, D.ch0.map (·, dsObserve)⟩),
    D.ch1.map (·, dsObserve)⟩ with hP1
  set Q := Fs.perm ⟨capOf P1, D.ch2.map (·, dsObserve)⟩ with hQ
  have e246 : σ (.n 232) = challengeOf Q :=
    challengeT_value (s0 := .n 232) (b := 232) rfl (P2 0 (by omega))
  have hz : (([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++ lyCap 232 :
      List V).map σ) = rateOf [] ++ capOf Q := by
    rw [ly_zero_rate z42 z43 z44 z45, B2]
  obtain ⟨k69, P3, B3⟩ := lyc_keccak (rd := rd) (σ := σ) (S := S) (w := w)
    (g 68 (.keccak ([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++ lyCap 232)
      (lyOuts 245) false false) (by decide +kernel))
  rw [hz] at P3 B3
  have e260 : σ (.n 245) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value (s0 := .n 245) (b := 245) rfl (P3 0 (by omega))
  -- the sponge after the children
  have hsb : D.sb s st = ⟨capOf P1, D.ch2.map (·, dsObserve)⟩ := by
    show (((D.run s st).2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
      dsObserve = _
    rw [hrun, show s.squeeze.2 = ⟨capOf s.perm, []⟩ from rfl,
      absorbAll_short ⟨capOf s.perm, []⟩ D.ch0 dsObserve (by simp [h0]), List.nil_append,
      tb_absorbAll_full ⟨capOf s.perm, D.ch0.map (·, dsObserve)⟩ (by simp [h0]) D.ch1 h1,
      tb_absorbAll_full _ (by simp [h1]) D.ch2 h2]
  have hys : D.ys s st 2 = [σ (.n 232), σ (.n 245)] := by
    rw [e246, e260]; show ((D.sb s st).squeezeN 2).1 = _; rw [hsb, tb_squeezeN_two]
  have hs' : D.s' s st 2 = ⟨(List.range 5).map fun k ↦ σ (.n (253 + k)), []⟩ := by
    have e : ((List.range 5).map fun k ↦ σ (.n (253 + k))) = capOf (permOf (rateOf [] ++
        capOf Q)) := by rw [← B3]; simp [lyCap]
    rw [e]; show ((D.sb s st).squeezeN 2).2 = _; rw [hsb, tb_squeezeN_two]
  -- the slot of `L = 2`
  have hpt2 : (D.st' s st 2).point = [σ (.n 232), σ (.n 245)] := by
    show D.ys s st 2 ++ (D.run s st).1 = _
    rw [hys, hrun]; rfl
  have s40 : LoadHolds rd (σ (.n 18)) 40 (σ (.n 232)) := by
    have := hpt' 0 (by rw [hpt2]; simp)
    simp only [hpt2, List.getElem_cons_zero] at this
    rwa [tb_loadHolds_mul_gen_pow] at this
  have s41 : LoadHolds rd (σ (.n 18)) 41 (σ (.n 245)) := by
    have := hpt' 1 (by rw [hpt2]; simp)
    simp only [hpt2, List.getElem_cons_succ, List.getElem_cons_zero] at this
    rwa [tb_loadHolds_mul_gen_pow] at this
  have s255 : ∀ k < 5, LoadHolds rd (σ (.n 139)) k (σ (.n (253 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    exact ld k _ (by simpa [List.getD_eq_getElem?_getD, hk] using this)
  have c261 : σ (.n 258) = word 16384 0 := g 76 (.const (.n 258) (word 16384 0)) (by decide +kernel)
  have m262 := good_mul (g 77 (.mul (.n 259) (.n 5) (.n 258)) (by decide +kernel)) (by omega)
    (by omega)
  have w14 : word 16384 0 = gen ^ 14 := by
    rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, tb_word_two_pow (by norm_num)]
  have s262 : LoadHolds rd (σ (.n 139)) 5 (σ (.n 259)) := by
    rw [m262, c261, w14, show (14 : ℕ) = 2 + 12 by rfl, pow_add, ← mul_assoc, ← hxl]
    exact ld 5 _ hcur'
  have sv : ∀ t < 3, LoadHolds rd (σ (.n 139)) (6 + t)
      (multilinearEval (chWords σ 142 t) [σ (.n 232), σ (.n 245)]) := by
    intro t ht
    have h := hval' t ht
    rw [show 10 * 2 + 6 + t = 10 * 2 + (6 + t) by ring] at h
    have hv : (D.st' s st 2).values.getD t 0 =
        multilinearEval (chWords σ 142 t) [σ (.n 232), σ (.n 245)] := by
      show ([D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st 2))).getD t 0 = _
      rw [hys, hcw t ht]
      interval_cases t <;> rfl
    rw [hv] at h
    exact ld _ _ h
  have V0 := chc_val (C := C) (rt4_goodB hA 79 (chValT 142 232 245 139 0 260 6) (by decide +kernel))
    (by omega) (by omega) (fun i hi => cp (4 * 0 + i) (by omega)) (sv 0 (by omega))
  have V1 := chc_val (C := C) (rt4_goodB hA 89 (chValT 142 232 245 139 1 269 7) (by decide +kernel))
    (by omega) (by omega) (fun i hi => cp (4 * 1 + i) (by omega)) (sv 1 (by omega))
  have V2 := chc_val (C := C) (rt4_goodB hA 99 (chValT 142 232 245 139 2 278 8) (by decide +kernel))
    (by omega) (by omega) (fun i hi => cp (4 * 2 + i) (by omega)) (sv 2 (by omega))
  have c290 : σ (.n 287) = word 2 0 := g 109 (.const (.n 287) (word 2 0)) (by decide +kernel)
  rw [rtFourL_eq]
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [rtFourL, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA]
  refine ⟨forall_flatten_range fun i hi => (EV i (by omega)).2.2.2, k16,
    forall_flatten_range fun i hi => (EV (4 + i) (by omega)).2.2.2, k33,
    forall_flatten_range fun i hi => (EV (8 + i) (by omega)).2.2.2,
    m217, m218, m219, c220, m221, a222, m223, m224, m225, m226, a227, m228, m229, m230, m231,
    a232, show σ (.n 62) + σ (.n 231) = 0 by
      rw [h63, e232, h59, hc0, hc1, hc2, ← hchk, e_add_self],
    k67, k69, s40, s41, fun k hk => s255 k hk, c261, m262, s262, V0, V1, V2,
    c290, show LoadHolds rd (σ (.n 139)) 9 (σ (.n 287)) by
      rw [c290, tb_word_gen]; exact ld 9 _ hpos'⟩

end Arms

end
end LeanVM.Guest.B1.Tables
