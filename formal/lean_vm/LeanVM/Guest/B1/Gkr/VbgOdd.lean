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

Both start from the body's combiner `σ 36`, the claim `σ 52`, the capacity after the combiner
`σ 44 .. σ 48` and the zeros `σ 32 .. σ 35`, the children past the roots at `σ 5·g^2`; both store
the layer record `0` at `layers = σ 173` and the point at row `1` of `σ 185`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.B1
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

/-- A tree's new value at one coordinate `y = σ 387` (`lo + y·(lo + hi)`), stored at `off`. -/
def rtVal (b u v off : ℕ) : List Stmt :=
  [.atom (.add (.n b) (.n u) (.n v)), .atom (.mul (.n (b + 1)) (.n 387) (.n b)),
    .atom (.add (.n (b + 2)) (.n u) (.n (b + 1))), .atom (.load (.n (b + 2)) (.n 173) off)]

/-- The binary arm. -/
def rtTwoL : List Stmt :=
  ((List.range 4).map (chT (.n 5) 2 340)).flatten ++
  [keccakA (chRate 340 0 ++ lyCap 36) (lyOuts 356)] ++
  chT (.n 5) 2 340 4 ++ chT (.n 5) 2 340 5 ++
  [.atom (.mul (.n 377) (.n 372) (.n 376)), .atom (.const (.n 378) (word 0 0)),
    .atom (.mul (.n 379) (.n 36) (.n 378)), .atom (.add (.n 380) (.n 377) (.n 379)),
    .atom (.mul (.n 381) (.n 351) (.n 355)), .atom (.mul (.n 382) (.n 36) (.n 380)),
    .atom (.add (.n 383) (.n 381) (.n 382)), .atom (.mul (.n 384) (.n 343) (.n 347)),
    .atom (.mul (.n 385) (.n 36) (.n 383)), .atom (.add (.n 386) (.n 384) (.n 385)),
    .atom (.assertEq (.n 52) (.n 386)),
    keccakA ([.n 370, .n 371, .n 374, .n 375, .n 32, .n 33, .n 34, .n 35] ++ lyCap 356)
      (lyOuts 387),
    .atom (.load (.n 387) (.n 185) 40)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (395 + k)) (.n 173) k)) ++
  [.atom (.const (.n 400) (word 256 0)), .atom (.mul (.n 401) (.n 5) (.n 400)),
    .atom (.load (.n 401) (.n 173) 5)] ++
  rtVal 402 343 347 6 ++ rtVal 405 351 355 7 ++ rtVal 408 372 376 8 ++
  [.atom (.const (.n 411) (word 1099511627776 0)), .atom (.mul (.n 412) (.n 185) (.n 411)),
    .atom (.load (.n 412) (.n 173) 9), .atom (.const (.n 413) (word 1 0)),
    .atom (.load (.n 413) (.n 173) 10), .atom (.const (.n 414) (word 1 0)),
    .atom (.load (.n 414) (.n 173) 11), .atom (.const (.n 415) (word 1 0)),
    .atom (.load (.n 415) (.n 173) 12)]

set_option maxRecDepth 10000 in
theorem rtTwo_eq : rtTwo = rtTwoL := tbStmtsEqb_sound (by decide +kernel)

/-- The radix-four arm. -/
def rtFourL : List Stmt :=
  ((List.range 4).map (chT (.n 5) 2 190)).flatten ++
  [keccakA (chRate 190 0 ++ lyCap 36) (lyOuts 206)] ++
  ((List.range 4).map fun i ↦ chT (.n 5) 2 190 (4 + i)).flatten ++
  [keccakA (chRate 190 1 ++ lyCap 206) (lyOuts 235)] ++
  ((List.range 4).map fun i ↦ chT (.n 5) 2 190 (8 + i)).flatten ++
  [.atom (.mul (.n 264) (.n 251) (.n 255)), .atom (.mul (.n 265) (.n 264) (.n 259)),
    .atom (.mul (.n 266) (.n 265) (.n 263)), .atom (.const (.n 267) (word 0 0)),
    .atom (.mul (.n 268) (.n 36) (.n 267)), .atom (.add (.n 269) (.n 266) (.n 268)),
    .atom (.mul (.n 270) (.n 222) (.n 226)), .atom (.mul (.n 271) (.n 270) (.n 230)),
    .atom (.mul (.n 272) (.n 271) (.n 234)), .atom (.mul (.n 273) (.n 36) (.n 269)),
    .atom (.add (.n 274) (.n 272) (.n 273)), .atom (.mul (.n 275) (.n 193) (.n 197)),
    .atom (.mul (.n 276) (.n 275) (.n 201)), .atom (.mul (.n 277) (.n 276) (.n 205)),
    .atom (.mul (.n 278) (.n 36) (.n 274)), .atom (.add (.n 279) (.n 277) (.n 278)),
    .atom (.assertEq (.n 52) (.n 279)),
    keccakA (chRate 190 2 ++ lyCap 235) (lyOuts 280)] ++
  [keccakA ([.n 32, .n 32, .n 32, .n 32, .n 32, .n 33, .n 34, .n 35] ++ lyCap 280) (lyOuts 293)] ++
  [.atom (.load (.n 280) (.n 185) 40), .atom (.load (.n 293) (.n 185) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (301 + k)) (.n 173) k)) ++
  [.atom (.const (.n 306) (word 16384 0)), .atom (.mul (.n 307) (.n 5) (.n 306)),
    .atom (.load (.n 307) (.n 173) 5)] ++
  chValT 190 280 293 173 0 308 6 ++ chValT 190 280 293 173 1 317 7 ++
  chValT 190 280 293 173 2 326 8 ++
  [.atom (.const (.n 335) (word 1099511627776 0)), .atom (.mul (.n 336) (.n 185) (.n 335)),
    .atom (.load (.n 336) (.n 173) 9), .atom (.const (.n 337) (word 1 0)),
    .atom (.load (.n 337) (.n 173) 10), .atom (.const (.n 338) (word 1 0)),
    .atom (.load (.n 338) (.n 173) 11), .atom (.const (.n 339) (word 2 0)),
    .atom (.load (.n 339) (.n 173) 12)]

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
    (fun s hs => hG _ (List.mem_map_of_mem hs)) 274 (.n 189) rtFour rtTwo (by decide +kernel)
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

section Arms

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val} {kret : List E → Prop}

/-- **The binary arm, completely** (an odd depth): from the sponge `s` the roots wait in, one
step of one level (no point), its six words past the roots, and the slot of `L = 1`. -/
theorem rtc_two (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) {s : Fs} {st : GkrState}
    (hpt : st.point = [])
    (h59 : σ (.n 36) = s.squeeze.1) (h63 : σ (.n 52) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 36).map σ = capOf s.perm)
    (z42 : σ (.n 32) = 0) (z43 : σ (.n 33) = 0) (z44 : σ (.n 34) = 0) (z45 : σ (.n 35) = 0)
    {D : GkStepD} (hD : D.Ok s st 1) (hx : TbReadsAt rd (σ (.n 5) * gen ^ 2) D.xs)
    (hS' : GkSlot rd (σ (.n 173)) 1 (D.s' s st 1) (σ (.n 5) * gen ^ 2 * gen ^ D.xs.length)
      (D.st' s st 1) (σ (.n 185) * gen ^ 40) 1 1 1) :
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
  have hk : ∀ i < 6, some (chB 340 i, 5, 2 + i) ∉ vbgS.map loadKey := by decide +kernel
  have ch : ∀ i < 6, LoadHolds rd (σ (.n 5)) (2 + i) ([w0, w1, w2, w3, w4, w5].getD i 0) := by
    intro i hi
    have := hx i (by simp; omega)
    rw [tb_loadHolds_mul_gen_pow] at this
    rwa [← List.getD_eq_getElem _ 0] at this
  have EV : ∀ i < 6, _ := fun i hi => chc_read (C := C)
    (rt2_goodB hG (rtPos i) (chT (.n 5) 2 340 i) (rtTwo_check i hi)) (hk i hi) (ch i hi)
  have ev : ∀ i < 6, ∀ v, [w0, w1, w2, w3, w4, w5].getD i 0 = v → σ (.n (chB 340 i)) = v :=
    fun i hi v hv => (EV i hi).1.trans hv
  have q : ∀ i < 6, ∀ v, [w0, w1, w2, w3, w4, w5].getD i 0 = v → σ (.n (chB 340 i + 3)) = v :=
    fun i hi v hv => (EV i hi).2.1.trans ((EV i hi).1.trans hv)
  have hp : ∀ i < 6, FsPackOk σ (.n (chB 340 i)) (chB 340 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.2.1
  have q0 : σ (.n 343) = w0 := q 0 (by omega) w0 rfl
  have q1 : σ (.n 347) = w1 := q 1 (by omega) w1 rfl
  have q2 : σ (.n 351) = w2 := q 2 (by omega) w2 rfl
  have q3 : σ (.n 355) = w3 := q 3 (by omega) w3 rfl
  have q4 : σ (.n 372) = w4 := q 4 (by omega) w4 rfl
  have q5 : σ (.n 376) = w5 := q 5 (by omega) w5 rfl
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((rtTwo.drop n).take 1) = true →
      Good rd vbgS w σ a := fun n a heq => rt2_goodB hG n [.atom a] heq (.atom a) List.mem_cons_self
  -- the first four children's permutation
  obtain ⟨k16, -⟩ := keccak_good (g 16 (.keccak (chRate 340 0 ++ lyCap 36) (lyOuts 356) false false)
    (by decide +kernel))
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k16
  rw [hcap] at B0
  have hw0 : chWords σ 340 0 = [w0, w1, w2, w3] := by
    rw [chWords_eq]
    simp only [show 4 * 0 = 0 from rfl, Nat.zero_add]
    rw [ev 0 (by omega) w0 rfl, ev 1 (by omega) w1 rfl, ev 2 (by omega) w2 rfl,
      ev 3 (by omega) w3 rfl]
  rw [hw0] at B0
  -- the check
  have m334 := good_mul (g 25 (.mul (.n 377) (.n 372) (.n 376)) (by decide +kernel)) (by omega)
    (by omega)
  have c335 : σ (.n 378) = word 0 0 := g 26 (.const (.n 378) (word 0 0)) (by decide +kernel)
  have m336 := good_mul (g 27 (.mul (.n 379) (.n 36) (.n 378)) (by decide +kernel)) (by omega)
    (by omega)
  have a337 : σ (.n 380) = σ (.n 377) + σ (.n 379) :=
    g 28 (.add (.n 380) (.n 377) (.n 379)) (by decide +kernel)
  have m338 := good_mul (g 29 (.mul (.n 381) (.n 351) (.n 355)) (by decide +kernel)) (by omega)
    (by omega)
  have m339 := good_mul (g 30 (.mul (.n 382) (.n 36) (.n 380)) (by decide +kernel)) (by omega)
    (by omega)
  have a340 : σ (.n 383) = σ (.n 381) + σ (.n 382) :=
    g 31 (.add (.n 383) (.n 381) (.n 382)) (by decide +kernel)
  have m341 := good_mul (g 32 (.mul (.n 384) (.n 343) (.n 347)) (by decide +kernel)) (by omega)
    (by omega)
  have m342 := good_mul (g 33 (.mul (.n 385) (.n 36) (.n 383)) (by decide +kernel)) (by omega)
    (by omega)
  have a343 : σ (.n 386) = σ (.n 384) + σ (.n 385) :=
    g 34 (.add (.n 386) (.n 384) (.n 385)) (by decide +kernel)
  have e343 : σ (.n 386) = polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]]
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
  rw [show σ (.n 369) = w4 from ev 4 (by omega) w4 rfl] at e327 e328
  rw [show σ (.n 373) = w5 from ev 5 (by omega) w5 rfl] at e331 e332
  set P2 := Fs.perm ⟨capOf s.perm, [w0, w1, w2, w3].map (·, dsObserve)⟩ with hP2
  have hr2 : (([.n 370, .n 371, .n 374, .n 375, .n 32, .n 33, .n 34, .n 35] ++ lyCap 356 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ capOf P2 := by
    rw [List.map_append, B0, rateOf_eq_cells _ (by simp)]
    simp [pendCells, e327, e328, e331, e332, z42, z43, z44, z45]
  obtain ⟨k36, hP3, hC3⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := w)
    (g 36 (.keccak ([.n 370, .n 371, .n 374, .n 375, .n 32, .n 33, .n 34, .n 35] ++
      lyCap 356) (lyOuts 387) false false) (by decide +kernel))
  rw [hr2] at hP3 hC3
  have e357 : σ (.n 387) = challengeOf (permOf (rateOf [(w4, dsObserve), (w5, dsObserve)] ++
      capOf P2)) := challengeT_value (s0 := .n 387) (b := 387) rfl (hP3 0 (by omega))
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
  have hy : GkStepD.ys ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = [σ (.n 387)] := by
    rw [e357]; show ((GkStepD.sb _ s st).squeezeN 1).1 = _; rw [hsb]; rfl
  have hs' : GkStepD.s' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = ⟨(lyCap 387).map σ, []⟩ := by
    rw [hC3]; show ((GkStepD.sb _ s st).squeezeN 1).2 = _; rw [hsb]; rfl
  -- the slot of `L = 1`
  have hpt1 : (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).point = [σ (.n 387)] := by
    show GkStepD.ys _ s st 1 ++ (GkStepD.run _ s st).1 = _
    rw [hy, GkStepD.run, hpt]; rfl
  have hval1 : ∀ t < 3, (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).values.getD t 0 =
      multilinearEval ([[w0, w1], [w2, w3], [w4, w5]].getD t []) [σ (.n 387)] := by
    intro t ht
    show ([[w0, w1], [w2, w3], [w4, w5]].map (multilinearEval · (GkStepD.ys _ s st 1))).getD t 0 = _
    rw [hy]
    interval_cases t <;> rfl
  have s357 : LoadHolds rd (σ (.n 185)) 40 (σ (.n 387)) := by
    have := hpt' 0 (by rw [hpt1]; simp)
    simp only [hpt1, List.getElem_cons_zero] at this
    rw [tb_loadHolds_mul_gen_pow] at this
    exact this
  have s352 : ∀ k < 5, LoadHolds rd (σ (.n 173)) k (σ (.n (395 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simpa [lyCap, List.getD_eq_getElem?_getD, hk, show 387 + 8 + k = 395 + k by omega] using this
  have c358 : σ (.n 400) = word 256 0 := g 43 (.const (.n 400) (word 256 0)) (by decide +kernel)
  have m359 := good_mul (g 44 (.mul (.n 401) (.n 5) (.n 400)) (by decide +kernel)) (by omega)
    (by omega)
  have w8 : word 256 0 = gen ^ 8 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)]
  have s359 : LoadHolds rd (σ (.n 173)) 5 (σ (.n 401)) := by
    rw [m359, c358, w8, show (8 : ℕ) = 2 + 6 by rfl, pow_add, ← mul_assoc]
    exact hcur'
  have VAL : ∀ t < 3, ∀ (b u v off : ℕ), u < b → v < b → 387 < b →
      (∀ s ∈ rtVal b u v off, GoodS rd vbgS w σ s) →
      LoadHolds rd (σ (.n 173)) off (σ (.n u) + σ (.n 387) * (σ (.n u) + σ (.n v))) →
      ∀ s ∈ rtVal b u v off, SHolds C rd σ s := by
    intro t _ b u v off hu hv h3 gb hl
    have a0 : σ (.n b) = σ (.n u) + σ (.n v) := gb (.atom (.add (.n b) _ _)) (by simp [rtVal])
    have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 387) (.n b))) (by simp [rtVal]))
      (by omega) (by omega)
    have a2 : σ (.n (b + 2)) = σ (.n u) + σ (.n (b + 1)) :=
      gb (.atom (.add (.n (b + 2)) _ _)) (by simp [rtVal])
    simp only [rtVal, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    exact ⟨a0, m1, a2, show LoadHolds rd (σ (.n 173)) off (σ (.n (b + 2))) by
      rw [a2, m1, a0]; exact hl⟩
  have hv' : ∀ t < 3, ∀ u v, [[w0, w1], [w2, w3], [w4, w5]].getD t [] = [σ (.n u), σ (.n v)] →
      LoadHolds rd (σ (.n 173)) (6 + t) (σ (.n u) + σ (.n 387) * (σ (.n u) + σ (.n v))) := by
    intro t ht u v huv
    have h := hval' t ht
    rw [hval1 t ht, huv, show 13 * ((1 - 1) / 2) + 6 + t = 6 + t by norm_num] at h
    convert h using 1
    simp [multilinearEval, foldPairs]
    ring
  have V0 := VAL 0 (by omega) 402 343 347 6 (by omega) (by omega) (by omega)
    (rt2_goodB hG 46 _ (by decide +kernel)) (hv' 0 (by omega) 343 347 (by rw [q0, q1]; rfl))
  have V1 := VAL 1 (by omega) 405 351 355 7 (by omega) (by omega) (by omega)
    (rt2_goodB hG 50 _ (by decide +kernel)) (hv' 1 (by omega) 351 355 (by rw [q2, q3]; rfl))
  have V2 := VAL 2 (by omega) 408 372 376 8 (by omega) (by omega) (by omega)
    (rt2_goodB hG 54 _ (by decide +kernel)) (hv' 2 (by omega) 372 376 (by rw [q4, q5]; rfl))
  have c369 : σ (.n 411) = word 1099511627776 0 :=
    g 58 (.const (.n 411) (word 1099511627776 0)) (by decide +kernel)
  have m370 := good_mul (g 59 (.mul (.n 412) (.n 185) (.n 411)) (by decide +kernel)) (by omega)
    (by omega)
  have w40 : word 1099511627776 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  have c371 : σ (.n 413) = word 1 0 := g 61 (.const (.n 413) (word 1 0)) (by decide +kernel)
  have c372 : σ (.n 414) = word 1 0 := g 63 (.const (.n 414) (word 1 0)) (by decide +kernel)
  have c373 : σ (.n 415) = word 1 0 := g 65 (.const (.n 415) (word 1 0)) (by decide +kernel)
  rw [rtTwo_eq]
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [rtTwoL, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA]
  refine ⟨forall_flatten_range fun i hi => (EV i (by omega)).2.2.2, k16, (EV 4 (by omega)).2.2.2,
    (EV 5 (by omega)).2.2.2, m334, c335, m336, a337, m338, m339, a340, m341, m342, a343,
    show σ (.n 52) + σ (.n 386) = 0 by rw [h63, e343, ← hchk, e_add_self], k36, s357,
    fun k hk => s352 k hk, c358, m359, s359, V0, V1, V2, c369, m370,
    show LoadHolds rd (σ (.n 173)) 9 (σ (.n 412)) by rw [m370, c369, w40]; exact hrow',
    c371, show LoadHolds rd (σ (.n 173)) 10 (σ (.n 413)) by rw [c371, tb_word_one]; exact hpos',
    c372, show LoadHolds rd (σ (.n 173)) 11 (σ (.n 414)) by rw [c372, tb_word_one]; exact hhalf',
    c373, show LoadHolds rd (σ (.n 173)) 12 (σ (.n 415)) by rw [c373, tb_word_one]; exact hpar'⟩

/-- **The radix-four arm, completely** (an even depth): from the sponge `s` the roots wait in,
one step of two levels (no point), its twelve words past the roots, and the slot of `L = 2`. -/
theorem rtc_four (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) {s : Fs} {st : GkrState}
    (hpt : st.point = [])
    (h59 : σ (.n 36) = s.squeeze.1) (h63 : σ (.n 52) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 36).map σ = capOf s.perm)
    (z42 : σ (.n 32) = 0) (z43 : σ (.n 33) = 0) (z44 : σ (.n 34) = 0) (z45 : σ (.n 35) = 0)
    {D : GkStepD} (hD : D.Ok s st 2) (hx : TbReadsAt rd (σ (.n 5) * gen ^ 2) D.xs)
    (hS' : GkSlot rd (σ (.n 173)) 2 (D.s' s st 2) (σ (.n 5) * gen ^ 2 * gen ^ D.xs.length)
      (D.st' s st 2) (σ (.n 185) * gen ^ 40) 1 1 gen) :
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
  have hk : ∀ i < 12, some (chB 190 i, 5, 2 + i) ∉ vbgS.map loadKey := by decide +kernel
  have ch : ∀ i < 12, LoadHolds rd (σ (.n 5)) (2 + i) ((D.ch0 ++ (D.ch1 ++ D.ch2)).getD i 0) := by
    intro i hi
    have := hx i (by simp [h0, h1, h2]; omega)
    rw [tb_loadHolds_mul_gen_pow] at this
    rwa [← List.getD_eq_getElem _ 0] at this
  have EV : ∀ i < 12, _ := fun i hi => chc_read (C := C)
    (rt4_goodB hG (rtPos i) (chT (.n 5) 2 190 i) (rtFour_check i hi)) (hk i hi) (ch i hi)
  have hp : ∀ i < 12, FsPackOk σ (.n (chB 190 i)) (chB 190 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.2.1
  have cp : ∀ i < 12, σ (.n (chB 190 i + 3)) = σ (.n (chB 190 i)) := fun i hi => (EV i hi).2.1
  have hcw : ∀ m < 3, chWords σ 190 m = [D.ch0, D.ch1, D.ch2].getD m [] := by
    intro m hm
    have hv : ∀ i < 12, σ (.n (chB 190 i)) = (D.ch0 ++ (D.ch1 ++ D.ch2)).getD i 0 :=
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
  have hc0 : chWords σ 190 0 = D.ch0 := hcw 0 (by omega)
  have hc1 : chWords σ 190 1 = D.ch1 := hcw 1 (by omega)
  have hc2 : chWords σ 190 2 = D.ch2 := hcw 2 (by omega)
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((rtFour.drop n).take 1) = true →
      Good rd vbgS w σ a := fun n a heq => rt4_goodB hG n [.atom a] heq (.atom a) List.mem_cons_self
  -- the permutations of the children
  obtain ⟨k16, -⟩ := keccak_good (g 16 (.keccak (chRate 190 0 ++ lyCap 36) (lyOuts 206) false false)
    (by decide +kernel))
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k16
  rw [hcap, hc0] at B0
  obtain ⟨k33, -⟩ := keccak_good (g 33 (.keccak (chRate 190 1 ++ lyCap 206) (lyOuts 235) false false)
    (by decide +kernel))
  obtain ⟨-, B1⟩ := ch_perm_block (fun i hi => hp (4 * 1 + i) (by omega)) k33
  rw [B0, hc1] at B1
  -- the check
  have m219 := good_mul (g 50 (.mul (.n 264) (.n 251) (.n 255)) (by decide +kernel)) (by omega)
    (by omega)
  have m220 := good_mul (g 51 (.mul (.n 265) (.n 264) (.n 259)) (by decide +kernel)) (by omega)
    (by omega)
  have m221 := good_mul (g 52 (.mul (.n 266) (.n 265) (.n 263)) (by decide +kernel)) (by omega)
    (by omega)
  have c222 : σ (.n 267) = word 0 0 := g 53 (.const (.n 267) (word 0 0)) (by decide +kernel)
  have m223 := good_mul (g 54 (.mul (.n 268) (.n 36) (.n 267)) (by decide +kernel)) (by omega)
    (by omega)
  have a224 : σ (.n 269) = σ (.n 266) + σ (.n 268) :=
    g 55 (.add (.n 269) (.n 266) (.n 268)) (by decide +kernel)
  have m225 := good_mul (g 56 (.mul (.n 270) (.n 222) (.n 226)) (by decide +kernel)) (by omega)
    (by omega)
  have m226 := good_mul (g 57 (.mul (.n 271) (.n 270) (.n 230)) (by decide +kernel)) (by omega)
    (by omega)
  have m227 := good_mul (g 58 (.mul (.n 272) (.n 271) (.n 234)) (by decide +kernel)) (by omega)
    (by omega)
  have m228 := good_mul (g 59 (.mul (.n 273) (.n 36) (.n 269)) (by decide +kernel)) (by omega)
    (by omega)
  have a229 : σ (.n 274) = σ (.n 272) + σ (.n 273) :=
    g 60 (.add (.n 274) (.n 272) (.n 273)) (by decide +kernel)
  have m230 := good_mul (g 61 (.mul (.n 275) (.n 193) (.n 197)) (by decide +kernel)) (by omega)
    (by omega)
  have m231 := good_mul (g 62 (.mul (.n 276) (.n 275) (.n 201)) (by decide +kernel)) (by omega)
    (by omega)
  have m232 := good_mul (g 63 (.mul (.n 277) (.n 276) (.n 205)) (by decide +kernel)) (by omega)
    (by omega)
  have m233 := good_mul (g 64 (.mul (.n 278) (.n 36) (.n 274)) (by decide +kernel)) (by omega)
    (by omega)
  have a234 : σ (.n 279) = σ (.n 277) + σ (.n 278) :=
    g 65 (.add (.n 279) (.n 277) (.n 278)) (by decide +kernel)
  have e234 : σ (.n 279) = polyEval [prodE (chWords σ 190 0), prodE (chWords σ 190 1),
      prodE (chWords σ 190 2)] (σ (.n 36)) := by
    rw [a234, m233, a229, m228, a224, m223, c222, tb_word_zero, m221, m220, m219, m227, m226, m225,
      m232, m231, m230,
      show σ (.n 193) = σ (.n 190) from cp 0 (by omega),
      show σ (.n 197) = σ (.n 194) from cp 1 (by omega),
      show σ (.n 201) = σ (.n 198) from cp 2 (by omega),
      show σ (.n 205) = σ (.n 202) from cp 3 (by omega),
      show σ (.n 222) = σ (.n 219) from cp 4 (by omega),
      show σ (.n 226) = σ (.n 223) from cp 5 (by omega),
      show σ (.n 230) = σ (.n 227) from cp 6 (by omega),
      show σ (.n 234) = σ (.n 231) from cp 7 (by omega),
      show σ (.n 251) = σ (.n 248) from cp 8 (by omega),
      show σ (.n 255) = σ (.n 252) from cp 9 (by omega),
      show σ (.n 259) = σ (.n 256) from cp 10 (by omega),
      show σ (.n 263) = σ (.n 260) from cp 11 (by omega)]
    have hc0 : chWords σ 190 0 = [σ (.n 190), σ (.n 194), σ (.n 198), σ (.n 202)] := by
      rw [chWords_eq]; rfl
    have hc1 : chWords σ 190 1 = [σ (.n 219), σ (.n 223), σ (.n 227), σ (.n 231)] := by
      rw [chWords_eq]; rfl
    have hc2 : chWords σ 190 2 = [σ (.n 248), σ (.n 252), σ (.n 256), σ (.n 260)] := by
      rw [chWords_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  rw [hrun] at hchk
  -- the third block's permutation and the two coordinates
  obtain ⟨k67, -⟩ := keccak_good (g 67 (.keccak (chRate 190 2 ++ lyCap 235) (lyOuts 280) false false)
    (by decide +kernel))
  obtain ⟨P2, B2⟩ := ch_perm_block (fun i hi => hp (4 * 2 + i) (by omega)) k67
  rw [B1, hc2] at P2 B2
  set P1 := Fs.perm ⟨capOf (Fs.perm ⟨capOf s.perm, D.ch0.map (·, dsObserve)⟩),
    D.ch1.map (·, dsObserve)⟩ with hP1
  set Q := Fs.perm ⟨capOf P1, D.ch2.map (·, dsObserve)⟩ with hQ
  have e248 : σ (.n 280) = challengeOf Q :=
    challengeT_value (s0 := .n 280) (b := 280) rfl (P2 0 (by omega))
  have hz : (([.n 32, .n 32, .n 32, .n 32, .n 32, .n 33, .n 34, .n 35] ++ lyCap 280 :
      List V).map σ) = rateOf [] ++ capOf Q := by
    rw [ly_zero_rate z42 z43 z44 z45, B2]
  obtain ⟨k69, P3, B3⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := w)
    (g 68 (.keccak ([.n 32, .n 32, .n 32, .n 32, .n 32, .n 33, .n 34, .n 35] ++ lyCap 280)
      (lyOuts 293) false false) (by decide +kernel))
  rw [hz] at P3 B3
  have e262 : σ (.n 293) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value (s0 := .n 293) (b := 293) rfl (P3 0 (by omega))
  -- the sponge after the children
  have hsb : D.sb s st = ⟨capOf P1, D.ch2.map (·, dsObserve)⟩ := by
    show (((D.run s st).2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
      dsObserve = _
    rw [hrun, show s.squeeze.2 = ⟨capOf s.perm, []⟩ from rfl,
      absorbAll_short ⟨capOf s.perm, []⟩ D.ch0 dsObserve (by simp [h0]), List.nil_append,
      tb_absorbAll_full ⟨capOf s.perm, D.ch0.map (·, dsObserve)⟩ (by simp [h0]) D.ch1 h1,
      tb_absorbAll_full _ (by simp [h1]) D.ch2 h2]
  have hys : D.ys s st 2 = [σ (.n 280), σ (.n 293)] := by
    rw [e248, e262]; show ((D.sb s st).squeezeN 2).1 = _; rw [hsb, tb_squeezeN_two]
  have hs' : D.s' s st 2 = ⟨(List.range 5).map fun k ↦ σ (.n (301 + k)), []⟩ := by
    have e : ((List.range 5).map fun k ↦ σ (.n (301 + k))) = capOf (permOf (rateOf [] ++
        capOf Q)) := by rw [← B3]; simp [lyCap]
    rw [e]; show ((D.sb s st).squeezeN 2).2 = _; rw [hsb, tb_squeezeN_two]
  -- the slot of `L = 2`
  have hpt2 : (D.st' s st 2).point = [σ (.n 280), σ (.n 293)] := by
    show D.ys s st 2 ++ (D.run s st).1 = _
    rw [hys, hrun]; rfl
  have s40 : LoadHolds rd (σ (.n 185)) 40 (σ (.n 280)) := by
    have := hpt' 0 (by rw [hpt2]; simp)
    simp only [hpt2, List.getElem_cons_zero] at this
    rwa [tb_loadHolds_mul_gen_pow] at this
  have s41 : LoadHolds rd (σ (.n 185)) 41 (σ (.n 293)) := by
    have := hpt' 1 (by rw [hpt2]; simp)
    simp only [hpt2, List.getElem_cons_succ, List.getElem_cons_zero] at this
    rwa [tb_loadHolds_mul_gen_pow] at this
  have s257 : ∀ k < 5, LoadHolds rd (σ (.n 173)) k (σ (.n (301 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simpa [List.getD_eq_getElem?_getD, hk] using this
  have c263 : σ (.n 306) = word 16384 0 := g 76 (.const (.n 306) (word 16384 0)) (by decide +kernel)
  have m264 := good_mul (g 77 (.mul (.n 307) (.n 5) (.n 306)) (by decide +kernel)) (by omega)
    (by omega)
  have w14 : word 16384 0 = gen ^ 14 := by
    rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, tb_word_two_pow (by norm_num)]
  have s264 : LoadHolds rd (σ (.n 173)) 5 (σ (.n 307)) := by
    rw [m264, c263, w14, show (14 : ℕ) = 2 + 12 by rfl, pow_add, ← mul_assoc, ← hxl]
    exact hcur'
  have sv : ∀ t < 3, LoadHolds rd (σ (.n 173)) (6 + t)
      (multilinearEval (chWords σ 190 t) [σ (.n 280), σ (.n 293)]) := by
    intro t ht
    have h := hval' t ht
    rw [show 13 * ((2 - 1) / 2) + 6 + t = 6 + t by norm_num] at h
    have hv : (D.st' s st 2).values.getD t 0 =
        multilinearEval (chWords σ 190 t) [σ (.n 280), σ (.n 293)] := by
      show ([D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st 2))).getD t 0 = _
      rw [hys, hcw t ht]
      interval_cases t <;> rfl
    rwa [hv] at h
  have V0 := chc_val (C := C) (rt4_goodB hG 79 (chValT 190 280 293 173 0 308 6) (by decide +kernel)) (by omega) (by omega)
    (fun i hi => cp (4 * 0 + i) (by omega)) (sv 0 (by omega))
  have V1 := chc_val (C := C) (rt4_goodB hG 89 (chValT 190 280 293 173 1 317 7) (by decide +kernel)) (by omega) (by omega)
    (fun i hi => cp (4 * 1 + i) (by omega)) (sv 1 (by omega))
  have V2 := chc_val (C := C) (rt4_goodB hG 99 (chValT 190 280 293 173 2 326 8) (by decide +kernel)) (by omega) (by omega)
    (fun i hi => cp (4 * 2 + i) (by omega)) (sv 2 (by omega))
  have c292 : σ (.n 335) = word 1099511627776 0 :=
    g 109 (.const (.n 335) (word 1099511627776 0)) (by decide +kernel)
  have m293 := good_mul (g 110 (.mul (.n 336) (.n 185) (.n 335)) (by decide +kernel)) (by omega)
    (by omega)
  have w40 : word 1099511627776 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  have c294 : σ (.n 337) = word 1 0 := g 112 (.const (.n 337) (word 1 0)) (by decide +kernel)
  have c295 : σ (.n 338) = word 1 0 := g 114 (.const (.n 338) (word 1 0)) (by decide +kernel)
  have c296 : σ (.n 339) = word 2 0 := g 116 (.const (.n 339) (word 2 0)) (by decide +kernel)
  rw [rtFour_eq]
  refine holdsList_straightN _ (by decide +kernel) ?_ trivial
  simp only [rtFourL, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc,
    keccakA]
  refine ⟨forall_flatten_range fun i hi => (EV i (by omega)).2.2.2, k16,
    forall_flatten_range fun i hi => (EV (4 + i) (by omega)).2.2.2, k33,
    forall_flatten_range fun i hi => (EV (8 + i) (by omega)).2.2.2,
    m219, m220, m221, c222, m223, a224, m225, m226, m227, m228, a229, m230, m231, m232, m233,
    a234, show σ (.n 52) + σ (.n 279) = 0 by
      rw [h63, e234, h59, hc0, hc1, hc2, ← hchk, e_add_self],
    k67, k69, s40, s41, fun k hk => s257 k hk, c263, m264, s264, V0, V1, V2,
    c292, m293,
    show LoadHolds rd (σ (.n 173)) 9 (σ (.n 336)) by rw [m293, c292, w40]; exact hrow',
    c294, show LoadHolds rd (σ (.n 173)) 10 (σ (.n 337)) by rw [c294, tb_word_one]; exact hpos',
    c295, show LoadHolds rd (σ (.n 173)) 11 (σ (.n 338)) by rw [c295, tb_word_one]; exact hhalf',
    c296, show LoadHolds rd (σ (.n 173)) 12 (σ (.n 339)) by rw [c296, tb_word_gen]; exact hpar'⟩

end Arms

end
end LeanVM.Guest.B1.Tables
