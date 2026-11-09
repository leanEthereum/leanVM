/-
  LeanVM.Guest.B1.Gkr.VbgOdd

  `verify_bus_gkr`'s evaluation list, and its binary layer at an odd depth, completely: from the
  root slot, one step of one level, its words at the cursor and the slot of `L = 1`, the layer
  holds on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7Complete
public import LeanVM.Guest.B1.Gkr.Holds

/-!
# The binary layer, completely (G:1815-1850)

`vbgEvL`: `verify_bus_gkr`'s body as the forward evaluator walks it (its `ite`'s branches in
order, the checked inverse as its product, `fixNe`); `vb_good`, `vb_good_odd`: the statements of
the body and of the binary layer satisfy their equations. `odc_holds`: on a valuation satisfying
them, a memory holding the root slot, the step's words and the slot of `L = 1`, the binary layer
(`odBody`) holds, its regions `odR1 .. odR4`: the combiner, the children, the check and the new
coordinate, the slot's stores.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The evaluation list -/

/-- `verify_bus_gkr`'s evaluation list. -/
def vbgEvL : List Stmt := (flatIte vbgPre).map fixNe

theorem vb_chk : (chk 8 vbgEvL).isSome = true := by decide +kernel

/-- `verify_bus_gkr`'s stores. -/
def vbgS : List Atom := storesOf 8 vbgEvL

/-- Not an `assertNe`. -/
def noNeB : Stmt → Bool
  | .atom (.assertNe ..) => false
  | _ => true

theorem fixNe_of_noNe {s : Stmt} (h : noNeB s = true) : fixNe s = s := by
  cases s with
  | atom a => cases a <;> first | rfl | simp [noNeB] at h
  | _ => rfl

theorem odBody_noNe : odBody.all noNeB = true := by decide +kernel

theorem tb_mem_of_slice {pre : List Stmt} {n : ℕ} {blk : List Stmt}
    (h : tbStmtsEqb blk ((pre.drop n).take blk.length) = true) : ∀ s ∈ blk, s ∈ pre := by
  intro s hs
  rw [tbStmtsEqb_sound h] at hs
  exact List.mem_of_mem_drop (List.mem_of_mem_take hs)

section Eval

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val} {kret : List E → Prop}

/-- A statement of the body satisfies its equations. -/
theorem vb_good (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vbgPre.drop n).take 1) = true)
    (hfix : fixNe (.atom a) = .atom a) : Good rd vbgS w σ a := by
  have h := good_slice (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) n [.atom a] heq rfl _ List.mem_cons_self
  rw [hfix] at h
  exact h

/-- The statements of the binary layer satisfy their equations. -/
theorem vb_good_odd (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) :
    ∀ t ∈ odBody, GoodS rd vbgS w σ t := by
  have h := good_ite (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) 216 (.n 136) [] odBody (by decide +kernel)
  intro t ht
  have := h t (by simpa using ht)
  rwa [fixNe_of_noNe (List.all_eq_true.mp odBody_noNe t ht)] at this

/-- An atom of the binary layer satisfies its equations. -/
theorem od_good (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((odBody.drop n).take 1) = true) : Good rd vbgS w σ a :=
  vb_good_odd hG (.atom a) (tb_mem_of_slice heq _ List.mem_cons_self)

/-- A block of the binary layer satisfies its equations. -/
theorem od_goodB (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((odBody.drop n).take blk.length) = true) :
    ∀ s ∈ blk, GoodS rd vbgS w σ s :=
  fun s hs => vb_good_odd hG s (tb_mem_of_slice heq s hs)

end Eval

/-! ## The binary layer's regions -/

/-- The combiner, the claim and the row. -/
def odR1 : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (137 + k)) (.n 15) k)) ++
  (List.range 4).map (fun k ↦ .atom (.load (.n (142 + k)) (.n 15) (13 + k))) ++
  [.atom (.const (.n 146) (word 1 0 0)), .atom (.const (.n 147) (word 0 0 0)),
    .atom (.const (.n 148) (word 0 0 0)), .atom (.const (.n 149) (word 0 0 0)),
    .atom (.const (.n 150) (word 0 0 0)),
    keccakA ([.n 142, .n 143, .n 144, .n 145, .n 147, .n 148, .n 149, .n 150] ++
      (List.range 5).map fun k ↦ .n (137 + k)) (lyOuts 151)] ++
  challengeT (.n 151) (.n 152) 164 ++
  [.atom (.load (.n 171) (.n 15) 5), .atom (.load (.n 172) (.n 15) 6),
    .atom (.load (.n 173) (.n 15) 7), .atom (.load (.n 174) (.n 15) 8),
    .atom (.mul (.n 175) (.n 170) (.n 174)), .atom (.add (.n 176) (.n 173) (.n 175)),
    .atom (.mul (.n 177) (.n 170) (.n 176)), .atom (.add (.n 178) (.n 172) (.n 177)),
    .atom (.load (.n 179) (.n 15) 9), .atom (.const (.n 180) (word 1099511627776 0 0)),
    .atom (.mul (.n 181) (.n 179) (.n 180))]

/-- The children. -/
def odR2 : List Stmt :=
  ((List.range 4).map odEvT).flatten ++
  [keccakA ([.n 189, .n 191, .n 200, .n 202, .n 211, .n 213, .n 222, .n 224] ++ lyCap 151)
    (lyOuts 226)] ++
  odEvT 4 ++ odEvT 5

/-- The check and the new coordinate. -/
def odR3 : List Stmt :=
  [.atom (.mul (.n 261) (.n 249) (.n 260)), .atom (.const (.n 262) (word 0 0 0)),
    .atom (.mul (.n 263) (.n 170) (.n 262)), .atom (.add (.n 264) (.n 261) (.n 263)),
    .atom (.mul (.n 265) (.n 214) (.n 225)), .atom (.mul (.n 266) (.n 170) (.n 264)),
    .atom (.add (.n 267) (.n 265) (.n 266)), .atom (.mul (.n 268) (.n 192) (.n 203)),
    .atom (.mul (.n 269) (.n 170) (.n 267)), .atom (.add (.n 270) (.n 268) (.n 269)),
    .atom (.assertEq (.n 178) (.n 270)),
    keccakA ([.n 246, .n 248, .n 257, .n 259, .n 147, .n 148, .n 149, .n 150] ++ lyCap 226)
      (lyOuts 271)] ++
  challengeT (.n 271) (.n 272) 284

/-- The slot of `L = 1`. -/
def odR4 : List Stmt :=
  [.atom (.load (.n 290) (.n 181) 0)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (279 + k)) (.n 15) (17 + k))) ++
  ((List.range 4).map fun k ↦ [.atom (.const (.n (291 + k)) (word 0 0 0)),
    .atom (.load (.n (291 + k)) (.n 15) (30 + k))]).flatten ++
  [.atom (.const (.n 295) (word 64 0 0)), .atom (.mul (.n 296) (.n 171) (.n 295)),
    .atom (.load (.n 296) (.n 15) 22)] ++
  odVal 0 ++ odVal 1 ++ odVal 2 ++
  [.atom (.load (.n 181) (.n 15) 26), .atom (.const (.n 306) (word 2 0 0)),
    .atom (.load (.n 306) (.n 15) 27), .atom (.const (.n 307) (word 1 0 0)),
    .atom (.load (.n 307) (.n 15) 28), .atom (.const (.n 308) (word 1 0 0)),
    .atom (.load (.n 308) (.n 15) 29)]

theorem odBody_eq' : odBody = odR1 ++ odR2 ++ odR3 ++ odR4 :=
  tbStmtsEqb_sound (by decide +kernel)

theorem odEvT_noRet (i : ℕ) : Stmt.noRetList (odEvT i) = true := by
  simp [odEvT, fsNextT, fsPackT, Stmt.noRetList, Stmt.noRet]

theorem tb_list2_eq {l : List E} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

section Odd

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val} {kret : List E → Prop}

/-- **The binary layer, completely**: from the root slot, one step of one level (no point), its
words at the cursor, and the slot of `L = 1`. -/
theorem odc_holds (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) {s : Fs} {cur : E} {st : GkrState}
    {row pos half par : E} (hS : GkSlotC rd (σ (.n 15)) 0 s cur st row pos half par)
    {D : GkStepD} (hD : D.Ok s st 1) (hp : st.point = []) (hx : TbReadsAt rd cur D.xs)
    (hS' : GkSlotC rd (σ (.n 15)) 1 (D.s' s st 1) (cur * gen ^ 6) (D.st' s st 1)
      (row * gen ^ 40) gen 1 1) :
    Stmt.HoldsList C rd σ odBody True kret := by
  have g := fun n a heq => od_good (rd := rd) (w := w) (σ := σ) hG n a heq
  obtain ⟨hcl, hcan, hpe, hcap, hrate, hcur, hvl, hval, hrow, -, -, -, -, -⟩ := hS
  obtain ⟨-, -, -, hcap', hrate', hcur', -, hval', hrow', -, hpt', hpos', hhalf', hpar'⟩ := hS'
  simp only [Nat.mul_zero, Nat.zero_add] at hcap hrate hcur hval hrow
  obtain ⟨cs, ch0, ch1, ch2⟩ := D
  obtain ⟨hl, -, h0, h1, h2, hchk⟩ := hD
  simp only at hl h0 h1 h2 hchk
  rw [hp] at hl
  rw [show (2 : ℕ) ^ 1 = 2 from rfl] at h0 h1 h2
  obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero hl
  obtain ⟨w0, w1, rfl⟩ := tb_list2_eq h0
  obtain ⟨w2, w3, rfl⟩ := tb_list2_eq h1
  obtain ⟨w4, w5, rfl⟩ := tb_list2_eq h2
  have hxs : GkStepD.xs ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ = [w0, w1, w2, w3, w4, w5] := rfl
  rw [hxs] at hx
  -- the combiner
  have gcap := od_goodB hG 0 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (137 + k)) (.n 15) k)) (by decide +kernel)
  have kcap : ∀ k < 5, some (137 + k, 15, k) ∉ vbgS.map loadKey := by decide +kernel
  have rcap : ∀ k < 5, σ (.n (137 + k)) = s.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 15)) k (σ (.n (137 + k))) := fun k hk =>
    good_readS (gcap _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kcap k hk)
      (hcap k hk)
  have grate := od_goodB hG 5 ((List.range 4).map fun k ↦
    Stmt.atom (.load (.n (142 + k)) (.n 15) (13 + k))) (by decide +kernel)
  have krate : ∀ k < 4, some (142 + k, 15, 13 + k) ∉ vbgS.map loadKey := by decide +kernel
  have rrate : ∀ k < 4, σ (.n (142 + k)) = (rateOf s.pend).getD k 0 ∧
      LoadHolds rd (σ (.n 15)) (13 + k) (σ (.n (142 + k))) := fun k hk =>
    good_readS (grate _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (krate k hk)
      (hrate k hk)
  have c146 : σ (.n 146) = word 1 0 0 := g 9 (.const (.n 146) (word 1 0 0)) (by decide +kernel)
  have c147 : σ (.n 147) = word 0 0 0 := g 10 (.const (.n 147) (word 0 0 0)) (by decide +kernel)
  have c148 : σ (.n 148) = word 0 0 0 := g 11 (.const (.n 148) (word 0 0 0)) (by decide +kernel)
  have c149 : σ (.n 149) = word 0 0 0 := g 12 (.const (.n 149) (word 0 0 0)) (by decide +kernel)
  have c150 : σ (.n 150) = word 0 0 0 := g 13 (.const (.n 150) (word 0 0 0)) (by decide +kernel)
  rw [tb_word_zero] at c147 c148 c149 c150
  have hrl : (rateOf s.pend).length = 8 := by simp [rateOf]
  have hins : (([.n 142, .n 143, .n 144, .n 145, .n 147, .n 148, .n 149, .n 150] ++
      (List.range 5).map fun k ↦ V.n (137 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [tb_eq_map_getD hrl, tb_eq_map_getD hcl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq, and_true]
    refine ⟨(rrate 0 (by omega)).1, (rrate 1 (by omega)).1, (rrate 2 (by omega)).1,
      (rrate 3 (by omega)).1, ?_, ?_, ?_, ?_, (rcap 0 (by omega)).1, (rcap 1 (by omega)).1,
      (rcap 2 (by omega)).1, (rcap 3 (by omega)).1, (rcap 4 (by omega)).1⟩
    · rw [c147, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c148, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c149, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c150, rateOf_getD_four (by omega) (by omega) (by omega)]
  have hcanI : AllCanonical (rateOf s.pend ++ s.cap) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact rateOf_canonical (by omega) c hc
    · exact hcan c hc
  obtain ⟨k14, hP1, hC1⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := w)
    (g 14 (.keccak ([.n 142, .n 143, .n 144, .n 145, .n 147, .n 148, .n 149, .n 150] ++
      (List.range 5).map fun k ↦ .n (137 + k)) (lyOuts 151) false false) (by decide +kernel))
    (by rw [hins]; exact hcanI)
  rw [hins] at hP1 hC1
  have hco := challengeT_good (od_goodB hG 15 (challengeT (.n 151) (.n 152) 164)
    (by decide +kernel)) (by rw [hP1 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e170 : σ (.n 170) = s.squeeze.1 :=
    challengeT_value hco (hP1 0 (by omega)) (hP1 1 (by omega))
  -- the claim and the row
  obtain ⟨e171, l171⟩ := good_read (g 23 (.load (.n 171) (.n 15) 5) (by decide +kernel))
    (by decide +kernel) hcur
  obtain ⟨e172, l172⟩ := good_read (g 24 (.load (.n 172) (.n 15) 6) (by decide +kernel))
    (by decide +kernel) (hval 0 (by omega))
  obtain ⟨e173, l173⟩ := good_read (g 25 (.load (.n 173) (.n 15) 7) (by decide +kernel))
    (by decide +kernel) (hval 1 (by omega))
  obtain ⟨e174, l174⟩ := good_read (g 26 (.load (.n 174) (.n 15) 8) (by decide +kernel))
    (by decide +kernel) (hval 2 (by omega))
  have m175 := good_mul (g 27 (.mul (.n 175) (.n 170) (.n 174)) (by decide +kernel)) (by omega)
    (by omega)
  have a176 : σ (.n 176) = σ (.n 173) + σ (.n 175) :=
    g 28 (.add (.n 176) (.n 173) (.n 175)) (by decide +kernel)
  have m177 := good_mul (g 29 (.mul (.n 177) (.n 170) (.n 176)) (by decide +kernel)) (by omega)
    (by omega)
  have a178 : σ (.n 178) = σ (.n 172) + σ (.n 177) :=
    g 30 (.add (.n 178) (.n 172) (.n 177)) (by decide +kernel)
  obtain ⟨e179, l179⟩ := good_read (g 31 (.load (.n 179) (.n 15) 9) (by decide +kernel))
    (by decide +kernel) hrow
  have c180 : σ (.n 180) = word 1099511627776 0 0 :=
    g 32 (.const (.n 180) (word 1099511627776 0 0)) (by decide +kernel)
  have m181 := good_mul (g 33 (.mul (.n 181) (.n 179) (.n 180)) (by decide +kernel)) (by omega)
    (by omega)
  have w40 : word 1099511627776 0 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  have e178 : σ (.n 178) = polyEval st.values s.squeeze.1 := by
    obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a178, m177, a176, m175, e172, e173, e174, e170, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring
  -- the children
  have ch : ∀ i < 6, LoadHolds rd (σ (.n 171)) i ([w0, w1, w2, w3, w4, w5].getD i 0) := by
    intro i hi
    have := hx i (by simp; omega)
    rw [e171]
    rwa [← List.getD_eq_getElem _ 0] at this
  have hk : ∀ i < 6, some (odEv i, 171, i) ∉ vbgS.map loadKey := by decide +kernel
  have EV : ∀ i < 6, Stmt.HoldsList C rd σ (odEvT i) True kret ∧
      σ (.n (odEv i)) = [w0, w1, w2, w3, w4, w5].getD i 0 ∧
      σ (.n (odEv i + 10)) = σ (.n (odEv i)) ∧
      (σ (.n (odEv i + 7)), σ (.n (odEv i + 9))) =
        Keccak.scalarCells (σ (.n (odEv i))) dsObserve := by
    intro i hi
    have gb := od_goodB hG (odPos i) (odEvT i) (odEvs_check i hi)
    obtain ⟨e0, hcells, hfs⟩ := fsNextT_good (C := C) (kret := kret)
      (fun s hs => gb s (List.mem_append_left _ hs)) (hk i hi) (ch i hi)
    have cp : σ (.n (odEv i + 10)) = σ (.n (odEv i)) :=
      gb (.atom (.copy (.n (odEv i + 10)) (.n (odEv i)))) (by simp [odEvT])
    refine ⟨?_, e0, cp, by rw [e0]; exact hcells⟩
    unfold odEvT
    rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT, Stmt.noRetList, Stmt.noRet])]
    refine ⟨hfs, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact cp
  have ev : ∀ i < 6, ∀ v, [w0, w1, w2, w3, w4, w5].getD i 0 = v → σ (.n (odEv i)) = v :=
    fun i hi v hv => (EV i hi).2.1.trans hv
  have e182 : σ (.n 182) = w0 := ev 0 (by omega) w0 rfl
  have e193 : σ (.n 193) = w1 := ev 1 (by omega) w1 rfl
  have e204 : σ (.n 204) = w2 := ev 2 (by omega) w2 rfl
  have e215 : σ (.n 215) = w3 := ev 3 (by omega) w3 rfl
  have e239 : σ (.n 239) = w4 := ev 4 (by omega) w4 rfl
  have e250 : σ (.n 250) = w5 := ev 5 (by omega) w5 rfl
  have cl : ∀ i < 6, σ (.n (odEv i + 7)) = (Keccak.scalarCells (σ (.n (odEv i))) dsObserve).1 ∧
      σ (.n (odEv i + 9)) = (Keccak.scalarCells (σ (.n (odEv i))) dsObserve).2 :=
    fun i hi => Prod.ext_iff.mp (EV i hi).2.2.2
  have e189 : σ (.n 189) = (Keccak.scalarCells w0 dsObserve).1 := by
    rw [← e182]; exact (cl 0 (by omega)).1
  have e191 : σ (.n 191) = (Keccak.scalarCells w0 dsObserve).2 := by
    rw [← e182]; exact (cl 0 (by omega)).2
  have e200 : σ (.n 200) = (Keccak.scalarCells w1 dsObserve).1 := by
    rw [← e193]; exact (cl 1 (by omega)).1
  have e202 : σ (.n 202) = (Keccak.scalarCells w1 dsObserve).2 := by
    rw [← e193]; exact (cl 1 (by omega)).2
  have e211 : σ (.n 211) = (Keccak.scalarCells w2 dsObserve).1 := by
    rw [← e204]; exact (cl 2 (by omega)).1
  have e213 : σ (.n 213) = (Keccak.scalarCells w2 dsObserve).2 := by
    rw [← e204]; exact (cl 2 (by omega)).2
  have e222 : σ (.n 222) = (Keccak.scalarCells w3 dsObserve).1 := by
    rw [← e215]; exact (cl 3 (by omega)).1
  have e224 : σ (.n 224) = (Keccak.scalarCells w3 dsObserve).2 := by
    rw [← e215]; exact (cl 3 (by omega)).2
  have e246 : σ (.n 246) = (Keccak.scalarCells w4 dsObserve).1 := by
    rw [← e239]; exact (cl 4 (by omega)).1
  have e248 : σ (.n 248) = (Keccak.scalarCells w4 dsObserve).2 := by
    rw [← e239]; exact (cl 4 (by omega)).2
  have e257 : σ (.n 257) = (Keccak.scalarCells w5 dsObserve).1 := by
    rw [← e250]; exact (cl 5 (by omega)).1
  have e259 : σ (.n 259) = (Keccak.scalarCells w5 dsObserve).2 := by
    rw [← e250]; exact (cl 5 (by omega)).2
  have hins2 : (([.n 189, .n 191, .n 200, .n 202, .n 211, .n 213, .n 222, .n 224] ++ lyCap 151 :
      List V).map σ) = rateOf [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve), (w3, dsObserve)] ++
      capOf s.perm := by
    rw [List.map_append, hC1, rateOf_eq_cells [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
      (w3, dsObserve)] (by simp)]
    simp only [List.map_cons, List.map_nil, e189, e191, e200, e202, e211, e213, e222, e224,
      pendCells, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, List.append_nil]
    rfl
  have hcan2 : AllCanonical (rateOf [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
      (w3, dsObserve)] ++ capOf s.perm) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact rateOf_canonical (by simp) c hc
    · exact tb_capOf_canonical _ c hc
  obtain ⟨k74, hP2, hC2⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := w)
    (g 74 (.keccak ([.n 189, .n 191, .n 200, .n 202, .n 211, .n 213, .n 222, .n 224] ++
      lyCap 151) (lyOuts 226) false false) (by decide +kernel)) (by rw [hins2]; exact hcan2)
  rw [hins2] at hP2 hC2
  set P2 := permOf (rateOf [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
    (w3, dsObserve)] ++ capOf s.perm) with hP2def
  -- the check
  have m261 := good_mul (g 95 (.mul (.n 261) (.n 249) (.n 260)) (by decide +kernel)) (by omega)
    (by omega)
  have c262 : σ (.n 262) = word 0 0 0 := g 96 (.const (.n 262) (word 0 0 0)) (by decide +kernel)
  have m263 := good_mul (g 97 (.mul (.n 263) (.n 170) (.n 262)) (by decide +kernel)) (by omega)
    (by omega)
  have a264 : σ (.n 264) = σ (.n 261) + σ (.n 263) :=
    g 98 (.add (.n 264) (.n 261) (.n 263)) (by decide +kernel)
  have m265 := good_mul (g 99 (.mul (.n 265) (.n 214) (.n 225)) (by decide +kernel)) (by omega)
    (by omega)
  have m266 := good_mul (g 100 (.mul (.n 266) (.n 170) (.n 264)) (by decide +kernel)) (by omega)
    (by omega)
  have a267 : σ (.n 267) = σ (.n 265) + σ (.n 266) :=
    g 101 (.add (.n 267) (.n 265) (.n 266)) (by decide +kernel)
  have m268 := good_mul (g 102 (.mul (.n 268) (.n 192) (.n 203)) (by decide +kernel)) (by omega)
    (by omega)
  have m269 := good_mul (g 103 (.mul (.n 269) (.n 170) (.n 267)) (by decide +kernel)) (by omega)
    (by omega)
  have a270 : σ (.n 270) = σ (.n 268) + σ (.n 269) :=
    g 104 (.add (.n 270) (.n 268) (.n 269)) (by decide +kernel)
  have q192 : σ (.n 192) = w0 := ((EV 0 (by omega)).2.2.1).trans e182
  have q203 : σ (.n 203) = w1 := ((EV 1 (by omega)).2.2.1).trans e193
  have q214 : σ (.n 214) = w2 := ((EV 2 (by omega)).2.2.1).trans e204
  have q225 : σ (.n 225) = w3 := ((EV 3 (by omega)).2.2.1).trans e215
  have q249 : σ (.n 249) = w4 := ((EV 4 (by omega)).2.2.1).trans e239
  have q260 : σ (.n 260) = w5 := ((EV 5 (by omega)).2.2.1).trans e250
  have e270 : σ (.n 270) = polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]]
      s.squeeze.1 := by
    rw [a270, m269, a267, m266, a264, m263, c262, tb_word_zero, m261, m265, m268, q192, q203, q214,
      q225, q249, q260, e170]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  have hrun : (GkStepD.run ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st).2.1 =
      polyEval st.values s.squeeze.1 := by
    rw [GkStepD.run, hp]; rfl
  rw [hrun] at hchk
  -- the new coordinate
  have hins3 : (([.n 246, .n 248, .n 257, .n 259, .n 147, .n 148, .n 149, .n 150] ++ lyCap 226 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ capOf P2 := by
    rw [List.map_append, hC2, rateOf_eq_cells [(w4, dsObserve), (w5, dsObserve)] (by simp)]
    simp only [List.map_cons, List.map_nil, e246, e248, e257, e259, c147, c148, c149, c150,
      pendCells, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, List.append_nil]
    rfl
  have hcan3 : AllCanonical (rateOf [(w4, dsObserve), (w5, dsObserve)] ++ capOf P2) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact rateOf_canonical (by simp) c hc
    · exact tb_capOf_canonical _ c hc
  obtain ⟨k106, hP3, hC3⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := w)
    (g 106 (.keccak ([.n 246, .n 248, .n 257, .n 259, .n 147, .n 148, .n 149, .n 150] ++
      lyCap 226) (lyOuts 271) false false) (by decide +kernel)) (by rw [hins3]; exact hcan3)
  rw [hins3] at hP3 hC3
  have hco3 := challengeT_good (od_goodB hG 107 (challengeT (.n 271) (.n 272) 284)
    (by decide +kernel)) (by rw [hP3 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e290 : σ (.n 290) = challengeOf (permOf (rateOf [(w4, dsObserve), (w5, dsObserve)] ++
      capOf P2)) := challengeT_value hco3 (hP3 0 (by omega)) (hP3 1 (by omega))
  -- the sponge after the children
  have hsb : GkStepD.sb ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st =
      ⟨capOf P2, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
    show (((GkStepD.run ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st).2.2.absorbAll [w0, w1]
      dsObserve).absorbAll [w2, w3] dsObserve).absorbAll [w4, w5] dsObserve = _
    rw [show (GkStepD.run ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st).2.2 = s.squeeze.2 by
      rw [GkStepD.run, hp]; rfl]
    have h1 : s.squeeze.2.absorbAll [w0, w1] dsObserve =
        ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ := by
      rw [absorbAll_short _ _ _ (by simp [Fs.squeeze])]; rfl
    have h2 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll [w2, w3]
        dsObserve = ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
          (w3, dsObserve)]⟩ := by
      rw [absorbAll_short _ _ _ (by simp)]; rfl
    have h3 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
        (w3, dsObserve)]⟩ : Fs).absorbAll [w4, w5] dsObserve =
          ⟨capOf P2, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
      rw [tb_absorbAll_full' _ (by simp) _ (by simp) (by simp)]; rfl
    rw [h1, h2, h3]
  have hy : GkStepD.ys ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = [σ (.n 290)] := by
    rw [e290]; show ((GkStepD.sb _ s st).squeezeN 1).1 = _; rw [hsb]; rfl
  have hs' : GkStepD.s' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1 = ⟨(lyCap 271).map σ, []⟩ := by
    rw [hC3]; show ((GkStepD.sb _ s st).squeezeN 1).2 = _; rw [hsb]; rfl
  -- the slot of `L = 1`
  have hpt1 : (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).point = [σ (.n 290)] := by
    show GkStepD.ys _ s st 1 ++ (GkStepD.run _ s st).1 = _
    rw [hy, GkStepD.run, hp]; rfl
  have hval1 : ∀ t < 3, (GkStepD.st' ⟨[], [w0, w1], [w2, w3], [w4, w5]⟩ s st 1).values.getD t 0 =
      multilinearEval ([[w0, w1], [w2, w3], [w4, w5]].getD t []) [σ (.n 290)] := by
    intro t ht
    show ([[w0, w1], [w2, w3], [w4, w5]].map (multilinearEval · (GkStepD.ys _ s st 1))).getD t 0 = _
    rw [hy]
    interval_cases t <;> rfl
  have e181 : σ (.n 181) = row * gen ^ 40 := by rw [m181, e179, c180, w40]
  have s281 : LoadHolds rd (σ (.n 181)) 0 (σ (.n 290)) := by
    have := hpt' 0 (by rw [hpt1]; simp)
    simp only [hpt1, List.getElem_cons_zero] at this
    rw [e181]; exact this
  have s270 : ∀ k < 5, LoadHolds rd (σ (.n 15)) (17 + k) (σ (.n (279 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simpa [lyCap, List.getD_eq_getElem?_getD, hk, show 262 + 8 + k = 270 + k by omega] using this
  have gz := od_goodB hG 121 ((List.range 4).map fun k ↦ [Stmt.atom (.const (.n (291 + k))
    (word 0 0 0)), .atom (.load (.n (291 + k)) (.n 15) (30 + k))]).flatten (by decide +kernel)
  have c295 : σ (.n 295) = word 64 0 0 := g 129 (.const (.n 295) (word 64 0 0)) (by decide +kernel)
  have m296 := good_mul (g 130 (.mul (.n 296) (.n 171) (.n 295)) (by decide +kernel)) (by omega)
    (by omega)
  have w64 : word 64 0 0 = gen ^ 6 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, tb_word_two_pow (by norm_num)]
  have c306 : σ (.n 306) = word 2 0 0 := g 145 (.const (.n 306) (word 2 0 0)) (by decide +kernel)
  have c307 : σ (.n 307) = word 1 0 0 := g 147 (.const (.n 307) (word 1 0 0)) (by decide +kernel)
  have c308 : σ (.n 308) = word 1 0 0 := g 149 (.const (.n 308) (word 1 0 0)) (by decide +kernel)
  have VAL : ∀ t < 3, Stmt.HoldsList C rd σ (odVal t) True kret := by
    intro t ht
    have gb := od_goodB hG (132 + 4 * t) (odVal t) (by interval_cases t <;> decide +kernel)
    have hlo : σ (.n (odEv (2 * t) + 10)) = [w0, w1, w2, w3, w4, w5].getD (2 * t) 0 :=
      ((EV (2 * t) (by omega)).2.2.1).trans ((EV (2 * t) (by omega)).2.1)
    have hhi : σ (.n (odEv (2 * t + 1) + 10)) = [w0, w1, w2, w3, w4, w5].getD (2 * t + 1) 0 :=
      ((EV (2 * t + 1) (by omega)).2.2.1).trans ((EV (2 * t + 1) (by omega)).2.1)
    have a0 : σ (.n (297 + 3 * t)) =
        σ (.n (odEv (2 * t) + 10)) + σ (.n (odEv (2 * t + 1) + 10)) :=
      gb (.atom (.add (.n (297 + 3 * t)) _ _)) (by simp [odVal])
    have m1 := good_mulS (gb (.atom (.mul (.n (297 + 3 * t + 1)) (.n 290) (.n (297 + 3 * t))))
      (by simp [odVal])) (by omega) (by omega)
    have a2 : σ (.n (297 + 3 * t + 2)) = σ (.n (odEv (2 * t) + 10)) + σ (.n (297 + 3 * t + 1)) :=
      gb (.atom (.add (.n (297 + 3 * t + 2)) _ _)) (by simp [odVal])
    have hv := hval' t ht
    rw [hval1 t ht] at hv
    simp only [odVal, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨a0, m1, a2, ?_⟩
    rw [a2, m1, a0, hlo, hhi]
    convert hv using 1
    interval_cases t <;> simp [multilinearEval, foldPairs] <;> ring
  rw [odBody_eq']
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the combiner, the claim, the row
    unfold odR1
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => (rcap k hk).2
    · exact (tb_holdsList_mapAtoms 4 _).mpr fun k hk => (rrate k hk).2
    · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨c146, by rw [c147, tb_word_zero], by rw [c148, tb_word_zero],
        by rw [c149, tb_word_zero], by rw [c150, tb_word_zero], k14⟩
    · exact (holds_challengeT _ _ _ _ _).mpr ⟨hco, trivial⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨l171, l172, l173, l174, m175, a176, m177, a178, l179, c180, m181⟩
  · -- the children
    unfold odR2
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    refine ⟨⟨⟨?_, ?_⟩, (EV 4 (by omega)).1⟩, (EV 5 (by omega)).1⟩
    · exact (tb_holdsList_flatten_range 4 _ odEvT_noRet).mpr fun i hi => (EV i (by omega)).1
    · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, and_true]; exact k74
  · -- the check, the new coordinate
    unfold odR3
    rw [tb_holdsList_append_noRet (by decide +kernel)]
    refine ⟨?_, (holds_challengeT _ _ _ _ _).mpr ⟨hco3, trivial⟩⟩
    simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨m261, c262, m263, a264, m265, m266, a267, m268, m269, a270,
      by rw [e178, e270, ← hchk, e_add_self], k106⟩
  · -- the slot of `L = 1`
    unfold odR4
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, VAL 0 (by omega)⟩, VAL 1 (by omega)⟩, VAL 2 (by omega)⟩, ?_⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]; exact s281
    · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => s270 k hk
    · refine (tb_holdsList_flatten_range 4 _ fun _ => rfl).mpr fun k hk => ?_
      have c : σ (.n (291 + k)) = word 0 0 0 :=
        gz (.atom (.const (.n (291 + k)) (word 0 0 0))) (List.mem_flatten.mpr ⟨_,
          List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, List.mem_cons_self⟩)
      have hz := hrate' k hk
      rw [hs', tb_rateOf_nil_getD, show 17 * 1 + 13 + k = 30 + k by ring] at hz
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨c, by rw [c, tb_word_zero]; exact hz⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨c295, m296, ?_⟩
      rw [m296, c295, w64, e171]; exact hcur'
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨by rw [e181]; exact hrow', c306, by rw [c306, tb_word_gen]; exact hpos', c307,
        by rw [c307, tb_word_one]; exact hhalf', c308, by rw [c308, tb_word_one]; exact hpar'⟩

end Odd

end
end LeanVM.Guest.B1.Tables
