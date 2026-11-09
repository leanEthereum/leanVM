/-
  LeanVM.Guest.B1.Gkr.Odd

  `verify_bus_gkr`'s binary layer at an odd depth: one step of one level from the root slot.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerStep
public import LeanVM.Guest.B1.Sumcheck.Run

/-!
# The odd depth's binary layer (G:1794-1836)

At an odd depth the guest runs one level first, from the root slot (`L = 0`): the combiner's
permutation over the slot's capacity and the two waiting roots, no rounds, the six children
(two per tree) read and absorbed, their check, the one new coordinate, and the slot of `L = 1`.
`od_step`: it is `gkrStep 1`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Child `i`'s word's value. -/
def odEv (i : ℕ) : ℕ := if i < 4 then 182 + 11 * i else 195 + 11 * i

/-- Child `i`'s read: `fs_next` at the cursor, its word copied. -/
def odEvT (i : ℕ) : List Stmt :=
  fsNextT (.n 171) i (odEv i) ++ [.atom (.copy (.n (odEv i + 10)) (.n (odEv i)))]

/-- Side `t`'s new value `lo + c·(lo + hi)`, its values from `297 + 3t`, stored at `23 + t`. -/
def odVal (t : ℕ) : List Stmt :=
  let b := 297 + 3 * t
  [.atom (.add (.n b) (.n (odEv (2 * t) + 10)) (.n (odEv (2 * t + 1) + 10))),
    .atom (.mul (.n (b + 1)) (.n 290) (.n b)),
    .atom (.add (.n (b + 2)) (.n (odEv (2 * t) + 10)) (.n (b + 1))),
    .atom (.load (.n (b + 2)) (.n 15) (23 + t))]

/-- The binary layer (`s216_e`). -/
def odBody : List Stmt :=
  List.flatten [
    (List.range 5).map (fun k ↦ .atom (.load (.n (137 + k)) (.n 15) k)),
    (List.range 4).map (fun k ↦ .atom (.load (.n (142 + k)) (.n 15) (13 + k))),
    [.atom (.const (.n 146) (word 1 0 0)), .atom (.const (.n 147) (word 0 0 0)),
      .atom (.const (.n 148) (word 0 0 0)), .atom (.const (.n 149) (word 0 0 0)),
      .atom (.const (.n 150) (word 0 0 0)),
      keccakA ([.n 142, .n 143, .n 144, .n 145, .n 147, .n 148, .n 149, .n 150] ++
        (List.range 5).map fun k ↦ .n (137 + k)) (lyOuts 151)],
    challengeT (.n 151) (.n 152) 164,
    [.atom (.load (.n 171) (.n 15) 5), .atom (.load (.n 172) (.n 15) 6),
      .atom (.load (.n 173) (.n 15) 7), .atom (.load (.n 174) (.n 15) 8),
      .atom (.mul (.n 175) (.n 170) (.n 174)), .atom (.add (.n 176) (.n 173) (.n 175)),
      .atom (.mul (.n 177) (.n 170) (.n 176)), .atom (.add (.n 178) (.n 172) (.n 177)),
      .atom (.load (.n 179) (.n 15) 9), .atom (.const (.n 180) (word 1099511627776 0 0)),
      .atom (.mul (.n 181) (.n 179) (.n 180))],
    ((List.range 4).map odEvT).flatten,
    [keccakA ([.n 189, .n 191, .n 200, .n 202, .n 211, .n 213, .n 222, .n 224] ++ lyCap 151)
      (lyOuts 226)],
    odEvT 4,
    odEvT 5,
    [.atom (.mul (.n 261) (.n 249) (.n 260)), .atom (.const (.n 262) (word 0 0 0)),
      .atom (.mul (.n 263) (.n 170) (.n 262)), .atom (.add (.n 264) (.n 261) (.n 263)),
      .atom (.mul (.n 265) (.n 214) (.n 225)), .atom (.mul (.n 266) (.n 170) (.n 264)),
      .atom (.add (.n 267) (.n 265) (.n 266)), .atom (.mul (.n 268) (.n 192) (.n 203)),
      .atom (.mul (.n 269) (.n 170) (.n 267)), .atom (.add (.n 270) (.n 268) (.n 269)),
      .atom (.assertEq (.n 178) (.n 270)),
      keccakA ([.n 246, .n 248, .n 257, .n 259, .n 147, .n 148, .n 149, .n 150] ++ lyCap 226)
        (lyOuts 271)],
    challengeT (.n 271) (.n 272) 284,
    [.atom (.load (.n 290) (.n 181) 0)],
    (List.range 5).map (fun k ↦ .atom (.load (.n (279 + k)) (.n 15) (17 + k))),
    ((List.range 4).map fun k ↦ [.atom (.const (.n (291 + k)) (word 0 0 0)),
      .atom (.load (.n (291 + k)) (.n 15) (30 + k))]).flatten,
    [.atom (.const (.n 295) (word 64 0 0)), .atom (.mul (.n 296) (.n 171) (.n 295)),
      .atom (.load (.n 296) (.n 15) 22)],
    odVal 0,
    odVal 1,
    odVal 2,
    [.atom (.load (.n 181) (.n 15) 26), .atom (.const (.n 306) (word 2 0 0)),
      .atom (.load (.n 306) (.n 15) 27), .atom (.const (.n 307) (word 1 0 0)),
      .atom (.load (.n 307) (.n 15) 28), .atom (.const (.n 308) (word 1 0 0)),
      .atom (.load (.n 308) (.n 15) 29)]]

theorem odBody_noRet : Stmt.noRetList odBody = true := by decide +kernel

/-- Child `i`'s read's first statement in `odBody`. -/
def odPos (i : ℕ) : ℕ := if i < 4 then 34 + 10 * i else 35 + 10 * i

theorem odEvs_check : ∀ i < 6,
    tbStmtsEqb (odEvT i) ((odBody.drop (odPos i)).take (odEvT i).length) = true := by
  decide +kernel

/-- Absorbing at a full queue: one permutation, then the scalars waiting. -/
theorem tb_absorbAll_full' (s : Fs) (hs : s.pend.length = 4) (xs : List E) (h1 : 0 < xs.length)
    (h4 : xs.length ≤ 4) (t : ℕ) : s.absorbAll xs t = ⟨capOf s.perm, xs.map (·, t)⟩ := by
  match xs, h1 with
  | x :: rest, _ =>
    simp only [Fs.absorbAll, List.foldl_cons]
    have e1 : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by
      simp [Fs.absorb, hs, rateScalars]
    rw [e1]
    have := absorbAll_short ⟨capOf s.perm, [(x, t)]⟩ rest t (by simp at h4 ⊢; omega)
    simp only [Fs.absorbAll] at this
    rw [this]
    simp

/-- `fs_pack`'s cells, once the first is canonical. -/
theorem tb_pack_cells {σ : Val} {b : ℕ} (hp : FsPackOk σ (.n b) (b + 1) dsObserve)
    (hc : IsCanonical128 (σ (.n (b + 7)))) :
    σ (.n (b + 7)) = (Keccak.scalarCells (σ (.n b)) dsObserve).1 ∧
      σ (.n (b + 9)) = (Keccak.scalarCells (σ (.n b)) dsObserve).2 := by
  have := fsPackT_cells hp (by rw [show b + 1 + 6 = b + 7 by omega]; exact hc)
  rw [show b + 1 + 6 = b + 7 by omega, show b + 1 + 8 = b + 9 by omega] at this
  exact Prod.ext_iff.mp this

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem od_ev {i : ℕ} (h : Stmt.HoldsList C rd σ (odEvT i) True kret) :
    LoadHolds rd (σ (.n 171)) i (σ (.n (odEv i))) ∧
      FsPackOk σ (.n (odEv i)) (odEv i + 1) dsObserve ∧ σ (.n (odEv i + 10)) = σ (.n (odEv i)) := by
  unfold odEvT at h
  rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT]; rfl), holds_fsNextT] at h
  obtain ⟨⟨⟨hl, hp⟩, -⟩, hc⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hc
  exact ⟨hl, hp, hc⟩

/-- **The binary layer** from the root slot is one step of one level, to the slot of `L = 1`. -/
theorem od_step (h : Stmt.HoldsList C rd σ odBody True kret) {s : Fs} {cur : E} {st : GkrState}
    {row pos half parity : E} (hslot : GkSlot rd (σ (.n 15)) 0 s cur st row pos half parity) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs), RunsTo (gkrStep 1 st) s xs st' s' ∧
      TbReadsAt rd cur xs ∧ s'.pend = [] ∧
      GkSlot rd (σ (.n 15)) 1 s' (cur * gen ^ xs.length) st' (row * gen ^ 40) gen 1 1 := by
  have hnr := odBody_noRet
  obtain ⟨hcl, hcap, hpl, hrate, hcur, hvl, hval, hrow, hptl, -, -, -, -⟩ := hslot
  simp only [Nat.mul_zero, Nat.zero_add] at hcap hrate hcur hval hrow
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  -- the combiner
  have hcapL := tb_holds_slice hnr h 0 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (137 + k)) (.n 15) k)) (by decide +kernel)
  have hpendL := tb_holds_slice hnr h 5 ((List.range 4).map fun k ↦
    Stmt.atom (.load (.n (142 + k)) (.n 15) (13 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcapL hpendL
  simp only [Atom.Holds] at hcapL hpendL
  have ecap : ∀ k < 5, σ (.n (137 + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique (hcapL k hk) (hcap k hk)
  have c138 := a 10 (.const (.n 147) (word 0 0 0)) (by decide +kernel)
  have c139 := a 11 (.const (.n 148) (word 0 0 0)) (by decide +kernel)
  have c140 := a 12 (.const (.n 149) (word 0 0 0)) (by decide +kernel)
  have c141 := a 13 (.const (.n 150) (word 0 0 0)) (by decide +kernel)
  have k1 := a 14 (.keccak ([.n 142, .n 143, .n 144, .n 145, .n 147, .n 148, .n 149, .n 150] ++
      (List.range 5).map fun k ↦ .n (137 + k)) (lyOuts 151) false false) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c138 c139 c140 c141
  obtain ⟨hcanI, hP1, hC1⟩ := ly_keccak k1
  have epend : ∀ k < 4, σ (.n (142 + k)) = (rateOf s.pend).getD k 0 := by
    refine hrate (fun k ↦ σ (.n (142 + k))) (fun k hk => hpendL k hk) (fun k hk => hcanI _ ?_)
    simp only [List.map_append, List.mem_append, List.map_cons, List.mem_cons, List.map_nil]
    left
    interval_cases k <;> simp
  have hrl : (rateOf s.pend).length = 8 := by simp [rateOf]
  have hins : (([.n 142, .n 143, .n 144, .n 145, .n 147, .n 148, .n 149, .n 150] ++
      (List.range 5).map fun k ↦ V.n (137 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [tb_eq_map_getD hrl, tb_eq_map_getD hcl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq, and_true]
    refine ⟨epend 0 (by omega), epend 1 (by omega), epend 2 (by omega), epend 3 (by omega),
      ?_, ?_, ?_, ?_, ecap 0 (by omega), ecap 1 (by omega), ecap 2 (by omega), ecap 3 (by omega),
      ecap 4 (by omega)⟩
    · rw [c138, rateOf_getD_four hpl (by omega) (by omega)]
    · rw [c139, rateOf_getD_four hpl (by omega) (by omega)]
    · rw [c140, rateOf_getD_four hpl (by omega) (by omega)]
    · rw [c141, rateOf_getD_four hpl (by omega) (by omega)]
  rw [hins] at hP1 hC1
  have hch := tb_holds_slice hnr h 15 (challengeT (.n 151) (.n 152) 164) (by decide +kernel)
  rw [holds_challengeT] at hch
  have e161 : σ (.n 170) = s.squeeze.1 :=
    challengeT_value hch.1 (hP1 0 (by omega)) (hP1 1 (by omega))
  -- the claim, the row
  have l162 := a 23 (.load (.n 171) (.n 15) 5) (by decide +kernel)
  have l163 := a 24 (.load (.n 172) (.n 15) 6) (by decide +kernel)
  have l164 := a 25 (.load (.n 173) (.n 15) 7) (by decide +kernel)
  have l165 := a 26 (.load (.n 174) (.n 15) 8) (by decide +kernel)
  have m166 := a 27 (.mul (.n 175) (.n 170) (.n 174)) (by decide +kernel)
  have a167 := a 28 (.add (.n 176) (.n 173) (.n 175)) (by decide +kernel)
  have m168 := a 29 (.mul (.n 177) (.n 170) (.n 176)) (by decide +kernel)
  have a169 := a 30 (.add (.n 178) (.n 172) (.n 177)) (by decide +kernel)
  have l170 := a 31 (.load (.n 179) (.n 15) 9) (by decide +kernel)
  have c171 := a 32 (.const (.n 180) (word 1099511627776 0 0)) (by decide +kernel)
  have m172 := a 33 (.mul (.n 181) (.n 179) (.n 180)) (by decide +kernel)
  simp only [Atom.Holds] at l162 l163 l164 l165 m166 a167 m168 a169 l170 c171 m172
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)] at c171
  have e162 := tb_loadHolds_unique l162 hcur
  have e163 := tb_loadHolds_unique l163 (hval 0 (by omega))
  have e164 := tb_loadHolds_unique l164 (hval 1 (by omega))
  have e165 := tb_loadHolds_unique l165 (hval 2 (by omega))
  have e170 := tb_loadHolds_unique l170 hrow
  rw [c171, e170] at m172
  -- the children
  have EV : ∀ i < 6, _ := fun i hi => od_ev (tb_holds_slice hnr h (odPos i) (odEvT i)
    (odEvs_check i hi))
  rw [e162] at EV
  have k2 := a 74 (.keccak ([.n 189, .n 191, .n 200, .n 202, .n 211, .n 213, .n 222, .n 224] ++
    lyCap 151) (lyOuts 226) false false) (by decide +kernel)
  obtain ⟨hcan2, hP2, hC2⟩ := ly_keccak k2
  have k3 := a 106 (.keccak ([.n 246, .n 248, .n 257, .n 259, .n 147, .n 148, .n 149, .n 150] ++
    lyCap 226) (lyOuts 271) false false) (by decide +kernel)
  obtain ⟨hcan3, hP3, hC3⟩ := ly_keccak k3
  have cl : ∀ i < 6, σ (.n (odEv i + 7)) = (Keccak.scalarCells (σ (.n (odEv i))) dsObserve).1 ∧
      σ (.n (odEv i + 9)) = (Keccak.scalarCells (σ (.n (odEv i))) dsObserve).2 := by
    intro i hi
    apply tb_pack_cells (EV i hi).2.1
    rcases (by omega : i < 4 ∨ 4 ≤ i) with hi4 | hi4
    · apply hcan2
      interval_cases i <;> simp [odEv]
    · apply hcan3
      interval_cases i <;> simp [odEv]
  have e180 : σ (.n 189) = (Keccak.scalarCells (σ (.n 182)) dsObserve).1 := (cl 0 (by omega)).1
  have e182 : σ (.n 191) = (Keccak.scalarCells (σ (.n 182)) dsObserve).2 := (cl 0 (by omega)).2
  have e191 : σ (.n 200) = (Keccak.scalarCells (σ (.n 193)) dsObserve).1 := (cl 1 (by omega)).1
  have e193 : σ (.n 202) = (Keccak.scalarCells (σ (.n 193)) dsObserve).2 := (cl 1 (by omega)).2
  have e202 : σ (.n 211) = (Keccak.scalarCells (σ (.n 204)) dsObserve).1 := (cl 2 (by omega)).1
  have e204 : σ (.n 213) = (Keccak.scalarCells (σ (.n 204)) dsObserve).2 := (cl 2 (by omega)).2
  have e213 : σ (.n 222) = (Keccak.scalarCells (σ (.n 215)) dsObserve).1 := (cl 3 (by omega)).1
  have e215 : σ (.n 224) = (Keccak.scalarCells (σ (.n 215)) dsObserve).2 := (cl 3 (by omega)).2
  have e237 : σ (.n 246) = (Keccak.scalarCells (σ (.n 239)) dsObserve).1 := (cl 4 (by omega)).1
  have e239 : σ (.n 248) = (Keccak.scalarCells (σ (.n 239)) dsObserve).2 := (cl 4 (by omega)).2
  have e248 : σ (.n 257) = (Keccak.scalarCells (σ (.n 250)) dsObserve).1 := (cl 5 (by omega)).1
  have e250 : σ (.n 259) = (Keccak.scalarCells (σ (.n 250)) dsObserve).2 := (cl 5 (by omega)).2
  have q183 : σ (.n 192) = σ (.n 182) := (EV 0 (by omega)).2.2
  have q194 : σ (.n 203) = σ (.n 193) := (EV 1 (by omega)).2.2
  have q205 : σ (.n 214) = σ (.n 204) := (EV 2 (by omega)).2.2
  have q216 : σ (.n 225) = σ (.n 215) := (EV 3 (by omega)).2.2
  have q240 : σ (.n 249) = σ (.n 239) := (EV 4 (by omega)).2.2
  have q251 : σ (.n 260) = σ (.n 250) := (EV 5 (by omega)).2.2
  -- the sponge
  set w0 := σ (.n 182)
  set w1 := σ (.n 193)
  set w2 := σ (.n 204)
  set w3 := σ (.n 215)
  set w4 := σ (.n 239)
  set w5 := σ (.n 250)
  have hins2 : (([.n 189, .n 191, .n 200, .n 202, .n 211, .n 213, .n 222, .n 224] ++ lyCap 151 :
      List V).map σ) = rateOf [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve), (w3, dsObserve)] ++
      capOf (permOf (rateOf s.pend ++ s.cap)) := by
    rw [List.map_append, hC1, rateOf_eq_cells [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
      (w3, dsObserve)] (by simp)]
    simp only [List.map_cons, List.map_nil, e180, e182, e191, e193, e202, e204, e213, e215,
      pendCells, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, List.append_nil]
    rfl
  rw [hins2] at hP2 hC2
  have hins3 : (([.n 246, .n 248, .n 257, .n 259, .n 147, .n 148, .n 149, .n 150] ++ lyCap 226 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ (lyCap 226).map σ := by
    rw [List.map_append, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, e237, e239, e248, e250, c138, c139, c140, c141,
      pendCells, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, List.append_nil]
    rfl
  rw [hins3] at hP3 hC3
  have hch2 := tb_holds_slice hnr h 107 (challengeT (.n 271) (.n 272) 284) (by decide +kernel)
  rw [holds_challengeT] at hch2
  have e281 := challengeT_value hch2.1 (hP3 0 (by omega)) (hP3 1 (by omega))
  -- the run
  obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
    match st.values, hvl with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  have hsc : RunsTo (sumcheck (polyEval st.values s.squeeze.1) (2 ^ 1 + 1) (st.point.map some))
      s.squeeze.2 [] ([], polyEval st.values s.squeeze.1) s.squeeze.2 := by
    rw [List.eq_nil_of_length_eq_zero hptl]
    exact runsTo_sumcheck_nil _ _ _
  have hcheck : polyEval st.values s.squeeze.1 =
      polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]] s.squeeze.1 := by
    have m252 := a 95 (.mul (.n 261) (.n 249) (.n 260)) (by decide +kernel)
    have c253 := a 96 (.const (.n 262) (word 0 0 0)) (by decide +kernel)
    have m254 := a 97 (.mul (.n 263) (.n 170) (.n 262)) (by decide +kernel)
    have a255 := a 98 (.add (.n 264) (.n 261) (.n 263)) (by decide +kernel)
    have m256 := a 99 (.mul (.n 265) (.n 214) (.n 225)) (by decide +kernel)
    have m257 := a 100 (.mul (.n 266) (.n 170) (.n 264)) (by decide +kernel)
    have a258 := a 101 (.add (.n 267) (.n 265) (.n 266)) (by decide +kernel)
    have m259 := a 102 (.mul (.n 268) (.n 192) (.n 203)) (by decide +kernel)
    have m260 := a 103 (.mul (.n 269) (.n 170) (.n 267)) (by decide +kernel)
    have a261 := a 104 (.add (.n 270) (.n 268) (.n 269)) (by decide +kernel)
    have q := a 105 (.assertEq (.n 178) (.n 270)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_zero] at m252 c253 m254 a255 m256 m257 a258 m259 m260 a261 q
    have q' := e_add_eq_zero_iff.mp q
    rw [a169, m168, a167, m166, e163, e164, e165, a261, m260, a258, m257, a255, m254, c253,
      m252, m256, m259, q183, q194, q205, q216, q240, q251, hv3, e161] at q'
    rw [hv3]
    simp only [List.getD_cons_zero, List.getD_cons_succ] at q'
    simp only [polyEval, prodE, List.foldr, List.foldl]
    linear_combination q'
  have hstep := gkrStep_run (step := 1) (ch0 := [w0, w1]) (ch1 := [w2, w3]) (ch2 := [w4, w5]) hsc
    rfl rfl rfl hcheck
  have hA0 : s.squeeze.2.absorbAll [w0, w1] dsObserve =
      ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ := by
    rw [absorbAll_short _ _ _ (by simp [Fs.squeeze])]
    rfl
  have hA1 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll [w2, w3]
      dsObserve = ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
        (w3, dsObserve)]⟩ := by
    rw [absorbAll_short _ _ _ (by simp)]
    rfl
  have hA2 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
      (w3, dsObserve)]⟩ : Fs).absorbAll [w4, w5] dsObserve =
      ⟨(lyCap 226).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
    rw [tb_absorbAll_full' _ (by simp) _ (by simp) (by simp), hC2]
    rfl
  rw [hA0, hA1, hA2] at hstep
  have hsq1 : ((⟨(lyCap 226).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).1 =
      [σ (.n 290)] := by rw [e281]; rfl
  have hsq2 : ((⟨(lyCap 226).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).2 =
      ⟨(lyCap 271).map σ, []⟩ := by rw [hC3]; rfl
  rw [hsq1, hsq2] at hstep
  refine ⟨_, _, _, hstep, ?_, rfl, ?_⟩
  · intro k hk
    simp only [List.nil_append, List.cons_append, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact (EV 0 (by omega)).1
    · exact (EV 1 (by omega)).1
    · exact (EV 2 (by omega)).1
    · exact (EV 3 (by omega)).1
    · exact (EV 4 (by omega)).1
    · exact (EV 5 (by omega)).1
  have hcs := tb_holds_slice hnr h 116 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (279 + k)) (.n 15) (17 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  simp only [Atom.Holds] at hcs
  have hzs := tb_holds_slice hnr h 121 ((List.range 4).map fun k ↦
    [Stmt.atom (.const (.n (291 + k)) (word 0 0 0)),
      .atom (.load (.n (291 + k)) (.n 15) (30 + k))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hzs
  have l281 := a 115 (.load (.n 290) (.n 181) 0) (by decide +kernel)
  have c286 := a 129 (.const (.n 295) (word 64 0 0)) (by decide +kernel)
  have m287 := a 130 (.mul (.n 296) (.n 171) (.n 295)) (by decide +kernel)
  have l287 := a 131 (.load (.n 296) (.n 15) 22) (by decide +kernel)
  have l172 := a 144 (.load (.n 181) (.n 15) 26) (by decide +kernel)
  have c297 := a 145 (.const (.n 306) (word 2 0 0)) (by decide +kernel)
  have l297 := a 146 (.load (.n 306) (.n 15) 27) (by decide +kernel)
  have c298 := a 147 (.const (.n 307) (word 1 0 0)) (by decide +kernel)
  have l298 := a 148 (.load (.n 307) (.n 15) 28) (by decide +kernel)
  have c299 := a 149 (.const (.n 308) (word 1 0 0)) (by decide +kernel)
  have l299 := a 150 (.load (.n 308) (.n 15) 29) (by decide +kernel)
  simp only [Atom.Holds] at l281 c286 m287 l287 l172 c297 l297 c298 l298 c299 l299
  rw [tb_word_gen] at c297
  rw [tb_word_one] at c298
  rw [tb_word_one] at c299
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, tb_word_two_pow (by norm_num)] at c286
  have VAL : ∀ t < 3, LoadHolds rd (σ (.n 15)) (23 + t)
      (σ (.n (odEv (2 * t) + 10)) + σ (.n 290) *
        (σ (.n (odEv (2 * t) + 10)) + σ (.n (odEv (2 * t + 1) + 10)))) := by
    intro t ht
    have hv := tb_holds_slice hnr h (132 + 4 * t) (odVal t) (by interval_cases t <;> decide +kernel)
    simp only [odVal, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hv
    obtain ⟨e0, e1, e2, l⟩ := hv
    rw [e2, e1, e0] at l
    exact l
  refine ⟨by simp [lyCap], fun k hk => ?_, by simp, fun c hc _ k hk => ?_, ?_, by simp,
    fun t ht => ?_, ?_, by simp, ?_, ?_, ?_, ?_⟩
  · have hg : ((lyCap 271).map σ).getD k 0 = σ (.n (279 + k)) := by
      simp [lyCap, List.getD_eq_getElem?_getD, hk]
    rw [hg, show 17 * 1 + k = 17 + k by ring]
    exact hcs k hk
  · rw [tb_rateOf_nil_getD]
    have hz := hzs k hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, tb_word_zero] at hz
    rw [hz.1] at hz
    exact tb_loadHolds_unique (hc k hk) (by rw [show 17 * 1 + 13 + k = 30 + k by ring]; exact hz.2)
  · rw [m287, c286, e162] at l287
    simpa using l287
  · rw [show 17 * 1 + 6 + t = 23 + t by ring]
    have := VAL t ht
    interval_cases t
    · rw [show σ (.n (odEv (2 * 0) + 10)) = w0 from q183,
        show σ (.n (odEv (2 * 0 + 1) + 10)) = w1 from q194] at this
      convert this using 1
      simp [multilinearEval, foldPairs]
      ring
    · rw [show σ (.n (odEv (2 * 1) + 10)) = w2 from q205,
        show σ (.n (odEv (2 * 1 + 1) + 10)) = w3 from q216] at this
      convert this using 1
      simp [multilinearEval, foldPairs]
      ring
    · rw [show σ (.n (odEv (2 * 2) + 10)) = w4 from q240,
        show σ (.n (odEv (2 * 2 + 1) + 10)) = w5 from q251] at this
      convert this using 1
      simp [multilinearEval, foldPairs]
      ring
  · rw [m172] at l172
    exact l172
  · rw [m172] at l281
    simpa [tbReadsAt_singleton] using l281
  · rw [c297] at l297
    exact l297
  · rw [c298] at l298
    exact l298
  · rw [c299] at l299
    exact l299

end Sem

end
end LeanVM.Guest.B1.Tables
