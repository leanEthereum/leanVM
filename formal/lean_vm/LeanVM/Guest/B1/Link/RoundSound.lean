/-
  LeanVM.Guest.B1.Link.RoundSound

  `link_round`'s template is one plain sum-check round on the carried sponge.
-/

module

public import LeanVM.Guest.B1.Link.Rounds
public import LeanVM.Guest.B1.Link.RoundRun
public import LeanVM.Guest.B1.Common.Vc
public import LeanVM.Guest.B1.Bits.Grind

/-!
# `link_round`, sound

`lrRound_sound`: wherever the template's atoms hold, its `nt + 1` words (and the grind's nonce)
lie at the cursor, the outputs are `Fs.grindSqueeze` of the carried capacity after absorbing
them, the grind passes, and the claim is the round polynomial at the challenge.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Permutation outputs -/

/-- The cells a permutation writes, one by one. -/
theorem outs_cells_of {σ : Val} {F : ℕ} {S : KeccakState}
    (h : cells13 (((List.range 13).map fun j ↦ V.n (F + j)).map σ) = cellsOfState S false) :
    ∀ j (hj : j < 13), σ (.n (F + j)) = cellsOfState S false ⟨j, hj⟩ := fun j hj ↦ by
  have := congrFun h ⟨j, hj⟩
  simpa [cells13, List.getD_eq_getElem?_getD, hj] using this

theorem capOf_outs {σ : Val} {F : ℕ} {S : KeccakState}
    (h : ∀ j (hj : j < 13), σ (.n (F + j)) = cellsOfState S false ⟨j, hj⟩) :
    capOf S = ((List.range 5).map fun j ↦ F + 8 + j).map fun v ↦ σ (.n v) := by
  simp only [capOf, List.map_map]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, Function.comp]
  rw [show F + 8 + 0 = F + 8 by rfl, h 8 (by norm_num), h (8 + 1) (by norm_num), h (8 + 2) (by norm_num),
    h (8 + 3) (by norm_num), h (8 + 4) (by norm_num)]
  rfl

/-! ## The scalars and the sponge -/

section Round

variable {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ}

theorem mem_lrRound_step {i : ℕ} (hi : i ≤ nt) {a : Atom} (ha : Stmt.atom a ∈ lrStep o cap cur i) :
    Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad := by
  unfold lrRound
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩, ha⟩))))))

/-- Scalar `i`'s word. -/
def lrX (σ : Val) (o i : ℕ) : E := σ (.n (o + lrSb i))

variable (hA : ∀ a, Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad → a.Holds rd σ)
include hA

theorem lr_scalar {i : ℕ} (hi : i ≤ nt) :
    LoadHolds rd (σ (.n cur)) i (lrX σ o i) ∧ σ (.n (o + lrSb i + 1)) = lrX σ o i ∧
      σ (.n (o + lrSb i + 2)) = word 0 1 ∧ (i ≠ 0 → σ (.n (o + lrSb i + 3)) = lrX σ o i) := by
  have mem : ∀ a, Stmt.atom a ∈ lrScalar o cur i → a.Holds rd σ := fun a ha ↦
    hA a (mem_lrRound_step hi (List.mem_append_right _ ha))
  by_cases h0 : i = 0
  · subst h0
    have a0 := mem (.load (.n (o + lrSb 0)) (.n cur) 0) (by simp [lrScalar])
    have a1 := mem (.copy (.n (o + lrSb 0 + 1)) (.n (o + lrSb 0))) (by simp [lrScalar])
    have a2 := mem (.const (.n (o + lrSb 0 + 2)) (word 0 1)) (by simp [lrScalar])
    exact ⟨a0, a1, a2, fun h ↦ absurd rfl h⟩
  · have a0 := mem (.load (.n (o + lrSb i)) (.n cur) i) (by simp [lrScalar, h0])
    have a1 := mem (.copy (.n (o + lrSb i + 1)) (.n (o + lrSb i))) (by simp [lrScalar, h0])
    have a2 := mem (.const (.n (o + lrSb i + 2)) (word 0 1)) (by simp [lrScalar, h0])
    have a3 := mem (.copy (.n (o + lrSb i + 3)) (.n (o + lrSb i))) (by simp [lrScalar, h0])
    exact ⟨a0, a1, a2, fun _ ↦ a3⟩

/-- The waiting scalars after scalar `i`: its group of four. -/
def lrGrp (σ : Val) (o i : ℕ) : List (E × ℕ) :=
  (List.range (i % 4 + 1)).map fun j ↦ (lrX σ o (4 * (i / 4) + j), dsObserve)

theorem lr_cells {j k : ℕ} (hjk : j + k ≤ nt + 1) :
    (lrCells o j k).map σ = pendCells ((List.range k).map fun i ↦ (lrX σ o (j + i), dsObserve)) := by
  simp only [lrCells, pendCells, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  obtain ⟨-, h1, h2, -⟩ := lr_scalar hA (i := j + i) (by omega)
  simp only [List.map_cons, List.map_nil, h1, h2, scalarCells_eq, word_dsObserve]

/-- **The sponge after scalar `i`**: the capacity values `lrCap` and the group waiting. -/
theorem lr_sponge :
    ∀ i ≤ nt, (⟨cap.map fun v ↦ σ (.n v), []⟩ : Fs).absorbAll
        (((List.range (nt + 1)).map (lrX σ o)).take (i + 1)) dsObserve =
      ⟨(lrCap o cap i).map fun v ↦ σ (.n v), lrGrp σ o i⟩ := by
  intro i hi
  induction i with
  | zero =>
    rw [absorbAll_short _ _ _ (by simp)]
    simp only [lrCap, show (0 : ℕ) < 4 by norm_num, ↓reduceIte, lrGrp, Nat.zero_mod, Nat.zero_div,
      Nat.zero_add, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, List.nil_append, Fs.mk.injEq,
      true_and]
    rw [List.range_succ_eq_map]
    rfl
  | succ i ih =>
    have ih := ih (by omega)
    have ht : ((List.range (nt + 1)).map (lrX σ o)).take (i + 1 + 1) =
        ((List.range (nt + 1)).map (lrX σ o)).take (i + 1) ++ [lrX σ o (i + 1)] := by
      rw [List.take_add_one, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    have hab : ∀ (s : Fs) (l : List E) (x : E), s.absorbAll (l ++ [x]) dsObserve =
        (s.absorbAll l dsObserve).absorb x dsObserve := fun s l x ↦ by
      simp [Fs.absorbAll, List.foldl_append]
    rw [ht, hab, ih]
    by_cases h4 : (i + 1) % 4 = 0
    · -- a permutation, then the scalar alone
      have hl : (lrGrp σ o i).length = rateScalars := by simp [lrGrp, rateScalars]; omega
      have hm : i + 1 ≠ 0 ∧ (i + 1) % 4 = 0 := ⟨by omega, h4⟩
      have hp := hA _ (mem_lrRound_step (bits := bits) (cl := cl) (tabs := tabs) (pad := pad)
        (show i + 1 ≤ nt by omega) (a := .keccak (lrCells o (4 * ((i + 1) / 4) - 4) 4 ++
          (lrCap o cap (4 * ((i + 1) / 4) - 1)).map V.n)
          ((List.range 13).map fun j ↦ .n (lrPermOut o ((i + 1) / 4) + j)) false false)
        (by simp [lrStep, hm, lrPerm]))
      have e1 : 4 * ((i + 1) / 4) - 4 = 4 * (i / 4) := by omega
      have e2 : 4 * ((i + 1) / 4) - 1 = i := by omega
      rw [e1, e2] at hp
      have hc := keccakA_fs (s := ⟨(lrCap o cap i).map fun v ↦ σ (.n v), lrGrp σ o i⟩) hp
        (by simp [lrGrp]; omega) (by
          rw [List.map_append, lr_cells hA (by omega), List.map_map]
          simp only [lrGrp, show i % 4 + 1 = 4 by omega, List.length_map, List.length_range,
            Nat.mul_comm 2 4, Nat.sub_self, List.replicate_zero, List.append_nil]
          rfl)
      have hcap' := capOf_outs (outs_cells_of hc)
      simp only [Fs.absorb, hl, ↓reduceIte, Fs.perm]
      rw [show permOf (rateOf (lrGrp σ o i) ++ (lrCap o cap i).map fun v ↦ σ (.n v)) =
        Fs.perm ⟨(lrCap o cap i).map fun v ↦ σ (.n v), lrGrp σ o i⟩ from rfl, hcap']
      simp only [lrCap, show ¬ i + 1 < 4 by omega, ↓reduceIte, lrGrp, h4, Nat.zero_add,
        List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.map_map,
        show 4 * ((i + 1) / 4) = i + 1 by omega]
    · -- appended to the group
      have hl : (lrGrp σ o i).length ≠ rateScalars := by simp [lrGrp, rateScalars]; omega
      simp only [Fs.absorb, hl, ↓reduceIte, Fs.mk.injEq]
      refine ⟨?_, ?_⟩
      · simp only [lrCap, show (i + 1) / 4 = i / 4 by omega]
        split_ifs <;> first | rfl | omega
      · simp only [lrGrp, show (i + 1) % 4 = i % 4 + 1 by omega, show (i + 1) / 4 = i / 4 by omega,
          List.range_succ (n := i % 4 + 1), List.map_append, List.map_singleton,
          show 4 * (i / 4) + (i % 4 + 1) = i + 1 by omega]

end Round

/-! ## The grind's atoms -/

theorem allAtoms_renameList (r : V → V) : ∀ {ss : List Stmt}, AllAtoms ss → AllAtoms (Stmt.renameList r ss)
  | [], _ => by simp [Stmt.renameList, AllAtoms]
  | s :: ss, h => by
    obtain ⟨a, rfl⟩ := h s (by simp)
    exact allAtoms_cons (allAtoms_renameList r (ss := ss) fun t ht ↦ h t (by simp [ht]))

theorem gcInlineT_atoms (o : ℕ) (w tabs : V) : AllAtoms (gcInlineT 1 o w tabs) :=
  allAtoms_renameList _ (allAtoms_of_isAtomsB (by decide +kernel))

/-- `grind_check` at one bit inlined is sound, from the windows table (`Bits/Grind`'s
`gc_sound`, whose deployed list does not hold the link's one bit). -/
def GcSound1 (rd : Reader) : Prop :=
  ∀ {σ : Val} {o : ℕ} {w tabs : V}, WinTabs rd (σ tabs) →
    (∀ a, Stmt.atom a ∈ gcInlineT 1 o w tabs → a.Holds rd σ) → ((σ w).limb 0).lane.toNat % 2 ^ 1 = 0

theorem gcSound1_image {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ) : GcSound1 L.read := by
  intro σ o w tabs ht hA
  have h := (holdsList_atoms (C := fun _ _ _ ↦ True) (gcInlineT_atoms o w tabs) True (fun _ ↦ True)).mpr
    ⟨hA, trivial⟩
  obtain ⟨hh, hi, htl, -⟩ := (holds_gcInlineT 1 o w tabs True _).mp h
  exact gc_sound hκ hκ11 L (by decide) ht hh hi htl

/-! ## The round -/

/-- The polynomial at `y` of `[c0, c1, tail…]`, the guest's way: `((H(tail)·y + c1)·y + c0)`. -/
theorem polyEval_cons_cons (c0 c1 y : E) (tail : List E) :
    polyEval (c0 :: c1 :: tail) y = (polyEval tail y * y + c1) * y + c0 := rfl

theorem polyEval_cons (c y : E) (tail : List E) : polyEval (c :: tail) y = polyEval tail y * y + c := rfl

section Round2

variable {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ}

theorem mem_lrRound_pre {a : Atom} (ha : Stmt.atom a ∈ (if bits = 0 then [] else
      (if nt % 4 + 1 = 4 then [lrPerm o cap ((nt + 1) / 4)] else []) ++
      [.atom (.load (.n (lrE o nt)) (.n cur) (nt + 1)), .atom (.copy (.n (lrE o nt + 1)) (.n (lrE o nt))),
        .atom (.const (.n (lrE o nt + 2)) (word 0 4))]) ++
      (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.1) :
    Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad := by
  unfold lrRound
  simp only [List.mem_append] at ha ⊢
  rcases ha with h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem mem_lrRound_perm :
    Stmt.atom (.keccak (lrCells o (nt + 1 - (nt % 4 + 1)) (nt % 4 + 1) ++
      (if bits = 0 then [] else [.n (lrE o nt + 1), .n (lrE o nt + 2)]) ++
      (lrPadCells (lrP o nt bits) (lrK nt bits) pad).1 ++ (lrCap o cap nt).map V.n)
      ((List.range 13).map fun j ↦ .n (lrF o nt bits pad + j)) false false) ∈
      lrRound nt bits o cap cur cl tabs pad := by
  unfold lrRound lrF
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_singleton.mpr rfl))))

theorem mem_lrRound_grind (hb : bits ≠ 0) {a : Atom}
    (ha : Stmt.atom a ∈ gcInlineT bits (lrF o nt bits pad + 13) (.n (lrF o nt bits pad + 1)) (.n tabs)) :
    Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad := by
  unfold lrRound
  simp only [List.mem_append, hb, ↓reduceIte]
  exact Or.inl (Or.inl (Or.inr ha))

theorem mem_lrRound_chain {j' : ℕ} (hj : j' < nt - 1) {a : Atom}
    (ha : a ∈ [Atom.mul (.n (lrC o nt bits pad + 3 * j')) (.n (lrAcc o nt (lrC o nt bits pad) j'))
        (.n (lrF o nt bits pad)),
      .add (.n (lrC o nt bits pad + 3 * j' + 1)) (.n (lrC o nt bits pad + 3 * j'))
        (.n (lrTail o (nt - 1 - (j' + 1)))),
      .add (.n (lrC o nt bits pad + 3 * j' + 2)) (.n (lrTs o nt (lrC o nt bits pad) j'))
        (.n (lrTail o (nt - 1 - (j' + 1))))]) :
    Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad := by
  unfold lrRound
  simp only [List.mem_append]
  refine Or.inl (Or.inr (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j', List.mem_range.mpr hj, rfl⟩, ?_⟩))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  simp only [Nat.add_sub_cancel]
  rcases ha with rfl | rfl | rfl <;> simp [lrF]

theorem mem_lrRound_last {a : Atom}
    (ha : a ∈ [Atom.mul (.n (lrD o nt bits pad)) (.n (lrAcc o nt (lrC o nt bits pad) (nt - 1)))
        (.n (lrF o nt bits pad)),
      .add (.n (lrD o nt bits pad + 1)) (.n cl) (.n (lrTs o nt (lrC o nt bits pad) (nt - 1))),
      .add (.n (lrD o nt bits pad + 2)) (.n (lrD o nt bits pad)) (.n (lrD o nt bits pad + 1)),
      .copy (.n (lrD o nt bits pad + 3)) (.n (lrF o nt bits pad)),
      .const (.n (lrD o nt bits pad + 4)) (word (2 ^ (nt + 1 + if bits = 0 then 0 else 1)) 0),
      .mul (.n (lrD o nt bits pad + 5)) (.n cur) (.n (lrD o nt bits pad + 4)),
      .copy (.n (lrD o nt bits pad + 6)) (.n (lrD o nt bits pad + 5)),
      .mul (.n (lrD o nt bits pad + 7)) (.n (lrD o nt bits pad + 2)) (.n (lrF o nt bits pad)),
      .add (.n (lrD o nt bits pad + 8)) (.n (lrD o nt bits pad + 7)) (.n o)]) :
    Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad := by
  unfold lrRound
  simp only [List.mem_append]
  refine Or.inr ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [lrD, lrF]

end Round2

section Round3

variable {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ}
variable (hA : ∀ a, Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad → a.Holds rd σ)
include hA

/-- **The padding**: the zero cells read zero, and so does the zero run left. -/
theorem lr_pad (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0) (hkw : lrK nt bits ≤ 4) :
    ((lrPadCells (lrP o nt bits) (lrK nt bits) pad).1.map σ =
        List.replicate (8 - 2 * lrK nt bits) 0) ∧
      ∀ z, (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.2.2 = some z → ∀ j < 4, σ (.n (z + j)) = 0 := by
  have mem : ∀ a, Stmt.atom a ∈ (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.1 → a.Holds rd σ :=
    fun a ha ↦ hA a (mem_lrRound_pre (List.mem_append_right _ ha))
  set P := lrP o nt bits
  set k := lrK nt bits with hk
  have hk1 : 1 ≤ k := by simp only [hk, lrK]; omega
  unfold lrPadCells at mem ⊢
  by_cases h4 : k = 4
  · simp only [h4, ↓reduceIte, List.map_nil]
    exact ⟨by norm_num, hpad⟩
  by_cases h3 : k = 3
  · simp only [h3, ↓reduceIte] at mem ⊢
    have a0 := mem (.const (.n P) (word 0 0)) (by simp)
    have a1 := mem (.const (.n (P + 1)) (word 0 0)) (by simp)
    simp only [Atom.Holds, word_zero] at a0 a1
    exact ⟨by simp [a0, a1], hpad⟩
  simp only [h4, h3, ↓reduceIte] at mem ⊢
  rcases hp : pad with _ | z
  · simp only [hp] at mem ⊢
    have z1 := mem (.const (.n (P + 1)) (word 0 0)) (by simp)
    have z2 := mem (.const (.n (P + 2)) (word 0 0)) (by simp)
    have z3 := mem (.const (.n (P + 3)) (word 0 0)) (by simp)
    have z4 := mem (.const (.n (P + 4)) (word 0 0)) (by simp)
    simp only [Atom.Holds, word_zero] at z1 z2 z3 z4
    refine ⟨?_, fun z' hz' j hj ↦ ?_⟩
    · by_cases h1 : k = 1
      · simp [h1, z1, z2, z3, z4]
      · have h2 : k = 2 := by omega
        simp [h2, z1, z2, z3, z4]
    · obtain rfl : z' = P + 1 := (Option.some.inj hz').symm
      interval_cases j
      · exact z1
      · rw [show P + 1 + 1 = P + 2 by ring]; exact z2
      · rw [show P + 1 + 2 = P + 3 by ring]; exact z3
      · rw [show P + 1 + 3 = P + 4 by ring]; exact z4
  · have hz := hpad z hp
    have z0 := hz 0 (by norm_num); have z1 := hz 1 (by norm_num)
    have z2 := hz 2 (by norm_num); have z3 := hz 3 (by norm_num)
    simp only [Nat.add_zero] at z0
    refine ⟨?_, fun z' hz' ↦ ?_⟩
    · by_cases h1 : k = 1
      · simp [h1, z0, z1, z2, z3]
      · have h2 : k = 2 := by omega
        simp [h2, z0, z1, z2, z3]
    · obtain rfl : z' = z := (Option.some.inj hz').symm
      exact hz

end Round3

/-- The tail coefficients `c2, c3, …`, the words of scalars `1 .. nt`. -/
def lrT (σ : Val) (o nt : ℕ) : List E := (List.range nt).map fun j ↦ lrX σ o (j + 1)

theorem lrT_drop (σ : Val) (o nt j : ℕ) (hj : j < nt) :
    (lrT σ o nt).drop j = lrX σ o (j + 1) :: (lrT σ o nt).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [lrT]; omega)]
  simp [lrT]

section Round4

variable {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ}
variable (hA : ∀ a, Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad → a.Holds rd σ)
include hA

/-- **The claim's Horner chain**: the polynomial of the tail at `y`, and the tail's sum. -/
theorem lr_chain (hnt : 1 ≤ nt) :
    ∀ j ≤ nt - 1, σ (.n (lrAcc o nt (lrC o nt bits pad) j)) =
        polyEval ((lrT σ o nt).drop (nt - 1 - j)) (σ (.n (lrF o nt bits pad))) ∧
      σ (.n (lrTs o nt (lrC o nt bits pad) j)) = sumE ((lrT σ o nt).drop (nt - 1 - j)) := by
  intro j hj
  induction j with
  | zero =>
    have hx := (lr_scalar hA (i := nt) le_rfl).2.2.2 (by omega)
    have e : lrTail o (nt - 1) = o + lrSb nt + 3 := by simp only [lrTail, Nat.sub_add_cancel hnt]
    simp only [lrAcc, lrTs, ↓reduceIte, e, hx, Nat.sub_zero]
    rw [lrT_drop σ o nt (nt - 1) (by omega), Nat.sub_add_cancel hnt,
      show (lrT σ o nt).drop nt = [] by simp [lrT]]
    simp [polyEval, sumE]
  | succ j ih =>
    obtain ⟨i1, i2⟩ := ih (by omega)
    have mem := fun a ha ↦ hA a (mem_lrRound_chain (cl := cl) (cap := cap) (cur := cur) (tabs := tabs)
      (j' := j) (by omega) ha)
    have a0 := mem (.mul (.n (lrC o nt bits pad + 3 * j)) (.n (lrAcc o nt (lrC o nt bits pad) j)) (.n (lrF o nt bits pad))) (by simp)
    have a1 := mem (.add (.n (lrC o nt bits pad + 3 * j + 1)) (.n (lrC o nt bits pad + 3 * j)) (.n (lrTail o (nt - 1 - (j + 1))))) (by simp)
    have a2 := mem (.add (.n (lrC o nt bits pad + 3 * j + 2)) (.n (lrTs o nt (lrC o nt bits pad) j)) (.n (lrTail o (nt - 1 - (j + 1)))))
      (by simp)
    simp only [Atom.Holds] at a0 a1 a2
    have ht : σ (.n (lrTail o (nt - 1 - (j + 1)))) = lrX σ o (nt - 1 - (j + 1) + 1) :=
      (lr_scalar hA (i := nt - 1 - (j + 1) + 1) (by omega)).2.2.2 (by omega)
    have hd := lrT_drop σ o nt (nt - 1 - (j + 1)) (by omega)
    rw [show nt - 1 - (j + 1) + 1 = nt - 1 - j by omega] at hd
    refine ⟨?_, ?_⟩
    · simp only [lrAcc, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [a1, a0, ht, i1, hd, polyEval_cons, show nt - 1 - (j + 1) + 1 = nt - 1 - j by omega]
    · simp only [lrTs, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [a2, i2, ht, hd, sumE_cons, show nt - 1 - (j + 1) + 1 = nt - 1 - j by omega, add_comm]

end Round4

section Round5

variable {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ}
variable (hA : ∀ a, Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad → a.Holds rd σ)
include hA

/-- The words of a round, `c0` and the tail. -/
def lrXs (σ : Val) (o nt : ℕ) : List E := (List.range (nt + 1)).map (lrX σ o)

omit hA in
theorem lrXs_eq (σ : Val) (o nt : ℕ) : lrXs σ o nt = lrX σ o 0 :: lrT σ o nt := by
  simp [lrXs, lrT, List.range_succ_eq_map]

/-- **`link_round`'s template is one sum-check round**: its words at the cursor, its grind
passing, and its outputs the carried sponge's after them, the claim the round polynomial at the
challenge. -/
theorem lrRound_sound (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3))
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    (hgc : bits ≠ 0 → GcSound1 rd ∧ WinTabs rd (σ (.n tabs))) :
    ∃ n : E, ReadsAt rd (σ (.n cur)) (lrXs σ o nt ++ grindWords bits n) ∧
      ((⟨cap.map (σ ∘ .n), []⟩ : Fs).absorbAll (lrXs σ o nt) dsObserve).GrindOk bits n ∧
      σ (.n (lrD o nt bits pad + 3)) =
        (((⟨cap.map (σ ∘ .n), []⟩ : Fs).absorbAll (lrXs σ o nt) dsObserve).grindSqueeze bits n).1 ∧
      (lrOutCap nt bits o pad).map (σ ∘ .n) =
        (((⟨cap.map (σ ∘ .n), []⟩ : Fs).absorbAll (lrXs σ o nt) dsObserve).grindSqueeze bits n).2.cap ∧
      (((⟨cap.map (σ ∘ .n), []⟩ : Fs).absorbAll (lrXs σ o nt) dsObserve).grindSqueeze bits n).2.pend = [] ∧
      σ (.n (lrD o nt bits pad + 6)) = σ (.n cur) * gen ^ (nt + 1 + if bits = 0 then 0 else 1) ∧
      σ (.n (lrD o nt bits pad + 8)) = polyEval (lrX σ o 0 :: (σ (.n cl) + sumE (lrT σ o nt)) :: lrT σ o nt)
        (σ (.n (lrD o nt bits pad + 3))) ∧
      ∀ z, lrPad nt bits o pad = some z → ∀ j < 4, σ (.n (z + j)) = 0 := by
  -- the sponge after the scalars
  have hS := lr_sponge hA nt le_rfl
  rw [show ((List.range (nt + 1)).map (lrX σ o)).take (nt + 1) = lrXs σ o nt from
    List.take_of_length_le (by simp)] at hS
  set S : Fs := ⟨(lrCap o cap nt).map fun v ↦ σ (.n v), lrGrp σ o nt⟩ with hSdef
  have hSl : S.pend.length = nt % 4 + 1 := by simp [hSdef, lrGrp]
  have hcap0 : cap.map (σ ∘ .n) = cap.map fun v ↦ σ (.n v) := rfl
  rw [hcap0, hS]
  have hreads : ReadsAt rd (σ (.n cur)) (lrXs σ o nt) := fun i hi ↦ by
    simp only [lrXs, List.length_map, List.length_range] at hi
    simpa [lrXs] using (lr_scalar hA (i := i) (by omega)).1
  have hkw : lrK nt bits ≤ 4 := by
    rcases hk with rfl | ⟨rfl, h⟩ <;> simp only [lrK, ↓reduceIte, one_ne_zero] <;> omega
  obtain ⟨hpz, hpad'⟩ := lr_pad hA hpad hkw
  have hperm := hA _ mem_lrRound_perm
  have hgrp : (lrCells o (nt + 1 - (nt % 4 + 1)) (nt % 4 + 1)).map σ = pendCells S.pend := by
    rw [lr_cells hA (by omega)]
    simp only [hSdef, lrGrp]
    congr 2
    funext j
    rw [show nt + 1 - (nt % 4 + 1) + j = 4 * (nt / 4) + j by omega]
  -- the chain and the outputs common to both grinds
  obtain ⟨c1, c2⟩ := lr_chain hA hnt (nt - 1) le_rfl
  rw [Nat.sub_self, List.drop_zero] at c1 c2
  have memL := fun a ha ↦ hA a (mem_lrRound_last ha)
  have l0 := memL (.mul (.n (lrD o nt bits pad)) (.n (lrAcc o nt (lrC o nt bits pad) (nt - 1)))
    (.n (lrF o nt bits pad))) (by simp)
  have l1 := memL (.add (.n (lrD o nt bits pad + 1)) (.n cl) (.n (lrTs o nt (lrC o nt bits pad) (nt - 1))))
    (by simp)
  have l2 := memL (.add (.n (lrD o nt bits pad + 2)) (.n (lrD o nt bits pad)) (.n (lrD o nt bits pad + 1)))
    (by simp)
  have l3 := memL (.copy (.n (lrD o nt bits pad + 3)) (.n (lrF o nt bits pad))) (by simp)
  have l4 := memL (.const (.n (lrD o nt bits pad + 4)) (word (2 ^ (nt + 1 + if bits = 0 then 0 else 1)) 0))
    (by simp)
  have l5 := memL (.mul (.n (lrD o nt bits pad + 5)) (.n cur) (.n (lrD o nt bits pad + 4))) (by simp)
  have l6 := memL (.copy (.n (lrD o nt bits pad + 6)) (.n (lrD o nt bits pad + 5))) (by simp)
  have l7 := memL (.mul (.n (lrD o nt bits pad + 7)) (.n (lrD o nt bits pad + 2)) (.n (lrF o nt bits pad)))
    (by simp)
  have l8 := memL (.add (.n (lrD o nt bits pad + 8)) (.n (lrD o nt bits pad + 7)) (.n o)) (by simp)
  simp only [Atom.Holds] at l0 l1 l2 l3 l4 l5 l6 l7 l8
  have hx0 : σ (.n o) = lrX σ o 0 := by simp [lrX, lrSb]
  have hcur : σ (.n (lrD o nt bits pad + 6)) = σ (.n cur) * gen ^ (nt + 1 + if bits = 0 then 0 else 1) := by
    rw [l6, l5, l4, word_two_pow (by split <;> omega)]
  have hcl : σ (.n (lrD o nt bits pad + 8)) =
      polyEval (lrX σ o 0 :: (σ (.n cl) + sumE (lrT σ o nt)) :: lrT σ o nt) (σ (.n (lrD o nt bits pad + 3))) := by
    rw [l8, l7, l2, l0, l1, c1, c2, hx0, l3, polyEval_cons_cons]
  have hout : ∀ {T : KeccakState}, (∀ j (hj : j < 13), σ (.n (lrF o nt bits pad + j)) =
      cellsOfState T false ⟨j, hj⟩) → (lrOutCap nt bits o pad).map (σ ∘ .n) = capOf T := fun h ↦ by
    rw [capOf_outs h, lrOutCap]
    rfl
  rcases hk with rfl | ⟨rfl, hk3⟩
  · -- no grind: a plain squeeze
    have hc := keccakA_fs (s := S) hperm (by omega) (by
      simp only [List.map_append, hgrp, hpz]
      simp only [↓reduceIte, List.map_nil, List.append_nil, hSl, lrK, Nat.add_zero, List.map_map]
      rfl)
    have ho := outs_cells_of hc
    have ho0 := ho 0 (by norm_num)
    simp only [Nat.add_zero] at ho0
    refine ⟨0, by simpa [grindWords] using hreads, Or.inl rfl, ?_, ?_, rfl, hcur, hcl, hpad'⟩
    · rw [l3, ho0]
      simp [Fs.grindSqueeze, Fs.squeeze, Keccak.challengeOf_cells]
    · simp only [Fs.grindSqueeze, ↓reduceIte, Fs.squeeze]
      exact hout ho
  · -- one bit of grind: the nonce, its permutation, `grind_check`
    have memP := fun a ha ↦ hA a (mem_lrRound_pre (List.mem_append_left _ ha))
    have n0 := memP (.load (.n (lrE o nt)) (.n cur) (nt + 1)) (by simp)
    have n1 := memP (.copy (.n (lrE o nt + 1)) (.n (lrE o nt))) (by simp)
    have n2 := memP (.const (.n (lrE o nt + 2)) (word 0 4)) (by simp)
    simp only [Atom.Holds] at n0 n1 n2
    set n := σ (.n (lrE o nt))
    have hSn : S.absorb n dsPowNonce = ⟨S.cap, S.pend ++ [(n, dsPowNonce)]⟩ := by
      simp only [Fs.absorb, hSl, rateScalars]
      simp only [show nt % 4 + 1 ≠ 4 by omega, ↓reduceIte]
    have hc := keccakA_fs (s := S.absorb n dsPowNonce) hperm (by rw [hSn]; simp [hSl]; omega) (by
      rw [hSn]
      simp only [List.map_append, hgrp, hpz]
      simp only [one_ne_zero, ↓reduceIte, List.map_cons, List.map_nil, n1, n2, List.map_map,
        lrK, pendCells, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, scalarCells_eq,
        List.length_append, List.length_singleton, hSl]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rfl)
    have ho := outs_cells_of hc
    have hns : (S.absorb n dsPowNonce).perm = S.nonceState n := rfl
    rw [hns] at ho
    have ho0 := ho 0 (by norm_num)
    simp only [Nat.add_zero] at ho0
    obtain ⟨hg1, hwt⟩ := hgc one_ne_zero
    have hpow := hg1 (o := lrF o nt 1 pad + 13) (w := .n (lrF o nt 1 pad + 1)) (tabs := .n tabs) hwt
      fun a ha ↦ hA a (mem_lrRound_grind one_ne_zero ha)
    rw [ho 1 (by norm_num)] at hpow
    have hok : S.GrindOk 1 n := (grindOk_iff (by norm_num) n).mpr hpow
    refine ⟨n, ?_, hok, ?_, ?_, ?_, hcur, hcl, hpad'⟩
    · intro i hi
      simp only [grindWords, one_ne_zero, ↓reduceIte, List.length_append, List.length_singleton,
        lrXs, List.length_map, List.length_range] at hi
      rcases Nat.lt_or_ge i (nt + 1) with h | h
      · rw [List.getElem_append_left (by simpa [lrXs] using h)]
        exact hreads i (by simpa [lrXs] using h)
      · obtain rfl : i = nt + 1 := by omega
        rw [List.getElem_append_right (by simp [lrXs])]
        simpa [lrXs, grindWords] using n0
    · rw [l3, Fs.grindSqueeze_pos S one_ne_zero n, ho0, Keccak.challengeOf_cells]
      rfl
    · rw [Fs.grindSqueeze_pos S one_ne_zero n, hout ho]
    · rw [Fs.grindSqueeze_pos S one_ne_zero n]

end Round5

end
end LeanVM.Guest.B1.Link
