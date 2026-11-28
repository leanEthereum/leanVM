/-
  LeanVM.Guest.B1.VsC.RoundsA

  `link_round`'s sponge before its grind, from the atoms before it; and its soundness given the
  grind's proof of work.
-/

module

public import LeanVM.Guest.B1.Link.RoundsSound

/-!
# A round's sponge before its grind

Completeness needs the sponge a round's template carries before `grind_check`'s atoms are known to
hold: those atoms hold only when the proof of work passes, which is a fact of the sponge. The
soundness stream's `lr_scalar`, `lr_cells`, `lr_sponge` and `lr_pad` read only the atoms before
the grind (`lrRoundA`), so their copies here (`lrA_*`) take those atoms alone. `lrRound_soundP`
and `lrRound_stepP` are `lrRound_sound` and `lrRound_step` with the proof of work given (`hpw`)
instead of `grind_check`'s soundness on the memory (`GcSound1`), which a memory with only its low
words defined does not have.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A round's atoms before its grind: the scalars, the nonce, the padding, the permutation. -/
def lrRoundA (nt bits o : ℕ) (cap : List ℕ) (cur : ℕ) (pad : Option ℕ) : List Stmt :=
  let E := lrE o nt
  let pc := lrPadCells (lrP o nt bits) (lrK nt bits) pad
  let F := pc.2.2.1
  let k := nt % 4 + 1
  ((List.range (nt + 1)).map (lrStep o cap cur)).flatten ++
  (if bits = 0 then []
    else (if k = 4 then [lrPerm o cap ((nt + 1) / 4)] else []) ++
      [.atom (.load (.n E) (.n cur) (nt + 1)), .atom (.copy (.n (E + 1)) (.n E)),
        .atom (.const (.n (E + 2)) (word 0 4))]) ++
  pc.2.1 ++
  [.atom (.keccak (lrCells o (nt + 1 - k) k ++ (if bits = 0 then [] else [.n (E + 1), .n (E + 2)]) ++
      pc.1 ++ (lrCap o cap nt).map V.n) ((List.range 13).map fun j ↦ .n (F + j)) false false)]

/-- **The atoms before the grind are the round's.** -/
theorem mem_lrRound_of_A {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ} {s : Stmt}
    (h : s ∈ lrRoundA nt bits o cap cur pad) : s ∈ lrRound nt bits o cap cur cl tabs pad := by
  unfold lrRoundA at h
  unfold lrRound
  simp only [List.mem_append] at h ⊢
  tauto

section RoundA

variable {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur : ℕ} {pad : Option ℕ}

theorem mem_lrRoundA_step {i : ℕ} (hi : i ≤ nt) {a : Atom} (ha : Stmt.atom a ∈ lrStep o cap cur i) :
    Stmt.atom a ∈ lrRoundA nt bits o cap cur pad := by
  unfold lrRoundA
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩, ha⟩)))

theorem mem_lrRoundA_pre {a : Atom} (ha : Stmt.atom a ∈ (if bits = 0 then [] else
      (if nt % 4 + 1 = 4 then [lrPerm o cap ((nt + 1) / 4)] else []) ++
      [.atom (.load (.n (lrE o nt)) (.n cur) (nt + 1)), .atom (.copy (.n (lrE o nt + 1)) (.n (lrE o nt))),
        .atom (.const (.n (lrE o nt + 2)) (word 0 4))]) ++
      (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.1) :
    Stmt.atom a ∈ lrRoundA nt bits o cap cur pad := by
  unfold lrRoundA
  simp only [List.mem_append] at ha ⊢
  rcases ha with h | h
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)

theorem mem_lrRoundA_perm :
    Stmt.atom (.keccak (lrCells o (nt + 1 - (nt % 4 + 1)) (nt % 4 + 1) ++
      (if bits = 0 then [] else [.n (lrE o nt + 1), .n (lrE o nt + 2)]) ++
      (lrPadCells (lrP o nt bits) (lrK nt bits) pad).1 ++ (lrCap o cap nt).map V.n)
      ((List.range 13).map fun j ↦ .n (lrF o nt bits pad + j)) false false) ∈
      lrRoundA nt bits o cap cur pad := by
  unfold lrRoundA lrF
  simp only [List.mem_append]
  exact Or.inr (List.mem_singleton.mpr rfl)

variable (hA : ∀ a, Stmt.atom a ∈ lrRoundA nt bits o cap cur pad → a.Holds rd σ)
include hA

theorem lrA_scalar {i : ℕ} (hi : i ≤ nt) :
    LoadHolds rd (σ (.n cur)) i (lrX σ o i) ∧ σ (.n (o + lrSb i + 1)) = lrX σ o i ∧
      σ (.n (o + lrSb i + 2)) = word 0 1 ∧ (i ≠ 0 → σ (.n (o + lrSb i + 3)) = lrX σ o i) := by
  have mem : ∀ a, Stmt.atom a ∈ lrScalar o cur i → a.Holds rd σ := fun a ha ↦
    hA a (mem_lrRoundA_step hi (List.mem_append_right _ ha))
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

theorem lrA_cells {j k : ℕ} (hjk : j + k ≤ nt + 1) :
    (lrCells o j k).map σ = pendCells ((List.range k).map fun i ↦ (lrX σ o (j + i), dsObserve)) := by
  simp only [lrCells, pendCells, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  obtain ⟨-, h1, h2, -⟩ := lrA_scalar hA (i := j + i) (by omega)
  simp only [List.map_cons, List.map_nil, h1, h2, scalarCells_eq, word_dsObserve]

/-- **The sponge after scalar `i`**: the capacity values `lrCap` and the group waiting. -/
theorem lrA_sponge :
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
      have hp := hA _ (mem_lrRoundA_step (bits := bits) (pad := pad)
        (show i + 1 ≤ nt by omega) (a := .keccak (lrCells o (4 * ((i + 1) / 4) - 4) 4 ++
          (lrCap o cap (4 * ((i + 1) / 4) - 1)).map V.n)
          ((List.range 13).map fun j ↦ .n (lrPermOut o ((i + 1) / 4) + j)) false false)
        (by simp [lrStep, hm, lrPerm]))
      have e1 : 4 * ((i + 1) / 4) - 4 = 4 * (i / 4) := by omega
      have e2 : 4 * ((i + 1) / 4) - 1 = i := by omega
      rw [e1, e2] at hp
      have hc := keccakA_fs (s := ⟨(lrCap o cap i).map fun v ↦ σ (.n v), lrGrp σ o i⟩) hp
        (by simp [lrGrp]; omega) (by
          rw [List.map_append, lrA_cells hA (by omega), List.map_map]
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


/-- **The padding**: the zero cells read zero, and so does the zero run left. -/
theorem lrA_pad (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0) (hkw : lrK nt bits ≤ 4) :
    ((lrPadCells (lrP o nt bits) (lrK nt bits) pad).1.map σ =
        List.replicate (8 - 2 * lrK nt bits) 0) ∧
      ∀ z, (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.2.2 = some z → ∀ j < 4, σ (.n (z + j)) = 0 := by
  have mem : ∀ a, Stmt.atom a ∈ (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.1 → a.Holds rd σ :=
    fun a ha ↦ hA a (mem_lrRoundA_pre (List.mem_append_right _ ha))
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


/-- **The nonce's permutation, before the grind**: the round's words and its nonce at the cursor,
and lane `1` of the nonce's permutation, `grind_check`'s word, at `F + 1`. -/
theorem lrA_nonce (hk3 : nt % 4 ≠ 3) (hb : bits = 1)
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0) :
    ReadsAt rd (σ (.n cur)) (lrXs σ o nt ++ [σ (.n (lrE o nt))]) ∧
      σ (.n (lrF o nt bits pad + 1)) =
        cellsOfState ((((⟨cap.map (σ ∘ .n), []⟩ : Fs).absorbAll (lrXs σ o nt) dsObserve).nonceState
          (σ (.n (lrE o nt))))) false ⟨1, by norm_num⟩ := by
  subst hb
  have hS := lrA_sponge hA nt le_rfl
  rw [show ((List.range (nt + 1)).map (lrX σ o)).take (nt + 1) = lrXs σ o nt from
    List.take_of_length_le (by simp)] at hS
  set S : Fs := ⟨(lrCap o cap nt).map fun v ↦ σ (.n v), lrGrp σ o nt⟩ with hSdef
  have hSl : S.pend.length = nt % 4 + 1 := by simp [hSdef, lrGrp]
  have hcap0 : cap.map (σ ∘ .n) = cap.map fun v ↦ σ (.n v) := rfl
  rw [hcap0, hS]
  have hreads : ReadsAt rd (σ (.n cur)) (lrXs σ o nt) := fun i hi ↦ by
    simp only [lrXs, List.length_map, List.length_range] at hi
    simpa [lrXs] using (lrA_scalar hA (i := i) (by omega)).1
  have hkw : lrK nt 1 ≤ 4 := by simp only [lrK, one_ne_zero, ↓reduceIte]; omega
  obtain ⟨hpz, -⟩ := lrA_pad hA hpad hkw
  have hperm := hA _ mem_lrRoundA_perm
  have hgrp : (lrCells o (nt + 1 - (nt % 4 + 1)) (nt % 4 + 1)).map σ = pendCells S.pend := by
    rw [lrA_cells hA (by omega)]
    simp only [hSdef, lrGrp]
    congr 2
    funext j
    rw [show nt + 1 - (nt % 4 + 1) + j = 4 * (nt / 4) + j by omega]
  have memP := fun a ha ↦ hA a (mem_lrRoundA_pre (List.mem_append_left _ ha))
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
  refine ⟨?_, ho 1 (by norm_num)⟩
  intro i hi
  simp only [List.length_append, List.length_singleton, lrXs, List.length_map, List.length_range] at hi
  rcases Nat.lt_or_ge i (nt + 1) with h | h
  · rw [List.getElem_append_left (by simpa [lrXs] using h)]
    exact hreads i (by simpa [lrXs] using h)
  · obtain rfl : i = nt + 1 := by omega
    rw [List.getElem_append_right (by simp [lrXs])]
    simpa [lrXs] using n0

end RoundA

section RoundP

variable {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ}
variable (hA : ∀ a, Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad → a.Holds rd σ)
include hA

/-- **`lrRound_sound` with the proof of work given.** -/
theorem lrRound_soundP (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3))
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    (hpw : bits ≠ 0 → ((σ (.n (lrF o nt bits pad + 1))).limb 0).lane.toNat % 2 ^ 1 = 0) :
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
    have hpow := hpw one_ne_zero
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

end RoundP

/-- **`lrRound_step` with the proof of work given.** -/
theorem lrRound_stepP {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ}
    {pad : Option ℕ} (hA : ∀ a, Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad → a.Holds rd σ)
    (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3))
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    (hpw : bits ≠ 0 → ((σ (.n (lrF o nt bits pad + 1))).limb 0).lane.toNat % 2 ^ 1 = 0) :
    RoundStep rd nt bits (rstOf σ cap cur cl) (σ (.n (lrD o nt bits pad + 3)))
        (rstOf σ (lrOutCap nt bits o pad) (lrD o nt bits pad + 6) (lrD o nt bits pad + 8)) ∧
      ∀ z, lrPad nt bits o pad = some z → ∀ j < 4, σ (.n (z + j)) = 0 := by
  obtain ⟨n, hr, hok, hy, hcap, hpend, hcur, hcl, hpad'⟩ := lrRound_soundP hA hnt hnt' hk hpad hpw
  rw [lrXs_eq] at hr hok hy hcap hpend
  rw [absorbAll_cons] at hok hy hcap hpend
  refine ⟨?_, hpad'⟩
  unfold RoundStep
  simp only [rstOf]
  refine ⟨lrX σ o 0, lrT σ o nt, n, by simp [lrT], hr, hok, ?_, ?_, ?_⟩
  · generalize hG : ((⟨cap.map (σ ∘ .n), []⟩ : Fs).absorb (lrX σ o 0) dsObserve |>.absorbAll
      (lrT σ o nt) dsObserve |>.grindSqueeze bits n) = G at hy hcap hpend ⊢
    obtain ⟨y', c', p'⟩ := G
    simp only at hy hcap hpend
    subst hy hcap hpend
    rfl
  · show σ (.n (lrD o nt bits pad + 6)) = _
    rw [hcur, grindWords_length]
  · exact hcl

end
end LeanVM.Guest.B1.Link
