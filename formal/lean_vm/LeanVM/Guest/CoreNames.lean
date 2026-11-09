/-
  LeanVM.Guest.CoreNames

  The names of the core program's functions are distinct, so a function is found by its name.
-/

module

public import LeanVM.Guest.CoreData

/-!
# Distinct function names

Strings are never compared in the kernel: each name is encoded as a natural number, and the
encodings are checked pairwise distinct (`coreProgram_names_nodup`).
-/

namespace LeanVM.Guest

open Core

@[expose] public section

/-- The bytes of a name as digits in base `2^9`, each shifted by one. -/
def encL : List UInt8 → ℕ
  | [] => 0
  | c :: cs => (c.toNat + 1) + 2 ^ 9 * encL cs

/-- The encoding of a name. -/
def encS (s : String) : ℕ := encL s.toByteArray.data.toList

/-- Pairwise distinctness by `Nat.beq`, with no `Decidable` instances. -/
def nodupB : List ℕ → Bool
  | [] => true
  | x :: xs => !(xs.any (Nat.beq x)) && nodupB xs

theorem nodup_of_nodupB : ∀ {l : List ℕ}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, Nat.beq_eq] at h
    exact List.nodup_cons.mpr ⟨fun hx ↦ h.1 x hx rfl, nodup_of_nodupB h.2⟩

/-- Entry `i` differs from every later one. -/
def ndAt (l : List ℕ) (i : ℕ) : Bool := !((l.drop (i + 1)).any (Nat.beq (l.getD i 0)))

theorem nodupB_of_ndAt : ∀ {l : List ℕ}, (∀ i < l.length, ndAt l i = true) → nodupB l = true
  | [], _ => rfl
  | x :: xs, h => by
    have h0 := h 0 (by simp)
    simp only [nodupB, Bool.and_eq_true]
    refine ⟨h0, nodupB_of_ndAt fun i hi ↦ ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [ndAt] using this

/-- The names' encodings. -/
noncomputable def coreCodes : List ℕ := coreProgram.map fun f ↦ encS f.name

theorem ndAt_of_ge {l : List ℕ} {i : ℕ} (h : l.length ≤ i) : ndAt l i = true := by
  simp [ndAt, List.drop_eq_nil_of_le (Nat.le_succ_of_le h)]

set_option maxRecDepth 100000 in
theorem coreCodes_length : coreCodes.length ≤ 1120 := by decide +kernel

/-! The check is split into windows of indices, one declaration each, to keep the kernel's
memory low. -/

set_option maxRecDepth 100000 in
theorem coreCodes_w0 : ∀ i ∈ List.range' 0 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w1 : ∀ i ∈ List.range' 70 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w2 : ∀ i ∈ List.range' 140 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w3 : ∀ i ∈ List.range' 210 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w4 : ∀ i ∈ List.range' 280 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w5 : ∀ i ∈ List.range' 350 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w6 : ∀ i ∈ List.range' 420 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w7 : ∀ i ∈ List.range' 490 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w8 : ∀ i ∈ List.range' 560 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w9 : ∀ i ∈ List.range' 630 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w10 : ∀ i ∈ List.range' 700 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w11 : ∀ i ∈ List.range' 770 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w12 : ∀ i ∈ List.range' 840 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w13 : ∀ i ∈ List.range' 910 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w14 : ∀ i ∈ List.range' 980 70, ndAt coreCodes i = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem coreCodes_w15 : ∀ i ∈ List.range' 1050 70, ndAt coreCodes i = true := by decide +kernel

theorem coreCodes_nd : ∀ i < 1120, ndAt coreCodes i = true := by
  intro i hi
  by_cases h0 : i < 70
  · exact coreCodes_w0 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h1 : i < 140
  · exact coreCodes_w1 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h2 : i < 210
  · exact coreCodes_w2 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h3 : i < 280
  · exact coreCodes_w3 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h4 : i < 350
  · exact coreCodes_w4 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h5 : i < 420
  · exact coreCodes_w5 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h6 : i < 490
  · exact coreCodes_w6 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h7 : i < 560
  · exact coreCodes_w7 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h8 : i < 630
  · exact coreCodes_w8 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h9 : i < 700
  · exact coreCodes_w9 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h10 : i < 770
  · exact coreCodes_w10 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h11 : i < 840
  · exact coreCodes_w11 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h12 : i < 910
  · exact coreCodes_w12 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h13 : i < 980
  · exact coreCodes_w13 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h14 : i < 1050
  · exact coreCodes_w14 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  exact coreCodes_w15 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

theorem coreProgram_encodings_nodup : (coreProgram.map fun f ↦ encS f.name).Nodup := by
  refine nodup_of_nodupB (nodupB_of_ndAt fun i _ ↦ ?_)
  by_cases hi : i < 1120
  · exact coreCodes_nd i hi
  · exact ndAt_of_ge (by have := coreCodes_length; unfold coreCodes at this; omega)

theorem coreProgram_names_nodup : (coreProgram.map (·.name)).Nodup := by
  have h := coreProgram_encodings_nodup
  have h' : ((coreProgram.map (·.name)).map encS).Nodup := by
    rwa [List.map_map]
  exact h'.of_map _

private theorem find_getElem_of_nodup :
    ∀ {l : List Fn}, (l.map (·.name)).Nodup → ∀ {j : ℕ} (h : j < l.length),
      l.find? (fun g ↦ g.name == l[j].name) = some l[j]
  | [], _, j, h => absurd h (Nat.not_lt_zero _)
  | g :: l, hn, j, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases j with
    | zero => simp
    | succ j =>
      have hj : j < l.length := Nat.lt_of_succ_lt_succ h
      have hne : g.name ≠ (l[j]'hj).name := fun e ↦
        hn.1 (List.mem_map.mpr ⟨l[j], List.getElem_mem hj, e.symm⟩)
      have hb : (g.name == (l[j]'hj).name) = false := by simpa using hne
      rw [List.getElem_cons_succ, List.find?_cons, hb]
      exact find_getElem_of_nodup hn.2 hj

theorem coreProgram_find_getElem {j : ℕ} (h : j < coreProgram.length) :
    coreProgram.find? coreProgram[j].name = some coreProgram[j] :=
  find_getElem_of_nodup coreProgram_names_nodup h

end
end LeanVM.Guest
