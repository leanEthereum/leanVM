/-
Codes, lists and interleaved codes, with nothing assumed of the code but a bound on the
agreement of two distinct codewords: the setting of Section 6.1 of the paper.

A word is a function `ι → α`; only its values on a finite set `D` of coordinates count
(`D = Finset.univ` when `ι` is a finite type). A code is a set `C` of words. An interleaved word
with lanes `m` is a word over the alphabet `m → α`, so its agreement with a tuple of codewords is
the set of coordinates where all lanes agree.
-/
import Mathlib

open Finset

namespace Interleave

variable {ι α : Type*}

open Classical in
/-- The coordinates of `D` where the words `w` and `c` agree. -/
noncomputable def agr (D : Finset ι) (w c : ι → α) : Finset ι := D.filter (fun i => w i = c i)

theorem mem_agr {D : Finset ι} {w c : ι → α} {i : ι} : i ∈ agr D w c ↔ i ∈ D ∧ w i = c i := by
  simp only [agr, mem_filter]

theorem agr_subset (D : Finset ι) (w c : ι → α) : agr D w c ⊆ D := fun _ hi => (mem_agr.mp hi).1

theorem agr_comm (D : Finset ι) (w c : ι → α) : agr D w c = agr D c w := by
  ext i
  simp only [mem_agr, eq_comm]

theorem agr_self (D : Finset ι) (w : ι → α) : agr D w w = D := by
  ext i
  simp only [mem_agr, and_true]

/-- Two words that both agree with `w` at a coordinate agree with each other there. -/
theorem mem_agr_of_mem_agr {D : Finset ι} {w c c' : ι → α} {i : ι} (h1 : i ∈ agr D w c)
    (h2 : i ∈ agr D w c') : i ∈ agr D c c' :=
  mem_agr.mpr ⟨(mem_agr.mp h1).1, (mem_agr.mp h1).2.symm.trans (mem_agr.mp h2).2⟩

/-- Two distinct codewords of `C` agree on at most `d` coordinates of `D`. -/
def AgreeLE (D : Finset ι) (C : Set (ι → α)) (d : ℕ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → (agr D c c').card ≤ d

/-- Every word has at most `L` codewords of `C` agreeing with it on at least `a` coordinates of
`D`: every finite set of such codewords has at most `L` elements. -/
def ListBound (D : Finset ι) (C : Set (ι → α)) (a L : ℕ) : Prop :=
  ∀ (w : ι → α) (S : Finset (ι → α)), (∀ c ∈ S, c ∈ C ∧ a ≤ (agr D w c).card) → S.card ≤ L

theorem ListBound.mono {D : Finset ι} {C : Set (ι → α)} {a a' L L' : ℕ}
    (h : ListBound D C a L) (ha : a ≤ a') (hL : L ≤ L') : ListBound D C a' L' :=
  fun w S hS => (h w S fun c hc => ⟨(hS c hc).1, ha.trans (hS c hc).2⟩).trans hL

/-- Lane `j` of an interleaved word. -/
def lane {m : Type*} (j : m) (c : ι → m → α) : ι → α := fun i => c i j

@[simp] theorem lane_apply {m : Type*} (j : m) (c : ι → m → α) (i : ι) : lane j c i = c i j := rfl

/-- The interleaved code with lanes `m`: the words over the alphabet `m → α` all of whose lanes
are codewords. -/
def interleave (m : Type*) (C : Set (ι → α)) : Set (ι → m → α) := {c | ∀ j, lane j c ∈ C}

theorem mem_interleave {m : Type*} {C : Set (ι → α)} {c : ι → m → α} :
    c ∈ interleave m C ↔ ∀ j, lane j c ∈ C := Iff.rfl

/-- Where two interleaved words agree, each of their lanes agree. -/
theorem agr_subset_agr_lane {m : Type*} (D : Finset ι) (w c : ι → m → α) (j : m) :
    agr D w c ⊆ agr D (lane j w) (lane j c) := fun _ hi =>
  mem_agr.mpr ⟨(mem_agr.mp hi).1, congrFun (mem_agr.mp hi).2 j⟩

/-- The interleaved code has the agreement bound of the code. -/
theorem AgreeLE.interleave {D : Finset ι} {C : Set (ι → α)} {d : ℕ} (hC : AgreeLE D C d)
    (m : Type*) : AgreeLE D (interleave m C) d := by
  intro c hc c' hc' hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  have hl : lane j c ≠ lane j c' := fun h => hj (congrFun h i)
  exact (card_le_card (agr_subset_agr_lane D c c' j)).trans (hC _ (hc j) _ (hc' j) hl)

/-- Unique decoding: beyond half the distance a word has at most one codeword. -/
theorem AgreeLE.listBound_one {D : Finset ι} {C : Set (ι → α)} {d a : ℕ} (hC : AgreeLE D C d)
    (h : D.card + d < 2 * a) : ListBound D C a 1 := by
  classical
  intro w S hS
  refine card_le_one.mpr fun c hc c' hc' => ?_
  by_contra hne
  have h1 := card_union_add_card_inter (agr D w c) (agr D w c')
  have h2 : (agr D w c ∪ agr D w c').card ≤ D.card :=
    card_le_card (union_subset (agr_subset _ _ _) (agr_subset _ _ _))
  have h3 : (agr D w c ∩ agr D w c').card ≤ d :=
    (card_le_card fun _ hi => mem_agr_of_mem_agr (mem_inter.mp hi).1 (mem_inter.mp hi).2).trans
      (hC c (hS c hc).1 c' (hS c' hc').1 hne)
  have h4 := (hS c hc).2
  have h5 := (hS c' hc').2
  omega

/-- An interleaved code with at least one lane has an empty list wherever the code has. -/
theorem ListBound.interleave_zero {D : Finset ι} {C : Set (ι → α)} {a : ℕ}
    (h : ListBound D C a 0) (m : Type*) [Nonempty m] : ListBound D (interleave m C) a 0 := by
  intro w S hS
  by_contra hne
  obtain ⟨c, hc⟩ : S.Nonempty := card_pos.mp (Nat.pos_of_ne_zero fun h0 => hne (le_of_eq h0))
  obtain ⟨j⟩ := ‹Nonempty m›
  have := h (lane j w) {lane j c} fun c' hc' => by
    rw [mem_singleton.mp hc']
    exact ⟨(hS c hc).1 j, (hS c hc).2.trans (card_le_card (agr_subset_agr_lane D w c j))⟩
  simp at this

/-- Interleaving cannot shrink lists: a list of a word is, lane by lane, a list of the word
repeated in every lane. So a bound for interleaved words is a bound for single words. -/
theorem ListBound.of_interleave {D : Finset ι} {C : Set (ι → α)} {a L : ℕ} {m : Type*}
    [Nonempty m] (h : ListBound D (interleave m C) a L) : ListBound D C a L := by
  classical
  intro w S hS
  obtain ⟨j⟩ := ‹Nonempty m›
  have hinj : Function.Injective (fun (c : ι → α) (i : ι) (_ : m) => c i) := fun c c' hcc => by
    funext i
    exact congrFun (congrFun hcc i) j
  rw [← card_image_of_injective S hinj]
  refine h (fun i _ => w i) _ fun c' hc' => ?_
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hc'
  refine ⟨fun _ => (hS c hc).1, (hS c hc).2.trans (card_le_card fun i hi => ?_)⟩
  exact mem_agr.mpr ⟨(mem_agr.mp hi).1, funext fun _ => (mem_agr.mp hi).2⟩

end Interleave
