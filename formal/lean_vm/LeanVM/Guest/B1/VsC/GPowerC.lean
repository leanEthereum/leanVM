/-
  LeanVM.Guest.B1.VsC.GPowerC

  `g_power_of_word` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Quiet
public import LeanVM.Guest.B1.VsC.TableSizeC
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.Value.FieldBits
import LeanVM.Guest.CoreRef

/-!
# `g_power_of_word`, complete

`g_power_of_word(value)` hints the six bits of `value`, squares each back in place and asserts
their weighted sum is `value`. Booleanity and the sum pin the bits (`bits_of_reconstruct`), so on
every valuation holding its atoms the hint is exact (`gpow_pinned`); its relation is its meaning
(`g_power_of_word_holds`). `g_power_of_word_complete`: on `E(n)`, `n < 64`, the call returns
`g^n`, popping nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Prover.Exec (wordNat bitWord)
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem gpow_body_at {rd : Reader} {σ : Val} {B : List Stmt}
    (hA : ∀ a, Stmt.atom a ∈ B → a.Holds rd σ) (i : ℕ) (hi : i < B.length) (a : Atom)
    (he : B[i] = .atom a) : a.Holds rd σ :=
  hA a (he ▸ List.getElem_mem hi)

theorem bitWord_eq_bitE (b : Bool) : bitWord b = bitE b := by cases b <;> rfl

/-- **The bits are pinned**: on a valuation holding `g_power_of_word`'s atoms, its hint is exact. -/
theorem gpow_pinned {rd : Reader} {σ : Val}
    (hA : ∀ a, Stmt.atom a ∈ (fn% «g_power_of_word»).body → a.Holds rd σ) :
    ∀ a, Stmt.atom a ∈ (fn% «g_power_of_word»).body → a.Exact rd σ := by
  have at_ := gpow_body_at hA
  have b1 := at_ 1 (by decide +kernel) _ rfl
  have b2 := at_ 6 (by decide +kernel) _ rfl
  have b3 := at_ 15 (by decide +kernel) _ rfl
  have b4 := at_ 24 (by decide +kernel) _ rfl
  have b5 := at_ 33 (by decide +kernel) _ rfl
  have b6 := at_ 42 (by decide +kernel) _ rfl
  have c11 := at_ 7 (by decide +kernel) _ rfl
  have m12 := at_ 8 (by decide +kernel) _ rfl
  have a13 := at_ 9 (by decide +kernel) _ rfl
  have c19 := at_ 16 (by decide +kernel) _ rfl
  have m20 := at_ 17 (by decide +kernel) _ rfl
  have a21 := at_ 18 (by decide +kernel) _ rfl
  have c27 := at_ 25 (by decide +kernel) _ rfl
  have m28 := at_ 26 (by decide +kernel) _ rfl
  have a29 := at_ 27 (by decide +kernel) _ rfl
  have c35 := at_ 34 (by decide +kernel) _ rfl
  have m36 := at_ 35 (by decide +kernel) _ rfl
  have a37 := at_ 36 (by decide +kernel) _ rfl
  have c43 := at_ 43 (by decide +kernel) _ rfl
  have m44 := at_ 44 (by decide +kernel) _ rfl
  have a45 := at_ 45 (by decide +kernel) _ rfl
  have hs := at_ 51 (by decide +kernel) _ rfl
  simp only [Atom.Holds] at b1 b2 b3 b4 b5 b6 c11 m12 a13 c19 m20 a21 c27 m28 a29 c35 m36 a37 c43 m44 a45 hs
  let b : ℕ → E := fun i => σ (.n (i + 1))
  have hb : ∀ i < 6, b i * b i = b i := fun i hi => by
    interval_cases i
    · exact b1.symm
    · exact b2.symm
    · exact b3.symm
    · exact b4.symm
    · exact b5.symm
    · exact b6.symm
  have hx : ∑ i ∈ Finset.range 6, b i * coordBasis (0 + i) = σ (.n 0) := by
    have e := e_add_eq_zero_iff.mp hs
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, b]
    simp only [coordBasis_of_lt (by norm_num : (0 : ℕ) < 64), coordBasis_of_lt (by norm_num : (1 : ℕ) < 64),
      coordBasis_of_lt (by norm_num : (2 : ℕ) < 64), coordBasis_of_lt (by norm_num : (3 : ℕ) < 64),
      coordBasis_of_lt (by norm_num : (4 : ℕ) < 64), coordBasis_of_lt (by norm_num : (5 : ℕ) < 64)]
    rw [← e, a45, a37, a29, a21, a13, m44, m36, m28, m20, m12, c43, c35, c27, c19, c11]
    simp only [word_eOfNat, pow_zero, pow_one, eOfNat_one, mul_one]
    norm_num
  obtain ⟨N, hN, hv, hbits⟩ := bits_of_reconstruct hb hx
  have hN64 : N < 2 ^ 64 := lt_trans hN (by norm_num)
  rw [Nat.pow_zero, Nat.one_mul, eOfNat128_of_lt hN64] at hv
  intro a ha
  have hsplit : (fn% «g_power_of_word»).body =
      .atom (.hint (.bits (.n 0) 0 6 (.stack [.n 1, .n 2, .n 3, .n 4, .n 5, .n 6]))) ::
        (fn% «g_power_of_word»).body.tail := rfl
  rw [hsplit] at ha
  rcases List.mem_cons.mp ha with he | ha
  · cases he
    show [σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] =
      (List.range 6).map fun j => bitWord ((wordNat (σ (.n 0))).testBit (0 + j))
    rw [hv, wordNat_eOfNat hN64]
    refine List.ext_getElem (by simp) fun j h1 h2 => ?_
    have hj : j < 6 := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add, bitWord_eq_bitE]
    rw [← hbits j hj]
    interval_cases j <;> rfl
  · have hnc : (atomsOf (fn% «g_power_of_word»).body.tail).all (fun a => !isComputed a) = true := by
      decide +kernel
    exact exact_of_not_computed (by simpa using List.all_eq_true.mp hnc a (mem_atomsOf' ha))

/-- **`g_power_of_word` completes**: on `E(n)`, `n < 64`, it returns `g^n`. -/
theorem g_power_of_word_complete (k : ℕ) (Pre : Reader → Prop) {n : ℕ} (hn : n < 64) :
    CallCompletes k "g_power_of_word" [eOfNat n] [gen ^ n] Pre PostQuiet :=
  callCompletes_leaf_pinned find_g_power_of_word (by decide +kernel)
    (fun rd _ _ => (g_power_of_word_holds rd _ _).mpr ⟨n, hn, rfl, rfl⟩)
    (fun _ _ _ _ _ hA => gpow_pinned hA)

end
end LeanVM.Guest.B1.VsC
