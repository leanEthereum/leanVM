/-
  LeanVM.Guest.B1.Tables.Vt.Fresh

  `verify_tables`' first stream words: the four framework column values read into the carried
  sponge, the bytecode share and its first round's two coefficients, and the first round's
  challenge squeezed after them.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The bus's first stream words

The framework decomposition reads, in block order, the memory block's two values (push side), the
final memory count and the final bytecode count (pull side), each `fs_next` into the rate. The
bytecode's share `S` then waits behind a permutation of the four, its first round's `c0`, `c2`
after it, and the round's challenge is the squeeze after them (a grind of `ROUND2_GRIND_BITS = 0`
is no nonce). In the specification's terms (`vt_fresh`): from the carried capacity, the seven
words absorbed, then one squeeze.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The seven words, in their stream order: the memory's two values, the final memory and
bytecode counts, the bytecode share, its first round's `c0` and `c2`. -/
def vtFreshWords (σ : Val) : List E :=
  [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2")), σ (.n (val% «verify_tables» "x@3")), σ (.n (val% «verify_tables» "x@4")), σ (.n (val% «verify_tables» "x@5")), σ (.n (val% «verify_tables» "x@6")), σ (.n (val% «verify_tables» "x@7"))]

/-- The carried sponge after them. -/
def vtFreshFs (σ : Val) : Fs :=
  (⟨[σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4"))], []⟩ : Fs).absorbAll (vtFreshWords σ)
    dsObserve

/-- A permutation's thirteen outputs from `b`. -/
def vtOuts (b : ℕ) : List V := (List.range 13).map fun k ↦ .n (b + k)

/-- A `KECCAK` atom writing the thirteen values from `b`: each is its cell of the permutation of
the cells read, and the last five are its capacity. -/
theorem vt_keccak {rd : Reader} {σ : Val} {ins : List V} {b : ℕ}
    (hk : (Atom.keccak ins (vtOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      ((List.range 5).map fun k ↦ σ (.n (b + 8 + k))) = capOf (permOf (ins.map σ)) := by
  obtain ⟨-, -, hout⟩ := keccakA_perm hk (by simp [vtOuts])
  have hP : ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa [vtOuts] using hk)
    simpa [vtOuts] using this
  refine ⟨hP, ?_⟩
  simp only [capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append]
  rw [hP (8 + 0) (by omega), hP (8 + 1) (by omega), hP (8 + 2) (by omega), hP (8 + 3) (by omega),
    hP (8 + 4) (by omega)]
  rfl

set_option maxRecDepth 10000 in
/-- **The bus's first stream words** and the bytecode sumcheck's first challenge (at `1855`),
the sponge's capacity after it (`1863 .. 1867`), and the copies of the share and the first round's
coefficients the round reads. -/
theorem vt_fresh {rd : Reader} {σ : Val} (h : VtH rd σ) :
    TbReadsAt rd (σ (.n (val% «verify_tables» "cursor@1"))) (vtFreshWords σ) ∧
      σ (.n (val% «verify_tables» "nxt[0]@2")) = (vtFreshFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "nxt[8]@2") + k))) = (vtFreshFs σ).squeeze.2.cap ∧
      σ (.n (val% «verify_tables» "bc_msg[0]")) = σ (.n (val% «verify_tables» "x@5")) ∧ σ (.n (val% «verify_tables» "bc_msg[1]")) = σ (.n (val% «verify_tables» "x@6")) ∧ σ (.n (val% «verify_tables» "bc_msg[2]")) = σ (.n (val% «verify_tables» "x@7")) := by
  obtain ⟨_, f0⟩ := h.sliceAt 799 (fsNextT (.n (val% «verify_tables» "cursor@1")) 0 (val% «verify_tables» "x@1")) (by decide +kernel)
  obtain ⟨_, f1⟩ := h.sliceAt 804 (fsNextT (.n (val% «verify_tables» "cursor@1")) 1 (val% «verify_tables» "x@2")) (by decide +kernel)
  obtain ⟨_, f2⟩ := h.sliceAt 1342 (fsNextT (.n (val% «verify_tables» "cursor@1")) 2 (val% «verify_tables» "x@3")) (by decide +kernel)
  obtain ⟨_, f3⟩ := h.sliceAt 1357 (fsNextT (.n (val% «verify_tables» "cursor@1")) 3 (val% «verify_tables» "x@4")) (by decide +kernel)
  obtain ⟨_, f4⟩ := h.sliceAt 1915 (fsNextT (.n (val% «verify_tables» "cursor@1")) 4 (val% «verify_tables» "x@5")) (by decide +kernel)
  obtain ⟨_, f5⟩ := h.sliceAt 1919 (fsNextT (.n (val% «verify_tables» "cursor@1")) 5 (val% «verify_tables» "x@6")) (by decide +kernel)
  obtain ⟨_, f6⟩ := h.sliceAt 1923 (fsNextT (.n (val% «verify_tables» "cursor@1")) 6 (val% «verify_tables» "x@7")) (by decide +kernel)
  rw [holds_fsNextT] at f0 f1 f2 f3 f4 f5 f6
  obtain ⟨⟨l0, p0⟩, -⟩ := f0
  obtain ⟨⟨l1, p1⟩, -⟩ := f1
  obtain ⟨⟨l2, p2⟩, -⟩ := f2
  obtain ⟨⟨l3, p3⟩, -⟩ := f3
  obtain ⟨⟨l4, p4⟩, -⟩ := f4
  obtain ⟨⟨l5, p5⟩, -⟩ := f5
  obtain ⟨⟨l6, p6⟩, -⟩ := f6
  have c20 := h.atomAt 0 (.copy (.n (val% «verify_tables» "sp[0]@1")) (.n (val% «verify_tables» "fs0"))) (by decide +kernel)
  have c21 := h.atomAt 1 (.copy (.n (val% «verify_tables» "sp[1]@1")) (.n (val% «verify_tables» "fs1"))) (by decide +kernel)
  have c22 := h.atomAt 2 (.copy (.n (val% «verify_tables» "sp[2]@1")) (.n (val% «verify_tables» "fs2"))) (by decide +kernel)
  have c23 := h.atomAt 3 (.copy (.n (val% «verify_tables» "sp[3]@1")) (.n (val% «verify_tables» "fs3"))) (by decide +kernel)
  have c24 := h.atomAt 4 (.copy (.n (val% «verify_tables» "sp[4]@1")) (.n (val% «verify_tables» "fs4"))) (by decide +kernel)
  have k1 := h.atomAt 1914 (.keccak [.n (val% «verify_tables» "rate[0]@1"), .n (val% «verify_tables» "rate[1]@1"), .n (val% «verify_tables» "rate[2]@1"), .n (val% «verify_tables» "rate[3]@1"), .n (val% «verify_tables» "rate[4]@1"), .n (val% «verify_tables» "rate[5]@1"), .n (val% «verify_tables» "rate[6]@1"),
    .n (val% «verify_tables» "rate[7]@1"), .n (val% «verify_tables» "sp[0]@1"), .n (val% «verify_tables» "sp[1]@1"), .n (val% «verify_tables» "sp[2]@1"), .n (val% «verify_tables» "sp[3]@1"), .n (val% «verify_tables» "sp[4]@1")] (vtOuts 1828) false false) (by decide +kernel)
  have z6 := h.atomAt 1927 (.const (.n (val% «verify_tables» "rate[6]@2")) (word 0 0)) (by decide +kernel)
  have z7 := h.atomAt 1928 (.const (.n (val% «verify_tables» "rate[7]@2")) (word 0 0)) (by decide +kernel)
  have k2 := h.atomAt 1929 (.keccak [.n (val% «verify_tables» "rate[0]@2"), .n (val% «verify_tables» "rate[1]@2"), .n (val% «verify_tables» "rate[2]@2"), .n (val% «verify_tables» "rate[3]@2"), .n (val% «verify_tables» "rate[4]@2"), .n (val% «verify_tables» "rate[5]@2"),
    .n (val% «verify_tables» "rate[6]@2"), .n (val% «verify_tables» "rate[7]@2"), .n (val% «verify_tables» "nxt[8]@1"), .n (val% «verify_tables» "nxt[9]@1"), .n (val% «verify_tables» "nxt[10]@1"), .n (val% «verify_tables» "nxt[11]@1"), .n (val% «verify_tables» "nxt[12]@1")] (vtOuts 1855) false false)
    (by decide +kernel)
  have d43 := h.atomAt 1918 (.copy (.n (val% «verify_tables» "bc_msg[0]")) (.n (val% «verify_tables» "x@5"))) (by decide +kernel)
  have d47 := h.atomAt 1922 (.copy (.n (val% «verify_tables» "bc_msg[1]")) (.n (val% «verify_tables» "x@6"))) (by decide +kernel)
  have d51 := h.atomAt 1926 (.copy (.n (val% «verify_tables» "bc_msg[2]")) (.n (val% «verify_tables» "x@7"))) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c20 c21 c22 c23 c24 z6 z7 d43 d47 d51
  obtain ⟨hP1, hC1⟩ := vt_keccak k1
  obtain ⟨hP2, hC2⟩ := vt_keccak k2
  have e0 := fsPackT_cells p0
  have e1 := fsPackT_cells p1
  have e2 := fsPackT_cells p2
  have e3 := fsPackT_cells p3
  have e4 := fsPackT_cells p4
  have e5 := fsPackT_cells p5
  have e6 := fsPackT_cells p6
  -- the four framework words, and their permutation
  set S4 : Fs := ⟨[σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4"))], [(σ (.n (val% «verify_tables» "x@1")), dsObserve),
    (σ (.n (val% «verify_tables» "x@2")), dsObserve), (σ (.n (val% «verify_tables» "x@3")), dsObserve), (σ (.n (val% «verify_tables» "x@4")), dsObserve)]⟩ with hS4d
  have hS4 : (⟨[σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4"))], []⟩ : Fs).absorbAll
      [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2")), σ (.n (val% «verify_tables» "x@3")), σ (.n (val% «verify_tables» "x@4"))] dsObserve = S4 := by
    rw [absorbAll_short _ _ _ (by simp)]; rfl
  have hin1 : ([.n (val% «verify_tables» "rate[0]@1"), .n (val% «verify_tables» "rate[1]@1"), .n (val% «verify_tables» "rate[2]@1"), .n (val% «verify_tables» "rate[3]@1"), .n (val% «verify_tables» "rate[4]@1"), .n (val% «verify_tables» "rate[5]@1"), .n (val% «verify_tables» "rate[6]@1"), .n (val% «verify_tables» "rate[7]@1"), .n (val% «verify_tables» "sp[0]@1"),
      .n (val% «verify_tables» "sp[1]@1"), .n (val% «verify_tables» "sp[2]@1"), .n (val% «verify_tables» "sp[3]@1"), .n (val% «verify_tables» "sp[4]@1")] : List V).map σ = rateOf S4.pend ++ S4.cap := by
    rw [rateOf_eq_cells _ (by simp [hS4d])]
    simp only [hS4d, List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      ← e0, ← e1, ← e2, ← e3, c20, c21, c22, c23, c24]
    rfl
  rw [hin1] at hC1
  have hcap : capOf S4.perm = [σ (.n (val% «verify_tables» "nxt[8]@1")), σ (.n (val% «verify_tables» "nxt[9]@1")), σ (.n (val% «verify_tables» "nxt[10]@1")), σ (.n (val% «verify_tables» "nxt[11]@1")), σ (.n (val% «verify_tables» "nxt[12]@1"))] := by
    rw [Fs.perm, ← hC1]; rfl
  -- the share and the round's coefficients, after the permutation
  set S7 : Fs := ⟨capOf S4.perm, [(σ (.n (val% «verify_tables» "x@5")), dsObserve), (σ (.n (val% «verify_tables» "x@6")), dsObserve),
    (σ (.n (val% «verify_tables» "x@7")), dsObserve)]⟩ with hS7d
  have hS7 : vtFreshFs σ = S7 := by
    have hsplit : vtFreshWords σ = [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2")), σ (.n (val% «verify_tables» "x@3")), σ (.n (val% «verify_tables» "x@4"))] ++
        [σ (.n (val% «verify_tables» "x@5")), σ (.n (val% «verify_tables» "x@6")), σ (.n (val% «verify_tables» "x@7"))] := rfl
    have happ : ∀ (s : Fs) (l1 l2 : List E) (t : ℕ),
        s.absorbAll (l1 ++ l2) t = (s.absorbAll l1 t).absorbAll l2 t := by
      intro s l1 l2 t; simp [Fs.absorbAll, List.foldl_append]
    have h1 : S4.absorb (σ (.n (val% «verify_tables» "x@5"))) dsObserve = ⟨capOf S4.perm, [(σ (.n (val% «verify_tables» "x@5")), dsObserve)]⟩ := by
      simp [Fs.absorb, hS4d, rateScalars]
    rw [vtFreshFs, hsplit, happ, hS4]
    show (S4.absorb (σ (.n (val% «verify_tables» "x@5"))) dsObserve).absorbAll [σ (.n (val% «verify_tables» "x@6")), σ (.n (val% «verify_tables» "x@7"))] dsObserve = S7
    rw [h1, absorbAll_short _ _ _ (by simp)]
    rfl
  have hin2 : ([.n (val% «verify_tables» "rate[0]@2"), .n (val% «verify_tables» "rate[1]@2"), .n (val% «verify_tables» "rate[2]@2"), .n (val% «verify_tables» "rate[3]@2"), .n (val% «verify_tables» "rate[4]@2"), .n (val% «verify_tables» "rate[5]@2"), .n (val% «verify_tables» "rate[6]@2"), .n (val% «verify_tables» "rate[7]@2"), .n (val% «verify_tables» "nxt[8]@1"),
      .n (val% «verify_tables» "nxt[9]@1"), .n (val% «verify_tables» "nxt[10]@1"), .n (val% «verify_tables» "nxt[11]@1"), .n (val% «verify_tables» "nxt[12]@1")] : List V).map σ = rateOf S7.pend ++ S7.cap := by
    rw [rateOf_eq_cells _ (by simp [hS7d])]
    simp only [hS7d, hcap, List.map_cons, List.map_nil, pendCells, List.flatMap_cons,
      List.flatMap_nil, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
      List.append_nil, ← e4, ← e5, ← e6, z6, z7]
    rfl
  rw [hin2] at hP2 hC2
  refine ⟨fun k hk => ?_, ?_, ?_, d43, d47, d51⟩
  · simp only [vtFreshWords, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
    · exact l5
    · exact l6
  · rw [hS7]
    simp only [Fs.squeeze, Fs.perm]
    exact challengeT_value (s0 := .n (val% «verify_tables» "nxt[0]@2")) (b := 1855) rfl (hP2 0 (by omega))
  · rw [hS7]
    simp only [Fs.squeeze, Fs.perm]
    have e : ∀ k, 1855 + 8 + k = 1863 + k := fun k => by omega
    simp only [e] at hC2
    exact hC2

end
end LeanVM.Guest.B1.Tables
