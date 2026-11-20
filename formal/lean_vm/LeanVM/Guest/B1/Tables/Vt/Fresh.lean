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

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The seven words, in their stream order: the memory's two values, the final memory and
bytecode counts, the bytecode share, its first round's `c0` and `c2`. -/
def vtFreshWords (σ : Val) : List E :=
  [σ (.n 814), σ (.n 818), σ (.n 1120), σ (.n 1134), σ (.n 1494), σ (.n 1498), σ (.n 1502)]

/-- The carried sponge after them. -/
def vtFreshFs (σ : Val) : Fs :=
  (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll (vtFreshWords σ)
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
/-- **The bus's first stream words** and the bytecode sumcheck's first challenge (at `1508`),
the sponge's capacity after it (`1516 .. 1520`), and the copies of the share and the first round's
coefficients the round reads. -/
theorem vt_fresh {rd : Reader} {σ : Val} (h : VtH rd σ) :
    TbReadsAt rd (σ (.n 5)) (vtFreshWords σ) ∧
      σ (.n 1508) = (vtFreshFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (1516 + k))) = (vtFreshFs σ).squeeze.2.cap ∧
      σ (.n 1497) = σ (.n 1494) ∧ σ (.n 1501) = σ (.n 1498) ∧ σ (.n 1505) = σ (.n 1502) := by
  obtain ⟨_, f0⟩ := h.sliceAt 789 (fsNextT (.n 5) 0 814) (by decide +kernel)
  obtain ⟨_, f1⟩ := h.sliceAt 794 (fsNextT (.n 5) 1 818) (by decide +kernel)
  obtain ⟨_, f2⟩ := h.sliceAt 1148 (fsNextT (.n 5) 2 1120) (by decide +kernel)
  obtain ⟨_, f3⟩ := h.sliceAt 1163 (fsNextT (.n 5) 3 1134) (by decide +kernel)
  obtain ⟨_, f4⟩ := h.sliceAt 1557 (fsNextT (.n 5) 4 1494) (by decide +kernel)
  obtain ⟨_, f5⟩ := h.sliceAt 1561 (fsNextT (.n 5) 5 1498) (by decide +kernel)
  obtain ⟨_, f6⟩ := h.sliceAt 1565 (fsNextT (.n 5) 6 1502) (by decide +kernel)
  rw [holds_fsNextT] at f0 f1 f2 f3 f4 f5 f6
  obtain ⟨⟨l0, p0⟩, -⟩ := f0
  obtain ⟨⟨l1, p1⟩, -⟩ := f1
  obtain ⟨⟨l2, p2⟩, -⟩ := f2
  obtain ⟨⟨l3, p3⟩, -⟩ := f3
  obtain ⟨⟨l4, p4⟩, -⟩ := f4
  obtain ⟨⟨l5, p5⟩, -⟩ := f5
  obtain ⟨⟨l6, p6⟩, -⟩ := f6
  have c20 := h.atomAt 0 (.copy (.n 20) (.n 0)) (by decide +kernel)
  have c21 := h.atomAt 1 (.copy (.n 21) (.n 1)) (by decide +kernel)
  have c22 := h.atomAt 2 (.copy (.n 22) (.n 2)) (by decide +kernel)
  have c23 := h.atomAt 3 (.copy (.n 23) (.n 3)) (by decide +kernel)
  have c24 := h.atomAt 4 (.copy (.n 24) (.n 4)) (by decide +kernel)
  have k1 := h.atomAt 1556 (.keccak [.n 815, .n 816, .n 819, .n 820, .n 1121, .n 1122, .n 1135,
    .n 1136, .n 20, .n 21, .n 22, .n 23, .n 24] (vtOuts 1481) false false) (by decide +kernel)
  have z6 := h.atomAt 1569 (.const (.n 1506) (word 0 0)) (by decide +kernel)
  have z7 := h.atomAt 1570 (.const (.n 1507) (word 0 0)) (by decide +kernel)
  have k2 := h.atomAt 1571 (.keccak [.n 1495, .n 1496, .n 1499, .n 1500, .n 1503, .n 1504,
    .n 1506, .n 1507, .n 1489, .n 1490, .n 1491, .n 1492, .n 1493] (vtOuts 1508) false false)
    (by decide +kernel)
  have d43 := h.atomAt 1560 (.copy (.n 1497) (.n 1494)) (by decide +kernel)
  have d47 := h.atomAt 1564 (.copy (.n 1501) (.n 1498)) (by decide +kernel)
  have d51 := h.atomAt 1568 (.copy (.n 1505) (.n 1502)) (by decide +kernel)
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
  set S4 : Fs := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 814), dsObserve),
    (σ (.n 818), dsObserve), (σ (.n 1120), dsObserve), (σ (.n 1134), dsObserve)]⟩ with hS4d
  have hS4 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll
      [σ (.n 814), σ (.n 818), σ (.n 1120), σ (.n 1134)] dsObserve = S4 := by
    rw [absorbAll_short _ _ _ (by simp)]; rfl
  have hin1 : ([.n 815, .n 816, .n 819, .n 820, .n 1121, .n 1122, .n 1135, .n 1136, .n 20,
      .n 21, .n 22, .n 23, .n 24] : List V).map σ = rateOf S4.pend ++ S4.cap := by
    rw [rateOf_eq_cells _ (by simp [hS4d])]
    simp only [hS4d, List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      ← e0, ← e1, ← e2, ← e3, c20, c21, c22, c23, c24]
    rfl
  rw [hin1] at hC1
  have hcap : capOf S4.perm = [σ (.n 1489), σ (.n 1490), σ (.n 1491), σ (.n 1492), σ (.n 1493)] := by
    rw [Fs.perm, ← hC1]; rfl
  -- the share and the round's coefficients, after the permutation
  set S7 : Fs := ⟨capOf S4.perm, [(σ (.n 1494), dsObserve), (σ (.n 1498), dsObserve),
    (σ (.n 1502), dsObserve)]⟩ with hS7d
  have hS7 : vtFreshFs σ = S7 := by
    have hsplit : vtFreshWords σ = [σ (.n 814), σ (.n 818), σ (.n 1120), σ (.n 1134)] ++
        [σ (.n 1494), σ (.n 1498), σ (.n 1502)] := rfl
    have happ : ∀ (s : Fs) (l1 l2 : List E) (t : ℕ),
        s.absorbAll (l1 ++ l2) t = (s.absorbAll l1 t).absorbAll l2 t := by
      intro s l1 l2 t; simp [Fs.absorbAll, List.foldl_append]
    have h1 : S4.absorb (σ (.n 1494)) dsObserve = ⟨capOf S4.perm, [(σ (.n 1494), dsObserve)]⟩ := by
      simp [Fs.absorb, hS4d, rateScalars]
    rw [vtFreshFs, hsplit, happ, hS4]
    show (S4.absorb (σ (.n 1494)) dsObserve).absorbAll [σ (.n 1498), σ (.n 1502)] dsObserve = S7
    rw [h1, absorbAll_short _ _ _ (by simp)]
    rfl
  have hin2 : ([.n 1495, .n 1496, .n 1499, .n 1500, .n 1503, .n 1504, .n 1506, .n 1507, .n 1489,
      .n 1490, .n 1491, .n 1492, .n 1493] : List V).map σ = rateOf S7.pend ++ S7.cap := by
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
    exact challengeT_value (s0 := .n 1508) (b := 1508) rfl (hP2 0 (by omega))
  · rw [hS7]
    simp only [Fs.squeeze, Fs.perm]
    have e : ∀ k, 1508 + 8 + k = 1516 + k := fun k => by omega
    simp only [e] at hC2
    exact hC2

end
end LeanVM.Guest.B1.Tables
