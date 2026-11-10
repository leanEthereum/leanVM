import Rv64Verifier.Proofs.Walk.R17D
import Rv64Verifier.Proofs.Walk.TailModel
import Rv64Verifier.Proofs.Walk.Keeps
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.Hash.Mem

/-!
# `walk` R17: what `table_sumcheck` reads, as the mirror's values

`tablePhase_run`: the table phase is `sample`, then `tableSumcheckM` on `xi`'s five powers split
at two. The congruences: memory `walk` allocated before `u₀`, unchanged, reads the same tables,
heights, forms and point (`formRowsAt_congr`); `evalRowsOf`: the `Vec` a `RowsAt` describes.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

theorem nConstraints_two :
    (LayoutMirror.tablesRust.map LayoutMirror.TableRust.nConstraints).sum = 2 := by
  rw [LayoutMirror.tablesRust_nConstraints]; rfl

theorem tablePhase_run (layout : LayoutMirror.LayoutRust) (bus : BusResultRust)
    (htab : layout.tables = LayoutMirror.tablesRust) (T : TState) :
    (tablePhaseRust layout bus).run T = (TM.sample.run T).bind fun p ↦
      (tableSumcheckM tables layout.tableLogHeights bus.forms ((powers p.1 5).take 2)
        ((powers p.1 5).drop 2) bus.point (dotRust ((powers p.1 5).drop 2) bus.totals)).run p.2 := by
  unfold tablePhaseRust
  rw [htab, nConstraints_two, StateT.run_bind]
  rfl

theorem tables_length : tables.length = 6 := rfl

theorem tablesAt_eq {w : MachineState} {a : Word}
    (h : ∀ i < 6, w.getMem (a + BitVec.ofNat 64 (80 * i + 72)) = BitVec.ofNat 64 i) :
    tablesAt w a 6 = tables := by
  apply List.ext_getElem (by simp [tablesAt, tables_length])
  intro i h1 h2
  simp only [tablesAt, List.length_map, List.length_range] at h1
  simp only [tablesAt, List.getElem_map, List.getElem_range, h i h1,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  rw [List.getD_eq_getElem _ _ (by rw [tables_length]; exact h1)]

/-- The rows of the `Vec<(Vec<E>, Vec<E>)>` at `a`. -/
def evalRowsOf (t : MachineState) (a : Word) : List (List E × List E) :=
  (List.range (vecLen t a).toNat).map fun i ↦
    (vecEs t (vecPtr t a + BitVec.ofNat 64 (48 * i)),
      vecEs t (vecPtr t a + BitVec.ofNat 64 (48 * i + 24)))

theorem RowsAt.eq {s t : MachineState} {a : Word} {rows : List (List E × List E)}
    (h : RowsAt s t a rows) : rows = evalRowsOf t a := by
  apply List.ext_getElem (by simp [evalRowsOf, h.len])
  intro i h1 h2
  obtain ⟨p1, p2⟩ := h.pairs i h1
  simp only [evalRowsOf, List.getElem_map, List.getElem_range]
  rw [p1.elems, p2.elems]

theorem formRowsAt_congr {w u : MachineState} {N : Nat}
    (hm : ∀ x : Word, x.toNat + 8 ≤ N → w.getMem x = u.getMem x) (hN : N ≤ 2 ^ 63) {F : Word}
    {n : Nat} (hF : F.toNat + 24 * n ≤ N)
    (hrow : ∀ i < n, (vecPtr u (F + BitVec.ofNat 64 (24 * i))).toNat +
      24 * (vecLen u (F + BitVec.ofNat 64 (24 * i))).toNat ≤ N)
    (hterm : ∀ i < n, ∀ j < (vecLen u (F + BitVec.ofNat 64 (24 * i))).toNat,
      (vecPtr u (vecPtr u (F + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j))).toNat +
        48 * (vecLen u (vecPtr u (F + BitVec.ofNat 64 (24 * i)) +
          BitVec.ofNat 64 (24 * j))).toNat ≤ N) :
    formRowsAt w F n = formRowsAt u F n := by
  unfold formRowsAt
  refine List.map_congr_left fun i hi ↦ ?_
  simp only [List.mem_range] at hi
  have hv (a : Word) (ha : a.toNat + 24 ≤ N) : vecPtr w a = vecPtr u a ∧ vecLen w a = vecLen u a :=
    ⟨hm _ (by addr_omega [ha, hN]), hm _ (by addr_omega [ha, hN])⟩
  obtain ⟨e1, e2⟩ := hv (F + BitVec.ofNat 64 (24 * i)) (by addr_omega [hF, hi, hN])
  unfold formVecAt
  rw [e1, e2]
  refine List.map_congr_left fun j hj ↦ ?_
  simp only [List.mem_range] at hj
  have hr := hrow i hi
  obtain ⟨e3, e4⟩ := hv (vecPtr u (F + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j))
    (by addr_omega [hr, hj, hN])
  unfold formAt
  rw [e3, e4]
  have ht := hterm i hi j hj
  congr 2
  unfold termsAt
  refine List.map_congr_left fun k hk ↦ ?_
  simp only [List.mem_range] at hk
  set X := vecPtr u (vecPtr u (F + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j)) +
    BitVec.ofNat 64 (48 * k) with hX
  have g (c : Nat) (hc : c ≤ 40) (y : Word) (hy : y = X + BitVec.ofNat 64 c) :
      w.getMem y = u.getMem y := by
    subst hy; exact hm _ (by rw [hX]; addr_omega [ht, hk, hc, hN])
  simp only [monoAt, eAt, g 0 (by omega) X (by rw [add_ofNat_zero]),
    g 8 (by omega) (X + 8) rfl, g 16 (by omega) (X + 16) rfl, g 24 (by omega) (X + 24) rfl,
    g 32 (by omega) (X + 24 + 8) (by bv_omega), g 40 (by omega) (X + 24 + 16) (by bv_omega)]

end Rv64Verifier.Proofs.Walk
