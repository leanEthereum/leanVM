/-
  LeanVM.Guest.B1.Whir.CLq

  `level_queries`, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CPrim
public import LeanVM.Guest.B1.Whir.HelperT

/-!
# `level_queries`, honestly

`lq_complete`: `level_queries` at `q` queries, its hinted cap at `CAP` and flags at `FL` checked up
to the root `(r0, r1)` by `verify_merkle_cap__L{cd}`, its `opening_queries` specialization
relating the cap, the flags, `lam`, `lam^q`, the window pointers, the row weights and `g^iters` to
the queries' sum, returns the root, the sum and `lam^q`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The iterations of `opening_queries` at `q` queries of base `base`. -/
def lqIters (q base : ℕ) : ℕ := if base = 1 then q / 2 else q

/-- `level_queries`' body before its `ret`. -/
def lqAtoms (q base il leaf d cd : ℕ) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits q) 0 9
  let k := 9 + osPowLen q
  osHeap (4 * 2 ^ cd) 3 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n 4) 0 (4 * 2 ^ cd))))] ++
    osHeap (2 ^ cd) 5 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 6) 0 (2 ^ cd)))),
      .call ("verify_merkle_cap__L" ++ natStr cd) [.n 4, .n 6] [.n 7, .n 8]] ++
    pw.1 ++
    [.atom (.const (.n k) (gw (lqIters q base))),
      .call (oqName q base il leaf d cd) [.n 4, .n 6, .n 0, .n pw.2, .n 1, .n 2, .n k] [.n (k + 1)],
      .atom (.copy (.n (k + 2)) (.n 7)), .atom (.copy (.n (k + 3)) (.n 8)),
      .atom (.copy (.n (k + 4)) (.n (k + 1))), .atom (.copy (.n (k + 5)) (.n pw.2))]

theorem lqBody_atoms (q base il leaf d cd : ℕ) : lqBody q base il leaf d cd =
    lqAtoms q base il leaf d cd ++ [.ret [.n (9 + osPowLen q + 2), .n (9 + osPowLen q + 3),
      .n (9 + osPowLen q + 4), .n (9 + osPowLen q + 5)]] := by
  simp [lqBody, lqAtoms, lqIters]

/-- The values of `level_queries`, by segments. -/
def lqSegs (q cd : ℕ) (iters : ℕ) (lam WP RW CAP FL r0 r1 sum : E) : List (ℕ × (ℕ → E)) :=
  [(9, fun i ↦ [lam, WP, RW, gw (4 * 2 ^ cd), CAP, gw (2 ^ cd), FL, r0, r1].getD i 0),
    (osPowLen q, fun i ↦ (powVals lam (osPowDigits q) 1).getD i 0),
    (6, fun i ↦ [gw iters, sum, r0, r1, sum, lam ^ q].getD i 0)]

/-- **`level_queries`, honestly.** -/
theorem lq_complete {name : String} {q base il leaf d cd : ℕ}
    (hfn : FnIs name (osParams 3) (lqBody q base il leaf d cd))
    (hpw : digitsVal (osPowDigits q) 1 = q) {lam WP RW CAP FL r0 r1 sum : E}
    (hcap : coreProgram.Rel rd ("verify_merkle_cap__L" ++ natStr cd) [CAP, FL] [r0, r1])
    (hoq : coreProgram.Rel rd (oqName q base il leaf d cd)
      [CAP, FL, lam, lam ^ q, WP, RW, gw (lqIters q base)] [sum]) :
    coreProgram.Rel rd name [lam, WP, RW] [r0, r1, sum, lam ^ q] := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  set L := osPowLen q with hL
  set segs := lqSegs q cd (lqIters q base) lam WP RW CAP FL r0 r1 sum with hsegs
  set σ := segVal segs with hσ
  have hv : ∀ i, σ (.n i) = segLookup segs i := segVal_n segs
  have sv : ∀ (m : ℕ) (hm : m < segs.length) (o : ℕ), segLen (segs.take m) = o → ∀ i,
      i < segs[m].1 → σ (.n (o + i)) = segs[m].2 i := fun m hm o ho i hi ↦ by
    have := seg_val (σ := σ) (k := 0) (segs := segs) (fun j _ ↦ by rw [Nat.zero_add]; exact hv j)
      m hm o ho i hi
    rwa [Nat.zero_add] at this
  have a : ∀ i < 9, σ (.n i) = [lam, WP, RW, gw (4 * 2 ^ cd), CAP, gw (2 ^ cd), FL, r0, r1].getD i 0 :=
    fun i hi ↦ by
      simpa [hsegs, lqSegs] using sv 0 (by simp [hsegs, lqSegs]) 0 (by simp [segLen]) i
        (by simp [hsegs, lqSegs]; omega)
  have e : ∀ i < 6, σ (.n (9 + L + i)) = [gw (lqIters q base), sum, r0, r1, sum, lam ^ q].getD i 0 :=
    fun i hi ↦ by
      simpa [hsegs, lqSegs] using sv 2 (by simp [hsegs, lqSegs]) (9 + L)
        (by simp [hsegs, lqSegs, segLen, ← hL]) i (by simp [hsegs, lqSegs]; omega)
  have vpw : ∀ j < (powVals (σ (.n 0)) (osPowDigits q) 1).length,
      σ (.n (9 + j)) = (powVals (σ (.n 0)) (osPowDigits q) 1).getD j 0 := fun j hj ↦ by
    have a0 : σ (.n 0) = lam := by simpa using a 0 (by omega)
    rw [a0] at hj ⊢
    simpa [hsegs, lqSegs] using sv 1 (by simp [hsegs, lqSegs]) 9 (by simp [hsegs, lqSegs, segLen])
      j (by simp [hsegs, lqSegs, osPowLen, powVals_length] at hj ⊢; omega)
  have hpwr := osPowSteps_complete (C := coreProgram.Rel rd) (rd := rd) (σ := σ) 0
    (osPowDigits q) 0 9 1 (by rw [pow_one]) vpw
  have a0 : σ (.n 0) = lam := by simpa using a 0 (by omega)
  have a1 : σ (.n 1) = WP := by simpa using a 1 (by omega)
  have a2 : σ (.n 2) = RW := by simpa using a 2 (by omega)
  have a3 : σ (.n 3) = gw (4 * 2 ^ cd) := by simpa using a 3 (by omega)
  have a4 : σ (.n 4) = CAP := by simpa using a 4 (by omega)
  have a5 : σ (.n 5) = gw (2 ^ cd) := by simpa using a 5 (by omega)
  have a6 : σ (.n 6) = FL := by simpa using a 6 (by omega)
  have a7 : σ (.n 7) = r0 := by simpa using a 7 (by omega)
  have a8 : σ (.n 8) = r1 := by simpa using a 8 (by omega)
  rw [hpw, a0] at hpwr
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5
  rw [rel_iff_sem hf]
  refine ⟨σ, ?_, ?_⟩
  · rw [hps]
    simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, a0, a1, a2]
  · rw [hb, lqBody_atoms, holdsList_flat_ret _ (by simp [lqAtoms, osHeap, osPowSteps_all_flat, Stmt.flat])]
    refine ⟨?_, ?_⟩
    · simp only [lqAtoms, allOk_append]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hpwr.1⟩, ?_⟩
      · simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
        exact a3
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      · simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
        exact a5
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil,
          true_and]
        rw [a4, a6, a7, a8]; exact hcap
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil]
        refine ⟨e0, ?_, by rw [e2, a7], by rw [e3, a8], by rw [e4, e1], by rw [e5, hpwr.2]⟩
        rw [a4, a6, a0, a1, a2, hpwr.2, e0, e1]; exact hoq
    · simp only [List.map_cons, List.map_nil]
      rw [e2, e3, e4, e5]

end
end LeanVM.Guest.B1.Whir
