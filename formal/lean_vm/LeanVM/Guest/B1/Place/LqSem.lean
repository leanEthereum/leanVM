/-
  LeanVM.Guest.B1.Place.LqSem

  `level_queries`' body under its honest valuation, for any call relation.
-/

module

public import LeanVM.Guest.B1.Whir.CLq
public import LeanVM.Guest.Memory.Uniform

/-!
# `level_queries`' body, its valuation

`lqVal`: the valuation `lq_complete` builds, from the cap's and flags' pointers chosen by the
caller (the allocator's, when placed). `lqVal_facts`: its parameters, its `HeapBuf`s' sizes and
pointers, its two calls' arguments and returns; `lqVal_holds`: the body holds of it for any call
relation that holds of those two calls. `lqAtoms_straight`, `lqAtoms_addrs`, `lqAtoms_calls`,
`lqAtoms_allocs`: the body is straight-line, places no frame run, makes the two calls and
allocates the two buffers.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `level_queries`' honest valuation. -/
noncomputable def lqVal (q cd iters : ℕ) (lam WP RW CAP FL r0 r1 sum : E) : Val :=
  segVal (lqSegs q cd iters lam WP RW CAP FL r0 r1 sum)

/-- The arguments of `level_queries`' call of `opening_queries`. -/
def lqOqArgs (q : ℕ) : List V :=
  [.n 4, .n 6, .n 0, .n (osPowSteps 0 (osPowDigits q) 0 9).2, .n 1, .n 2, .n (9 + osPowLen q)]

/-- **The honest valuation's words**: the parameters, the `HeapBuf`s' sizes and pointers, the
calls' arguments and returns, the copies returned, and `λ^q` by the power steps. -/
theorem lqVal_facts {C : CallRel} {rd : Reader} (q cd iters : ℕ)
    (hpw : digitsVal (osPowDigits q) 1 = q) (lam WP RW CAP FL r0 r1 sum : E) :
    let σ := lqVal q cd iters lam WP RW CAP FL r0 r1 sum
    let L := osPowLen q
    σ (.n 0) = lam ∧ σ (.n 1) = WP ∧ σ (.n 2) = RW ∧ σ (.n 3) = gw (4 * 2 ^ cd) ∧
      σ (.n 4) = CAP ∧ σ (.n 5) = gw (2 ^ cd) ∧ σ (.n 6) = FL ∧ σ (.n 7) = r0 ∧ σ (.n 8) = r1 ∧
      σ (.n (9 + L)) = gw iters ∧ σ (.n (9 + L + 1)) = sum ∧ σ (.n (9 + L + 2)) = r0 ∧
      σ (.n (9 + L + 3)) = r1 ∧ σ (.n (9 + L + 4)) = sum ∧ σ (.n (9 + L + 5)) = lam ^ q ∧
      σ (.n (osPowSteps 0 (osPowDigits q) 0 9).2) = lam ^ q ∧
      AllOk C rd σ (osPowSteps 0 (osPowDigits q) 0 9).1 := by
  intro σ L
  set segs := lqSegs q cd iters lam WP RW CAP FL r0 r1 sum with hsegs
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
  have e : ∀ i < 6, σ (.n (9 + L + i)) = [gw iters, sum, r0, r1, sum, lam ^ q].getD i 0 :=
    fun i hi ↦ by
      simpa [hsegs, lqSegs] using sv 2 (by simp [hsegs, lqSegs]) (9 + L)
        (by simp [hsegs, lqSegs, segLen, L]) i (by simp [hsegs, lqSegs]; omega)
  have a0 : σ (.n 0) = lam := by simpa using a 0 (by omega)
  have vpw : ∀ j < (powVals (σ (.n 0)) (osPowDigits q) 1).length,
      σ (.n (9 + j)) = (powVals (σ (.n 0)) (osPowDigits q) 1).getD j 0 := fun j hj ↦ by
    rw [a0] at hj ⊢
    simpa [hsegs, lqSegs] using sv 1 (by simp [hsegs, lqSegs]) 9 (by simp [hsegs, lqSegs, segLen])
      j (by simp [hsegs, lqSegs, osPowLen, powVals_length] at hj ⊢; omega)
  have hpwr := osPowSteps_complete (C := C) (rd := rd) (σ := σ) 0
    (osPowDigits q) 0 9 1 (by rw [pow_one]) vpw
  rw [hpw, a0] at hpwr
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5
  exact ⟨a0, by simpa using a 1 (by omega), by simpa using a 2 (by omega),
    by simpa using a 3 (by omega), by simpa using a 4 (by omega), by simpa using a 5 (by omega),
    by simpa using a 6 (by omega), by simpa using a 7 (by omega), by simpa using a 8 (by omega),
    e0, e1, e2, e3, e4, e5, hpwr.2, hpwr.1⟩

theorem osPowSteps_all_straight (x : ℕ) : ∀ ds acc k,
    (osPowSteps x ds acc k).1.all Main.Stmt.straight = true
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    cases d <;> simp [osPowSteps, osPowSteps_all_straight x ds, Main.Stmt.straight]

theorem lqAtoms_eq (q base il leaf d cd : ℕ) : lqAtoms q base il leaf d cd =
    osHeap (4 * 2 ^ cd) 3 ++
      [.atom (.hint (.witness "merkle_caps" (.heap (.n 4) 0 (4 * 2 ^ cd))))] ++
      osHeap (2 ^ cd) 5 ++
      [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 6) 0 (2 ^ cd)))),
        .call ("verify_merkle_cap__L" ++ natStr cd) [.n 4, .n 6] [.n 7, .n 8]] ++
      (osPowSteps 0 (osPowDigits q) 0 9).1 ++
      [.atom (.const (.n (9 + osPowLen q)) (gw (lqIters q base))),
        .call (oqName q base il leaf d cd) (lqOqArgs q) [.n (9 + osPowLen q + 1)],
        .atom (.copy (.n (9 + osPowLen q + 2)) (.n 7)), .atom (.copy (.n (9 + osPowLen q + 3)) (.n 8)),
        .atom (.copy (.n (9 + osPowLen q + 4)) (.n (9 + osPowLen q + 1))),
        .atom (.copy (.n (9 + osPowLen q + 5)) (.n (osPowSteps 0 (osPowDigits q) 0 9).2))] := rfl

/-- The body's statements are straight-line. -/
theorem lqAtoms_straight (q base il leaf d cd : ℕ) :
    (lqAtoms q base il leaf d cd).all Main.Stmt.straight = true := by
  rw [lqAtoms_eq]
  simp [osHeap, osPowSteps_all_straight 0 (osPowDigits q) 0 9, Main.Stmt.straight]

theorem osPowSteps_filterMap {β : Type} (f : Stmt → Option β)
    (hf : ∀ a b c, f (.atom (.mul a b c)) = none)
    (x : ℕ) : ∀ ds acc k, (osPowSteps x ds acc k).1.filterMap f = []
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    cases d <;> simp [osPowSteps, osPowSteps_filterMap f hf x ds, hf]

/-- The body places no frame run. -/
theorem lqAtoms_addrs (q base il leaf d cd : ℕ) :
    (lqAtoms q base il leaf d cd).filterMap Main.Stmt.addrS = [] := by
  rw [lqAtoms_eq]
  simp only [List.filterMap_append, osPowSteps_filterMap Main.Stmt.addrS (fun _ _ _ ↦ rfl)]
  rfl

/-- The body's two calls. -/
theorem lqAtoms_calls (q base il leaf d cd : ℕ) :
    (lqAtoms q base il leaf d cd).filterMap Main.Stmt.callS =
      [(none, "verify_merkle_cap__L" ++ natStr cd, [V.n 4, V.n 6], [V.n 7, V.n 8]),
        (none, oqName q base il leaf d cd, lqOqArgs q, [V.n (9 + osPowLen q + 1)])] := by
  rw [lqAtoms_eq]
  simp only [List.filterMap_append, osPowSteps_filterMap Main.Stmt.callS (fun _ _ _ ↦ rfl)]
  rfl

/-- The body's two `HeapBuf`s. -/
theorem lqAtoms_allocs (q base il leaf d cd : ℕ) :
    (lqAtoms q base il leaf d cd).filterMap Main.Stmt.allocSz =
      [(V.n 4, .inr (V.n 3)), (V.n 6, .inr (V.n 5))] := by
  rw [lqAtoms_eq]
  simp only [List.filterMap_append, osPowSteps_filterMap Main.Stmt.allocSz (fun _ _ _ ↦ rfl)]
  rfl

/-- **The body holds of the honest valuation**, for any call relation holding of its two calls. -/
theorem lqVal_holds {C : CallRel} {rd : Reader} (q base il leaf d cd : ℕ)
    (hpw : digitsVal (osPowDigits q) 1 = q) {lam WP RW CAP FL r0 r1 sum : E}
    (hcap : C ("verify_merkle_cap__L" ++ natStr cd) [CAP, FL] [r0, r1])
    (hoq : C (oqName q base il leaf d cd) [CAP, FL, lam, lam ^ q, WP, RW, gw (lqIters q base)]
      [sum]) :
    Stmt.HoldsList C rd (lqVal q cd (lqIters q base) lam WP RW CAP FL r0 r1 sum)
      (lqBody q base il leaf d cd) False (fun rs ↦ rs = [r0, r1, sum, lam ^ q]) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, e0, e1, e2, e3, e4, e5, hp2, hp1⟩ :=
    lqVal_facts (C := C) (rd := rd) q cd (lqIters q base) hpw lam WP RW CAP FL r0 r1 sum
  rw [lqBody_atoms, holdsList_flat_ret _ (by simp [lqAtoms, osHeap, osPowSteps_all_flat, Stmt.flat])]
  refine ⟨?_, by simp only [List.map_cons, List.map_nil, e2, e3, e4, e5]⟩
  rw [lqAtoms_eq]
  simp only [allOk_append]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hp1⟩, ?_⟩
  · simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact a3
  · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  · simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact a5
  · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil,
      true_and]
    rw [a4, a6, a7, a8]; exact hcap
  · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil,
      lqOqArgs]
    refine ⟨e0, ?_, by rw [e2, a7], by rw [e3, a8], by rw [e4, e1], by rw [e5, hp2]⟩
    rw [a4, a6, a0, a1, a2, hp2, e0, e1]; exact hoq

end
end LeanVM.Guest.B1.Whir
