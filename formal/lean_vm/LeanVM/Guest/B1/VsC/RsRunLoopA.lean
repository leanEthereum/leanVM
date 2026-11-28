/-
  LeanVM.Guest.B1.VsC.RsRunLoopA

  `rs_eq_rows__L{n}` and `rs_eq_run`'s loop complete placed.
-/

module

public import LeanVM.Guest.B1.VsC.LoopLeafA
public import LeanVM.Guest.B1.VsC.FreeC
public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Complete.LeafA
import LeanVM.Guest.CoreRef

/-!
# `rs_eq_rows` and `rs_eq_run_loop0`, placed

`rs_eq_rows__L{n}(row, zs, ps)`, `n ≤ 8`, a straight leaf with no words of its own, reads the `64`
words at `row` and `n` at `zs`, `ps`, and stores the next row at `row·g^64` (`rs_eq_rows_placed`:
its free completeness, `callAtA_leaf0`). `rs_eq_run_loop0` is `LoopLeafA.lean`'s template with the
leaf `rs_eq_rows__L8` and stride `64` (`rrl_T`); it is free, so it completes where its relation
holds (`loop_rel_iff`, from each iteration's leaf meaning, `rrl_complete0`), and is placed by its
shape (`rrl_placed`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `rs_eq_rows__L{n}` -/

set_option maxRecDepth 100000 in
theorem rsr_fn_0 : coreProgram.find? (rsEqRowsNames.getD 0 "") = some fn% «rs_eq_rows__L0» ∧
    (fn% «rs_eq_rows__L0»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L0»).body).all (loadInB [(0, 128), (1, 0), (2, 0)]) = true ∧
    (retOf (fn% «rs_eq_rows__L0»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 0 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L0») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_1 : coreProgram.find? (rsEqRowsNames.getD 1 "") = some fn% «rs_eq_rows__L1» ∧
    (fn% «rs_eq_rows__L1»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L1»).body).all (loadInB [(0, 128), (1, 1), (2, 1)]) = true ∧
    (retOf (fn% «rs_eq_rows__L1»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 1 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L1») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_2 : coreProgram.find? (rsEqRowsNames.getD 2 "") = some fn% «rs_eq_rows__L2» ∧
    (fn% «rs_eq_rows__L2»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L2»).body).all (loadInB [(0, 128), (1, 2), (2, 2)]) = true ∧
    (retOf (fn% «rs_eq_rows__L2»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 2 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L2») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_3 : coreProgram.find? (rsEqRowsNames.getD 3 "") = some fn% «rs_eq_rows__L3» ∧
    (fn% «rs_eq_rows__L3»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L3»).body).all (loadInB [(0, 128), (1, 3), (2, 3)]) = true ∧
    (retOf (fn% «rs_eq_rows__L3»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 3 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L3») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_4 : coreProgram.find? (rsEqRowsNames.getD 4 "") = some fn% «rs_eq_rows__L4» ∧
    (fn% «rs_eq_rows__L4»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L4»).body).all (loadInB [(0, 128), (1, 4), (2, 4)]) = true ∧
    (retOf (fn% «rs_eq_rows__L4»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 4 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L4») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_5 : coreProgram.find? (rsEqRowsNames.getD 5 "") = some fn% «rs_eq_rows__L5» ∧
    (fn% «rs_eq_rows__L5»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L5»).body).all (loadInB [(0, 128), (1, 5), (2, 5)]) = true ∧
    (retOf (fn% «rs_eq_rows__L5»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 5 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L5») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_6 : coreProgram.find? (rsEqRowsNames.getD 6 "") = some fn% «rs_eq_rows__L6» ∧
    (fn% «rs_eq_rows__L6»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L6»).body).all (loadInB [(0, 128), (1, 6), (2, 6)]) = true ∧
    (retOf (fn% «rs_eq_rows__L6»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 6 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L6») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_7 : coreProgram.find? (rsEqRowsNames.getD 7 "") = some fn% «rs_eq_rows__L7» ∧
    (fn% «rs_eq_rows__L7»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L7»).body).all (loadInB [(0, 128), (1, 7), (2, 7)]) = true ∧
    (retOf (fn% «rs_eq_rows__L7»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 7 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L7») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn_8 : coreProgram.find? (rsEqRowsNames.getD 8 "") = some fn% «rs_eq_rows__L8» ∧
    (fn% «rs_eq_rows__L8»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows__L8»).body).all (loadInB [(0, 128), (1, 8), (2, 8)]) = true ∧
    (retOf (fn% «rs_eq_rows__L8»).body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD 8 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows__L8») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rsr_fn : ∀ n ≤ 8, ∃ f : Fn, coreProgram.find? (rsEqRowsNames.getD n "") = some f ∧
    f.params = [.n 0, .n 1, .n 2] ∧ (atomsOf f.body).all (loadInB [(0, 128), (1, n), (2, n)]) = true ∧
    (retOf f.body).isSome = true ∧ coreProgram.loop (rsEqRowsNames.getD n "") = false := by
  intro n hn
  interval_cases n
  exacts [⟨_, rsr_fn_0⟩, ⟨_, rsr_fn_1⟩, ⟨_, rsr_fn_2⟩, ⟨_, rsr_fn_3⟩, ⟨_, rsr_fn_4⟩, ⟨_, rsr_fn_5⟩, ⟨_, rsr_fn_6⟩, ⟨_, rsr_fn_7⟩, ⟨_, rsr_fn_8⟩]

set_option maxRecDepth 100000 in
theorem rsr_pureIn : coreProgram.PureIn rsEqRowsNames := Tables.pureIn_of_pureInB (by decide +kernel)

theorem rsr_mem {n : ℕ} (hn : n ≤ 8) : rsEqRowsNames.getD n "" ∈ rsEqRowsNames := by
  rw [List.getD_eq_getElem _ _ (by change n < 9; omega)]; exact List.getElem_mem _

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem rsr_ptr {n : ℕ} {row z p : E} {R : ℕ → Prop} (hrow : PtrCells R row 128) (hz : PtrCells R z n)
    (hp : PtrCells R p n) : ∀ q ∈ [(0, 128), (1, n), (2, n)], ∀ off < q.2,
      ∃ i, ([row, z, p].getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  exacts [hrow, hz, hp]

/-- **`rs_eq_rows__L{n}` completes placed**, `n ≤ 8`, where its meaning holds. -/
theorem rs_eq_rows_placed (kd : ℕ) {n : ℕ} (hn : n ≤ 8) {row z p : E} {rets : List E} {R : ℕ → Prop}
    (hrow : PtrCells R row 128) (hz : PtrCells R z n) (hp : PtrCells R p n) (fp c : ℕ) :
    CallAtA fs al cert kd (rsEqRowsNames.getD n "") [row, z, p] rets R (fun _ => False) (fun _ => True)
      (fun rd => MeaningRsEqRows n rd [row, z, p] rets) PostQuiet (fs (rsEqRowsNames.getD n "")) fp c c := by
  obtain ⟨f, hf, hpa, hL, hr, hlp⟩ := rsr_fn n hn
  exact callAtA_leaf0 rsr_pureIn (rsr_mem hn) hlp hf (by rw [hpa]; rfl) hL hr
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> simp)
    (rsr_ptr hrow hz hp)
    ((callCompletes0_free coreProgram_wf (rs_eq_rows_free n (by omega)).1 (rs_eq_rows_free n (by omega)).2
      fun rd _ h => (rs_eq_rows_holds n hn rd _ _).mpr h).mono (fun _ h => h) fun _ _ _ h => h) fp c

/-- **Every valid tree of `rs_eq_rows__L{n}`** has its leaf shape. -/
theorem rsr_shapeR {n : ℕ} (hn : n ≤ 8) {row z p : E} {R : ℕ → Prop} (hrow : PtrCells R row 128)
    (hz : PtrCells R z n) (hp : PtrCells R p n) {rd : Reader} {t : Tree} {rets : List E}
    (hn' : t.name = rsEqRowsNames.getD n "") (hv : t.Valid coreProgram rd [row, z, p] rets)
    (hb : t.BufsOk coreProgram) : LlShape fs al (fs (rsEqRowsNames.getD n "")) id R t := by
  obtain ⟨f, hf, hpa, hL, hr, hlp⟩ := rsr_fn n hn
  exact leaf_shapeR rsr_pureIn (rsr_mem hn) hf hlp (by rw [hpa]; rfl) hL hr
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> simp)
    (rsr_ptr hrow hz hp) hn' hv hb

/-! ## `rs_eq_run_loop0` -/

/-- The loop's multiplications: `x^8`, `x^64`, the leaf's arguments. -/
def rrlA : List Atom :=
  [.mul (.n 5) (.n 0) (.n 0), .mul (.n 6) (.n 5) (.n 5), .mul (.n 7) (.n 6) (.n 6), .mul (.n 8) (.n 0) (.n 0),
    .mul (.n 9) (.n 8) (.n 8), .mul (.n 10) (.n 9) (.n 9), .mul (.n 11) (.n 10) (.n 10),
    .mul (.n 12) (.n 11) (.n 11), .mul (.n 13) (.n 12) (.n 12), .mul (.n 14) (.n 2) (.n 13),
    .mul (.n 15) (.n 3) (.n 7), .mul (.n 16) (.n 4) (.n 7)]

set_option maxRecDepth 100000 in
theorem rrl_T : LoopT name% «rs_eq_run_loop0» "rs_eq_rows__L8" rrlA 64 fn% «rs_eq_run_loop0» where
  find := find_loop5
  params := rfl
  body := stmtsEqb_sound (by decide +kernel)
  loop := by decide +kernel
  muls := rfl
  args := by
    intro rd σ h
    have m : ∀ d x y, Atom.mul (.n d) (.n x) (.n y) ∈ rrlA → σ (.n d) = σ (.n x) * σ (.n y) :=
      fun d x y hm => h _ hm
    rw [m 14 2 13 (by simp [rrlA]), m 15 3 7 (by simp [rrlA]), m 16 4 7 (by simp [rrlA]),
      m 13 12 12 (by simp [rrlA]), m 12 11 11 (by simp [rrlA]), m 11 10 10 (by simp [rrlA]),
      m 10 9 9 (by simp [rrlA]), m 9 8 8 (by simp [rrlA]), m 8 0 0 (by simp [rrlA]),
      m 7 6 6 (by simp [rrlA]), m 6 5 5 (by simp [rrlA]), m 5 0 0 (by simp [rrlA])]
    refine ⟨by ring, by ring, by ring⟩

set_option maxRecDepth 100000 in
theorem rrl_free : NoWitG name% «rs_eq_run_loop0» ∧ ExactFreeG name% «rs_eq_run_loop0» :=
  free_of (by decide +kernel : freeAt name% «rs_eq_run_loop0» idx% «rs_eq_run_loop0» = true)

set_option maxRecDepth 100000 in
theorem rrl_pureIn : coreProgram.PureIn [name% «rs_eq_run_loop0», "rs_eq_rows__L8"] :=
  Tables.pureIn_of_pureInB (by decide +kernel)

/-- What the loop from iteration `j` of `q` asks: each later iteration's leaf meaning. -/
def RrlPre (q j : ℕ) (chain z p : E) (rd : Reader) : Prop :=
  ∀ t, j ≤ t → t < q → MeaningRsEqRows 8 rd (llArgs 64 t chain z p) [chain * (gen ^ t) ^ 64 * gen ^ 64]

/-- **`rs_eq_run_loop0` completes** from iteration `j < q` where its leaves' meanings hold. -/
theorem rrl_complete0 (kd : ℕ) {q j : ℕ} (hq : q < 2 ^ 30) (hj : j < q) (chain z p : E) :
    CallCompletes0 kd name% «rs_eq_run_loop0» [gen ^ j, gen ^ q, chain, z, p] [] (RrlPre q j chain z p)
      PostQuiet :=
  (callCompletes0_free coreProgram_wf rrl_free.1 rrl_free.2 fun rd _ hP =>
    (loop_rel_iff (P := coreProgram) (f := name% «rs_eq_run_loop0») (ps := [gen ^ q, chain, z, p])
      (N := gen ^ q) (B := L5Body rd chain z p) (fun d x h => loop5_sound rd _ _ _ _ d x h)
      (fun x hb hk hn => loop5_complete rd _ _ _ _ x hb hk hn) j).mpr
      ⟨q, hj, rfl, fun t h1 h2 he => absurd (gen_pow_inj (by omega) (by omega) he) (by omega),
        fun t h1 h2 => ⟨_, (rs_eq_rows_holds 8 le_rfl rd _ _).mpr (hP t h1 h2)⟩⟩).mono
    (fun _ h => h) fun _ _ _ h => h

theorem ptrCells_row {R : ℕ → Prop} {x : E} {n t s : ℕ} (h : PtrCells R x n) (hs : t * 64 + s ≤ n) :
    PtrCells R (x * (gen ^ t) ^ 64) s := by
  rw [← pow_mul]; exact ptrCells_shift h hs

theorem ptrCells_coord {R : ℕ → Prop} {x : E} {n t s : ℕ} (h : PtrCells R x n) (hs : t * 8 + s ≤ n) :
    PtrCells R (x * (gen ^ t) ^ 8) s := by
  rw [← pow_mul]; exact ptrCells_shift h hs

/-- **`rs_eq_run_loop0` completes placed** from iteration `j < q`: its leaves read the chain's rows
`j ..= q` and the coordinates below `8 q`, cells of `R`. -/
theorem rrl_placed {k q j : ℕ} (hq : q < 2 ^ 30) (hj : j < q) {chain z p : E} {R : ℕ → Prop}
    (hc : PtrCells R chain (64 * (q + 1))) (hz : PtrCells R z (8 * q)) (hp : PtrCells R p (8 * q)) (fp c : ℕ) :
    CallAtA fs al cert k name% «rs_eq_run_loop0» [gen ^ j, gen ^ q, chain, z, p] [] R (fun _ => False)
      (fun _ => True) (RrlPre q j chain z p) PostQuiet (llBlk fs name% «rs_eq_run_loop0» q j) fp c
      (llEnd fs al "rs_eq_rows__L8" q j c) :=
  ll_placed rrl_T rrl_pureIn hq hj (fun t ht rd t1 rets hn hv hb =>
    rsr_shapeR (n := 8) le_rfl (ptrCells_row hc (by omega)) (ptrCells_coord hz (by omega))
      (ptrCells_coord hp (by omega)) hn hv hb) (rrl_complete0 k hq hj chain z p) fp c

end
end LeanVM.Guest.B1.VsC
