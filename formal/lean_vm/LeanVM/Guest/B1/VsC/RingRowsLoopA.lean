/-
  LeanVM.Guest.B1.VsC.RingRowsLoopA

  `rs_eq_rows_all__L{n}`'s layout-free completeness and `ring_rows`' loop, placed.
-/

module

public import LeanVM.Guest.B1.VsC.LoopLeafA
public import LeanVM.Guest.B1.VsC.RsRowsAllA
public import LeanVM.Guest.B1.Eq.RingRows
public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Complete.LeafA
import LeanVM.Guest.CoreRef

/-!
# `rs_eq_rows_all` and `ring_rows_loop0`, placed

* `callCompletes0_of_callAtA2`: a call placed with every frame two words (its header) and its cursor
  not moving claims no word, so its placed completeness is layout-free completeness. On
  `rs_eq_rows_all_placed'` (any `fs`), `rra_complete0`: `rs_eq_rows_all__L{n}` completes on every
  memory holding its words (`RraPre`), whence its relation (`Tree.Valid.rel`).
* `ring_rows_loop0` is `LoopLeafA.lean`'s template with the leaf `rs_eq_rows_all__L8` and stride
  `512` (`rrg_T`); it is free, so it completes where its relation holds (`loop_rel_iff`, each
  iteration's relation from `rra_complete0`), and is placed by its shape (`rrg_placed`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- **A call placed with two-word frames and no cursor words completes layout-free.** -/
theorem callCompletes0_of_callAtA2 {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop} {fp c : ℕ}
    (h : CallAtA (fun _ => 2) al cert k f args rets R D Out Pre Post 2 fp c c) :
    CallCompletes0 k f args rets Pre Post := by
  intro rd hl hp
  obtain ⟨W, hW, -, -, hr⟩ := h
  have hw : HoldsWords rd W := by
    intro q hq
    have hlen : q.2 = [] := by
      rcases hW.1 q hq with h' | h' <;> exact List.eq_nil_of_length_eq_zero (by omega)
    rw [hlen]; exact readsAt_nil _ _
  obtain ⟨t, hn, hv, hb, -, -, -, -, -, -, hq⟩ := hr rd hl hw hp
  exact ⟨t, hn, hv, hb, hq⟩

/-- What `rs_eq_rows_all__L{n}` reads at `row`, `z`, `p` and the rows it stores past `row`. -/
def RraPre (row z p : E) (zs ps c : List E) (n : ℕ) (rd : Reader) : Prop :=
  ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd row c ∧
    ∀ i < n, ∀ k < 64, LoadHolds rd row (64 * (i + 1) + k)
      (ringRow (c.getD k 0) (zs.take (i + 1)) (ps.take (i + 1)) k)

/-- **`rs_eq_rows_all__L{n}` completes layout-free** on its arrays' cells. -/
theorem rra_complete0 (k : ℕ) {n : ℕ} (h8 : n ≤ 8) {row z p : E} {zs ps c : List E} (hzs : zs.length = n)
    (hps : ps.length = n) (hc : c.length = 64) {R : ℕ → Prop} (hrow : PtrCells R row (64 * (n + 1)))
    (hz : PtrCells R z n) (hp : PtrCells R p n) :
    CallCompletes0 k (rsEqRowsAllNames.getD n "") [row, z, p] [0] (RraPre row z p zs ps c n) PostQuiet :=
  callCompletes0_of_callAtA2 (rs_eq_rows_all_placed' (fs := fun _ => 2) (al := fun _ => false)
    (cert := fun _ _ => 0) (k := k) n h8 hzs hps hc ⟨hrow, hz, hp⟩ 0 0)

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem rra_fn_0 : coreProgram.find? (rsEqRowsAllNames.getD 0 "") = some fn% «rs_eq_rows_all__L0» ∧
    (fn% «rs_eq_rows_all__L0»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L0»).body).all (loadInB [(0, 64 * (0 + 1)), (1, 0), (2, 0)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L0»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 0 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L0») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_1 : coreProgram.find? (rsEqRowsAllNames.getD 1 "") = some fn% «rs_eq_rows_all__L1» ∧
    (fn% «rs_eq_rows_all__L1»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L1»).body).all (loadInB [(0, 64 * (1 + 1)), (1, 1), (2, 1)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L1»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 1 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L1») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_2 : coreProgram.find? (rsEqRowsAllNames.getD 2 "") = some fn% «rs_eq_rows_all__L2» ∧
    (fn% «rs_eq_rows_all__L2»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L2»).body).all (loadInB [(0, 64 * (2 + 1)), (1, 2), (2, 2)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L2»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 2 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L2») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_3 : coreProgram.find? (rsEqRowsAllNames.getD 3 "") = some fn% «rs_eq_rows_all__L3» ∧
    (fn% «rs_eq_rows_all__L3»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L3»).body).all (loadInB [(0, 64 * (3 + 1)), (1, 3), (2, 3)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L3»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 3 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L3») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_4 : coreProgram.find? (rsEqRowsAllNames.getD 4 "") = some fn% «rs_eq_rows_all__L4» ∧
    (fn% «rs_eq_rows_all__L4»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L4»).body).all (loadInB [(0, 64 * (4 + 1)), (1, 4), (2, 4)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L4»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 4 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L4») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_5 : coreProgram.find? (rsEqRowsAllNames.getD 5 "") = some fn% «rs_eq_rows_all__L5» ∧
    (fn% «rs_eq_rows_all__L5»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L5»).body).all (loadInB [(0, 64 * (5 + 1)), (1, 5), (2, 5)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L5»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 5 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L5») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_6 : coreProgram.find? (rsEqRowsAllNames.getD 6 "") = some fn% «rs_eq_rows_all__L6» ∧
    (fn% «rs_eq_rows_all__L6»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L6»).body).all (loadInB [(0, 64 * (6 + 1)), (1, 6), (2, 6)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L6»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 6 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L6») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_7 : coreProgram.find? (rsEqRowsAllNames.getD 7 "") = some fn% «rs_eq_rows_all__L7» ∧
    (fn% «rs_eq_rows_all__L7»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L7»).body).all (loadInB [(0, 64 * (7 + 1)), (1, 7), (2, 7)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L7»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 7 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L7») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn_8 : coreProgram.find? (rsEqRowsAllNames.getD 8 "") = some fn% «rs_eq_rows_all__L8» ∧
    (fn% «rs_eq_rows_all__L8»).params = [.n 0, .n 1, .n 2] ∧
    (atomsOf (fn% «rs_eq_rows_all__L8»).body).all (loadInB [(0, 64 * (8 + 1)), (1, 8), (2, 8)]) = true ∧
    (retOf (fn% «rs_eq_rows_all__L8»).body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD 8 "") = false :=
  ⟨coreProgram_find?_at (j := idx% «rs_eq_rows_all__L8») rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem rra_fn : ∀ n ≤ 8, ∃ f : Fn, coreProgram.find? (rsEqRowsAllNames.getD n "") = some f ∧
    f.params = [.n 0, .n 1, .n 2] ∧ (atomsOf f.body).all (loadInB [(0, 64 * (n + 1)), (1, n), (2, n)]) = true ∧
    (retOf f.body).isSome = true ∧ coreProgram.loop (rsEqRowsAllNames.getD n "") = false := by
  intro n hn
  interval_cases n
  exacts [⟨_, rra_fn_0⟩, ⟨_, rra_fn_1⟩, ⟨_, rra_fn_2⟩, ⟨_, rra_fn_3⟩, ⟨_, rra_fn_4⟩, ⟨_, rra_fn_5⟩, ⟨_, rra_fn_6⟩, ⟨_, rra_fn_7⟩, ⟨_, rra_fn_8⟩]

set_option maxRecDepth 100000 in
theorem rra_pureIn : coreProgram.PureIn rsEqRowsAllNames := Tables.pureIn_of_pureInB (by decide +kernel)

theorem rra_mem {n : ℕ} (hn : n ≤ 8) : rsEqRowsAllNames.getD n "" ∈ rsEqRowsAllNames := by
  rw [List.getD_eq_getElem _ _ (by change n < 9; omega)]; exact List.getElem_mem _

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **Every valid tree of `rs_eq_rows_all__L{n}`** has its leaf shape. -/
theorem rra_shape {n : ℕ} (hn : n ≤ 8) {row z p : E} {R : ℕ → Prop} (hrow : PtrCells R row (64 * (n + 1)))
    (hz : PtrCells R z n) (hp : PtrCells R p n) {rd : Reader} {t : Tree} {rets : List E}
    (hn' : t.name = rsEqRowsAllNames.getD n "") (hv : t.Valid coreProgram rd [row, z, p] rets)
    (hb : t.BufsOk coreProgram) : LlShape fs al (fs (rsEqRowsAllNames.getD n "")) id R t := by
  obtain ⟨f, hf, hpa, hL, hr, hlp⟩ := rra_fn n hn
  refine leaf_shapeR rra_pureIn (rra_mem hn) hf hlp (by rw [hpa]; rfl) hL hr
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> simp)
    ?_ hn' hv hb
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  exacts [hrow, hz, hp]

/-! ## `ring_rows_loop0` -/

/-- The loop's multiplications: `x^8`, `x^512`, the leaf's arguments. -/
def rgLA : List Atom :=
  [.mul (.n 5) (.n 0) (.n 0), .mul (.n 6) (.n 5) (.n 5), .mul (.n 7) (.n 6) (.n 6), .mul (.n 8) (.n 7) (.n 7),
    .mul (.n 9) (.n 8) (.n 8), .mul (.n 10) (.n 9) (.n 9), .mul (.n 11) (.n 10) (.n 10),
    .mul (.n 12) (.n 11) (.n 11), .mul (.n 13) (.n 12) (.n 12), .mul (.n 14) (.n 2) (.n 13),
    .mul (.n 15) (.n 3) (.n 7), .mul (.n 16) (.n 4) (.n 7)]

set_option maxRecDepth 100000 in
theorem rrg_T : LoopT name% «ring_rows_loop0» "rs_eq_rows_all__L8" rgLA 512 fn% «ring_rows_loop0» where
  find := find_loopRg
  params := rfl
  body := stmtsEqb_sound (by decide +kernel)
  loop := by decide +kernel
  muls := rfl
  args := by
    intro rd σ h
    have m : ∀ d x y, Atom.mul (.n d) (.n x) (.n y) ∈ rgLA → σ (.n d) = σ (.n x) * σ (.n y) :=
      fun d x y hm => h _ hm
    rw [m 14 2 13 (by simp [rgLA]), m 15 3 7 (by simp [rgLA]), m 16 4 7 (by simp [rgLA]),
      m 13 12 12 (by simp [rgLA]), m 12 11 11 (by simp [rgLA]), m 11 10 10 (by simp [rgLA]),
      m 10 9 9 (by simp [rgLA]), m 9 8 8 (by simp [rgLA]), m 8 7 7 (by simp [rgLA]),
      m 7 6 6 (by simp [rgLA]), m 6 5 5 (by simp [rgLA]), m 5 0 0 (by simp [rgLA])]
    refine ⟨by ring, by ring, by ring⟩

set_option maxRecDepth 100000 in
theorem rrg_free : NoWitG name% «ring_rows_loop0» ∧ ExactFreeG name% «ring_rows_loop0» :=
  free_of (by decide +kernel : freeAt name% «ring_rows_loop0» idx% «ring_rows_loop0» = true)

set_option maxRecDepth 100000 in
theorem rrg_pureIn : coreProgram.PureIn [name% «ring_rows_loop0», "rs_eq_rows_all__L8"] :=
  Tables.pureIn_of_pureInB (by decide +kernel)

/-- What the loop from iteration `j` of `q` asks: each later iteration's leaf words, chunk `t`'s
coordinates `Zs t`, `Ps t` and row `Cs t`. -/
def RrgPre (q j : ℕ) (chain z p : E) (Zs Ps Cs : ℕ → List E) (rd : Reader) : Prop :=
  ∀ t, j ≤ t → t < q → RraPre (chain * (gen ^ t) ^ 512) (z * (gen ^ t) ^ 8) (p * (gen ^ t) ^ 8) (Zs t) (Ps t) (Cs t) 8 rd

theorem ptrCells_pow {R : ℕ → Prop} {x : E} {n t s S : ℕ} (h : PtrCells R x n) (hs : t * S + s ≤ n) :
    PtrCells R (x * (gen ^ t) ^ S) s := by
  rw [← pow_mul]; exact ptrCells_shift h hs

/-- **`ring_rows_loop0` completes** from iteration `j < q` where its leaves' words hold. -/
theorem rrg_complete0 (kd : ℕ) {q j : ℕ} (hq : q < 2 ^ 30) (hj : j < q) {chain z p : E} {Zs Ps Cs : ℕ → List E}
    (hZ : ∀ t < q, (Zs t).length = 8) (hP : ∀ t < q, (Ps t).length = 8)
    (hC : ∀ t < q, (Cs t).length = 64) {R : ℕ → Prop}
    (hc : PtrCells R chain (64 * (8 * q + 1))) (hz : PtrCells R z (8 * q)) (hp : PtrCells R p (8 * q)) :
    CallCompletes0 kd name% «ring_rows_loop0» [gen ^ j, gen ^ q, chain, z, p] [] (RrgPre q j chain z p Zs Ps Cs)
      PostQuiet :=
  (callCompletes0_free coreProgram_wf rrg_free.1 rrg_free.2 fun rd hl hP' =>
    (loop_rel_iff (P := coreProgram) (f := name% «ring_rows_loop0») (ps := [gen ^ q, chain, z, p])
      (N := gen ^ q) (B := LRgBody rd chain z p) (fun d x h => loopRg_sound rd _ _ _ _ d x h)
      (fun x hb hk hn => loopRg_complete rd _ _ _ _ x hb hk hn) j).mpr
      ⟨q, hj, rfl, fun t h1 h2 he => absurd (gen_pow_inj (by omega) (by omega) he) (by omega),
        fun t h1 h2 => by
          obtain ⟨tr, hn, hv, -, -⟩ := rra_complete0 kd (n := 8) le_rfl (hZ t h2) (hP t h2) (hC t h2)
            (ptrCells_pow hc (by omega)) (ptrCells_pow hz (by omega)) (ptrCells_pow hp (by omega)) rd hl
            (hP' t h1 h2)
          have hrel := Tree.Valid.rel tr hv
          rw [hn] at hrel
          exact ⟨0, hrel⟩⟩).mono
    (fun _ h => h) fun _ _ _ h => h

/-- **`ring_rows_loop0` completes placed** from iteration `j < q`. -/
theorem rrg_placed {k q j : ℕ} (hq : q < 2 ^ 30) (hj : j < q) {chain z p : E} {Zs Ps Cs : ℕ → List E}
    (hZ : ∀ t < q, (Zs t).length = 8) (hP : ∀ t < q, (Ps t).length = 8)
    (hC : ∀ t < q, (Cs t).length = 64) {R : ℕ → Prop}
    (hc : PtrCells R chain (64 * (8 * q + 1))) (hz : PtrCells R z (8 * q)) (hp : PtrCells R p (8 * q)) (fp c : ℕ) :
    CallAtA fs al cert k name% «ring_rows_loop0» [gen ^ j, gen ^ q, chain, z, p] [] R (fun _ => False)
      (fun _ => True) (RrgPre q j chain z p Zs Ps Cs) PostQuiet (llBlk fs name% «ring_rows_loop0» q j) fp c
      (llEnd fs al "rs_eq_rows_all__L8" q j c) :=
  ll_placed rrg_T rrg_pureIn hq hj (fun t ht rd t1 rets hn hv hb =>
    rra_shape (n := 8) le_rfl (ptrCells_pow hc (by omega)) (ptrCells_pow hz (by omega))
      (ptrCells_pow hp (by omega)) hn hv hb) (rrg_complete0 k hq hj hZ hP hC hc hz hp) fp c

end
end LeanVM.Guest.B1.VsC
