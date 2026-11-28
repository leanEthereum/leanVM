/-
  LeanVM.Guest.B1.VsC.LoopLeafA

  A `mul_range` loop calling one leaf per iteration, placed by its shape: `rs_eq_run`'s and
  `ring_rows`' loops.
-/

module

public import LeanVM.Guest.Complete.PureA
public import LeanVM.Guest.Complete.ComposeA
public import LeanVM.Guest.B1.VsC.SqueezeFwd
public import LeanVM.Guest.Complete.TransferA

/-!
# A loop of leaf calls, placed

`rs_eq_run_loop0` and `ring_rows_loop0` share a template (`llPre A leaf self`): at `x = g^j` their
multiplications `A` give the leaf's three arguments `chain·x^S`, `z·x^8`, `p·x^8` (`LlArgs`), the
leaf is called, and the tail call goes to `x·g` while `x·g ≠ g^q`. They place nothing of their own.

* `leaf_shapeR`: every valid tree of a straight pure leaf reading its arguments' arrays has its
  shape (block its frame, ending at its cursor, loading in the arrays' cells).
* `ll_shape`: every valid tree of the loop from iteration `j < q` has the shape `llBlk`, `llEnd` (its `q - j` frames then a phantom; each iteration's leaf at the aligned base),
  loading what its leaves load.
* `ll_placed`: the loop's layout-free completeness placed by `callAtA_of_callCompletes0`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-! ## Shapes -/

/-- A subtree placed by its shape alone: block `B`, end `Ec c` from every cursor `c`, its loads and
heap hints in `R` (`SlowA.lean`'s `ShapeR`). -/
def LlShape (fs : String → ℕ) (al : String → Bool) (B : ℕ) (Ec : ℕ → ℕ) (R : ℕ → Prop) (t : Tree) : Prop :=
  t.block fs coreProgram.loop = B ∧ (∀ c, t.endA fs coreProgram.loop al c = Ec c) ∧
    t.LoadsR coreProgram R ∧ t.HintsR coreProgram R

/-- The loop's block from iteration `j` of `q`: its frames, then its last phantom. -/
def llBlk (fs : String → ℕ) (self : String) (q j : ℕ) : ℕ := (q - j) * fs self + fs (tailKey self)

/-- An iteration's step of the cursor: its leaf's frame at the aligned base. -/
def llStep (fs : String → ℕ) (al : String → Bool) (leaf : String) (x : ℕ) : ℕ := allocBase (al leaf) x + fs leaf

/-- The loop's end from iteration `j` of `q`, from the cursor `c`. -/
def llEnd (fs : String → ℕ) (al : String → Bool) (leaf : String) (q j c : ℕ) : ℕ := (llStep fs al leaf)^[q - j] c

theorem le_llEnd (leaf : String) (q j c : ℕ) : c ≤ llEnd fs al leaf q j c := by
  unfold llEnd
  generalize q - j = n
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact le_trans (le_trans (le_allocBase _ c) (Nat.le_add_right _ _)) (ih _)

theorem ll_gen_add_ne {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) :
    gen ^ a + gen ^ b = 0 ↔ a = b := by
  refine ⟨fun h => gen_pow_inj ha hb (CharTwo.add_eq_zero.mp h), fun h => ?_⟩
  rw [h]; exact CharTwo.add_self_eq_zero _

/-! ## Leaves -/

/-- **Every valid tree of a straight pure leaf reading its arguments' arrays has its shape.** -/
theorem leaf_shapeR {S : List String} (hS : coreProgram.PureIn S) {f : String} (hf : f ∈ S) {fn : Fn}
    (hfind : coreProgram.find? f = some fn) (hlp : coreProgram.loop f = false) {ps : List (ℕ × ℕ)}
    {args rets : List E} (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadInB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) {R : ℕ → Prop}
    (hptr : ∀ q ∈ ps, ∀ off < q.2, ∃ i, (args.getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i)
    {rd : Reader} {t : Tree} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    LlShape fs al (fs f) id R t := by
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  have hnc : ∀ fn' σ es vs, coreProgram.find? f = some fn' → walk σ fn'.body = .ret es vs → calls es = [] := by
    intro fn' σ es vs hfn hw
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    rw [hb', walk_atoms] at hw
    cases hw
    exact calls_atoms _
  obtain ⟨h3, h4⟩ := loadsR_hintsR_of_loadIn R R hfind hparams hL hr hargs hptr hn hv
  exact ⟨(block_endA_leaf (fs := fs) (al := al) hS hf hlp hnc hn hv hb 0).1,
    fun c => (block_endA_leaf (fs := fs) (al := al) hS hf hlp hnc hn hv hb c).2, h3, h4⟩

/-- The cells `x·g^off`, `off < n`, are cells of `R`. -/
def PtrCells (R : ℕ → Prop) (x : E) (n : ℕ) : Prop :=
  ∀ off < n, ∃ i, x.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i

theorem ptrCells_shift {R : ℕ → Prop} {x : E} {n m n' : ℕ} (h : PtrCells R x n) (hm : m + n' ≤ n) :
    PtrCells R (x * gen ^ m) n' := by
  intro off hoff
  obtain ⟨i, hi, hR⟩ := h (m + off) (by omega)
  refine ⟨i, ?_, hR⟩
  rw [gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, ← pow_add, ← hi, addressOfIndex]

theorem ptrCells_mono {R : ℕ → Prop} {x : E} {n n' : ℕ} (h : PtrCells R x n) (hn : n' ≤ n) : PtrCells R x n' :=
  fun off hoff => h off (by omega)

theorem ptrAt_cells {R : ℕ → Prop} {a n : ℕ} (h : ∀ i < n, R (a + i)) : PtrCells R (ptrAt a) n :=
  fun off hoff => ⟨a + off, Main.addr_ofK a off, h off hoff⟩

/-! ## The loop's template -/

/-- A multiplication. -/
def isMulB : Atom → Bool
  | .mul .. => true
  | _ => false

/-- The loop's atoms after its call: the counter's step and the guard. -/
def llB : List Atom :=
  [.const (.n 18) (word 2 0), .mul (.n 19) (.n 0) (.n 18), .add (.n 20) (.n 19) (.n 1),
    .const (.n 21) (word 2 0), .mul (.n 22) (.n 0) (.n 21)]

/-- The loop's arguments to itself. -/
def llSelfArgs : List V := [.n 22, .n 1, .n 2, .n 3, .n 4]

/-- The loop's body before its `ret`: `A`, the leaf, the step, the tail call. -/
def llPre (A : List Atom) (leaf self : String) : List Stmt :=
  A.map .atom ++ [.call leaf [.n 14, .n 15, .n 16] [.n 17]] ++ llB.map .atom ++ [.callIf (.n 20) self llSelfArgs]

theorem llPre_straight (A : List Atom) (leaf self : String) : (llPre A leaf self).all Stmt.straight = true := by
  simp [llPre, Stmt.straight]

theorem llFlatMap_atoms (σ : Val) : ∀ A : List Atom, (A.map Stmt.atom).flatMap (slEvs σ) = A.map Ev.atom
  | [] => rfl
  | a :: A => by rw [List.map_cons, List.flatMap_cons, llFlatMap_atoms σ A]; rfl

theorem ll_evs (σ : Val) (A : List Atom) (leaf self : String) : (llPre A leaf self).flatMap (slEvs σ) =
    A.map .atom ++ [.call leaf [.n 14, .n 15, .n 16] [.n 17]] ++ llB.map .atom ++
      [.inK (.n 20), if σ (.n 20) = 0 then .skip self llSelfArgs else .call self llSelfArgs []] := by
  simp only [llPre, List.flatMap_append, llFlatMap_atoms]
  rfl

theorem muls_filterMap {β : Type} (g : Stmt → Option β) (hg : ∀ d x y, g (.atom (.mul d x y)) = none) :
    ∀ A : List Atom, A.all isMulB = true → (A.map Stmt.atom).filterMap g = []
  | [] , _ => rfl
  | a :: A, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases a with
    | mul d x y => rw [List.map_cons, List.filterMap_cons, hg, muls_filterMap g hg A h.2]
    | _ => simp [isMulB] at h

theorem ll_calls (σ : Val) {A : List Atom} (hA : A.all isMulB = true) (leaf self : String) :
    calls ((llPre A leaf self).flatMap (slEvs σ)) =
      [⟨leaf, [.n 14, .n 15, .n 16], [.n 17], true⟩, ⟨self, llSelfArgs, [], decide (σ (.n 20) ≠ 0)⟩] := by
  rw [(straight_parts σ _ (llPre_straight A leaf self)).2.2.2]
  simp only [llPre, List.filterMap_append, muls_filterMap Stmt.callS (fun _ _ _ => rfl) A hA]
  rfl

theorem ll_allocs (σ : Val) {A : List Atom} (hA : A.all isMulB = true) (leaf self : String) :
    allocs σ ((llPre A leaf self).flatMap (slEvs σ)) = [] := by
  rw [(straight_parts σ _ (llPre_straight A leaf self)).2.1]
  simp only [llPre, List.filterMap_append, muls_filterMap Stmt.allocSz (fun _ _ _ => rfl) A hA]
  rfl

theorem ll_noLoad (σ : Val) {A : List Atom} (hA : A.all isMulB = true) (leaf self : String) :
    loadAddrs σ ((llPre A leaf self).flatMap (slEvs σ)) = [] := by
  rw [ll_evs]
  have h1 : ∀ B : List Atom, B.all isMulB = true → loadAddrs σ (B.map Ev.atom) = [] := by
    intro B hB
    induction B with
    | nil => rfl
    | cons a B ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hB
      cases a with
      | mul => rw [List.map_cons, loadAddrs, List.filterMap_cons]; exact ih hB.2
      | _ => simp [isMulB] at hB
  simp only [loadAddrs, List.filterMap_append] at h1 ⊢
  rw [h1 A hA]
  split <;> rfl

theorem ll_noHint (σ : Val) {A : List Atom} (hA : A.all isMulB = true) (leaf self : String) :
    heapHintAddrs σ ((llPre A leaf self).flatMap (slEvs σ)) = [] := by
  rw [ll_evs]
  have h1 : ∀ B : List Atom, B.all isMulB = true → heapHintAddrs σ (B.map Ev.atom) = [] := by
    intro B hB
    induction B with
    | nil => rfl
    | cons a B ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hB
      cases a with
      | mul => rw [List.map_cons, heapHintAddrs, List.flatMap_cons]; exact ih hB.2
      | _ => simp [isMulB] at hB
  simp only [heapHintAddrs, List.flatMap_append] at h1 ⊢
  rw [h1 A hA]
  split <;> rfl

/-- The leaf's arguments at iteration `t`: `chain·g^(S t)`, `z·g^(8t)`, `p·g^(8t)`. -/
def llArgs (S t : ℕ) (chain z p : E) : List E := [chain * (gen ^ t) ^ S, z * (gen ^ t) ^ 8, p * (gen ^ t) ^ 8]

/-- What the loop's template facts are: its function, its multiplications giving the leaf's
arguments. -/
structure LoopT (sf leaf : String) (A : List Atom) (S : ℕ) (f : Fn) : Prop where
  find : coreProgram.find? sf = some f
  params : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4]
  body : f.body = llPre A leaf sf ++ [.ret []]
  loop : coreProgram.loop sf = true
  muls : A.all isMulB = true
  args : ∀ rd σ, (∀ a ∈ A, a.Holds rd σ) →
    σ (.n 14) = σ (.n 2) * σ (.n 0) ^ S ∧ σ (.n 15) = σ (.n 3) * σ (.n 0) ^ 8 ∧
      σ (.n 16) = σ (.n 4) * σ (.n 0) ^ 8

/-! ## The loop's shape -/

/-- **One iteration's shape**, the next one's when `j + 1 < q`. -/
theorem ll_shape_step {self leaf : String} {A : List Atom} {S : ℕ} {f : Fn} (hT : LoopT self leaf A S f)
    {q : ℕ} (hq : q < 2 ^ 30) {chain z p : E} {R : ℕ → Prop}
    (hleaf : ∀ t < q, ∀ rd t1 rets, t1.name = leaf → t1.Valid coreProgram rd (llArgs S t chain z p) rets →
      t1.BufsOk coreProgram → LlShape fs al (fs leaf) id R t1) {j : ℕ} (hj : j < q)
    (hnext : j + 1 < q → ∀ rd t, t.name = self → t.Valid coreProgram rd [gen ^ (j + 1), gen ^ q, chain, z, p] [] →
      t.BufsOk coreProgram → LlShape fs al (llBlk fs self q (j + 1)) (llEnd fs al leaf q (j + 1)) R t) :
    ∀ rd t, t.name = self → t.Valid coreProgram rd [gen ^ j, gen ^ q, chain, z, p] [] →
      t.BufsOk coreProgram → LlShape fs al (llBlk fs self q j) (llEnd fs al leaf q j) R t := by
  intro rd t hn hv hb
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
  simp only [Tree.name] at hn
  subst hn
  obtain ⟨fn, hf, hp, es, vs, hw, -, hev, hk⟩ := hv
  have hff : fn = f := Option.some.inj (hf.symm.trans hT.find)
  subst hff
  have hw0 : walk σ fn.body = .ret ((llPre A leaf g).flatMap (slEvs σ)) [] := by
    rw [hT.body]; exact walk_straight σ [] _ (llPre_straight A leaf g)
  rw [hw0] at hw
  cases hw
  rw [hT.params] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4⟩ := hp
  have hat : ∀ a, a ∈ A ∨ a ∈ llB → a.Holds rd σ := fun a ha =>
    hev (.atom a) (by rw [ll_evs]; rcases ha with ha | ha <;> simp [ha])
  obtain ⟨e14, e15, e16⟩ := hT.args rd σ fun a ha => hat a (Or.inl ha)
  have e18 : σ (.n 18) = word 2 0 := hat (.const (.n 18) (word 2 0)) (Or.inr (by simp [llB]))
  have e19 : σ (.n 19) = σ (.n 0) * σ (.n 18) := hat (.mul (.n 19) (.n 0) (.n 18)) (Or.inr (by simp [llB]))
  have e20 : σ (.n 20) = σ (.n 19) + σ (.n 1) := hat (.add (.n 20) (.n 19) (.n 1)) (Or.inr (by simp [llB]))
  have e21 : σ (.n 21) = word 2 0 := hat (.const (.n 21) (word 2 0)) (Or.inr (by simp [llB]))
  have e22 : σ (.n 22) = σ (.n 0) * σ (.n 21) := hat (.mul (.n 22) (.n 0) (.n 21)) (Or.inr (by simp [llB]))
  have hsucc : σ (.n 0) * word 2 0 = gen ^ (j + 1) := by rw [h0, word_gen, pow_succ]
  have h20 : σ (.n 20) = 0 ↔ j + 1 = q := by
    rw [e20, e19, e18, hsucc, h1]; exact ll_gen_add_ne (by omega) (by omega)
  have hev0 : (Memory.Tree.node g σ bufs kids).events coreProgram = (llPre A leaf g).flatMap (slEvs σ) :=
    Complete.events_node hT.find hw0
  rw [Tree.BufsOk, hev0, ll_allocs σ hT.muls] at hb
  obtain ⟨rfl, hbk⟩ := hb
  rw [ll_calls σ hT.muls] at hk
  rcases kids with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, ks⟩⟩⟩ <;> try (simp [Tree.KidsValid] at hk; done)
  rw [Tree.KidsValid, Tree.KidsValid, Tree.KidsValid] at hk
  obtain ⟨hn1, hv1, hn2, hv2, -⟩ := hk
  simp only [↓reduceIte] at hv1
  rw [Tree.BufsOkKids, Tree.BufsOkKids] at hbk
  obtain ⟨hb1, hb2, -⟩ := hbk
  have ha1 : [V.n 14, .n 15, .n 16].map σ = llArgs S j chain z p := by
    simp only [List.map_cons, List.map_nil, llArgs, e14, e15, e16, h0, h2, h3, h4]
  rw [ha1] at hv1
  obtain ⟨hB1, hE1, hL1, hH1⟩ := hleaf j hj rd t1 _ hn1 hv1 hb1
  have hs2 : LlShape fs al (llBlk fs g q (j + 1)) (llEnd fs al leaf q (j + 1)) R t2 := by
    by_cases hl : j + 1 = q
    · have hd : decide (σ (.n 20) ≠ 0) = false := by simp [h20.mpr hl]
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hv2
      obtain ⟨⟨f', σ', rfl⟩, -⟩ := hv2
      simp only [Tree.name] at hn2
      have h0' : q - (j + 1) = 0 := by omega
      refine ⟨?_, fun c => ?_, by simp only [Tree.LoadsR], by simp only [Tree.HintsR]⟩
      · rw [Tree.block, hn2, llBlk, h0', zero_mul, zero_add]
      · rw [endA_phantom, llEnd, h0']; rfl
    · have hd : decide (σ (.n 20) ≠ 0) = true := by simp [h20, hl]
      simp only [hd, ↓reduceIte] at hv2
      have ha : llSelfArgs.map σ = [gen ^ (j + 1), gen ^ q, chain, z, p] := by
        simp only [llSelfArgs, List.map_cons, List.map_nil, e22, e21, hsucc, h1, h2, h3, h4]
      rw [ha] at hv2
      exact hnext (by omega) rd t2 hn2 hv2 hb2
  obtain ⟨hB2, hE2, hL2, hH2⟩ := hs2
  refine ⟨?_, fun c => ?_, ?_, ?_⟩
  · rw [Tree.block, hT.loop]
    simp only [↓reduceIte, Tree.blockLast]
    rw [hB2]
    unfold llBlk
    have : q - j = (q - (j + 1)) + 1 := by omega
    rw [this]
    generalize q - (j + 1) = n
    ring
  · rw [endA_node, hT.loop]
    simp only [↓reduceIte, List.sum_nil, add_zero]
    rw [endL_cons, endL_one, hn1, hB1, hE1, hE2]
    unfold llEnd
    have : q - j = (q - (j + 1)) + 1 := by omega
    rw [this, Function.iterate_succ_apply]
    rfl
  · rw [Tree.LoadsR, hev0, ll_noLoad σ hT.muls]
    refine ⟨fun A hA => by simp at hA, ?_⟩
    rw [Tree.LoadsRKids, Tree.LoadsRKids, Tree.LoadsRKids]; exact ⟨hL1, hL2, trivial⟩
  · rw [Tree.HintsR, hev0, ll_noHint σ hT.muls]
    refine ⟨fun A hA => by simp at hA, ?_⟩
    rw [Tree.HintsRKids, Tree.HintsRKids, Tree.HintsRKids]; exact ⟨hH1, hH2, trivial⟩

/-- **Every valid tree of the loop from iteration `j < q` has its shape.** -/
theorem ll_shape {self leaf : String} {A : List Atom} {S : ℕ} {f : Fn} (hT : LoopT self leaf A S f)
    {q : ℕ} (hq : q < 2 ^ 30) {chain z p : E} {R : ℕ → Prop}
    (hleaf : ∀ t < q, ∀ rd t1 rets, t1.name = leaf → t1.Valid coreProgram rd (llArgs S t chain z p) rets →
      t1.BufsOk coreProgram → LlShape fs al (fs leaf) id R t1) :
    ∀ m j, q = j + m + 1 → ∀ rd t, t.name = self → t.Valid coreProgram rd [gen ^ j, gen ^ q, chain, z, p] [] →
      t.BufsOk coreProgram → LlShape fs al (llBlk fs self q j) (llEnd fs al leaf q j) R t := by
  intro m
  induction m with
  | zero =>
    intro j hj
    exact ll_shape_step hT hq hleaf (by omega) (fun h => absurd h (by omega))
  | succ m ih =>
    intro j hj
    exact ll_shape_step hT hq hleaf (by omega) (fun _ => ih (j + 1) (by omega))

/-- **The loop completes placed** from iteration `j < q`, from its layout-free completeness. -/
theorem ll_placed {self leaf : String} {A : List Atom} {S : ℕ} {f : Fn} (hT : LoopT self leaf A S f)
    (hS : coreProgram.PureIn [self, leaf]) {k q j : ℕ} (hq : q < 2 ^ 30) (hj : j < q) {chain z p : E}
    {R : ℕ → Prop} {Pre : Reader → Prop}
    (hleaf : ∀ t < q, ∀ rd t1 rets, t1.name = leaf → t1.Valid coreProgram rd (llArgs S t chain z p) rets →
      t1.BufsOk coreProgram → LlShape fs al (fs leaf) id R t1)
    (h : CallCompletes0 k self [gen ^ j, gen ^ q, chain, z, p] [] Pre PostQuiet) (fp c : ℕ) :
    CallAtA fs al cert k self [gen ^ j, gen ^ q, chain, z, p] [] R (fun _ => False) (fun _ => True) Pre PostQuiet
      (llBlk fs self q j) fp c (llEnd fs al leaf q j c) :=
  callAtA_of_callCompletes0 hS List.mem_cons_self (le_llEnd leaf q j c) h fun rd t _ _ hn hv hb _ =>
    let hs := ll_shape hT hq hleaf (q - j - 1) j (by omega) rd t hn hv hb
    ⟨hs.1, hs.2.1 c, hs.2.2.1, hs.2.2.2⟩

end
end LeanVM.Guest.B1.VsC
