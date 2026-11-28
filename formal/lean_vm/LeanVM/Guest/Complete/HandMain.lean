/-
  LeanVM.Guest.Complete.HandMain

  `main`'s own hand fact on its honest tree: its meta hint's cells are the node's counts
  (`main_meta`, from the pops), so its inner bound at its values is `mainWordsC` (`main_hand_own`).
-/

module

public import LeanVM.Guest.Complete.HandHonest
public import LeanVM.Guest.Complete.Open

/-!
# `main`'s own hand fact

`main` pops `meta` first and `honestPushes` pushes it first, so `SameStreams` pins its eight cells
to `metaCells` (`main_meta`), whatever the memory. Its virtual values are those counts and two
products of them; its inner bound at them (`whmain_eval`) is `mainWordsC` of the node's items, the
declared claims and the duplicates filling the coverage table's slots (`planSlots_eq`), each count
within the memory budget.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## Affine bounds, coefficient by coefficient -/

/-- An affine bound's coefficient of argument `i`. -/
def coefOf (cs : List (ℕ × ℕ)) (i : ℕ) : ℕ := ((cs.filter fun q => q.1 = i).map (·.2)).sum

/-- An affine bound's sum over its arguments, grouped by argument. -/
theorem sum_coef (x : ℕ → ℕ) (n : ℕ) : ∀ cs : List (ℕ × ℕ), (∀ q ∈ cs, q.1 < n) →
    (cs.map fun q => q.2 * x q.1).sum = ∑ i ∈ Finset.range n, coefOf cs i * x i
  | [], _ => by simp [coefOf]
  | q :: cs, h => by
      have hq : q.1 < n := h q List.mem_cons_self
      rw [List.map_cons, List.sum_cons, sum_coef x n cs fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]
      have e : ∀ i, coefOf (q :: cs) i * x i = (if q.1 = i then q.2 * x i else 0) + coefOf cs i * x i := by
        intro i
        by_cases hi : q.1 = i <;> simp [coefOf, hi, add_mul]
      rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_ite_eq,
        ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_range.mpr hq))]

/-! ## `main`'s meta cells -/

theorem sameStreams_head {s : String} {x y : List E} {a b : List Pop}
    (h : SameStreams ((s, x) :: a) ((s, y) :: b)) : x = y := by
  have h' := h s
  rw [List.filter_cons, List.filter_cons] at h'
  simp at h'
  exact h'.1

theorem honest_head (s : NodeStatement) (w : NodeWitness) :
    ∃ rest, Prover.honestPushes guestBytecode guestSeed s w = ("meta", metaCells s w) :: rest :=
  ⟨_, by rw [honest_eq, mPreX]; rfl⟩

theorem mainItems_head (rd : Reader) (σ : Val) (ks : List (List Pop)) (da leaf : Bool) :
    ∃ r, skelPops rd σ (mainItems da leaf) ks =
      ("meta", [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)]) :: r :=
  ⟨_, rfl⟩

variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {rd : Reader} {σ : Val} {bufs : List ℕ}
  {kids : List Tree}

/-- **`main`'s meta cells are the node's counts**, from the pops. -/
theorem main_meta (h : MainHonest al s w rd (.node "main" σ bufs kids)) :
    [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] = metaCells s w := by
  have hp : (Memory.Tree.node "main" σ bufs kids).pops coreProgram rd = _ := pops_node Main.find_main (walk_main σ)
  rw [splice_skel, mainEvs_skel] at hp
  obtain ⟨r, hr⟩ := mainItems_head rd σ (Tree.popsKids coreProgram rd kids) (decide (σ (.n 384) = 0))
    (decide (σ (.n 423) = 0))
  obtain ⟨rest, hrest⟩ := honest_head s w
  have hs := h.pops
  rw [hp, hr, hrest] at hs
  exact sameStreams_head hs

/-- `main`'s products of counts. -/
theorem main_muls (h : MainHonest al s w rd (.node "main" σ bufs kids)) :
    σ (.n 22) = σ (.n 0) * σ (.n 1) ∧ σ (.n 23) = σ (.n 3) * σ (.n 4) := by
  obtain ⟨fn, hf, -, es, vs, hw, -, hes, -⟩ := h.valid
  rw [Main.find_main] at hf
  obtain rfl := Option.some.inj hf
  rw [walk_main] at hw
  obtain ⟨rfl, -⟩ := Out.ret.inj hw
  have hm : Atom.mul (.n 22) (.n 0) (.n 1) ∈ VsC.atomsOf Main.mPre ∧ Atom.mul (.n 23) (.n 3) (.n 4) ∈ VsC.atomsOf Main.mPre := by
    decide +kernel
  have hin : ∀ a, a ∈ VsC.atomsOf Main.mPre → Ev.atom a ∈ mainEvs σ := fun a ha => by
    unfold mainEvs
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨_, atom_mem_of_atomsOf ha, by simp [slEvs]⟩))))
  exact ⟨hes _ (hin _ hm.1), hes _ (hin _ hm.2)⟩

/-! ## The counts -/

theorem count_gpow {n : ℕ} (h : n < 2 ^ 64 - 1) : GPow (Prover.count n) n :=
  ⟨by rw [Sig.count_eq (by omega), gen_pow_eq_ofK], h⟩

theorem gpow_mul {x y : E} {a b : ℕ} (hx : GPow x a) (hy : GPow y b) (h : a + b < 2 ^ 64 - 1) :
    GPow (x * y) (a + b) :=
  ⟨by rw [hx.1, hy.1, pow_add], h⟩

/-- Preconditions `g^b` with `b` below the order of `g`, at arguments with such values. -/
theorem argsPre_of {pre : List (ℕ × ℕ)} {args : List E} (hpre : ∀ q ∈ pre, q.2 = 2 ^ 64)
    (h : ∀ q ∈ pre, ∃ e, GPow (args.getD q.1 0) e) : ArgsPre pre args := by
  intro q hq
  obtain ⟨e, he⟩ := h q hq
  refine ⟨e, ?_, he.2, he.ofK⟩
  rw [hpre q hq]
  unfold preLt gT
  rw [Nat.ble_eq_true_of_le (le_refl _), Bool.cond_true, Nat.sub_self]
  exact Nat.ble_eq_true_of_le (Nat.zero_le _)

/-- `main`'s inner bound at its values' exponents. -/
theorem whmain_eval (args : List E) :
    Data.whmainHand.b.eval args = 41235 + 5 * argExp args 0 + 5 * argExp args 1 + 15 * argExp args 2 +
      15 * argExp args 3 + 16 * argExp args 4 + 16 * argExp args 5 + 1327 * argExp args 6 +
      7315 * argExp args 7 + 993 * argExp args 8 := by
  have hlt : ∀ q ∈ Data.whmainHand.b.cs, q.1 < 9 := by decide +kernel
  have hco : coefOf Data.whmainHand.b.cs 0 = 5 ∧ coefOf Data.whmainHand.b.cs 1 = 5 ∧
      coefOf Data.whmainHand.b.cs 2 = 15 ∧ coefOf Data.whmainHand.b.cs 3 = 15 ∧
      coefOf Data.whmainHand.b.cs 4 = 16 ∧ coefOf Data.whmainHand.b.cs 5 = 16 ∧
      coefOf Data.whmainHand.b.cs 6 = 1327 ∧ coefOf Data.whmainHand.b.cs 7 = 7315 ∧
      coefOf Data.whmainHand.b.cs 8 = 993 := by decide +kernel
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := hco
  have hc : Data.whmainHand.b.c = 41235 := rfl
  unfold Aff.eval
  rw [sum_coef (argExp args) 9 _ hlt, hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7, c8]
  ring

/-- **`main`'s own hand fact**: its preconditions at its values and its inner bound there within
`mainWordsC` of the node's items. -/
theorem main_hand_own (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (h : MainHonest al s w rd (.node "main" σ bufs kids)) :
    ArgsPre Data.whmainHand.pre ([] ++ Data.whmainHand.vps.map σ) ∧
      Data.whmainHand.b.eval ([] ++ Data.whmainHand.vps.map σ) ≤ mainWordsC (itemsOf s w) := by
  have hm := main_meta h
  simp only [metaCells, List.cons.injEq, and_true] at hm
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := hm
  obtain ⟨m22, m23⟩ := main_muls h
  have hb := hlim.withinMemoryBudget
  simp only [NodeWitness.memoryBudget, NodeWitness.childClaimCount] at hb
  have hps : s.claims.xmss.length + (xPlan s w).duplicates.length + s.claims.sphincs.length +
      (sPlan s w).duplicates.length = w.xmssSignatures.length + w.sphincsSignatures.length +
        (w.children.map fun c => c.statement.claims.xmss.length + c.statement.claims.sphincs.length).sum := by
    have := Main.planSlots_eq hrel.1
    simp only [Coverage.planSlots, coverageSlots] at this
    rw [← (coveragePlan_eq _ _ _).1, ← (coveragePlan_eq _ _ _).1] at this
    exact this
  have L : ∀ n, n ≤ 3 * 2 ^ 24 → n < 2 ^ 64 - 1 := fun n hn => by omega
  have g0 := count_gpow (n := s.claims.xmss.length) (L _ (by omega))
  have g1 := count_gpow (n := (xPlan s w).duplicates.length) (L _ (by omega))
  have g2 := count_gpow (n := w.xmssSignatures.length) (L _ (by omega))
  have g3 := count_gpow (n := s.claims.sphincs.length) (L _ (by omega))
  have g4 := count_gpow (n := (sPlan s w).duplicates.length) (L _ (by omega))
  have g5 := count_gpow (n := w.sphincsSignatures.length) (L _ (by omega))
  have g6 := count_gpow (n := w.children.length) (L _ (by omega))
  rw [← h0] at g0; rw [← h1] at g1; rw [← h2] at g2; rw [← h3] at g3; rw [← h4] at g4; rw [← h5] at g5
  rw [← h6] at g6
  have g22 : GPow (σ (.n 22)) (s.claims.xmss.length + (xPlan s w).duplicates.length) := by
    rw [m22]; exact gpow_mul g0 g1 (L _ (by omega))
  have g23 : GPow (σ (.n 23)) (s.claims.sphincs.length + (sPlan s w).duplicates.length) := by
    rw [m23]; exact gpow_mul g3 g4 (L _ (by omega))
  have hvps : Data.whmainHand.vps = [.n 22, .n 23, .n 0, .n 3, .n 1, .n 4, .n 2, .n 5, .n 6] := rfl
  have hpre : Data.whmainHand.pre = [(0, 2 ^ 64), (1, 2 ^ 64), (8, 2 ^ 64), (4, 2 ^ 64), (5, 2 ^ 64),
      (6, 2 ^ 64), (7, 2 ^ 64)] := rfl
  rw [hvps, hpre]
  simp only [List.nil_append, List.map_cons, List.map_nil]
  refine ⟨argsPre_of (by simp) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨_, g22⟩, ⟨_, g23⟩, ⟨_, g6⟩, ⟨_, g1⟩, ⟨_, g4⟩, ⟨_, g2⟩, ⟨_, g5⟩]
  · have a0 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 0 = _ :=
      g22.logG
    have a1 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 1 = _ :=
      g23.logG
    have a2 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 2 = _ :=
      g0.logG
    have a3 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 3 = _ :=
      g3.logG
    have a4 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 4 = _ :=
      g1.logG
    have a5 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 5 = _ :=
      g4.logG
    have a6 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 6 = _ :=
      g2.logG
    have a7 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 7 = _ :=
      g5.logG
    have a8 : argExp [σ (.n 22), σ (.n 23), σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] 8 = _ :=
      g6.logG
    rw [whmain_eval, a0, a1, a2, a3, a4, a5, a6, a7, a8]
    simp only [mainWordsC, NodeItems.holders, NodeItems.childClaims, itemsOf, NodeItems.ofWitness, List.map_map,
      Function.comp_def, List.length_map]
    omega

end
end LeanVM.Guest.Complete
