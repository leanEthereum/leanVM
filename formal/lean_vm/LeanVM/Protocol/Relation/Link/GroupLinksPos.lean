/-
  LeanVM.Protocol.Relation.Link.GroupLinksPos

  A draw of `verify_link`'s challenges with each named slice set: `lkp_set` realises given values
  for `θ`, `γ_state`, `γ_mem`, `μ`, `α`, `η_mem`, `η_bc`, `ε`, `τ`, `ζ`, `ν`.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupCh

/-!
# Setting the link's challenges

`lkp_tail x` is `drawn` cut as `linkCh` cuts it, each slice read off `x : lkp_Vals`, and
`lkp_set x : Fin (linkDrawn + 1) → E` is `θ_0 :: lkp_tail x` as a draw (`lkp_ofFn_set`). Then
`lkp_linkCh_tail` reads every slice of `linkCh` back as a list, and `lkp_chV_*` state it per slice
at `chV (lkp_set x)`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link

@[expose] public section

/-- Values for each named challenge: `θ_t`, `γ_pc, γ_fp`, `g_0, g_1, g_2` (`γ_mem` is
`[g_0, g_1, g_1·y, g_2]`), table `t`'s `μ_t,k`, `α`, `η_mem`, `η_bc`, `ε`, `τ`, `ζ`, `ν`. -/
structure lkp_Vals where
  theta : ℕ → E
  gammaState : ℕ → E
  gammaMem : ℕ → E
  mu : ℕ → ℕ → E
  alpha : ℕ → E
  etaMem : E
  etaBc : E
  eps : ℕ → E
  tau : ℕ → E
  zeta : ℕ → E
  nu : ℕ → E

/-- The `μ` slices of tables `s, s + 1, …`, concatenated. -/
def lkp_muList (f : ℕ → ℕ → E) : List Table → ℕ → List E
  | [], _ => []
  | tb :: ts, s => List.ofFn (n := tb.links.memory.length) (fun k ↦ f s k) ++ lkp_muList f ts (s + 1)

/-- The `μ` slices of tables `s, s + 1, …`. -/
def lkp_muLists (f : ℕ → ℕ → E) : List Table → ℕ → List (List E)
  | [], _ => []
  | tb :: ts, s => List.ofFn (n := tb.links.memory.length) (fun k ↦ f s k) :: lkp_muLists f ts (s + 1)

theorem lkp_mu_fold (f : ℕ → ℕ → E) : ∀ (ts : List Table) (s : ℕ) (acc : List (List E)) (rest : List E),
    ts.foldl (fun (acc : List (List E) × List E) t ↦
      (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length))
      (acc, lkp_muList f ts s ++ rest) = (acc ++ lkp_muLists f ts s, rest)
  | [], _, acc, rest => by simp [lkp_muList, lkp_muLists]
  | tb :: ts, s, acc, rest => by
    rw [List.foldl_cons]
    simp only [lkp_muList, lkp_muLists, List.append_assoc]
    rw [List.take_left' (by simp), List.drop_left' (by simp), lkp_mu_fold f ts (s + 1)]
    simp

theorem lkp_muList_length (f : ℕ → ℕ → E) : ∀ (ts : List Table) (s : ℕ),
    (lkp_muList f ts s).length = (ts.map (·.links.memory.length)).sum
  | [], _ => by simp [lkp_muList]
  | tb :: ts, s => by simp [lkp_muList, lkp_muList_length f ts (s + 1)]

theorem lkp_muLists_getD (f : ℕ → ℕ → E) : ∀ (ts : List Table) (s t : ℕ), t < ts.length →
    (lkp_muLists f ts s).getD t [] = List.ofFn (n := (ts.getD t default).links.memory.length)
      (fun k ↦ f (s + t) k)
  | [], _, _, h => by simp at h
  | tb :: ts, s, 0, _ => by simp [lkp_muLists]
  | tb :: ts, s, t + 1, h => by
    have := lkp_muLists_getD f ts (s + 1) t (by simpa using h)
    rw [show s + 1 + t = s + (t + 1) by omega] at this
    exact this

/-- `drawn` with each slice set from `x`, in `verify_link`'s order. -/
def lkp_tail (layout : Layout) (chunks : Chunks) (x : lkp_Vals) : List E :=
  List.ofFn (n := nTables - 1) (fun i ↦ x.theta (i + 1)) ++
  ([x.gammaState 0, x.gammaState 1] ++
  ([x.gammaMem 0, x.gammaMem 1, x.gammaMem 2] ++
  (lkp_muList x.mu layout.tables 0 ++
  (List.ofFn (n := bytecodeSlotBits) (fun i ↦ x.alpha i) ++
  ([x.etaMem, x.etaBc] ++
  (List.ofFn (n := nPointersOf layout) (fun i ↦ x.eps i) ++
  (List.ofFn (n := linkRows layout) (fun i ↦ x.tau i) ++
  (List.ofFn (n := chunks.width) (fun i ↦ x.zeta i) ++
  List.ofFn (n := chunks.d) (fun i ↦ x.nu i)))))))))

/-- The draw `θ_0 :: lkp_tail x`. -/
def lkp_set (layout : Layout) (chunks : Chunks) (x : lkp_Vals) : Fin (linkDrawn layout chunks + 1) → E :=
  fun i ↦ (x.theta 0 :: lkp_tail layout chunks x).getD i 0

theorem lkp_ofFn_getD {n : ℕ} (L : List E) (h : L.length = n) :
    List.ofFn (fun i : Fin n ↦ L.getD i 0) = L := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem lkp_tail_length (layout : Layout) (chunks : Chunks) (hch : Chunks.new chunks.width = some chunks)
    (x : lkp_Vals) : (lkp_tail layout chunks x).length + 1 = linkDrawn layout chunks + 1 := by
  have hN := linkDrawn_eq layout chunks hch
  have hT1 : 1 ≤ nTables := by decide
  simp only [nuOff, tauOff, epsOff, nAccessesOf] at hN
  simp only [lkp_tail, List.length_append, List.length_ofFn, List.length_cons, List.length_nil,
    lkp_muList_length]
  omega

theorem lkp_ofFn_set (layout : Layout) (chunks : Chunks) (hch : Chunks.new chunks.width = some chunks)
    (x : lkp_Vals) : List.ofFn (lkp_set layout chunks x) = x.theta 0 :: lkp_tail layout chunks x :=
  lkp_ofFn_getD _ (by simpa using lkp_tail_length layout chunks hch x)

theorem lkp_headD_set (layout : Layout) (chunks : Chunks) (x : lkp_Vals) :
    (List.ofFn (lkp_set layout chunks x)).headD 0 = x.theta 0 := by
  rw [headD_ofFn]
  simp [lkp_set]

theorem lkp_tail_set (layout : Layout) (chunks : Chunks) (hch : Chunks.new chunks.width = some chunks)
    (x : lkp_Vals) : (List.ofFn (lkp_set layout chunks x)).tail = lkp_tail layout chunks x := by
  rw [lkp_ofFn_set layout chunks hch x, List.tail_cons]

theorem lkp_cons_ofFn (f : ℕ → E) {n : ℕ} (hn : 1 ≤ n) :
    f 0 :: List.ofFn (n := n - 1) (fun i ↦ f (i + 1)) = List.ofFn (n := n) (fun i ↦ f i) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  rcases i with _ | i <;> simp

theorem lkp_take_ofFn_append {n : ℕ} (f : Fin n → E) (R : List E) : (List.ofFn f ++ R).take n = List.ofFn f :=
  List.take_left' (by simp)

theorem lkp_drop_ofFn_append {n : ℕ} (f : Fin n → E) (R : List E) : (List.ofFn f ++ R).drop n = R :=
  List.drop_left' (by simp)

theorem lkp_take_ofFn {n : ℕ} (f : Fin n → E) : (List.ofFn f).take n = List.ofFn f :=
  List.take_of_length_le (by simp)

theorem lkp_take2 (a b : E) (R : List E) : ([a, b] ++ R).take 2 = [a, b] := rfl
theorem lkp_drop2 (a b : E) (R : List E) : ([a, b] ++ R).drop 2 = R := rfl
theorem lkp_take3 (a b c : E) (R : List E) : ([a, b, c] ++ R).take 3 = [a, b, c] := rfl
theorem lkp_drop3 (a b c : E) (R : List E) : ([a, b, c] ++ R).drop 3 = R := rfl
theorem lkp_getD0 (a b : E) (R : List E) : ([a, b] ++ R).getD 0 0 = a := rfl
theorem lkp_getD1 (a b : E) (R : List E) : ([a, b] ++ R).getD 1 0 = b := rfl

/-- Every slice of `linkCh` at `θ_0 :: lkp_tail x`. -/
theorem lkp_linkCh_tail (layout : Layout) (chunks : Chunks) (x : lkp_Vals) :
    linkCh layout chunks (x.theta 0) (lkp_tail layout chunks x) =
      ⟨List.ofFn (n := nTables) (fun i ↦ x.theta i), [x.gammaState 0, x.gammaState 1],
        [x.gammaMem 0, x.gammaMem 1, x.gammaMem 1 * eY, x.gammaMem 2], lkp_muLists x.mu layout.tables 0,
        List.ofFn (n := bytecodeSlotBits) (fun i ↦ x.alpha i), x.etaMem, x.etaBc,
        List.ofFn (n := nPointersOf layout) (fun i ↦ x.eps i), List.ofFn (n := linkRows layout) (fun i ↦ x.tau i),
        List.ofFn (n := chunks.width) (fun i ↦ x.zeta i), List.ofFn (n := chunks.d) (fun i ↦ x.nu i)⟩ := by
  have hT1 : 1 ≤ nTables := by decide
  simp only [linkCh, lkp_tail, nPointersOf, linkRows]
  simp only [lkp_take_ofFn_append, lkp_drop_ofFn_append, lkp_take_ofFn, lkp_take2, lkp_drop2, lkp_take3,
    lkp_drop3, lkp_getD0, lkp_getD1, lkp_mu_fold, List.nil_append, lkp_cons_ofFn x.theta hT1]
  rfl

section Set

variable {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks) (x : lkp_Vals)
include hch

theorem lkp_chV_set : chV layout chunks (lkp_set layout chunks x) =
    linkCh layout chunks (x.theta 0) (lkp_tail layout chunks x) := by
  simp only [chV, lkp_headD_set, lkp_tail_set layout chunks hch x]

theorem lkp_chV_theta : (chV layout chunks (lkp_set layout chunks x)).theta =
    List.ofFn (n := nTables) (fun i ↦ x.theta i) := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_gammaState : (chV layout chunks (lkp_set layout chunks x)).gammaState =
    [x.gammaState 0, x.gammaState 1] := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_gammaMem : (chV layout chunks (lkp_set layout chunks x)).gammaMem =
    [x.gammaMem 0, x.gammaMem 1, x.gammaMem 1 * eY, x.gammaMem 2] := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_mu {t : ℕ} (ht : t < layout.tables.length) :
    (chV layout chunks (lkp_set layout chunks x)).mu.getD t [] =
      List.ofFn (n := (layout.tables.getD t default).links.memory.length) (fun k ↦ x.mu t k) := by
  rw [lkp_chV_set hch, lkp_linkCh_tail, lkp_muLists_getD _ _ _ _ ht, Nat.zero_add]

theorem lkp_chV_alpha : (chV layout chunks (lkp_set layout chunks x)).alpha =
    List.ofFn (n := bytecodeSlotBits) (fun i ↦ x.alpha i) := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_etaMem : (chV layout chunks (lkp_set layout chunks x)).etaMem = x.etaMem := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_etaBc : (chV layout chunks (lkp_set layout chunks x)).etaBc = x.etaBc := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_eps : (chV layout chunks (lkp_set layout chunks x)).eps =
    List.ofFn (n := nPointersOf layout) (fun i ↦ x.eps i) := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_tau : (chV layout chunks (lkp_set layout chunks x)).tau =
    List.ofFn (n := linkRows layout) (fun i ↦ x.tau i) := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_zeta : (chV layout chunks (lkp_set layout chunks x)).zeta =
    List.ofFn (n := chunks.width) (fun i ↦ x.zeta i) := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

theorem lkp_chV_nu : (chV layout chunks (lkp_set layout chunks x)).nu =
    List.ofFn (n := chunks.d) (fun i ↦ x.nu i) := by
  rw [lkp_chV_set hch, lkp_linkCh_tail]

end Set

end

end LeanVM.Protocol.Relation
