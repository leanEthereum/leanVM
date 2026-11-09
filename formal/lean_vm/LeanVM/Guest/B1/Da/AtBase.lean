/-
  LeanVM.Guest.B1.Da.AtBase

  What the placed completeness of `da_verify` and its callees shares: a leaf of atoms placed by
  its walk (`relAtIn_atoms`), a straight body's events, the trees' cells as one buffer
  (`treeCells`, `treeMem_of_reads`), and reading a layout's entries.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Da.LevelsComplete

/-!
# Placed completeness, the shared part

* `relAtIn_atoms`: a function whose body is atoms and a return, not a loop helper, holds placed at
  `fp` (`RelAtIn`, its frame only) from a valuation satisfying its atoms, its `frameAddr`s at their
  runs in its frame, its loads in its region or its runs.
* `slEvs_holds`: the events of a straight run hold when its atoms hold and its conditional calls'
  conditions are in `K`.
* `treeCells leaves k`: the cells of `da_levels`' tree over `2^k` leaves, level after level, as
  `TreeMem` reads them (`treeMem_of_reads`), `4·2^k - 2` words (`length_treeCells`).
* `memL_of_sub`, `reads_of_memL`: a layout's entries.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## A leaf of atoms -/

/-- The words of the runs of the atoms `as` of `f` in its frame at `fp`. -/
def RunIn (cert : String → V → ℕ) (fp : ℕ) (f : String) (as : List Atom) (i : ℕ) : Prop :=
  ∃ q ∈ as.filterMap atomRun?, fp + cert f q.1 ≤ i ∧ i < fp + cert f q.1 + q.2

/-- **A leaf of atoms, placed**: its frame only, its `frameAddr`s at their runs, its loads in its
region or its runs, its claim within its runs. -/
theorem relAtIn_atoms {f : String} {fn : Fn} {as : List Atom} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hb : fn.body = as.map Stmt.atom ++ [.ret vs])
    (hl : coreProgram.loop f = false) (hna : as.all (fun a => !atomAllocB a) = true)
    {rd : Reader} {σ : Val} {args rets : List E} {fp : ℕ} {R D : ℕ → Prop}
    (hp : fn.params.map σ = args) (hh : ∀ a ∈ as, a.Holds rd σ) (hr : vs.map σ = rets)
    (haddr : ∀ q ∈ as.filterMap atomAddr?, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    (hload : ∀ q ∈ as.filterMap atomLoad?, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
        addressOfIndex i ∧
      (R i ∨ RunIn cert fp f as i))
    (hD : ∀ i, D i → RunIn cert fp f as i) :
    RelAtIn coreProgram fs cert rd R D fp (fs f) f args rets := by
  have hw := walk_atoms σ as vs
  rw [← hb] at hw
  have hown : ∀ i, RunIn cert fp f as i →
      ownData cert fp (fp + fs f) f (allocs σ (as.map Ev.atom)) (as.map Ev.atom) i := by
    rintro i ⟨q, hq, h1, h2⟩
    exact Or.inr ⟨q, by rw [runs_atoms]; exact hq, h1, h2⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := R) (D := D)
    (Dk := fun _ => False) (N := 0) (fp := fp) (σ := σ) (rd := rd) coreProgram_wf hf (Or.inl hl)
    hp hw hr (holds_atoms hh) (by rw [allocDsts_atoms hna, allocs_atoms σ hna]; rfl)
    (by rw [addrs_atoms]; exact haddr) (by rw [calls_atoms]; exact ⟨rfl, fun _ h => h⟩)
    (fun A hA => ?_) (fun i hi => Or.inl (hown i (hD i hi)))
  · rw [allocs_atoms σ hna] at h
    simpa using h
  · rw [loadAddrs_atoms] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h⟩ := hload q hq
    exact ⟨i, hi, h.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (hown i h)⟩

/-! ## A straight run's events -/

/-- What a straight statement's events need: an atom holds, a conditional call's condition is in
`K`. -/
def SlOk (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .callIf c _ _ => IsInK (σ c)
  | _ => True

theorem slEvs_holds {rd : Reader} {σ : Val} {pre : List Stmt} (h : ∀ s ∈ pre, SlOk rd σ s) :
    ∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have hs' := h s hs
  match s, hs', he with
  | .atom a, hs', he =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he; exact hs'
  | .call .., _, he =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he; trivial
  | .callIf c f args, hs', he =>
    simp only [Main.slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hs'
    · split <;> trivial
  | .ite .., _, he => simp [Main.slEvs] at he
  | .match_ .., _, he => simp [Main.slEvs] at he
  | .dispatch .., _, he => simp [Main.slEvs] at he
  | .ret _, _, he => simp [Main.slEvs] at he

/-! ## Trees as buffers -/

/-- The cells of the tree over `leaves`, levels `0` to `k`. -/
def treeCells (leaves : List (E × E)) (k : ℕ) : List E :=
  (List.range (k + 1)).flatMap fun l => pairCells (treeLvl leaves l)

theorem readsAt_range_prefix {rd : Reader} {p : E} {f : ℕ → List E} :
    ∀ n, ReadsAt rd p ((List.range n).flatMap f) →
      ∀ l < n, ReadsAt rd (p * gen ^ ((List.range l).map fun m => (f m).length).sum) (f l)
  | 0, _, l, hl => absurd hl (by omega)
  | n + 1, h, l, hl => by
    rw [List.range_succ, List.flatMap_append, Main.readsAt_append'] at h
    rcases Nat.lt_or_ge l n with hl' | hl'
    · exact readsAt_range_prefix n h.1 l hl'
    · have e : l = n := by omega
      subst e
      have hlen : ((List.range l).flatMap f).length = ((List.range l).map fun m => (f m).length).sum := by
        rw [List.length_flatMap]
      rw [← hlen]
      simpa using h.2

theorem sum_level_lengths {k : ℕ} : ∀ l ≤ k,
    ((List.range l).map fun m => 2 * 2 ^ (k - m)).sum = off k l
  | 0, _ => by simp [off]
  | l + 1, hl => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_level_lengths l (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, off]
    have e : 2 ^ (k - l) = 2 * 2 ^ (k - (l + 1)) := by
      rw [← pow_succ']; congr 1; omega
    have hle : 2 ^ (k - l) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem length_pairCells_lvl {leaves : List (E × E)} {k : ℕ} (hlen : leaves.length = 2 ^ k)
    {l : ℕ} (hl : l ≤ k) : (pairCells (treeLvl leaves l)).length = 2 * 2 ^ (k - l) := by
  rw [length_pairCells, length_treeLvl hlen l hl]

/-- **The tree's cells as one buffer are `TreeMem`.** -/
theorem treeMem_of_reads {rd : Reader} {tree : E} {k : ℕ} {leaves : List (E × E)}
    (hlen : leaves.length = 2 ^ k) (h : ReadsAt rd tree (treeCells leaves k)) :
    TreeMem rd tree k leaves := by
  intro l hl
  have := readsAt_range_prefix (k + 1) h l (by omega)
  have e : ((List.range l).map fun m => (pairCells (treeLvl leaves m)).length) =
      (List.range l).map fun m => 2 * 2 ^ (k - m) :=
    List.map_congr_left fun m hm => length_pairCells_lvl hlen (by simp at hm; omega)
  rwa [e, sum_level_lengths l hl] at this

theorem length_treeCells {leaves : List (E × E)} {k : ℕ} (hlen : leaves.length = 2 ^ k) :
    (treeCells leaves k).length = 4 * 2 ^ k - 2 := by
  rw [treeCells, List.length_flatMap, List.range_succ, List.map_append, List.sum_append]
  have e : ((List.range k).map fun l => (pairCells (treeLvl leaves l)).length) =
      (List.range k).map fun m => 2 * 2 ^ (k - m) :=
    List.map_congr_left fun m hm => length_pairCells_lvl hlen (by simp at hm; omega)
  rw [e, sum_level_lengths k le_rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    length_pairCells_lvl hlen le_rfl, Nat.sub_self, pow_zero, off]
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-! ## Layout entries -/

theorem reads_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {b : ℕ} {xs : List E}
    (hq : (b, xs) ∈ L) : ReadsAt rd (gen ^ b) xs := by
  rw [gen_pow_eq_ofK]; exact h _ hq

theorem regionL_of_mem {L : Layout} {b : ℕ} {xs : List E} (hq : (b, xs) ∈ L) {k : ℕ}
    (hk : k < xs.length) : RegionL L (b + k) := ⟨(b, xs), hq, by simp, by simp; omega⟩

theorem exists_of_length_succ {α : Type} {l : List α} {n : ℕ} (h : l.length = n + 1) :
    ∃ a t, l = a :: t ∧ t.length = n := by
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl, by simpa using h⟩

theorem limb0_gen_pow_mul (b k : ℕ) : (gen ^ b).limb 0 * addressOfIndex k = addressOfIndex (b +
    k) := by
  rw [gen_pow_eq_ofK, Main.addr_ofK]


/-! ## Shared by the completeness proofs -/

theorem fn_name_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  have := List.find?_some h
  simpa using this

theorem good_mul {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ} (hx : x < d)
    (hy : y < d) (h : Fwd.Good rd S w σ (.mul (.n d) (.n x) (.n y))) :
    σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [Fwd.Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

theorem good_load {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {o : ℕ}
    (hS : Atom.load d p o ∉ S) (h : Fwd.Good rd S w σ (.load d p o)) : σ d = Fwd.rdAt rd (σ p) o := by
  rcases h with h | h
  · exact absurd h hS
  · exact h


theorem params_of_shape {fn : Fn} {f : String} {n : ℕ} (hs : loopShapeF fn f = true)
    (hl : fn.params.length = n) : fn.params = (List.range n).map V.n := by
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
  rw [hs.1.2, hl]

end
end LeanVM.Guest.B1.Da
