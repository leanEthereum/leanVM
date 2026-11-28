/-
  LeanVM.Prover.Complete.Link.BalanceSum

  The index side's balance as a sum over the tables' executed rows.
-/

module

public import LeanVM.Prover.Complete.Link.BalanceAlg
public import LeanVM.Prover.Complete.Link.IndexTabs
public import LeanVM.Prover.Complete.Link.OneHot

/-!
# The balance, row by row

The balance's arrays (`indexArrays`) are scattered from the rows (`scatterWords`): against a
target `Z`, a scattered array pairs to the sum over the rows of each row's weight times `Z` at the
cell its pointer names, when every row of nonzero weight names one cell (`pair_scatterWords`). So
the balance's cube sum is the sum over the tables' executed rows of each row's share, `rowBal`
(`cubeSum_balance`), when the rows' pointers are one-hot and their shifted reads stay in their
windows (`ScatterOK`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Prover

/-! ## Pairing a scattered array -/

/-- An array's first `N` entries against `Z`. -/
noncomputable def pair (N : ℕ) (a : Array E) (Z : ℕ → E) : E := ∑ j ∈ Finset.range N, a.getD j 0 * Z j

theorem pair_modify (N : ℕ) (a : Array E) (Z : ℕ → E) {i : ℕ} (hi : i < a.size) (hN : i < N)
    (w : E) : pair N (a.modify i (· + w)) Z = pair N a Z + w * Z i := by
  unfold pair
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hN),
    ← Finset.add_sum_erase _ (fun j ↦ a.getD j 0 * Z j) (Finset.mem_range.mpr hN),
    getD_modify_self _ _ hi,
    Finset.sum_congr rfl fun j hj ↦ by rw [getD_modify_ne _ _ (Finset.ne_of_mem_erase hj).symm]]
  ring

theorem foldl_filterMap_of (f : Array E → ℕ → Array E) (g : ℕ → Option ℕ)
    (F : Array E → ℕ → Array E) (hs : ∀ a j k, g j = some k → f a j = F a k)
    (hn : ∀ a j, g j = none → f a j = a) :
    ∀ (js : List ℕ) (a : Array E), js.foldl f a = (js.filterMap g).foldl F a
  | [], _ => rfl
  | j :: js, a => by
    rw [List.foldl_cons, List.filterMap_cons]
    rcases hg : g j with _ | k
    · rw [hn a j hg]; exact foldl_filterMap_of f g F hs hn js a
    · rw [hs a j k hg]; exact foldl_filterMap_of f g F hs hn js _

/-- **A scattered array against `Z`**: each row of nonzero weight names one cell `tgt u` inside
the array. -/
theorem pair_scatterWords (chunks : Chunks) (words : Array K) (shift : ℕ) (weight : ℕ → E)
    (Z : ℕ → E) (tgt : ℕ → ℕ) (a : Array E) :
    ∀ rows, (∀ u < rows, weight u ≠ 0 →
      (chunks.indices (kToNat (words.getD u 0))).filterMap (chunks.shifted · shift) = [tgt u] ∧
        tgt u < a.size) →
      pair a.size (scatterWords chunks words rows shift weight a) Z =
        pair a.size a Z + ∑ u ∈ Finset.range rows, weight u * Z (tgt u)
  | 0, _ => by simp [scatterWords]
  | rows + 1, h => by
    have ih := pair_scatterWords chunks words shift weight Z tgt a rows fun u hu ↦ h u (by omega)
    have hsz := size_scatterWords chunks words rows shift weight a
    unfold scatterWords at ih hsz ⊢
    rw [Nat.fold_succ, Finset.sum_range_succ]
    dsimp only
    by_cases hw : weight rows = 0
    · rw [ite_eq_left hw, ih, hw, zero_mul, add_zero]
    · rw [ite_eq_right hw, foldl_filterMap_of _ (chunks.shifted · shift)
          (fun a j ↦ a.modify j (· + weight rows)) (fun a j k hk ↦ by simp only [hk])
          (fun a j hk ↦ by simp only [hk]),
        (h rows (by omega) hw).1, List.foldl_cons, List.foldl_nil,
        pair_modify _ _ _ (by rw [hsz]; exact (h rows (by omega) hw).2) (h rows (by omega) hw).2, ih]
      ring

/-! ## The index side's arrays -/

/-- `indexArrays`' scattering step over table `t`. -/
def scatterStep (W : Witness) (ch : LinkChallenges) (acc : Vector (Array E) 6) (t : ℕ) :
    Vector (Array E) 6 :=
  let table := tables.getD t default
  let links := table.links
  let cols := W.tableCols t
  let n := W.rows.getD t 0
  let omega := omegaTable (ch.theta.getD t 0) ch.tau (W.layout.tableLogHeights.getD t 0) n
  let mu := ch.mu.getD t []
  let state := links.stateLink
  let cyc := cols.getD state.cycle #[]
  let bcw := cols.getD links.bytecodeLink.pointer #[]
  let states := scatterWords W.chunks cyc n 0
    (fun u ↦ (stateValues ch links (rowValue cols u)).1) acc[0]
  let nexts := scatterWords W.chunks cyc n 0
    (fun u ↦ (stateValues ch links (rowValue cols u)).2) acc[1]
  let wMem := (links.memory.zip mu).foldl (fun a (access, m) ↦
    scatterWords W.chunks (cols.getD access.pointer #[]) n access.shift (fun u ↦
      let w := m * omega.getD u 0
      match access.gate with
      | some g => w * rowValue cols u g
      | none => w) a) acc[2]
  let vWord := (wordReads links mu (ch.gammaMem.getD 1 0)).foldl (fun a (p, scale) ↦
    scatterWords W.chunks (cols.getD p #[]) n 0
      (fun u ↦ scale.evaluate (rowValue cols u) * omega.getD u 0) a) acc[3]
  let wBc := scatterWords W.chunks bcw n 0 (fun u ↦ omega.getD u 0) acc[4]
  let wFp := scatterWords W.chunks bcw n 0
    (fun u ↦ omega.getD u 0 * rowValue cols u state.fp) acc[5]
  #v[states, nexts, wMem, vWord, wBc, wFp]

/-- The scattered arrays. -/
def scattered (W : Witness) (ch : LinkChallenges) : Vector (Array E) 6 :=
  (List.range nTables).foldl (scatterStep W ch) (Vector.replicate 6 (Array.replicate (2 ^ W.chunks.width) 0))

/-- Index array `k`'s entry `j`. -/
def idxAt (W : Witness) (ch : LinkChallenges) (k j : ℕ) : E := ((indexArrays W ch).getD k #[]).getD j 0

theorem idxAt_scattered (W : Witness) (ch : LinkChallenges) (j : ℕ) :
    idxAt W ch 2 j = (scattered W ch)[2].getD j 0 ∧ idxAt W ch 4 j = (scattered W ch)[4].getD j 0 ∧
      idxAt W ch 9 j = (scattered W ch)[3].getD j 0 ∧ idxAt W ch 11 j = (scattered W ch)[5].getD j 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem termsAt_balance (W : Witness) (ch : LinkChallenges) (j : ℕ) :
    termsAt (balanceProds W ch) j = 0 + ch.etaMem * idxAt W ch 2 j * idxAt W ch 3 j +
      1 * idxAt W ch 4 j * idxAt W ch 5 j + 1 * idxAt W ch 8 j +
      ch.etaMem * idxAt W ch 9 j * idxAt W ch 10 j + 1 * idxAt W ch 11 j * idxAt W ch 12 j := by
  rw [termsAt_eq]
  rfl

theorem sum_list_finset {α : Type} (L : List α) (n : ℕ) (f : α → ℕ → E) :
    (L.map fun x ↦ ∑ u ∈ Finset.range n, f x u).sum = ∑ u ∈ Finset.range n, (L.map fun x ↦ f x u).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- A fold of scatterings against `Z`. -/
theorem pair_foldl_scatter {α : Type} (chunks : Chunks) (n N : ℕ) (wd : α → Array K) (sh : α → ℕ)
    (wt : α → ℕ → E) (tgt : α → ℕ → ℕ) (Z : ℕ → E) :
    ∀ (L : List α) (a : Array E), a.size = N →
      (∀ x ∈ L, ∀ u < n, wt x u ≠ 0 →
        (chunks.indices (kToNat ((wd x).getD u 0))).filterMap (chunks.shifted · (sh x)) = [tgt x u] ∧
          tgt x u < N) →
      pair N (L.foldl (fun a x ↦ scatterWords chunks (wd x) n (sh x) (wt x) a) a) Z =
        pair N a Z + ∑ u ∈ Finset.range n, (L.map fun x ↦ wt x u * Z (tgt x u)).sum
  | [], a, _, _ => by simp
  | x :: L, a, ha, h => by
    rw [List.foldl_cons, pair_foldl_scatter chunks n N wd sh wt tgt Z L _
      (by rw [size_scatterWords]; exact ha) fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]
    rw [← ha, pair_scatterWords chunks (wd x) (sh x) (wt x) Z (tgt x) a n fun u hu hw ↦ by
      rw [ha]; exact h x List.mem_cons_self u hu hw]
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    ring

/-! ## Rows -/

/-- Row `u` of table `t`, as `E`. -/
def colAt (W : Witness) (t u : ℕ) : ℕ → E := rowValue (W.tableCols t) u

/-- Row `u` of table `t`'s weight `ω`. -/
def omegaRow (W : Witness) (ch : LinkChallenges) (t u : ℕ) : E :=
  (omegaTable (ch.theta.getD t 0) ch.tau (W.layout.tableLogHeights.getD t 0) (W.rows.getD t 0)).getD u 0

/-- The index row `u` of table `t`'s pointer column `p` names (its first index). -/
def ptrAt (W : Witness) (t p u : ℕ) : ℕ :=
  (W.chunks.indices (kToNat (((W.tableCols t).getD p #[]).getD u 0))).headD 0

/-- **The rows' pointers name their cells**: every executed row's pointer columns are one-hot,
naming an index below `2^W`, and an access of nonzero gate reads inside its pointer's window. -/
def ScatterOK (W : Witness) : Prop :=
  (∀ t < nTables, ∀ u < W.rows.getD t 0, ∀ p ∈ (tables.getD t default).links.pointers,
      W.chunks.indices (kToNat (((W.tableCols t).getD p #[]).getD u 0)) = [ptrAt W t p u] ∧
        ptrAt W t p u < 2 ^ W.chunks.width) ∧
    ∀ t < nTables, ∀ u < W.rows.getD t 0, ∀ a ∈ (tables.getD t default).links.memory,
      gateOf (colAt W t u) a ≠ 0 →
        W.chunks.shifted (ptrAt W t a.pointer u) a.shift = some (ptrAt W t a.pointer u + a.shift) ∧
          ptrAt W t a.pointer u + a.shift < 2 ^ W.chunks.width

/-- The pointers a table's links read are among its pointer columns. -/
def ptrsOK (links : Links) : Bool :=
  links.pointers.contains links.bytecodeLink.pointer &&
    links.memory.all fun a ↦ links.pointers.contains a.pointer && a.reads.all fun r ↦ match r with
      | .word p _ => links.pointers.contains p
      | _ => true

theorem ptrsOK_tables : ∀ t < nTables, ptrsOK (tables.getD t default).links = true := by
  decide +kernel

/-- The word reads' pointers are the reads'. -/
theorem wordReads_keys (links : Links) (mu : List E) (weight : E) :
    ∀ x ∈ wordReads links mu weight, ∃ a ∈ links.memory, ∃ sc, Read.word x.1 sc ∈ a.reads := by
  have h : wordReads links mu weight = (links.memory.zip mu).foldl
      (fun out am ↦ am.1.reads.foldl (wordStep weight am.2) out) [] := rfl
  rw [h]
  suffices key : ∀ (L : List (Access × E)) (out : List (ℕ × Form)), (∀ am ∈ L, am.1 ∈ links.memory) →
      (∀ x ∈ out, ∃ a ∈ links.memory, ∃ sc, Read.word x.1 sc ∈ a.reads) →
      ∀ x ∈ L.foldl (fun out am ↦ am.1.reads.foldl (wordStep weight am.2) out) out,
        ∃ a ∈ links.memory, ∃ sc, Read.word x.1 sc ∈ a.reads from
    key _ [] (fun am hm ↦ (List.of_mem_zip hm).1) (by simp)
  intro L
  induction L with
  | nil => intro out _ h; exact h
  | cons am L ih =>
    intro out hL hout
    rw [List.foldl_cons]
    refine ih _ (fun b hb ↦ hL b (List.mem_cons_of_mem _ hb)) ?_
    have ha := hL am List.mem_cons_self
    suffices hr : ∀ (rs : List Read), (∀ r ∈ rs, r ∈ am.1.reads) → ∀ out : List (ℕ × Form),
        (∀ x ∈ out, ∃ a ∈ links.memory, ∃ sc, Read.word x.1 sc ∈ a.reads) →
        ∀ x ∈ rs.foldl (wordStep weight am.2) out, ∃ a ∈ links.memory, ∃ sc, Read.word x.1 sc ∈ a.reads from
      hr _ (fun _ h ↦ h) out hout
    intro rs
    induction rs with
    | nil => intro _ out h; exact h
    | cons r rs ihr =>
      intro hrs out hout
      rw [List.foldl_cons]
      refine ihr (fun r' h' ↦ hrs r' (List.mem_cons_of_mem _ h')) _ ?_
      intro x hx
      cases r with
      | word p scale =>
        simp only [wordStep] at hx
        split_ifs at hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact hout y hy
        · rcases List.mem_append.mp hx with hx | hx
          · exact hout x hx
          · rw [List.mem_singleton.mp hx]
            exact ⟨am.1, ha, scale, hrs _ List.mem_cons_self⟩
      | slot => exact hout x hx
      | frame => exact hout x hx
      | pc => exact hout x hx

/-! ## Each scattered array against its target -/

theorem ptr_mem {t : ℕ} (ht : t < nTables) :
    (tables.getD t default).links.bytecodeLink.pointer ∈ (tables.getD t default).links.pointers ∧
      (∀ a ∈ (tables.getD t default).links.memory, a.pointer ∈ (tables.getD t default).links.pointers ∧
        ∀ p sc, Read.word p sc ∈ a.reads → p ∈ (tables.getD t default).links.pointers) := by
  have h := ptrsOK_tables t ht
  simp only [ptrsOK, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at h
  refine ⟨h.1, fun a ha ↦ ⟨(h.2 a ha).1, fun p sc hr ↦ ?_⟩⟩
  have := (h.2 a ha).2 _ hr
  simpa using this

theorem gate_weight (col : ℕ → E) (a : Access) (w : E) :
    (match a.gate with
      | some g => w * col g
      | none => w) = gateOf col a * w := by
  rcases h : a.gate with _ | g <;> simp [gateOf, h, mul_comm]

/-- The memory weights `w_mem` of table `t` against `Z`. -/
theorem pair_step_mem (W : Witness) (ch : LinkChallenges) (hS : ScatterOK W) {t : ℕ}
    (ht : t < nTables) (Z : ℕ → E) (acc : Vector (Array E) 6) (hacc : acc[2].size = 2 ^ W.chunks.width) :
    pair (2 ^ W.chunks.width) (scatterStep W ch acc t)[2] Z = pair (2 ^ W.chunks.width) acc[2] Z +
      ∑ u ∈ Finset.range (W.rows.getD t 0),
        (((tables.getD t default).links.memory.zip (ch.mu.getD t [])).map fun am ↦
          gateOf (colAt W t u) am.1 * (am.2 * omegaRow W ch t u) *
            Z (ptrAt W t am.1.pointer u + am.1.shift)).sum := by
  have key := pair_foldl_scatter W.chunks (W.rows.getD t 0) (2 ^ W.chunks.width)
    (fun x : Access × E ↦ (W.tableCols t).getD x.1.pointer #[]) (fun x ↦ x.1.shift)
    (fun x u ↦
      let w := x.2 * (omegaTable (ch.theta.getD t 0) ch.tau (W.layout.tableLogHeights.getD t 0)
        (W.rows.getD t 0)).getD u 0
      match x.1.gate with
      | some g => w * rowValue (W.tableCols t) u g
      | none => w)
    (fun x u ↦ ptrAt W t x.1.pointer u + x.1.shift) Z
    ((tables.getD t default).links.memory.zip (ch.mu.getD t [])) acc[2] hacc (fun x hx u hu hw ↦ by
      have hx1 := (List.of_mem_zip hx).1
      simp only [gate_weight] at hw
      have hg : gateOf (colAt W t u) x.1 ≠ 0 := left_ne_zero_of_mul hw
      obtain ⟨h1, -⟩ := hS.1 t ht u hu x.1.pointer ((ptr_mem ht).2 x.1 hx1).1
      obtain ⟨h3, h4⟩ := hS.2 t ht u hu x.1 hx1 hg
      refine ⟨?_, h4⟩
      rw [h1, List.filterMap_cons, h3]
      rfl)
  refine key.trans (congrArg (pair (2 ^ W.chunks.width) acc[2] Z + ·) ?_)
  refine Finset.sum_congr rfl fun u _ ↦ congrArg List.sum <| List.map_congr_left fun x _ ↦ ?_
  simp only [gate_weight]
  rfl

/-- The word reads' weights `v_word` of table `t` against `Z`. -/
theorem pair_step_word (W : Witness) (ch : LinkChallenges) (hS : ScatterOK W) {t : ℕ}
    (ht : t < nTables) (Z : ℕ → E) (acc : Vector (Array E) 6) (hacc : acc[3].size = 2 ^ W.chunks.width) :
    pair (2 ^ W.chunks.width) (scatterStep W ch acc t)[3] Z = pair (2 ^ W.chunks.width) acc[3] Z +
      ∑ u ∈ Finset.range (W.rows.getD t 0),
        ((wordReads (tables.getD t default).links (ch.mu.getD t []) (ch.gammaMem.getD 1 0)).map fun pf ↦
          pf.2.evaluate (colAt W t u) * omegaRow W ch t u * Z (ptrAt W t pf.1 u)).sum :=
  pair_foldl_scatter W.chunks (W.rows.getD t 0) (2 ^ W.chunks.width)
    (fun x : ℕ × Form ↦ (W.tableCols t).getD x.1 #[]) (fun _ ↦ 0)
    (fun x u ↦ x.2.evaluate (colAt W t u) * omegaRow W ch t u) (fun x u ↦ ptrAt W t x.1 u) Z
    _ acc[3] hacc fun x hx u hu _ ↦ by
      obtain ⟨a, ha, sc, hr⟩ := wordReads_keys _ _ _ x hx
      obtain ⟨h1, h2⟩ := hS.1 t ht u hu x.1 (((ptr_mem ht).2 a ha).2 x.1 sc hr)
      refine ⟨?_, h2⟩
      rw [h1, List.filterMap_cons, shifted_zero]
      rfl

/-- The program weights `w_bc` of table `t` against `Z`. -/
theorem pair_step_bc (W : Witness) (ch : LinkChallenges) (hS : ScatterOK W) {t : ℕ}
    (ht : t < nTables) (Z : ℕ → E) (acc : Vector (Array E) 6) (hacc : acc[4].size = 2 ^ W.chunks.width) :
    pair (2 ^ W.chunks.width) (scatterStep W ch acc t)[4] Z = pair (2 ^ W.chunks.width) acc[4] Z +
      ∑ u ∈ Finset.range (W.rows.getD t 0), omegaRow W ch t u *
        Z (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u) := by
  have key := pair_scatterWords W.chunks ((W.tableCols t).getD (tables.getD t default).links.bytecodeLink.pointer #[])
    0 (fun u ↦ omegaRow W ch t u) Z (fun u ↦ ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u)
    acc[4] (W.rows.getD t 0) fun u hu _ ↦ by
      obtain ⟨h1, h2⟩ := hS.1 t ht u hu _ (ptr_mem ht).1
      refine ⟨?_, by rw [hacc]; exact h2⟩
      rw [h1, List.filterMap_cons, shifted_zero]
      rfl
  rw [hacc] at key
  exact key

/-- The frame weights `w_fp` of table `t` against `Z`. -/
theorem pair_step_fp (W : Witness) (ch : LinkChallenges) (hS : ScatterOK W) {t : ℕ}
    (ht : t < nTables) (Z : ℕ → E) (acc : Vector (Array E) 6) (hacc : acc[5].size = 2 ^ W.chunks.width) :
    pair (2 ^ W.chunks.width) (scatterStep W ch acc t)[5] Z = pair (2 ^ W.chunks.width) acc[5] Z +
      ∑ u ∈ Finset.range (W.rows.getD t 0), omegaRow W ch t u *
        colAt W t u (tables.getD t default).links.stateLink.fp *
        Z (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u) := by
  have key := pair_scatterWords W.chunks ((W.tableCols t).getD (tables.getD t default).links.bytecodeLink.pointer #[])
    0 (fun u ↦ omegaRow W ch t u * colAt W t u (tables.getD t default).links.stateLink.fp) Z
    (fun u ↦ ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u)
    acc[5] (W.rows.getD t 0) fun u hu _ ↦ by
      obtain ⟨h1, h2⟩ := hS.1 t ht u hu _ (ptr_mem ht).1
      refine ⟨?_, by rw [hacc]; exact h2⟩
      rw [h1, List.filterMap_cons, shifted_zero]
      rfl
  rw [hacc] at key
  exact key

theorem sum_map_range_finset (c : ℕ → E) : ∀ n, ((List.range n).map c).sum = ∑ t ∈ Finset.range n, c t
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range_finset c n, Finset.sum_range_succ]
    simp

/-- **A scattered array against `Z`** is the sum of its tables' shares. -/
theorem pair_scattered (W : Witness) (ch : LinkChallenges) (k : ℕ) (hk : k < 6) (Z : ℕ → E) (c : ℕ → E)
    (hstep : ∀ t < nTables, ∀ acc : Vector (Array E) 6, (∀ i : Fin 6, acc[i].size = 2 ^ W.chunks.width) →
      pair (2 ^ W.chunks.width) ((scatterStep W ch acc t)[k]'hk) Z =
        pair (2 ^ W.chunks.width) (acc[k]'hk) Z + c t) :
    pair (2 ^ W.chunks.width) ((scattered W ch)[k]'hk) Z = ∑ t ∈ Finset.range nTables, c t := by
  suffices key : ∀ (L : List ℕ), (∀ t ∈ L, t < nTables) → ∀ acc : Vector (Array E) 6,
      (∀ i : Fin 6, acc[i].size = 2 ^ W.chunks.width) →
      pair (2 ^ W.chunks.width) ((L.foldl (scatterStep W ch) acc)[k]'hk) Z =
        pair (2 ^ W.chunks.width) (acc[k]'hk) Z + (L.map c).sum by
    rw [scattered, key _ (fun t ht ↦ List.mem_range.mp ht) _ (fun i ↦ by simp)]
    have h0 : pair (2 ^ W.chunks.width) ((Vector.replicate 6 (Array.replicate (2 ^ W.chunks.width) (0 : E)))[k]'hk) Z
        = 0 := by
      unfold pair
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [show ((Vector.replicate 6 (Array.replicate (2 ^ W.chunks.width) (0 : E)))[k]'hk) =
        Array.replicate (2 ^ W.chunks.width) 0 from Vector.getElem_replicate hk,
        Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split_ifs <;> simp
    rw [h0, zero_add, sum_map_range_finset]
  intro L
  induction L with
  | nil => intro _ acc _; simp
  | cons t L ih =>
    intro hL acc hacc
    have hsz : ∀ i : Fin 6, (scatterStep W ch acc t)[i].size = 2 ^ W.chunks.width :=
      fun i ↦ size_scattered W ch [t] acc hacc i
    rw [List.foldl_cons, ih (fun t' h' ↦ hL t' (List.mem_cons_of_mem _ h')) _ hsz,
      hstep t (hL t List.mem_cons_self) acc hacc]
    simp only [List.map_cons, List.sum_cons]
    ring

/-! ## The payload -/

theorem blocks_list (pf : Form × List (ℕ × Form)) (col : ℕ → E) :
    sumE (((⟨false, none, ({} : Form).addScaled pf.1 1⟩ :: pf.2.map fun x ↦
        (⟨false, some x.1, ({} : Form).addScaled x.2 1⟩ : Block)).filter (!·.onEq)).map fun b ↦
        (b.gate.map col).getD 1 * b.form.evaluate col) =
      pf.1.evaluate col + gatedVal col col pf.2 := by
  obtain ⟨ug, gs⟩ := pf
  rw [LeanVM.Protocol.Tables.sumE_eq, List.filter_cons]
  simp only [Bool.not_false, ↓reduceIte, List.map_cons, List.sum_cons, Option.map_none,
    Option.getD_none, one_mul, Form.evaluate_addScaled, Form.evaluate_empty, zero_add, gatedVal]
  congr 1
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, List.filter_cons]
    simp only [Bool.not_false, ↓reduceIte, List.map_cons, List.sum_cons, Option.map_some,
      Option.getD_some, Form.evaluate_addScaled, Form.evaluate_empty, zero_add, one_mul, ih]

theorem blocks_val (ch : LinkChallenges) (t : ℕ) (col : ℕ → E) :
    sumE (((tableBlocks ch t 1 none).filter (!·.onEq)).map fun b ↦
        (b.gate.map col).getD 1 * b.form.evaluate col) =
      (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).1.evaluate col +
        gatedVal col col (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).2 := by
  have h : tableBlocks ch t 1 none =
      (⟨false, none, ({} : Form).addScaled (payloadForms ch (tables.getD t default).links
          (ch.mu.getD t [])).1 1⟩ ::
        (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).2.map fun x ↦
          (⟨false, some x.1, ({} : Form).addScaled x.2 1⟩ : Block)) ++ [] := rfl
  rw [h, List.append_nil, blocks_list]

theorem sumRange_eq (f : ℕ → E) : ∀ n, sumRange n f = ∑ u ∈ Finset.range n, f u
  | 0 => by simp [sumRange]
  | n + 1 => by rw [sumRange, Nat.fold_succ, ← sumRange, sumRange_eq f n, Finset.sum_range_succ]

theorem sum_payload (W : Witness) (ch : LinkChallenges) :
    ∑ j ∈ Finset.range (2 ^ W.chunks.width), idxAt W ch 8 j =
      ∑ t ∈ Finset.range nTables, ∑ u ∈ Finset.range (W.rows.getD t 0), omegaRow W ch t u *
        ((payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).1.evaluate (colAt W t u) +
          gatedVal (colAt W t u) (colAt W t u)
            (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).2) := by
  have h8 : ∀ j, idxAt W ch 8 j = ((Array.replicate (2 ^ W.chunks.width) (0 : E)).set! 0
      (sumE ((List.range nTables).map fun t ↦ tablePayload ch t (W.rows.getD t 0) (W.tableCols t)
        (omegaTable (ch.theta.getD t 0) ch.tau (W.layout.tableLogHeights.getD t 0)
          (W.rows.getD t 0))))).getD j 0 := fun _ ↦ rfl
  simp only [h8]
  rw [Finset.sum_eq_single 0 (fun j _ hj ↦ by
      simp only [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hj),
        Array.getElem?_replicate]
      split_ifs <;> rfl)
    (fun h ↦ absurd (Finset.mem_range.mpr (Nat.two_pow_pos _)) h)]
  simp only [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds, Array.size_replicate,
    Nat.two_pow_pos, ↓reduceIte, Option.getD_some, LeanVM.Protocol.Tables.sumE_eq, sum_map_range_finset]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [tablePayload, sumRange_eq]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← blocks_val]
  rfl

/-! ## The balance -/

/-- Row `u` of table `t`'s share of the balance, at the witness's arrays. -/
def rowShare (W : Witness) (ch : LinkChallenges) (t u : ℕ) : E :=
  rowBal ch (tables.getD t default) (ch.mu.getD t []) (colAt W t u) (omegaRow W ch t u)
    (fun a ↦ ptrAt W t a.pointer u + a.shift) (fun p ↦ ptrAt W t p u)
    (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u)
    (idxAt W ch 3) (idxAt W ch 5) (idxAt W ch 10) (idxAt W ch 12)

/-- **The balance is the sum of the executed rows' shares**, when their pointers name their
cells. -/
theorem cubeSum_balance (W : Witness) (ch : LinkChallenges) (hS : ScatterOK W) :
    cubeSum (2 ^ W.chunks.width) (balanceProds W ch) =
      ∑ t ∈ Finset.range nTables, ∑ u ∈ Finset.range (W.rows.getD t 0), rowShare W ch t u := by
  have hsplit : cubeSum (2 ^ W.chunks.width) (balanceProds W ch) =
      ch.etaMem * pair (2 ^ W.chunks.width) (scattered W ch)[2] (idxAt W ch 3) +
        pair (2 ^ W.chunks.width) (scattered W ch)[4] (idxAt W ch 5) +
        ∑ j ∈ Finset.range (2 ^ W.chunks.width), idxAt W ch 8 j +
        ch.etaMem * pair (2 ^ W.chunks.width) (scattered W ch)[3] (idxAt W ch 10) +
        pair (2 ^ W.chunks.width) (scattered W ch)[5] (idxAt W ch 12) := by
    unfold cubeSum pair
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    obtain ⟨h2, h4, h9, h11⟩ := idxAt_scattered W ch j
    rw [termsAt_balance, h2, h4, h9, h11]
    ring
  rw [hsplit, sum_payload,
    pair_scattered W ch 2 (by decide) _ _ fun t ht acc hacc ↦ pair_step_mem W ch hS ht _ acc (hacc 2),
    pair_scattered W ch 4 (by decide) _ _ fun t ht acc hacc ↦ pair_step_bc W ch hS ht _ acc (hacc 4),
    pair_scattered W ch 3 (by decide) _ _ fun t ht acc hacc ↦ pair_step_word W ch hS ht _ acc (hacc 3),
    pair_scattered W ch 5 (by decide) _ _ fun t ht acc hacc ↦ pair_step_fp W ch hS ht _ acc (hacc 5)]
  simp only [rowShare, rowBal, Finset.sum_add_distrib, Finset.mul_sum]

end LeanVM.Prover.Complete

end
