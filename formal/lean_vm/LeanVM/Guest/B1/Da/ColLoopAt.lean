/-
  LeanVM.Guest.B1.Da.ColLoopAt

  The column loops `__loop90` and `__loop91` placed by the bump allocator (`RelAtIn`): each
  iteration's tail call right after its frame, its column after the tail's words.
-/

module

public import LeanVM.Guest.B1.Da.ColumnAt
public import LeanVM.Guest.B1.Da.Loops

/-!
# The column loops, placed

A loop helper places its tail call first, at `fp + fs L`, then its column. So iteration `j`
of a loop entered at `fp0` with `j0` lies at `fp0 + (j - j0)·fs L`, and its column at
`colPos … j`, after the words `clTot … (j + 1)` of the iterations after it (or the skipped tail's
frame at the last).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

open LeanVM.Guest.B1.Main (RelAtInW relAtInW_of_walk_loop)

@[expose] public section

/-- A column's memory: its vector hash's states, counter words, weights' run at `lv`, rows, gap
rows, tree at `node` and root slot. -/
def ColMem (store : Bool) (rd : Reader) (b r N lp : ℕ) (pb ct rb hs ctr node lv h0 h1 o0 o1 c0 c1 : E)
    (ws cv : List E) : Prop :=
  CellsAt rd (hs * (gen ^ b * gen ^ b)) [h0, h1] ∧
  CellsAt rd (hs * (gen ^ b * gen * (gen ^ b * gen))) [o0, o1] ∧
  CellsAt rd (ctr * (gen ^ b * gen ^ b * gen ^ b)) cv ∧
  (∀ k < 256, ∀ v, rd (lv.limb 0 * Parameters.gpow k) = some v → v = ws.getD k 0) ∧
  (∀ j < r, RowCell store rd lv rb (gen ^ b) node pb (gen ^ j)) ∧
  (∀ d < N - r, GapStep rd node (gen ^ r) (gen ^ d)) ∧
  Meaning_da_levels lp rd [node] [c0, c1] ∧
  CellsAt rd (ct * (gen ^ b * gen ^ b)) [c0, c1]

/-- A column's memory at `fp`: its tree right after its frame, its weights in its vector cell's
frame. -/
def ColAt (fs : String → ℕ) (cert : String → V → ℕ) (store : Bool) (rd : Reader)
    (b r N lp p t q h c : ℕ) (h0 h1 o0 o1 c0 c1 : E) (ws cv : List E) (fp : ℕ) : Prop :=
  ColMem store rd b r N lp (gen ^ p) (gen ^ t) (gen ^ q) (gen ^ h) (gen ^ c) (gen ^ (fp + fs (colName store)))
    (gen ^ (fp + fs (colName store) + 4 * N + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4)))
    h0 h1 o0 o1 c0 c1 ws cv

/-- The column loop's first and end columns. -/
def clLo (store : Bool) : ℕ := if store then 0 else 64
def clHi (store : Bool) : ℕ := if store then 64 else 128

/-- The words of the column loop from iteration `j`: each iteration's frame and column, then the
skipped tail's frame. -/
def clTot (fs : String → ℕ) (store : Bool) (r N lp j : ℕ) : ℕ :=
  fs (colLoopName store) +
    ((List.range (clHi store - j)).map fun i => fs (colLoopName store) + colTot fs store (j + i) r N lp).sum

/-- The position of iteration `b`'s column, the loop entered at `fp0`. -/
def colPos (fs : String → ℕ) (store : Bool) (r N lp fp0 b : ℕ) : ℕ :=
  fp0 + (b - clLo store) * fs (colLoopName store) + fs (colLoopName store) +
    (if b + 1 < clHi store then clTot fs store r N lp (b + 1) else fs (colLoopName store))

theorem clTot_succ (fs : String → ℕ) (store : Bool) (r N lp j : ℕ) (hj : j < clHi store) :
    clTot fs store r N lp j = fs (colLoopName store) +
      (if j + 1 < clHi store then clTot fs store r N lp (j + 1) else fs (colLoopName store)) +
      colTot fs store j r N lp := by
  unfold clTot
  obtain ⟨k, hk⟩ : ∃ k, clHi store - j = k + 1 := ⟨clHi store - j - 1, by omega⟩
  rw [hk, List.range_succ_eq_map, List.map_cons, List.sum_cons, Nat.add_zero]
  by_cases h1 : j + 1 < clHi store
  · rw [ite_pos' h1, show clHi store - (j + 1) = k by omega, List.map_map]
    simp only [Function.comp_def, Nat.add_succ, Nat.succ_add]
    ring
  · rw [ite_neg' h1, show k = 0 by omega]
    simp only [List.range_zero, List.map_nil, List.sum_nil]
    ring

theorem colLoopBody_split (store : Bool) : colLoopBody store = (colLoopBody store).dropLast ++ [.ret []] := by
  cases store <;> rfl

theorem colLoopPre_straight (store : Bool) : (colLoopBody store).dropLast.all Main.Stmt.straight = true := by
  cases store <;> rfl

theorem colLoopEnd_isInK (store : Bool) : IsInK (colLoopEnd store) := by
  rw [colLoopEnd_eq]; exact isInK_gen_pow _

/-- **One iteration of the column loop**: its column after its tail's words, its tail at
`fp + fs L` (or skipped at the last). -/
theorem colLoop_iter (fs : String → ℕ) (cert : String → V → ℕ) (store : Bool) {rd : Reader} {R : ℕ → Prop}
    {ps : List E} (hps : ps.length = 9) {j m n : ℕ} (hj : j < clHi store) (fp : ℕ)
    {Bc Bt : (String → ℕ) → ℕ}
    (hcol : RelAtInW fs cert wId rd R (fun _ => False) (fp + fs (colLoopName store) + m) n
      (colName store) (gen ^ j :: ps) [] Bc)
    (htail : if j + 1 < clHi store then RelAtInW fs cert wId rd R (fun _ => False) (fp + fs (colLoopName store))
      m (colLoopName store) (gen ^ (j + 1) :: ps) [] Bt else m = fs (colLoopName store)) :
    RelAtInW fs cert wId rd R (fun _ => False) fp (fs (colLoopName store) + m + n) (colLoopName store)
      (gen ^ j :: ps) [] fun θ => θ (colLoopName store) + Bc θ + Bt θ := by
  match ps, hps with
  | [nb, np, gap, glp, pb, ct, rb, hs, ctr], _ =>
  have hend : colLoopEnd store = gen ^ clHi store := by rw [colLoopEnd_eq]; cases store <;> rfl
  have hhi : clHi store ≤ 128 := by cases store <;> decide
  let σ : Val := listVal [gen ^ j, nb, np, gap, glp, pb, ct, rb, hs, ctr, gen, gen ^ (j + 1), colLoopEnd store,
    gen ^ (j + 1) + colLoopEnd store, gen, gen ^ (j + 1)]
  have h13 : σ (.n 13) ≠ 0 ↔ j + 1 < clHi store := by
    show gen ^ (j + 1) + colLoopEnd store ≠ 0 ↔ _
    rw [hend, ne_eq, e_add_eq_zero_iff]
    exact ⟨fun h => by by_contra h'; exact h (by rw [show j + 1 = clHi store by omega]),
      fun h he => by have := gen_pow_inj' (by omega) (by omega) he; omega⟩
  have hholds : Stmt.HoldsList (coreProgram.Rel rd) rd σ (colLoopBody store) False (fun rs => rs = []) := by
    simp only [colLoopBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
    refine ⟨hcol.toRelAtIn.relAt.rel, rfl, (pow_succ gen j).symm ▸ rfl, rfl, rfl, rfl, (pow_succ gen j).symm ▸ rfl,
      (isInK_add_left (isInK_gen_pow _)).mpr (colLoopEnd_isInK store), fun hne => ?_, trivial⟩
    have ht := (h13.mp hne)
    rw [ite_pos' ht] at htail
    exact htail.toRelAtIn.relAt.rel
  have hw : walk σ (colLoopBody store) = .ret ((colLoopBody store).dropLast.flatMap (Main.slEvs σ)) [] :=
    (congrArg (walk σ) (colLoopBody_split store)).trans (Main.walk_straight σ [] _ (colLoopPre_straight store))
  have hev := holds_of_holdsList (find_colLoop store) hholds hw
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ (colLoopPre_straight store)
  have hal0 : allocs σ ((colLoopBody store).dropLast.flatMap (Main.slEvs σ)) = [] := by
    rw [hal]; cases store <;> rfl
  have hcalls : calls ((colLoopBody store).dropLast.flatMap (Main.slEvs σ)) =
      [⟨colName store, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [], true⟩] ++
      [⟨colLoopName store, [.n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [],
        decide (σ (.n 13) ≠ 0)⟩] := by
    rw [hcl]; cases store <;> rfl
  have h := relAtInW_of_walk_loop (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False) (fp := fp) (m := m)
    (N := n) (bws := [Bc]) (bt := Bt) (find_colLoop store) (by cases store <;> decide +kernel) rfl hw rfl hev hcalls ?_
    (by rw [had, hal0]; cases store <;> rfl)
    (fun q hq => by
      rw [hadr, show (colLoopBody store).dropLast.filterMap Main.Stmt.addrS = [] by cases store <;> rfl] at hq
      simp at hq)
    (by rw [hal0]; exact ⟨n, 0, R, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), hcol, ⟨rfl, fun i h => h.elim⟩⟩)
    (fun i hi => Or.inl hi)
    (fun A hA => by
      rw [loadAddrs_straight σ _ (colLoopPre_straight store),
        show (colLoopBody store).dropLast.filterMap stmtLoad? = [] by cases store <;> rfl] at hA
      simp at hA)
    (fun _ h => h.elim)
  · simp only [hal0, List.sum_nil, Nat.add_zero, List.map_cons, List.map_nil, List.sum_cons] at h
    exact h
  · by_cases ht : j + 1 < clHi store
    · rw [ite_pos' ht] at htail
      simp only [decide_eq_true (h13.mpr ht), ↓reduceIte]
      exact htail
    · rw [ite_neg' ht] at htail
      have : ¬ σ (.n 13) ≠ 0 := fun h => ht (h13.mp h)
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact htail

/-- **The column loop at iteration `j`**, entered at `fp0`: every column after it placed at its
`colPos`, each on its `ColAt` memory. -/
theorem colLoop_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) (store : Bool) {r N lp p t q h c a pd : ℕ}
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hN : N = 2 ^ lp) (hlp : lp ≤ 10)
    {H0 H1 O0 O1 C0 C1 : ℕ → E} {WS CV : ℕ → List E} (hcl : ∀ b, (CV b).length = 4)
    (hch : ∀ b < 128, ChainCells (H0 b, H1 b) (vxBlocks ((WS b).getD · 0))
      (vxMd (decide (b = 127)) ((CV b).getD · 0)) 96 (O0 b, O1 b))
    {R : ℕ → Prop} (hRc : ∀ b < 128, ∀ k < 4, R (c + 3 * b + k)) (hRh : ∀ b < 128, ∀ k < 4, R (h + 2 * b + k))
    (hRt : ∀ b < 128, ∀ k < 2, R (t + 2 * b + k))
    (hRrow : ∀ b < clHi store, ∀ j < r, R (q + j) ∧ R (a + 129 * j + b) ∧ R (a + 129 * j + b + 1) ∧
      (store = true → R (p + j) ∧ R (pd + 128 * j + 2 * b) ∧ R (pd + 128 * j + 2 * b + 1)))
    (fp0 : ℕ) (rd : Reader)
    (hmem : ∀ b, clLo store ≤ b → b < clHi store → ColAt fs cert store rd b r N lp p t q h c (H0 b) (H1 b)
      (O0 b) (O1 b) (C0 b) (C1 b) (WS b) (CV b) (colPos fs store r N lp fp0 b))
    (hrb : ∀ j < r, rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → ∀ j < r, rd (gpow (p + j)) = some (gen ^ (pd + 128 * j))) :
    ∀ j, clLo store ≤ j → j < clHi store →
      RelAtInW fs cert wId rd R (fun _ => False) (fp0 + (j - clLo store) * fs (colLoopName store))
        (clTot fs store r N lp j) (colLoopName store)
        [gen ^ j, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
        fun θ => clTot θ store r N lp j := by
  have hhi : clHi store ≤ 128 := by cases store <;> decide
  have hlohi : ∀ j, j < clHi store → j + 1 < clHi store ∨ j + 1 = clHi store := fun j _ => by omega
  suffices H : ∀ k j, j + k + 1 = clHi store → clLo store ≤ j →
      RelAtInW fs cert wId rd R (fun _ => False) (fp0 + (j - clLo store) * fs (colLoopName store))
        (clTot fs store r N lp j) (colLoopName store)
        [gen ^ j, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
        (fun θ => clTot θ store r N lp j) from
    fun j hj1 hj2 => H (clHi store - j - 1) j (by omega) hj1
  have hcol : ∀ j, clLo store ≤ j → j < clHi store →
      RelAtInW fs cert wId rd R (fun _ => False) (colPos fs store r N lp fp0 j)
        (colTot fs store j r N lp) (colName store)
        [gen ^ j, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
        (fun θ => colTot θ store j r N lp) :=
    fun j hj1 hj2 => by
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hmem j hj1 hj2
      exact col_relAtIn fs cert store (by omega) hr1 hrN hN hlp (hcl j) (hch j (by omega)) (hRc j (by omega))
        (hRh j (by omega)) (hRt j (by omega)) (hRrow j (by omega)) _ rd m1 m2 m3
        (fun k hk v hv => m4 k hk v (by rwa [limb0_gen_pow, gpow_add'])) m5 hrb hpb m6 m7 m8
  intro k
  induction k with
  | zero =>
    intro j hj hlo
    have hlast : ¬ j + 1 < clHi store := by omega
    have := colLoop_iter fs cert store (ps := [gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t,
      gen ^ q, gen ^ h, gen ^ c]) rfl (j := j) (m := fs (colLoopName store)) (by omega)
      (fp0 + (j - clLo store) * fs (colLoopName store)) (Bt := fun θ => θ (colLoopName store))
      (by have := hcol j hlo (by omega); rwa [colPos, ite_neg' hlast] at this) (by rw [ite_neg' hlast])
    rw [clTot_succ fs store r N lp j (by omega), ite_neg' hlast]
    refine this.wmono fun θ => ?_
    rw [clTot_succ θ store r N lp j (by omega), ite_neg' hlast]
    omega
  | succ k ih =>
    intro j hj hlo
    have hnext : j + 1 < clHi store := by omega
    have ht := ih (j + 1) (by omega) (by omega)
    rw [show j + 1 - clLo store = (j - clLo store) + 1 by omega, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at ht
    have := colLoop_iter fs cert store (ps := [gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t,
      gen ^ q, gen ^ h, gen ^ c]) rfl (j := j) (m := clTot fs store r N lp (j + 1)) (by omega)
      (fp0 + (j - clLo store) * fs (colLoopName store))
      (by have := hcol j hlo (by omega); rwa [colPos, ite_pos' hnext] at this) (by rw [ite_pos' hnext]; exact ht)
    rw [clTot_succ fs store r N lp j (by omega), ite_pos' hnext]
    refine this.wmono fun θ => ?_
    rw [clTot_succ θ store r N lp j (by omega), ite_pos' hnext]
    omega

end
end LeanVM.Guest.B1.Digest
