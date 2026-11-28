/-
  LeanVM.Guest.B1.Link.RoundsLoop

  `link_rounds`' loop helper and the function itself, as templates.
-/

module

public import LeanVM.Guest.B1.Link.RoundsLast
public import LeanVM.Guest.B1.Common.Loops
public import LeanVM.Guest.B1.Link.IndexSide

/-!
# `link_rounds`: the templates

`link_rounds(fs0..fs4, cursor, claim, point, count_g, tabs, n_tail, bits)` (G) splits the round
count `count = 4 h + r` from six hinted bits (`split_count`), stores the first record (the
capacity, the cursor, the claim) at a fresh buffer `recs`, runs the loop helper over `x = g^j`,
`j < h` (`lrLoopBody`: four rounds from the record at `recs·x^7` to the next, their challenges at
`point·x^4`), then `link_rounds_last` on the record at `recs·g^(7h)` for the `r` rounds left, and
returns the record after them (`lrMainBody`).
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The loop helper's four rounds. -/
def lrLoopRounds (nt bits : ℕ) : List Stmt × List ℕ × ℕ × ℕ × ℕ × Option ℕ :=
  lrRounds nt bits 12 4 4 20 [13, 14, 15, 16, 17] 18 19 none

/-- **The loop helper's body** (parameters `x, N, recs, point, tabs`): `rd = recs·x^7`,
`pts = point·x^4`, the record read, four rounds, the next record stored at `rd·g^7`, then the
call at `x·g` while `x·g ≠ N`. -/
def lrLoopBody (nt bits : ℕ) (name : String) : List Stmt :=
  let rs := lrLoopRounds nt bits
  let V := rs.2.2.2.2.1
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 0)), .atom (.mul (.n 9) (.n 2) (.n 8)), .atom (.mul (.n 10) (.n 0) (.n 0)),
    .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 3) (.n 11)),
    .atom (.load (.n 13) (.n 9) 0), .atom (.load (.n 14) (.n 9) 1), .atom (.load (.n 15) (.n 9) 2),
    .atom (.load (.n 16) (.n 9) 3), .atom (.load (.n 17) (.n 9) 4), .atom (.load (.n 18) (.n 9) 5),
    .atom (.load (.n 19) (.n 9) 6)] ++ rs.1 ++
  ((List.range 5).map fun j ↦ .atom (.load (.n (rs.2.1.getD j 0)) (.n 9) (7 + j))) ++
  [.atom (.load (.n rs.2.2.1) (.n 9) 12), .atom (.load (.n rs.2.2.2.1) (.n 9) 13),
    .atom (.const (.n V) (word 2 0)), .atom (.mul (.n (V + 1)) (.n 0) (.n V)),
    .atom (.add (.n (V + 2)) (.n (V + 1)) (.n 1)), .atom (.const (.n (V + 3)) (word 2 0)),
    .atom (.mul (.n (V + 4)) (.n 0) (.n (V + 3))),
    .callIf (.n (V + 2)) name [.n (V + 4), .n 1, .n 2, .n 3, .n 4], .ret []]

/-- `split_count`'s factor at bit `k`: `1 + b·(1 + g^(2^(k mod 2 or k - 2)))`. -/
def lrSplitFactor (k : ℕ) : ℕ := if k < 2 then 2 ^ (2 ^ k) + 1 else 2 ^ (2 ^ (k - 2)) + 1

/-- **`link_rounds`' body** (parameters `fs0..fs4, cursor, claim, point, count_g, tabs`). -/
def lrMainBody (loop : String) (lasts : List String) : List Stmt :=
  [.atom (.hint (.bitsExp (.n 8) 6 (.stack [.n 10, .n 11, .n 12, .n 13, .n 14, .n 15]))),
    .atom (.mul (.n 10) (.n 10) (.n 10)), .atom (.const (.n 16) (word 1 0)), .atom (.const (.n 17) (word 3 0)),
    .atom (.mul (.n 18) (.n 10) (.n 17)), .atom (.add (.n 19) (.n 16) (.n 18)),
    .atom (.mul (.n 11) (.n 11) (.n 11)), .atom (.const (.n 20) (word 1 0)), .atom (.const (.n 21) (word 5 0)),
    .atom (.mul (.n 22) (.n 11) (.n 21)), .atom (.add (.n 23) (.n 20) (.n 22)),
    .atom (.mul (.n 24) (.n 19) (.n 23)),
    .atom (.mul (.n 12) (.n 12) (.n 12)), .atom (.const (.n 25) (word 1 0)), .atom (.const (.n 26) (word 3 0)),
    .atom (.mul (.n 27) (.n 12) (.n 26)), .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.mul (.n 13) (.n 13) (.n 13)), .atom (.const (.n 29) (word 1 0)), .atom (.const (.n 30) (word 5 0)),
    .atom (.mul (.n 31) (.n 13) (.n 30)), .atom (.add (.n 32) (.n 29) (.n 31)),
    .atom (.mul (.n 33) (.n 28) (.n 32)),
    .atom (.mul (.n 14) (.n 14) (.n 14)), .atom (.const (.n 34) (word 1 0)), .atom (.const (.n 35) (word 17 0)),
    .atom (.mul (.n 36) (.n 14) (.n 35)), .atom (.add (.n 37) (.n 34) (.n 36)),
    .atom (.mul (.n 38) (.n 33) (.n 37)),
    .atom (.mul (.n 15) (.n 15) (.n 15)), .atom (.const (.n 39) (word 1 0)), .atom (.const (.n 40) (word 257 0)),
    .atom (.mul (.n 41) (.n 15) (.n 40)), .atom (.add (.n 42) (.n 39) (.n 41)),
    .atom (.mul (.n 43) (.n 38) (.n 42)),
    .atom (.mul (.n 44) (.n 43) (.n 43)), .atom (.mul (.n 45) (.n 44) (.n 44)),
    .atom (.mul (.n 46) (.n 45) (.n 24)), .atom (.assertEq (.n 46) (.n 8)),
    .atom (.const (.n 47) (word 4 0)), .atom (.mul (.n 48) (.n 43) (.n 47)),
    .atom (.mul (.n 49) (.n 48) (.n 48)), .atom (.mul (.n 50) (.n 49) (.n 48)),
    .atom (.mul (.n 51) (.n 50) (.n 50)), .atom (.mul (.n 52) (.n 51) (.n 48)),
    .atom (.hint (.allocDyn (.n 53) (.n 52))),
    .atom (.load (.n 0) (.n 53) 0), .atom (.load (.n 1) (.n 53) 1), .atom (.load (.n 2) (.n 53) 2),
    .atom (.load (.n 3) (.n 53) 3), .atom (.load (.n 4) (.n 53) 4), .atom (.load (.n 5) (.n 53) 5),
    .atom (.load (.n 6) (.n 53) 6),
    .atom (.const (.n 54) (word 1 0)), .atom (.add (.n 55) (.n 54) (.n 43)), .atom (.const (.n 56) (word 1 0)),
    .callIf (.n 55) loop [.n 56, .n 43, .n 53, .n 7, .n 9],
    .atom (.mul (.n 57) (.n 43) (.n 43)), .atom (.mul (.n 58) (.n 57) (.n 43)),
    .atom (.mul (.n 59) (.n 58) (.n 58)), .atom (.mul (.n 60) (.n 59) (.n 43)),
    .atom (.mul (.n 61) (.n 53) (.n 60)), .atom (.const (.n 62) (word 128 0)),
    .atom (.mul (.n 63) (.n 61) (.n 62)), .atom (.mul (.n 64) (.n 43) (.n 43)),
    .atom (.mul (.n 65) (.n 64) (.n 64)), .atom (.mul (.n 66) (.n 7) (.n 65)),
    .dispatch (.n 24) lasts [.n 61, .n 63, .n 66, .n 9] [.n 67],
    .atom (.load (.n 68) (.n 61) 7), .atom (.load (.n 69) (.n 61) 8), .atom (.load (.n 70) (.n 61) 9),
    .atom (.load (.n 71) (.n 61) 10), .atom (.load (.n 72) (.n 61) 11), .atom (.load (.n 73) (.n 61) 12),
    .atom (.load (.n 74) (.n 61) 13), .ret [.n 68, .n 69, .n 70, .n 71, .n 72, .n 73, .n 74]]

/-! ## The loop helper -/

/-- The loop helper's atoms, before its conditional call. -/
def lrLoopA (nt bits : ℕ) : List Stmt :=
  let rs := lrLoopRounds nt bits
  let V := rs.2.2.2.2.1
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 0)), .atom (.mul (.n 9) (.n 2) (.n 8)), .atom (.mul (.n 10) (.n 0) (.n 0)),
    .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 3) (.n 11)),
    .atom (.load (.n 13) (.n 9) 0), .atom (.load (.n 14) (.n 9) 1), .atom (.load (.n 15) (.n 9) 2),
    .atom (.load (.n 16) (.n 9) 3), .atom (.load (.n 17) (.n 9) 4), .atom (.load (.n 18) (.n 9) 5),
    .atom (.load (.n 19) (.n 9) 6)] ++ rs.1 ++
  ((List.range 5).map fun j ↦ .atom (.load (.n (rs.2.1.getD j 0)) (.n 9) (7 + j))) ++
  [.atom (.load (.n rs.2.2.1) (.n 9) 12), .atom (.load (.n rs.2.2.2.1) (.n 9) 13),
    .atom (.const (.n V) (word 2 0)), .atom (.mul (.n (V + 1)) (.n 0) (.n V)),
    .atom (.add (.n (V + 2)) (.n (V + 1)) (.n 1)), .atom (.const (.n (V + 3)) (word 2 0)),
    .atom (.mul (.n (V + 4)) (.n 0) (.n (V + 3)))]

theorem lrLoopBody_eq (nt bits : ℕ) (name : String) :
    lrLoopBody nt bits name = lrLoopA nt bits ++
      [.callIf (.n ((lrLoopRounds nt bits).2.2.2.2.1 + 2)) name
        [.n ((lrLoopRounds nt bits).2.2.2.2.1 + 4), .n 1, .n 2, .n 3, .n 4], .ret []] := by
  simp only [lrLoopBody, lrLoopA, List.append_assoc, List.cons_append, List.nil_append]

theorem lrLoopA_atoms (nt bits : ℕ) : AllAtoms (lrLoopA nt bits) := by
  unfold lrLoopA
  refine allAtoms_append (allAtoms_append (allAtoms_append ?_ (lrRounds_atoms _ _ _ _ _ _ _ _ _ _))
    (fun s hs ↦ ?_)) ?_
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, rfl⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- What one iteration of the loop establishes at `x`: four rounds from the record at `recs·x^7`
to the record at `recs·x^7·g^7`, the challenges at `point·x^4`. -/
def LoopIter (rd : Reader) (nt bits : ℕ) (x recs point tabs : E) : Prop :=
  (bits ≠ 0 → WinTabs rd tabs) → ∃ (st : RSt) (l : List (E × RSt)), st.cap.length = 5 ∧
    ReadsAt rd (recs * x ^ 7) st.cells ∧ l.length = 4 ∧ RoundChain rd nt bits st l ∧
    ReadsAt rd (point * x ^ 4) (l.map Prod.fst) ∧ ReadsAt rd (recs * x ^ 7 * gen ^ 7) (chainLast st l).cells

theorem readsAt_shift7 {rd : Reader} {p : E} {xs : List E} (h : ∀ j (hj : j < xs.length), LoadHolds rd p (7 + j) xs[j]) :
    ReadsAt rd (p * gen ^ 7) xs := fun j hj ↦ (loadHolds_mul_gen_pow rd p 7 j _).mpr (h j hj)

/-- **An iteration's atoms** establish `LoopIter`. -/
theorem lrLoop_iter {rd : Reader} {nt bits : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32)
    (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3)) (hgc : bits ≠ 0 → GcSound1 rd) {σ : Val}
    (hA : ∀ a, Stmt.atom a ∈ lrLoopA nt bits → a.Holds rd σ) :
    LoopIter rd nt bits (σ (.n 0)) (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) := by
  intro hw
  generalize hrs : lrLoopRounds nt bits = rs at hA
  have hlen : rs.2.1.length = 5 := by
    rw [← hrs]; exact lrRounds_cap_length _ _ _ _ _ _ _ _ _ _ rfl
  have mem := fun a (ha : a ∈ [Atom.mul (.n 5) (.n 0) (.n 0), .mul (.n 6) (.n 5) (.n 0), .mul (.n 7) (.n 6) (.n 6),
      .mul (.n 8) (.n 7) (.n 0), .mul (.n 9) (.n 2) (.n 8), .mul (.n 10) (.n 0) (.n 0),
      .mul (.n 11) (.n 10) (.n 10), .mul (.n 12) (.n 3) (.n 11),
      .load (.n 13) (.n 9) 0, .load (.n 14) (.n 9) 1, .load (.n 15) (.n 9) 2,
      .load (.n 16) (.n 9) 3, .load (.n 17) (.n 9) 4, .load (.n 18) (.n 9) 5, .load (.n 19) (.n 9) 6]) ↦
    hA a (by
      unfold lrLoopA; rw [hrs]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp)
  have m5 := mem (.mul (.n 5) (.n 0) (.n 0)) (by simp)
  have m6 := mem (.mul (.n 6) (.n 5) (.n 0)) (by simp)
  have m7 := mem (.mul (.n 7) (.n 6) (.n 6)) (by simp)
  have m8 := mem (.mul (.n 8) (.n 7) (.n 0)) (by simp)
  have m9 := mem (.mul (.n 9) (.n 2) (.n 8)) (by simp)
  have m10 := mem (.mul (.n 10) (.n 0) (.n 0)) (by simp)
  have m11 := mem (.mul (.n 11) (.n 10) (.n 10)) (by simp)
  have m12 := mem (.mul (.n 12) (.n 3) (.n 11)) (by simp)
  have l0 := mem (.load (.n 13) (.n 9) 0) (by simp)
  have l1 := mem (.load (.n 14) (.n 9) 1) (by simp)
  have l2 := mem (.load (.n 15) (.n 9) 2) (by simp)
  have l3 := mem (.load (.n 16) (.n 9) 3) (by simp)
  have l4 := mem (.load (.n 17) (.n 9) 4) (by simp)
  have l5 := mem (.load (.n 18) (.n 9) 5) (by simp)
  have l6 := mem (.load (.n 19) (.n 9) 6) (by simp)
  simp only [Atom.Holds] at m5 m6 m7 m8 m9 m10 m11 m12 l0 l1 l2 l3 l4 l5 l6
  have h9 : σ (.n 9) = σ (.n 2) * σ (.n 0) ^ 7 := by rw [m9, m8, m7, m6, m5]; ring
  have h12 : σ (.n 12) = σ (.n 3) * σ (.n 0) ^ 4 := by rw [m12, m11, m10]; ring
  have hR : ∀ a, Stmt.atom a ∈ (lrRounds nt bits 12 4 4 20 [13, 14, 15, 16, 17] 18 19 none).1 → a.Holds rd σ :=
    fun a ha ↦ hA a (by
      unfold lrLoopA; rw [hrs]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (by rw [← hrs]; exact ha))))
  obtain ⟨l, hl, hc, hlast, hpts, -⟩ := lrRounds_sound hnt hnt' hk (fun hb ↦ ⟨hgc hb, hw hb⟩) 4 20
    [13, 14, 15, 16, 17] 18 19 none hR (fun z hz ↦ absurd hz (by simp))
  have hS : ∀ a ∈ ((List.range 5).map fun j ↦ Stmt.atom (.load (.n (rs.2.1.getD j 0)) (.n 9) (7 + j))) ++
      [.atom (.load (.n rs.2.2.1) (.n 9) 12), .atom (.load (.n rs.2.2.2.1) (.n 9) 13)],
      ∃ b, a = .atom b ∧ b.Holds rd σ := fun a ha ↦ by
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact ⟨_, rfl, hA _ (by
        unfold lrLoopA; rw [hrs]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩)))⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, rfl, hA _ (by unfold lrLoopA; rw [hrs]; simp)⟩
      · exact ⟨_, rfl, hA _ (by unfold lrLoopA; rw [hrs]; simp)⟩
  have hrs' : lrRounds nt bits 12 4 4 20 [13, 14, 15, 16, 17] 18 19 none = rs := hrs
  rw [hrs'] at hlast
  refine ⟨_, l, rfl, ?_, hl, hc, by rw [← h12]; exact hpts, ?_⟩
  · rw [← h9]
    exact readsAt_cells rfl (fun j hj ↦ match j, hj with
      | 0, _ => l0 | 1, _ => l1 | 2, _ => l2 | 3, _ => l3 | 4, _ => l4) l5 l6
  · rw [hlast, ← h9]
    apply readsAt_shift7
    intro j hj
    simp only [RSt.cells, rstOf, List.length_append, List.length_map, hlen, List.length_cons,
      List.length_nil] at hj
    rcases Nat.lt_or_ge j 5 with h | h
    · obtain ⟨b, hb, hh⟩ := hS (.atom (.load (.n (rs.2.1.getD j 0)) (.n 9) (7 + j)))
        (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr h, rfl⟩))
      cases hb
      simp only [Atom.Holds] at hh
      simpa [RSt.cells, rstOf, h, hlen, List.getElem_append_left, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show j < rs.2.1.length by omega)] using hh
    · obtain ⟨b5, hb5, hh5⟩ := hS (.atom (.load (.n rs.2.2.1) (.n 9) 12)) (by simp)
      obtain ⟨b6, hb6, hh6⟩ := hS (.atom (.load (.n rs.2.2.2.1) (.n 9) 13)) (by simp)
      cases hb5; cases hb6
      simp only [Atom.Holds] at hh5 hh6
      interval_cases j
      · simpa [RSt.cells, rstOf, hlen] using hh5
      · simpa [RSt.cells, rstOf, hlen] using hh6

/-- **The loop helper's relation**: from `x = g^0` to `N = g^q`, `1 ≤ q < ord g`, every iteration
`j < q` establishes `LoopIter` at `g^j`. -/
theorem lrLoop_rel {rd : Reader} {nt bits : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32)
    (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3)) (hgc : bits ≠ 0 → GcSound1 rd) {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hbody : fn.body = lrLoopBody nt bits name) {q : ℕ} (hq1 : 1 ≤ q) (hq : q < ordG) (recs point tabs : E)
    (h : coreProgram.Rel rd name [gen ^ 0, gen ^ q, recs, point, tabs] []) :
    ∀ j < q, LoopIter rd nt bits (gen ^ j) recs point tabs := by
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) name (x :: [gen ^ q, recs, point, tabs]) [] ↔
      AtomsBody rd fn.params (lrLoopA nt bits) (x :: gen ^ q :: [recs, point, tabs]) ∧
        IsInK (x * gen + gen ^ q) ∧
        (x * gen + gen ^ q ≠ 0 → coreProgram.relN rd d name (x * gen :: [gen ^ q, recs, point, tabs]) []) := by
    intro d x
    refine loop_step_atoms hf (by rw [hbody, lrLoopBody_eq]) (lrLoopA_atoms nt bits) (fun σ hp hall ↦ ?_) d
    rw [hparams] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨h0, h1, h2, h3, h4, -⟩ := hp
    set V := (lrLoopRounds nt bits).2.2.2.2.1
    have mem : ∀ a ∈ [Atom.const (.n V) (word 2 0), .mul (.n (V + 1)) (.n 0) (.n V),
        .add (.n (V + 2)) (.n (V + 1)) (.n 1), .const (.n (V + 3)) (word 2 0),
        .mul (.n (V + 4)) (.n 0) (.n (V + 3))], a.Holds rd σ := fun a ha ↦ hall a (by
      unfold lrLoopA
      refine List.mem_append_right _ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [V])
    have a0 := mem (.const (.n V) (word 2 0)) (by simp)
    have a1 := mem (.mul (.n (V + 1)) (.n 0) (.n V)) (by simp)
    have a2 := mem (.add (.n (V + 2)) (.n (V + 1)) (.n 1)) (by simp)
    have a3 := mem (.const (.n (V + 3)) (word 2 0)) (by simp)
    have a4 := mem (.mul (.n (V + 4)) (.n 0) (.n (V + 3))) (by simp)
    simp only [Atom.Holds, word_gen] at a0 a1 a2 a3 a4
    refine ⟨by rw [a2, a1, a0, h0, h1], ?_⟩
    simp only [List.map_cons, List.map_nil, a4, a3, h0, h1, h2, h3, h4]
  have hl := (loop_iff (P := coreProgram) (f := name) (B := fun x ↦
    AtomsBody rd fn.params (lrLoopA nt bits) (x :: gen ^ q :: [recs, point, tabs])) hstep 0).mp h
  obtain ⟨m, hm0, hN, hfirst, hall⟩ := hl
  have hmq : m = q := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hm' : m < ordG := by omega
      exact absurd (gen_pow_inj (by unfold ordG at hm'; omega) (by unfold ordG at hq; omega) hN) (by omega)
    · exact hfirst q (by omega) hgt rfl
  intro j hj
  obtain ⟨σ, hp, hall'⟩ := hall j (by omega) (by omega)
  rw [hparams] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, -, h2, h3, h4, -⟩ := hp
  have := lrLoop_iter hnt hnt' hk hgc hall'
  rwa [h0, h2, h3, h4] at this

/-! ## `link_rounds` -/

/-- **`link_rounds__L{nt}_L{bits}(fs0..fs4, cursor, claim, point, count_g, tabs)`**: `count_g` is
`g^count`, `count < 64`; when the rounds grind, with `tabs` the windows table, a chain of `count`
rounds from the state `fs0..fs4, cursor, claim`, the challenges at `point`, returning the state
after them. -/
def MeaningLR (nt bits : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, cl, point, cg, tabs], rets => ∃ cnt < 64, cg = gen ^ cnt ∧
      ((bits ≠ 0 → WinTabs rd tabs) → ∃ l : List (E × RSt), l.length = cnt ∧
        RoundChain rd nt bits ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l ∧ ReadsAt rd point (l.map Prod.fst) ∧
        rets = (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cells)
  | _, _ => False

theorem word_two_pow_xor_one {a : ℕ} (ha : a < 64) : word (2 ^ a ^^^ 1) 0 = gen ^ a + 1 := by
  rw [word_eOfNat, eOfNat_xor, eOfNat_one, ← word_eOfNat, word_two_pow ha]

/-- A hinted bit's factor in the exponent. -/
theorem bit_factor {b : E} (hb : b = b * b) (a : ℕ) :
    1 + b * (gen ^ a + 1) = gen ^ (a * if b = 1 then 1 else 0) := by
  have := bitE_of_mul_self hb.symm
  by_cases h1 : b = 1
  · subst h1
    simp only [one_mul, ↓reduceIte, mul_one]
    rw [add_comm, add_assoc, add_self_E, add_zero]
  · rw [this]
    simp [Value.bitE, h1]

/-- A bit's value. -/
def bv (b : E) : ℕ := if b = 1 then 1 else 0

theorem bv_le (b : E) : bv b ≤ 1 := by unfold bv; split <;> omega

theorem rst_eq_of_cells {st st' : RSt} (h1 : st.cap.length = 5) (h2 : st'.cap.length = 5)
    (h : st.cells = st'.cells) : st = st' := by
  obtain ⟨c, u, l⟩ := st
  obtain ⟨c', u', l'⟩ := st'
  simp only [RSt.cells] at h h1 h2
  have := List.append_inj h (by rw [h1, h2])
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

theorem readsAt_cells_unique {rd : Reader} {p : E} {st st' : RSt} (h1 : st.cap.length = 5)
    (h2 : st'.cap.length = 5) (r1 : ReadsAt rd p st.cells) (r2 : ReadsAt rd p st'.cells) : st = st' :=
  rst_eq_of_cells h1 h2 (readsAt_unique r1 r2 (by simp [RSt.cells, h1, h2]))

theorem chainLast_cap_length {rd : Reader} {nt bits : ℕ} : ∀ {st : RSt} {l : List (E × RSt)},
    st.cap.length = 5 → RoundChain rd nt bits st l → (chainLast st l).cap.length = 5
  | _, [], h, _ => h
  | _, (_, st') :: l, _, ⟨⟨_, _, _, _, _, _, hgs, _⟩, hc⟩ => by
    apply chainLast_cap_length (st := st') _ hc
    have := congrArg (fun p ↦ p.2.cap) hgs
    simp only at this
    rw [← this]
    unfold Fs.grindSqueeze
    split <;> simp [Fs.squeeze, capOf]


/-- **`link_rounds`' template implies its meaning**, given its loop's and its last arms'. -/
theorem lrMain_sound {rd : Reader} {nt bits : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32)
    (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3)) (hgc : bits ≠ 0 → GcSound1 rd) {name loopName : String}
    {lasts : List String} {fn loopFn : Fn} (hf : coreProgram.find? name = some fn)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9])
    (hbody : fn.body = lrMainBody loopName lasts) (hlf : coreProgram.find? loopName = some loopFn)
    (hlp : loopFn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hlb : loopFn.body = lrLoopBody nt bits loopName)
    (hll : lasts.length = 4) (hlasts : ∀ k (hk : k < lasts.length) args rets, coreProgram.Rel rd lasts[k] args rets →
      MeaningLRLast nt bits k rd args rets)
    (args rets : List E) :
    coreProgram.Rel rd name args rets → MeaningLR nt bits rd args rets := by
  rw [rel_iff_sem hf, hbody, hparams]
  rintro ⟨σ, rfl, h⟩
  simp only [lrMainBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and] at h
  obtain ⟨b0, c16, c17, m18, a19, b1, c20, c21, m22, a23, m24, b2, c25, c26, m27, a28, b3, c29, c30,
    m31, a32, m33, b4, c34, c35, m36, a37, m38, b5, c39, c40, m41, a42, m43, m44, m45, m46, hassert,
    c47, m48, m49, m50, m51, m52, s0, s1, s2, s3, s4, s5, s6, c54, a55, c56, hK55, hcall, m57, m58, m59,
    m60, m61, c62, m63, m64, m65, m66, ⟨j, hj, hj24, hlast⟩, r68, r69, r70, r71, r72, r73, r74, hret⟩ := h
  -- the split count
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := word_two_pow_xor_one (a := 8) (by norm_num)
  have hrg : σ (.n 24) = gen ^ (bv (σ (.n 10)) + 2 * bv (σ (.n 11))) := by
    rw [m24, a19, a23, m18, m22, c16, c17, c20, c21, w3, w5, word_one, bit_factor b0, bit_factor b1,
      ← pow_add]
    simp only [bv, one_mul]
  have hqg : σ (.n 43) = gen ^ (bv (σ (.n 12)) + 2 * bv (σ (.n 13)) + 4 * bv (σ (.n 14)) + 8 * bv (σ (.n 15))) := by
    rw [m43, m38, m33, a28, a32, a37, a42, m27, m31, m36, m41, c25, c26, c29, c30, c34, c35, c39, c40, w3, w5,
      w17, w257, word_one, bit_factor b2, bit_factor b3, bit_factor b4, bit_factor b5, ← pow_add, ← pow_add,
      ← pow_add]
    simp only [bv, one_mul]
  set rv := bv (σ (.n 10)) + 2 * bv (σ (.n 11)) with hrv
  set qv := bv (σ (.n 12)) + 2 * bv (σ (.n 13)) + 4 * bv (σ (.n 14)) + 8 * bv (σ (.n 15)) with hqv
  have hrv4 : rv < 4 := by have := bv_le (σ (.n 10)); have := bv_le (σ (.n 11)); omega
  have hqv16 : qv < 16 := by
    have := bv_le (σ (.n 12)); have := bv_le (σ (.n 13)); have := bv_le (σ (.n 14))
    have := bv_le (σ (.n 15)); omega
  have hcg : σ (.n 8) = gen ^ (4 * qv + rv) := by
    have : σ (.n 8) = σ (.n 46) := by linear_combination hassert.symm + σ (.n 8) * two_eq_zero_E
    rw [this, m46, m45, m44, hqg, hrg]
    ring
  refine ⟨4 * qv + rv, by omega, hcg, fun hw ↦ ?_⟩
  -- the records
  set st0 : RSt := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], σ (.n 5), σ (.n 6)⟩
  have hst0 : ReadsAt rd (σ (.n 53)) st0.cells := by
    intro i hi
    simp only [st0, RSt.cells, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hi ⊢
    match i, hi with
    | 0, _ => exact s0 | 1, _ => exact s1 | 2, _ => exact s2 | 3, _ => exact s3
    | 4, _ => exact s4 | 5, _ => exact s5 | 6, _ => exact s6
  have hloop : ∀ m < qv, LoopIter rd nt bits (gen ^ m) (σ (.n 53)) (σ (.n 7)) (σ (.n 9)) := by
    intro m hm
    have hq0 : σ (.n 55) ≠ 0 := by
      rw [a55, c54, word_one, hqg]
      intro h0
      have : gen ^ qv = 1 := by linear_combination h0 - two_eq_zero_E
      rw [gen_pow_eq_one_iff (by omega)] at this
      omega
    have hc := hcall hq0
    rw [c56, word_one, hqg, ← pow_zero gen] at hc
    exact lrLoop_rel hnt hnt' hk hgc hlf hlp hlb (by omega) (by unfold ordG; omega) _ _ _ hc m hm
  have hchain : ∀ m ≤ qv, ∃ l : List (E × RSt), l.length = 4 * m ∧ RoundChain rd nt bits st0 l ∧
      ReadsAt rd (σ (.n 7)) (l.map Prod.fst) ∧ ReadsAt rd (σ (.n 53) * gen ^ (7 * m)) (chainLast st0 l).cells ∧
      (chainLast st0 l).cap.length = 5 := by
    intro m hm
    induction m with
    | zero => exact ⟨[], rfl, trivial, readsAt_nil _ _, by rw [Nat.mul_zero, pow_zero, mul_one]; exact hst0, rfl⟩
    | succ m ih =>
      obtain ⟨l, hl, hc, hp, hr, hcl⟩ := ih (by omega)
      obtain ⟨st, l', hst, hrs, hl', hc', hp', hr'⟩ := hloop m (by omega) hw
      rw [← pow_mul, mul_comm m 7] at hrs hr'
      have e := readsAt_cells_unique hst hcl hrs hr
      subst e
      refine ⟨l ++ l', by simp [hl, hl']; ring, roundChain_append hc hc', ?_, ?_, ?_⟩
      · rw [List.map_append]
        refine readsAt_append_shift hp ?_
        rw [List.length_map, hl, ← pow_mul, mul_comm 4 m] at *
        exact hp'
      · rw [chainLast_append', mul_add, mul_one, pow_add, ← mul_assoc]
        exact hr'
      · rw [chainLast_append']
        exact chainLast_cap_length hst hc'
  obtain ⟨l, hl, hc, hp, hr, hcl⟩ := hchain qv le_rfl
  -- the last arm
  have hjr : j = rv := by
    rw [hrg, ← gen_pow_eq_ofK] at hj24
    exact (gen_pow_inj (by omega) (by omega) hj24).symm
  obtain ⟨-, hmeaning⟩ := hlasts j hj _ _ hlast
  rw [hjr] at hmeaning
  obtain ⟨st, l', hst, hrs, hl', hc', hp', hr'⟩ := hmeaning hw
  have h61 : σ (.n 61) = σ (.n 53) * gen ^ (7 * qv) := by
    rw [m61, m60, m59, m58, m57, hqg]
    ring
  have h63 : σ (.n 63) = σ (.n 61) * gen ^ 7 := by
    rw [m63, c62, show (128 : ℕ) = 2 ^ 7 from rfl, word_two_pow (by norm_num)]
  have h66 : σ (.n 66) = σ (.n 7) * gen ^ (4 * qv) := by
    rw [m66, m65, m64, hqg]
    ring
  rw [h61] at hrs
  have e := readsAt_cells_unique hst hcl hrs hr
  subst e
  refine ⟨l ++ l', by simp [hl, hl'], roundChain_append hc hc', ?_, ?_⟩
  · rw [List.map_append]
    refine readsAt_append_shift hp ?_
    rw [List.length_map, hl, ← h66]
    exact hp'
  · rw [chainLast_append']
    have hout : ReadsAt rd (σ (.n 63)) [σ (.n 68), σ (.n 69), σ (.n 70), σ (.n 71), σ (.n 72), σ (.n 73), σ (.n 74)] := by
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      rw [h63, loadHolds_mul_gen_pow]
      match i, hi with
      | 0, _ => exact r68 | 1, _ => exact r69 | 2, _ => exact r70 | 3, _ => exact r71
      | 4, _ => exact r72 | 5, _ => exact r73 | 6, _ => exact r74
    have hlen : ((chainLast (chainLast st0 l) l').cells).length = 7 := by
      simp [RSt.cells, chainLast_cap_length hcl hc']
    rw [← hret]
    exact (readsAt_unique hr' hout (by rw [hlen]; rfl)).symm
/-! ## The bodies -/

set_option maxRecDepth 100000 in
theorem lrLoop_L1_L0_body :
    Fn.body (fn% «link_rounds__L1_L0_loop0») = lrLoopBody 1 0 "__loop0_link_rounds__L1_L0" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrMain_L1_L0_body :
    Fn.body (fn% «link_rounds__L1_L0») = lrMainBody "__loop0_link_rounds__L1_L0"
      ["link_rounds_last__L1_L0_L0", "link_rounds_last__L1_L0_L1", "link_rounds_last__L1_L0_L2",
        "link_rounds_last__L1_L0_L3"] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrLoop_L7_L0_body :
    Fn.body (fn% «link_rounds__L7_L0_loop0») = lrLoopBody 7 0 "__loop0_link_rounds__L7_L0" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrMain_L7_L0_body :
    Fn.body (fn% «link_rounds__L7_L0») = lrMainBody "__loop0_link_rounds__L7_L0"
      ["link_rounds_last__L7_L0_L0", "link_rounds_last__L7_L0_L1", "link_rounds_last__L7_L0_L2",
        "link_rounds_last__L7_L0_L3"] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrLoop_L6_L0_body :
    Fn.body (fn% «link_rounds__L6_L0_loop0») = lrLoopBody 6 0 "__loop0_link_rounds__L6_L0" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrMain_L6_L0_body :
    Fn.body (fn% «link_rounds__L6_L0») = lrMainBody "__loop0_link_rounds__L6_L0"
      ["link_rounds_last__L6_L0_L0", "link_rounds_last__L6_L0_L1", "link_rounds_last__L6_L0_L2",
        "link_rounds_last__L6_L0_L3"] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrLoop_L8_L1_body :
    Fn.body (fn% «link_rounds__L8_L1_loop0») = lrLoopBody 8 1 "__loop0_link_rounds__L8_L1" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrMain_L8_L1_body :
    Fn.body (fn% «link_rounds__L8_L1») = lrMainBody "__loop0_link_rounds__L8_L1"
      ["link_rounds_last__L8_L1_L0", "link_rounds_last__L8_L1_L1", "link_rounds_last__L8_L1_L2",
        "link_rounds_last__L8_L1_L3"] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrLoop_L9_L1_body :
    Fn.body (fn% «link_rounds__L9_L1_loop0») = lrLoopBody 9 1 "__loop0_link_rounds__L9_L1" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrMain_L9_L1_body :
    Fn.body (fn% «link_rounds__L9_L1») = lrMainBody "__loop0_link_rounds__L9_L1"
      ["link_rounds_last__L9_L1_L0", "link_rounds_last__L9_L1_L1", "link_rounds_last__L9_L1_L2",
        "link_rounds_last__L9_L1_L3"] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrLoop_L10_L1_body :
    Fn.body (fn% «link_rounds__L10_L1_loop0») = lrLoopBody 10 1 "__loop0_link_rounds__L10_L1" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrMain_L10_L1_body :
    Fn.body (fn% «link_rounds__L10_L1») = lrMainBody "__loop0_link_rounds__L10_L1"
      ["link_rounds_last__L10_L1_L0", "link_rounds_last__L10_L1_L1", "link_rounds_last__L10_L1_L2",
        "link_rounds_last__L10_L1_L3"] :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Link
