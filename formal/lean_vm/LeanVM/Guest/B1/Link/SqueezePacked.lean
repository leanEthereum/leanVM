/-
  LeanVM.Guest.B1.Link.SqueezePacked

  B1 for `squeeze_packed`, its loop and its last arms: the link's packed challenges.
-/

module

public import LeanVM.Guest.B1.Link.Squeeze
public import LeanVM.Guest.B1.Link.RoundsLoop
import LeanVM.Guest.CoreRef

/-!
# `squeeze_packed`

`squeeze_packed(fs0..fs4, out, count_g)` (G) permutes the carried capacity alone
`count = log count_g` times, each output's eight rate cells written to `out`, in order: four a loop
frame (`count = 4 h + r`, `split_count`), records of the capacity at `recs·g^(5 j)`, then
`squeeze_packed_last` for the `r` left. Its meaning (`MeaningSP`): `count_g = g^p`, the cells at
`out` are `pkSqueeze p`'s and it returns the capacity after them; with `runsTo_samplePacked` that is
the Statement's packed draw.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The templates -/

/-- `squeeze_packed_last__L{k}(rec, end, cells)`. -/
def spLastBody (k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 3) (.n 0) 0), .atom (.load (.n 3) (.n 1) 0), .atom (.load (.n 4) (.n 0) 1),
      .atom (.load (.n 4) (.n 1) 1), .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 5) (.n 1) 2),
      .atom (.load (.n 6) (.n 0) 3), .atom (.load (.n 6) (.n 1) 3), .atom (.load (.n 7) (.n 0) 4),
      .atom (.load (.n 7) (.n 1) 4), .atom (.const (.n 8) (word 0 0)), .ret [.n 8]]
  else
    [.atom (.load (.n 3) (.n 0) 0), .atom (.load (.n 4) (.n 0) 1), .atom (.load (.n 5) (.n 0) 2),
      .atom (.load (.n 6) (.n 0) 3), .atom (.load (.n 7) (.n 0) 4), .atom (.const (.n 8) (word 1 0)),
      .atom (.const (.n 9) (word 0 0)), .atom (.const (.n 10) (word 0 0)),
      .atom (.const (.n 11) (word 0 0)), .atom (.const (.n 12) (word 0 0))] ++
    spPermsT 13 [3, 4, 5, 6, 7] 9 2 0 k ++
    ((List.range 5).map fun j ↦ .atom (.load (.n (13 + 13 * (k - 1) + 8 + j)) (.n 1) j)) ++
    [.atom (.const (.n (13 + 13 * k)) (word 0 0)), .ret [.n (13 + 13 * k)]]

/-- The loop helper's atoms (parameters `x, N, recs, out`). -/
def spLoopA : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)), .atom (.mul (.n 6) (.n 5) (.n 0)),
    .atom (.mul (.n 7) (.n 2) (.n 6)), .atom (.mul (.n 8) (.n 0) (.n 0)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 3) (.n 12)),
    .atom (.load (.n 14) (.n 7) 0), .atom (.load (.n 15) (.n 7) 1), .atom (.load (.n 16) (.n 7) 2),
    .atom (.load (.n 17) (.n 7) 3), .atom (.load (.n 18) (.n 7) 4), .atom (.const (.n 19) (word 1 0)),
    .atom (.const (.n 20) (word 0 0)), .atom (.const (.n 21) (word 0 0)), .atom (.const (.n 22) (word 0 0)),
    .atom (.const (.n 23) (word 0 0))] ++
  spPermsT 24 [14, 15, 16, 17, 18] 20 13 0 4 ++
  ((List.range 5).map fun j ↦ .atom (.load (.n (71 + j)) (.n 7) (5 + j))) ++
  [.atom (.const (.n 76) (word 2 0)), .atom (.mul (.n 77) (.n 0) (.n 76)), .atom (.add (.n 78) (.n 77) (.n 1)),
    .atom (.const (.n 79) (word 2 0)), .atom (.mul (.n 80) (.n 0) (.n 79))]

/-- The loop helper's body. -/
def spLoopBody (name : String) : List Stmt :=
  spLoopA ++ [.callIf (.n 78) name [.n 80, .n 1, .n 2, .n 3], .ret []]

/-- `squeeze_packed`'s body. -/
def spMainBody (loop : String) (lasts : List String) : List Stmt :=
  [.atom (.hint (.bitsExp (.n 6) 6 (.stack [.n 7, .n 8, .n 9, .n 10, .n 11, .n 12]))),
    .atom (.mul (.n 7) (.n 7) (.n 7)), .atom (.const (.n 13) (word 1 0)), .atom (.const (.n 14) (word 3 0)),
    .atom (.mul (.n 15) (.n 7) (.n 14)), .atom (.add (.n 16) (.n 13) (.n 15)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.const (.n 17) (word 1 0)), .atom (.const (.n 18) (word 5 0)),
    .atom (.mul (.n 19) (.n 8) (.n 18)), .atom (.add (.n 20) (.n 17) (.n 19)),
    .atom (.mul (.n 21) (.n 16) (.n 20)),
    .atom (.mul (.n 9) (.n 9) (.n 9)), .atom (.const (.n 22) (word 1 0)), .atom (.const (.n 23) (word 3 0)),
    .atom (.mul (.n 24) (.n 9) (.n 23)), .atom (.add (.n 25) (.n 22) (.n 24)),
    .atom (.mul (.n 10) (.n 10) (.n 10)), .atom (.const (.n 26) (word 1 0)), .atom (.const (.n 27) (word 5 0)),
    .atom (.mul (.n 28) (.n 10) (.n 27)), .atom (.add (.n 29) (.n 26) (.n 28)),
    .atom (.mul (.n 30) (.n 25) (.n 29)),
    .atom (.mul (.n 11) (.n 11) (.n 11)), .atom (.const (.n 31) (word 1 0)), .atom (.const (.n 32) (word 17 0)),
    .atom (.mul (.n 33) (.n 11) (.n 32)), .atom (.add (.n 34) (.n 31) (.n 33)),
    .atom (.mul (.n 35) (.n 30) (.n 34)),
    .atom (.mul (.n 12) (.n 12) (.n 12)), .atom (.const (.n 36) (word 1 0)), .atom (.const (.n 37) (word 257 0)),
    .atom (.mul (.n 38) (.n 12) (.n 37)), .atom (.add (.n 39) (.n 36) (.n 38)),
    .atom (.mul (.n 40) (.n 35) (.n 39)),
    .atom (.mul (.n 41) (.n 40) (.n 40)), .atom (.mul (.n 42) (.n 41) (.n 41)),
    .atom (.mul (.n 43) (.n 42) (.n 21)), .atom (.assertEq (.n 43) (.n 6)),
    .atom (.const (.n 44) (word 4 0)), .atom (.mul (.n 45) (.n 40) (.n 44)),
    .atom (.mul (.n 46) (.n 45) (.n 45)), .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 47) (.n 45)), .atom (.hint (.allocDyn (.n 49) (.n 48))),
    .atom (.load (.n 0) (.n 49) 0), .atom (.load (.n 1) (.n 49) 1), .atom (.load (.n 2) (.n 49) 2),
    .atom (.load (.n 3) (.n 49) 3), .atom (.load (.n 4) (.n 49) 4),
    .atom (.const (.n 50) (word 1 0)), .atom (.add (.n 51) (.n 50) (.n 40)), .atom (.const (.n 52) (word 1 0)),
    .callIf (.n 51) loop [.n 52, .n 40, .n 49, .n 5],
    .atom (.mul (.n 53) (.n 40) (.n 40)), .atom (.mul (.n 54) (.n 53) (.n 53)),
    .atom (.mul (.n 55) (.n 54) (.n 40)), .atom (.mul (.n 56) (.n 49) (.n 55)),
    .atom (.const (.n 57) (word 32 0)), .atom (.mul (.n 58) (.n 56) (.n 57)),
    .atom (.mul (.n 59) (.n 40) (.n 40)), .atom (.mul (.n 60) (.n 59) (.n 59)),
    .atom (.mul (.n 61) (.n 60) (.n 60)), .atom (.mul (.n 62) (.n 61) (.n 61)),
    .atom (.mul (.n 63) (.n 62) (.n 62)), .atom (.mul (.n 64) (.n 5) (.n 63)),
    .dispatch (.n 21) lasts [.n 56, .n 58, .n 64] [.n 65],
    .atom (.load (.n 66) (.n 56) 5), .atom (.load (.n 67) (.n 56) 6), .atom (.load (.n 68) (.n 56) 7),
    .atom (.load (.n 69) (.n 56) 8), .atom (.load (.n 70) (.n 56) 9),
    .ret [.n 66, .n 67, .n 68, .n 69, .n 70]]

/-! ## The meanings -/

theorem pkSqueeze_add : ∀ (a b : ℕ) (cap : List E), pkSqueeze (a + b) cap =
    ((pkSqueeze a cap).1 ++ (pkSqueeze b (pkSqueeze a cap).2).1, (pkSqueeze b (pkSqueeze a cap).2).2)
  | 0, b, cap => by simp [pkSqueeze]
  | a + 1, b, cap => by
    rw [show a + 1 + b = (a + b) + 1 by ring, pkSqueeze, pkSqueeze, pkSqueeze_add a b]
    simp

theorem pkSqueeze_cap_length : ∀ (p : ℕ) (cap : List E), cap.length = 5 → (pkSqueeze p cap).2.length = 5
  | 0, _, h => h
  | p + 1, cap, _ => pkSqueeze_cap_length p _ (by simp [capOf])

/-- **`squeeze_packed_last__L{k}(rec, end, cells)`**: it returns `0`; the capacity at `rec`, the
cells of `k` permutations of it alone at `cells`, the capacity after them at `end`. -/
def MeaningSPL (k : ℕ) (rd : Reader) : List E → List E → Prop
  | [rec, en, cells], rets => rets = [0] ∧ ∃ cap : List E, cap.length = 5 ∧ ReadsAt rd rec cap ∧
      ReadsAt rd cells (pkSqueeze k cap).1 ∧ ReadsAt rd en (pkSqueeze k cap).2
  | _, _ => False

theorem readsAt_five {rd : Reader} {p : E} {σ : Val} {a b c d e : ℕ}
    (h0 : LoadHolds rd p 0 (σ (.n a))) (h1 : LoadHolds rd p 1 (σ (.n b))) (h2 : LoadHolds rd p 2 (σ (.n c)))
    (h3 : LoadHolds rd p 3 (σ (.n d))) (h4 : LoadHolds rd p 4 (σ (.n e))) :
    ReadsAt rd p ([a, b, c, d, e].map (σ ∘ .n)) := fun i hi ↦ by
  simp only [List.length_map, List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3 | 4, _ => exact h4

theorem readsAt_of_getD {rd : Reader} {p : E} {xs : List E} {off : ℕ}
    (h : ∀ i < xs.length, LoadHolds rd p (off + i) (xs.getD i 0)) :
    ReadsAt rd (p * gen ^ off) xs := fun i hi ↦ by
  rw [loadHolds_mul_gen_pow]
  have := h i hi
  simpa [List.getD_eq_getElem?_getD, hi] using this

theorem spl_sound {k : ℕ} {rd : Reader} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = spLastBody k) (args rets : List E) :
    coreProgram.Rel rd name args rets → MeaningSPL k rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  by_cases hk : k = 0
  · subst hk
    simp only [spLastBody, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
      List.map_nil, word_zero]
    rintro ⟨σ, rfl, l0, s0, l1, s1, l2, s2, l3, s3, l4, s4, h8, hret⟩
    refine ⟨by rw [← hret, h8], _, rfl, readsAt_five l0 l1 l2 l3 l4, by simp [pkSqueeze, ReadsAt],
      by simpa [pkSqueeze] using readsAt_five s0 s1 s2 s3 s4⟩
  · simp only [spLastBody, hk, ↓reduceIte]
    rintro ⟨σ, rfl, h⟩
    simp only [holdsList_append] at h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, word_zero] at h
    obtain ⟨l0, l1, l2, l3, l4, -, z0, z1, z2, z3, h⟩ := h
    obtain ⟨hP, h⟩ := (holdsList_atoms (spPermsT_atoms _ _ _ _ _ _) _ _).mp h
    have hatS : AllAtoms ((List.range 5).map fun j ↦ Stmt.atom (.load (.n (13 + 13 * (k - 1) + 8 + j)) (.n 1) j)) :=
      fun s hs ↦ by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩
    obtain ⟨hS, h0, hret⟩ := (holdsList_atoms hatS _ _).mp h
    simp only [List.map_cons, List.map_nil] at hret
    obtain ⟨hc, hk'⟩ := spPerms_sound (fun i hi ↦ by
      match i, hi with | 0, _ => exact z0 | 1, _ => exact z1 | 2, _ => exact z2 | 3, _ => exact z3) hP
    refine ⟨by rw [← hret, h0], _, rfl, readsAt_five l0 l1 l2 l3 l4, ?_, ?_⟩
    · have := readsAt_of_getD (off := 0) (fun i hi ↦ by
        rw [pkSqueeze_length] at hi; simpa using hc i hi)
      simpa using this
    · rw [← hk']
      intro j hj
      simp only [spCap, hk, ↓reduceIte, List.length_map, List.length_range] at hj ⊢
      have := hS _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      simpa [Atom.Holds, hj] using this

/-- What one loop iteration establishes at `x`: four permutations from the capacity at `recs·x^5`,
their cells at `out·x^32`, the capacity after at `recs·x^5·g^5`. -/
def SPIter (rd : Reader) (x recs out : E) : Prop :=
  ∃ cap : List E, cap.length = 5 ∧ ReadsAt rd (recs * x ^ 5) cap ∧
    ReadsAt rd (out * x ^ 32) (pkSqueeze 4 cap).1 ∧ ReadsAt rd (recs * x ^ 5 * gen ^ 5) (pkSqueeze 4 cap).2

theorem spLoopA_atoms : AllAtoms spLoopA := by
  unfold spLoopA
  refine allAtoms_append (allAtoms_append (allAtoms_append ?_ (spPermsT_atoms _ _ _ _ _ _))
    (fun s hs ↦ ?_)) ?_
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem sp_iter {rd : Reader} {σ : Val} (hA : ∀ a, Stmt.atom a ∈ spLoopA → a.Holds rd σ) :
    SPIter rd (σ (.n 0)) (σ (.n 2)) (σ (.n 3)) := by
  have mem := fun a (ha : a ∈ [Atom.mul (.n 4) (.n 0) (.n 0), .mul (.n 5) (.n 4) (.n 4), .mul (.n 6) (.n 5) (.n 0),
      .mul (.n 7) (.n 2) (.n 6), .mul (.n 8) (.n 0) (.n 0), .mul (.n 9) (.n 8) (.n 8),
      .mul (.n 10) (.n 9) (.n 9), .mul (.n 11) (.n 10) (.n 10), .mul (.n 12) (.n 11) (.n 11),
      .mul (.n 13) (.n 3) (.n 12), .load (.n 14) (.n 7) 0, .load (.n 15) (.n 7) 1, .load (.n 16) (.n 7) 2,
      .load (.n 17) (.n 7) 3, .load (.n 18) (.n 7) 4, .const (.n 20) (word 0 0), .const (.n 21) (word 0 0),
      .const (.n 22) (word 0 0), .const (.n 23) (word 0 0)]) ↦ hA a (by
    unfold spLoopA
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp)
  have m4 := mem (.mul (.n 4) (.n 0) (.n 0)) (by simp)
  have m5 := mem (.mul (.n 5) (.n 4) (.n 4)) (by simp)
  have m6 := mem (.mul (.n 6) (.n 5) (.n 0)) (by simp)
  have m7 := mem (.mul (.n 7) (.n 2) (.n 6)) (by simp)
  have m8 := mem (.mul (.n 8) (.n 0) (.n 0)) (by simp)
  have m9 := mem (.mul (.n 9) (.n 8) (.n 8)) (by simp)
  have m10 := mem (.mul (.n 10) (.n 9) (.n 9)) (by simp)
  have m11 := mem (.mul (.n 11) (.n 10) (.n 10)) (by simp)
  have m12 := mem (.mul (.n 12) (.n 11) (.n 11)) (by simp)
  have m13 := mem (.mul (.n 13) (.n 3) (.n 12)) (by simp)
  have l0 := mem (.load (.n 14) (.n 7) 0) (by simp)
  have l1 := mem (.load (.n 15) (.n 7) 1) (by simp)
  have l2 := mem (.load (.n 16) (.n 7) 2) (by simp)
  have l3 := mem (.load (.n 17) (.n 7) 3) (by simp)
  have l4 := mem (.load (.n 18) (.n 7) 4) (by simp)
  have z0 := mem (.const (.n 20) (word 0 0)) (by simp)
  have z1 := mem (.const (.n 21) (word 0 0)) (by simp)
  have z2 := mem (.const (.n 22) (word 0 0)) (by simp)
  have z3 := mem (.const (.n 23) (word 0 0)) (by simp)
  simp only [Atom.Holds, word_zero] at m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 l0 l1 l2 l3 l4 z0 z1 z2 z3
  have h7 : σ (.n 7) = σ (.n 2) * σ (.n 0) ^ 5 := by rw [m7, m6, m5, m4]; ring
  have h13 : σ (.n 13) = σ (.n 3) * σ (.n 0) ^ 32 := by rw [m13, m12, m11, m10, m9, m8]; ring
  have hP : ∀ a, Stmt.atom a ∈ spPermsT 24 [14, 15, 16, 17, 18] 20 13 0 4 → a.Holds rd σ := fun a ha ↦
    hA a (by unfold spLoopA; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))
  obtain ⟨hc, hk⟩ := spPerms_sound (fun i hi ↦ by
    match i, hi with | 0, _ => exact z0 | 1, _ => exact z1 | 2, _ => exact z2 | 3, _ => exact z3) hP
  refine ⟨[14, 15, 16, 17, 18].map (σ ∘ .n), rfl, ?_, ?_, ?_⟩
  · rw [← h7]; exact readsAt_five l0 l1 l2 l3 l4
  · rw [← h13]
    have := readsAt_of_getD (off := 0) (fun i hi ↦ by rw [pkSqueeze_length] at hi; simpa using hc i hi)
    simpa using this
  · rw [← hk, ← h7]
    intro j hj
    simp only [spCap, Nat.reduceEqDiff, ↓reduceIte, List.length_map, List.length_range] at hj ⊢
    rw [loadHolds_mul_gen_pow]
    have := hA (.load (.n (71 + j)) (.n 7) (5 + j)) (by
      unfold spLoopA
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    simpa [Atom.Holds, hj, show 24 + 13 * (4 - 1) + 8 + j = 71 + j by omega] using this

/-- **The loop helper's relation**, from `g^0` to `N = g^q`, `1 ≤ q < ord g`. -/
theorem spLoop_rel {rd : Reader} {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3])
    (hbody : fn.body = spLoopBody name) {q : ℕ} (hq1 : 1 ≤ q) (hq : q < ordG) (recs out : E)
    (h : coreProgram.Rel rd name [gen ^ 0, gen ^ q, recs, out] []) :
    ∀ j < q, SPIter rd (gen ^ j) recs out := by
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) name (x :: [gen ^ q, recs, out]) [] ↔
      AtomsBody rd fn.params spLoopA (x :: gen ^ q :: [recs, out]) ∧ IsInK (x * gen + gen ^ q) ∧
        (x * gen + gen ^ q ≠ 0 → coreProgram.relN rd d name (x * gen :: [gen ^ q, recs, out]) []) := by
    intro d x
    refine loop_step_atoms hf (by rw [hbody, spLoopBody]) spLoopA_atoms (fun σ hp hall ↦ ?_) d
    rw [hparams] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨h0, h1, h2, h3, -⟩ := hp
    have mem : ∀ a ∈ [Atom.const (.n 76) (word 2 0), .mul (.n 77) (.n 0) (.n 76),
        .add (.n 78) (.n 77) (.n 1), .const (.n 79) (word 2 0), .mul (.n 80) (.n 0) (.n 79)],
        a.Holds rd σ := fun a ha ↦ hall a (by unfold spLoopA; exact List.mem_append_right _ (by simpa using ha))
    have a0 := mem (.const (.n 76) (word 2 0)) (by simp)
    have a1 := mem (.mul (.n 77) (.n 0) (.n 76)) (by simp)
    have a2 := mem (.add (.n 78) (.n 77) (.n 1)) (by simp)
    have a3 := mem (.const (.n 79) (word 2 0)) (by simp)
    have a4 := mem (.mul (.n 80) (.n 0) (.n 79)) (by simp)
    simp only [Atom.Holds, word_gen] at a0 a1 a2 a3 a4
    refine ⟨by rw [a2, a1, a0, h0, h1], ?_⟩
    simp only [List.map_cons, List.map_nil, a4, a3, h0, h1, h2, h3]
  obtain ⟨m, hm0, hN, hfirst, hall⟩ := (loop_iff (P := coreProgram) (f := name) (B := fun x ↦
    AtomsBody rd fn.params spLoopA (x :: gen ^ q :: [recs, out])) hstep 0).mp h
  have hmq : m = q := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd (gen_pow_inj (by unfold ordG at hq; omega) (by unfold ordG at hq; omega) hN) (by omega)
    · exact hfirst q (by omega) hgt rfl
  intro j hj
  obtain ⟨σ, hp, hall'⟩ := hall j (by omega) (by omega)
  rw [hparams] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, -, h2, h3, -⟩ := hp
  have := sp_iter hall'
  rwa [h0, h2, h3] at this

/-! ## The bodies -/

set_option maxRecDepth 100000 in
theorem spl0_body : Fn.body (fn% «squeeze_packed_last__L0») = spLastBody 0 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem spl1_body : Fn.body (fn% «squeeze_packed_last__L1») = spLastBody 1 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem spl2_body : Fn.body (fn% «squeeze_packed_last__L2») = spLastBody 2 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem spl3_body : Fn.body (fn% «squeeze_packed_last__L3») = spLastBody 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem spLoop_body : Fn.body (fn% «squeeze_packed_loop0») = spLoopBody "__loop0_squeeze_packed" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem spMain_body : Fn.body (fn% «squeeze_packed») = spMainBody "__loop0_squeeze_packed"
    ["squeeze_packed_last__L0", "squeeze_packed_last__L1", "squeeze_packed_last__L2",
      "squeeze_packed_last__L3"] :=
  stmtsEqb_sound (by decide +kernel)

/-- **`squeeze_packed(fs0..fs4, out, count_g)`**: `count_g = g^p`, `p < 64`; the cells of `p`
permutations of the capacity alone at `out`, and it returns the capacity after them. -/
def MeaningSP (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, out, cg], rets => ∃ p < 64, cg = gen ^ p ∧
      ReadsAt rd out (pkSqueeze p [f0, f1, f2, f3, f4]).1 ∧ rets = (pkSqueeze p [f0, f1, f2, f3, f4]).2
  | _, _ => False

/-- **`squeeze_packed`'s template implies its meaning**, given its loop's and last arms'. -/
theorem spMain_sound {rd : Reader} {name loopName : String} {lasts : List String} {fn loopFn : Fn}
    (hf : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbody : fn.body = spMainBody loopName lasts) (hlf : coreProgram.find? loopName = some loopFn)
    (hlp : loopFn.params = [.n 0, .n 1, .n 2, .n 3]) (hlb : loopFn.body = spLoopBody loopName)
    (hll : lasts.length = 4) (hlasts : ∀ k (hk : k < lasts.length) args rets,
      coreProgram.Rel rd lasts[k] args rets → MeaningSPL k rd args rets)
    (args rets : List E) :
    coreProgram.Rel rd name args rets → MeaningSP rd args rets := by
  rw [rel_iff_sem hf, hbody, hparams]
  rintro ⟨σ, rfl, h⟩
  simp only [spMainBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and] at h
  obtain ⟨b0, c13, c14, m15, a16, b1, c17, c18, m19, a20, m21, b2, c22, c23, m24, a25, b3, c26, c27, m28, a29,
    m30, b4, c31, c32, m33, a34, m35, b5, c36, c37, m38, a39, m40, m41, m42, m43, hassert, c44, m45, m46,
    m47, m48, s0, s1, s2, s3, s4, c50, a51, c52, hK51, hcall, m53, m54, m55, m56, c57, m58, m59, m60, m61,
    m62, m63, m64, ⟨j, hj, hj21, hlast⟩, r66, r67, r68, r69, r70, hret⟩ := h
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := word_two_pow_xor_one (a := 8) (by norm_num)
  have hrg : σ (.n 21) = gen ^ (bv (σ (.n 7)) + 2 * bv (σ (.n 8))) := by
    rw [m21, a16, a20, m15, m19, c13, c14, c17, c18, w3, w5, word_one, bit_factor b0, bit_factor b1,
      ← pow_add]
    simp only [bv, one_mul]
  have hqg : σ (.n 40) = gen ^ (bv (σ (.n 9)) + 2 * bv (σ (.n 10)) + 4 * bv (σ (.n 11)) + 8 * bv (σ (.n 12))) := by
    rw [m40, m35, m30, a25, a29, a34, a39, m24, m28, m33, m38, c22, c23, c26, c27, c31, c32, c36, c37, w3, w5,
      w17, w257, word_one, bit_factor b2, bit_factor b3, bit_factor b4, bit_factor b5, ← pow_add, ← pow_add,
      ← pow_add]
    simp only [bv, one_mul]
  set rv := bv (σ (.n 7)) + 2 * bv (σ (.n 8)) with hrv
  set qv := bv (σ (.n 9)) + 2 * bv (σ (.n 10)) + 4 * bv (σ (.n 11)) + 8 * bv (σ (.n 12)) with hqv
  have hrv4 : rv < 4 := by have := bv_le (σ (.n 7)); have := bv_le (σ (.n 8)); omega
  have hqv16 : qv < 16 := by
    have := bv_le (σ (.n 9)); have := bv_le (σ (.n 10)); have := bv_le (σ (.n 11))
    have := bv_le (σ (.n 12)); omega
  have hcg : σ (.n 6) = gen ^ (4 * qv + rv) := by
    have : σ (.n 6) = σ (.n 43) := by linear_combination hassert.symm + σ (.n 6) * two_eq_zero_E
    rw [this, m43, m42, m41, hqg, hrg]
    ring
  set cap0 : List E := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]
  have hloop : ∀ m < qv, SPIter rd (gen ^ m) (σ (.n 49)) (σ (.n 5)) := by
    intro m hm
    have hq0 : σ (.n 51) ≠ 0 := by
      rw [a51, c50, word_one, hqg]
      intro h0
      have : gen ^ qv = 1 := by linear_combination h0 - two_eq_zero_E
      rw [gen_pow_eq_one_iff (by omega)] at this
      omega
    have hc := hcall hq0
    rw [c52, word_one, hqg, ← pow_zero gen] at hc
    exact spLoop_rel hlf hlp hlb (by omega) (by unfold ordG; omega) _ _ hc m hm
  have hchain : ∀ m ≤ qv, ReadsAt rd (σ (.n 5)) (pkSqueeze (4 * m) cap0).1 ∧
      ReadsAt rd (σ (.n 49) * gen ^ (5 * m)) (pkSqueeze (4 * m) cap0).2 := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨by simp [pkSqueeze, ReadsAt], ?_⟩
      rw [Nat.mul_zero, pow_zero, mul_one]
      exact readsAt_five (σ := σ) (a := 0) (b := 1) (c := 2) (d := 3) (e := 4) s0 s1 s2 s3 s4
    | succ m ih =>
      obtain ⟨hc, hr⟩ := ih (by omega)
      obtain ⟨cap, hcl, hrc, hcells, hnext⟩ := hloop m (by omega)
      rw [← pow_mul, mul_comm m 5] at hrc hnext
      have e : cap = (pkSqueeze (4 * m) cap0).2 :=
        readsAt_unique hrc hr (by rw [hcl, pkSqueeze_cap_length _ _ rfl])
      subst e
      rw [show 4 * (m + 1) = 4 * m + 4 by ring, pkSqueeze_add]
      refine ⟨readsAt_append_shift hc ?_, ?_⟩
      · rw [pkSqueeze_length, show 8 * (4 * m) = m * 32 by ring, pow_mul]
        exact hcells
      · rw [show 5 * (m + 1) = 5 * m + 5 by ring, pow_add, ← mul_assoc]
        exact hnext
  obtain ⟨hc, hr⟩ := hchain qv le_rfl
  have hjr : j = rv := by
    rw [hrg, ← gen_pow_eq_ofK] at hj21
    exact (gen_pow_inj (by omega) (by omega) hj21).symm
  obtain ⟨-, cap, hcl, hrc, hcells, hend⟩ := hlasts j hj _ _ hlast
  rw [hjr] at hcells hend
  have h56 : σ (.n 56) = σ (.n 49) * gen ^ (5 * qv) := by rw [m56, m55, m54, m53, hqg]; ring
  have h58 : σ (.n 58) = σ (.n 56) * gen ^ 5 := by
    rw [m58, c57, show (32 : ℕ) = 2 ^ 5 from rfl, word_two_pow (by norm_num)]
  have h64 : σ (.n 64) = σ (.n 5) * gen ^ (32 * qv) := by rw [m64, m63, m62, m61, m60, m59, hqg]; ring
  rw [h56] at hrc
  have e : cap = (pkSqueeze (4 * qv) cap0).2 :=
    readsAt_unique hrc hr (by rw [hcl, pkSqueeze_cap_length _ _ rfl])
  subst e
  refine ⟨4 * qv + rv, by omega, hcg, ?_, ?_⟩
  · rw [pkSqueeze_add]
    refine readsAt_append_shift hc ?_
    rw [pkSqueeze_length, show 8 * (4 * qv) = 32 * qv by ring, ← h64]
    exact hcells
  · rw [pkSqueeze_add]
    have hout : ReadsAt rd (σ (.n 58)) [σ (.n 66), σ (.n 67), σ (.n 68), σ (.n 69), σ (.n 70)] := by
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      rw [h58, loadHolds_mul_gen_pow]
      match i, hi with
      | 0, _ => exact r66 | 1, _ => exact r67 | 2, _ => exact r68 | 3, _ => exact r69 | 4, _ => exact r70
    exact (readsAt_unique hend hout (by rw [pkSqueeze_cap_length _ _ (pkSqueeze_cap_length _ _ rfl)]; rfl)).symm ▸ hret.symm

/-- **`squeeze_packed`'s core IR implies its meaning.** -/
theorem squeeze_packed_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "squeeze_packed" args rets → MeaningSP rd args rets :=
  spMain_sound (coreProgram_find?_at (j := idx% «squeeze_packed») rfl) rfl spMain_body
    (coreProgram_find?_at (j := idx% «squeeze_packed_loop0») rfl) rfl spLoop_body rfl
    (fun k hk args rets h ↦ by
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact spl_sound (coreProgram_find?_at (j := idx% «squeeze_packed_last__L0») rfl) rfl spl0_body _ _ h
      · exact spl_sound (coreProgram_find?_at (j := idx% «squeeze_packed_last__L1») rfl) rfl spl1_body _ _ h
      · exact spl_sound (coreProgram_find?_at (j := idx% «squeeze_packed_last__L2») rfl) rfl spl2_body _ _ h
      · exact spl_sound (coreProgram_find?_at (j := idx% «squeeze_packed_last__L3») rfl) rfl spl3_body _ _ h)
    args rets

end
end LeanVM.Guest.B1.Link
