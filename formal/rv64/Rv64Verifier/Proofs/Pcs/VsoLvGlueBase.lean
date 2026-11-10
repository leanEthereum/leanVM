import Rv64Verifier.Proofs.Pcs.VsoGlueSpec

/-!
# `verify_stacked_opening`'s glue: the mirror claim by claim, and the claims' words

`gacc` is `glueRust` after the first `i` pending claims. A weight or a glued claim reads only a
few doublewords and the buffers they point to (`InBufs`): `weightAt_congr` and `gluedAt_congr`
carry them from one state and address to another.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-! ## The mirror -/

/-- The first `i` pending claims glued, and the scalar after them. -/
def gacc (lam : E) (Wl : Model.Pcs.WhirLocals) (pend : List (List E × Model.Pcs.GluedWeightRust))
    (i : ℕ) : Model.Pcs.WhirLocals × E :=
  (pend.take i).foldl (Model.Pcs.glueStepRust lam) (Wl, 1)

theorem gacc_zero (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) : gacc lam Wl pend 0 = (Wl, 1) := by
  simp [gacc]

theorem gacc_succ {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} (h : i < pend.length) :
    gacc lam Wl pend (i + 1) = Model.Pcs.glueStepRust lam (gacc lam Wl pend i) pend[i] := by
  simp only [gacc, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem glue_eq (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) :
    Model.Pcs.glueRust lam Wl pend = (gacc lam Wl pend pend.length).1 := by
  simp only [Model.Pcs.glueRust, gacc, List.take_length]

theorem zipAddScaled_length (q c : List E) (sc : E) :
    (Model.Pcs.zipAddScaled q c sc).length = q.length := by
  simp only [Model.Pcs.zipAddScaled, List.length_append, List.length_map, List.length_zip,
    List.length_drop]
  omega

theorem foldl_glue (lam : E) : ∀ (l : List (List E × Model.Pcs.GluedWeightRust))
    (acc : Model.Pcs.WhirLocals × E),
    (l.foldl (Model.Pcs.glueStepRust lam) acc).1.folds = acc.1.folds ∧
    (l.foldl (Model.Pcs.glueStepRust lam) acc).1.glued.length = acc.1.glued.length + l.length ∧
    (l.foldl (Model.Pcs.glueStepRust lam) acc).1.runningQuad.length = acc.1.runningQuad.length
  | [], _ => ⟨rfl, rfl, rfl⟩
  | p :: l, acc => by
    obtain ⟨h1, h2, h3⟩ := foldl_glue lam l (Model.Pcs.glueStepRust lam acc p)
    refine ⟨h1, ?_, ?_⟩
    · rw [List.foldl_cons, h2]
      simp only [Model.Pcs.glueStepRust, List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [List.foldl_cons, h3]
      exact zipAddScaled_length _ _ _

theorem gacc_folds (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (i : ℕ) :
    (gacc lam Wl pend i).1.folds = Wl.folds :=
  (foldl_glue lam _ _).1

theorem gacc_glued_length (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) {i : ℕ} (h : i ≤ pend.length) :
    (gacc lam Wl pend i).1.glued.length = Wl.glued.length + i := by
  rw [gacc, (foldl_glue lam _ _).2.1, List.length_take]
  simp only
  omega

theorem gacc_quad_length (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (i : ℕ) :
    (gacc lam Wl pend i).1.runningQuad.length = Wl.runningQuad.length :=
  (foldl_glue lam _ _).2.2

/-- The quadratic with its first `j` coefficients given `sc` times the intro's. -/
def zipPart (q c : List E) (sc : E) (j : ℕ) : List E :=
  (List.range q.length).map fun k ↦ if k < j then q.getD k 0 + sc * c.getD k 0 else q.getD k 0

theorem zipPart_zero (q c : List E) (sc : E) : zipPart q c sc 0 = q := by
  apply List.ext_getElem (by simp [zipPart])
  intro k h1 h2
  simp [zipPart, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem zipAddScaled_eq (q c : List E) (sc : E) :
    Model.Pcs.zipAddScaled q c sc = zipPart q c sc (min q.length c.length) := by
  apply List.ext_getElem (by rw [zipAddScaled_length]; simp [zipPart])
  intro k h1 h2
  have hk : k < q.length := by rw [zipAddScaled_length] at h1; exact h1
  simp only [zipPart, List.getElem_map, List.getElem_range]
  simp only [Model.Pcs.zipAddScaled]
  rw [List.getElem_append]
  split
  · rename_i hlt
    simp only [List.length_map, List.length_zip] at hlt
    simp only [List.getElem_map, List.getElem_zip, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (show k < c.length by omega),
      Option.getD_some, show k < min q.length c.length from hlt, ite_true]
  · rename_i hge
    simp only [List.length_map, List.length_zip, not_lt] at hge
    simp only [List.getElem_drop, List.length_map, List.length_zip,
      show ¬ k < min q.length c.length by omega, ite_false, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, Option.getD_some]
    congr 1
    omega

theorem zipPart_succ_getD {q c : List E} {sc : E} {j k : ℕ} (hk : k < q.length) :
    (zipPart q c sc (j + 1)).getD k 0 =
      if k = j then q.getD k 0 + sc * c.getD k 0 else (zipPart q c sc j).getD k 0 := by
  simp only [zipPart, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]
  by_cases h : k = j
  · subst h; simp
  · simp only [h, ite_false]
    by_cases h' : k < j
    · simp [h', show k < j + 1 by omega]
    · simp [h', show ¬ k < j + 1 by omega]

/-! ## Bounds from what a range holds -/

/-- The bytes of a range all below `heapEnd`: the range ends there. -/
theorem within_bound {p : Word} {n : ℕ} (h : ∀ y : Word, Within y p n → y.toNat < heapEnd) :
    n = 0 ∨ p.toNat + n ≤ heapEnd := by
  by_cases hn : n = 0
  · exact Or.inl hn
  refine Or.inr ?_
  by_cases hc : p.toNat + n - 1 < 2 ^ 64
  · have := h (BitVec.ofNat 64 (p.toNat + n - 1)) (by
      simp only [Within, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]; omega)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc] at this
    omega
  · have := h (BitVec.ofNat 64 (2 ^ 64 - 1)) (by
      simp only [Within, BitVec.toNat_ofNat]; have := p.isLt; omega)
    simp only [BitVec.toNat_ofNat, heapEnd] at this
    omega

/-! ## A weight's and a glued claim's words -/

/-- The first `n` doublewords at `a` in `v` are those at `b` in `u`. -/
def WordsEq (v : MachineState) (a : Word) (u : MachineState) (b : Word) (n : ℕ) : Prop :=
  ∀ k < n, v.getMem (a + BitVec.ofNat 64 (8 * k)) = u.getMem (b + BitVec.ofNat 64 (8 * k))

theorem add_add_ofNat (a : Word) (x y : ℕ) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem WordsEq.get {v u : MachineState} {a b : Word} {n : ℕ} (h : WordsEq v a u b n) (k : ℕ)
    (hk : k < n) (c : Word) (hc : c = BitVec.ofNat 64 (8 * k)) : v.getMem (a + c) = u.getMem (b + c) := by
  rw [hc]; exact h k hk

theorem WordsEq.zero {v u : MachineState} {a b : Word} {n : ℕ} (h : WordsEq v a u b n) (hn : 0 < n) :
    v.getMem a = u.getMem b := by
  have := h 0 hn
  simpa using this

/-- What a weight at `b` reads through: its doublewords at `a` in `v` as at `b` in `u`. -/
structure WPtrs (v : MachineState) (a : Word) (u : MachineState) (b : Word) : Prop where
  w0 : v.getMem a = u.getMem b
  p0 : vecPtr v a = vecPtr u b
  l0 : vecLen v a = vecLen u b
  p8 : vecPtr v (a + 8) = vecPtr u (b + 8)
  l8 : vecLen v (a + 8) = vecLen u (b + 8)
  p24 : vecPtr v (a + 24) = vecPtr u (b + 24)
  l24 : vecLen v (a + 24) = vecLen u (b + 24)
  w48 : v.getMem (a + 48) = u.getMem (b + 48)

theorem WordsEq.ptrs {v u : MachineState} {a b : Word} {n : ℕ} (h : WordsEq v a u b n)
    (hn : 7 ≤ n) : WPtrs v a u b := by
  have g (k : ℕ) (hk : k < 7) (c : Word) (hc : c = BitVec.ofNat 64 (8 * k)) :
      v.getMem (a + c) = u.getMem (b + c) := h.get k (by omega) c hc
  refine ⟨h.zero (by omega), g 1 (by decide) 8 (by decide), g 2 (by decide) 16 (by decide),
    ?_, ?_, ?_, ?_, g 6 (by decide) 48 (by decide)⟩
  · simp only [vecPtr, BitVec.add_assoc]; exact g 2 (by decide) _ (by decide)
  · simp only [vecLen, BitVec.add_assoc]; exact g 3 (by decide) _ (by decide)
  · simp only [vecPtr, BitVec.add_assoc]; exact g 4 (by decide) _ (by decide)
  · simp only [vecLen, BitVec.add_assoc]; exact g 5 (by decide) _ (by decide)

/-- The buffers a weight at `b` points to are the same in `v` and `u`. -/
structure WBufs (v u : MachineState) (b : Word) : Prop where
  ood : u.getMem b = 0xffffffffffffffff → eListAt v (vecPtr u (b + 8)) (vecLen u (b + 8)).toNat =
    eListAt u (vecPtr u (b + 8)) (vecLen u (b + 8)).toNat
  qw : u.getMem b ≠ 0xffffffffffffffff →
    v.readWords (vecPtr u b) (vecLen u b).toNat = u.readWords (vecPtr u b) (vecLen u b).toNat
  qe : u.getMem b ≠ 0xffffffffffffffff →
    eListAt v (vecPtr u (b + 24)) (vecLen u (b + 24)).toNat =
      eListAt u (vecPtr u (b + 24)) (vecLen u (b + 24)).toNat

theorem weightAt_congr {v u : MachineState} {a b : Word} (hp : WPtrs v a u b) (hb : WBufs v u b) :
    weightAt v a = weightAt u b := by
  unfold weightAt
  rw [hp.w0]
  split
  · rename_i h
    simp only [vecEs, hp.p8, hp.l8]
    rw [hb.ood h]
  · rename_i h
    simp only [vecWords, vecEs, hp.p0, hp.l0, hp.p24, hp.l24, hp.w48]
    rw [hb.qw h, hb.qe h]

theorem InBufs_congr {v u : MachineState} {a b : Word} (hp : WPtrs v a u b) (y : Word) :
    InBufs v a y ↔ InBufs u b y := by
  unfold InBufs
  rw [hp.w0, hp.p0, hp.l0, hp.p8, hp.l8, hp.p24, hp.l24]

theorem WeightAligned_congr {v u : MachineState} {a b : Word} (hp : WPtrs v a u b) :
    WeightAligned v a ↔ WeightAligned u b := by
  unfold WeightAligned
  rw [hp.w0, hp.p0, hp.p8, hp.p24]

/-- A frame that misses the buffers of a weight, all below `heapEnd`, keeps them. -/
theorem WBufs.of_frame {u v : MachineState} {X : Word → Prop} {b : Word} (hX : DFrame u v X)
    (hm : ∀ y, InBufs u b y → ¬ X y ∧ y.toNat < heapEnd) : WBufs v u b := by
  have bnd {p : Word} {n : ℕ} (hw : ∀ y, Within y p n → InBufs u b y) : n = 0 ∨ p.toNat + n ≤ heapEnd :=
    within_bound fun y hy ↦ (hm y (hw y hy)).2
  have eL {p : Word} {n : ℕ} (hw : ∀ y, Within y p (24 * n) → InBufs u b y) :
      eListAt v p n = eListAt u p n := by
    refine hX.eListAt fun i hi hx ↦ (hm _ (hw _ ?_)).1 hx
    rcases bnd hw with h0 | h0
    · omega
    · simp only [heapEnd] at h0; addr_omega [h0, hi]
  refine ⟨fun h ↦ eL fun y hy ↦ by unfold InBufs; simp only [h, ↓reduceIte]; exact hy,
    fun h ↦ ?_, fun h ↦ eL fun y hy ↦ by unfold InBufs; simp only [h, ↓reduceIte]; exact Or.inr hy⟩
  have hw : ∀ y, Within y (vecPtr u b) (8 * (vecLen u b).toNat) → InBufs u b y := fun y hy ↦ by
    unfold InBufs; simp only [h, ↓reduceIte]; exact Or.inl hy
  refine DFrame.readWords' hX (fun y hx hy ↦ (hm y (hw y hy)).1 hx) ?_
  rcases bnd hw with h0 | h0
  · omega
  · simp only [heapEnd] at h0; omega

end Rv64Verifier.Proofs.Pcs.Vso
