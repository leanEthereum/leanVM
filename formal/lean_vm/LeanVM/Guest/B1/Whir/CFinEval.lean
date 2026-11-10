/-
  LeanVM.Guest.B1.Whir.CFinEval

  Straight-line blocks evaluated: the values a block's statements define, in order, from a memory
  every admissible reader agrees on, and the block holding there.
-/

module

public import LeanVM.Guest.B1.Whir.CBlk
public import LeanVM.Guest.Memory.Straight

/-!
# Straight-line blocks, evaluated

A block whose statements define their values in increasing order, each from earlier ones
(`Ssa w ss w'`: from the watermark `w` to `w'`), has its values computed by `evalV`: a constant,
a sum, a product or a copy its value; a load from the watermark on its word in the memory `M`; a
product whose destination is defined and whose middle operand is fresh a division; an allocation
or a call's single return a given value `Pt`. `ssa_allOk`: every valuation holding those values
holds the block, given its side conditions (`SidesOk`): the loads' words in the reader, the
divisors not zero, the calls in `C`.

`memOf H`: the memory of some reader `H` admits; `memOf_eq`: at a word every such reader holds, it
is that word.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The memory of the admissible readers -/

/-- The word at `p·g^off` of some reader `H` admits (`0` when none). -/
noncomputable def memOf (H : CallRel → Reader → Prop) (p : E) (off : ℕ) : E := by
  classical
  exact if h : ∃ C rd, H C rd then
    ((Classical.choose (Classical.choose_spec h)) (p.limb 0 * addressOfIndex off)).getD 0 else 0

/-- **At a word every admissible reader holds, the memory is that word.** -/
theorem memOf_eq {H : CallRel → Reader → Prop} {p : E} {off : ℕ} {w : E}
    (hw : ∀ C rd, H C rd → LoadHolds rd p off w) {C : CallRel} {rd : Reader} (hH : H C rd) :
    memOf H p off = w := by
  have hex : ∃ C rd, H C rd := ⟨C, rd, hH⟩
  unfold memOf
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have := (hw _ _ (Classical.choose_spec (Classical.choose_spec hex))).2
  rw [this]
  rfl

/-! ## Evaluation -/

/-- The watermark after a statement: one past the value it defines, if it defines one past the
watermark. -/
def stepW (w : ℕ) : Stmt → ℕ
  | .atom (.const d _) => if w ≤ d.idx then d.idx + 1 else w
  | .atom (.add d _ _) => if w ≤ d.idx then d.idx + 1 else w
  | .atom (.mul d a _) => if w ≤ d.idx then d.idx + 1 else if w ≤ a.idx then a.idx + 1 else w
  | .atom (.copy d _) => if w ≤ d.idx then d.idx + 1 else w
  | .atom (.load d _ _) => if w ≤ d.idx then d.idx + 1 else w
  | .atom (.hint (.alloc d _)) => if w ≤ d.idx then d.idx + 1 else w
  | .atom (.hint (.allocDyn d _)) => if w ≤ d.idx then d.idx + 1 else w
  | .call _ _ [r] => if w ≤ r.idx then r.idx + 1 else w
  | _ => w

/-- The values after a statement, from the memory `M` and the given values `Pt`. -/
def stepV (M : E → ℕ → E) (Pt : ℕ → E) (w : ℕ) (v : ℕ → E) : Stmt → ℕ → E
  | .atom (.const d c) => if w ≤ d.idx then Function.update v d.idx c else v
  | .atom (.add d a b) => if w ≤ d.idx then Function.update v d.idx (v a.idx + v b.idx) else v
  | .atom (.mul d a b) => if w ≤ d.idx then Function.update v d.idx (v a.idx * v b.idx)
      else if w ≤ a.idx then Function.update v a.idx (v d.idx / v b.idx) else v
  | .atom (.copy d s) => if w ≤ d.idx then Function.update v d.idx (v s.idx) else v
  | .atom (.load d p off) => if w ≤ d.idx then Function.update v d.idx (M (v p.idx) off) else v
  | .atom (.hint (.alloc d _)) => if w ≤ d.idx then Function.update v d.idx (Pt d.idx) else v
  | .atom (.hint (.allocDyn d _)) => if w ≤ d.idx then Function.update v d.idx (Pt d.idx) else v
  | .call _ _ [r] => if w ≤ r.idx then Function.update v r.idx (Pt r.idx) else v
  | _ => v

/-- **The values a block defines**, from the watermark `w` and the values `v`. -/
def evalV (M : E → ℕ → E) (Pt : ℕ → E) : ℕ → (ℕ → E) → List Stmt → ℕ → E
  | _, v, [] => v
  | w, v, s :: ss => evalV M Pt (stepW w s) (stepV M Pt w v s) ss

/-- A statement of a block in order, from the watermark `w` to `w'`: a definition past the
watermark from values below it, a division (a product at a defined destination, its middle
operand fresh), a store, an allocation, a conditional call or a call with at most one return. -/
inductive SStep : ℕ → Stmt → ℕ → Prop
  | const {w d : ℕ} {c : E} : w ≤ d → SStep w (.atom (.const (.n d) c)) (d + 1)
  | add {w d a b : ℕ} : w ≤ d → a < d → b < d → SStep w (.atom (.add (.n d) (.n a) (.n b))) (d + 1)
  | mul {w d a b : ℕ} : w ≤ d → a < d → b < d → SStep w (.atom (.mul (.n d) (.n a) (.n b))) (d + 1)
  | div {w d q b : ℕ} : d < w → w ≤ q → b < q → SStep w (.atom (.mul (.n d) (.n q) (.n b))) (q + 1)
  | copy {w d s : ℕ} : w ≤ d → s < d → SStep w (.atom (.copy (.n d) (.n s))) (d + 1)
  | load {w d p off : ℕ} : w ≤ d → p < d → SStep w (.atom (.load (.n d) (.n p) off)) (d + 1)
  | store {w d p off : ℕ} : d < w → p < w → SStep w (.atom (.load (.n d) (.n p) off)) w
  | alloc {w d n : ℕ} : w ≤ d → SStep w (.atom (.hint (.alloc (.n d) n))) (d + 1)
  | allocDyn {w d s : ℕ} : w ≤ d → s < d → SStep w (.atom (.hint (.allocDyn (.n d) (.n s)))) (d + 1)
  | callIf {w c : ℕ} {f : String} {args : List ℕ} : c < w → (∀ a ∈ args, a < w) →
      SStep w (.callIf (.n c) f (args.map V.n)) w
  | call0 {w : ℕ} {f : String} {args : List ℕ} : (∀ a ∈ args, a < w) →
      SStep w (.call f (args.map V.n) []) w
  | call1 {w r : ℕ} {f : String} {args : List ℕ} : w ≤ r → (∀ a ∈ args, a < r) →
      SStep w (.call f (args.map V.n) [.n r]) (r + 1)

/-- **A block in order**, from the watermark `w` to `w'`. -/
inductive Ssa : ℕ → List Stmt → ℕ → Prop
  | nil {w : ℕ} : Ssa w [] w
  | cons {w w1 w2 : ℕ} {s : Stmt} {ss : List Stmt} : SStep w s w1 → Ssa w1 ss w2 →
      Ssa w (s :: ss) w2

theorem SStep.le {w w' : ℕ} {s : Stmt} (h : SStep w s w') : w ≤ w' := by
  cases h <;> omega

theorem Ssa.le {w w' : ℕ} {ss : List Stmt} (h : Ssa w ss w') : w ≤ w' := by
  induction h with
  | nil => exact le_rfl
  | cons h1 _ ih => exact le_trans h1.le ih

theorem SStep.wm {w w' : ℕ} {s : Stmt} (h : SStep w s w') : stepW w s = w' := by
  cases h <;> simp only [stepW] <;> split_ifs <;> omega

theorem Ssa.append {w w1 w2 : ℕ} {a b : List Stmt} (ha : Ssa w a w1) (hb : Ssa w1 b w2) :
    Ssa w (a ++ b) w2 := by
  induction ha with
  | nil => exact hb
  | cons h1 _ ih => exact .cons h1 (ih hb)

/-- A step changes no value below the watermark. -/
theorem SStep.keep {M : E → ℕ → E} {Pt : ℕ → E} {w w' : ℕ} {s : Stmt} (h : SStep w s w')
    (v : ℕ → E) (j : ℕ) (hj : j < w) : stepV M Pt w v s j = v j := by
  cases h <;> simp only [stepV] <;> split_ifs <;> first | rfl | exact Function.update_of_ne (by omega) _ _

/-- **A block changes no value below its watermark.** -/
theorem Ssa.keep {M : E → ℕ → E} {Pt : ℕ → E} {w w' : ℕ} {ss : List Stmt} (h : Ssa w ss w') :
    ∀ (v : ℕ → E) (j : ℕ), j < w → evalV M Pt w v ss j = v j := by
  induction h with
  | nil => intro v j _; rfl
  | cons h1 h2 ih =>
    intro v j hj
    rw [evalV, h1.wm, ih _ j (lt_of_lt_of_le hj h1.le), h1.keep v j hj]

/-! ## The side conditions -/

/-- A statement's side condition at the watermark `w`: a fresh load reads the memory's word, a
store holds, a divisor is not zero, a call holds in `C` at the given returns. -/
def Side (M : E → ℕ → E) (Pt : ℕ → E) (C : CallRel) (rd : Reader) (σ : Val) (w : ℕ) : Stmt → Prop
  | .atom (.load d p off) => if w ≤ d.idx then LoadHolds rd (σ p) off (M (σ p) off)
      else LoadHolds rd (σ p) off (σ d)
  | .atom (.mul d _ b) => d.idx < w → σ b ≠ 0
  | .callIf c f args => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) [])
  | .call f args rets => C f (args.map σ) (rets.map fun r ↦ Pt r.idx)
  | _ => True

/-- Every statement's side condition, at its watermark. -/
def SidesOk (M : E → ℕ → E) (Pt : ℕ → E) (C : CallRel) (rd : Reader) (σ : Val) : ℕ → List Stmt → Prop
  | _, [] => True
  | w, s :: ss => Side M Pt C rd σ w s ∧ SidesOk M Pt C rd σ (stepW w s) ss

theorem sidesOk_append {M : E → ℕ → E} {Pt : ℕ → E} {C : CallRel} {rd : Reader} {σ : Val}
    {w w1 : ℕ} {a b : List Stmt} (ha : Ssa w a w1) :
    SidesOk M Pt C rd σ w (a ++ b) ↔ SidesOk M Pt C rd σ w a ∧ SidesOk M Pt C rd σ w1 b := by
  induction ha with
  | nil => simp [SidesOk]
  | cons h1 _ ih => simp only [List.cons_append, SidesOk, h1.wm, ih, and_assoc]

/-- **A block at its evaluated values holds**, given its side conditions. -/
theorem ssa_allOk {M : E → ℕ → E} {Pt : ℕ → E} {C : CallRel} {rd : Reader} {w w' : ℕ}
    {ss : List Stmt} (h : Ssa w ss w') :
    ∀ (v : ℕ → E) (σ : Val), (∀ j < w', σ (.n j) = evalV M Pt w v ss j) →
      SidesOk M Pt C rd σ w ss → AllOk C rd σ ss := by
  induction h with
  | nil => intro _ _ _ _; exact allOk_nil
  | @cons w w1 w2 s ss h1 h2 ih =>
    intro v σ hσ hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [h1.wm] at hs2
    have hσ' : ∀ j < w2, σ (.n j) = evalV M Pt w1 (stepV M Pt w v s) ss j := by
      intro j hj; rw [hσ j hj, evalV, h1.wm]
    have hb : ∀ j < w1, σ (.n j) = stepV M Pt w v s j := fun j hj ↦ by
      rw [hσ' j (lt_of_lt_of_le hj h2.le), h2.keep _ j hj]
    have hw2 := h2.le
    refine allOk_cons.mpr ⟨?_, ih _ σ hσ' hs2⟩
    cases h1 with
    | @const d c hd =>
      simp only [stepV, V.n, hd, ↓reduceIte] at hb
      have := hb d (by omega); simp at this
      exact this
    | @add d a b hd ha hb' =>
      simp only [stepV, V.n, hd, ↓reduceIte] at hb
      have e := hb d (by omega)
      have ea := hb a (by omega)
      have eb := hb b (by omega)
      simp [show a ≠ d by omega, show b ≠ d by omega] at e ea eb
      show σ (.n d) = σ (.n a) + σ (.n b)
      rw [e, ea, eb]
    | @mul d a b hd ha hb' =>
      simp only [stepV, V.n, hd, ↓reduceIte] at hb
      have e := hb d (by omega)
      have ea := hb a (by omega)
      have eb := hb b (by omega)
      simp [show a ≠ d by omega, show b ≠ d by omega] at e ea eb
      show σ (.n d) = σ (.n a) * σ (.n b)
      rw [e, ea, eb]
    | @div d q b hd hq hb' =>
      simp only [stepV, V.n, show ¬ w ≤ d by omega, hq, ↓reduceIte] at hb
      have e := hb q (by omega)
      have ed := hb d (by omega)
      have eb := hb b (by omega)
      simp [show d ≠ q by omega, show b ≠ q by omega] at e ed eb
      have hne : σ (.n b) ≠ 0 := hs1 (by show d < w; omega)
      show σ (.n d) = σ (.n q) * σ (.n b)
      rw [e, ed, ← eb, div_mul_cancel₀ _ hne]
    | @copy d s hd hs' =>
      simp only [stepV, V.n, hd, ↓reduceIte] at hb
      have e := hb d (by omega)
      have es := hb s (by omega)
      simp [show s ≠ d by omega] at e es
      show σ (.n d) = σ (.n s)
      rw [e, es]
    | @load d p off hd hp =>
      simp only [stepV, V.n, hd, ↓reduceIte] at hb
      have e := hb d (by omega)
      have ep := hb p (by omega)
      simp [show p ≠ d by omega] at e ep
      simp only [Side, V.n, hd, ↓reduceIte] at hs1
      show LoadHolds rd (σ (.n p)) off (σ (.n d))
      rw [e, ← ep]; exact hs1
    | @store d p off hd hp =>
      simp only [Side, V.n, show ¬ w ≤ d by omega, ↓reduceIte] at hs1
      exact hs1
    | alloc _ => trivial
    | allocDyn _ _ => trivial
    | callIf _ _ => exact hs1
    | call0 _ => exact hs1
    | @call1 r f args hr ha =>
      simp only [stepV, V.n, hr, ↓reduceIte] at hb
      have e := hb r (by omega)
      simp at e
      simp only [Side, List.map_cons, List.map_nil] at hs1
      show C f ((args.map V.n).map σ) ([V.n r].map σ)
      simp only [List.map_cons, List.map_nil, e]
      exact hs1

/-- **A block at its evaluated values**, in `BlkA` form: the values from the valuation's below `w`,
the memory `memOf H`; the side conditions wherever `H` holds. -/
theorem ssa_blk {H : CallRel → Reader → Prop} {σ : Val} {Pt : ℕ → E} {w w' : ℕ} {ss : List Stmt}
    (h : Ssa w ss w') {Out : Val → Prop}
    (hside : ∀ C rd, H C rd → ∀ σ', AgreeBelow w σ σ' →
      RangeVals σ' w w' (evalV (memOf H) Pt w (fun i ↦ σ (.n i)) ss) →
      AllOk C rd σ' ss → Out σ')
    (hs : ∀ C rd, H C rd → ∀ σ', AgreeBelow w σ σ' →
      RangeVals σ' w w' (evalV (memOf H) Pt w (fun i ↦ σ (.n i)) ss) →
      SidesOk (memOf H) Pt C rd σ' w ss) :
    BlkA H σ w w' ss Out := by
  refine ⟨evalV (memOf H) Pt w (fun i ↦ σ (.n i)) ss, fun C rd hH σ' ha hr ↦ ?_⟩
  have hv : ∀ j < w', σ' (.n j) = evalV (memOf H) Pt w (fun i ↦ σ (.n i)) ss j := by
    intro j hj
    by_cases hjw : j < w
    · rw [ha j hjw, h.keep _ j hjw]
    · exact hr j (by omega) hj
  have hok := ssa_allOk h _ σ' hv (hs C rd hH σ' ha hr)
  exact ⟨hok, hside C rd hH σ' ha hr hok⟩

theorem Ssa.evalV_append {M : E → ℕ → E} {Pt : ℕ → E} {w w1 : ℕ} {a : List Stmt} (ha : Ssa w a w1)
    (v : ℕ → E) (b : List Stmt) : evalV M Pt w v (a ++ b) = evalV M Pt w1 (evalV M Pt w v a) b := by
  induction ha generalizing v with
  | nil => rfl
  | cons h1 _ ih => simp only [List.cons_append, evalV, h1.wm, ih]

/-- A block's values below its watermark are its prefix's. -/
theorem Ssa.evalV_lt {M : E → ℕ → E} {Pt : ℕ → E} {w w1 w2 : ℕ} {a b : List Stmt} (ha : Ssa w a w1)
    (hb : Ssa w1 b w2) (v : ℕ → E) {j : ℕ} (hj : j < w1) :
    evalV M Pt w v (a ++ b) j = evalV M Pt w v a j := by
  rw [ha.evalV_append, hb.keep _ j hj]

/-! ## Pure blocks: definitions and fresh loads only -/

/-- **A pure block in order**: constants, sums, products, copies and fresh loads, each past the
watermark from values below it. -/
inductive SsaP : ℕ → List Stmt → ℕ → Prop
  | nil {w : ℕ} : SsaP w [] w
  | const {w w' d : ℕ} {c : E} {ss : List Stmt} : w ≤ d → SsaP (d + 1) ss w' →
      SsaP w (.atom (.const (.n d) c) :: ss) w'
  | add {w w' d a b : ℕ} {ss : List Stmt} : w ≤ d → a < d → b < d → SsaP (d + 1) ss w' →
      SsaP w (.atom (.add (.n d) (.n a) (.n b)) :: ss) w'
  | mul {w w' d a b : ℕ} {ss : List Stmt} : w ≤ d → a < d → b < d → SsaP (d + 1) ss w' →
      SsaP w (.atom (.mul (.n d) (.n a) (.n b)) :: ss) w'
  | copy {w w' d s : ℕ} {ss : List Stmt} : w ≤ d → s < d → SsaP (d + 1) ss w' →
      SsaP w (.atom (.copy (.n d) (.n s)) :: ss) w'
  | load {w w' d p off : ℕ} {ss : List Stmt} : w ≤ d → p < d → SsaP (d + 1) ss w' →
      SsaP w (.atom (.load (.n d) (.n p) off) :: ss) w'

theorem SsaP.toSsa {w w' : ℕ} {ss : List Stmt} (h : SsaP w ss w') : Ssa w ss w' := by
  induction h with
  | nil => exact .nil
  | const h1 _ ih => exact .cons (.const h1) ih
  | add h1 h2 h3 _ ih => exact .cons (.add h1 h2 h3) ih
  | mul h1 h2 h3 _ ih => exact .cons (.mul h1 h2 h3) ih
  | copy h1 h2 _ ih => exact .cons (.copy h1 h2) ih
  | load h1 h2 _ ih => exact .cons (.load h1 h2) ih

theorem SsaP.le {w w' : ℕ} {ss : List Stmt} (h : SsaP w ss w') : w ≤ w' := h.toSsa.le

theorem SsaP.append {w w1 w2 : ℕ} {a b : List Stmt} (ha : SsaP w a w1) (hb : SsaP w1 b w2) :
    SsaP w (a ++ b) w2 := by
  induction ha with
  | nil => exact hb
  | const h1 _ ih => exact .const h1 (ih hb)
  | add h1 h2 h3 _ ih => exact .add h1 h2 h3 (ih hb)
  | mul h1 h2 h3 _ ih => exact .mul h1 h2 h3 (ih hb)
  | copy h1 h2 _ ih => exact .copy h1 h2 (ih hb)
  | load h1 h2 _ ih => exact .load h1 h2 (ih hb)

/-- The loads of a block: their pointers and offsets. -/
def loadsOf : List Stmt → List (ℕ × ℕ)
  | [] => []
  | .atom (.load _ p off) :: ss => (p.idx, off) :: loadsOf ss
  | _ :: ss => loadsOf ss

theorem loadsOf_append (a b : List Stmt) : loadsOf (a ++ b) = loadsOf a ++ loadsOf b := by
  induction a with
  | nil => rfl
  | cons s a ih =>
    rcases s with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ | _ | _ | _ <;>
      simp [loadsOf, ih]

/-- **A pure block's side conditions**: its loads' words, in the memory `M`. -/
theorem SsaP.sidesOk {M : E → ℕ → E} {Pt : ℕ → E} {C : CallRel} {rd : Reader} {σ : Val}
    {w w' : ℕ} {ss : List Stmt} (h : SsaP w ss w')
    (hM : ∀ p off, (p, off) ∈ loadsOf ss → LoadHolds rd (σ (.n p)) off (M (σ (.n p)) off)) :
    SidesOk M Pt C rd σ w ss := by
  induction h with
  | nil => trivial
  | @const w w' d c ss h1 _ ih =>
    exact ⟨trivial, by simp only [stepW, h1, ↓reduceIte]; exact ih hM⟩
  | @add w w' d a b ss h1 _ _ _ ih =>
    exact ⟨trivial, by simp only [stepW, h1, ↓reduceIte]; exact ih hM⟩
  | @mul w w' d a b ss h1 _ _ _ ih =>
    refine ⟨fun h ↦ absurd (show d < w from h) (by omega), ?_⟩
    simp only [stepW, h1, ↓reduceIte]; exact ih hM
  | @copy w w' d s ss h1 _ _ ih =>
    exact ⟨trivial, by simp only [stepW, h1, ↓reduceIte]; exact ih hM⟩
  | @load w w' d p off ss h1 _ _ ih =>
    refine ⟨?_, ?_⟩
    · simp only [Side, V.n, h1, ↓reduceIte]
      exact hM p off (by simp [loadsOf])
    · simp only [stepW, h1, ↓reduceIte]
      exact ih fun p' o' hm ↦ hM p' o' (by simp [loadsOf, hm])

/-! ## Allocations -/

/-- **A block's allocations**, in order: each pointer's value and its size (a dynamic one's the
exponent of its size word). -/
noncomputable def AllocsAt (σ : Val) (ss : List Stmt) : List (E × ℕ) :=
  (ss.filterMap Memory.Stmt.allocSz).map fun x ↦ (σ x.1, x.2.elim id fun s ↦ Memory.logG (σ s))

theorem allocsAt_append (σ : Val) (a b : List Stmt) :
    AllocsAt σ (a ++ b) = AllocsAt σ a ++ AllocsAt σ b := by
  simp [AllocsAt, List.filterMap_append]

theorem allocsAt_cons (σ : Val) (s : Stmt) (ss : List Stmt) :
    AllocsAt σ (s :: ss) = AllocsAt σ [s] ++ AllocsAt σ ss := by
  rw [← allocsAt_append]; rfl

/-- A pure block allocates nothing. -/
theorem SsaP.allocs {w w' : ℕ} {ss : List Stmt} (h : SsaP w ss w') (σ : Val) : AllocsAt σ ss = [] := by
  induction h with
  | nil => rfl
  | const _ _ ih | add _ _ _ _ ih | mul _ _ _ _ ih | copy _ _ _ ih | load _ _ _ ih =>
    rw [allocsAt_cons, ih]; rfl

/-- A `HeapBuf(g^e)` at `k`: its pointer `k + 1`, its size `e`. -/
theorem allocsAt_heap (σ : Val) (e k : ℕ) (he : e < 2 ^ 64 - 1) (hs : σ (.n k) = gw e) :
    AllocsAt σ (osHeap e k) = [(σ (.n (k + 1)), e)] := by
  simp only [AllocsAt, osHeap, List.filterMap_cons, Memory.Stmt.allocSz, List.filterMap_nil,
    List.map_cons, List.map_nil, Sum.elim_inr, hs, gw_eq (show e < u128Bound by unfold u128Bound; omega)]
  rw [Memory.logG_gen_pow he]

/-- **A pure block holds at its evaluated values**, its loads reading words every reader `H` admits
fixes, from pointers below its first value. -/
theorem pure_blk {H : CallRel → Reader → Prop} {σ : Val} {w w' : ℕ} {ss : List Stmt} (h : SsaP w ss w')
    (hL : ∀ p o, (p, o) ∈ loadsOf ss → p < w ∧ ∃ v, ∀ C rd, H C rd → LoadHolds rd (σ (.n p)) o v) :
    BlkA H σ w w' ss (fun σ' ↦ AllocsAt σ' ss = []) := by
  refine ssa_blk (Pt := fun _ ↦ 0) h.toSsa (fun _ _ _ σ' _ _ _ ↦ h.allocs σ') fun C rd hH σ' ha _ ↦ ?_
  refine h.sidesOk fun p o hpo ↦ ?_
  obtain ⟨hp, v, hv⟩ := hL p o hpo
  rw [ha _ hp, memOf_eq hv hH]
  exact hv C rd hH

end
end LeanVM.Guest.B1.Whir
