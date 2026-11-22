/-
  LeanVM.Guest.Bridge.AllocCur

  What the bump pointer check gives at each offset: the buffers reserved before it, and the callee
  frame pending at it, from one offset to the next a step reaches.
-/

module

public import LeanVM.Guest.Bridge.AllocDefs
public import LeanVM.Guest.Bridge.JumpCellsSound
public import LeanVM.Guest.Bridge.AlignSound

/-!
# The bump pointer's static part by offset

For a function's advice `d` (its pcs increasing from its entry, `HintsUp`), `hintsAtD d entry off`
are the hints at offset `off`; `nbAt` counts the buffer hints before an offset, `pendAt` says a
callee frame is reserved and not entered. From `curChk`:

* `nb_succ`: past an offset, the buffer hints at it are counted; `nb_skip`: a jump skipping no
  buffer hint counts those at its offset; `nb_none`: past every buffer hint, all of them;
* `pend_succ`: past an instruction no jump, the frame hints at it are pending (at most one frame
  pending, `pend_le`); `pend_nf`: at a jump no frame hint's, nothing is pending or reserved;
  `pend_site`: at a jump through a call site's frame cell, its frame was reserved and is no longer
  pending past it;
* `bufsJumps_at`, `targetsOk_at`, `blockM_sels`, `armTgtsOk_at`: the code's jumps and the body's
  `match`es as the check sees them; `allocDsts_le_cnt`: a path allocates at most `cntL` buffers.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- The hints at offset `off`, the function's entry `entry`. -/
def hintsAtD (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (entry off : ℕ) : List Prover.Exec.Hint :=
  (d.2.2.lookup (entry + off)).getD []

/-- The advice's pcs increasing from the entry `entry`. -/
def HintsUp (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (entry : ℕ) : Prop :=
  d.1 = entry ∧ pcsUp d.2.2 = true ∧ ∀ p ∈ d.2.2, entry ≤ p.1

/-- The buffer hints with their offsets. -/
noncomputable def bufsOf (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : List (ℕ × Prover.Exec.Hint) :=
  (allocHints d).filter fun q ↦ isBuf X q.2

end

public section

/-! ## Offsets of the hints -/

/-- **The hints at an offset**: those of the advice's pc there. -/
theorem countP_off {entry off : ℕ} (p : Prover.Exec.Hint → Bool) :
    ∀ (l : List (ℕ × List Prover.Exec.Hint)), pcsUp l = true → (∀ q ∈ l, entry ≤ q.1) →
      (l.flatMap fun q ↦ q.2.map fun h ↦ (q.1 - entry, h)).countP (fun q ↦ decide (q.1 = off) && p q.2) =
        ((l.lookup (entry + off)).getD []).countP p
  | [], _, _ => rfl
  | ⟨a1, a2⟩ :: l, hu, hge => by
    rw [List.flatMap_cons, List.countP_append, countP_off p l (pcsUp_tail hu) fun q hq ↦ hge q (List.mem_cons_of_mem _ hq)]
    have ha := hge _ List.mem_cons_self
    simp only at ha
    rw [List.lookup_cons]
    by_cases he : a1 = entry + off
    · have hk : (entry + off == a1) = true := by simp [he]
      rw [hk]
      have hnone : l.lookup (entry + off) = none := by
        rw [List.lookup_eq_none_iff]
        intro q hq
        have := pcsUp_lt hu q hq
        simp only at this
        simp only [bne_iff_ne, ne_eq]
        omega
      rw [hnone, List.countP_map]
      simp only [Option.getD_none, List.countP_nil, Nat.add_zero, Option.getD_some]
      congr 1
      funext h
      simp [Function.comp, show a1 - entry = off by omega]
    · have hk : (entry + off == a1) = false := by simp; omega
      rw [hk, List.countP_map]
      have : (a2.countP ((fun q ↦ decide (q.1 = off) && p q.2) ∘ fun h ↦ (a1 - entry, h))) = 0 := by
        rw [List.countP_eq_zero]
        intro h _
        simp only [Function.comp, Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro h'
        omega
      rw [this, Nat.zero_add]

theorem isBuf_ptr {X : AlignCtx} {h : Prover.Exec.Hint} (hb : isBuf X h = true) : (allocPtr h).isSome = true := by
  unfold isBuf at hb; simp only [Bool.and_eq_true] at hb; exact hb.1

theorem isFrame_ptr {X : AlignCtx} {h : Prover.Exec.Hint} (hb : isFrame X h = true) : (allocPtr h).isSome = true := by
  unfold isFrame at hb
  split at hb
  · rename_i p hp; rw [hp]; rfl
  · cases hb

theorem countP_alloc {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {p : Prover.Exec.Hint → Bool}
    (hp : ∀ h, p h = true → (allocPtr h).isSome = true) (r : ℕ × Prover.Exec.Hint → Bool) :
    ((allocHints d).filter fun q ↦ p q.2).countP r = (hintsOff d).countP fun q ↦ r q && p q.2 := by
  unfold allocHints
  rw [List.filter_filter, List.countP_filter]
  congr 1
  funext q
  cases h1 : p q.2
  · simp
  · simp [hp _ h1]

/-- **The hints of a kind at an offset**, counted among the function's. -/
theorem countP_at {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {entry : ℕ} (hU : HintsUp d entry)
    {p : Prover.Exec.Hint → Bool} (hp : ∀ h, p h = true → (allocPtr h).isSome = true) (off : ℕ) :
    ((allocHints d).filter fun q ↦ p q.2).countP (fun q ↦ decide (q.1 = off)) = (hintsAtD d entry off).countP p := by
  rw [countP_alloc hp]
  obtain ⟨h1, h2, h3⟩ := hU
  have := countP_off (entry := entry) (off := off) p d.2.2 h2 h3
  unfold hintsOff
  rw [h1]
  exact this

/-! ## The buffers before an offset -/

variable {X : AlignCtx} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}

theorem nbAt_eq (off : ℕ) : nbAt X d off = (bufsOf X d).countP fun q ↦ decide (q.1 < off) := by
  unfold nbAt bufsOf
  rw [List.countP_filter, List.countP_eq_length_filter]

theorem countP_lt_succ (l : List (ℕ × Prover.Exec.Hint)) (off : ℕ) :
    l.countP (fun q ↦ decide (q.1 < off + 1)) = l.countP (fun q ↦ decide (q.1 < off)) + l.countP (fun q ↦ decide (q.1 = off)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    by_cases h1 : a.1 < off
    · simp [h1, show a.1 < off + 1 by omega, show a.1 ≠ off by omega]; omega
    · by_cases h2 : a.1 = off
      · simp [h2]; omega
      · simp [show ¬ a.1 < off + 1 by omega, h1, h2]

/-- **Past an offset, the buffer hints at it are counted.** -/
theorem nb_succ {entry : ℕ} (hU : HintsUp d entry) (off : ℕ) :
    nbAt X d (off + 1) = nbAt X d off + (hintsAtD d entry off).countP (isBuf X) := by
  rw [nbAt_eq, nbAt_eq, countP_lt_succ, bufsOf, countP_at hU (fun _ ↦ isBuf_ptr (X := X)) off]

/-- **A jump skipping no buffer hint** counts those at its offset. -/
theorem nb_skip {entry : ℕ} (hU : HintsUp d entry) {off t : ℕ} (hlt : off < t)
    (h : ∀ q ∈ bufsOf X d, ¬(off < q.1 ∧ q.1 < t)) :
    nbAt X d t = nbAt X d off + (hintsAtD d entry off).countP (isBuf X) := by
  rw [← nb_succ hU, nbAt_eq, nbAt_eq]
  apply List.countP_congr
  intro q hq
  have := h q hq
  simp only [decide_eq_true_eq]
  omega

/-- **Past every buffer hint**, all of them are counted. -/
theorem nb_none {entry : ℕ} (hU : HintsUp d entry) {off : ℕ} (h : ∀ q ∈ bufsOf X d, q.1 ≤ off) :
    nbAt X d off + (hintsAtD d entry off).countP (isBuf X) = (bufsOf X d).length ∧
      ∀ t, off < t → nbAt X d t = (bufsOf X d).length := by
  have hall : ∀ t, off < t → nbAt X d t = (bufsOf X d).length := fun t ht ↦ by
    rw [nbAt_eq, List.countP_eq_length]
    intro q hq
    have := h q hq
    simp only [decide_eq_true_eq]
    omega
  exact ⟨by rw [← nb_succ hU]; exact hall _ (Nat.lt_succ_self _), hall⟩

/-! ## The next jump -/

variable {code : List OffsetInstruction}

theorem nextJump_ge (a : ℕ) : a ≤ nextJump code a := Nat.le_add_right _ _

theorem findIdx_le {α : Type} {p : α → Bool} {xs : List α} {j : ℕ} (hj : j < xs.length) (hp : p xs[j] = true) :
    xs.findIdx p ≤ j := by
  by_contra h
  have := List.not_of_lt_findIdx (p := p) (xs := xs) (i := j) (by omega)
  rw [this] at hp
  cases hp

theorem nextJump_le {a i : ℕ} {ins : OffsetInstruction} (hi : code[i]? = some ins) (hj : ins.isJump = true)
    (ha : a ≤ i) : nextJump code a ≤ i := by
  unfold nextJump
  have h1 : (code.drop a)[i - a]? = some ins := by
    rw [List.getElem?_drop, show a + (i - a) = i by omega]; exact hi
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h1
  have := findIdx_le (p := OffsetInstruction.isJump) hlt (by rw [heq]; exact hj)
  omega

theorem nextJump_not {a i : ℕ} {ins : OffsetInstruction} (hi : code[i]? = some ins) (ha : a ≤ i)
    (hlt : i < nextJump code a) : ins.isJump = false := by
  cases hj : ins.isJump
  · rfl
  · exact absurd (nextJump_le hi hj ha) (by omega)

/-- The next jump, where there is one, is a jump. -/
theorem nextJump_jump {a : ℕ} {ins : OffsetInstruction} (hi : code[nextJump code a]? = some ins) : ins.isJump = true := by
  unfold nextJump at hi
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  have h2 : (code.drop a).findIdx OffsetInstruction.isJump < (code.drop a).length := by
    rw [List.length_drop]; omega
  have := List.findIdx_getElem (w := h2)
  rw [List.getElem_drop] at this
  rw [List.getElem?_eq_getElem hlt] at hi
  rw [← Option.some.inj hi]
  exact this

/-- From an offset up to a next jump that is one, the next jump is the same. -/
theorem nextJump_eq {a b : ℕ} {ins : OffsetInstruction} (hi : code[nextJump code a]? = some ins) (hab : a ≤ b)
    (hb : b ≤ nextJump code a) : nextJump code b = nextJump code a := by
  have h1 : nextJump code b ≤ nextJump code a := nextJump_le hi (nextJump_jump hi) hb
  by_contra hne
  have hlt : nextJump code b < nextJump code a := lt_of_le_of_ne h1 hne
  have hlen : nextJump code b < code.length := lt_of_lt_of_le hlt (List.getElem?_eq_some_iff.mp hi).1.le
  obtain ⟨ins', hins'⟩ : ∃ ins', code[nextJump code b]? = some ins' := ⟨_, List.getElem?_eq_getElem hlen⟩
  have := nextJump_not hins' (le_trans hab (nextJump_ge b)) hlt
  rw [nextJump_jump hins'] at this
  cases this

/-! ## What is pending at an offset -/

section Pend

variable {fr : List (ℕ × Prover.Exec.Hint)}

theorem countP_or {α : Type} {p q : α → Bool} (h : ∀ x, ¬(p x = true ∧ q x = true)) :
    ∀ l : List α, l.countP (fun x ↦ p x || q x) = l.countP p + l.countP q
  | [] => rfl
  | a :: l => by
    simp only [List.countP_cons, countP_or h l]
    have := h a
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

theorem countP_le_one_of {α : Type} {l : List α} {p : α → Bool} (h : 0 < l.countP p → l.countP p ≤ 1) :
    l.countP p ≤ 1 := by
  rcases Nat.eq_zero_or_pos (l.countP p) with h0 | h0
  · omega
  · exact h h0

theorem pendIn_eq (off : ℕ) :
    pendIn code fr off = decide (0 < fr.countP fun q ↦ decide (q.1 < off) && decide (off ≤ nextJump code q.1)) := by
  unfold pendIn
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, List.countP_pos_iff]

/-- The frame hints whose next jump is `i`: at most one at a jump. -/
@[expose] def FrUniq (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) : Prop :=
  ∀ i ins, code[i]? = some ins → ins.isJump = true → (fr.filter fun r ↦ Nat.beq (nextJump code r.1) i).length ≤ 1

/-- Each frame hint's next jump a jump. -/
@[expose] def FrJump (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) : Prop :=
  ∀ q ∈ fr, ∃ ins, code[nextJump code q.1]? = some ins

theorem countP_uniq (hU : FrUniq code fr) {i : ℕ} {ins : OffsetInstruction} (hi : code[i]? = some ins)
    (hj : ins.isJump = true) {p : ℕ × Prover.Exec.Hint → Bool} (hp : ∀ q ∈ fr, p q = true → nextJump code q.1 = i) :
    fr.countP p ≤ 1 := by
  have := hU i ins hi hj
  rw [← List.countP_eq_length_filter] at this
  refine le_trans (List.countP_mono_left fun q hq hpq ↦ ?_) this
  simp [hp q hq hpq]

/-- **Past an instruction no jump**, the frame hints at it are pending, at most one frame in all. -/
theorem pend_succ (hF : FrJump code fr) (hU : FrUniq code fr) {off : ℕ} {ins : OffsetInstruction}
    (hi : code[off]? = some ins) (hj : ins.isJump = false) :
    (bif pendIn code fr (off + 1) then 1 else 0) =
      (bif pendIn code fr off then 1 else 0) + fr.countP fun q ↦ decide (q.1 = off) := by
  have hne : ∀ q ∈ fr, nextJump code q.1 ≠ off := fun q hq he ↦ by
    obtain ⟨ins', hins'⟩ := hF q hq
    rw [he, hi] at hins'
    rw [Option.some.inj hins', nextJump_jump (he ▸ hi.trans (by rw [Option.some.inj hins'])) ] at hj
    cases hj
  set A : ℕ × Prover.Exec.Hint → Bool := fun q ↦ decide (q.1 < off) && decide (off ≤ nextJump code q.1)
  set B : ℕ × Prover.Exec.Hint → Bool := fun q ↦ decide (q.1 = off)
  have hkey : fr.countP (fun q ↦ decide (q.1 < off + 1) && decide (off + 1 ≤ nextJump code q.1)) =
      fr.countP (fun q ↦ A q || B q) := by
    apply List.countP_congr
    intro q hq
    have h1 := hne q hq
    have h2 := nextJump_ge (code := code) q.1
    simp only [A, B, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hdis : ∀ q, ¬(A q = true ∧ B q = true) := fun q ⟨h1, h2⟩ ↦ by
    simp only [A, B, Bool.and_eq_true, decide_eq_true_eq] at h1 h2; omega
  have hle : fr.countP A + fr.countP B ≤ 1 := by
    rw [← countP_or hdis]
    refine countP_le_one_of fun h0 ↦ ?_
    obtain ⟨q0, hq0, hab⟩ := List.countP_pos_iff.mp h0
    obtain ⟨ins0, hins0⟩ := hF q0 hq0
    refine countP_uniq hU hins0 (nextJump_jump hins0) fun q hq habq ↦ ?_
    have hq0b : q0.1 ≤ off ∧ off ≤ nextJump code q0.1 := by
      simp only [A, B, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
      rcases hab with ⟨h1, h2⟩ | h1
      · exact ⟨h1.le, h2⟩
      · exact ⟨h1.le, h1 ▸ nextJump_ge _⟩
    have hqb : q.1 ≤ off ∧ off ≤ nextJump code q.1 := by
      simp only [A, B, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at habq
      rcases habq with ⟨h1, h2⟩ | h1
      · exact ⟨h1.le, h2⟩
      · exact ⟨h1.le, h1 ▸ nextJump_ge _⟩
    obtain ⟨insq, hinsq⟩ := hF q hq
    rw [← nextJump_eq hinsq hqb.1 hqb.2, nextJump_eq hins0 hq0b.1 hq0b.2]
  rw [pendIn_eq, pendIn_eq, hkey, countP_or hdis]
  change (bif decide (0 < fr.countP A + fr.countP B) then 1 else 0) = (bif decide (0 < fr.countP A) then 1 else 0) +
    fr.countP B
  generalize fr.countP A = a at hle ⊢
  generalize fr.countP B = b at hle ⊢
  by_cases ha : 0 < a <;> by_cases hb : 0 < a + b <;> simp [ha, hb] <;> omega

/-- **At a jump no frame hint's**, nothing is pending or reserved, before or past it. -/
theorem pend_nf {off : ℕ} {ins : OffsetInstruction} (hi : code[off]? = some ins) (hj : ins.isJump = true)
    (hn : ∀ q ∈ fr, nextJump code q.1 ≠ off) :
    pendIn code fr off = false ∧ fr.countP (fun q ↦ decide (q.1 = off)) = 0 ∧ pendIn code fr (off + 1) = false := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pendIn
    rw [List.any_eq_false]
    intro q hq
    have := hn q hq
    have := fun h : q.1 ≤ off ↦ nextJump_le hi hj h
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    omega
  · rw [List.countP_eq_zero]
    intro q hq
    have := hn q hq
    have := fun h : q.1 ≤ off ↦ nextJump_le hi hj h
    have := nextJump_ge (code := code) q.1
    simp only [decide_eq_true_eq]
    omega
  · unfold pendIn
    rw [List.any_eq_false]
    intro q hq
    have := fun h : q.1 ≤ off ↦ nextJump_le hi hj h
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    omega

/-- **At a jump some frame hint's**, its frame was reserved, the only one, and is not pending past it. -/
theorem pend_site (hU : FrUniq code fr) {off : ℕ} {ins : OffsetInstruction} (hi : code[off]? = some ins)
    (hj : ins.isJump = true) (hr : ∃ r ∈ fr, nextJump code r.1 = off) :
    (bif pendIn code fr off then 1 else 0) + fr.countP (fun q ↦ decide (q.1 = off)) = 1 ∧
      pendIn code fr (off + 1) = false := by
  refine ⟨?_, ?_⟩
  · set A : ℕ × Prover.Exec.Hint → Bool := fun q ↦ decide (q.1 < off) && decide (off ≤ nextJump code q.1)
    set B : ℕ × Prover.Exec.Hint → Bool := fun q ↦ decide (q.1 = off)
    have hdis : ∀ q, ¬(A q = true ∧ B q = true) := fun q ⟨h1, h2⟩ ↦ by
      simp only [A, B, Bool.and_eq_true, decide_eq_true_eq] at h1 h2; omega
    have hle : fr.countP A + fr.countP B ≤ 1 := by
      rw [← countP_or hdis]
      refine countP_uniq hU hi hj fun q hq hab ↦ ?_
      simp only [A, B, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
      rcases hab with ⟨h1, h2⟩ | h1
      · exact le_antisymm (nextJump_le hi hj h1.le) h2
      · exact le_antisymm (nextJump_le hi hj h1.le) (h1 ▸ nextJump_ge _)
    obtain ⟨r, hr, hrj⟩ := hr
    have hge : 0 < fr.countP A + fr.countP B := by
      have := nextJump_ge (code := code) r.1
      rcases Nat.lt_or_ge r.1 off with h | h
      · have : 0 < fr.countP A := List.countP_pos_iff.mpr ⟨r, hr, by simp [A, h, hrj]⟩
        omega
      · have : 0 < fr.countP B := List.countP_pos_iff.mpr ⟨r, hr, by simp [B]; omega⟩
        omega
    rw [pendIn_eq]
    change (bif decide (0 < fr.countP A) then 1 else 0) + fr.countP B = 1
    generalize fr.countP A = a at hle hge ⊢
    generalize fr.countP B = b at hle hge ⊢
    by_cases ha : 0 < a <;> simp [ha] <;> omega
  · unfold pendIn
    rw [List.any_eq_false]
    intro q hq
    have := fun h : q.1 ≤ off ↦ nextJump_le hi hj h
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    omega

end Pend

/-! ## The check's walks -/

theorem bufsJumps_at {X : AlignCtx} {bs : List (ℕ × Prover.Exec.Hint)} :
    ∀ (k : ℕ) (l : List OffsetInstruction), bufsJumps X bs k l = true → ∀ i oc od of, l[i]? = some (.jump oc od of) →
      (∀ q ∈ bs, q.1 ≤ k + i) ∨ bufJumpOk X bs (k + i) oc od of = true
  | _, [], _, _, _, _, _, h => by simp at h
  | k, ins :: rest, h, i, oc, od, of, hi => by
    simp only [bufsJumps, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, not_lt,
        Nat.add_zero] at h ⊢
      exact h.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := bufsJumps_at (k + 1) rest h.2 i oc od of hi
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem sitesOk_at {X : AlignCtx} {code : List OffsetInstruction} {fr : List (ℕ × Prover.Exec.Hint)} :
    ∀ (k : ℕ) (l : List OffsetInstruction), sitesOk X code fr k l = true → ∀ i oc od q, l[i]? = some (.jump oc od q) →
      ((getF X.sites q).isSome = true →
        ∃ r ∈ fr, allocPtr r.2 = some q ∧ nextJump code r.1 = k + i) ∧
      (fr.filter fun r ↦ Nat.beq (nextJump code r.1) (k + i)).length ≤ 1
  | _, [], _, _, _, _, _, h => by simp at h
  | k, ins :: rest, h, i, oc, od, q, hi => by
    simp only [sitesOk, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        Nat.beq_eq, decide_eq_true_eq, Nat.add_zero] at h ⊢
      obtain ⟨⟨h1, h2⟩, -⟩ := h
      refine ⟨fun hs ↦ ?_, h2⟩
      rcases h1 with h1 | h1
      · rw [h1] at hs; cases hs
      · exact h1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := sitesOk_at (k + 1) rest h.2 i oc od q hi
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem targetsOk_at {X : AlignCtx} {code : List OffsetInstruction} {fr : List (ℕ × Prover.Exec.Hint)} :
    ∀ (l : List OffsetInstruction), targetsOk X code fr l = true → ∀ (i oc od of : ℕ),
      l[i]? = some (OffsetInstruction.jump oc od of) →
      ∀ t, X.pcAt od = some t → pendIn code fr (t - X.entry) = false
  | [], _, _, _, _, _, h, _, _ => by simp at h
  | ins :: rest, h, i, oc, od, of, hi, t, ht => by
    simp only [targetsOk, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have := h.1
      simp only [ht, Bool.not_eq_true'] at this
      exact this
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      exact targetsOk_at rest h.2 i oc od of hi t ht

/-! ## The body's `match`es and allocations -/

/-- `blockM` of a statement. -/
noncomputable def stmtM (ok : V → ℕ → Bool) : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun x arms ha ↦ ok x arms.length && ha) (fun _ _ _ ↦ true)
    (fun _ _ _ ↦ true) (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

/-- `blockM` of arms. -/
noncomputable def armsM (ok : V → ℕ → Bool) : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun x arms ha ↦ ok x arms.length && ha) (fun _ _ _ ↦ true)
    (fun _ _ _ ↦ true) (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

section M

variable (ok : V → ℕ → Bool)

mutual
theorem blockM_sels : ∀ (ss : List Stmt), blockM ok ss = true → ∀ s ∈ stmtsOf ss, ∀ x arms,
    s = .match_ x arms → ok x arms.length = true
  | [], _, s, hs => by simp [stmtsOf] at hs
  | s' :: ss, h, s, hs => by
    change (stmtM ok s' && blockM ok ss) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsOf, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · intro x arms he
      subst he
      have h1 := h.1
      change (ok x arms.length && armsM ok arms) = true at h1
      exact ((Bool.and_eq_true _ _).mp h1).1
    · exact stmtM_sels s' h.1 s hs
    · exact blockM_sels ss h.2 s hs

theorem stmtM_sels : ∀ (s' : Stmt), stmtM ok s' = true → ∀ s ∈ stmtsSub s', ∀ x arms,
    s = .match_ x arms → ok x arms.length = true
  | .ite c' z n, h, s, hs => by
    change (blockM ok z && blockM ok n) = true at h
    simp only [Bool.and_eq_true] at h
    simp only [stmtsSub, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockM_sels z h.1 s hs
    · exact blockM_sels n h.2 s hs
  | .match_ x arms, h, s, hs => by
    change (ok x arms.length && armsM ok arms) = true at h
    rw [Bool.and_eq_true] at h
    exact armsM_sels arms h.2 s hs
  | .atom _, _, _, hs | .call .., _, _, hs | .callIf .., _, _, hs | .dispatch .., _, _, hs | .ret _, _, _, hs => by
    simp [stmtsSub] at hs

theorem armsM_sels : ∀ (arms : List (List Stmt)), armsM ok arms = true → ∀ s ∈ stmtsArms arms, ∀ x as,
    s = .match_ x as → ok x as.length = true
  | [], _, s, hs => by simp [stmtsArms] at hs
  | a :: as, h, s, hs => by
    change (blockM ok a && armsM ok as) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsArms, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockM_sels a h.1 s hs
    · exact armsM_sels as h.2 s hs
end

end M

theorem armTgtsOk_at {X : AlignCtx} {P : B2C.Plumb} {code : List OffsetInstruction} {fr : List (ℕ × Prover.Exec.Hint)}
    {x : V} {n : ℕ} (h : armTgtsOk X P code fr x n = true) {od : ℕ} {a : ℕ × ℕ} (ha : (od, a) ∈ armsOf P)
    (hax : a.1 = x.idx) {k t : ℕ} (hk : k < n) (ht : getF X.jt (a.2 + k) = some t) :
    pendIn code fr (t - X.entry) = false := by
  have h1 := List.all_eq_true.mp h _ ha
  simp only [hax, Nat.beq_refl, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have := h1 k hk
  simp only [ht, Bool.not_eq_true'] at this
  exact this

/-- `cntL` of a statement. -/
noncomputable def cntS : Stmt → ℕ :=
  Stmt.rec (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun a ↦ bif allocAtom a then 1 else 0) (fun _ _ _ hz hn ↦ hz + hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ 0)
    (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) (fun _ ↦ 0) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

/-- `cntL` of arms. -/
noncomputable def cntA : List (List Stmt) → ℕ :=
  Stmt.rec_2 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun a ↦ bif allocAtom a then 1 else 0) (fun _ _ _ hz hn ↦ hz + hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ 0)
    (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) (fun _ ↦ 0) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

section Cnt

variable {σ : Val}

/-- The events of an outcome. -/
def evs : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

theorem nA_pre (es : List Ev) : ∀ o : Out, (allocDsts (evs (o.pre es))).length ≤
    (allocDsts es).length + (allocDsts (evs o)).length
  | .fall _ | .ret _ _ => by simp [Out.pre, evs, allocDsts]
  | .stuck => by simp [Out.pre, evs, allocDsts]

theorem nA_seq (k : Out) : ∀ o : Out, (allocDsts (evs (o.seq k))).length ≤
    (allocDsts (evs o)).length + (allocDsts (evs k)).length
  | .fall es => by simp only [Out.seq]; exact nA_pre es k
  | .ret _ _ => by simp [Out.seq, evs]
  | .stuck => by simp [Out.seq, evs, allocDsts]

theorem nA_pick {x : V} {args rets : List V} :
    ∀ (fs : List String) (j : ℕ), (allocDsts (evs (pick σ x args rets j fs))).length = 0
  | [], _ => by simp [pick, evs, allocDsts]
  | f :: fs, j => by
    rw [pick]
    split_ifs
    · simp [evs, allocDsts, Ev.allocDst?]
    · exact nA_pick fs (j + 1)

mutual
theorem nA_walk1 : ∀ (s : Stmt), (allocDsts (evs (walk1 σ s))).length ≤ cntS s
  | .atom a => by
    change (allocDsts [Ev.atom a]).length ≤ bif allocAtom a then 1 else 0
    rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _ <;>
      simp [allocDsts, Ev.allocDst?, allocAtom, coreFlow]
  | .ite c z n => by
    change _ ≤ cntL z + cntL n
    rw [walk1]
    refine (nA_pre _ _).trans ?_
    have h1 := nA_walk z
    have h2 := nA_walk n
    have h0 : (allocDsts [Ev.inK c]).length = 0 := rfl
    split_ifs <;> omega
  | .match_ x arms => by
    change _ ≤ cntA arms
    rw [walk1]
    exact nA_arms x arms 0
  | .call f args rets => by
    change (allocDsts [Ev.call f args rets]).length ≤ 0
    exact Nat.le_of_eq rfl
  | .callIf c f args => by
    change (allocDsts [.inK c, if σ c = 0 then .skip f args else .call f args []]).length ≤ 0
    split_ifs <;> exact Nat.le_of_eq rfl
  | .dispatch x fs args rets => by rw [walk1, nA_pick]; exact Nat.zero_le _
  | .ret _ => by simp [walk1, evs, allocDsts]

theorem nA_walk : ∀ (ss : List Stmt), (allocDsts (evs (walk σ ss))).length ≤ cntL ss
  | [] => by simp [walk, evs, allocDsts]
  | s :: ss => by
    change _ ≤ cntS s + cntL ss
    rw [walk]
    exact (nA_seq _ _).trans (Nat.add_le_add (nA_walk1 s) (nA_walk ss))

theorem nA_arms (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), (allocDsts (evs (walkArms σ x j arms))).length ≤ cntA arms
  | [], _ => by simp [walkArms, evs, allocDsts]
  | a :: as, j => by
    change _ ≤ cntL a + cntA as
    rw [walkArms]
    split_ifs
    · exact (nA_walk a).trans (Nat.le_add_right _ _)
    · exact (nA_arms x as (j + 1)).trans (Nat.le_add_left _ _)
end

/-- **A path allocates at most `cntL` buffers.** -/
theorem allocDsts_le_cnt {body : List Stmt} {es : List Ev} {vs : List V} (h : walk σ body = .ret es vs) :
    (allocDsts es).length ≤ cntL body := by
  have := nA_walk (σ := σ) body
  rw [h] at this
  exact this

end Cnt

end

end LeanVM.Guest.Bridge
