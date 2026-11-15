/-
  LeanVM.Guest.EndExecAHeap

  The advised sizes' track: past each step the frames still pop the stream past the executor's
  `heap_sizes` cursor, and each `allocAdvice` pops its buffer's size (`AdvNext`).
-/

module

public import LeanVM.Guest.EndExecAReady
public import LeanVM.Guest.EndExecYShape

/-!
# The advised sizes along the run

Every `allocAdvice` is a buffer hint before its function's first jump (`Bridge.advChk_all`), so a
frame pops its advised sizes before any call, and at a jump has popped them all.

* `heapArith_alignA : HeapArith alignA`: a step of the tree track (`Bridge.StepOff`) leaves the
  frames popping what they did, less the advised sizes at the step's offset: within the frame the
  offset's (`advBefore_succ`); a phantom pops none; a call's callee pops its subtree's, first its
  own; a loop's tail callee its subtree's; at a return the frame below has popped its own
  (`ChainH`, its resume pc past its first jump).
* `advNext_alignA : AdvNext alignA`: at an `allocAdvice`, the stream past the cursor is the frame's
  own entries past those its hints before it popped (`HeapAt`), whose head is the size of its buffer
  (`slot_at`, `Bridge.bufsOf_idx`).
* `keepY_allocA_of`: each step keeps `YAlloc alignA`, from `SizesAt` and `HeapPops`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

/-! ## The advised hints -/

theorem advChk_alignA (f : String) : advChk (alignA f) = true := by
  unfold alignA
  rcases h : B2C.idxOf f with _ | j
  · simp only [Option.getD_none]
    exact advChk_all 0 (by have : nFns = 1602 := rfl; omega)
  · simp only [Option.getD_some]
    obtain ⟨-, -, -, -, -, -, -, -, -, h2⟩ := B2C.fn_of_idx h
    exact advChk_all j h2

theorem adv_spec {F : FnAl} (h : advChk F = true) {q : ℕ × Hint} (hq : q ∈ allocHints F.d) (ha : isAdv q.2 = true) :
    q.1 < nextJump F.code 0 ∧ isBuf F.X q.2 = true := by
  have := List.all_eq_true.mp h q hq
  simp only [ha, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem isAdv_ptr {h : Hint} (ha : isAdv h = true) : (allocPtr h).isSome = true := by
  cases h <;> simp_all [isAdv, allocPtr]

/-- **The advised sizes at an offset** are those of its hints. -/
theorem adv_at {F : FnAl} (hU : HintsUp F.d F.X.entry) (off : ℕ) :
    (allocHints F.d).countP (fun q ↦ decide (q.1 = off) && isAdv q.2) =
      (hintsAtOff F off).countP isAdv := by
  rw [← List.countP_filter]
  exact countP_at hU (fun _ ↦ isAdv_ptr) off

theorem countP_lt_succ_and (p : Hint → Bool) (l : List (ℕ × Hint)) (off : ℕ) :
    l.countP (fun q ↦ decide (q.1 < off + 1) && p q.2) =
      l.countP (fun q ↦ decide (q.1 < off) && p q.2) + l.countP (fun q ↦ decide (q.1 = off) && p q.2) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    rcases hp : p a.2 with _ | _
    · simp
    · by_cases h1 : a.1 < off
      · simp [h1, show a.1 < off + 1 by omega, show a.1 ≠ off by omega]; omega
      · by_cases h2 : a.1 = off
        · simp [h2]; omega
        · simp [show ¬ a.1 < off + 1 by omega, h1, h2]

/-- **Past an offset, its advised sizes are popped.** -/
theorem advBefore_succ {F : FnAl} (hU : HintsUp F.d F.X.entry) (off : ℕ) :
    advBefore F (off + 1) = advBefore F off + (hintsAtOff F off).countP isAdv := by
  rw [advBefore, advBefore, countP_lt_succ_and, adv_at hU]

theorem advBefore_zero (F : FnAl) : advBefore F 0 = 0 := by simp [advBefore]

theorem advIdx_length : ∀ (k : ℕ) (l : List (ℕ × Hint)), (advIdx k l).length = l.countP fun q ↦ isAdv q.2
  | _, [] => rfl
  | k, q :: l => by
    unfold advIdx
    rw [List.countP_cons]
    split <;> simp_all [advIdx_length (k + 1) l]

/-- The advised sizes of a function are its advised buffer hints'. -/
theorem slotsOf_length {F : FnAl} (h : advChk F = true) :
    (slotsOf F).length = (allocHints F.d).countP fun q ↦ isAdv q.2 := by
  rw [slotsOf, advIdx_length, bufsOf, List.countP_filter]
  apply List.countP_congr
  intro q hq
  cases ha : isAdv q.2
  · simp
  · simp [(adv_spec h hq ha).2]

theorem advBefore_le {F : FnAl} (h : advChk F = true) (off : ℕ) : advBefore F off ≤ (slotsOf F).length := by
  rw [slotsOf_length h, advBefore]
  exact List.countP_mono_left fun q _ hq ↦ by simp only [Bool.and_eq_true] at hq; exact hq.2

/-- **At or past the first jump, every advised size is popped.** -/
theorem advBefore_all {F : FnAl} (h : advChk F = true) {off : ℕ} (hle : nextJump F.code 0 ≤ off) :
    advBefore F off = (slotsOf F).length := by
  rw [slotsOf_length h, advBefore]
  apply List.countP_congr
  intro q hq
  cases ha : isAdv q.2
  · simp
  · have := (adv_spec h hq ha).1
    have h2 : q.1 < off := by omega
    simp [h2]

/-- **At or past the first jump, no hint pops an advised size.** -/
theorem adv_none {F : FnAl} (h : advChk F = true) (hU : HintsUp F.d F.X.entry) {off : ℕ}
    (hle : nextJump F.code 0 ≤ off) : (hintsAtOff F off).countP isAdv = 0 := by
  rw [← adv_at hU, List.countP_eq_zero]
  intro q hq hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  have := (adv_spec h hq hd.2).1
  omega

/-! ## The frames' entries -/

theorem heapPopsKids_drop (sl : String → List ℕ) :
    ∀ (ks : List Tree) (n : ℕ) {k : Tree}, ks[n]? = some k →
      Tree.heapPopsKids sl (ks.drop n) = k.heapPops sl ++ Tree.heapPopsKids sl (ks.drop (n + 1))
  | [], _, _, h => by simp at h
  | k' :: ks, 0, k, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [Tree.heapPopsKids]
  | _ :: ks, n + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.drop_succ_cons]
    exact heapPopsKids_drop sl ks n h

theorem heapPopsKids_past (sl : String → List ℕ) {ks : List Tree} {n : ℕ} (h : ks.length ≤ n) :
    Tree.heapPopsKids sl (ks.drop n) = [] := by
  rw [List.drop_eq_nil_of_le h]; rfl

theorem heapPops_node (sl : String → List ℕ) {t : Tree} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (h : t = .node f σ bufs kids) :
    t.heapPops sl = (sl t.name).map (advEntry t.bufs) ++ Tree.heapPopsKids sl t.kids := by
  subst h; rfl

theorem restH_cons (A : String → FnAl) (e : Ent) (st : List Ent) (off : ℕ) :
    restH A (e :: st) off = ((slotsOf (A e.I.t.name)).map (advEntry e.I.t.bufs)).drop (advBefore (A e.I.t.name) off) ++
      kidsH A e ++ st.flatMap (kidsH A) := rfl

theorem kidsH_congr {A : String → FnAl} {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc) : kidsH A e' = kidsH A e := by
  simp only [kidsH, hI, hnc]

theorem restH_congr {A : String → FnAl} {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc) (st : List Ent) (off : ℕ) :
    restH A (e' :: st) off = restH A (e :: st) off := by
  rw [restH_cons, restH_cons, kidsH_congr hI hnc, hI]

theorem drop3 {α : Type} {x y z : List α} {n : ℕ} (h : n ≤ x.length) : (x ++ y ++ z).drop n = x.drop n ++ y ++ z := by
  rw [List.append_assoc, List.drop_append_of_le_length h, List.append_assoc]

/-- **Popping `a` more advised sizes of the top frame.** -/
theorem restH_more {A : String → FnAl} {e : Ent} {st : List Ent} {off off' a : ℕ}
    (h : advBefore (A e.I.t.name) off' = advBefore (A e.I.t.name) off + a)
    (hle : advBefore (A e.I.t.name) off' ≤ (slotsOf (A e.I.t.name)).length) :
    restH A (e :: st) off' = (restH A (e :: st) off).drop a := by
  rw [restH_cons, restH_cons, drop3 (by rw [List.length_drop, List.length_map]; omega), List.drop_drop, h,
    Nat.add_comm]

theorem chainH_top {A : String → FnAl} {M : ℕ → E} {e e' : Ent} (hI : e'.I = e.I) {st : List Ent}
    (h : ChainH A M (e :: st)) : ChainH A M (e' :: st) := by
  rcases st with _ | ⟨e2, st2⟩
  · trivial
  · simp only [ChainH] at h ⊢; rw [hI]; exact h

theorem chainH_tail {A : String → FnAl} {M : ℕ → E} {e : Ent} {st : List Ent} (h : ChainH A M (e :: st)) :
    ChainH A M st := by
  rcases st with _ | ⟨e2, st2⟩
  · trivial
  · exact h.2


/-! ## The advised size at an `allocAdvice` -/

theorem lookup_at {d : ℕ × ℕ × List (ℕ × List Hint)} {entry off i : ℕ} {h : Hint}
    (hi : (hintsAtD d entry off)[i]? = some h) : d.2.2.lookup (entry + off) = some (hintsAtD d entry off) := by
  unfold hintsAtD at hi ⊢
  cases hlk : d.2.2.lookup (entry + off) with
  | none => rw [hlk] at hi; simp at hi
  | some _ => rfl

theorem filter_take_countP {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : ℕ), (l.filter p).take ((l.take i).countP p) = (l.take i).filter p
  | [], _ => by simp
  | a :: l, 0 => by simp
  | a :: l, i + 1 => by
    simp only [List.take_succ_cons, List.countP_cons, List.filter_cons]
    by_cases hp : p a = true <;> simp [hp, filter_take_countP p l i]

theorem advIdx_get : ∀ (n : ℕ) (l : List (ℕ × Hint)) (k : ℕ) {q : ℕ × Hint}, l[k]? = some q → isAdv q.2 = true →
    (advIdx n l)[(l.take k).countP fun q ↦ isAdv q.2]? = some (n + k)
  | _, [], _, _, h, _ => by simp at h
  | n, q' :: l, 0, q, h, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [advIdx, ha]
  | n, q' :: l, k + 1, q, h, ha => by
    simp only [List.getElem?_cons_succ] at h
    have := advIdx_get (n + 1) l k h ha
    rw [show n + (k + 1) = n + 1 + k by omega, List.take_succ_cons, List.countP_cons]
    by_cases hq : isAdv q'.2
    · rw [show advIdx n (q' :: l) = n :: advIdx (n + 1) l by simp [advIdx, hq]]; simpa [hq] using this
    · rw [show advIdx n (q' :: l) = advIdx (n + 1) l by simp [advIdx, hq]]; simpa [hq] using this

/-- **The advised sizes popped before an `allocAdvice`**: those before its offset and before it at
its offset, the advised buffer hints before its buffer's. -/
theorem adv_count {F : FnAl} (hU : HintsUp F.d F.X.entry) (hA : advChk F = true) {off i : ℕ} {h : Hint}
    (hi : (hintsAtOff F off)[i]? = some h) :
    ((bufsOf F.X F.d).take (nbAt F.X F.d off + ((hintsAtOff F off).take i).countP (isBuf F.X))).countP
        (fun q ↦ isAdv q.2) = advBefore F off + ((hintsAtOff F off).take i).countP isAdv := by
  obtain ⟨P, S, he, hP, hS⟩ := hintsOff_split hU (lookup_at hi)
  have hab : ∀ q ∈ hintsOff F.d, isAdv q.2 = true → isBuf F.X q.2 = true := fun q hq ha ↦
    (adv_spec hA (List.mem_filter.mpr ⟨hq, isAdv_ptr ha⟩) ha).2
  set hs := hintsAtD F.d F.X.entry off
  have hnb : nbAt F.X F.d off = (P.filter fun q ↦ isBuf F.X q.2).length := by
    rw [nbAt_eq, bufsOf_eq, he, List.filter_append, List.filter_append, List.countP_append, List.countP_append]
    have h1 : (P.filter fun q ↦ isBuf F.X q.2).countP (fun q ↦ decide (q.1 < off)) =
        (P.filter fun q ↦ isBuf F.X q.2).length :=
      List.countP_eq_length.mpr fun q hq ↦ by simpa using hP q (List.mem_filter.mp hq).1
    have h2 : ((hs.map fun h ↦ (off, h)).filter fun q ↦ isBuf F.X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        obtain ⟨h', -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1
        simp
    have h3 : (S.filter fun q ↦ isBuf F.X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        have := hS q (List.mem_filter.mp hq).1
        simp only [decide_eq_true_eq]
        omega
    rw [h1, h2, h3]; rfl
  have hc : (hs.take i).countP (isBuf F.X) = ((hs.map fun h ↦ (off, h)).take i).countP (fun q ↦ isBuf F.X q.2) := by
    rw [← List.map_take, List.countP_map]; rfl
  set hsm := hs.map fun h ↦ (off, h) with hhsm
  have hmemP : ∀ q ∈ P, q ∈ hintsOff F.d := fun q hq ↦ by rw [he]; simp [hq]
  have hmemH : ∀ q ∈ hsm, q ∈ hintsOff F.d := fun q hq ↦ by rw [he]; simp [hq]
  have hbufs : bufsOf F.X F.d = P.filter (fun q ↦ isBuf F.X q.2) ++ (hsm.filter (fun q ↦ isBuf F.X q.2) ++
      S.filter (fun q ↦ isBuf F.X q.2)) := by
    rw [bufsOf_eq, he, List.filter_append, List.filter_append, List.append_assoc]
  have hcle : (hsm.take i).countP (fun q ↦ isBuf F.X q.2) ≤ (hsm.filter (fun q ↦ isBuf F.X q.2)).length := by
    rw [← List.countP_eq_length_filter]
    exact (List.take_sublist i hsm).countP_le
  have htake : (bufsOf F.X F.d).take ((P.filter fun q ↦ isBuf F.X q.2).length + (hsm.take i).countP (fun q ↦ isBuf F.X q.2)) =
      P.filter (fun q ↦ isBuf F.X q.2) ++ (hsm.take i).filter (fun q ↦ isBuf F.X q.2) := by
    rw [hbufs, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      List.take_append, show (hsm.take i).countP (fun q ↦ isBuf F.X q.2) -
        (hsm.filter (fun q ↦ isBuf F.X q.2)).length = 0 by omega, List.take_zero, List.append_nil, filter_take_countP]
  rw [hintsAtOff_eq, hnb, hc, htake, List.countP_append, List.countP_filter, List.countP_filter]
  have e1 : P.countP (fun q ↦ isAdv q.2 && isBuf F.X q.2) = P.countP (fun q ↦ isAdv q.2) :=
    List.countP_congr fun q hq ↦ by
      cases ha : isAdv q.2
      · simp
      · simp [hab q (hmemP q hq) ha]
  have e2 : (hsm.take i).countP (fun q ↦ isAdv q.2 && isBuf F.X q.2) = (hs.take i).countP isAdv := by
    rw [hhsm, ← List.map_take, List.countP_map]
    apply List.countP_congr
    intro x hx
    have hxm : (off, x) ∈ hsm := List.mem_map.mpr ⟨x, List.mem_of_mem_take hx, rfl⟩
    cases ha : isAdv x
    · simp [Function.comp, ha]
    · simp [Function.comp, ha, hab _ (hmemH _ hxm) ha]
  have e3 : advBefore F off = P.countP (fun q ↦ isAdv q.2) := by
    rw [advBefore, allocHints, List.countP_filter, he, List.countP_append, List.countP_append]
    have h1 : P.countP (fun q ↦ (decide (q.1 < off) && isAdv q.2) && (allocPtr q.2).isSome) = P.countP (fun q ↦ isAdv q.2) :=
      List.countP_congr fun q hq ↦ by
        have := hP q hq
        cases ha : isAdv q.2
        · simp
        · simp [this, isAdv_ptr ha]
    have h2 : hsm.countP (fun q ↦ (decide (q.1 < off) && isAdv q.2) && (allocPtr q.2).isSome) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        obtain ⟨h', -, rfl⟩ := List.mem_map.mp hq
        simp
    have h3 : S.countP (fun q ↦ (decide (q.1 < off) && isAdv q.2) && (allocPtr q.2).isSome) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        have := hS q hq
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro h; omega
    rw [h1, h2, h3]; rfl
  rw [e1, e2, e3]

/-- **An `allocAdvice` pops its buffer's size**: the stream past the cursor is its frame's own
entries past those the hints before it popped, the next one its buffer's. -/
theorem advNext_alignA : AdvNext alignA := by
  intro r C e s sx i p S hat
  obtain ⟨hr, hC, ⟨done, st, htr, -, hha, -⟩, -, -, -, hget, hpre, -⟩ := hat
  obtain ⟨off, hpcE, hhs⟩ := hint_off hC htr hget
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  have hE := htr.track.ents e List.mem_cons_self
  have hU := hintsUp_frame hE.find
  have hA := advChk_alignA e.I.t.name
  have hS : S = Hints.heapSizeStream := by
    have := hints_adv hC rfl s.pc _ (List.mem_of_getElem? hget)
    simpa [advHintOk] using this
  subst hS
  have hcur : sx.cursor.getD Hints.heapSizeStream 0 = s.cursor.getD Hints.heapSizeStream 0 +
      (((C.hints[s.pc]?).getD []).take i).countP isAdv := by
    rw [hints_cursor _ _ s sx hpre,
      filter_heap fun x hx ↦ hints_heap hC rfl s.pc x (List.mem_of_mem_take hx)]
  rw [hhs] at hget hcur
  have hi : (hintsAtOff (alignA e.I.t.name) off)[i]? = some (.allocAdvice p Hints.heapSizeStream) := hget
  have hb : isBuf (alignA e.I.t.name).X (.allocAdvice p Hints.heapSizeStream) = true := by
    obtain ⟨P, S', he, -, -⟩ := hintsOff_split hU (lookup_at hi)
    have hm : (off, Hint.allocAdvice p Hints.heapSizeStream) ∈ hintsOff (alignA e.I.t.name).d := by
      rw [he]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, List.mem_of_getElem? hi, rfl⟩))
    exact (adv_spec hA (List.mem_filter.mpr ⟨hm, rfl⟩) rfl).2
  have hslot := advIdx_get 0 _ _ (bufsOf_idx hU hi hb) rfl
  rw [← hintsAtOff_eq, adv_count hU hA hi, Nat.zero_add] at hslot
  have hown : ((slotsOf (alignA e.I.t.name)).map (advEntry e.I.t.bufs))[advBefore (alignA e.I.t.name) off +
      ((hintsAtOff (alignA e.I.t.name) off).take i).countP isAdv]? = some (advEntry e.I.t.bufs (bufIdx alignA e off i)) := by
    rw [List.getElem?_map, slotsOf, hslot]; rfl
  have hlt := (List.getElem?_eq_some_iff.mp hown).1
  have hdrop := hha
  rw [hoff, restH_cons] at hdrop
  have hget2 : (heapStream r)[sx.cursor.getD Hints.heapSizeStream 0]? = some (advEntry e.I.t.bufs (bufIdx alignA e off i)) := by
    rw [hcur, ← List.getElem?_drop, hdrop, List.append_assoc, List.getElem?_append_left (by rw [List.length_drop]; omega),
      List.getElem?_drop, hown]
  have hex : ∃ q ∈ Hints.honestPushes bytecodeShape r.seed r.s r.w, q.1 = Hints.heapSizeStream := by
    obtain ⟨q, hq, -⟩ := List.mem_map.mp (List.mem_of_getElem? hget2)
    rw [List.mem_filter, pushShape] at hq
    exact ⟨q, hq.1, by simpa using hq.2⟩
  refine ⟨_, streams_guest hC hex, ?_⟩
  rw [List.getElem?_toArray, ← pushShape, hoff]
  rw [heapStream] at hget2
  rw [hget2]
  unfold advEntry
  cases e.I.t.bufs[bufIdx alignA e off i]? <;> rfl

/-! ## The step -/

section

variable {r : Ref}

/-- **The advised sizes follow each step of the tree track.** -/
theorem heapArith_alignA : HeapArith alignA := by
  intro r hr pc fp done e st off pc' fp' st'' done' htr hpc hk hts hch
  have hE := htr.track.ents e List.mem_cons_self
  have hU : HintsUp (alignA e.I.t.name).d (alignA e.I.t.name).X.entry := hintsUp_frame hE.find
  have hA := advChk_alignA e.I.t.name
  have hkl : (calls (e.pre ++ e.es)).length = e.I.t.kids.length := by
    obtain ⟨rv, hkv⟩ := hE.kids; exact kidsValid_len hkv
  -- at a jump, every advised size of the frame popped, none at the offset
  have hjmp : ∀ {oc od of}, (alignA e.I.t.name).code[off]? = some (.jump oc od of) →
      nextJump (alignA e.I.t.name).code 0 ≤ off := fun h ↦ nextJump_le h rfl (Nat.zero_le _)
  have hall : ∀ {oc od of}, (alignA e.I.t.name).code[off]? = some (.jump oc od of) → ∀ o, off ≤ o →
      restH alignA (e :: st) o = (restH alignA (e :: st) off).drop ((hintsAtOff (alignA e.I.t.name) off).countP isAdv) :=
    fun h o ho ↦ by
      rw [adv_none hA hU (hjmp h), List.drop_zero, restH_cons, restH_cons, advBefore_all hA (hjmp h),
        advBefore_all hA (le_trans (hjmp h) ho)]
  -- the frame's own entries all popped
  have hown : ∀ {oc od of}, (alignA e.I.t.name).code[off]? = some (.jump oc od of) →
      restH alignA (e :: st) off = kidsH alignA e ++ st.flatMap (kidsH alignA) := fun h ↦ by
    rw [restH_cons, advBefore_all hA (hjmp h), List.drop_eq_nil_of_le (by rw [List.length_map]), List.nil_append]
  have hnz : ∀ {oc od of}, (alignA e.I.t.name).code[off]? = some (.jump oc od of) →
      (hintsAtOff (alignA e.I.t.name) off).countP isAdv = 0 := fun h ↦ adv_none hA hU (hjmp h)
  cases hk with
  | @fall e' ins hI' hnc' hins hjk =>
    refine ⟨chainH_top hI' hch, ?_⟩
    rw [restH_congr hI' hnc', hI', show entOf alignA e.I.t.name + off + 1 - entOf alignA e.I.t.name = off + 1 by omega]
    exact restH_more (advBefore_succ hU off) (advBefore_le hA _)
  | @fwd e' oc od of t hI' hnc' hins hz0 hself htgt hlt =>
    refine ⟨chainH_top hI' hch, ?_⟩
    rw [restH_congr hI' hnc', hI']
    exact hall hins _ (by omega)
  | @skip e' oc od of c f σ' hI' hnc' hins hc hkp hwhy =>
    refine ⟨chainH_top hI' hch, ?_⟩
    have hkE : kidsH alignA e = kidsH alignA e' := by
      rw [kidsH, kidsH, hI', hnc', heapPopsKids_drop _ _ _ hkp]
      rfl
    rw [hI', show entOf alignA e.I.t.name + off + 1 - entOf alignA e.I.t.name = off + 1 by omega, hnz hins,
      List.drop_zero, restH_cons, restH_cons, hI', advBefore_all hA (by have := hjmp hins; omega),
      advBefore_all hA (hjmp hins), hkE]
  | @push e' J fn oc od of c s hI' hnc' hins hc hsite hsr hat hJ hkJ hkf hfind hhdr =>
    have hE' : EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) e' :=
      hts.track.ents e' (List.mem_cons_of_mem _ List.mem_cons_self)
    have hEJ := hts.track.ents _ List.mem_cons_self
    have hsr63 : s.r < 2 ^ 63 := by
      have := (entry_of_atPc progAl alLayout_alignA hE' hat).1
      rw [guest_logSize] at this
      omega
    have hentI : entOf alignA e'.I.t.name = entOf alignA e.I.t.name := by rw [hI']
    refine ⟨⟨⟨s.r, hhdr, hsr63, ?_⟩, chainH_top hI' hch⟩, ?_⟩
    · rw [hentI, hI']; have := hjmp hins; omega
    · obtain ⟨f, bufs, kids, hJt⟩ := hEJ.node
      change restH alignA (Ent.enter coreProgram J fn :: e' :: st) (entOf alignA J.t.name - entOf alignA J.t.name) = _
      have hkE : kidsH alignA e = J.t.heapPops (fun f ↦ slotsOf (alignA f)) ++ kidsH alignA e' := by
        rw [kidsH, kidsH, hI', hnc', heapPopsKids_drop _ _ _ hkJ]
      have hkJ' : kidsH alignA (Ent.enter coreProgram J fn) = Tree.heapPopsKids (fun f ↦ slotsOf (alignA f)) J.t.kids := by
        simp [kidsH, Ent.enter, Ent.nc, calls]
      rw [Nat.sub_self, hnz hins, List.drop_zero, hown hins, restH_cons, advBefore_zero, List.drop_zero, hkJ', hkE,
        heapPops_node _ (t := J.t) hJt]
      simp only [Ent.enter, List.flatMap_cons, List.append_assoc]
  | @tail J fn oc od of hins hz0 hnext hlen hJ hkJ hkf hfind hhdr =>
    have hEJ := hts.track.ents _ List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rcases st with _ | ⟨e2, st2⟩
      · trivial
      · obtain ⟨⟨r0, hr0, h2⟩, hrest⟩ := hch
        exact ⟨⟨r0, by rw [← hr0]; exact hhdr, h2⟩, hrest⟩
    · obtain ⟨f, bufs, kids, hJt⟩ := hEJ.node
      change restH alignA (Ent.enter coreProgram J fn :: st) (entOf alignA J.t.name - entOf alignA J.t.name) = _
      have hkE : kidsH alignA e = J.t.heapPops (fun f ↦ slotsOf (alignA f)) := by
        rw [kidsH, heapPopsKids_drop _ _ _ hkJ, heapPopsKids_past _ (show e.I.t.kids.length ≤ e.nc + 1 by omega),
          List.append_nil]
      have hkJ' : kidsH alignA (Ent.enter coreProgram J fn) = Tree.heapPopsKids (fun f ↦ slotsOf (alignA f)) J.t.kids := by
        simp [kidsH, Ent.enter, Ent.nc, calls]
      rw [Nat.sub_self, hnz hins, List.drop_zero, hown hins, restH_cons, advBefore_zero, List.drop_zero, hkJ', hkE,
        heapPops_node _ (t := J.t) hJt]
      simp only [Ent.enter, List.append_assoc]
  | @ret e2 st2 oc _ hins hz0 hmain hst hlen hhdr =>
    subst hst
    obtain ⟨⟨r1, hr1, hr1lt, hle⟩, hrest⟩ := hch
    have hE2 : EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) e2 :=
      hts.track.ents e2 List.mem_cons_self
    have hr0lt : pc' < 2 ^ 63 := by
      have := (entry_of_atPc progAl alLayout_alignA hE2 hts.linked.top.2).1
      rw [guest_logSize] at this
      omega
    have hr10 : r1 = pc' := by
      have h := ofK_injective (hr1.symm.trans hhdr)
      exact gpow_inj (by omega) (by omega) h
    subst hr10
    refine ⟨hrest, ?_⟩
    rw [hnz hins, List.drop_zero, hown hins, kidsH, heapPopsKids_past _ (by omega), List.nil_append, List.flatMap_cons,
      restH_cons, advBefore_all (advChk_alignA _) hle, List.drop_eq_nil_of_le (by rw [List.length_map]), List.nil_append]

end

end

public section

/-- **Each step keeps `YAlloc alignA`**, from `SizesAt` and the advised sizes' stream the tree's. -/
theorem keepY_allocA_of (hS : SizesAt alignA) (hHP : HeapPops) : KeepY (YAlloc alignA) :=
  keepY_allocA hS curArith_alignA heapArith_alignA fun r hr ↦ hHP r hr

end

end LeanVM.Guest.EndExec
