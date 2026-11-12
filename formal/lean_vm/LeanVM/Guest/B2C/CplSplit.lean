/-
  LeanVM.Guest.B2C.CplSplit

  A completeness window that is one `match` of straight-line arms, checked by groups of its arms,
  each group in its own kernel evaluation over the cells of its own values.
-/

module

public import LeanVM.Guest.B2C.Cpl
public import LeanVM.Guest.B2C.CplSpec
public import LeanVM.Guest.B2C.CplSem
public import LeanVM.Guest.B2C.ShareSplit

/-!
# Completeness windows split by arms

The completeness walk of a window of one `match` of many straight-line arms (`Check.checkWinS`
splits its soundness window) walks every arm from the table jump to its end, the join or, the
`match` chained, the next one's table jump, and keeps the most instructions of each opcode any arm
passes. A group (`cplWinS`) walks arm `0` and the arms `lo ≤ k < hi` over the cells of its own
values and the next selector (`clocG`), from the table jump (`cwMatchS`, `cw`'s) or, the window
entered, from its arms (`cwES`, `cwE`'s), and checks that its most counts are within what the
next window starts with; the groups together give the window's check (`cplWin_of_split`): an
arm's walk files its atoms over the group's cells, which are the window's (`clocG_get`), and
otherwise reads no cell (`cw_atoms_loc`), and the window's counts are the most of the groups'
(`cwArms_of_groups`, which `cw_of_groups` and `cwE_of_groups` share).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Walks of atoms read no cell -/

theorem justI_loc (X : CX) (L : CLoc) (st : CW) (pc : ℕ) (ins : OffsetInstruction) :
    justI { X with loc := L } st pc ins = justI X st pc ins := rfl

theorem cellK_loc (X : CX) (L : CLoc) (st : CW) (o : ℕ) : cellK { X with loc := L } st o = cellK X st o :=
  rfl

theorem passL_loc (X : CX) (L : CLoc) (st : CW) : ∀ (its : List Exec.Item) (c : Cnt),
    passL { X with loc := L } st its c = passL X st its c
  | [], _ => rfl
  | .ins (.instr pc ins) :: its, c => by
    simp only [passL, justI_loc, Cnt.seq_eq, passL_loc X L st its]
  | .ins (.jump oc od of) :: its, c => by
    simp only [passL, cellK_loc, Cnt.seq_eq, passL_loc X L st its]
  | .ins (.copy ..) :: _, _ => rfl
  | .ins (.eq ..) :: _, _ => rfl
  | .ins (.nz ..) :: _, _ => rfl
  | .ins (.ne ..) :: _, _ => rfl
  | .ins (.bool ..) :: _, _ => rfl
  | .ins (.range ..) :: _, _ => rfl
  | .ins (.powPair ..) :: _, _ => rfl
  | .fact _ :: its, c => by simp only [passL, passL_loc X L st its]
  | .branch .. :: _, _ => rfl

theorem endAtC_loc (X : CX) (L : CLoc) (st : CW) : endAtC { X with loc := L } st = endAtC X st := by
  unfold endAtC; rw [passL_loc]

theorem chainEnd_loc (X : CX) (L : CLoc) (se : CW) (t : ℕ) (ft : Tgt) :
    chainEnd { X with loc := L } se t ft = chainEnd X se t ft := rfl

theorem endC_loc (X : CX) (L : CLoc) (st : CW) : endC { X with loc := L } st = endC X st := by
  unfold endC
  simp only [passL_loc, endAtC_loc, chainEnd_loc]

/-- **An atom block's walk reads no cell**: only its filed atoms do. -/
theorem cw_atoms_loc (X : CX) (L : CLoc) : ∀ (ss : List Core.Stmt) (st : CW), ss.all isAtomS = true →
    cw { X with loc := L } ss st = cw X ss st
  | [], st, _ => by simp only [cw]; exact endC_loc X L st
  | .atom a :: ss, st, hs => by
    simp only [List.all_cons, isAtomS, Bool.true_and] at hs
    simp only [cw, natSeq_eq]
    exact cw_atoms_loc X L ss _ hs
  | .ite .. :: _, _, hs => by simp [isAtomS] at hs
  | .match_ .. :: _, _, hs => by simp [isAtomS] at hs
  | .call .. :: _, _, hs => by simp [isAtomS] at hs
  | .callIf .. :: _, _, hs => by simp [isAtomS] at hs
  | .dispatch .. :: _, _, hs => by simp [isAtomS] at hs
  | .ret .. :: _, _, hs => by simp [isAtomS] at hs

/-! ## Filing on agreeing cells -/

section Congr

variable {L L' : CLoc} {A : ℕ → Prop} (hA : ∀ n, A n → L.get? n = L'.get? n)
include hA

theorem ccell_congr {v : V} (h : A v.idx) : L.cell v = L'.cell v := by
  unfold CLoc.cell; rw [hA _ h]

theorem locC_congr {a : Core.Atom} (h : ∀ w ∈ atomVals a, A w.idx) : locC L a = locC L' a := by
  cases a <;> simp only [atomVals, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [locC]
  all_goals first
    | (rw [ccell_congr hA h])
    | (rw [ccell_congr hA h.1, ccell_congr hA h.2])
    | (rw [ccell_congr hA h.1, ccell_congr hA h.2.1, ccell_congr hA h.2.2])
    | (rw [ccell_congr hA h.1, ccell_congr hA h.2.1, ccell_congr hA h.2.2.1, ccell_congr hA h.2.2.2.1,
        ccell_congr hA h.2.2.2.2])
    | (rw [List.map_congr_left fun v hv ↦ ccell_congr hA (h v (Or.inl hv)),
        List.map_congr_left fun v hv ↦ ccell_congr hA (h v (Or.inr hv))])
    | (rename_i run; cases run with
        | nil => rfl
        | cons r rs =>
          simp only [List.mem_cons, forall_eq_or_imp] at h
          show LAtom.addr (L.cell _) ((r :: rs).map L.cell) = LAtom.addr (L'.cell _) ((r :: rs).map L'.cell)
          rw [ccell_congr hA h.1, List.map_congr_left fun v hv ↦ ccell_congr hA (by
            rcases List.mem_cons.mp hv with rfl | hv
            · exact h.2.1
            · exact h.2.2 _ hv)])

theorem fileB_congr (n : ℕ) : ∀ (ss : List Core.Stmt) (B : BookC),
    (∀ v ∈ stmtsVals ss, A v.idx) → fileB L n ss B = fileB L' n ss B
  | [], _, _ => rfl
  | .atom a :: ss, B, h => by
    simp only [fileB, LAtom.seq_eq]
    rw [locC_congr hA fun w hw ↦ h w (by
      simp only [stmtsVals, stmtVals, List.mem_append]; exact Or.inl hw)]
    have hs : ∀ v ∈ stmtsVals ss, A v.idx := fun v hv ↦ h v (by
      simp only [stmtsVals, List.mem_append]; exact Or.inr hv)
    cases inFrame n (cellsC (locC L' a))
    · simp only [Bool.cond_false]; exact fileB_congr n ss _ hs
    · simp only [Bool.cond_true, Exec.Trie.seq_eq]; exact fileB_congr n ss _ hs
  | .ite .. :: ss, B, h => by
    simp only [fileB]; exact fileB_congr n ss B fun v hv ↦ h v (by
      simp only [stmtsVals, List.mem_append]; exact Or.inr hv)
  | .match_ .. :: ss, B, h => by
    simp only [fileB]; exact fileB_congr n ss B fun v hv ↦ h v (by
      simp only [stmtsVals, List.mem_append]; exact Or.inr hv)
  | .call .. :: ss, B, h => by
    simp only [fileB]; exact fileB_congr n ss B fun v hv ↦ h v (by
      simp only [stmtsVals, List.mem_append]; exact Or.inr hv)
  | .callIf .. :: ss, B, h => by
    simp only [fileB]; exact fileB_congr n ss B fun v hv ↦ h v (by
      simp only [stmtsVals, List.mem_append]; exact Or.inr hv)
  | .dispatch .. :: ss, B, h => by
    simp only [fileB]; exact fileB_congr n ss B fun v hv ↦ h v (by
      simp only [stmtsVals, List.mem_append]; exact Or.inr hv)
  | .ret .. :: ss, B, h => by
    simp only [fileB]; exact fileB_congr n ss B fun v hv ↦ h v (by
      simp only [stmtsVals, List.mem_append]; exact Or.inr hv)

end Congr

/-! ## A group's cells -/

/-- A group's cells in window `i`: the window's of the values `lo + gm` on (`gn` of them) packed, those
of arm `0`'s values `lo + am` on (`an`) and of the values named outside the window listed. -/
noncomputable def clocG (C : Cert) (i gm gn am an : ℕ) : CLoc :=
  ⟨listElementOrDefault C.los i 0 + gm, (((listElementOrDefault C.cells i []).drop gm).take
      gn).length,
    packC (((listElementOrDefault C.cells i []).drop gm).take gn),
    listElementOrDefault C.ins i [] ++ ((((listElementOrDefault C.cells i []).drop am).take
        an).zipIdx).map fun p ↦
      (listElementOrDefault C.los i 0 + am + p.2, p.1, 0)⟩

theorem insC_append (v : ℕ) : ∀ (l₁ l₂ : List (ℕ × ℕ × ℕ)),
    insC v (l₁ ++ l₂) = match insC v l₁ with
      | some c => some c
      | none => insC v l₂
  | [], _ => rfl
  | p :: l₁, l₂ => by
    simp only [List.cons_append, insC]
    cases Nat.beq p.1 v
    · exact insC_append v l₁ l₂
    · rfl

theorem insC_some {v c : ℕ} : ∀ {l : List (ℕ × ℕ × ℕ)}, insC v l = some c → ∃ p ∈ l, p.1 = v ∧ p.2.1 = c
  | [], h => by simp [insC] at h
  | p :: l, h => by
    simp only [insC, Bool.cond_eq_ite, Nat.beq_eq] at h
    split_ifs at h with hp
    · exact ⟨p, List.mem_cons_self, hp, (Option.some.inj h)⟩
    · obtain ⟨q, hq, h1, h2⟩ := insC_some h
      exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- What a completeness window split by arms checks once: its cells below `2^16`, the values it
names outside it below it. -/
def cplFits (C : Cert) (i : ℕ) : Bool :=
  (listElementOrDefault C.cells i []).all (fun c ↦ Nat.blt c 65536) &&
    (listElementOrDefault C.ins i []).all fun p ↦ Nat.blt p.1 (listElementOrDefault C.los i 0)

theorem clocG_get {C : Cert} {i gm gn am an : ℕ} (hf : cplFits C i = true) {v c : ℕ}
    (h : (clocG C i gm gn am an).get? v = some c) : (clocW C i).get? v = some c := by
  simp only [cplFits, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hf
  obtain ⟨hc, hins⟩ := hf
  set cells := listElementOrDefault C.cells i []
  set lo := listElementOrDefault C.los i 0
  have hwin : ∀ (hm : v - lo < cells.length), lo ≤ v → (clocW C i).get? v = some cells[v - lo] := by
    intro hm hv
    have hcond : (Nat.ble lo v && Nat.blt v (Nat.add lo cells.length)) = true := by
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
      exact ⟨hv, by show v < lo + cells.length; omega⟩
    show (bif Nat.ble lo v && Nat.blt v (Nat.add lo cells.length) then
      some (Nat.mod (Nat.div (packC cells) (Nat.pow 65536 (Nat.sub v lo))) 65536)
      else insC v (listElementOrDefault C.ins i [])) = _
    rw [hcond, Bool.cond_true]
    exact congrArg some (packC_digit cells hc _ hm)
  have hg : (clocG C i gm gn am an).get? v =
      (bif Nat.ble (lo + gm) v && Nat.blt v (Nat.add (lo + gm) ((cells.drop gm).take gn).length) then
        some (Nat.mod (Nat.div (packC ((cells.drop gm).take gn)) (Nat.pow 65536 (Nat.sub v (lo + gm)))) 65536)
      else insC v (listElementOrDefault C.ins i [] ++ (((cells.drop am).take an).zipIdx).map fun p ↦
        (lo + am + p.2, p.1, 0))) := rfl
  rw [hg] at h
  cases hr : (Nat.ble (lo + gm) v && Nat.blt v (Nat.add (lo + gm) ((cells.drop gm).take gn).length))
  · rw [hr, Bool.cond_false, insC_append] at h
    split at h
    · rename_i c' hc'
      obtain ⟨p, hp, rfl, -⟩ := insC_some hc'
      have hplo := hins p hp
      have hcond : (Nat.ble lo p.1 && Nat.blt p.1 (Nat.add lo cells.length)) = false := by
        have : Nat.ble lo p.1 = false := by
          rw [Bool.eq_false_iff]; intro h'; rw [Nat.ble_eq] at h'; omega
        rw [this, Bool.false_and]
      show (bif Nat.ble lo p.1 && Nat.blt p.1 (Nat.add lo cells.length) then
        some (Nat.mod (Nat.div (packC cells) (Nat.pow 65536 (Nat.sub p.1 lo))) 65536)
        else insC p.1 (listElementOrDefault C.ins i [])) = _
      rw [hcond, Bool.cond_false, hc']
      exact h
    · obtain ⟨p, hp, hv, hpc⟩ := insC_some h
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simp only at hv hpc
      obtain ⟨hq1, hq2⟩ := List.mem_zipIdx_iff_getElem?.mp hq |> fun h' ↦
        (⟨(List.getElem?_eq_some_iff.mp h').1, (List.getElem?_eq_some_iff.mp h').2⟩ :
          ∃ hh : q.2 < ((cells.drop am).take an).length, ((cells.drop am).take an)[q.2] = q.1)
      simp only [List.length_take, List.length_drop] at hq1
      simp only [List.getElem_take, List.getElem_drop] at hq2
      subst hv hpc
      rw [hwin (by rw [show lo + am + q.2 - lo = am + q.2 by omega]; omega) (by omega)]
      congr 1
      rw [← hq2]
      congr 1
      omega
  · rw [hr, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hr
    obtain ⟨h1, h2⟩ := hr
    have h2' : v < lo + gm + ((cells.drop gm).take gn).length := h2
    have hm : v - (lo + gm) < ((cells.drop gm).take gn).length := by omega
    have hdg := packC_digit _ (fun c' hc' ↦ hc c' (List.mem_of_mem_drop (List.mem_of_mem_take hc'))) _ hm
    simp only [List.length_take, List.length_drop] at h2'
    have e : ((cells.drop gm).take gn)[v - (lo + gm)] = cells[v - lo]'(by omega) := by
      simp only [List.getElem_take, List.getElem_drop]
      congr 1; omega
    have hs : Nat.sub v (lo + gm) = v - (lo + gm) := rfl
    rw [hs, hdg, e] at h
    rw [hwin (by omega) (by omega)]
    exact h

/-! ## The arms of a group -/

section Arms

variable (X : CX)

/-- One arm of the `match` on `v` walked from its segment, ending as `armEnd J succ` says: its
counts and set-up cells. -/
noncomputable def armStep (J : ℕ) (succ : List ℕ) (se : CW) (key : Option (List Cnt)) (v : V)
    (a : List Core.Stmt) (t k : ℕ) : Option (Cnt × ℕ) :=
  match segAtC X t se with
  | some s => match armEnd J succ
      (cw X a { s with book := fileB X.loc X.fs a se.book, tg := armTg X v k ++ s.tg }) with
    | some (c', u') => bif armChkK key k c' then some (c', u') else none
    | none => none
  | none => none

theorem cwArms_cons (J : ℕ) (succ : List ℕ) (se : CW) (key : Option (List Cnt)) (v : V) (a : List Core.Stmt)
    (as : List (List Core.Stmt)) (t : ℕ) (ts : List ℕ) (c : Cnt) (u k : ℕ) :
    cwArms X J succ v se key (a :: as) (t :: ts) c u k =
      match armStep X J succ se key v a t k with
      | some (c', u') => cwArms X J succ v se key as ts (Cnt.max c c') (Nat.lor u u') (k + 1)
      | none => none := by
  simp only [cwArms, armStep]
  cases hs : segAtC X t se with
  | none => rfl
  | some s =>
    simp only [Exec.Trie.seq_eq]
    cases hc : armEnd J succ
      (cw X a { s with book := fileB X.loc X.fs a se.book, tg := armTg X v k ++ s.tg }) with
    | none => rfl
    | some r =>
      obtain ⟨c', u'⟩ := r
      dsimp only
      cases hb : armChkK key k c' <;>
        simp only [Bool.cond_true, Bool.cond_false, Cnt.seq_eq, natSeq_eq]

/-- The arms `lo ≤ k < hi` of a `match` (from index `k`) walked, the others skipped: the most
counts. -/
noncomputable def cwArmsS (J : ℕ) (succ : List ℕ) (se : CW) (key : Option (List Cnt)) (v : V)
    (lo hi : ℕ) : List (List Core.Stmt) → List ℕ → Cnt → ℕ → ℕ → Option (Cnt × ℕ)
  | [], [], c, u, _ => some (c, u)
  | a :: as, t :: ts, c, u, k =>
    bif Nat.ble lo k && Nat.blt k hi then
      (match armStep X J succ se key v a t k with
        | some (c', u') => cwArmsS J succ se key v lo hi as ts (Cnt.max c c') (Nat.lor u u') (k + 1)
        | none => none)
    else cwArmsS J succ se key v lo hi as ts c u (k + 1)
  | _, _, _, _, _ => none

end Arms

/-! ### Counts within bounds -/

/-- Counts and set-up cells within `B` and `U`. -/
def Good (B : Cnt) (U : ℕ) (r : Cnt × ℕ) : Prop := r.1.le B = true ∧ subK r.2 U = true

theorem le_max_iff (c c' B : Cnt) : (Cnt.max c c').le B = true ↔ c.le B = true ∧ c'.le B = true := by
  simp only [Cnt.le, Cnt.max, Bool.and_eq_true, Nat.ble_eq, Nat.max_def]
  split_ifs <;> omega

theorem subK_lor_iff (u u' U : ℕ) : subK (Nat.lor u u') U = true ↔ subK u U = true ∧ subK u' U = true := by
  simp only [subK, land_beq_iff, testBit_lor', Bool.or_eq_true]
  constructor
  · intro h; exact ⟨fun i hi ↦ h i (Or.inl hi), fun i hi ↦ h i (Or.inr hi)⟩
  · rintro ⟨h1, h2⟩ i (hi | hi)
    · exact h1 i hi
    · exact h2 i hi

theorem good_max {B : Cnt} {U : ℕ} {c c' : Cnt} {u u' : ℕ} :
    Good B U (Cnt.max c c', Nat.lor u u') ↔ Good B U (c, u) ∧ Good B U (c', u') := by
  simp only [Good, le_max_iff, subK_lor_iff]
  tauto

/-- A property of counts and set-up cells that holds of two's most iff of each. -/
def MaxClosed (P : Cnt × ℕ → Prop) : Prop :=
  ∀ c c' u u', P (Cnt.max c c', Nat.lor u u') ↔ P (c, u) ∧ P (c', u')

theorem maxClosed_good (B : Cnt) (U : ℕ) : MaxClosed (Good B U) := fun _ _ _ _ ↦ good_max

theorem maxClosed_subK (U : ℕ) : MaxClosed fun r ↦ subK r.2 U = true :=
  fun _ _ u u' ↦ subK_lor_iff u u' U

theorem cwArms_good (X : CX) (J : ℕ) (succ : List ℕ) (se : CW) (key : Option (List Cnt)) (v : V)
    {P : Cnt × ℕ → Prop} (hP : MaxClosed P) :
    ∀ (as : List (List Core.Stmt)) (ts : List ℕ) (c : Cnt) (u k : ℕ), ts.length = as.length →
      P (c, u) → (∀ e (he : e < as.length) (ht : e < ts.length), ∃ r,
        armStep X J succ se key v as[e] ts[e] (k + e) = some r ∧ P r) →
      ∃ r, cwArms X J succ v se key as ts c u k = some r ∧ P r
  | [], [], c, u, _, _, hg, _ => ⟨(c, u), by simp [cwArms], hg⟩
  | [], _ :: _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | a :: as, t :: ts, c, u, k, hl, hg, h => by
    obtain ⟨⟨c', u'⟩, hs, hg'⟩ := h 0 (by simp) (by simp)
    rw [cwArms_cons, show armStep X J succ se key v a t k = some (c', u') by simpa using hs]
    exact cwArms_good X J succ se key v hP as ts _ _ (k + 1) (by simpa using hl) ((hP _ _ _ _).mpr ⟨hg, hg'⟩)
      fun e he ht ↦ by
        have := h (e + 1) (by simp; omega) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 e] using this

theorem cwArmsS_good (X : CX) (J : ℕ) (succ : List ℕ) (se : CW) (key : Option (List Cnt)) (v : V) (lo hi : ℕ)
    {P : Cnt × ℕ → Prop} (hP : MaxClosed P) :
    ∀ (as : List (List Core.Stmt)) (ts : List ℕ) (c : Cnt) (u k : ℕ) {r : Cnt × ℕ},
      cwArmsS X J succ se key v lo hi as ts c u k = some r → P r →
      ts.length = as.length ∧ P (c, u) ∧ ∀ e (he : e < as.length) (ht : e < ts.length),
        lo ≤ k + e → k + e < hi → ∃ r', armStep X J succ se key v as[e] ts[e] (k + e) = some r' ∧
          P r'
  | [], [], c, u, _, r, h, hg => by
    simp only [cwArmsS, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hg, fun _ he ↦ absurd he (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, _, _, _, h, _ => by simp [cwArmsS] at h
  | _ :: _, [], _, _, _, _, h, _ => by simp [cwArmsS] at h
  | a :: as, t :: ts, c, u, k, r, h, hg => by
    simp only [cwArmsS] at h
    cases hsel : (Nat.ble lo k && Nat.blt k hi)
    · rw [hsel, Bool.cond_false] at h
      obtain ⟨hl, hgc, ha⟩ := cwArmsS_good X J succ se key v lo hi hP as ts c u (k + 1) h hg
      refine ⟨by simp [hl], hgc, fun e he ht hlo hhi ↦ ?_⟩
      cases e with
      | zero =>
        exfalso
        have : (Nat.ble lo k && Nat.blt k hi) = true := by
          simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; omega
        rw [this] at hsel; cases hsel
      | succ e =>
        have := ha e (by simpa using he) (by simpa using ht) (by omega) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 e] using this
    · rw [hsel, Bool.cond_true] at h
      split at h
      · rename_i c' u' hs
        obtain ⟨hl, hgc, ha⟩ := cwArmsS_good X J succ se key v lo hi hP as ts _ _ (k + 1) h hg
        obtain ⟨hg1, hg2⟩ := (hP _ _ _ _).mp hgc
        refine ⟨by simp [hl], hg1, fun e he ht hlo hhi ↦ ?_⟩
        cases e with
        | zero => exact ⟨(c', u'), by simpa using hs, hg2⟩
        | succ e =>
          have := ha e (by simpa using he) (by simpa using ht) (by omega) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 e] using this
      · simp at h

theorem armTg_none {X : CX} {v : V} (h : chainOf X v.idx = none) (k : ℕ) : armTg X v k = [] := by
  simp only [armTg, h]

theorem chainPre_none {X : CX} {v : V} (h : chainOf X v.idx = none) (st : CW) (n : ℕ) :
    chainPre X st v n = true := by
  simp only [chainPre, h]

theorem armTg_congr (X : CX) {L : CLoc} {A : ℕ → Prop} (hA : ∀ n, A n → X.loc.get? n = L.get? n)
    {v : V} (hy : ∀ ts y b, chainOf X v.idx = some (ts, y, b) → A y) (k : ℕ) :
    armTg X v k = armTg { X with loc := L } v k := by
  unfold armTg
  rw [show chainOf { X with loc := L } v.idx = chainOf X v.idx from rfl]
  cases h : chainOf X v.idx with
  | none => rfl
  | some p =>
    obtain ⟨ts, y, b⟩ := p
    simp only
    rw [ccell_congr hA (v := V.n y) (hy ts y b h)]

theorem chainPre_congr (X : CX) {L : CLoc} {A : ℕ → Prop} (hA : ∀ n, A n → X.loc.get? n = L.get? n)
    {v : V} (hy : ∀ ts y b, chainOf X v.idx = some (ts, y, b) → A y) (st : CW) (n : ℕ) :
    chainPre X st v n = chainPre { X with loc := L } st v n := by
  unfold chainPre
  rw [show chainOf { X with loc := L } v.idx = chainOf X v.idx from rfl]
  cases h : chainOf X v.idx with
  | none => rfl
  | some p =>
    obtain ⟨ts, y, b⟩ := p
    simp only
    rw [ccell_congr hA (v := V.n y) (hy ts y b h)]
    rfl

theorem armStep_congr (X : CX) {L : CLoc} {A : ℕ → Prop} (hA : ∀ n, A n → X.loc.get? n = L.get? n)
    (J : ℕ) (succ : List ℕ) (se : CW) (key : Option (List Cnt)) {v : V}
    (hy : ∀ ts y b, chainOf X v.idx = some (ts, y, b) → A y)
    {a : List Core.Stmt} (t k : ℕ) (ha : a.all isAtomS = true)
    (hv : ∀ v ∈ stmtsVals a, A v.idx) :
    armStep X J succ se key v a t k = armStep { X with loc := L } J succ se key v a t k := by
  unfold armStep
  rw [fileB_congr hA X.fs a se.book hv, armTg_congr X hA hy k]
  have hs : segAtC { X with loc := L } t se = segAtC X t se := rfl
  rw [hs]
  split
  · rename_i s _
    rw [cw_atoms_loc X L a _ ha]
  · rfl

/-! ## Groups of arms -/

theorem cw_nil_fresh (X : CX) {J : ℕ} {st sj : CW} (h : segAtC X J st = some sj) (c : Cnt) (u : ℕ) :
    cw X [] { sj with cnt := c, uq := u } = .join J c u := by
  unfold segAtC at h
  split at h
  · rename_i s _
    cases hb : Nat.beq s.start J
    · rw [hb] at h; cases h
    · rw [hb] at h
      obtain rfl := (Option.some.inj h)
      simp only [cw, endC]
  · cases h

/-- A group's walk of arm `0` of a `match` on `v`, its values' cells and the next selector's the
window's, is the window's. -/
theorem armZero_congr (X : CX) (v : V) (a0 : List Core.Stmt) (ha0 : a0.all isAtomS = true)
    (gs : List (ℕ × ℕ × CLoc))
    (h0v : ∀ g ∈ gs, ∀ x ∈ stmtsVals a0, g.2.2.get? x.idx = X.loc.get? x.idx)
    (hy : ∀ g ∈ gs, ∀ ts y b, chainOf X v.idx = some (ts, y, b) → g.2.2.get? y = X.loc.get? y) :
    ∀ g ∈ gs, ∀ se s0 : CW, cw { X with loc := g.2.2 } a0 { s0 with
      book := fileB g.2.2 X.fs a0 se.book, tg := armTg { X with loc := g.2.2 } v 0 ++ s0.tg } =
      cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } := by
  intro g hg se s0
  rw [cw_atoms_loc X g.2.2 a0 _ ha0,
    ← fileB_congr (A := fun n ↦ g.2.2.get? n = X.loc.get? n) (fun n hn ↦ hn.symm) X.fs a0 se.book
      (fun x hx ↦ h0v g hg x hx),
    ← armTg_congr X (A := fun n ↦ g.2.2.get? n = X.loc.get? n) (fun n hn ↦ hn.symm) (hy g hg)]

/-- **A `match`'s arms from its groups'**: every arm's step from the group holding it (`cwArmsS`
on the group's cells, which agree with the window's on the arm's values and the next selector),
all within `P`, give the window's arms (`cwArms`) within `P`. -/
theorem cwArms_of_groups (X : CX) (J : ℕ) (succ : List ℕ) (se : CW) (key : Option (List Cnt))
    (v : V) (as : List (List Core.Stmt)) (ts : List ℕ) (c0 : Cnt) (u0 : ℕ)
    (gs : List (ℕ × ℕ × CLoc)) (g0 : ℕ × ℕ × CLoc) (hg0 : g0 ∈ gs)
    (hcov : ∀ e < as.length, ∃ g ∈ gs, g.1 ≤ e + 1 ∧ e + 1 < g.2.1)
    (has : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      as[e].all isAtomS = true)
    (hy : ∀ g ∈ gs, ∀ ts y b, chainOf X v.idx = some (ts, y, b) → g.2.2.get? y = X.loc.get? y)
    (hav : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      ∀ x ∈ stmtsVals as[e], g.2.2.get? x.idx = X.loc.get? x.idx)
    {P : Cnt × ℕ → Prop} (hP : MaxClosed P)
    (h : ∀ g ∈ gs, ∃ r, cwArmsS { X with loc := g.2.2 } J succ se key v g.1 g.2.1 as ts c0 u0 1 =
      some r ∧ P r) :
    ∃ r, cwArms X J succ v se key as ts c0 u0 1 = some r ∧ P r := by
  obtain ⟨r0, h0, hp0⟩ := h g0 hg0
  obtain ⟨hl, hg0', -⟩ := cwArmsS_good _ _ _ _ _ _ _ _ hP as ts c0 u0 1 h0 hp0
  refine cwArms_good X J succ se key v hP as ts c0 u0 1 hl hg0' fun e he ht ↦ ?_
  obtain ⟨g, hg, hlo, hhi⟩ := hcov e he
  obtain ⟨r, hr, hpr⟩ := h g hg
  obtain ⟨-, -, harm⟩ := cwArmsS_good _ _ _ _ _ _ _ _ hP as ts c0 u0 1 hr hpr
  obtain ⟨r', hr', hgr⟩ := harm e he ht (by omega) (by omega)
  refine ⟨r', ?_, hgr⟩
  rw [armStep_congr X (A := fun n ↦ g.2.2.get? n = X.loc.get? n) (fun n hn ↦ hn.symm) _ _ _ _
    (hy g hg) _ _ (has g hg e he hlo hhi) (hav g hg e he hlo hhi)]
  exact hr'

/-- What the counts and set-up cells of a `match`'s arms must satisfy for the walk to end within
`B`, `U`: within them, or, the arms counted separately (`armKeyD`), the set-up cells within `U`. -/
theorem armsGood (key : Option (List Cnt)) (B : Cnt) (U : ℕ) : ∃ P : Cnt × ℕ → Prop, MaxClosed P ∧
    (∀ (se : CW) (r : Cnt × ℕ), Good B U (armCnt key se r.1, r.2) → P r) ∧
    (∀ (se : CW) (r r' : Cnt × ℕ), Good B U (armCnt key se r'.1, r'.2) → P r →
      Good B U (armCnt key se r.1, r.2)) := by
  rcases key with _ | cs
  · exact ⟨Good B U, maxClosed_good B U, fun _ _ hr ↦ hr, fun _ _ _ _ hr ↦ hr⟩
  · exact ⟨fun r ↦ subK r.2 U = true, maxClosed_subK U, fun _ _ hr ↦ hr.2,
      fun _ _ _ h' hr ↦ ⟨h'.1, hr⟩⟩

/-- How an arm's walk ends, for the arms after it: at the join `J` (`succ = []`), or in the next
chained `match`'s table jump through `fp[J]` into `succ`; with its counts and set-up cells. -/
def armTgt : RC → Option (ℕ × List ℕ × Cnt × ℕ)
  | .join J c u => some (J, [], c, u)
  | .chain o succ c u => bif succ.isEmpty then none else some (o, succ, c, u)
  | _ => none

/-- The end of a `match`'s walk, its arms ending as `armTgt` gives `(J, succ)`, with the counts `c`
and set-up cells `u`. -/
noncomputable def armsEnd (X : CX) (se : CW) (e J : ℕ) (succ : List ℕ) (c : Cnt) (u : ℕ) : RC :=
  bif succ.isEmpty then
    (match segAtC X J se with
      | some _ => .join J c u
      | none => .fail e)
  else .chain J succ c u

theorem armEnd_armsEnd {X : CX} {se : CW} {e J J' : ℕ} {sc sc' : List ℕ} {c : Cnt} {u : ℕ}
    {p : Cnt × ℕ} (h : armEnd J sc (armsEnd X se e J' sc' c u) = some p) :
    J' = J ∧ sc' = sc ∧ p = (c, u) ∧ (sc.isEmpty = true → (segAtC X J se).isSome = true) := by
  unfold armsEnd at h
  cases hs : sc'.isEmpty
  · rw [hs, Bool.cond_false] at h
    simp only [armEnd, Bool.cond_eq_ite, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq,
      beq_iff_eq] at h
    split_ifs at h with hc
    · obtain ⟨⟨hne, rfl⟩, rfl⟩ := hc
      exact ⟨rfl, rfl, (Option.some.inj h).symm, fun he ↦ by rw [hne] at he; cases he⟩
  · rw [hs, Bool.cond_true] at h
    split at h
    · rename_i sj hsj
      simp only [armEnd, Bool.cond_eq_ite, Bool.and_eq_true, Nat.beq_eq] at h
      split_ifs at h with hc
      obtain ⟨he, rfl⟩ := hc
      have h1 := List.isEmpty_iff.mp he
      have h2 := List.isEmpty_iff.mp hs
      exact ⟨rfl, by rw [h1, h2], (Option.some.inj h).symm, fun _ ↦ by rw [hsj]; rfl⟩
    · simp [armEnd] at h

theorem armEnd_armsEnd_self {X : CX} {se : CW} {e J : ℕ} {sc : List ℕ} {c : Cnt} {u : ℕ}
    (hs : sc.isEmpty = true → (segAtC X J se).isSome = true) :
    armEnd J sc (armsEnd X se e J sc c u) = some (c, u) := by
  unfold armsEnd
  cases he : sc.isEmpty
  · simp [armEnd, he]
  · obtain ⟨sj, hsj⟩ := Option.isSome_iff_exists.mp (hs he)
    simp [armEnd, he, hsj]

/-! ## A `match` not entered, by groups -/

/-- The condition of a `match`'s walk at its table jump through `fp[t]`, read through `fp[o1]`
from the table at `base` into the arms `t0 :: ts` (`cw`'s, `cwMatchS`'s). -/
noncomputable def matchOk (X : CX) (st : CW) (v : V) (t : ℕ) (ft : Tgt) (t0 : ℕ) (ts : List ℕ)
    (n o1 base : ℕ) : Bool :=
  X.F.self ft && Nat.beq ts.length n && Nat.beq o1 (X.loc.cell v) &&
    v.path.isEmpty && Nat.beq v.tag 0 && selOk X st v &&
    inFrame X.fs [o1, t] &&
    X.arms.any (fun a ↦ Nat.beq a.1 v.idx && Nat.beq a.2.1 t && Nat.beq a.2.2 base) &&
    armsOk X.G X.entry base 0 (t0 :: ts) && chainPre X st v (n + 1)

/-- **A `match`'s completeness walk with the arms `lo ≤ k < hi` (and arm `0`)**: `cw`'s on a
window of one `match`, its arms by `cwArmsS`. -/
noncomputable def cwMatchS (X : CX) (lo hi : ℕ) (v : V) (arms : List (List Core.Stmt)) (st : CW) : RC :=
  match arms with
  | [] => .fail 28
  | a0 :: as =>
    match st.seg.exit.kind, st.seg.exit.succ with
    | .jump (.cell t) ft, t0 :: ts =>
      match tblRead t st.its with
      | some (o1, base) =>
        bif matchOk X st v t ft t0 ts as.length o1 base then
          match endAtC X { st with tg := (t, o1, base) :: st.tg } with
          | .ok se =>
            match segAtC X t0 (armSt (armKeyD X.acs v.idx) se) with
            | some s0 =>
              match armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) with
              | some (J, sc, c0, u0) =>
                bif armChkK (armKeyD X.acs v.idx) 0 c0 then
                  match cwArmsS X J sc (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) v lo hi as
                      ts c0 u0 1 with
                  | some (c, u) => armsEnd X se 20 J sc (armCnt (armKeyD X.acs v.idx) se c) u
                  | none => .fail 21
                else .fail 24
              | none => .fail 22
            | none => .fail 23
          | .error e => .fail e
        else .fail 25
      | none => .fail 26
    | _, _ => .fail 27

theorem cwMatchS_dec {X : CX} {lo hi : ℕ} {v : V} {a0 : List Core.Stmt} {as : List (List Core.Stmt)}
    {st : CW} {J : ℕ} {sc : List ℕ} {p : Cnt × ℕ}
    (h : armEnd J sc (cwMatchS X lo hi v (a0 :: as) st) = some p) :
    ∃ t ft t0 ts o1 base se s0 J' sc' c0 u0 c u, st.seg.exit.kind = .jump (.cell t) ft ∧
      st.seg.exit.succ = t0 :: ts ∧ tblRead t st.its = some (o1, base) ∧
      matchOk X st v t ft t0 ts as.length o1 base = true ∧
      endAtC X { st with tg := (t, o1, base) :: st.tg } = .ok se ∧
      segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0 ∧
      armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) =
        some (J', sc', c0, u0) ∧ armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧
      cwArmsS X J' sc' (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) v lo hi as ts c0 u0 1 =
        some (c, u) ∧
      cwMatchS X lo hi v (a0 :: as) st = armsEnd X se 20 J' sc' (armCnt (armKeyD X.acs v.idx) se c) u := by
  generalize hr : cwMatchS X lo hi v (a0 :: as) st = r at h
  unfold cwMatchS at hr
  dsimp only at hr
  split at hr
  · rename_i t ft t0 ts hk hs
    split at hr
    · rename_i o1 base hb
      simp only [Bool.cond_eq_ite] at hr
      split_ifs at hr with hc
      · split at hr
        · rename_i se hse
          split at hr
          · rename_i s0 hs0
            split at hr
            · rename_i J' sc' c0 u0 ht
              split_ifs at hr with hk0
              · split at hr
                · rename_i c u harms
                  exact ⟨t, ft, t0, ts, o1, base, se, s0, J', sc', c0, u0, c, u, hk, hs, hb, hc, hse, hs0,
                    ht, hk0, harms, hr.symm⟩
                · subst hr; simp [armEnd] at h
              · subst hr; simp [armEnd] at h
            · subst hr; simp [armEnd] at h
          · subst hr; simp [armEnd] at h
        · subst hr; simp [armEnd] at h
      · subst hr; simp [armEnd] at h
    · subst hr; simp [armEnd] at h
  · subst hr; simp [armEnd] at h

/-- `cw` on a `match`, the window's one statement, from its parts. -/
theorem cw_of_parts {X : CX} {v : V} {a0 : List Core.Stmt} {as : List (List Core.Stmt)} {st : CW}
    {t : ℕ} {ft : Tgt} {t0 : ℕ} {ts : List ℕ} {o1 base : ℕ} {se s0 : CW} {J : ℕ} {sc : List ℕ}
    {c0 : Cnt} {u0 : ℕ} {c : Cnt} {u : ℕ} (hk : st.seg.exit.kind = .jump (.cell t) ft)
    (hs : st.seg.exit.succ = t0 :: ts) (hb : tblRead t st.its = some (o1, base))
    (hc : matchOk X st v t ft t0 ts as.length o1 base = true)
    (hse : endAtC X { st with tg := (t, o1, base) :: st.tg } = .ok se)
    (hs0 : segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0)
    (ht : armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) =
      some (J, sc, c0, u0))
    (hk0 : armChkK (armKeyD X.acs v.idx) 0 c0 = true)
    (ha : cwArms X J sc v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 =
      some (c, u)) :
    cw X [.match_ v (a0 :: as)] st = armsEnd X se 20 J sc (armCnt (armKeyD X.acs v.idx) se c) u := by
  unfold matchOk at hc
  simp only [cw, hk, hs, hb, hc, Bool.cond_true, hse, hs0, Exec.Trie.seq_eq]
  generalize cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = r
    at ht ⊢
  cases r with
  | join J' c' u' =>
    simp only [armTgt, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
    simp only [hk0, Bool.cond_true, ha, armsEnd, List.isEmpty_nil]
    cases hsj : segAtC X J' se with
    | none => rfl
    | some sj =>
      simpa only [Cnt.seq_eq, natSeq_eq, cw] using cw_nil_fresh X hsj (armCnt (armKeyD X.acs v.idx) se c) u
  | chain o' succ' c' u' =>
    simp only [armTgt, Bool.cond_eq_ite] at ht
    split_ifs at ht with he
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
    simp only [hk0, he, List.isEmpty_nil, Bool.not_false, Bool.and_self, Bool.cond_true, ha,
      Cnt.seq_eq, natSeq_eq, armsEnd, Bool.cond_false]
  | mid => simp [armTgt] at ht
  | done => simp [armTgt] at ht
  | fail => simp [armTgt] at ht

theorem matchOk_congr {X : CX} {L : CLoc} {A : ℕ → Prop} (hA : ∀ n, A n → X.loc.get? n = L.get? n)
    {st : CW} {v : V} {t : ℕ} {ft : Tgt} {t0 : ℕ} {ts : List ℕ} {n o1 base : ℕ} (hv : A v.idx)
    (hy : ∀ ts y b, chainOf X v.idx = some (ts, y, b) → A y) :
    matchOk X st v t ft t0 ts n o1 base = matchOk { X with loc := L } st v t ft t0 ts n o1 base := by
  unfold matchOk
  rw [ccell_congr hA hv, chainPre_congr X hA hy]
  rfl

/-- **A `match` window's completeness walk from its groups'**: groups `(lo, hi, cells)` covering
every arm, each group's walk on its cells ending as `armEnd J sc` says within `B`, `U`, the cells
agreeing with the window's on the values each names and on the next selector, give the window's
walk ending so within `B`, `U`. -/
theorem cw_of_groups (X : CX) (v : V) (a0 : List Core.Stmt) (as : List (List Core.Stmt)) (st : CW)
    (gs : List (ℕ × ℕ × CLoc)) (g0 : ℕ × ℕ × CLoc) (hg0 : g0 ∈ gs)
    (hcov : ∀ e < as.length, ∃ g ∈ gs, g.1 ≤ e + 1 ∧ e + 1 < g.2.1)
    (ha0 : a0.all isAtomS = true)
    (has : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      as[e].all isAtomS = true)
    (hv : ∀ g ∈ gs, g.2.2.get? v.idx = X.loc.get? v.idx)
    (h0v : ∀ g ∈ gs, ∀ x ∈ stmtsVals a0, g.2.2.get? x.idx = X.loc.get? x.idx)
    (hav : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      ∀ x ∈ stmtsVals as[e], g.2.2.get? x.idx = X.loc.get? x.idx)
    (hy : ∀ g ∈ gs, ∀ ts y b, chainOf X v.idx = some (ts, y, b) → g.2.2.get? y = X.loc.get? y)
    {J : ℕ} {sc : List ℕ} {B : Cnt} {U : ℕ}
    (h : ∀ g ∈ gs, ∃ p, armEnd J sc (cwMatchS { X with loc := g.2.2 } g.1 g.2.1 v (a0 :: as) st) =
      some p ∧ Good B U p) :
    ∃ p, armEnd J sc (cw X [.match_ v (a0 :: as)] st) = some p ∧ Good B U p := by
  obtain ⟨P, hP, hPg, hPf⟩ := armsGood (armKeyD X.acs v.idx) B U
  have hw0 := armZero_congr X v a0 ha0 gs h0v hy
  -- each group's parts are the window's
  have hdec : ∀ g ∈ gs, ∃ t ft t0 ts o1 base se s0 c0 u0 c u, st.seg.exit.kind = .jump (.cell t) ft ∧
      st.seg.exit.succ = t0 :: ts ∧ tblRead t st.its = some (o1, base) ∧
      matchOk X st v t ft t0 ts as.length o1 base = true ∧
      endAtC X { st with tg := (t, o1, base) :: st.tg } = .ok se ∧
      segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0 ∧
      armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) =
        some (J, sc, c0, u0) ∧ armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧
      cwArmsS { X with loc := g.2.2 } J sc (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) v
        g.1 g.2.1 as ts c0 u0 1 = some (c, u) ∧ Good B U (armCnt (armKeyD X.acs v.idx) se c, u) ∧
      (sc.isEmpty = true → (segAtC X J se).isSome = true) := by
    intro g hg
    obtain ⟨p, hp, hgood⟩ := h g hg
    obtain ⟨t, ft, t0, ts, o1, base, se, s0, J', sc', c0, u0, c, u, hk, hs, hb, hc, hse, hs0, ht, hk0,
      harms, heq⟩ := cwMatchS_dec hp
    rw [heq] at hp
    obtain ⟨rfl, rfl, rfl, hsj⟩ := armEnd_armsEnd hp
    refine ⟨t, ft, t0, ts, o1, base, se, s0, c0, u0, c, u, hk, hs, hb, ?_,
      by rw [← endAtC_loc X g.2.2]; exact hse, hs0, by rw [← hw0 g hg]; exact ht, hk0, harms,
      hgood, hsj⟩
    rw [matchOk_congr (A := fun n ↦ g.2.2.get? n = X.loc.get? n) (fun n hn ↦ hn.symm) (hv g hg)
      (hy g hg)]
    exact hc
  obtain ⟨t, ft, t0, ts, o1, base, se, s0, c0, u0, c1, u1, hk, hs, hb, hc, hse, hs0, ht, hk0, -, hg1,
    hsj⟩ := hdec g0 hg0
  obtain ⟨⟨rc, ru⟩, hr, hgr⟩ := cwArms_of_groups X J sc (armSt (armKeyD X.acs v.idx) se)
    (armKeyD X.acs v.idx) v as ts c0 u0 gs g0 hg0 hcov has hy hav hP fun g hg ↦ by
      obtain ⟨t', ft', t0', ts', o1', base', se', s0', c0', u0', c, u, hk', hs', hb', -, hse', hs0', ht',
        -, harms, hpc, -⟩ := hdec g hg
      obtain ⟨rfl, rfl⟩ := List.cons.inj (hs'.symm.trans hs)
      obtain ⟨rfl, rfl⟩ : t' = t ∧ ft' = ft := by
        have e := hk'.symm.trans hk
        simp only [Kind.jump.injEq, Tgt.cell.injEq] at e
        exact e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hb'.symm.trans hb))
      obtain rfl : se = se' := by
        have e := hse'.symm.trans hse
        simp only [Except.ok.injEq] at e
        exact e.symm
      obtain rfl := Option.some.inj (hs0'.symm.trans hs0)
      simp only [ht, Option.some.injEq, Prod.mk.injEq] at ht'
      obtain ⟨-, -, rfl, rfl⟩ := ht'
      exact ⟨(c, u), harms, hPg se (c, u) hpc⟩
  refine ⟨(armCnt (armKeyD X.acs v.idx) se rc, ru), ?_, hPf se (rc, ru) (c1, u1) hg1 hgr⟩
  rw [cw_of_parts hk hs hb hc hse hs0 ht hk0 hr]
  exact armEnd_armsEnd_self hsj

/-! ## An entered `match`, by groups -/

/-- The condition of an entered `match`'s walk (`cwE`'s, `cwES`'s). -/
noncomputable def entOk (X : CX) (o : ℕ) (se : CW) (v : V) (ts : List ℕ) (n : ℕ) : Bool :=
  Nat.beq o (X.loc.cell v) && v.path.isEmpty && Nat.beq v.tag 0 && selOk X se v &&
    Nat.beq ts.length n && inFrame X.fs [o] && chainPre X se v (n + 1)

/-- **An entered window's chained `match` with the arms `lo ≤ k < hi` (and arm `0`)**: `cwE`'s on
it, its arms by `cwArmsS`. -/
noncomputable def cwES (X : CX) (lo hi o : ℕ) (succ : List ℕ) (se : CW) (v : V)
    (arms : List (List Core.Stmt)) : RC :=
  match arms, succ with
  | a0 :: as, t0 :: ts =>
    bif entOk X o se v ts as.length then
      match segAtC X t0 (armSt (armKeyD X.acs v.idx) se) with
      | some s0 =>
        match armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) with
        | some (J, sc, c0, u0) =>
          bif armChkK (armKeyD X.acs v.idx) 0 c0 then
            match cwArmsS X J sc (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) v lo hi as ts
                c0 u0 1 with
            | some (c, u) => armsEnd X se 80 J sc (armCnt (armKeyD X.acs v.idx) se c) u
            | none => .fail 81
          else .fail 84
        | none => .fail 82
      | none => .fail 83
    else .fail 85
  | _, _ => .fail 86

theorem cwES_dec {X : CX} {lo hi o : ℕ} {succ : List ℕ} {se : CW} {v : V} {a0 : List Core.Stmt}
    {as : List (List Core.Stmt)} {J : ℕ} {sc : List ℕ} {p : Cnt × ℕ}
    (h : armEnd J sc (cwES X lo hi o succ se v (a0 :: as)) = some p) :
    ∃ t0 ts s0 J' sc' c0 u0 c u, succ = t0 :: ts ∧ entOk X o se v ts as.length = true ∧
      segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0 ∧
      armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) =
        some (J', sc', c0, u0) ∧ armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧
      cwArmsS X J' sc' (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) v lo hi as ts c0 u0 1 =
        some (c, u) ∧
      cwES X lo hi o succ se v (a0 :: as) = armsEnd X se 80 J' sc' (armCnt (armKeyD X.acs v.idx) se c) u := by
  cases succ with
  | nil => simp [cwES, armEnd] at h
  | cons t0 ts =>
    generalize hr : cwES X lo hi o (t0 :: ts) se v (a0 :: as) = r at h
    unfold cwES at hr
    simp only [Bool.cond_eq_ite] at hr
    split_ifs at hr with hc
    · split at hr
      · rename_i s0 hs0
        split at hr
        · rename_i J' sc' c0 u0 ht
          split_ifs at hr with hk
          · split at hr
            · rename_i c u harms
              exact ⟨t0, ts, s0, J', sc', c0, u0, c, u, rfl, hc, hs0, ht, hk, harms, hr.symm⟩
            · subst hr; simp [armEnd] at h
          · subst hr; simp [armEnd] at h
        · subst hr; simp [armEnd] at h
      · subst hr; simp [armEnd] at h
    · subst hr; simp [armEnd] at h

/-- `cwE` on a chained `match`, the window's last statement, from its parts. -/
theorem cwE_of_parts {X : CX} {o : ℕ} {se : CW} {v : V} {a0 : List Core.Stmt}
    {as : List (List Core.Stmt)} {t0 : ℕ} {ts : List ℕ} {s0 : CW} {J : ℕ} {sc : List ℕ} {c0 : Cnt}
    {u0 : ℕ} {c : Cnt} {u : ℕ} (hc : entOk X o se v ts as.length = true)
    (hs0 : segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0)
    (ht : armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) =
      some (J, sc, c0, u0))
    (hk : armChkK (armKeyD X.acs v.idx) 0 c0 = true)
    (ha : cwArms X J sc v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 =
      some (c, u)) :
    cwE X o (t0 :: ts) se [.match_ v (a0 :: as)] =
      armsEnd X se 80 J sc (armCnt (armKeyD X.acs v.idx) se c) u := by
  unfold entOk at hc
  simp only [cwE, hc, Bool.cond_true, hs0, Exec.Trie.seq_eq]
  generalize cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = r
    at ht ⊢
  cases r with
  | join J' c' u' =>
    simp only [armTgt, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
    simp only [hk, Bool.cond_true, ha, armsEnd, List.isEmpty_nil]
    cases hsj : segAtC X J' se with
    | none => rfl
    | some sj => simp only [Cnt.seq_eq, natSeq_eq, cw_nil_fresh X hsj]
  | chain o' succ' c' u' =>
    simp only [armTgt, Bool.cond_eq_ite] at ht
    split_ifs at ht with he
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
    simp only [hk, he, List.isEmpty_nil, Bool.not_false, Bool.and_self, Bool.cond_true, ha,
      Cnt.seq_eq, natSeq_eq, armsEnd, Bool.cond_false]
  | mid => simp [armTgt] at ht
  | done => simp [armTgt] at ht
  | fail => simp [armTgt] at ht

theorem entOk_congr {X : CX} {L : CLoc} {A : ℕ → Prop} (hA : ∀ n, A n → X.loc.get? n = L.get? n)
    {o : ℕ} {se : CW} {v : V} {ts : List ℕ} {n : ℕ} (hv : A v.idx)
    (hy : ∀ ts y b, chainOf X v.idx = some (ts, y, b) → A y) :
    entOk X o se v ts n = entOk { X with loc := L } o se v ts n := by
  unfold entOk
  rw [ccell_congr hA hv, chainPre_congr X hA hy]
  rfl

/-- **An entered window's chained `match` from its groups'**: groups `(lo, hi, cells)` covering
every arm, each group's walk on its cells ending as `armEnd J sc` says within `B`, `U`, the cells
agreeing with the window's on the values each names and on the next selector, give the window's
walk ending so within `B`, `U`. -/
theorem cwE_of_groups (X : CX) (o : ℕ) (succ : List ℕ) (se : CW) (v : V) (a0 : List Core.Stmt)
    (as : List (List Core.Stmt)) (gs : List (ℕ × ℕ × CLoc)) (g0 : ℕ × ℕ × CLoc) (hg0 : g0 ∈ gs)
    (hcov : ∀ e < as.length, ∃ g ∈ gs, g.1 ≤ e + 1 ∧ e + 1 < g.2.1)
    (ha0 : a0.all isAtomS = true)
    (has : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      as[e].all isAtomS = true)
    (hv : ∀ g ∈ gs, g.2.2.get? v.idx = X.loc.get? v.idx)
    (h0v : ∀ g ∈ gs, ∀ x ∈ stmtsVals a0, g.2.2.get? x.idx = X.loc.get? x.idx)
    (hav : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      ∀ x ∈ stmtsVals as[e], g.2.2.get? x.idx = X.loc.get? x.idx)
    (hy : ∀ g ∈ gs, ∀ ts y b, chainOf X v.idx = some (ts, y, b) → g.2.2.get? y = X.loc.get? y)
    {J : ℕ} {sc : List ℕ} {B : Cnt} {U : ℕ}
    (h : ∀ g ∈ gs, ∃ p, armEnd J sc (cwES { X with loc := g.2.2 } g.1 g.2.1 o succ se v (a0 :: as)) =
      some p ∧ Good B U p) :
    ∃ p, armEnd J sc (cwE X o succ se [.match_ v (a0 :: as)]) = some p ∧ Good B U p := by
  obtain ⟨P, hP, hPg, hPf⟩ := armsGood (armKeyD X.acs v.idx) B U
  have hw0 := armZero_congr X v a0 ha0 gs h0v hy
  -- each group's parts are the window's
  have hdec : ∀ g ∈ gs, ∃ t0 ts s0 c0 u0 c u, succ = t0 :: ts ∧ entOk X o se v ts as.length = true ∧
      segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0 ∧
      armTgt (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) =
        some (J, sc, c0, u0) ∧ armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧
      cwArmsS { X with loc := g.2.2 } J sc (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) v
        g.1 g.2.1 as ts c0 u0 1 = some (c, u) ∧ P (c, u) ∧
      (sc.isEmpty = true → (segAtC X J se).isSome = true) := by
    intro g hg
    obtain ⟨p, hp, hgood⟩ := h g hg
    obtain ⟨t0, ts, s0, J', sc', c0, u0, c, u, rfl, hc, hs0, ht, hk, harms, heq⟩ := cwES_dec hp
    rw [heq] at hp
    obtain ⟨rfl, rfl, rfl, hsj⟩ := armEnd_armsEnd hp
    refine ⟨t0, ts, s0, c0, u0, c, u, rfl, ?_, hs0, by rw [← hw0 g hg]; exact ht, hk, harms,
      hPg se (c, u) hgood, hsj⟩
    rw [entOk_congr (A := fun n ↦ g.2.2.get? n = X.loc.get? n) (fun n hn ↦ hn.symm) (hv g hg) (hy g hg)]
    exact hc
  obtain ⟨t0, ts, s0, c0, u0, -, -, rfl, hc, hs0, ht, hk, -, -, hsj⟩ := hdec g0 hg0
  obtain ⟨⟨rc, ru⟩, hr, hgr⟩ := cwArms_of_groups X J sc (armSt (armKeyD X.acs v.idx) se)
    (armKeyD X.acs v.idx) v as ts c0 u0 gs g0 hg0 hcov has hy hav hP fun g hg ↦ by
      obtain ⟨t0', ts', s0', c0', u0', c, u, he, -, hs0', ht', -, harms, hpc, -⟩ := hdec g hg
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      obtain rfl := Option.some.inj (hs0'.symm.trans hs0)
      simp only [ht, Option.some.injEq, Prod.mk.injEq] at ht'
      obtain ⟨-, -, rfl, rfl⟩ := ht'
      exact ⟨(c, u), harms, hpc⟩
  refine ⟨(armCnt (armKeyD X.acs v.idx) se rc, ru), ?_, ?_⟩
  · rw [cwE_of_parts hc hs0 ht hk hr]
    exact armEnd_armsEnd_self hsj
  · obtain ⟨-, -, -, c0', u0', c, u, -, -, -, -, -, -, -, -⟩ := hdec g0 hg0
    obtain ⟨p, hp, hgood⟩ := h g0 hg0
    obtain ⟨t0', ts', s0', J', sc', c0'', u0'', c', u', he, -, hs0', ht', -, harms, heq⟩ := cwES_dec hp
    rw [heq] at hp
    obtain ⟨rfl, rfl, rfl, -⟩ := armEnd_armsEnd hp
    exact hPf se (rc, ru) (c', u') hgood hgr

/-! ## A completeness window by groups -/

/-- The next selector of a chained `match` on `v` has a cell. -/
noncomputable def nextSelOk (X : CX) (v : V) : Bool :=
  match chainOf X v.idx with
  | some (_, y, _) => (X.loc.get? y).isSome
  | none => true

/-- The walk of a window of one `match` with the arms `lo ≤ k < hi` (and arm `0`): `cplRes`'s,
entered (`cwES`) or not (`cwMatchS`). -/
noncomputable def cwSplit (X : CX) (lo hi : ℕ) (ent : Option (ℕ × List ℕ)) (v : V)
    (arms : List (List Core.Stmt)) (st : CW) : RC :=
  match ent with
  | some (o, succ) => cwES X lo hi o succ st v arms
  | none => cwMatchS X lo hi v arms st

/-- **The check of a group of a completeness window of one `match`**: the window one part, arm
`0` and the arms `lo ≤ k < hi` atoms all, their values and the next selector with cells among the
group's (`clocG`), and the walk with those arms (`cwSplit`) ending as the window's part must
(`partEnd`). Not the last window. -/
noncomputable def cplWinS (j i lo hi gm gn am an : ℕ) : Bool :=
  Nat.beq (nParts j i) 1 && Nat.beq (partM j i 0) 0 && Nat.blt i (certOf j).cuts.length &&
  match partStmts j i 0 with
  | [.match_ v (a0 :: as)] =>
    matchAtoms lo hi [.match_ v (a0 :: as)] &&
    match execWinCS (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
        (((certOf j).succAt i).drop 1) ((certOf j).endAt (fnOf j) i) with
    | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦
      (clocG (certOf j) i gm gn am an).seq fun loc ↦
      (statT (fsN j) (plumbOf j).stat .nil).seq fun stat ↦
      (partC j i 0).seq fun c ↦ natSeq (partU j i 0) fun u ↦ natSeq (partJ j i 0) fun J ↦
      natSeq (plumbOf j).nv fun nv ↦
      (stmtsVals (selStmts lo hi [.match_ v (a0 :: as)])).all (fun x ↦ (loc.get? x.idx).isSome) &&
      nextSelOk (cxOf j idx loc stat nv (stopOf j i 0)) v &&
      match getF idx J with
      | some s => bif Nat.beq s.start J then
          partEnd j i 0 (cwSplit (cxOf j idx loc stat nv (stopOf j i 0)) lo hi (partEnt j i 0) v
            (a0 :: as) ⟨s, s.items, .nil, [], [], [], c, u, some J, 0⟩)
        else false
      | none => false
  | _ => false

/-- Where a window of one part hands on: into the next window's chained `match`'s table jump if it
is entered, else at its start. -/
noncomputable def nextTgt (j i : ℕ) : ℕ × List ℕ :=
  match partEnt j (i + 1) 0 with
  | some (o, succ) => (o, succ)
  | none => (((certOf j).cutAt (i + 1)).J, [])

/-- What `partEnd` checks of a window of one part beyond its walk's end: an entered next window
starts at its first arm. -/
noncomputable def nextOk (j i : ℕ) : Bool :=
  match partEnt j (i + 1) 0 with
  | some (_, succ) => !succ.isEmpty && Nat.beq (partJ j (i + 1) 0) (succ.headD 0)
  | none => true

theorem partEnd_one {j i : ℕ} (h1 : nParts j i = 1) (hi : i < (certOf j).cuts.length) {r : RC}
    (h : partEnd j i 0 r = true) :
    nextOk j i = true ∧ ∃ p, armEnd (nextTgt j i).1 (nextTgt j i).2 r = some p ∧
      Good (partC j (i + 1) 0) (partU j (i + 1) 0) p := by
  have hn : Nat.blt (0 + 1) (nParts j i) = false := by rw [h1]; rfl
  unfold nextOk nextTgt
  cases r with
  | join J c u =>
    simp only [partEnd, hn, Bool.cond_false, Bool.and_eq_true, Nat.beq_eq,
      Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨-, rfl⟩, hpe⟩, hc⟩, hu⟩ := h
    simp only [hpe]
    exact ⟨by simp, (c, u), by simp [armEnd], hc, hu⟩
  | chain o succ c u =>
    simp only [partEnd, hn, Bool.cond_false, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, Nat.beq_eq] at h
    obtain ⟨hne, ⟨⟨⟨⟨-, hpe⟩, hj⟩, hc⟩, hu⟩⟩ := h
    simp only [hpe, hne, Bool.not_false, Bool.true_and, hj, Nat.beq_refl]
    refine ⟨by simp, (c, u), ?_, hc, hu⟩
    simp [armEnd, hne]
  | mid J m c u => simp [partEnd, hn] at h
  | done =>
    simp only [partEnd, hn, Bool.not_false, Bool.true_and, Bool.not_eq_true'] at h
    rw [Nat.blt_eq.mpr hi] at h; cases h
  | fail e => simp [partEnd] at h

theorem partEnd_of_one {j i : ℕ} (h1 : nParts j i = 1) (hi : i < (certOf j).cuts.length)
    (hn : nextOk j i = true) {r : RC} {p : Cnt × ℕ}
    (ha : armEnd (nextTgt j i).1 (nextTgt j i).2 r = some p)
    (hg : Good (partC j (i + 1) 0) (partU j (i + 1) 0) p) : partEnd j i 0 r = true := by
  have hb : Nat.blt (0 + 1) (nParts j i) = false := by rw [h1]; rfl
  have hi' : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hi
  unfold nextOk at hn
  unfold nextTgt at ha
  obtain ⟨hc, hu⟩ := hg
  cases hpe : partEnt j (i + 1) 0 with
  | none =>
    rw [hpe] at ha
    obtain ⟨c, u⟩ := p
    obtain ⟨rfl, rfl⟩ := armEnd_join ha
    simp only [partEnd, hb, hi', Bool.cond_false, hpe, Option.isNone_none, Nat.beq_refl, hc, hu,
      Bool.and_self]
  | some q =>
    obtain ⟨o, succ⟩ := q
    rw [hpe] at ha hn
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hn
    obtain ⟨hne, hj⟩ := hn
    have hne' : succ ≠ [] := fun h ↦ by rw [h] at hne; cases hne
    obtain ⟨c, u⟩ := p
    obtain rfl := armEnd_chain hne' ha
    simp only [partEnd, hb, hi', Bool.cond_false, hpe, hne, Bool.not_false, hj,
      Nat.beq_refl, hc, hu, Bool.and_self, decide_true]

/-- **A completeness window of one `match` from its groups**: groups covering every arm, each
passing `cplWinS`, give the window's `cplWin`. -/
theorem cplWin_of_split {j i : ℕ} (gs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ))
    (g0 : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (hg0 : g0 ∈ gs)
    (hcov : coverOk (gs.map fun g ↦ (g.1, g.2.1)) (partStmts j i 0) = true)
    (hpre : (winOkC j i && Nat.ble (partS j i 0) ((certOf j).stmtsAt (coreOf j) i).length &&
      (bif lastPart j i 0 then lastOkC (partStmts j i 0) else Stmt.noRetList (partStmts j i 0)) &&
      cplFits (certOf j) i) = true)
    (h : ∀ g ∈ gs, cplWinS j i g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 = true) :
    cplWin j i 0 = true := by
  obtain ⟨v, a0, as, hss⟩ : ∃ v a0 as, partStmts j i 0 = [.match_ v (a0 :: as)] := by
    revert hcov
    unfold coverOk
    split
    · rename_i v a0 as heq
      exact fun _ ↦ ⟨v, a0, as, by assumption⟩
    · simp
  have hcov' : ∀ e < as.length, ∃ g ∈ gs, g.1 ≤ e + 1 ∧ e + 1 < g.2.1 := by
    intro e he
    rw [hss] at hcov
    simp only [coverOk, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
      Nat.ble_eq, Nat.blt_eq] at hcov
    obtain ⟨g', hg', h1, h2⟩ := hcov e he
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨g, hg, h1, h2⟩
  simp only [Bool.and_eq_true] at hpre
  obtain ⟨⟨⟨hwin, hps⟩, hlast⟩, hfit⟩ := hpre
  unfold cplWin
  simp only [Nat.beq_refl, Bool.cond_true, hwin, hps, hlast, Bool.true_and]
  rcases hR : execWinCS (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
    (((certOf j).succAt i).drop 1) ((certOf j).endAt (fnOf j) i) with ⟨segs, dead⟩
  -- the context on cells `L`
  set cx := fun L ↦ cxOf j (index segs) L (statT (fsN j) (plumbOf j).stat .nil) (plumbOf j).nv
    (stopOf j i 0) with hcx
  set cg := fun (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) ↦
    clocG (certOf j) i g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 with hcg
  -- each group's facts
  have hG : ∀ g ∈ gs, nParts j i = 1 ∧ partM j i 0 = 0 ∧ i < (certOf j).cuts.length ∧
      matchAtoms g.1 g.2.1 [.match_ v (a0 :: as)] = true ∧
      (∀ x ∈ stmtsVals (selStmts g.1 g.2.1 [.match_ v (a0 :: as)]),
        ((cg g).get? x.idx).isSome = true) ∧ nextSelOk (cx (cg g)) v = true ∧
      ∃ s, getF (index segs) (partJ j i 0) = some s ∧ s.start = partJ j i 0 ∧
        partEnd j i 0 (cwSplit (cx (cg g)) g.1 g.2.1 (partEnt j i 0) v (a0 :: as)
          ⟨s, s.items, .nil, [], [], [], partC j i 0, partU j i 0, some (partJ j i 0), 0⟩) = true := by
    intro g hg
    have hc := h g hg
    unfold cplWinS at hc
    rw [hss, hR] at hc
    simp only [listSeq_eq, Exec.Trie.seq_eq, CLoc.seq_eq, Cnt.seq_eq, natSeq_eq, Bool.and_eq_true,
      Nat.beq_eq, Nat.blt_eq, List.all_eq_true] at hc
    obtain ⟨⟨⟨hn, hm⟩, hi⟩, hma, ⟨hvals, hnx⟩, hend⟩ := hc
    refine ⟨hn, hm, hi, hma, hvals, hnx, ?_⟩
    split at hend
    · rename_i s hs
      simp only [Bool.cond_eq_ite, Nat.beq_eq] at hend
      split_ifs at hend with hst
      exact ⟨s, hs, hst, hend⟩
    · simp at hend
  obtain ⟨hn, hm, hi, -, -, -, s, hs, hst, hend0⟩ := hG g0 hg0
  -- the window's walk
  unfold cplRes
  rw [hR]
  simp only [listSeq_eq, Exec.Trie.seq_eq, CLoc.seq_eq, Cnt.seq_eq, natSeq_eq, hm, hs, hst,
    Nat.beq_refl, Bool.cond_true, List.drop_zero, hss]
  have hfile : fileB (clocW (certOf j) i) (fsN j) [.match_ v (a0 :: as)] .nil = .nil := rfl
  rw [hfile]
  -- the groups' cells agree with the window's
  have hag : ∀ g ∈ gs, ∀ x, ((cg g).get? x).isSome = true → (cg g).get? x = (clocW (certOf j) i).get? x := by
    intro g hg x hx
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
    rw [hc, clocG_get hfit hc]
  have hsel : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      ∀ x ∈ stmtsVals as[e], x ∈ stmtsVals (selStmts g.1 g.2.1 [.match_ v (a0 :: as)]) := by
    intro g _ e he hlo hhi x hx
    simp only [selStmts, stmtsVals, stmtVals, armsVals, List.mem_cons, List.mem_append, List.append_nil]
    refine Or.inr (Or.inr (mem_armsVals_of (as := selArms g.1 g.2.1 1 as) (e := e)
      (by rw [length_selArms]; exact he) ?_))
    rw [getElem_selArms g.1 g.2.1 1 as e he (by omega) (by omega)]
    exact hx
  have hatoms : ∀ g ∈ gs, a0.all isAtomS = true ∧ ∀ e (he : e < as.length), g.1 ≤ e + 1 →
      e + 1 < g.2.1 → as[e].all isAtomS = true := by
    intro g hg
    obtain ⟨-, -, -, hma, -⟩ := hG g hg
    simp only [matchAtoms, Bool.and_eq_true, List.all_eq_true] at hma
    refine ⟨List.all_eq_true.mpr hma.1, fun e he hlo hhi ↦ ?_⟩
    have := hma.2 _ (List.getElem_mem (l := selArms g.1 g.2.1 1 as) (n := e)
      (by rw [length_selArms]; exact he))
    rw [getElem_selArms g.1 g.2.1 1 as e he (by omega) (by omega)] at this
    exact List.all_eq_true.mpr this
  -- the groups as `cw_of_groups` and `cwE_of_groups` take them
  have hval : ∀ g ∈ gs, ∀ x ∈ stmtsVals (selStmts g.1 g.2.1 [.match_ v (a0 :: as)]),
      (cg g).get? x.idx = (clocW (certOf j) i).get? x.idx := fun g hg x hx ↦
    hag g hg x.idx ((hG g hg).2.2.2.2.1 x hx)
  have gs0 : (g0.1, g0.2.1, cg g0) ∈ gs.map (fun g ↦ (g.1, g.2.1, cg g)) := List.mem_map.mpr ⟨g0, hg0, rfl⟩
  have hcov2 : ∀ e < as.length, ∃ g ∈ gs.map (fun g ↦ (g.1, g.2.1, cg g)), g.1 ≤ e + 1 ∧
      e + 1 < g.2.1 := fun e he ↦ by
    obtain ⟨g, hg, h1, h2⟩ := hcov' e he
    exact ⟨_, List.mem_map.mpr ⟨g, hg, rfl⟩, h1, h2⟩
  have has2 : ∀ g ∈ gs.map (fun g ↦ (g.1, g.2.1, cg g)), ∀ e (he : e < as.length),
      g.1 ≤ e + 1 → e + 1 < g.2.1 → as[e].all isAtomS = true := fun g' hg' ↦ by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'; exact (hatoms g hg).2
  have hv2 : ∀ g ∈ gs.map (fun g ↦ (g.1, g.2.1, cg g)), g.2.2.get? v.idx =
      (clocW (certOf j) i).get? v.idx := fun g' hg' ↦ by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact hval g hg v (by simp [selStmts, stmtsVals, stmtVals])
  have h0v2 : ∀ g ∈ gs.map (fun g ↦ (g.1, g.2.1, cg g)), ∀ x ∈ stmtsVals a0,
      g.2.2.get? x.idx = (clocW (certOf j) i).get? x.idx := fun g' hg' x hx ↦ by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact hval g hg x (by simp [selStmts, stmtsVals, stmtVals, armsVals, hx])
  have hav2 : ∀ g ∈ gs.map (fun g ↦ (g.1, g.2.1, cg g)), ∀ e (he : e < as.length),
      g.1 ≤ e + 1 → e + 1 < g.2.1 → ∀ x ∈ stmtsVals as[e],
        g.2.2.get? x.idx = (clocW (certOf j) i).get? x.idx := fun g' hg' e he hlo hhi x hx ↦ by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact hval g hg x (hsel g hg e he hlo hhi x hx)
  have hy2 : ∀ g ∈ gs.map (fun g ↦ (g.1, g.2.1, cg g)), ∀ ts y b,
      chainOf (cx (clocW (certOf j) i)) v.idx = some (ts, y, b) →
        g.2.2.get? y = (clocW (certOf j) i).get? y := fun g' hg' ts y b hc ↦ by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    have hnx := (hG g hg).2.2.2.2.2.1
    unfold nextSelOk at hnx
    rw [show chainOf (cx (cg g)) v.idx = chainOf (cx (clocW (certOf j) i)) v.idx from rfl, hc] at hnx
    exact hag g hg y hnx
  cases hpe : partEnt j i 0 with
  | none =>
    rw [hpe] at hend0
    obtain ⟨hnx, -⟩ := partEnd_one hn hi hend0
    obtain ⟨p, hp, hgood⟩ := cw_of_groups (cx (clocW (certOf j) i)) v a0 as _
      (gs.map fun g ↦ (g.1, g.2.1, cg g)) _ gs0 hcov2 (hatoms g0 hg0).1 has2 hv2 h0v2 hav2 hy2
      (J := (nextTgt j i).1) (sc := (nextTgt j i).2) (B := partC j (i + 1) 0) (U := partU j (i + 1) 0)
      (fun g' hg' ↦ by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
        obtain ⟨-, -, -, -, -, -, s', hs', -, hend⟩ := hG g hg
        obtain rfl := Option.some.inj (hs'.symm.trans hs)
        rw [hpe] at hend
        exact (partEnd_one hn hi hend).2)
    exact partEnd_of_one hn hi hnx hp hgood
  | some q =>
    obtain ⟨o, succ⟩ := q
    rw [hpe] at hend0
    obtain ⟨hnx, -⟩ := partEnd_one hn hi hend0
    obtain ⟨p, hp, hgood⟩ := cwE_of_groups (cx (clocW (certOf j) i)) o succ _ v a0 as
      (gs.map fun g ↦ (g.1, g.2.1, cg g)) _ gs0 hcov2 (hatoms g0 hg0).1 has2 hv2 h0v2 hav2 hy2
      (J := (nextTgt j i).1) (sc := (nextTgt j i).2) (B := partC j (i + 1) 0) (U := partU j (i + 1) 0)
      (fun g' hg' ↦ by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
        obtain ⟨-, -, -, -, -, -, s', hs', -, hend⟩ := hG g hg
        obtain rfl := Option.some.inj (hs'.symm.trans hs)
        rw [hpe] at hend
        exact (partEnd_one hn hi hend).2)
    exact partEnd_of_one hn hi hnx hp hgood

end
end LeanVM.Guest.B2C
