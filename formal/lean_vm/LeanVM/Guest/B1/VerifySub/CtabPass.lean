/-
  LeanVM.Guest.B1.VerifySub.CtabPass

  Monomials in six challenges: a kernel-evaluated pass over a block of atoms records each value's
  and each cell's exponents, sound for every valuation of the block.
-/

module

public import LeanVM.Guest.B1.VerifySub.Template

/-!
# Monomials in the ring map's challenges

`c_table`'s section (G:3454-3462) computes, from `1` and the six challenges at `chs`, products and
squares, each stored in or read from the table at `665`. A monomial `Π_i chs_i^(e_i)` is its six
exponents `e` (`evVal`); a product adds them (`evAdd`).

`ctRun st block` walks the block, keeping each value's exponents (`vars`) and each table cell's
(`mem`): a constant `1`, a challenge read at `664`, a product, and a table cell read (a cell
already known gives the value, an unknown cell is the value's). `ctRun_sound`: if the block holds,
every recorded value and cell is its monomial (`CtOk`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The monomial of exponents `e` in the six challenges `chs`. -/
def evVal (chs : List E) (e : List ℕ) : E := ∏ i ∈ range 6, chs.getD i 0 ^ e.getD i 0

/-- Challenge `i`'s exponents. -/
def evUnit (i : ℕ) : List ℕ := (List.range 6).map fun j ↦ if j = i then 1 else 0

/-- A product's exponents. -/
def evAdd (a b : List ℕ) : List ℕ := List.zipWith (· + ·) a b

theorem evUnit_getD {i j : ℕ} (hj : j < 6) : (evUnit i).getD j 0 = if j = i then 1 else 0 := by
  rw [evUnit, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

theorem evVal_unit (chs : List E) {i : ℕ} (hi : i < 6) : evVal chs (evUnit i) = chs.getD i 0 := by
  unfold evVal
  rw [Finset.prod_eq_single_of_mem i (mem_range.2 hi) fun j hj hji ↦ by
    simp only [evUnit_getD (mem_range.1 hj), hji, ↓reduceIte, pow_zero]]
  rw [evUnit_getD hi]
  simp

theorem evVal_zero (chs : List E) : evVal chs (List.replicate 6 0) = 1 := by
  unfold evVal
  refine Finset.prod_eq_one fun i hi ↦ ?_
  rw [List.getD_eq_getElem (List.replicate 6 0) _ (by simpa using hi), List.getElem_replicate,
    pow_zero]

theorem evAdd_length {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) :
    (evAdd a b).length = 6 := by simp [evAdd, ha, hb]

theorem evVal_add (chs : List E) {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) :
    evVal chs (evAdd a b) = evVal chs a * evVal chs b := by
  unfold evVal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.1 hi
  rw [← pow_add, List.getD_eq_getElem (evAdd a b) _ (by rw [evAdd_length ha hb]; exact hi'),
    List.getD_eq_getElem a _ (by omega), List.getD_eq_getElem b _ (by omega)]
  simp only [evAdd, List.getElem_zipWith]

/-- The pass's state: each value's exponents, each table cell's. -/
structure CtSt where
  vars : List (V × List ℕ)
  mem : List (ℕ × List ℕ)

/-- One atom of the pass. -/
def ctStep (st : CtSt) : Stmt → Option CtSt
  | .atom (.const d c) =>
      if eEqb c (word 1 0 0) then some ⟨(d, List.replicate 6 0) :: st.vars, st.mem⟩ else none
  | .atom (.load d p off) =>
      if p = .n 664 then
        if off < 6 then some ⟨(d, evUnit off) :: st.vars, st.mem⟩ else none
      else if p = .n 665 then
        match st.mem.lookup off with
        | some e => some ⟨(d, e) :: st.vars, st.mem⟩
        | none =>
          match st.vars.lookup d with
          | some e => some ⟨st.vars, (off, e) :: st.mem⟩
          | none => none
      else none
  | .atom (.mul d a b) =>
      match st.vars.lookup a, st.vars.lookup b with
      | some ea, some eb => some ⟨(d, evAdd ea eb) :: st.vars, st.mem⟩
      | _, _ => none
  | _ => none

/-- The pass over a block. -/
def ctRun : CtSt → List Stmt → Option CtSt
  | st, [] => some st
  | st, s :: ss =>
      match ctStep st s with
      | some st' => ctRun st' ss
      | none => none

/-- Every recorded value and table cell is its monomial. -/
def CtOk (chs : List E) (rd : Reader) (σ : Val) (st : CtSt) : Prop :=
  (∀ p ∈ st.vars, σ p.1 = evVal chs p.2 ∧ p.2.length = 6) ∧
    ∀ p ∈ st.mem, LoadHolds rd (σ (.n 665)) p.1 (evVal chs p.2) ∧ p.2.length = 6

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {e : β}, l.lookup k = some e → (k, e) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: l, k, e, h => by
    by_cases hk : k = a
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · simp only [List.lookup, beq_eq_false_iff_ne.mpr hk] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem ctStep_sound {chs : List E} (hcl : chs.length = 6) (hc : ReadsAt rd (σ (.n 664)) chs)
    {st st' : CtSt} {s : Stmt} (hs : ctStep st s = some st') (hok : CtOk chs rd σ st)
    {next : Prop} {kret : List E → Prop} (h : Stmt.Holds C rd σ s next kret) :
    CtOk chs rd σ st' ∧ next := by
  obtain ⟨hv, hm⟩ := hok
  match s, hs with
  | .atom (.const d c), hs =>
    simp only [ctStep] at hs
    split at hs
    · rename_i hc1
      cases hs
      obtain ⟨hd, hn⟩ := h
      refine ⟨⟨fun p hp ↦ ?_, hm⟩, hn⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only [Atom.Holds] at hd
        rw [hd, eEqb_sound hc1, word_one, evVal_zero]
        exact ⟨rfl, by simp⟩
      · exact hv p hp
    · cases hs
  | .atom (.load d p off), hs =>
    simp only [ctStep] at hs
    obtain ⟨hd, hn⟩ := h
    simp only [Atom.Holds] at hd
    split at hs
    · rename_i hp
      subst hp
      split at hs
      · rename_i hoff
        cases hs
        refine ⟨⟨fun q hq ↦ ?_, hm⟩, hn⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · refine ⟨?_, by simp [evUnit]⟩
          rw [evVal_unit chs hoff, loadHolds_unique hd (hc off (by omega)),
            List.getD_eq_getElem _ _ (by omega)]
        · exact hv q hq
      · cases hs
    · split at hs
      · rename_i _ hp
        subst hp
        split at hs
        · rename_i e he
          cases hs
          obtain ⟨hme, hel⟩ := hm _ (lookup_mem he)
          refine ⟨⟨fun q hq ↦ ?_, hm⟩, hn⟩
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ⟨loadHolds_unique hd hme, hel⟩
          · exact hv q hq
        · split at hs
          · rename_i e he
            cases hs
            obtain ⟨hve, hel⟩ := hv _ (lookup_mem he)
            refine ⟨⟨hv, fun q hq ↦ ?_⟩, hn⟩
            rcases List.mem_cons.1 hq with rfl | hq
            · refine ⟨?_, hel⟩
              rw [← hve]; exact hd
            · exact hm q hq
          · cases hs
      · cases hs
  | .atom (.mul d a b), hs =>
    simp only [ctStep] at hs
    split at hs
    · rename_i ea eb ha hb
      cases hs
      obtain ⟨hd, hn⟩ := h
      simp only [Atom.Holds] at hd
      obtain ⟨hva, hla⟩ := hv _ (lookup_mem ha)
      obtain ⟨hvb, hlb⟩ := hv _ (lookup_mem hb)
      refine ⟨⟨fun q hq ↦ ?_, hm⟩, hn⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨by rw [hd, hva, hvb, evVal_add chs hla hlb], evAdd_length hla hlb⟩
      · exact hv q hq
    · cases hs

/-- **The pass is sound**: from a sound start, if the block holds, every value and cell the pass
records is its monomial. -/
theorem ctRun_sound {chs : List E} (hcl : chs.length = 6) (hc : ReadsAt rd (σ (.n 664)) chs) :
    ∀ {st st' : CtSt} {ss : List Stmt}, ctRun st ss = some st' → CtOk chs rd σ st →
      ∀ {next : Prop} {kret : List E → Prop}, Stmt.HoldsList C rd σ ss next kret →
        CtOk chs rd σ st' ∧ next
  | st, st', [], hr, hok, _, _, h => by
    simp only [ctRun, Option.some.injEq] at hr
    subst hr; exact ⟨hok, h⟩
  | st, st', s :: ss, hr, hok, next, kret, h => by
    simp only [ctRun] at hr
    split at hr
    · rename_i st1 h1
      obtain ⟨hok1, hrest⟩ := ctStep_sound hcl hc h1 hok h
      exact ctRun_sound hcl hc hr hok1 hrest
    · cases hr

end
end LeanVM.Guest.B1.VerifySub
