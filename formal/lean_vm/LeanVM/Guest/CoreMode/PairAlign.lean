/-
  LeanVM.Guest.CoreMode.PairAlign

  A function passing its pairing passes its alignment check: the pairing's pass is the alignment's with its zippers
  normalized less far.
-/

module

public import LeanVM.Guest.CoreMode.PairRun

/-!
# The pairing gives the alignment

The pairing (`pairOk`) is the alignment pass (`Bridge.alignOk`) with the heap events: its normalizations stop at more
atoms (`stopL`, `stopS`, each stopping at every flow hint), its `DEREF`s consume `load`s the alignment skips, and it
checks the oracle besides. So its pass simulates the alignment's (`pairGo_sim`): at each offset the alignment's
zipper is the pairing's normalized (`Rz`), the arrivals pending at the same offsets, the same table jumps registered.

The alignment's one normalization covers several of the pairing's, so its fuel must last: a normalization step
shrinks the zipper's size (`zSize`, the statements left, nested ones included), which no step of the pass grows, so
a body smaller than the fuel (`blkSize body < X.fuel`) suffices. `alignOk_of_pairOk`.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Bridge
open LeanVM.Guest.Exec (natSeq natSeq_eq)

@[expose] public section

/-- The statements of a block, nested ones included: by the recursor, for the kernel. -/
noncomputable def blkSize : List Stmt → ℕ :=
  Stmt.rec_1 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun _ ↦ 1) (fun _ _ _ hz hn ↦ hz + hn + 1) (fun _ _ ha ↦ ha + 1) (fun _ _ _ ↦ 1) (fun _ _ _ ↦ 1)
    (fun _ _ _ _ ↦ 1) (fun _ ↦ 1) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

end

/-! ## Sizes -/

/-- `blkSize` of a statement. -/
noncomputable def stSize : Stmt → ℕ :=
  Stmt.rec (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun _ ↦ 1) (fun _ _ _ hz hn ↦ hz + hn + 1) (fun _ _ ha ↦ ha + 1) (fun _ _ _ ↦ 1) (fun _ _ _ ↦ 1)
    (fun _ _ _ _ ↦ 1) (fun _ ↦ 1) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

/-- `blkSize` of arms. -/
noncomputable def armSize : List (List Stmt) → ℕ :=
  Stmt.rec_2 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun _ ↦ 1) (fun _ _ _ hz hn ↦ hz + hn + 1) (fun _ _ ha ↦ ha + 1) (fun _ _ _ ↦ 1) (fun _ _ _ ↦ 1)
    (fun _ _ _ _ ↦ 1) (fun _ ↦ 1) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

theorem blkSize_nil : blkSize [] = 0 := rfl

theorem blkSize_cons (s : Stmt) (ss : List Stmt) : blkSize (s :: ss) = stSize s + blkSize ss := rfl

theorem armSize_getD : ∀ (arms : List (List Stmt)) (c : ℕ), blkSize (arms.getD c []) ≤ armSize arms
  | [], _ => by simp [blkSize_nil]
  | a :: as, 0 => by
    change blkSize a ≤ blkSize a + armSize as
    omega
  | a :: as, c + 1 => by
    have := armSize_getD as c
    change blkSize (as.getD c []) ≤ blkSize a + armSize as
    omega

theorem subBlock_size (s : Stmt) (c : ℕ) : blkSize (subBlock s c) + 1 ≤ stSize s := by
  cases s with
  | ite x zb nb =>
    change blkSize (bif Nat.beq c 0 then zb else nb) + 1 ≤ blkSize zb + blkSize nb + 1
    cases Nat.beq c 0 <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
  | match_ x arms =>
    change blkSize (arms.getD c []) + 1 ≤ armSize arms + 1
    have := armSize_getD arms c
    omega
  | _ => exact Nat.le_refl 1

/-- **The size of a zipper**: the statements left, nested ones included, a level for each enclosing block. -/
noncomputable def zSize (z : Zip) : ℕ := blkSize z.cur + (z.up.map fun e ↦ blkSize e.2.2 + 1).sum

theorem zSize_next {z : Zip} {s : Stmt} {ss : List Stmt} (h : z.cur = s :: ss) :
    zSize (z.next ss) + stSize s = zSize z := by
  obtain ⟨up, k, cur⟩ := z
  simp only at h
  subst h
  simp only [Zip.next_eq, zSize, blkSize_cons]
  omega

theorem zSize_enter {z : Zip} {s : Stmt} {ss : List Stmt} (h : z.cur = s :: ss) (c : ℕ) :
    zSize (z.enter s ss c) ≤ zSize z := by
  obtain ⟨up, k, cur⟩ := z
  simp only at h
  subst h
  have := subBlock_size s c
  simp only [Zip.enter, zSize, blkSize_cons, List.map_cons, List.sum_cons]
  omega

/-! ## The normalization, step by step -/

/-- **One step of a normalization stopping at `stop`**: the zipper past the head atom or out of the finished
block, or none where it stops. -/
def skip1 (stop : Atom → Bool) : Zip → Option Zip
  | ⟨up, k, .atom a :: ss⟩ => bif stop a then none else some ⟨up, k + 1, ss⟩
  | ⟨(k', _, ss) :: up, _, []⟩ => some ⟨up, k' + 1, ss⟩
  | _ => none

theorem normStepG_eq (stop : Atom → Bool) (r : Zip → Option Zip) (z : Zip) :
    normStepG stop r z = (skip1 stop z).elim (some z) r := by
  obtain ⟨up, k, cur⟩ := z
  cases cur with
  | nil =>
    cases up with
    | nil => rfl
    | cons e up => obtain ⟨k', c, ss⟩ := e; simp [normStepG, skip1, natSeq_eq]
  | cons s ss =>
    cases s
    case atom a => cases h : stop a <;> simp [normStepG, skip1, h, natSeq_eq]
    all_goals rfl

theorem normG_succ' (stop : Atom → Bool) (f : ℕ) (z : Zip) :
    normG stop (f + 1) z = (skip1 stop z).elim (some z) (normG stop f) :=
  normStepG_eq stop _ z

theorem normZ_eq_normG : ∀ f, normZ f = normG flowAtom f
  | 0 => rfl
  | f + 1 => by
    funext z
    rw [normG_succ', ← normZ_eq_normG f]
    change normStep (normZ f) z = _
    obtain ⟨up, k, cur⟩ := z
    cases cur with
    | nil =>
      cases up with
      | nil => rfl
      | cons e up => obtain ⟨k', c, ss⟩ := e; simp [normStep, skip1, natSeq_eq]
    | cons s ss =>
      cases s
      case atom a => cases h : flowAtom a <;> simp [normStep, skip1, h, natSeq_eq]
      all_goals rfl

theorem skip1_size {stop : Atom → Bool} {z z' : Zip} (h : skip1 stop z = some z') : zSize z' < zSize z := by
  obtain ⟨up, k, cur⟩ := z
  cases cur with
  | nil =>
    cases up with
    | nil => cases h
    | cons e up =>
      obtain ⟨k', c, ss⟩ := e
      cases h
      simp only [zSize, blkSize_nil, List.map_cons, List.sum_cons]
      omega
  | cons s ss =>
    cases s
    case atom a =>
      cases hs : stop a <;> simp only [skip1, hs, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
      subst h
      simp only [zSize, blkSize_cons]
      have : 1 ≤ stSize (.atom a) := Nat.le_refl 1
      omega
    all_goals cases h

theorem skip1_mono {stop stop' : Atom → Bool} (hst : ∀ a, stop a = false → stop' a = false) {z z' : Zip}
    (h : skip1 stop z = some z') : skip1 stop' z = some z' := by
  obtain ⟨up, k, cur⟩ := z
  cases cur with
  | nil => cases up with
    | nil => cases h
    | cons e up => exact h
  | cons s ss =>
    cases s
    case atom a =>
      cases hs : stop a <;> simp only [skip1, hs, Bool.cond_true, Bool.cond_false, reduceCtorEq] at h
      simp only [skip1, hst a hs, Bool.cond_false]
      exact h
    all_goals cases h

theorem skip1_atom {stop : Atom → Bool} {z : Zip} {a : Atom} {ss : List Stmt} (h : z.cur = .atom a :: ss) :
    skip1 stop z = bif stop a then none else some (z.next ss) := by
  obtain ⟨up, k, cur⟩ := z
  simp only at h
  subst h
  rw [Zip.next_eq]
  rfl

/-- A normalization's result is where it stops, no larger. -/
theorem normG_some {stop : Atom → Bool} : ∀ {f : ℕ} {z w : Zip}, normG stop f z = some w →
    skip1 stop w = none ∧ zSize w ≤ zSize z
  | 0, _, _, h => by cases h
  | f + 1, z, w, h => by
    rw [normG_succ'] at h
    cases hs : skip1 stop z with
    | none => rw [hs] at h; cases h; exact ⟨hs, Nat.le_refl _⟩
    | some z' =>
      rw [hs] at h
      obtain ⟨h1, h2⟩ := normG_some h
      exact ⟨h1, Nat.le_trans h2 (Nat.le_of_lt (skip1_size hs))⟩

theorem normG_stop {stop : Atom → Bool} {w : Zip} (h : skip1 stop w = none) (f : ℕ) :
    normG stop (f + 1) w = some w := by
  rw [normG_succ', h]
  rfl

theorem normG_total (stop : Atom → Bool) : ∀ (f : ℕ) (z : Zip), zSize z < f → ∃ w, normG stop f z = some w
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, z, h => by
    rw [normG_succ']
    cases hs : skip1 stop z with
    | none => exact ⟨z, rfl⟩
    | some z' => exact normG_total stop f z' (by have := skip1_size hs; omega)

theorem normG_fuel (stop : Atom → Bool) : ∀ (f g : ℕ) (z : Zip), zSize z < f → zSize z < g →
    normG stop f z = normG stop g z
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, z, hf, hg => by
    rw [normG_succ', normG_succ']
    cases hs : skip1 stop z with
    | none => rfl
    | some z' =>
      have := skip1_size hs
      exact normG_fuel stop f g z' (by omega) (by omega)

theorem normG_skip {stop : Atom → Bool} {F : ℕ} {z z' : Zip} (hs : skip1 stop z = some z') (hz : zSize z < F) :
    normG stop F z = normG stop F z' := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have := skip1_size hs
  rw [normG_succ', hs]
  exact normG_fuel stop F (F + 1) z' (by omega) (by omega)

/-- **A normalization stopping at more atoms, then one stopping at fewer**, is the latter. -/
theorem normG_comp {stop stop' : Atom → Bool} (hst : ∀ a, stop a = false → stop' a = false) {F : ℕ} :
    ∀ {g : ℕ} {z w : Zip}, normG stop g z = some w → zSize z < F → normG stop' F z = normG stop' F w
  | 0, _, _, h, _ => by cases h
  | g + 1, z, w, h, hz => by
    rw [normG_succ'] at h
    cases hs : skip1 stop z with
    | none => rw [hs] at h; cases h; rfl
    | some z' =>
      rw [hs] at h
      rw [normG_skip (skip1_mono hst hs) hz]
      exact normG_comp hst h (Nat.lt_trans (skip1_size hs) hz)

theorem stopL_flow (a : Atom) (h : stopL a = false) : flowAtom a = false := by
  simp only [stopL, Bool.or_eq_false_iff] at h
  exact h.1

theorem stopS_flow (R : Exec.Trie (List (ℕ × ℕ × Wit))) (a : Atom) (h : stopS R a = false) : flowAtom a = false := by
  simp only [stopS, Bool.or_eq_false_iff] at h
  exact h.1

/-! ## The simulation -/

/-- **The alignment's zipper is the pairing's normalized**, within the fuel. -/
def Rz (F : ℕ) (zp za : Zip) : Prop := zSize zp < F ∧ normG flowAtom F zp = some za

theorem Rz.self {F : ℕ} {zp za : Zip} (h : Rz F zp za) : normG flowAtom F za = some za := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by have := h.1; omega⟩
  exact normG_stop (normG_some h.2).1 F

theorem norm_sim {stop : Atom → Bool} (hst : ∀ a, stop a = false → flowAtom a = false) {g F : ℕ} {z w : Zip}
    (h : normG stop g z = some w) (hz : zSize z < F) : ∃ wa, normG flowAtom F z = some wa ∧ Rz F w wa := by
  have hw := (normG_some h).2
  obtain ⟨wa, hwa⟩ := normG_total flowAtom F w (by omega)
  exact ⟨wa, (normG_comp hst h hz).trans hwa, by omega, hwa⟩

theorem nL_sim (P : PairCtx) {z w : Zip} (h : P.nL z = some w) (hz : zSize z < P.X.fuel) :
    ∃ wa, normZ P.X.fuel z = some wa ∧ Rz P.X.fuel w wa := by
  rw [normZ_eq_normG]
  exact norm_sim stopL_flow h hz

/-- Arrivals pending at the same offsets, the alignment's zippers the pairing's normalized. -/
def PendR (F : ℕ) : List (ℕ × Zip) → List (ℕ × Zip) → Prop
  | [], [] => True
  | p :: l, q :: m => p.1 = q.1 ∧ Rz F p.2 q.2 ∧ PendR F l m
  | _, _ => False

/-- The zipper falling through, both or neither. -/
def OptR (F : ℕ) : Option Zip → Option Zip → Prop
  | none, none => True
  | some a, some b => Rz F a b
  | _, _ => False

/-- What a step hands on, related. -/
def OutR (F : ℕ) (r ra : Option Zip × List (ℕ × Zip)) : Prop := OptR F r.1 ra.1 ∧ PendR F r.2 ra.2

theorem PendR.offs {F : ℕ} : ∀ {l m : List (ℕ × Zip)}, PendR F l m → l.map Prod.fst = m.map Prod.fst
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.map_cons, h.1, PendR.offs h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem insP_sim {F : ℕ} {a b : ℕ × Zip} (hab : a.1 = b.1 ∧ Rz F a.2 b.2) :
    ∀ {l m : List (ℕ × Zip)}, PendR F l m → PendR F (insP a l) (insP b m)
  | [], [], _ => ⟨hab.1, hab.2, trivial⟩
  | p :: l, q :: m, h => by
    change PendR F (bif Nat.blt p.1 a.1 then p :: insP a l else a :: p :: l)
      (bif Nat.blt q.1 b.1 then q :: insP b m else b :: q :: m)
    rw [← h.1, ← hab.1]
    cases Nat.blt p.1 a.1
    · exact ⟨hab.1, hab.2, h⟩
    · exact ⟨h.1, h.2.1, insP_sim hab h.2.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem mergeP_sim {F : ℕ} : ∀ {as bs l m : List (ℕ × Zip)}, PendR F as bs → PendR F l m →
    PendR F (mergeP as l) (mergeP bs m)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, ha, h => insP_sim ⟨ha.1, ha.2.1⟩ (mergeP_sim ha.2.2 h)
  | [], _ :: _, _, _, ha, _ => ha.elim
  | _ :: _, [], _, _, ha, _ => ha.elim

theorem spanP_sim {F : ℕ} (i : ℕ) : ∀ {l m : List (ℕ × Zip)}, PendR F l m →
    PendR F (spanP i l).1 (spanP i m).1 ∧ PendR F (spanP i l).2 (spanP i m).2
  | [], [], _ => ⟨trivial, trivial⟩
  | p :: l, q :: m, h => by
    have ih := spanP_sim i h.2.2
    change PendR F (bif Nat.beq p.1 i then (match spanP i l with | (h, t) => (p :: h, t)) else ([], p :: l)).1
        (bif Nat.beq q.1 i then (match spanP i m with | (h, t) => (q :: h, t)) else ([], q :: m)).1 ∧
      PendR F (bif Nat.beq p.1 i then (match spanP i l with | (h, t) => (p :: h, t)) else ([], p :: l)).2
        (bif Nat.beq q.1 i then (match spanP i m with | (h, t) => (q :: h, t)) else ([], q :: m)).2
    rw [← h.1]
    cases Nat.beq p.1 i
    · exact ⟨trivial, h⟩
    · generalize spanP i l = S at ih ⊢
      generalize spanP i m = T at ih ⊢
      obtain ⟨_, _⟩ := S
      obtain ⟨_, _⟩ := T
      exact ⟨⟨h.1, h.2.1, ih.1⟩, ih.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A table jump registered depends on the arrivals' offsets alone. -/
theorem tabReg_offs (X : AlignCtx) (i : ℕ) (ins : OffsetInstruction) (z : Zip) {tg tg' : List (ℕ × Zip)}
    (h : tg.map Prod.fst = tg'.map Prod.fst) (tabs : List (ℕ × Zip × ℕ)) :
    tabReg X i ins z tg tabs = tabReg X i ins z tg' tabs := by
  have hm : minOff tg = minOff tg' := by
    simp only [minOff, ← List.foldr_map (f := Prod.fst) (g := fun o m ↦ Nat.min o m), h]
  cases tg with
  | nil => cases tg' with
    | nil => rfl
    | cons _ _ => cases h
  | cons a tg => cases tg' with
    | nil => cases h
    | cons b tg' =>
      unfold tabReg
      cases ins
      case jump oc od of =>
        generalize z.cur = zc
        cases zc with
        | nil => rfl
        | cons s ss => cases s <;> first | rfl | simp only [hm]
      all_goals rfl

theorem tabReg_nil (X : AlignCtx) (i : ℕ) (ins : OffsetInstruction) (z : Zip) (tabs : List (ℕ × Zip × ℕ)) :
    tabReg X i ins z [] tabs = tabs := by
  unfold tabReg
  split
  · rename_i heq; simp at heq
  · rfl

theorem tabReg_fwdJ {X : AlignCtx} {i oc od of : ℕ} (h : fwdJ X i oc od of = true) (z : Zip) (tg : List (ℕ × Zip))
    (tabs : List (ℕ × Zip × ℕ)) : tabReg X i (.jump oc od of) z tg tabs = tabs := by
  unfold tabReg
  generalize z.cur = zc
  cases zc with
  | nil => rfl
  | cons s ss => cases s <;> cases tg <;> first | rfl | simp [h]

/-! ## The steps -/

theorem hintsStepH_sim (P : PairCtx) : ∀ (hs : List Prover.Exec.Hint) {z za z2 : Zip}, zSize z < P.X.fuel →
    normG flowAtom P.X.fuel z = some za → hintsStepH P hs z = some z2 →
    ∃ z2a, hintsStep P.X hs za = some z2a ∧ Rz P.X.fuel z2 z2a
  | [], _, za, _, hz, hza, h => by cases h; exact ⟨za, rfl, hz, hza⟩
  | hd :: hs, z, za, z2, hz, hza, h => by
    change hintStepH P (hintsStepH P hs) hd z = some z2 at h
    change ∃ z2a, hintStep P.X (hintsStep P.X hs) hd za = some z2a ∧ _
    simp only [hintStepH, hintStep, Bool.cond_eq_ite] at h ⊢
    split at h
    · rename_i hf
      rw [ite_eq_left hf]
      obtain ⟨zs, hzs, h⟩ := Option.bind_eq_some_iff.mp h
      change normG (stopS P.R) P.X.fuel z = some zs at hzs
      obtain ⟨hst, hle⟩ := normG_some hzs
      split at h
      · rename_i hc ss heq
        rw [skip1_atom heq] at hst
        have hfl : flowAtom (.hint hc) = true := by
          revert hst; simp [stopS, isLoad]
        have hza' : za = zs := by
          have e := normG_comp (stopS_flow P.R) hzs hz
          rw [hza, show normG flowAtom P.X.fuel zs = some zs from ?_] at e
          · exact Option.some.inj e
          obtain ⟨F, hF⟩ : ∃ F', P.X.fuel = F' + 1 := ⟨P.X.fuel - 1, by omega⟩
          rw [hF]
          exact normG_stop (by rw [skip1_atom heq, hfl]; rfl) F
        subst hza'
        rw [heq]
        simp only at h ⊢
        split at h
        · rename_i hcomp
          rw [ite_eq_left hcomp]
          obtain ⟨z3, hz3, h⟩ := Option.bind_eq_some_iff.mp h
          have hnext : zSize (za.next ss) < P.X.fuel := by
            have := zSize_next heq
            have : 1 ≤ stSize (.atom (.hint hc)) := Nat.le_refl 1
            omega
          obtain ⟨w3, hw3, hR3⟩ := nL_sim P hz3 hnext
          rw [hw3, Option.bind_some]
          exact hintsStepH_sim P hs hR3.1 hR3.2 h
        · cases h
      · cases h
    · rename_i hf
      rw [ite_eq_right hf]
      exact hintsStepH_sim P hs hz hza h

theorem scan_sim (P : PairCtx) (o1 o2 o3 : ℕ) : ∀ (f : ℕ) {z : Zip} {r : Zip × Bool}, zSize z < P.X.fuel →
    scan P o1 o2 o3 f z = some r →
    zSize r.1 < P.X.fuel ∧ normG flowAtom P.X.fuel r.1 = normG flowAtom P.X.fuel z
  | 0, _, _, _, h => by cases h
  | f + 1, z, r, hz, h => by
    change scanStep P o1 o2 o3 (scan P o1 o2 o3 f) z = some r at h
    simp only [scanStep, Bool.cond_eq_ite] at h
    split at h
    · rename_i d p off ss heq
      have hsk : skip1 flowAtom z = some (z.next ss) := by rw [skip1_atom heq]; rfl
      have hn : zSize (z.next ss) < P.X.fuel := Nat.lt_trans (skip1_size hsk) hz
      have e0 := normG_skip hsk hz
      split at h
      · obtain ⟨z', h1, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨Nat.lt_of_le_of_lt (normG_some h1).2 hn, ((normG_comp stopL_flow h1 hn).symm).trans e0.symm⟩
      · split at h
        · obtain ⟨z', h1, h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨a, b⟩ := scan_sim P o1 o2 o3 f (Nat.lt_of_le_of_lt (normG_some h1).2 hn) h2
          exact ⟨a, b.trans ((normG_comp stopL_flow h1 hn).symm.trans e0.symm)⟩
        · cases h
    · cases h

theorem plainStep_sim (P : PairCtx) (i : ℕ) (ins : OffsetInstruction) {z z' : Zip} (hz : zSize z < P.X.fuel)
    (h : plainStep P i ins z = some z') :
    zSize z' < P.X.fuel ∧ normG flowAtom P.X.fuel z' = normG flowAtom P.X.fuel z := by
  unfold plainStep at h
  split at h
  · split at h
    · rename_i z1 b hs
      simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h; exact scan_sim P _ _ _ _ hz hs
      · cases h
    · simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h; exact ⟨hz, rfl⟩
      · cases h
  · simp only [Bool.cond_eq_ite] at h
    split at h
    · cases h; exact ⟨hz, rfl⟩
    · cases h

theorem armZs_sim (P : PairCtx) (i : ℕ) {z : Zip} {s : Stmt} {ss : List Stmt} (hz : zSize z < P.X.fuel)
    (hc : z.cur = s :: ss) (base : ℕ) : ∀ (as : List (List Stmt)) (j : ℕ) {l : List (ℕ × Zip)},
    armZsH P i z s ss base j as = some l → ∃ la, armZs P.X i z s ss base j as = some la ∧ PendR P.X.fuel l la
  | [], _, _, h => by cases h; exact ⟨[], rfl, trivial⟩
  | _ :: as, j, l, h => by
    simp only [armZsH] at h
    simp only [armZs]
    cases ht : Check.getF P.X.jt (Nat.add base j) <;> simp only [ht] at h
    · cases h
    cases hn : P.nL (z.enter s ss j) <;> simp only [hn] at h
    · cases h
    rename_i c
    obtain ⟨ca, hca, hR⟩ := nL_sim P hn (Nat.lt_of_le_of_lt (zSize_enter hc j) hz)
    rw [hca]
    simp only
    rename_i t
    cases ho : P.X.fwdOff i t <;> simp only [ho] at h
    · cases h
    cases hl : armZsH P i z s ss base (j + 1) as <;> simp only [hl] at h
    · cases h
    cases h
    obtain ⟨la, hla, hR'⟩ := armZs_sim P i hz hc base as (j + 1) hl
    rw [hla]
    exact ⟨_, rfl, rfl, hR, hR'⟩

/-- `retNil` of a stopped zipper's position: its head is the closing `ret []`, where every normalization stops. -/
theorem retNil_stop {stop stop' : Atom → Bool} {w : Zip} (hw : skip1 stop w = none) (h : retNil w.pos = true) :
    skip1 stop' w = none := by
  obtain ⟨up, k, cur⟩ := w
  cases cur with
  | nil =>
    cases up with
    | nil => simp [Zip.pos, retNil] at h
    | cons e up => cases hw
  | cons s ss =>
    cases s
    case atom a =>
      exfalso
      revert h
      simp only [Zip.pos, List.cons_append]
      unfold retNil
      split <;> simp_all
    all_goals rfl

theorem headStepH_stop {P : PairCtx} {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip}
    {r : Option Zip × List (ℕ × Zip)} (h : headStepH P i oc od of tabs z = some r) (stop : Atom → Bool) :
    skip1 stop z = none := by
  obtain ⟨up, k, cur⟩ := z
  cases cur with
  | nil =>
    cases up with
    | nil => rfl
    | cons e up => simp [headStepH] at h
  | cons s ss =>
    cases s
    case atom a => simp [headStepH] at h
    all_goals rfl

theorem headStepH_sim (P : PairCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) {z : Zip}
    {r : Option Zip × List (ℕ × Zip)} (hz : zSize z < P.X.fuel) (h : headStepH P i oc od of tabs z = some r) :
    ∃ ra, headStep P.X i oc od of tabs z = some ra ∧ OutR P.X.fuel r ra := by
  obtain ⟨up, k, cur⟩ := z
  cases cur with
  | nil => cases up <;> simp [headStepH] at h
  | cons s ss =>
    have hc : (Zip.mk up k (s :: ss)).cur = s :: ss := rfl
    have hnx : zSize ((Zip.mk up k (s :: ss)).next ss) < P.X.fuel := by
      have := zSize_next hc
      have : 1 ≤ stSize s := by cases s <;> first | exact Nat.le_refl 1 | (change 1 ≤ _ + 1; omega)
      omega
    have hen : ∀ c, zSize ((Zip.mk up k (s :: ss)).enter s ss c) < P.X.fuel :=
      fun c ↦ Nat.lt_of_le_of_lt (zSize_enter hc c) hz
    generalize Zip.mk up k (s :: ss) = z at hc hnx hen h hz ⊢
    cases s with
    | atom a => simp [headStepH, hc] at h
    | ite c zb nb =>
      simp only [headStepH, headStep, hc] at h ⊢
      cases hb : (Nat.beq (P.X.locAt c.idx) oc && P.X.selfAt of) <;> simp only [hb, Bool.cond_false, Bool.cond_true] at h ⊢
      · cases h
      cases ht : P.X.pcAt od <;> simp only [ht] at h
      · cases h
      cases h0 : P.nL (z.enter (.ite c zb nb) ss 0) <;> simp only [h0] at h
      · cases h
      cases h1 : P.nL (z.enter (.ite c zb nb) ss 1) <;> simp only [h1] at h
      · cases h
      obtain ⟨w0, hw0, hR0⟩ := nL_sim P h0 (hen 0)
      obtain ⟨w1, hw1, hR1⟩ := nL_sim P h1 (hen 1)
      rw [hw0, hw1]
      simp only
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨(some w0, [(o, w1)]), ?_, hR0, rfl, hR1, trivial⟩
      rw [ho]; rfl
    | match_ x arms =>
      simp only [headStepH, headStep, hc] at h ⊢
      cases hb : (P.X.nzAt oc && P.X.selfAt of) <;> simp only [hb, Bool.cond_false, Bool.cond_true] at h ⊢
      · cases h
      cases ha : Check.getF P.X.arms od <;> simp only [ha] at h ⊢
      · cases h
      rename_i a
      cases hx : Nat.beq a.1 x.idx <;> simp only [hx, Bool.cond_false, Bool.cond_true] at h ⊢
      · cases h
      cases hh : tabHit tabs a.2 z i <;> simp only [hh, Bool.cond_false, Bool.cond_true] at h ⊢
      · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨la, hla, hR⟩ := armZs_sim P i hz hc a.2 arms 0 hl
        refine ⟨(none, la), ?_, trivial, hR⟩
        rw [hla]; rfl
      · cases h
        exact ⟨_, rfl, trivial, trivial⟩
    | call f args rets =>
      simp only [headStepH, headStep, hc] at h ⊢
      cases hs : P.X.siteAt of args rets <;> simp only [hs] at h
      · cases h
      cases ht : P.X.pcAt od <;> simp only [ht] at h
      · cases h
      cases hn : P.nL (z.next ss) <;> simp only [hn] at h
      · cases h
      obtain ⟨w, hw, hR⟩ := nL_sim P hn hnx
      rw [hw]
      simp only
      revert h
      cases P.X.nzAt oc && P.X.entOk _ f <;> simp only [Bool.cond_false, Bool.cond_true, reduceCtorEq, false_imp_iff]
      intro h
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨(none, [(o, w)]), ?_, trivial, rfl, hR, trivial⟩
      rw [ho]; rfl
    | callIf c f args =>
      simp only [headStepH, headStep, hc] at h ⊢
      cases hb : Nat.beq (P.X.locAt c.idx) oc <;> simp only [hb, Bool.cond_false, Bool.cond_true] at h ⊢
      · cases h
      cases ht : P.X.pcAt od <;> simp only [ht] at h
      · cases h
      cases hn : P.nL (z.next ss) <;> simp only [hn] at h
      · cases h
      rename_i t ca
      obtain ⟨w, hw, hR⟩ := nL_sim P hn hnx
      rw [hw]
      simp only
      cases he : P.X.entOk t f <;> simp only [he, Bool.cond_false, Bool.cond_true] at h ⊢
      · cases h
      cases hnt : P.X.nextAt of <;> simp only [hnt, Bool.cond_false, Bool.cond_true] at h ⊢
      · cases hs : P.X.siteAt of args [] <;> simp only [hs] at h ⊢
        · cases h
        revert h
        cases Nat.beq _ (P.X.entry + i + 1) <;> simp only [Bool.cond_false, Bool.cond_true, reduceCtorEq, false_imp_iff]
        intro h
        cases h
        exact ⟨_, rfl, hR, trivial⟩
      · cases hr : retNil ca.pos <;> simp only [hr, Bool.cond_false, Bool.cond_true] at h
        · cases h
        cases h
        have hwa : w = ca := by
          have hs := retNil_stop (stop' := flowAtom) (normG_some hn).1 hr
          obtain ⟨F, hF⟩ : ∃ F', P.X.fuel = F' + 1 := ⟨P.X.fuel - 1, by have := hR.1; omega⟩
          have := hR.2
          rw [hF, normG_stop hs F] at this
          exact (Option.some.inj this).symm
        subst hwa
        rw [hr]
        exact ⟨_, rfl, hR, trivial⟩
    | dispatch x fs args rets =>
      simp only [headStepH, headStep, hc] at h ⊢
      cases hs : P.X.siteAt of args rets <;> simp only [hs] at h
      · cases h
      cases hn : P.nL (z.next ss) <;> simp only [hn] at h
      · cases h
      obtain ⟨w, hw, hR⟩ := nL_sim P hn hnx
      rw [hw]
      simp only
      revert h
      cases P.X.nzAt oc && Nat.beq _ od && !Nat.beq od 0 <;>
        simp only [Bool.cond_false, Bool.cond_true, reduceCtorEq, false_imp_iff]
      intro h
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨(none, [(o, w)]), ?_, trivial, rfl, hR, trivial⟩
      rw [ho]; rfl
    | ret vs =>
      simp only [headStepH, headStep, hc] at h ⊢
      revert h
      cases P.X.main <;> simp only [Bool.cond_false, Bool.cond_true]
      · cases P.X.nzAt oc && Nat.beq od 0 && Nat.beq of 1 <;>
          simp only [Bool.cond_false, Bool.cond_true, reduceCtorEq, false_imp_iff, Option.some.injEq]
        rintro rfl
        exact ⟨_, rfl, trivial, trivial⟩
      · cases P.X.nzAt oc && P.X.selfAt of && P.X.pcAt od == some P.X.halt <;>
          simp only [Bool.cond_false, Bool.cond_true, reduceCtorEq, false_imp_iff, Option.some.injEq]
        rintro rfl
        exact ⟨_, rfl, trivial, trivial⟩

/-- **A jump**: the alignment's from the pairing's zipper normalized, the same table jumps registered. -/
theorem jumpStepH_sim (P : PairCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) {z za zs : Zip}
    {r : Option Zip × List (ℕ × Zip)} (hR : Rz P.X.fuel z za) (hzs : P.nS z = some zs)
    (h : jumpStepH P i oc od of tabs z zs = some r) :
    ∃ ra, jumpStep P.X i oc od of tabs za = some ra ∧ OutR P.X.fuel r ra ∧
      tabReg P.X i (.jump oc od of) zs r.2 tabs = tabReg P.X i (.jump oc od of) za ra.2 tabs := by
  simp only [jumpStepH, jumpStep] at h ⊢
  cases hz0 : P.X.zeroAt oc <;> simp only [hz0, Bool.cond_false, Bool.cond_true] at h ⊢
  · cases hf : fwdJ P.X i oc od of <;> simp only [hf, Bool.cond_false, Bool.cond_true] at h ⊢
    · -- by the head statement, from the zipper past its reads, where the alignment's stands
      change normG (stopS P.R) P.X.fuel z = some zs at hzs
      have hst := headStepH_stop h flowAtom
      have hza : za = zs := by
        have e := normG_comp (stopS_flow P.R) hzs hR.1
        obtain ⟨F, hF⟩ : ∃ F', P.X.fuel = F' + 1 := ⟨P.X.fuel - 1, by have := hR.1; omega⟩
        rw [hR.2, hF, normG_stop hst F] at e
        exact Option.some.inj e
      subst hza
      obtain ⟨ra, hra, hout⟩ := headStepH_sim P i oc od of tabs (Nat.lt_of_le_of_lt (normG_some hzs).2 hR.1) h
      exact ⟨ra, hra, hout, tabReg_offs _ _ _ _ hout.2.offs _⟩
    · obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨(none, [(o, za)]), ?_, ⟨trivial, rfl, hR, trivial⟩, ?_⟩
      · rw [ht]; simp only [Option.bind_some, ho]; rfl
      · rw [tabReg_fwdJ hf, tabReg_fwdJ hf]
  · cases h
    exact ⟨_, rfl, ⟨hR, trivial⟩, by rw [tabReg_nil, tabReg_nil]⟩

/-! ## The pass -/

/-- The zipper falling in, both or neither; at the body's start (nothing pending) the alignment's may be the
pairing's itself. -/
def CurR (F : ℕ) : Option Zip → Option Zip → Prop → Prop
  | none, none, _ => True
  | some zp, some za, e => zSize zp < F ∧ (normG flowAtom F zp = some za ∨ (za = zp ∧ e))
  | _, _, _ => False

/-- **The pass's states related**: the same offset, hints and table jumps, the arrivals pending and the zipper
falling in the pairing's normalized. -/
structure SimR (F : ℕ) (sp sa : St) : Prop where
  i : sp.i = sa.i
  hs : sp.hs = sa.hs
  tabs : sp.tabs = sa.tabs
  pend : PendR F sp.pend sa.pend
  cur : CurR F sp.cur sa.cur (sp.pend = [])

theorem visitH_sim (P : PairCtx) (ins : OffsetInstruction) (i i' : ℕ) (h1 : List Prover.Exec.Hint)
    (hs' : List (ℕ × List Prover.Exec.Hint)) {rest ra' : List (ℕ × Zip)} (tabs : List (ℕ × Zip × ℕ)) {c ca w : Zip}
    {r : St × Option (ℕ × Zip)} (hc : zSize c < P.X.fuel) (hw : normG flowAtom P.X.fuel c = some w)
    (hwa : normG flowAtom P.X.fuel ca = some w) (hrest : PendR P.X.fuel rest ra')
    (h : visitH P ins i i' h1 hs' rest tabs c = some r) :
    ∃ ra, visit P.X ins i i' h1 hs' ra' tabs ca = some ra ∧ SimR P.X.fuel r.1 ra.1 := by
  simp only [visitH] at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z1, hz1, hz⟩ := Option.bind_eq_some_iff.mp hz
  change normG stopL P.X.fuel c = some z1 at hz1
  have e1 := normG_comp stopL_flow hz1 hc
  have hz1s : zSize z1 < P.X.fuel := Nat.lt_of_le_of_lt (normG_some hz1).2 hc
  obtain ⟨z2a, hz2a, hR⟩ := hintsStepH_sim P h1 hz1s (e1 ▸ hw) hz
  simp only [visit]
  rw [normZ_eq_normG, hwa, Option.bind_some, hz2a, Option.bind_some]
  cases ins
  case jump oc od of h =>
    dsimp only at h
    simp only [Bool.cond_eq_ite] at h
    split at h
    · obtain ⟨zs, hzs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨qa, hqa, hout, htab⟩ := jumpStepH_sim P i oc od of tabs hR hzs hq
      refine ⟨(⟨i', hs', qa.1, mergeP qa.2 ra', tabReg P.X i (.jump oc od of) z2a qa.2 tabs⟩, some (i, ca)), ?_,
        rfl, rfl, htab, mergeP_sim hout.2 hrest, ?_⟩
      · simp only [insStep, hqa, Option.map_some]
      have h1 := hout.1
      revert h1
      cases q.1 <;> cases qa.1 <;> simp only [OptR, CurR, imp_self]
      exact fun h ↦ ⟨h.1, Or.inl h.2⟩
    · cases h
  all_goals
    rename_i h
    dsimp only at h
    obtain ⟨z', hz', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hs1, hs2⟩ := plainStep_sim P i _ hR.1 hz'
    exact ⟨_, rfl, ⟨rfl, rfl, by simp only [tabReg_nil], hrest, hs1, Or.inl (hs2.trans hR.2)⟩⟩

theorem allKey_sim {F : ℕ} {body : List Stmt} {c ca : Zip} (hc : ZOk body c) (hca : normG flowAtom F c = some ca) :
    ∀ {here hera : List (ℕ × Zip)}, PendR F here hera → (∀ p ∈ here, ZOk body p.2) → allKey here c = true →
      allKey hera ca = true
  | [], [], _, _, _ => rfl
  | p :: here, q :: hera, hr, hok, h => by
    simp only [allKey, List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, allKey_sim hc hca hr.2.2 (fun p hp ↦ hok p (List.mem_cons_of_mem _ hp)) h.2⟩
    have hp := ZOk.eq_of_key (hok p List.mem_cons_self) hc ((keyEq_iff).mp h.1)
    have : some q.2 = some ca := by rw [← hr.2.1.2, ← hca, hp]
    rw [Option.some.inj this, keyEq_iff]
  | [], _ :: _, hr, _, _ => hr.elim
  | _ :: _, [], hr, _, _ => hr.elim

/-- **A step of the pairing is one of the alignment.** -/
theorem stepIH_sim {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (P : PairCtx)
    (ins : OffsetInstruction) {sp sa : St} {r : St × Option (ℕ × Zip)} (hst : StOk body hs0 sp)
    (hR : SimR P.X.fuel sp sa) (h : stepIH P ins sp = some r) :
    ∃ ra, stepI P.X ins sa = some ra ∧ SimR P.X.fuel r.1 ra.1 := by
  unfold stepIH at h
  unfold stepI
  rw [natSeq_eq] at h ⊢
  rw [← hR.i, ← hR.hs, ← hR.tabs]
  have hsp := spanP_sim sp.i hR.pend
  have hmem : ∀ p, _ := fun p ↦ spanP_mem sp.i sp.pend (p := p)
  have hcur := hR.cur
  have hemp : sp.pend = [] → spanP sp.i sp.pend = ([], []) := fun he ↦ by rw [he]; rfl
  generalize spanP sp.i sp.pend = S at h hsp hmem hemp
  generalize spanP sp.i sa.pend = T at hsp ⊢
  generalize hintsAt (Nat.add P.X.entry sp.i) sp.hs = H at h ⊢
  obtain ⟨here, rest⟩ := S
  obtain ⟨hera, resta⟩ := T
  obtain ⟨h1, hs'⟩ := H
  obtain ⟨hhere, hrest⟩ := hsp
  have hok : ∀ p ∈ here, ZOk body p.2 := fun p hp ↦ hst.pend p ((hmem p).1 hp)
  simp only [Bool.cond_eq_ite] at h ⊢
  revert hcur
  cases hc : sp.cur <;> cases hca : sa.cur <;> simp only [CurR, false_imp_iff]
  · -- nothing falls in: the first arrival pending, if any
    intro _
    simp only [hc] at h
    cases here with
    | nil =>
      cases hera with
      | nil =>
        cases h
        exact ⟨_, rfl, ⟨rfl, rfl, rfl, hrest, by simp [CurR]⟩⟩
      | cons _ _ => exact hhere.elim
    | cons p here =>
      cases hera with
      | nil => exact hhere.elim
      | cons q hera =>
        simp only at h ⊢
        split at h
        · rename_i hk
          rw [ite_eq_left (allKey_sim (hok p List.mem_cons_self) hhere.2.1.2 hhere hok hk)]
          exact visitH_sim P ins _ _ h1 hs' _ hhere.2.1.1 hhere.2.1.2 hhere.2.1.self hrest h
        · cases h
  · rename_i c ca
    rintro ⟨hcs, hn⟩
    simp only [hc] at h
    split at h
    · rename_i hk
      have hcok : ZOk body c := hst.cur c (by simp [hc])
      obtain ⟨w, hw⟩ := normG_total flowAtom P.X.fuel c hcs
      rcases hn with hn | ⟨rfl, he⟩
      · rw [ite_eq_left (allKey_sim hcok hn hhere hok hk)]
        exact visitH_sim P ins _ _ h1 hs' _ hcs hn (Rz.self ⟨hcs, hn⟩) hrest h
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (hemp he)
        cases hera with
        | nil => exact visitH_sim P ins _ _ h1 hs' _ hcs hw hw hrest h
        | cons _ _ => exact hhere.elim
    · cases h

theorem pairGo_sim {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (P : PairCtx) :
    ∀ (code : List OffsetInstruction) {sp sa : St} {acc acca : List (ℕ × Zip)} {r : St × List (ℕ × Zip)},
    StOk body hs0 sp → SimR P.X.fuel sp sa → pairGo P code sp acc = some r →
    ∃ ra, alignGo P.X code sa acca = some ra ∧ SimR P.X.fuel r.1 ra.1
  | [], _, _, _, _, _, _, hR, h => by cases h; exact ⟨_, rfl, hR⟩
  | ins :: code, sp, sa, acc, acca, r, hst, hR, h => by
    rw [pairGo_cons] at h
    rw [alignGo_cons]
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨pa, hpa, hR'⟩ := stepIH_sim P ins hst hR hp
    rw [hpa, Option.bind_some]
    exact pairGo_sim P code (stepIH_ok P ins hst hp).1 hR' h

public section

/-- **A function passing its pairing passes its alignment check**, its body smaller than the normalization's
fuel. -/
theorem alignOk_of_pairOk {X : AlignCtx} {H : HCert} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hfit : blkSize body < X.fuel)
    (h : pairOk X H O S body code d = true) : alignOk X body code d = true := by
  rw [pairOk, PairCtx.seq_eq] at h
  rw [alignOk, AlignCtx.seq_eq]
  change (alignPre X d && (alignRun X body code d).isSome) = true
  change (alignPre X d && (pairRun (PairCtx.ofH X H O S) body code d).isSome) = true at h
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h.2
  simp only [pairRun, alignRun] at hl ⊢
  obtain ⟨⟨st', acc'⟩, hgo, hend⟩ := Option.bind_eq_some_iff.mp hl
  have hst0 : StOk body d.2.2 ⟨0, d.2.2, some (Zip.init body), [], []⟩ :=
    ⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩
  have hR0 : SimR X.fuel ⟨0, d.2.2, some (Zip.init body), [], []⟩ ⟨0, d.2.2, some (Zip.init body), [], []⟩ :=
    ⟨rfl, rfl, rfl, trivial, hfit, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨⟨sa, acca⟩, hga, hR⟩ := pairGo_sim (body := body) (hs0 := d.2.2) (PairCtx.ofH X H O S) code
    (acca := []) hst0 hR0 hgo
  change alignGo X code _ [] = some (sa, acca) at hga
  rw [hga, Option.bind_some]
  simp only [alignEnd, Bool.cond_eq_ite, Bool.and_eq_true] at hend ⊢
  split at hend
  · rename_i he
    have hc := hR.cur
    have hp := hR.pend
    simp only at he hc hp
    obtain ⟨he1, he2⟩ := he
    revert hc hp
    cases hcp : st'.cur <;> cases hca : sa.cur <;> simp_all [CurR]
    cases hpp : st'.pend <;> cases hpa : sa.pend <;> simp_all [PendR]
  · cases hend

end

end LeanVM.Guest.CoreMode
