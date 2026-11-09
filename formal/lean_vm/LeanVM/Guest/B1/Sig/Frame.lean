/-
  LeanVM.Guest.B1.Sig.Frame

  The semantics of a block depends only on the values it names; valuations extended on a range of
  numbers.
-/

module

public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Renumber

/-!
# Frames

The renumbered values of a function are `V.n k`, numbered by first occurrence, so the values a
block of the guest names first form a range `lo ..< hi`, and every value it names is below `hi`
(`NumBelow`). The completeness proofs build a valuation block by block: each block's valuation
`Ext`ends the previous one on its own range, and `holdsList_congr` keeps the earlier blocks true.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- Every value of the list is numbered below `hi`. -/
def NumBelow (hi : Nat) (vs : List V) : Prop := ∀ v ∈ vs, ∃ k < hi, v = .n k

/-- Two valuations agree below `hi`. -/
def AgreeBelow (hi : Nat) (σ σ' : Val) : Prop := ∀ k < hi, σ (.n k) = σ' (.n k)

/-- `σ'` changes `σ` only on the values numbered `lo ..< hi`. -/
def Ext (lo hi : Nat) (σ σ' : Val) : Prop := ∀ v, (∀ k, lo ≤ k → k < hi → v ≠ .n k) → σ' v = σ v

theorem Ext.refl (lo hi : Nat) (σ : Val) : Ext lo hi σ σ := fun _ _ => rfl

theorem Ext.trans {lo m hi : Nat} {σ σ' σ'' : Val} (h1 : Ext lo m σ σ') (h2 : Ext m hi σ' σ'')
    (hlo : lo ≤ m) (hhi : m ≤ hi) : Ext lo hi σ σ'' := fun v hv =>
  (h2 v fun k hk1 hk2 => hv k (by omega) (by omega)).trans
    (h1 v fun k hk1 hk2 => hv k (by omega) (by omega))

theorem Ext.comp {lo hi : Nat} {σ σ' σ'' : Val} (h1 : Ext lo hi σ σ') (h2 : Ext lo hi σ' σ'') :
    Ext lo hi σ σ'' := fun v hv => (h2 v hv).trans (h1 v hv)

theorem Ext.mono {lo hi lo' hi' : Nat} {σ σ' : Val} (h : Ext lo hi σ σ') (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : Ext lo' hi' σ σ' := fun v hv => h v fun k h1 h2 => hv k (by omega) (by omega)

theorem Ext.agree {lo hi : Nat} {σ σ' : Val} (h : Ext lo hi σ σ') : AgreeBelow lo σ σ' :=
  fun k hk => (h (.n k) fun j hj _ e => by simp only [V.mk.injEq] at e; omega).symm

theorem Ext.apply {lo hi k : Nat} {σ σ' : Val} (h : Ext lo hi σ σ') (hk : k < lo ∨ hi ≤ k) :
    σ' (.n k) = σ (.n k) :=
  h (.n k) fun j hj1 hj2 e => by simp only [V.mk.injEq] at e; omega

theorem AgreeBelow.apply {hi : Nat} {σ σ' : Val} (h : AgreeBelow hi σ σ') {v : V} (hv : ∃ k < hi, v = .n k) :
    σ' v = σ v := by
  obtain ⟨k, hk, rfl⟩ := hv; exact (h k hk).symm

theorem AgreeBelow.mono {hi hi' : Nat} {σ σ' : Val} (h : AgreeBelow hi σ σ') (hle : hi' ≤ hi) :
    AgreeBelow hi' σ σ' := fun k hk => h k (by omega)

theorem NumBelow.mono {hi hi' : Nat} {vs : List V} (h : NumBelow hi vs) (hle : hi ≤ hi') :
    NumBelow hi' vs := fun v hv => let ⟨k, hk, e⟩ := h v hv; ⟨k, by omega, e⟩

theorem NumBelow.append {hi : Nat} {vs ws : List V} (h1 : NumBelow hi vs) (h2 : NumBelow hi ws) :
    NumBelow hi (vs ++ ws) := fun v hv => by
  rcases List.mem_append.mp hv with h | h
  · exact h1 v h
  · exact h2 v h

theorem NumBelow.nil (hi : Nat) : NumBelow hi [] := fun _ h => absurd h (by simp)

theorem NumBelow.cons {hi : Nat} {v : V} {vs : List V} (h1 : ∃ k < hi, v = .n k)
    (h2 : NumBelow hi vs) : NumBelow hi (v :: vs) := fun w hw => by
  rcases List.mem_cons.mp hw with h | h
  · exact h ▸ h1
  · exact h2 w h

/-! ## The frame lemma -/

theorem map_congr {σ σ' : Val} {vs : List V} (h : ∀ v ∈ vs, σ v = σ' v) : vs.map σ = vs.map σ' :=
  List.map_congr_left h

theorem atom_congr {σ σ' : Val} (a : Atom) (h : ∀ v ∈ a.vals, σ v = σ' v) :
    a.Holds rd σ ↔ a.Holds rd σ' := by
  cases a with
  | frameAddr p run =>
      simp only [Atom.vals, List.mem_cons] at h
      simp only [Atom.Holds]
      rw [h p (Or.inl rfl)]
      refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk =>
        forall_congr' fun w => imp_congr_right fun _ => ?_
      rw [h run[k] (Or.inr (List.getElem_mem hk))]
  | hint => simp [Atom.Holds]
  | keccak ins outs inOdd outOdd =>
      simp only [Atom.vals, List.mem_append] at h
      simp only [Atom.Holds]
      rw [map_congr (fun v hv => h v (Or.inl hv)), map_congr (fun v hv => h v (Or.inr hv))]
  | _ => simp only [Atom.vals, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at h; simp only [Atom.Holds, h]

theorem mem_valsList_of_mem {s : Stmt} {ss : List Stmt} (hs : s ∈ ss) {v : V} (hv : v ∈ s.vals) :
    v ∈ Stmt.valsList ss := by
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
      simp only [Stmt.valsList, List.mem_append]
      rcases List.mem_cons.mp hs with rfl | h
      · exact Or.inl hv
      · exact Or.inr (ih h)

mutual
theorem holds_congr {σ σ' : Val} : ∀ (s : Stmt), (∀ v ∈ s.vals, σ v = σ' v) →
    ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.Holds C rd σ s next kret ↔ Stmt.Holds C rd σ' s next kret)
  | .atom a, h, _, _ => by simp only [Stmt.Holds, atom_congr a h]
  | .ite c z n, h, next, kret => by
      simp only [Stmt.vals, List.mem_cons, List.mem_append] at h
      simp only [Stmt.Holds]
      rw [h c (Or.inl (Or.inl rfl)), holdsList_congr z (fun v hv => h v (Or.inl (Or.inr hv))) next kret,
        holdsList_congr n (fun v hv => h v (Or.inr hv)) next kret]
  | .match_ x arms, h, next, kret => by
      simp only [Stmt.vals, List.mem_cons] at h
      simp only [Stmt.Holds]
      exact holdsArms_congr x arms (h x (Or.inl rfl)) (fun v hv => h v (Or.inr hv)) 0 next kret
  | .call f args rets, h, _, _ => by
      simp only [Stmt.vals, List.mem_append] at h
      simp only [Stmt.Holds, map_congr fun v hv => h v (Or.inl hv), map_congr fun v hv => h v (Or.inr hv)]
  | .callIf c f args, h, _, _ => by
      simp only [Stmt.vals, List.mem_cons] at h
      simp only [Stmt.Holds, h c (Or.inl rfl), map_congr fun v hv => h v (Or.inr hv)]
  | .dispatch x fs args rets, h, _, _ => by
      simp only [Stmt.vals, List.mem_cons, List.mem_append] at h
      simp only [Stmt.Holds, h x (Or.inl (Or.inl rfl)), map_congr fun v hv => h v (Or.inl (Or.inr hv)),
        map_congr fun v hv => h v (Or.inr hv)]
  | .ret vs, h, _, _ => by simp only [Stmt.Holds, Stmt.vals] at h ⊢; rw [map_congr h]

theorem holdsList_congr {σ σ' : Val} : ∀ (ss : List Stmt), (∀ v ∈ Stmt.valsList ss, σ v = σ' v) →
    ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsList C rd σ ss next kret ↔ Stmt.HoldsList C rd σ' ss next kret)
  | [], _, _, _ => Iff.rfl
  | s :: ss, h, next, kret => by
      simp only [Stmt.valsList, List.mem_append] at h
      simp only [Stmt.HoldsList]
      rw [holdsList_congr ss (fun v hv => h v (Or.inr hv)) next kret]
      exact holds_congr s (fun v hv => h v (Or.inl hv)) _ kret

theorem holdsArms_congr {σ σ' : Val} (x : V) : ∀ (arms : List (List Stmt)),
    σ x = σ' x → (∀ v ∈ Stmt.valsArms arms, σ v = σ' v) →
    ∀ (j : Nat) (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsArms C rd σ x j arms next kret ↔ Stmt.HoldsArms C rd σ' x j arms next kret)
  | [], _, _, _, _, _ => Iff.rfl
  | a :: as, hx, h, j, next, kret => by
      simp only [Stmt.valsArms, List.mem_append] at h
      simp only [Stmt.HoldsArms]
      rw [hx, holdsList_congr a (fun v hv => h v (Or.inl hv)) next kret,
        holdsArms_congr x as hx (fun v hv => h v (Or.inr hv)) (j + 1) next kret]
end

/-- **The frame lemma**: a block whose values are numbered below `hi` holds of two valuations
agreeing below `hi` alike. -/
theorem holdsList_frame {hi : Nat} {σ σ' : Val} {ss : List Stmt}
    (hb : NumBelow hi (Stmt.valsList ss)) (hσ : AgreeBelow hi σ σ') (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ ss next kret ↔ Stmt.HoldsList C rd σ' ss next kret :=
  holdsList_congr ss (fun v hv => let ⟨k, hk, e⟩ := hb v hv; e ▸ hσ k hk) next kret

/-! ## Values of blocks -/

@[simp] theorem valsList_nil : Stmt.valsList [] = [] := rfl

@[simp] theorem valsList_cons (s : Stmt) (ss : List Stmt) :
    Stmt.valsList (s :: ss) = s.vals ++ Stmt.valsList ss := rfl

@[simp] theorem valsList_append (xs ys : List Stmt) :
    Stmt.valsList (xs ++ ys) = Stmt.valsList xs ++ Stmt.valsList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem numBelow_valsArms {hi : Nat} (arms : List (List Stmt))
    (h : ∀ a ∈ arms, NumBelow hi (Stmt.valsList a)) : NumBelow hi (Stmt.valsArms arms) := by
  induction arms with
  | nil => exact NumBelow.nil hi
  | cons a as ih =>
      simp only [Stmt.valsArms]
      exact (h a (by simp)).append (ih fun b hb => h b (by simp [hb]))

/-! ## Blocks in sequence -/

@[simp] theorem holdsList_cons_atom (a : Atom) (ss : List Stmt) (next : Prop) (kret : List E → Prop)
    (σ : Val) :
    Stmt.HoldsList C rd σ (.atom a :: ss) next kret ↔ a.Holds rd σ ∧ Stmt.HoldsList C rd σ ss next kret :=
  Iff.rfl

@[simp] theorem holdsList_nil (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsList C rd σ [] next kret ↔ next := Iff.rfl

/-- What a completeness proof of a block gives: from `σ`, a valuation changing only `lo ..< hi`
under which the block holds before any true continuation. -/
def Completes (C : CallRel) (rd : Reader) (lo hi : Nat) (ss : List Stmt) (σ : Val) (Post : Val → Prop) : Prop :=
  ∃ σ', Ext lo hi σ σ' ∧ Post σ' ∧
    ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsList C rd σ' ss next kret

/-- Completeness in sequence: a first block completing on `lo ..< m`, then, from any valuation it
reaches, a second on `m ..< hi`, the first numbered below `m`. -/
theorem Completes.append {lo m hi : Nat} {xs ys : List Stmt} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hxs : NumBelow m (Stmt.valsList xs))
    (h1 : Completes C rd lo m xs σ P) (h2 : ∀ σ', Ext lo m σ σ' → P σ' → Completes C rd m hi ys σ' Q) :
    Completes C rd lo hi (xs ++ ys) σ Q := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  obtain ⟨σ2, he2, hq2, hh2⟩ := h2 σ1 he1 hp1
  refine ⟨σ2, he1.trans he2 hlo hhi, hq2, fun next kret hn => ?_⟩
  rw [holdsList_append]
  exact (holdsList_frame hxs he2.agree _ _).mp (hh1 _ kret (hh2 next kret hn))

theorem Completes.mono {lo hi lo' hi' : Nat} {ss : List Stmt} {σ : Val} {P Q : Val → Prop}
    (h : Completes C rd lo hi ss σ P) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hPQ : ∀ σ', P σ' → Q σ') :
    Completes C rd lo' hi' ss σ Q :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he.mono hlo hhi, hPQ σ' hp, hh⟩

/-! ## Valuations updated at numbered values -/

/-- `σ` updated at the numbered values of the list, the first entry of a number winning. -/
def upds (σ : Val) : List (Nat × E) → Val
  | [] => σ
  | (k, e) :: l => Function.update (upds σ l) (.n k) e

theorem upds_cons_self (σ : Val) (k : Nat) (e : E) (l : List (Nat × E)) :
    upds σ ((k, e) :: l) (.n k) = e := by simp [upds]

theorem upds_cons_ne (σ : Val) {k j : Nat} (e : E) (l : List (Nat × E)) (h : j ≠ k) :
    upds σ ((k, e) :: l) (.n j) = upds σ l (.n j) := by
  simp only [upds]
  exact Function.update_of_ne (by simp only [ne_eq, V.mk.injEq, true_and]; exact h) _ _

theorem upds_of_not_mem (σ : Val) {v : V} : ∀ (l : List (Nat × E)), (∀ p ∈ l, v ≠ .n p.1) →
    upds σ l v = σ v
  | [], _ => rfl
  | (k, e) :: l, h => by
      simp only [upds]
      rw [Function.update_of_ne (h (k, e) (by simp)), upds_of_not_mem σ l fun p hp => h p (by simp [hp])]

theorem upds_ext {lo hi : Nat} (σ : Val) (l : List (Nat × E)) (h : ∀ p ∈ l, lo ≤ p.1 ∧ p.1 < hi) :
    Ext lo hi σ (upds σ l) := by
  intro w hw
  exact upds_of_not_mem σ l fun p hp => hw p.1 (h p hp).1 (h p hp).2

end
end LeanVM.Guest.B1.Sig
