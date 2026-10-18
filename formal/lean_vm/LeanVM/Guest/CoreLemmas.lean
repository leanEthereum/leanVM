/-
  LeanVM.Guest.CoreLemmas

  The structural lemmas of the core IR's semantics: blocks in sequence, return-free blocks as
  conjunctions, `match` as one in-range arm, calls as their callee's relation, and the meaning of
  a range check.
-/

module

public import LeanVM.Guest.Core
public import LeanVM.Semantics.Lemmas

/-!
# Lemmas about the core semantics

* `holdsList_append`: a block followed by another is the first with the second as its
  continuation; `holdsList_flatten`: return-free blocks in sequence (an `unroll`'s iterations)
  hold exactly when each holds;
* `holdsArms_iff`, `holds_match_iff`, `holds_dispatch_iff`: a `match` holds of one arm `j` at
  `x = g^j`, `j < arms.length`, the in-range condition a conjunct;
* `holds_mono`, `relN_mono`, `rel_iff`: the semantics is monotone in the call relation, and
  `Program.Rel` is a fixed point, a call holding exactly when the callee's body does under
  `Program.Rel`;
* `rangeCheck_iff`: on a memory of `2^κ ≤ 2^32` words, a range check against `g^(K-1)`,
  `1 ≤ K ≤ 2^κ`, holds for some complement and touched words exactly when `x = g^e` with
  `e < K`, the bounded discrete logarithm the compiler documents.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Sequencing -/

theorem holdsList_append (xs ys : List Stmt) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (xs ++ ys) next kret =
      Stmt.HoldsList C rd σ xs (Stmt.HoldsList C rd σ ys next kret) kret := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, Stmt.HoldsList, ih]

mutual
/-- A statement without a `ret`, at any depth. -/
def Stmt.noRet : Stmt → Bool
  | .ret _ => false
  | .ite _ z n => Stmt.noRetList z && Stmt.noRetList n
  | .match_ _ arms => Stmt.noRetArms arms
  | _ => true

/-- A block without a `ret`. -/
def Stmt.noRetList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.noRet s && Stmt.noRetList ss

/-- Arms without a `ret`. -/
def Stmt.noRetArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.noRetList a && Stmt.noRetArms as
end

mutual
theorem holds_noRet : ∀ (s : Stmt), Stmt.noRet s = true → ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.Holds C rd σ s next kret ↔ Stmt.Holds C rd σ s True kret ∧ next)
  | .atom _, _, _, _ => by simp [Stmt.Holds]
  | .ite c z n, h, next, kret => by
      simp only [Stmt.noRet, Bool.and_eq_true] at h
      simp only [Stmt.Holds]
      rw [holdsList_noRet z h.1 next kret, holdsList_noRet n h.2 next kret,
        holdsList_noRet z h.1 True kret, holdsList_noRet n h.2 True kret]
      by_cases hc : σ c = 0 <;> simp [hc] <;> tauto
  | .match_ x arms, h, next, kret => by
      simp only [Stmt.noRet] at h
      simp only [Stmt.Holds]
      exact holdsArms_noRet x arms h 0 next kret
  | .call .., _, _, _ => by simp [Stmt.Holds]
  | .callIf .., _, _, _ => by simp [Stmt.Holds, and_assoc]
  | .dispatch .., _, _, _ => by simp [Stmt.Holds]
  | .ret _, h, _, _ => by simp [Stmt.noRet] at h

theorem holdsList_noRet : ∀ (ss : List Stmt), Stmt.noRetList ss = true →
    ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsList C rd σ ss next kret ↔ Stmt.HoldsList C rd σ ss True kret ∧ next)
  | [], _, _, _ => by simp [Stmt.HoldsList]
  | s :: ss, h, next, kret => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at h
      simp only [Stmt.HoldsList]
      rw [holds_noRet s h.1 (Stmt.HoldsList C rd σ ss next kret) kret,
        holds_noRet s h.1 (Stmt.HoldsList C rd σ ss True kret) kret, holdsList_noRet ss h.2 next kret]
      tauto

theorem holdsArms_noRet (x : V) : ∀ (arms : List (List Stmt)), Stmt.noRetArms arms = true →
    ∀ (j : Nat) (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsArms C rd σ x j arms next kret ↔ Stmt.HoldsArms C rd σ x j arms True kret ∧ next)
  | [], _, _, _, _ => by simp [Stmt.HoldsArms]
  | a :: as, h, j, next, kret => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at h
      simp only [Stmt.HoldsArms]
      rw [holdsList_noRet a h.1 next kret, holdsArms_noRet x as h.2 (j + 1) next kret]
      tauto
end

/-- Return-free blocks in sequence hold exactly when each does: the semantics of an expanded
`unroll` is the conjunction over its counter of the iterations'. -/
theorem holdsList_flatten (bs : List (List Stmt)) (h : ∀ b ∈ bs, Stmt.noRetList b = true)
    (next : Prop) (kret : List E → Prop) :
    (Stmt.HoldsList C rd σ bs.flatten next kret ↔
      (∀ b ∈ bs, Stmt.HoldsList C rd σ b True kret) ∧ next) := by
  induction bs with
  | nil => simp [Stmt.HoldsList]
  | cons b bs ih =>
      simp only [List.flatten_cons, holdsList_append, List.mem_cons, forall_eq_or_imp]
      rw [holdsList_noRet b (h b (by simp)) _ kret, ih (fun b hb => h b (by simp [hb]))]
      tauto

/-! ## `match` -/

theorem holdsArms_iff (x : V) : ∀ (arms : List (List Stmt)) (j : Nat) (next : Prop)
    (kret : List E → Prop),
    Stmt.HoldsArms C rd σ x j arms next kret ↔
      ∃ (i : Nat) (h : i < arms.length), σ x = ofK (gpow (j + i)) ∧
        Stmt.HoldsList C rd σ arms[i] next kret
  | [], _, _, _ => by simp [Stmt.HoldsArms]
  | a :: as, j, next, kret => by
      simp only [Stmt.HoldsArms, holdsArms_iff x as (j + 1) next kret]
      constructor
      · rintro (⟨hx, ha⟩ | ⟨i, hi, hx, ha⟩)
        · exact ⟨0, by simp, by simpa using hx, by simpa using ha⟩
        · exact ⟨i + 1, by simp; omega, by rw [hx]; congr 2; omega, by simpa using ha⟩
      · rintro ⟨i, hi, hx, ha⟩
        cases i with
        | zero => exact Or.inl ⟨by simpa using hx, by simpa using ha⟩
        | succ i =>
            exact Or.inr ⟨i, by simp at hi; omega, by rw [hx]; congr 2; omega, by simpa using ha⟩

/-- A `match` holds of one arm `j < arms.length`, at `x = g^j`. -/
theorem holds_match_iff (x : V) (arms : List (List Stmt)) (next : Prop) (kret : List E → Prop) :
    Stmt.Holds C rd σ (.match_ x arms) next kret ↔
      ∃ (j : Nat) (h : j < arms.length), σ x = ofK (gpow j) ∧
        Stmt.HoldsList C rd σ arms[j] next kret := by
  simp only [Stmt.Holds, holdsArms_iff, Nat.zero_add]

/-- A fused `match` of calls holds of one callee `j < fs.length`, at `x = g^j`. -/
theorem holds_dispatch_iff (x : V) (fs : List String) (args rets : List V) (next : Prop)
    (kret : List E → Prop) :
    Stmt.Holds C rd σ (.dispatch x fs args rets) next kret ↔
      (∃ (j : Nat) (h : j < fs.length), σ x = ofK (gpow j) ∧
        C fs[j] (args.map σ) (rets.map σ)) ∧ next := Iff.rfl

/-- A call holds exactly when the call relation relates its argument and return words. -/
theorem holds_call_iff (f : String) (args rets : List V) (next : Prop) (kret : List E → Prop) :
    Stmt.Holds C rd σ (.call f args rets) next kret ↔ C f (args.map σ) (rets.map σ) ∧ next :=
  Iff.rfl

/-! ## Calls -/

/-- One call relation below another. -/
def CallRel.Le (C C' : CallRel) : Prop := ∀ f a r, C f a r → C' f a r

mutual
theorem holds_mono {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ (s : Stmt) {next next' : Prop} {kret kret' : List E → Prop}, (next → next') →
      (∀ r, kret r → kret' r) → Stmt.Holds C rd σ s next kret → Stmt.Holds C' rd σ s next' kret'
  | .atom _, _, _, _, _, hn, _, h => ⟨h.1, hn h.2⟩
  | .ite _ z n, _, _, _, _, hn, hk, h =>
      ⟨h.1, fun hc => holdsList_mono hC z hn hk (h.2.1 hc),
        fun hc => holdsList_mono hC n hn hk (h.2.2 hc)⟩
  | .match_ x arms, _, _, _, _, hn, hk, h => holdsArms_mono hC x arms 0 hn hk h
  | .call .., _, _, _, _, hn, _, h => ⟨hC _ _ _ h.1, hn h.2⟩
  | .callIf .., _, _, _, _, hn, _, h => ⟨h.1, fun hc => hC _ _ _ (h.2.1 hc), hn h.2.2⟩
  | .dispatch .., _, _, _, _, hn, _, h =>
      ⟨let ⟨j, hj, hx, hc⟩ := h.1; ⟨j, hj, hx, hC _ _ _ hc⟩, hn h.2⟩
  | .ret _, _, _, _, _, _, hk, h => hk _ h

theorem holdsList_mono {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ (ss : List Stmt) {next next' : Prop} {kret kret' : List E → Prop}, (next → next') →
      (∀ r, kret r → kret' r) → Stmt.HoldsList C rd σ ss next kret →
        Stmt.HoldsList C' rd σ ss next' kret'
  | [], _, _, _, _, hn, _, h => hn h
  | s :: ss, _, _, _, _, hn, hk, h => holds_mono hC s (holdsList_mono hC ss hn hk) hk h

theorem holdsArms_mono {C C' : CallRel} (hC : CallRel.Le C C') (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) {next next' : Prop} {kret kret' : List E → Prop},
      (next → next') → (∀ r, kret r → kret' r) → Stmt.HoldsArms C rd σ x j arms next kret →
        Stmt.HoldsArms C' rd σ x j arms next' kret'
  | [], _, _, _, _, _, _, _, h => h
  | a :: as, j, _, _, _, _, hn, hk, h =>
      h.imp (fun h => ⟨h.1, holdsList_mono hC a hn hk h.2⟩) (holdsArms_mono hC x as (j + 1) hn hk)
end

theorem fnSem_mono {C C' : CallRel} (hC : CallRel.Le C C') (f : Fn) (args rets : List E) :
    f.Sem C rd args rets → f.Sem C' rd args rets := fun ⟨σ, hp, h⟩ =>
  ⟨σ, hp, holdsList_mono hC f.body id (fun _ h => h) h⟩

theorem relN_succ (P : Program) : ∀ n, CallRel.Le (P.relN rd n) (P.relN rd (n + 1))
  | 0 => fun _ _ _ h => h.elim
  | n + 1 => fun _ _ _ ⟨fn, hf, h⟩ => ⟨fn, hf, fnSem_mono (relN_succ P n) fn _ _ h⟩

theorem relN_mono (P : Program) {m n : Nat} (h : m ≤ n) : CallRel.Le (P.relN rd m) (P.relN rd n) := by
  induction h with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun f a r h => relN_succ P _ f a r (ih f a r h)

theorem relN_le_rel (P : Program) (n : Nat) : CallRel.Le (P.relN rd n) (P.Rel rd) :=
  fun _ _ _ h => ⟨n, h⟩

/-- A family of continuations, monotone in the call relation and reached at a finite depth. -/
structure Finitary (P : Program) (rd : Reader) (F : CallRel → Prop) : Prop where
  mono : ∀ C C', CallRel.Le C C' → F C → F C'
  finite : F (P.Rel rd) → ∃ n, F (P.relN rd n)

mutual
theorem holds_finite (P : Program) :
    ∀ (s : Stmt) (F : CallRel → Prop) (kret : List E → Prop), Finitary P rd F →
      Stmt.Holds (P.Rel rd) rd σ s (F (P.Rel rd)) kret →
        ∃ n, Stmt.Holds (P.relN rd n) rd σ s (F (P.relN rd n)) kret
  | .atom _, F, _, hF, h => (hF.finite h.2).imp fun _ hn => ⟨h.1, hn⟩
  | .ite c z n', F, kret, hF, h => by
      by_cases hc : σ c = 0
      · obtain ⟨n, hn⟩ := holdsList_finite P z F kret hF (h.2.1 hc)
        exact ⟨n, h.1, fun _ => hn, fun hc' => absurd hc hc'⟩
      · obtain ⟨n, hn⟩ := holdsList_finite P n' F kret hF (h.2.2 hc)
        exact ⟨n, h.1, fun hc' => absurd hc' hc, fun _ => hn⟩
  | .match_ x arms, F, kret, hF, h => holdsArms_finite P x arms 0 F kret hF h
  | .call f args rets, F, _, hF, h => by
      obtain ⟨n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, relN_mono P (le_max_left _ _) _ _ _ h1,
        hF.mono _ _ (relN_mono P (le_max_right _ _)) h2⟩
  | .callIf c f args, F, _, hF, h => by
      obtain ⟨n2, h2⟩ := hF.finite h.2.2
      by_cases hc : σ c ≠ 0
      · obtain ⟨n1, h1⟩ := h.2.1 hc
        exact ⟨max n1 n2, h.1, fun _ => relN_mono P (le_max_left _ _) _ _ _ h1,
          hF.mono _ _ (relN_mono P (le_max_right _ _)) h2⟩
      · exact ⟨n2, h.1, fun hc' => absurd hc' hc, h2⟩
  | .dispatch x fs args rets, F, _, hF, h => by
      obtain ⟨j, hj, hx, n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, ⟨j, hj, hx, relN_mono P (le_max_left _ _) _ _ _ h1⟩,
        hF.mono _ _ (relN_mono P (le_max_right _ _)) h2⟩
  | .ret _, _, _, _, h => ⟨0, h⟩

theorem holdsList_finite (P : Program) :
    ∀ (ss : List Stmt) (F : CallRel → Prop) (kret : List E → Prop), Finitary P rd F →
      Stmt.HoldsList (P.Rel rd) rd σ ss (F (P.Rel rd)) kret →
        ∃ n, Stmt.HoldsList (P.relN rd n) rd σ ss (F (P.relN rd n)) kret
  | [], _, _, hF, h => hF.finite h
  | s :: ss, F, kret, hF, h =>
      holds_finite P s (fun C => Stmt.HoldsList C rd σ ss (F C) kret) kret
        ⟨fun C C' hC h => holdsList_mono hC ss (hF.mono C C' hC) (fun _ h => h) h,
          holdsList_finite P ss F kret hF⟩ h

theorem holdsArms_finite (P : Program) (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) (F : CallRel → Prop) (kret : List E → Prop),
      Finitary P rd F → Stmt.HoldsArms (P.Rel rd) rd σ x j arms (F (P.Rel rd)) kret →
        ∃ n, Stmt.HoldsArms (P.relN rd n) rd σ x j arms (F (P.relN rd n)) kret
  | [], _, _, _, _, h => h.elim
  | a :: as, j, F, kret, hF, h => by
      rcases h with ⟨hx, ha⟩ | ha
      · exact (holdsList_finite P a F kret hF ha).imp fun _ hn => Or.inl ⟨hx, hn⟩
      · exact (holdsArms_finite P x as (j + 1) F kret hF ha).imp fun _ hn => Or.inr hn
end

/-- `Program.Rel` is a fixed point: a call holds exactly when the callee's body does, its own
calls under `Program.Rel`. -/
theorem rel_iff (P : Program) (f : String) (args rets : List E) :
    P.Rel rd f args rets ↔ ∃ fn, P.find? f = some fn ∧ fn.Sem (P.Rel rd) rd args rets := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n =>
        obtain ⟨fn, hf, h⟩ := hn
        exact ⟨fn, hf, fnSem_mono (relN_le_rel P n) fn args rets h⟩
  · rintro ⟨fn, hf, σ, hp, h⟩
    obtain ⟨n, hn⟩ := holdsList_finite (σ := σ) P fn.body (fun _ => False) (fun rs => rs = rets)
      ⟨fun _ _ _ h => h, fun h => h.elim⟩ h
    exact ⟨n + 1, fn, hf, σ, hp, hn⟩

/-! ## Range checks -/

theorem read_some_iff {κ : Nat} (hκ : κ < 64) (L : MemImage κ) (a : K) (w : E) :
    L.read a = some w ↔ ∃ i : Fin (2 ^ κ), a = gpow i ∧ L i = w := by
  unfold MemImage.read
  constructor
  · intro h
    obtain ⟨i, hi, hw⟩ := Option.map_eq_some_iff.mp h
    exact ⟨i, (gLog?_spec hκ).mp hi, hw⟩
  · rintro ⟨i, rfl, rfl⟩
    rw [(gLog?_spec hκ).mpr rfl]
    rfl

theorem eq_ofK_limb {x : E} (h : IsInK x) : x = ofK (x.limb 0) := by
  rw [ofK_eq_ofLimbs, ofLimbs_of_isInK h]

/-- A range check's meaning: on a memory of `2^κ ≤ 2^32` words, `x` passes the check against
`g^(K-1)`, for some complement and touched words, exactly when `x = g^e` with `e < K`, for
`1 ≤ K ≤ 2^κ`. The compiler's cap `K ≤ 2^16` is this bound at the least memory size. -/
theorem rangeCheck_iff {κ : Nat} (hκ : κ ≤ 32) (L : MemImage κ) (x : E) {K : Nat}
    (hK1 : 1 ≤ K) (hK : K ≤ 2 ^ κ) :
    (∃ y t1 t2 : E, LoadHolds L.read x 0 t1 ∧ ofK (gpow (K - 1)) = x * y ∧ LoadHolds L.read y 0 t2) ↔
      ∃ e < K, x = ofK (gpow e) := by
  have hκ64 : κ < 64 := by omega
  have h32 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
  constructor
  · rintro ⟨y, t1, t2, ⟨hx, h1⟩, hk, ⟨hy, h2⟩⟩
    rw [gpow, pow_zero, mul_one] at h1 h2
    obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp h1
    obtain ⟨j, hj, -⟩ := (read_some_iff hκ64 L _ _).mp h2
    have ex : x = ofK (gpow i) := by rw [eq_ofK_limb hx, hi]
    have ey : y = ofK (gpow j) := by rw [eq_ofK_limb hy, hj]
    rw [ex, ey, ← ofK_mul, gpow, gpow, ← pow_add] at hk
    have hij := gpow_injOn (by have := i.isLt; have := j.isLt; simp only [Set.mem_Iio]; omega)
      (by simp only [Set.mem_Iio]; omega) (ofK_injective hk).symm
    exact ⟨i, by omega, ex⟩
  · rintro ⟨e, he, rfl⟩
    have he' : e < 2 ^ κ := by omega
    have hc : K - 1 - e < 2 ^ κ := by omega
    refine ⟨ofK (gpow (K - 1 - e)), L ⟨e, he'⟩, L ⟨K - 1 - e, hc⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
    · exact (isInK_iff _).mpr ⟨_, rfl⟩
    · rw [limb_ofK]
      simp only [gpow, pow_zero, mul_one]
      exact (read_some_iff hκ64 L _ _).mpr ⟨⟨e, he'⟩, rfl, rfl⟩
    · rw [← ofK_mul, gpow, gpow, ← pow_add]
      congr 2
      omega
    · exact (isInK_iff _).mpr ⟨_, rfl⟩
    · rw [limb_ofK]
      simp only [gpow, pow_zero, mul_one]
      exact (read_some_iff hκ64 L _ _).mpr ⟨⟨K - 1 - e, hc⟩, rfl, rfl⟩

/-- The range-check atom, its auxiliary values chosen freely, is `rangeCheck_iff`'s relation. -/
theorem holds_rangeCheck (x y t1 t2 k : V) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd σ ↔
      LoadHolds rd (σ x) 0 (σ t1) ∧ σ k = σ x * σ y ∧ LoadHolds rd (σ y) 0 (σ t2) := Iff.rfl

end
end LeanVM.Guest.Core
