/-
  LeanVM.Guest.B1.Sig.WotsArm

  The arms of a WOTS+C group are in single-assignment form and complete: arm `0` lays the slots out,
  every other arm writes them from its own fresh values.
-/

module

public import LeanVM.Guest.B1.Sig.WotsComplete

/-!
# The arms, complete

* `walkSum`, `walkBase_eq`: where a walk starts;
* `walkLay_zero`, `walkLay_pos`: the walks of arm `0` and of a later arm are laid out
  (`WalkLay`), their regions apart;
* `armT_ssa`, `armT_canon`: an arm is in single-assignment form, its `KECCAK`s on canonical
  inputs;
* `armBase_*`: the arms' bases.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The fresh values of walks `r ..< r + t` of arm `k`. -/
def walkSum (stride k : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | r, t + 1 => walkSize stride (dig k r) + walkSum stride k (r + 1) t

theorem walkSum_succ (stride k : Nat) : ∀ (r t : Nat),
    walkSum stride k r (t + 1) = walkSum stride k r t + walkSize stride (dig k (r + t))
  | r, 0 => by simp [walkSum]
  | r, t + 1 => by
      rw [walkSum, walkSum_succ stride k (r + 1) t, walkSum, show r + 1 + t = r + (t + 1) by omega]
      omega

theorem walkBase_eq (stride k : Nat) : ∀ (r t b : Nat), walkBase stride k r t b = b + walkSum stride k r t
  | _, 0, _ => rfl
  | r, t + 1, b => by
      rw [walkBase, walkBase_eq stride k (r + 1) t, walkSum]
      simp only [dig]
      omega

theorem walkSum_zero_digits (S : Nat) : ∀ (r t : Nat), walkSum S 0 r t = t * (1 + 3 * S)
  | _, 0 => by simp [walkSum]
  | r, t + 1 => by
      rw [walkSum, walkSum_zero_digits S (r + 1) t]
      simp [walkSize, dig]
      ring

/-- The region of the walks of arm `k` from `b0`, stride `S`. -/
def WalksR (slots : Nat → Nat → Nat) (S k n b0 : Nat) (x : V) : Prop :=
  ∃ t < n, WalkR (slots t) S (dig k t) (walkBase S k 0 t b0) x

theorem ssa_single_atom {a : Atom} (hd : DefOK a) (hr : ∀ v ∈ aOuts a, v ∉ aReads a) : SSA [.atom a] :=
  ⟨hd, hr, fun _ h => by simp [outsList] at h, trivial⟩

/-- **An arm is in single-assignment form.** -/
theorem armT_ssa {W : WotsT} {B : Nat} (hW : StepShape W B) {slots : Nat → Nat → Nat}
    {first n : Nat} {fold : Bool} {prodIn encIn : V} {po eo k b : Nat}
    (hwl : ∀ t < n, WalkLay W B (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
      (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b)))
    (hwd : ∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b)) x →
      ¬ WalkR (slots t') (if k = 0 then W.size + 1 else W.size) (dig k t')
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t' (if fold then b + 1 else b)) x)
    (hpi : NBv B prodIn) (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n)))
    (hpe : po ≠ eo) (hpoB : B ≤ po) (heoB : B ≤ eo)
    (hfold : fold = true → b ≠ po ∧ b ≠ eo)
    (hR : ∀ x, WalksR slots (if k = 0 then W.size + 1 else W.size) k n (if fold then b + 1 else b) x →
      x ≠ .n po ∧ x ≠ .n eo ∧ (fold = true → x ≠ .n b) ∧
      (k ≠ 0 → x ≠ .n (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2))
    (hws : k ≠ 0 → ¬ NBv B (.n (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2) ∧
      (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2 ≠ po ∧
      (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2 ≠ eo ∧
      (fold = true → (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2 ≠ b)) :
    SSA (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1 ∧
      ∀ x ∈ outsList (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1,
        WalksR slots (if k = 0 then W.size + 1 else W.size) k n (if fold then b + 1 else b) x ∨
        x = .n po ∨ x = .n eo ∨ (fold = true ∧ x = .n b) ∨
        (k ≠ 0 ∧ x = .n (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2) := by
  obtain ⟨w1, w2, w3⟩ := walksT_ssa hW slots first k (if k = 0 then W.size + 1 else W.size) n 0
    (if fold then b + 1 else b) (by simpa using hwl) (by simpa using hwd)
  simp only [Nat.zero_add] at w2 w3
  have hnb : ∀ {x : V} {j : Nat}, B ≤ j → x = .n j → ¬ NBv B x := by
    rintro x j hj rfl ⟨i, hi, e⟩
    simp only [V.mk.injEq, true_and] at e
    omega
  -- the product
  have hprod : SSA [if fold = true then copyS (.n po) (W.power (digitSum k n))
      else mulS (.n po) prodIn (W.power (digitSum k n))] := by
    cases fold
    · refine ssa_single_atom trivial ?_
      simp only [aOuts, aReads, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq, not_or]
      exact ⟨fun e => hnb hpoB e.symm hpi, fun e => hnb hpoB e.symm hpw⟩
    · refine ssa_single_atom trivial ?_
      simp only [aOuts, aReads, List.mem_singleton, forall_eq]
      exact fun e => hnb hpoB e.symm hpw
  have hvprod : ∀ x ∈ Stmt.valsList [if fold = true then copyS (.n po) (W.power (digitSum k n))
      else mulS (.n po) prodIn (W.power (digitSum k n))], x = .n po ∨ NBv B x := by
    intro x hx
    cases fold <;> simp [mulS, copyS, Stmt.vals, Atom.vals] at hx <;> rcases hx with rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr hpi | exact Or.inr hpw
  have henc0 : ∀ x, x = (if fold = true then V.n b else encIn) → x ≠ .n eo ∧ (x = .n b ∨ NBv B x) := by
    rintro x rfl
    cases fold
    · exact ⟨fun e => hnb heoB e hei, Or.inr hei⟩
    · exact ⟨fun e => by simp at e; exact (hfold rfl).2 e, Or.inl rfl⟩
  -- the prefix
  have hpre : SSA (if fold = true then [cst b (word 0 0)] else []) ∧
      (∀ x ∈ Stmt.valsList (if fold = true then [cst b (word 0 0)] else []), fold = true ∧ x = .n b) ∧
      (∀ x ∈ outsList (if fold = true then [cst b (word 0 0)] else []), fold = true ∧ x = .n b) := by
    cases fold
    · exact ⟨trivial, by simp, by simp [outsList]⟩
    · refine ⟨ssa_single_atom trivial (by simp [aReads]), ?_, ?_⟩ <;>
        simp [cst, Stmt.vals, Atom.vals, outsList, aOuts]
  have hpw : SSA ((if fold = true then [cst b (word 0 0)] else []) ++
      (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold then b + 1 else b)).1) :=
    SSA.append' hpre.1 w1 (P := fun x => fold = true ∧ x = .n b)
      (Q := WalksR slots (if k = 0 then W.size + 1 else W.size) k n (if fold then b + 1 else b))
      hpre.2.1 w2 (fun x hx ⟨hf, e⟩ => (hR x hx).2.2.1 hf e)
  have hvpw : ∀ x ∈ Stmt.valsList ((if fold = true then [cst b (word 0 0)] else []) ++
      (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold then b + 1 else b)).1),
      (fold = true ∧ x = .n b) ∨ NBv B x ∨
        WalksR slots (if k = 0 then W.size + 1 else W.size) k n (if fold then b + 1 else b) x := by
    intro x hx
    rw [valsList_append] at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl (hpre.2.1 x h)
    · exact Or.inr (w3 x h)
  have hopw : ∀ x ∈ outsList ((if fold = true then [cst b (word 0 0)] else []) ++
      (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold then b + 1 else b)).1),
      (fold = true ∧ x = .n b) ∨
        WalksR slots (if k = 0 then W.size + 1 else W.size) k n (if fold then b + 1 else b) x := by
    intro x hx
    rw [outsList_append] at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl (hpre.2.2 x h)
    · exact Or.inr (w2 x h)
  unfold armT
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte] at hpw hvpw hopw ⊢
    have htail : SSA ([if fold = true then copyS (.n po) (W.power (digitSum 0 n))
        else mulS (.n po) prodIn (W.power (digitSum 0 n))] ++ [copyS (.n eo) (if fold = true then V.n b else encIn)]) :=
      SSA.append' hprod (ssa_single_atom trivial (by
        simp only [aOuts, aReads, List.mem_singleton, forall_eq]
        exact fun e => (henc0 _ rfl).1 e.symm)) hvprod (Q := fun x => x = .n eo)
        (fun x hx => by simpa [copyS, outsList, aOuts] using hx) (fun x e h => by
          subst e
          rcases h with e | h
          · simp only [V.mk.injEq, true_and] at e; exact hpe e.symm
          · exact hnb heoB rfl h)
    refine ⟨SSA.append' hpw htail hvpw (Q := fun x => x = .n po ∨ x = .n eo) ?_ ?_, ?_⟩
    · intro x hx
      cases fold <;> simp [mulS, copyS, outsList, aOuts] at hx <;> tauto
    · rintro x (rfl | rfl) (⟨hf, e⟩ | h | h)
      · simp only [V.mk.injEq, true_and] at e; exact (hfold hf).1 e.symm
      · exact hnb hpoB rfl h
      · exact (hR _ h).1 rfl
      · simp only [V.mk.injEq, true_and] at e; exact (hfold hf).2 e.symm
      · exact hnb heoB rfl h
      · exact (hR _ h).2.1 rfl
    · intro x hx
      rw [outsList_append] at hx
      rcases List.mem_append.mp hx with h | h
      · rcases hopw x h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inl h
      · cases fold <;> simp [mulS, copyS, outsList, aOuts] at h <;> rcases h with rfl | rfl <;> simp
  · simp only [hk, ↓reduceIte] at hpw hvpw hopw hR ⊢
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hws hk
    set w2 := (walksT W slots first k W.size n 0 (if fold = true then b + 1 else b)).2 with hw2def
    have ht2 : SSA ([cst w2 (lit (W.enc first n k))] ++
        [addS (.n eo) (if fold = true then V.n b else encIn) (.n w2)]) :=
      SSA.append' (ssa_single_atom trivial (by simp [aReads]))
        (ssa_single_atom trivial (by
          simp only [aOuts, aReads, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq, not_or]
          refine ⟨fun e => (henc0 _ rfl).1 e.symm, fun e => ?_⟩
          simp only [V.mk.injEq, true_and] at e
          exact hw3 e.symm))
        (P := fun x => x = .n w2) (Q := fun x => x = .n eo)
        (fun x hx => by simpa [cst, Stmt.vals, Atom.vals] using hx)
        (fun x hx => by simpa [addS, outsList, aOuts] using hx)
        (fun x e1 e2 => by subst e1; simp only [V.mk.injEq, true_and] at e2; exact hw3 e2.symm)
    have htail : SSA ([if fold = true then copyS (.n po) (W.power (digitSum k n))
        else mulS (.n po) prodIn (W.power (digitSum k n))] ++ ([cst w2 (lit (W.enc first n k))] ++
        [addS (.n eo) (if fold = true then V.n b else encIn) (.n w2)])) :=
      SSA.append' hprod ht2 hvprod (Q := fun x => x = .n w2 ∨ x = .n eo)
        (fun x hx => by simp [cst, addS, outsList, aOuts] at hx; tauto)
        (fun x hx h => by
          rcases hx with rfl | rfl <;> rcases h with e | h
          · simp only [V.mk.injEq, true_and] at e; exact hw2 e
          · exact hw1 h
          · simp only [V.mk.injEq, true_and] at e; exact hpe e.symm
          · exact hnb heoB rfl h)
    refine ⟨SSA.append' hpw htail hvpw (Q := fun x => x = .n po ∨ x = .n w2 ∨ x = .n eo) ?_ ?_, ?_⟩
    · intro x hx
      cases fold <;> simp [mulS, copyS, cst, addS, outsList, aOuts] at hx <;> tauto
    · rintro x (rfl | rfl | rfl) (⟨hf, e⟩ | h | h)
      · simp only [V.mk.injEq, true_and] at e; exact (hfold hf).1 e.symm
      · exact hnb hpoB rfl h
      · exact (hR _ h).1 rfl
      · simp only [V.mk.injEq, true_and] at e; exact hw4 hf e
      · exact hw1 h
      · exact (hR _ h).2.2.2 hk rfl
      · simp only [V.mk.injEq, true_and] at e; exact (hfold hf).2 e.symm
      · exact hnb heoB rfl h
      · exact (hR _ h).2.1 rfl
    · intro x hx
      rw [outsList_append] at hx
      rcases List.mem_append.mp hx with h | h
      · rcases hopw x h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inl h
      · cases fold <;> simp [mulS, copyS, cst, addS, outsList, aOuts] at h <;>
          rcases h with rfl | rfl | rfl <;> simp [hk]

theorem kcanon_noKec {σ : Val} {ss : List Stmt}
    (h : ∀ x ∈ ss, ∀ ins outs i o, x ≠ .atom (.keccak ins outs i o)) : KCanon σ ss :=
  fun ins outs i o hm => absurd rfl (h _ hm ins outs i o)

/-- **An arm's `KECCAK`s read canonical inputs**, and its tips are canonical. -/
theorem armT_canon {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {slots : Nat → Nat → Nat} {first n : Nat} {fold : Bool}
    {prodIn encIn : V} {po eo k b : Nat}
    (hwl : ∀ t < n, WalkLay W B (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
      (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b)))
    (hwd : ∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b)) x →
      ¬ WalkR (slots t') (if k = 0 then W.size + 1 else W.size) (dig k t')
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t' (if fold then b + 1 else b)) x)
    (hB : B ≤ b)
    (hR : ∀ x, WalksR slots (if k = 0 then W.size + 1 else W.size) k n (if fold then b + 1 else b) x →
      x ≠ .n po ∧ x ≠ .n eo ∧ (fold = true → x ≠ .n b) ∧
      (k ≠ 0 → x ≠ .n (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2))
    (hssa : SSA (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1)
    (σ : Val) (hg : good σ)
    (hs : ∀ t < n, StartCanon σ (slots t) (dig k t)
      (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b))) :
    KCanon (fwd (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1 σ)
        (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1 ∧
      ∀ t < n, IsCanonical128 (fwd (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1 σ
        (.n (slots t 2))) := by
  have hpreK : KCanon (fwd (if fold = true then [cst b (word 0 0)] else []) σ) (if fold = true then [cst b (word 0 0)] else []) := kcanon_noKec (by
    intro x hx ins outs i o e
    subst e
    cases fold <;> simp [cst] at hx)
  have hσ1 : AgreeBelow B σ (fwd (if fold = true then [cst b (word 0 0)] else []) σ) := fwd_agree (by
    intro v hv ⟨j, hj, e⟩
    subst e
    cases fold <;> simp [cst, outsList, aOuts] at hv
    omega) σ
  have hg1 := hc.1 _ _ hσ1 hg
  have hs1 : ∀ t < n, StartCanon (fwd (if fold = true then [cst b (word 0 0)] else []) σ) (slots t) (dig k t) (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold = true then b + 1 else b)) := by
    intro t ht
    have := hs t ht
    unfold StartCanon at this ⊢
    rw [fwd_of_not_mem _ _ fun hm => ?_]
    · exact this
    · cases fold
      · simp [outsList] at hm
      · simp only [↓reduceIte, cst, outsList, aOuts, List.append_nil, List.mem_singleton] at hm
        refine (hR _ ⟨t, ht, ?_⟩).2.2.1 rfl hm
        by_cases h3 : dig k t = 3
        · simp only [walkStartV, h3, ↓reduceIte]
          exact Or.inr ⟨2, by omega, 0, by omega, by simp⟩
        · simp only [walkStartV, h3, ↓reduceIte]
          exact Or.inl ⟨0, by simp [walkSize, h3], by simp⟩
  obtain ⟨w1, w2⟩ := walksT_canon hW hc slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold = true then b + 1 else b) (by simpa using hwl) (by simpa using hwd)
    (fwd (if fold = true then [cst b (word 0 0)] else []) σ) hg1 (by simpa using hs1)
  simp only [Nat.zero_add] at w2
  have fin : ∀ tail : List Stmt, (∀ x ∈ tail, ∀ ins outs i o, x ≠ .atom (.keccak ins outs i o)) →
      (∀ v ∈ outsList tail, ∀ t < n, v ≠ .n (slots t 2)) →
      SSA ((if fold = true then [cst b (word 0 0)] else []) ++ (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold = true then b + 1 else b)).1 ++ tail) →
      KCanon (fwd ((if fold = true then [cst b (word 0 0)] else []) ++ (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold = true then b + 1 else b)).1 ++ tail) σ)
          ((if fold = true then [cst b (word 0 0)] else []) ++ (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold = true then b + 1 else b)).1 ++ tail) ∧
        ∀ t < n, IsCanonical128 (fwd ((if fold = true then [cst b (word 0 0)] else []) ++ (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold = true then b + 1 else b)).1 ++ tail) σ
          (.n (slots t 2))) := by
    intro tail hk ho hs'
    refine ⟨KCanon.append (KCanon.append hpreK w1 (SSA.disj (SSA.left hs'))) (kcanon_noKec hk)
      (SSA.disj hs'), fun t ht => ?_⟩
    rw [fwd_append, fwd_append, fwd_of_not_mem _ _ fun hm => ho _ hm t ht rfl]
    exact w2 t ht
  have hsplit : (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1 =
      (if fold = true then [cst b (word 0 0)] else []) ++ (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 (if fold = true then b + 1 else b)).1 ++
        (if k = 0 then [if fold then copyS (.n po) (W.power (digitSum k n))
            else mulS (.n po) prodIn (W.power (digitSum k n)), copyS (.n eo) (if fold then .n b else encIn)]
          else [if fold then copyS (.n po) (W.power (digitSum k n))
            else mulS (.n po) prodIn (W.power (digitSum k n)),
            cst (walksT W slots first k W.size n 0 (if fold = true then b + 1 else b)).2 (lit (W.enc first n k)),
            addS (.n eo) (if fold then .n b else encIn) (.n (walksT W slots first k W.size n 0 (if fold = true then b + 1 else b)).2)]) := by
    unfold armT
    split <;> rfl
  rw [hsplit] at hssa ⊢
  refine fin _ (fun x hx ins outs i o e => ?_) (fun v hv t ht e => ?_) hssa
  · subst e
    revert hx
    split <;> cases fold <;> simp [mulS, copyS, cst, addS]
  · subst e
    have hr := hR (.n (slots t 2)) ⟨t, ht, Or.inr ⟨2, by omega, 0, by omega, by simp⟩⟩
    revert hv
    split <;> cases fold <;> simp [mulS, copyS, cst, addS, outsList, aOuts] <;> simp_all
/-- **An arm's values**: below `B`, in its walks' region, its product's and encoding's cells, its
base and its walks' end. -/
theorem armT_vals {W : WotsT} {B : Nat} (hW : StepShape W B) {slots : Nat → Nat → Nat}
    {first n : Nat} {fold : Bool} {prodIn encIn : V} {po eo k b : Nat}
    (hwl : ∀ t < n, WalkLay W B (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
      (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b)))
    (hwd : ∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b)) x →
      ¬ WalkR (slots t') (if k = 0 then W.size + 1 else W.size) (dig k t')
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t' (if fold then b + 1 else b)) x)
    {P : V → Prop} (hP1 : ∀ x, NBv B x → P x)
    (hP2 : ∀ x, WalksR slots (if k = 0 then W.size + 1 else W.size) k n (if fold then b + 1 else b) x → P x)
    (hP3 : P (.n po) ∧ P (.n eo) ∧ P (.n b) ∧ P prodIn ∧ P encIn ∧ P (W.power (digitSum k n)) ∧
      P (.n (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2)) :
    ∀ x ∈ Stmt.valsList (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1, P x := by
  obtain ⟨-, -, w3⟩ := walksT_ssa hW slots first k (if k = 0 then W.size + 1 else W.size) n 0
    (if fold then b + 1 else b) (by simpa using hwl) (by simpa using hwd)
  simp only [Nat.zero_add] at w3
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hP3
  have hw : ∀ x ∈ Stmt.valsList (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0
      (if fold then b + 1 else b)).1, P x := fun x hx => by
    rcases w3 x hx with h | h
    · exact hP1 x h
    · exact hP2 x h
  unfold armT
  split
  · rename_i hk
    subst hk
    intro x hx
    simp only [valsList_append, List.mem_append] at hx
    rcases hx with (h | h) | h
    · cases fold <;> simp [cst, Stmt.vals, Atom.vals] at h; subst h; exact p3
    · exact hw x h
    · cases fold <;> simp [mulS, copyS, Stmt.vals, Atom.vals] at h <;> rcases h with h | h | h | h <;>
        try (subst h; assumption)
      all_goals (rcases h with rfl | rfl <;> assumption)
  · rename_i hk
    intro x hx
    simp only [valsList_append, List.mem_append] at hx
    rcases hx with (h | h) | h
    · cases fold <;> simp [cst, Stmt.vals, Atom.vals] at h; subst h; exact p3
    · exact hw x (by simpa [hk] using h)
    · cases fold <;> simp [mulS, copyS, cst, addS, Stmt.vals, Atom.vals] at h <;>
        rcases h with h | h | h | h | h | h | h <;> (try subst h) <;> assumption

end
end LeanVM.Guest.B1.Sig
