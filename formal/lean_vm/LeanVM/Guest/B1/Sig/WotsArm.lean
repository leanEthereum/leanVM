/-
  LeanVM.Guest.B1.Sig.WotsArm

  The arms of a WOTS+C group are in single-assignment form and complete: arm `0` lays the slots out,
  every other arm writes them from its own fresh values.
-/

module

public import LeanVM.Guest.B1.Sig.WotsComplete
import LeanVM.Guest.StmtsAppend

/-!
# The arms, complete

* `walkSum`, `walkBase_eq`: where a walk starts;
* `armT_ssa`: an arm is in single-assignment form;
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
      (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t b))
    (hwd : ∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t b) x →
      ¬ WalkR (slots t') (if k = 0 then W.size + 1 else W.size) (dig k t')
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t' b) x)
    (hpi : NBv B prodIn) (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n)))
    (hpe : po ≠ eo) (hpoB : B ≤ po) (heoB : B ≤ eo)
    (hR : ∀ x, WalksR slots (if k = 0 then W.size + 1 else W.size) k n b x →
      x ≠ .n po ∧ x ≠ .n eo ∧ (k ≠ 0 → x ≠ .n (walksT W slots first k W.size n 0 b).2))
    (hws : k ≠ 0 → ¬ NBv B (.n (walksT W slots first k W.size n 0 b).2) ∧
      (walksT W slots first k W.size n 0 b).2 ≠ po ∧ (walksT W slots first k W.size n 0 b).2 ≠ eo) :
    SSA (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1 ∧
      ∀ x ∈ outsList (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1,
        WalksR slots (if k = 0 then W.size + 1 else W.size) k n b x ∨
        x = .n po ∨ x = .n eo ∨ (fold = false ∧ k ≠ 0 ∧ x = .n (walksT W slots first k W.size n 0 b).2) := by
  obtain ⟨w1, w2, w3⟩ := walksT_ssa hW slots first k (if k = 0 then W.size + 1 else W.size) n 0 b
    (by simpa using hwl) (by simpa using hwd)
  simp only [Nat.zero_add] at w2 w3
  have hnb : ∀ {x : V} {j : Nat}, B ≤ j → x = .n j → ¬ NBv B x := by
    rintro x j hj rfl ⟨i, hi, e⟩
    simp only [V.mk.injEq, true_and] at e
    omega
  -- the walks, then a tail whose outputs are neither below `B` nor in the walks
  have hcat : ∀ (T : List Stmt) (Q : V → Prop), SSA T → (∀ x ∈ outsList T, Q x) →
      (∀ x, Q x → ¬ NBv B x ∧ ¬ WalksR slots (if k = 0 then W.size + 1 else W.size) k n b x) →
      SSA ((walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 b).1 ++ T) :=
    fun T Q hT hQ hd => SSA.append' w1 hT w3 hQ fun x hq hp => by
      rcases hp with h | h
      · exact (hd x hq).1 h
      · exact (hd x hq).2 h
  have hpoQ : ¬ NBv B (.n po) ∧ ¬ WalksR slots (if k = 0 then W.size + 1 else W.size) k n b (.n po) :=
    ⟨hnb hpoB rfl, fun h => (hR _ h).1 rfl⟩
  have heoQ : ¬ NBv B (.n eo) ∧ ¬ WalksR slots (if k = 0 then W.size + 1 else W.size) k n b (.n eo) :=
    ⟨hnb heoB rfl, fun h => (hR _ h).2.1 rfl⟩
  have hout : ∀ T : List Stmt, (∀ x ∈ outsList T, x = .n po ∨ x = .n eo ∨
      (fold = false ∧ k ≠ 0 ∧ x = .n (walksT W slots first k W.size n 0 b).2)) →
      ∀ x ∈ outsList ((walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 b).1 ++ T),
        WalksR slots (if k = 0 then W.size + 1 else W.size) k n b x ∨ x = .n po ∨ x = .n eo ∨
        (fold = false ∧ k ≠ 0 ∧ x = .n (walksT W slots first k W.size n 0 b).2) := fun T hT x hx => by
    rw [outsList_append] at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl (w2 x h)
    · exact Or.inr (hT x h)
  -- the product, then the encoding `E` written once at `eo`
  have hpe' : V.n eo ≠ V.n po := fun e => by simp only [V.mk.injEq, true_and] at e; exact hpe e.symm
  have hprodE : ∀ (p : Stmt) (a : Atom), SSA [p] → (∀ x ∈ Stmt.valsList [p], x = .n po ∨ NBv B x) →
      (∀ x ∈ outsList [p], x = .n po) → DefOK a → (∀ v ∈ aOuts a, v ∉ aReads a) → aOuts a = [.n eo] →
      SSA ([p] ⧺ [.atom a]) ∧ ∀ x ∈ outsList ([p] ⧺ [.atom a]), x = .n po ∨ x = .n eo :=
    fun p a hp hv ho hd hr he => ⟨SSA.append' hp (ssa_single_atom hd hr) hv (Q := fun x => x = .n eo)
      (fun x hx => by simpa [outsList, he] using hx) (fun x e h => by
        subst e
        rcases h with e | h
        · exact hpe' e
        · exact hnb heoB rfl h), fun x hx => by
      rw [outsList_append] at hx
      rcases List.mem_append.mp hx with h | h
      · exact Or.inl (ho x h)
      · right; simpa [outsList, he] using h⟩
  cases fold
  · have hmul : SSA [mulS (.n po) prodIn (W.power (digitSum k n))] :=
      ssa_single_atom trivial (by
        simp only [aOuts, aReads, List.mem_cons, List.not_mem_nil, or_false, forall_eq, not_or]
        exact ⟨fun e => hnb hpoB e.symm hpi, fun e => hnb hpoB e.symm hpw⟩)
    have hvmul : ∀ x ∈ Stmt.valsList [mulS (.n po) prodIn (W.power (digitSum k n))], x = .n po ∨ NBv B x := by
      intro x hx
      simp [mulS, Stmt.vals, Atom.vals] at hx
      rcases hx with rfl | rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr hpi | exact Or.inr hpw
    have homul : ∀ x ∈ outsList [mulS (.n po) prodIn (W.power (digitSum k n))], x = .n po := by
      intro x hx; simpa [mulS, outsList, aOuts] using hx
    by_cases hk : k = 0
    · subst hk
      simp only [armT, ↓reduceIte, Bool.false_eq_true]
      obtain ⟨t1, t2⟩ := hprodE _ (.copy (.n eo) encIn) hmul hvmul homul trivial
        (by simp only [aOuts, aReads, List.mem_singleton, forall_eq]; exact fun e => hnb heoB e.symm hei) rfl
      refine ⟨hcat _ (fun x => x = .n po ∨ x = .n eo) t1 t2 ?_, fun x hx => ?_⟩
      · rintro x (rfl | rfl)
        · exact hpoQ
        · exact heoQ
      · have := hout _ (fun y hy => by
          rcases t2 y hy with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)) x hx
        simpa using this
    · simp only [armT, hk, ↓reduceIte, Bool.false_eq_true] at hcat hout hpoQ heoQ hR ⊢
      obtain ⟨hw1, hw2, hw3⟩ := hws hk
      set w2 := (walksT W slots first k W.size n 0 b).2 with hw2def
      have hnw : ∀ {j : Nat}, j ≠ w2 → V.n j ≠ V.n w2 := fun h e => by
        simp only [V.mk.injEq, true_and] at e; exact h e
      have ht2 : SSA ([cst w2 (lit (W.enc first n k))] ++ [addS (.n eo) encIn (.n w2)]) :=
        SSA.append' (ssa_single_atom trivial (by simp [aReads]))
          (ssa_single_atom trivial (by
            simp only [aOuts, aReads, List.mem_cons, List.not_mem_nil, or_false,
              forall_eq, not_or]
            exact ⟨fun e => hnb heoB e.symm hei, hnw (Ne.symm hw3)⟩))
          (P := fun x => x = .n w2) (Q := fun x => x = .n eo)
          (fun x hx => by simpa [cst, Stmt.vals, Atom.vals] using hx)
          (fun x hx => by simpa [addS, outsList, aOuts] using hx)
          (fun x e1 e2 => by subst e1; exact hnw (Ne.symm hw3) e2)
      have htail : SSA ([mulS (.n po) prodIn (W.power (digitSum k n))] ++
          ([cst w2 (lit (W.enc first n k))] ++ [addS (.n eo) encIn (.n w2)])) :=
        SSA.append' hmul ht2 hvmul (Q := fun x => x = .n w2 ∨ x = .n eo)
          (fun x hx => by simp [cst, addS, outsList, aOuts] at hx; tauto)
          (fun x hx h => by
            rcases hx with rfl | rfl <;> rcases h with e | h
            · exact hnw hw2.symm e.symm
            · exact hw1 h
            · exact hpe' e
            · exact hnb heoB rfl h)
      refine ⟨hcat _ (fun x => x = .n po ∨ x = .n w2 ∨ x = .n eo) htail ?_ ?_, hout _ fun x hx => ?_⟩
      · intro x hx
        simp [mulS, cst, addS, outsList, aOuts] at hx; tauto
      · rintro x (rfl | rfl | rfl)
        · exact hpoQ
        · exact ⟨hw1, fun h => (hR _ h).2.2 hk rfl⟩
        · exact heoQ
      · simp [mulS, cst, addS, outsList, aOuts] at hx
        rcases hx with rfl | rfl | rfl <;> simp [hk]
  · simp only [armT, ↓reduceIte]
    obtain ⟨t1, t2⟩ := hprodE (copyS (.n po) (W.power (digitSum k n))) (.const (.n eo) (lit (W.enc first n k)))
      (ssa_single_atom trivial (by
        simp only [aOuts, aReads, List.mem_singleton, forall_eq]; exact fun e => hnb hpoB e.symm hpw))
      (fun x hx => by
        simp [copyS, Stmt.vals, Atom.vals] at hx
        rcases hx with rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr hpw)
      (fun x hx => by simpa [copyS, outsList, aOuts] using hx) trivial (by simp [aReads]) rfl
    refine ⟨hcat _ (fun x => x = .n po ∨ x = .n eo) t1 t2 ?_, hout _ fun x hx => ?_⟩
    · rintro x (rfl | rfl)
      · exact hpoQ
      · exact heoQ
    · rcases t2 x hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- **An arm's values**: below `B`, in its walks' region, its product's and encoding's cells, its
inputs and its walks' end. -/
theorem armT_vals {W : WotsT} {B : Nat} (hW : StepShape W B) {slots : Nat → Nat → Nat}
    {first n : Nat} {fold : Bool} {prodIn encIn : V} {po eo k b : Nat}
    (hwl : ∀ t < n, WalkLay W B (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
      (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t b))
    (hwd : ∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slots t) (if k = 0 then W.size + 1 else W.size) (dig k t)
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t b) x →
      ¬ WalkR (slots t') (if k = 0 then W.size + 1 else W.size) (dig k t')
        (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t' b) x)
    {P : V → Prop} (hP1 : ∀ x, NBv B x → P x)
    (hP2 : ∀ x, WalksR slots (if k = 0 then W.size + 1 else W.size) k n b x → P x)
    (hP3 : P (.n po) ∧ P (.n eo) ∧ P prodIn ∧ P encIn ∧ P (W.power (digitSum k n)) ∧
      (fold = false → P (.n (walksT W slots first k W.size n 0 b).2))) :
    ∀ x ∈ Stmt.valsList (armT W slots first n fold prodIn encIn (.n po) (.n eo) k b).1, P x := by
  obtain ⟨-, -, w3⟩ := walksT_ssa hW slots first k (if k = 0 then W.size + 1 else W.size) n 0 b
    (by simpa using hwl) (by simpa using hwd)
  simp only [Nat.zero_add] at w3
  obtain ⟨p1, p2, p4, p5, p6, p7⟩ := hP3
  have hw : ∀ x ∈ Stmt.valsList (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 b).1,
      P x := fun x hx => by
    rcases w3 x hx with h | h
    · exact hP1 x h
    · exact hP2 x h
  cases fold
  · by_cases hk : k = 0
    · subst hk
      simp only [armT, ↓reduceIte, Bool.false_eq_true]
      intro x hx
      simp only [valsList_append, List.mem_append] at hx
      rcases hx with h | h
      · exact hw x h
      · simp [mulS, copyS, Stmt.vals, Atom.vals] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> assumption
    · have p7 := p7 rfl
      simp only [armT, hk, ↓reduceIte, Bool.false_eq_true] at hw p7 ⊢
      intro x hx
      simp only [valsList_append, List.mem_append] at hx
      rcases hx with h | h
      · exact hw x h
      · simp [mulS, cst, addS, Stmt.vals, Atom.vals] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · simp only [armT, ↓reduceIte]
    intro x hx
    simp only [valsList_append, List.mem_append] at hx
    rcases hx with h | h
    · exact hw x h
    · simp [copyS, Stmt.vals, Atom.vals] at h
      rcases h with rfl | rfl | rfl <;> assumption

end
end LeanVM.Guest.B1.Sig
