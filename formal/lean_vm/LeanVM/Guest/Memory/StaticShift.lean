/-
  LeanVM.Guest.Memory.StaticShift

  The static checker under raised callee bounds: a `stat` certificate's constant raised by `δ g` at
  its callee `g` raises a block's bound by at most `δ g` a call site of `g`, every arm's sites
  counted (`blockB_shift`, `statB_shift`).
-/

module

public import LeanVM.Guest.Memory.StaticSound

/-!
# Raising a callee's constant

A function's check reads its callees' certificates through a lookup. Raising a `stat` callee's
constant by `δ g` (`ShiftOk`) raises a block's bound by at most the sum of `δ` over its call sites
(`sitesL`, every arm's, by the recursor for the kernel), its terms and preconditions unchanged. So a
caller checked against a callee's bound `0` passes against the bound `C`, its own bound raised by
`C` a site: a callee whose bound is a node's quantity, not its arguments', is checked so.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

@[expose] public section

/-- **`look'` is `look` with some `stat` constants raised**, by `δ g` at `g`. -/
def ShiftOk (look look' : String → Cert) (δ : String → ℕ) : Prop :=
  ∀ g, look' g = look g ∨
    ∃ pre c cs ks, look g = .stat pre ⟨c, cs⟩ ks ∧ look' g = .stat pre ⟨c + δ g, cs⟩ ks

/-- A statement's call sites weighed by `δ`, every arm's, by the recursor. -/
noncomputable def sitesS (δ : String → ℕ) : Stmt → ℕ :=
  Stmt.rec (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun _ ↦ 0) (fun _ _ _ rz rn ↦ rz + rn) (fun _ _ ra ↦ ra) (fun g _ _ ↦ δ g) (fun _ g _ ↦ δ g)
    (fun _ gs _ _ ↦ (gs.map δ).sum) (fun _ ↦ 0) 0 (fun _ _ a b ↦ a + b) 0 (fun _ _ a b ↦ a + b)

/-- A block's call sites weighed by `δ` (`sitesS`). -/
noncomputable def sitesL (δ : String → ℕ) : List Stmt → ℕ :=
  Stmt.rec_1 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun _ ↦ 0) (fun _ _ _ rz rn ↦ rz + rn) (fun _ _ ra ↦ ra) (fun g _ _ ↦ δ g) (fun _ g _ ↦ δ g)
    (fun _ gs _ _ ↦ (gs.map δ).sum) (fun _ ↦ 0) 0 (fun _ _ a b ↦ a + b) 0 (fun _ _ a b ↦ a + b)

/-- Arms' call sites weighed by `δ` (`sitesS`). -/
noncomputable def sitesA (δ : String → ℕ) : List (List Stmt) → ℕ :=
  Stmt.rec_2 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun _ ↦ 0) (fun _ _ _ rz rn ↦ rz + rn) (fun _ _ ra ↦ ra) (fun g _ _ ↦ δ g) (fun _ g _ ↦ δ g)
    (fun _ gs _ _ ↦ (gs.map δ).sum) (fun _ ↦ 0) 0 (fun _ _ a b ↦ a + b) 0 (fun _ _ a b ↦ a + b)

section Eqs

variable (δ : String → ℕ)

theorem sitesL_nil : sitesL δ [] = 0 := rfl
theorem sitesL_atom (a : Atom) (ss : List Stmt) : sitesL δ (.atom a :: ss) = sitesL δ ss :=
  Nat.zero_add _
theorem sitesL_ite (c : V) (z n ss : List Stmt) :
    sitesL δ (.ite c z n :: ss) = sitesL δ z + sitesL δ n + sitesL δ ss := rfl
theorem sitesL_match (x : V) (arms : List (List Stmt)) (ss : List Stmt) :
    sitesL δ (.match_ x arms :: ss) = sitesA δ arms + sitesL δ ss := rfl
theorem sitesL_call (g : String) (a r : List V) (ss : List Stmt) :
    sitesL δ (.call g a r :: ss) = δ g + sitesL δ ss := rfl
theorem sitesL_callIf (c : V) (g : String) (a : List V) (ss : List Stmt) :
    sitesL δ (.callIf c g a :: ss) = δ g + sitesL δ ss := rfl
theorem sitesL_dispatch (x : V) (gs : List String) (a r : List V) (ss : List Stmt) :
    sitesL δ (.dispatch x gs a r :: ss) = (gs.map δ).sum + sitesL δ ss := rfl
theorem sitesL_ret (vs : List V) (ss : List Stmt) : sitesL δ (.ret vs :: ss) = sitesL δ ss :=
  Nat.zero_add _
theorem sitesA_nil : sitesA δ [] = 0 := rfl
theorem sitesA_cons (a : List Stmt) (as : List (List Stmt)) :
    sitesA δ (a :: as) = sitesL δ a + sitesA δ as := rfl

end Eqs

/-- **`r'` within `r` plus `d`**: its constant at most `d` more, the same terms and preconditions. -/
def Acc.Within (r' r : Acc) (d : ℕ) : Prop := r'.1.c ≤ r.1.c + d ∧ r'.1.cs = r.1.cs ∧ r'.2 = r.2

theorem Acc.Within.refl (r : Acc) (d : ℕ) : r.Within r d := ⟨by omega, rfl, rfl⟩

theorem Acc.Within.add {a a' b b' : Acc} {d e : ℕ} (ha : a'.Within a d) (hb : b'.Within b e) :
    (a'.add b').Within (a.add b) (d + e) := by
  obtain ⟨h1, h2, h3⟩ := ha
  obtain ⟨h4, h5, h6⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · simp only [Acc.add, Aff.add]; omega
  · simp only [Acc.add, Aff.add, h2, h5]
  · simp only [Acc.add, h3, h6]

theorem Acc.Within.join {a a' b b' : Acc} {d e : ℕ} (ha : a'.Within a d) (hb : b'.Within b e) :
    (a'.join b').Within (a.join b) (d + e) := by
  obtain ⟨h1, h2, h3⟩ := ha
  obtain ⟨h4, h5, h6⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · simp only [Acc.join]; omega
  · simp only [Acc.join, h2, h5]
  · simp only [Acc.join, h3, h6]

theorem Acc.Within.mono {a a' : Acc} {d e : ℕ} (h : a'.Within a d) (hde : d ≤ e) : a'.Within a e :=
  ⟨by have := h.1; omega, h.2.1, h.2.2⟩

section Shift

variable {look look' : String → Cert} {δ : String → ℕ} {wl : String → Option ℕ} {α : Bool}
  {ks : List (V × ℕ)} {ps : List V} {self : String}

theorem siteB_shift (hsh : ShiftOk look look' δ) {ρ : Env} {g : String} {a : List V} {r : Acc}
    (h : siteB look wl α ρ ps g a = some r) :
    ∃ r', siteB look' wl α ρ ps g a = some r' ∧ r'.Within r (δ g) := by
  rcases hsh g with he | ⟨pre, c, cs, ks', h1, h2⟩
  · refine ⟨r, ?_, Acc.Within.refl r _⟩
    unfold siteB at h ⊢; rw [he]; exact h
  · unfold siteB at h ⊢
    rw [h1] at h; rw [h2]
    simp only [transB] at h ⊢
    obtain ⟨r0, rr, h0, hrr, rfl⟩ := addAcc_some h
    cases h0
    rw [hrr]
    refine ⟨_, rfl, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [Acc.add, Aff.add]; omega
    · simp only [Acc.add, Aff.add]
    · simp only [Acc.add]

theorem siteBC_shift (hsh : ShiftOk look look' δ) {ρ : Env × BEnv} {c : V} {g : String} {a : List V}
    {r : Acc} (h : siteBC look wl α ρ ps c g a = some r) :
    ∃ r', siteBC look' wl α ρ ps c g a = some r' ∧ r'.Within r (δ g) := by
  have hL : ∀ a0 k, siteBL look' wl α ρ.1 ps g a a0 k = siteBL look wl α ρ.1 ps g a a0 k := by
    intro a0 k
    rcases hsh g with he | ⟨pre, c, cs, ks', h1, h2⟩
    · unfold siteBL; rw [he]
    · unfold siteBL; rw [h1, h2]
  unfold siteBC at h ⊢
  split at h
  · rename_i a0 k hg
    rw [hL a0 k]
    split at h
    · cases h; exact ⟨_, rfl, Acc.Within.refl _ _⟩
    · exact siteB_shift hsh h
  · rename_i hg
    exact siteB_shift hsh h

theorem maxB_shift (hsh : ShiftOk look look' δ) {ρ : Env} {a : List V} :
    ∀ {gs : List String} {r : Acc}, maxB (fun g => siteB look wl α ρ ps g a) gs = some r →
      ∃ r', maxB (fun g => siteB look' wl α ρ ps g a) gs = some r' ∧ r'.Within r (gs.map δ).sum
  | [], r, h => ⟨r, h, Acc.Within.refl r _⟩
  | g :: gs, r, h => by
      simp only [maxB] at h ⊢
      obtain ⟨rx, ry, hx, hy, rfl⟩ := maxAcc_some h
      obtain ⟨rx', hx', wx⟩ := siteB_shift hsh hx
      obtain ⟨ry', hy', wy⟩ := maxB_shift hsh hy
      rw [hx', hy']
      exact ⟨_, rfl, by simpa only [List.map_cons, List.sum_cons] using wx.join wy⟩

mutual
/-- **A block's bound under raised callee constants**: within `sitesL δ` more. -/
theorem blockB_shift (hsh : ShiftOk look look' δ) : ∀ (ss : List Stmt) (ρ : Env × BEnv) {r : Acc},
    blockB look wl α ks ps self ρ ss = some r →
      ∃ r', blockB look' wl α ks ps self ρ ss = some r' ∧ r'.Within r (sitesL δ ss)
  | [], _, r, h => by rw [blockB] at h ⊢; exact ⟨r, h, Acc.Within.refl r _⟩
  | s :: ss, ρ, r, h => by
      cases s with
      | atom a =>
          simp only [blockB] at h ⊢
          split at h
          · rename_i r1 ρ' hab
            obtain ⟨r2, rr, h2, hrr, rfl⟩ := addAcc_some h
            cases h2
            obtain ⟨rr', hrr', w⟩ := blockB_shift hsh ss ρ' hrr
            rw [hrr']
            exact ⟨_, rfl, by rw [sitesL_atom]; simpa using (Acc.Within.refl r1 0).add w⟩
          · cases h
      | ite c z n =>
          simp only [blockB] at h ⊢
          obtain ⟨rzn, rr, hzn, hrr, rfl⟩ := addAcc_some h
          obtain ⟨rz, rn, hz, hn, rfl⟩ := maxAcc_some hzn
          obtain ⟨rz', hz', wz⟩ := blockB_shift hsh z ρ hz
          obtain ⟨rn', hn', wn⟩ := blockB_shift hsh n ρ hn
          obtain ⟨rr', hrr', wr⟩ := blockB_shift hsh ss ρ hrr
          rw [hz', hn', hrr']
          exact ⟨_, rfl, by rw [sitesL_ite]; exact (wz.join wn).add wr⟩
      | match_ x arms =>
          simp only [blockB] at h ⊢
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          obtain ⟨ra', ha', wa⟩ := armsB_shift hsh arms ρ ha
          obtain ⟨rr', hrr', wr⟩ := blockB_shift hsh ss ρ hrr
          rw [ha', hrr']
          exact ⟨_, rfl, by rw [sitesL_match]; exact wa.add wr⟩
      | call g a rets =>
          simp only [blockB] at h ⊢
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          obtain ⟨ra', ha', wa⟩ := siteB_shift hsh ha
          obtain ⟨rr', hrr', wr⟩ := blockB_shift hsh ss ρ hrr
          rw [ha', hrr']
          exact ⟨_, rfl, by rw [sitesL_call]; exact wa.add wr⟩
      | callIf c g a =>
          simp only [blockB] at h ⊢
          split at h
          · cases h
          · rename_i hg
            rw [ite_eq_right hg]
            obtain ⟨ra, rpr, ha, hpr, rfl⟩ := addAcc_some h
            obtain ⟨rph, rr, hph, hrr, rfl⟩ := addAcc_some hpr
            obtain ⟨ra', ha', wa⟩ := siteBC_shift hsh ha
            obtain ⟨rr', hrr', wr⟩ := blockB_shift hsh ss ρ hrr
            rw [ha', hph, hrr']
            exact ⟨_, rfl, by
              rw [sitesL_callIf]
              simpa using wa.add ((Acc.Within.refl rph 0).add wr)⟩
      | dispatch x gs a rets =>
          simp only [blockB] at h ⊢
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          obtain ⟨ra', ha', wa⟩ := maxB_shift hsh ha
          obtain ⟨rr', hrr', wr⟩ := blockB_shift hsh ss ρ hrr
          rw [ha', hrr']
          exact ⟨_, rfl, by rw [sitesL_dispatch]; exact wa.add wr⟩
      | ret vs => simp only [blockB] at h ⊢; exact ⟨r, h, Acc.Within.refl r _⟩

/-- `blockB_shift` for arms. -/
theorem armsB_shift (hsh : ShiftOk look look' δ) : ∀ (arms : List (List Stmt)) (ρ : Env × BEnv) {r : Acc},
    armsB look wl α ks ps self ρ arms = some r →
      ∃ r', armsB look' wl α ks ps self ρ arms = some r' ∧ r'.Within r (sitesA δ arms)
  | [], _, r, h => by rw [armsB] at h ⊢; exact ⟨r, h, Acc.Within.refl r _⟩
  | a :: as, ρ, r, h => by
      simp only [armsB] at h ⊢
      obtain ⟨ra, rr, ha, hrr, rfl⟩ := maxAcc_some h
      obtain ⟨ra', ha', wa⟩ := blockB_shift hsh a ρ ha
      obtain ⟨rr', hrr', wr⟩ := armsB_shift hsh as ρ hrr
      rw [ha', hrr']
      exact ⟨_, rfl, by rw [sitesA_cons]; exact wa.join wr⟩
end

/-- **A body's `stat` check under raised callee constants**, its bound raised by `sitesL δ`. -/
theorem statB_shift (hsh : ShiftOk look look' δ) {pre : List (ℕ × ℕ)} {b : Aff} {w : ℕ} {fn : Fn}
    {body : List Stmt} (h : statB look wl α pre b ks w fn body = true) :
    statB look' wl α pre ⟨b.c + sitesL δ body, b.cs⟩ ks w fn body = true := by
  unfold statB at h ⊢
  split at h
  · rename_i r hr
    rw [blockR_eq] at hr
    obtain ⟨r', hr', hw, hcs, hpre⟩ := blockB_shift hsh body ([], []) hr
    rw [blockR_eq, hr']
    simp only [Bool.and_eq_true, Aff.leB, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨⟨by omega, by rw [hcs]; exact h2⟩, by rw [hpre]; exact h3⟩
  · cases h

mutual
/-- `sitesL` of a sum of weights. -/
theorem sitesL_add (δ₁ δ₂ : String → ℕ) :
    ∀ ss : List Stmt, sitesL (fun g => δ₁ g + δ₂ g) ss = sitesL δ₁ ss + sitesL δ₂ ss
  | [] => rfl
  | s :: ss => by
      cases s with
      | atom a => simp only [sitesL_atom, sitesL_add δ₁ δ₂ ss]
      | ite c z n => simp only [sitesL_ite, sitesL_add δ₁ δ₂ z, sitesL_add δ₁ δ₂ n, sitesL_add δ₁ δ₂ ss]; omega
      | match_ x arms => simp only [sitesL_match, sitesA_add δ₁ δ₂ arms, sitesL_add δ₁ δ₂ ss]; omega
      | call g a r => simp only [sitesL_call, sitesL_add δ₁ δ₂ ss]; omega
      | callIf c g a => simp only [sitesL_callIf, sitesL_add δ₁ δ₂ ss]; omega
      | dispatch x gs a r => simp only [sitesL_dispatch, List.sum_map_add, sitesL_add δ₁ δ₂ ss]; omega
      | ret vs => simp only [sitesL_ret, sitesL_add δ₁ δ₂ ss]

theorem sitesA_add (δ₁ δ₂ : String → ℕ) :
    ∀ as : List (List Stmt), sitesA (fun g => δ₁ g + δ₂ g) as = sitesA δ₁ as + sitesA δ₂ as
  | [] => rfl
  | a :: as => by simp only [sitesA_cons, sitesL_add δ₁ δ₂ a, sitesA_add δ₁ δ₂ as]; omega
end

mutual
/-- `sitesL` of a multiple of weights. -/
theorem sitesL_mul (C : ℕ) (δ : String → ℕ) :
    ∀ ss : List Stmt, sitesL (fun g => C * δ g) ss = C * sitesL δ ss
  | [] => rfl
  | s :: ss => by
      cases s with
      | atom a => simp only [sitesL_atom, sitesL_mul C δ ss]
      | ite c z n => simp only [sitesL_ite, sitesL_mul C δ z, sitesL_mul C δ n, sitesL_mul C δ ss, Nat.mul_add]
      | match_ x arms => simp only [sitesL_match, sitesA_mul C δ arms, sitesL_mul C δ ss, Nat.mul_add]
      | call g a r => simp only [sitesL_call, sitesL_mul C δ ss, Nat.mul_add]
      | callIf c g a => simp only [sitesL_callIf, sitesL_mul C δ ss, Nat.mul_add]
      | dispatch x gs a r => simp only [sitesL_dispatch, List.sum_map_mul_left, sitesL_mul C δ ss, Nat.mul_add]
      | ret vs => simp only [sitesL_ret, sitesL_mul C δ ss]

theorem sitesA_mul (C : ℕ) (δ : String → ℕ) :
    ∀ as : List (List Stmt), sitesA (fun g => C * δ g) as = C * sitesA δ as
  | [] => by simp only [sitesA_nil, Nat.mul_zero]
  | a :: as => by simp only [sitesA_cons, sitesL_mul C δ a, sitesA_mul C δ as, Nat.mul_add]
end

end Shift

end
end LeanVM.Guest.Memory
