/-
  LeanVM.Guest.CoreMode.SelGoW

  The selectors' check of a body (`CoreMode.selGo`) with the top-level atoms it remembers cut to those using a
  selector the generator names.
-/

module

public import LeanVM.Guest.CoreMode.Route

/-!
# The selectors' check, witnessed

`selGo` remembers every top-level atom before a `match` or `dispatch` and searches them all for one using its
selector, quadratic in a long body's top level. `selGoW S` remembers only the atoms using a value of the bitset `S`
(`keepB`), the selectors the generator names; its remembered atoms are among `selGo`'s, so its success is
`selGo`'s (`selGo_of_W`: the check reads its remembered atoms only through `List.any`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- An atom using a value of the bitset `S`. -/
def keepB (S : ℕ) (a : Atom) : Bool := (Memory.atomUses a).any fun v ↦ Nat.testBit S v.idx

/-- `seen` with `a` when it uses a value of `S`. -/
def keepIn (S : ℕ) (a : Atom) (seen : List Atom) : List Atom := bif keepB S a then a :: seen else seen

/-- `selBr`, remembering the atoms `keepB S` keeps. -/
noncomputable def selBrW (j : ℕ) (B : List Stmt) (S : ℕ) : List Atom → List Stmt → Bool
  | _, [] => true
  | seen, .atom a :: ss => selBrW j B S (keepIn S a seen) ss
  | seen, .match_ x arms :: ss => cellB j x && seen.any (fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      noMatch (Bridge.stmtsArms arms) && onceAfter B ss && selBrW j B S seen ss
  | seen, .ite _ z n :: ss => noMatch (Bridge.stmtsOf z) && noMatch (Bridge.stmtsOf n) && selBrW j B S seen ss
  | seen, .ret _ :: ss => selBrW j B S seen ss
  | seen, .call .. :: ss => selBrW j B S seen ss
  | seen, .callIf .. :: ss => selBrW j B S seen ss
  | seen, .dispatch .. :: ss => selBrW j B S seen ss

/-- `selGo`, remembering the atoms `keepB S` keeps. -/
noncomputable def selGoW (j : ℕ) (ps : List V) (B : List Stmt) (S : ℕ) : List Atom → List Stmt → Bool
  | _, [] => true
  | seen, .atom a :: ss => selGoW j ps B S (keepIn S a seen) ss
  | seen, .match_ x arms :: ss => cellB j x && seen.any (fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      noMatch (Bridge.stmtsArms arms) && selGoW j ps B S seen ss
  | seen, .ite _ z n :: ss => selBrW j B S seen z && selBrW j B S seen n && selGoW j ps B S seen ss
  | _, .ret _ :: ss => noMatch (Bridge.stmtsOf ss) && noDsp (Bridge.stmtsOf ss)
  | seen, .call .. :: ss => selGoW j ps B S seen ss
  | seen, .callIf .. :: ss => selGoW j ps B S seen ss
  | seen, .dispatch x .. :: ss => cellB j x && (ps.contains x || seen.any fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      selGoW j ps B S seen ss

end

public section

private theorem keepIn_sub {S : ℕ} {a : Atom} {s s' : List Atom} (h : ∀ b ∈ s', b ∈ s) :
    ∀ b ∈ keepIn S a s', b ∈ a :: s := by
  intro b hb
  unfold keepIn at hb
  generalize keepB S a = c at hb
  cases c
  · exact List.mem_cons_of_mem _ (h b (hb : b ∈ s'))
  · rcases List.mem_cons.mp (hb : b ∈ a :: s') with rfl | hb
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h b hb)

private theorem any_sub' {p : Atom → Bool} {s s' : List Atom} (h : ∀ b ∈ s', b ∈ s) (ha : s'.any p = true) :
    s.any p = true := by
  obtain ⟨b, hb, hp⟩ := List.any_eq_true.mp ha
  exact List.any_eq_true.mpr ⟨b, h b hb, hp⟩

theorem selBr_of_W {j : ℕ} {B : List Stmt} {S : ℕ} :
    ∀ (ss : List Stmt) (s s' : List Atom), (∀ b ∈ s', b ∈ s) → selBrW j B S s' ss = true → selBr j B s ss = true
  | [], _, _, _, _ => by simp [selBr]
  | st :: ss, s, s', hs, h => by
    cases st with
    | atom a => simp only [selBrW, selBr] at h ⊢; exact selBr_of_W ss _ _ (keepIn_sub hs) h
    | match_ x arms =>
      simp only [selBrW, selBr, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨h.1.1.1.1, any_sub' hs h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, selBr_of_W ss _ _ hs h.2⟩
    | ite c z n =>
      simp only [selBrW, selBr, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, selBr_of_W ss _ _ hs h.2⟩
    | ret _ => simp only [selBrW, selBr] at h ⊢; exact selBr_of_W ss _ _ hs h
    | call f a r => simp only [selBrW, selBr] at h ⊢; exact selBr_of_W ss _ _ hs h
    | callIf c f a => simp only [selBrW, selBr] at h ⊢; exact selBr_of_W ss _ _ hs h
    | dispatch x fs a r => simp only [selBrW, selBr] at h ⊢; exact selBr_of_W ss _ _ hs h

/-- **The selectors' check, from its witnessed check.** -/
theorem selGo_of_W {j : ℕ} {ps : List V} {B : List Stmt} {S : ℕ} :
    ∀ (ss : List Stmt) (s s' : List Atom), (∀ b ∈ s', b ∈ s) → selGoW j ps B S s' ss = true →
      selGo j ps B s ss = true
  | [], _, _, _, _ => by simp [selGo]
  | st :: ss, s, s', hs, h => by
    cases st with
    | atom a => simp only [selGoW, selGo] at h ⊢; exact selGo_of_W ss _ _ (keepIn_sub hs) h
    | match_ x arms =>
      simp only [selGoW, selGo, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨h.1.1.1, any_sub' hs h.1.1.2⟩, h.1.2⟩, selGo_of_W ss _ _ hs h.2⟩
    | ite c z n =>
      simp only [selGoW, selGo, Bool.and_eq_true] at h ⊢
      exact ⟨⟨selBr_of_W z _ _ hs h.1.1, selBr_of_W n _ _ hs h.1.2⟩, selGo_of_W ss _ _ hs h.2⟩
    | ret _ => simp only [selGoW, selGo] at h ⊢; exact h
    | call f a r => simp only [selGoW, selGo] at h ⊢; exact selGo_of_W ss _ _ hs h
    | callIf c f a => simp only [selGoW, selGo] at h ⊢; exact selGo_of_W ss _ _ hs h
    | dispatch x fs args rets =>
      simp only [selGoW, selGo, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨⟨h.1.1, h.1.2.imp id (any_sub' hs)⟩, selGo_of_W ss _ _ hs h.2⟩

/-- `selGo` over a body from no atom, by its witnessed check. -/
theorem selGo_nil_of_W {j : ℕ} {ps : List V} {B : List Stmt} (S : ℕ) (h : selGoW j ps B S [] B = true) :
    selGo j ps B [] B = true :=
  selGo_of_W B [] [] (fun _ h ↦ h) h

end

end LeanVM.Guest.CoreMode
