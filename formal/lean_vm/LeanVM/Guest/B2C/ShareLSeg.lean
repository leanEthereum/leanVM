/-
  LeanVM.Guest.B2C.ShareLSeg

  The local sharing check of a large function from its pieces, each in its own kernel
  evaluation.
-/

module

public import LeanVM.Guest.B2C.ShareL

/-!
# The check from its pieces

`segL_join` joins the walks of consecutive statements of a block, `segArms_join` of consecutive
arms of a `match`, `seg_match` a `match`'s own step and its arms into the walk of the statement,
and `shareCheckL_of` the once-per-function parts, the parameters and the body's walk into the
check.
-/

namespace LeanVM.Guest.B2C.ShareL

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Local LeanVM.Guest.Check LeanVM.Guest.Exec
open LeanVM.Guest.Packed (fld fld_lt)

@[expose] public section

theorem take_drop_join {α : Type} (l : List α) {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    (l.drop a).take (c - a) = (l.drop a).take (b - a) ++ (l.drop b).take (c - b) := by
  rw [show c - a = (b - a) + (c - b) by omega, List.take_add, List.drop_drop, show a + (b - a) = b by omega]

theorem res_eq {r : FoldR (ℕ × ℕ)} {p : ℕ} {st : ℕ × ℕ} {es : List ℕ}
    (h : (Nat.beq r.1 p && Nat.beq r.2.1.1 st.1 && Nat.beq r.2.1.2 st.2 && r.2.2 == es) = true) :
    r = (p, st, es) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨r1, ⟨r21, r22⟩, r3⟩ := r
  simp only at h1 h2 h3 h4
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, h4]

theorem segL_spec {K : FnK} {ss : List Stmt} {cx : Ctx} {a b p : ℕ} {st : ℕ × ℕ} {ea p' : ℕ}
    {st' : ℕ × ℕ} {eb : ℕ} (h : segL K ss cx a b p st ea p' st' eb = true) :
    Local.foldL (step K) ((ss.drop a).take (b - a)) cx p st (K.T.ends.drop ea) = some (p', st', K.T.ends.drop eb) := by
  unfold segL at h
  split at h
  · rename_i r hr; rw [hr, res_eq h]
  · cases h

theorem segL_of {K : FnK} {ss : List Stmt} {cx : Ctx} {a b p : ℕ} {st : ℕ × ℕ} {ea p' : ℕ}
    {st' : ℕ × ℕ} {eb : ℕ}
    (h : Local.foldL (step K) ((ss.drop a).take (b - a)) cx p st (K.T.ends.drop ea) = some (p', st', K.T.ends.drop eb)) :
    segL K ss cx a b p st ea p' st' eb = true := by
  unfold segL; rw [h]; simp

/-- **Consecutive statements' walks join.** -/
theorem segL_join {K : FnK} {ss : List Stmt} {cx : Ctx} {a b c p p1 p2 : ℕ} {st st1 st2 : ℕ × ℕ}
    {ea e1 e2 : ℕ} (h1 : segL K ss cx a b p st ea p1 st1 e1 = true) (h2 : segL K ss cx b c p1 st1 e1 p2 st2 e2 = true)
    (hab : a ≤ b) (hbc : b ≤ c) : segL K ss cx a c p st ea p2 st2 e2 = true := by
  apply segL_of
  rw [take_drop_join ss hab hbc, Local.foldL_append, segL_spec h1, Local.bindO_some]
  exact segL_spec h2

theorem segArms_spec {K : FnK} {ss : List Stmt} {m t a b pa : ℕ} {st : ℕ × ℕ} {ea pb : ℕ} {st' : ℕ × ℕ}
    {eb : ℕ} (h : segArms K ss m t a b pa st ea pb st' eb = true) :
    ∃ x arms, (ss.drop m).head? = some (.match_ x arms) ∧
      Local.foldA (step K) ((arms.drop a).take (b - a)) t pa st (K.T.ends.drop ea) = some (pb, st', K.T.ends.drop eb) := by
  unfold segArms at h
  split at h
  · rename_i x arms hx
    split at h
    · rename_i r hr; exact ⟨x, arms, hx, by rw [hr, res_eq h]⟩
    · cases h
  · cases h

/-- **Consecutive arms' walks join.** -/
theorem segArms_join {K : FnK} {ss : List Stmt} {m t a b c p p1 p2 : ℕ} {st st1 st2 : ℕ × ℕ}
    {ea e1 e2 : ℕ} (h1 : segArms K ss m t a b p st ea p1 st1 e1 = true)
    (h2 : segArms K ss m t b c p1 st1 e1 p2 st2 e2 = true) (hab : a ≤ b) (hbc : b ≤ c) :
    segArms K ss m t a c p st ea p2 st2 e2 = true := by
  obtain ⟨x, arms, hx, f1⟩ := segArms_spec h1
  obtain ⟨x', arms', hx', f2⟩ := segArms_spec h2
  rw [hx] at hx'
  obtain ⟨rfl, rfl⟩ : x = x' ∧ arms = arms' := by
    simp only [Option.some.injEq, Stmt.match_.injEq] at hx'; exact hx'
  unfold segArms
  rw [hx]
  simp only
  rw [take_drop_join arms hab hbc, Local.foldA_append, f1, Local.bindO_some, f2]
  simp

/-- **A `match`'s walk**: its own step and its arms'. -/
theorem seg_match {K : FnK} {ss : List Stmt} {cx : Ctx} {m n p p' : ℕ} {st st1 st' : ℕ × ℕ} {ea eb : ℕ}
    (hh : segHead K ss cx m p st st1 = true) (ha : segArms K ss m p 0 n (p + 1) st1 ea p' st' eb = true)
    (hn : segArity ss m n = true) : segL K ss cx m (m + 1) p st ea p' st' eb = true := by
  obtain ⟨x, arms, hx, f⟩ := segArms_spec ha
  unfold segHead at hh
  unfold segArity at hn
  rw [hx] at hh hn
  dsimp only at hh hn
  have hn' := Nat.eq_of_beq_eq_true hn
  split at hh
  · rename_i r hr
    simp only [Bool.and_eq_true] at hh
    have hr1 : r = st1 := Prod.ext (Nat.eq_of_beq_eq_true hh.1) (Nat.eq_of_beq_eq_true hh.2)
    subst hr1
    apply segL_of
    have htake : (ss.drop m).take (m + 1 - m) = [.match_ x arms] := by
      rw [show m + 1 - m = 1 by omega]
      cases hd : ss.drop m with
      | nil => rw [hd] at hx; cases hx
      | cons s rest => rw [hd] at hx; simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; rfl
    rw [htake, Local.foldL_cons, Local.foldL_nil]
    unfold Local.consF
    rw [Local.foldS_match]
    unfold Local.matchF
    rw [hr, Local.bindO_some]
    rw [List.drop_zero, Nat.sub_zero, ← hn', List.take_length] at f
    rw [f, Local.bindO_some]
  · exact absurd hh (by simp)

theorem walkL_of {K : FnK} {cf : Core.Fn} {n : ℕ} (hp : paramsOk K cf.params = some n)
    (hw : segL K cf.body ⟨K.T.e, 0, 0⟩ 0 cf.body.length 1 (n, 0) 0 K.T.e (K.T.nv, K.T.nat) K.T.ends.length = true) :
    walkL K cf = true := by
  unfold walkL; rw [hp]; exact hw

/-- The walk ends at statement `b`, position `e`, `n` values and `a` anchors on, the arms' ends
`ea` on: the body's, the certificate's. -/
noncomputable def endOk (K : FnK) (cf : Core.Fn) (b e n a ea : ℕ) : Bool :=
  Nat.beq cf.body.length b && Nat.beq K.T.e e && Nat.beq K.T.nv n && Nat.beq K.T.nat a && Nat.beq K.T.ends.length ea

/-- **The walk from its pieces**, joined up to literal ends that `endOk` matches with the body's. -/
theorem walkL_of' {K : FnK} {cf : Core.Fn} {n b e n' a ea : ℕ} (hp : paramsOk K cf.params = some n)
    (hw : segL K cf.body ⟨K.T.e, 0, 0⟩ 0 b 1 (n, 0) 0 e (n', a) ea = true) (he : endOk K cf b e n' a ea = true) :
    walkL K cf = true := by
  simp only [endOk, Bool.and_eq_true] at he
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := he
  rw [← Nat.eq_of_beq_eq_true h1, ← Nat.eq_of_beq_eq_true h2, ← Nat.eq_of_beq_eq_true h3,
    ← Nat.eq_of_beq_eq_true h4, ← Nat.eq_of_beq_eq_true h5] at hw
  exact walkL_of hp hw

/-- **The check from its parts.** -/
theorem shareCheckL_of {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs}
    (hs : staticL cf C P fs main mc T = true) (hw : walkL (fnK cf C P fs main mc T) cf = true) :
    shareCheckL cf C P fs main mc T = true := by
  unfold shareCheckL; rw [hs, hw]; rfl

end
end LeanVM.Guest.B2C.ShareL
