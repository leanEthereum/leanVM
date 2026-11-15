/-
  LeanVM.Guest.Memory.Scope

  What the check of every statement in its context (`allB`) gives of a path: each event the path
  emits comes from a statement passing the check in a context the path passes, and so does its
  return.
-/

module

public import LeanVM.Guest.Memory.ScopeDefs
public import LeanVM.Guest.Bridge.Pair

/-!
# Statements in their context, on a path

`spineE_sub`: a path through a block that does not get stuck passes its spine. `allB_evs`: each
event of a block's path is emitted (`Emits`) by a statement of the block passing `p` in a context
whose events are the given context's or the path's. `allB_ret`: likewise for the `ret` a returning
path ends at.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core
open LeanVM.Guest.Bridge (noRet noRetArms walk1_noRet pick_ne_ret seq_eq_ret pre_eq_ret)

@[expose] public section

/-- The events a statement emits itself. -/
def Emits : Stmt → Ev → Prop
  | .atom a, e => e = .atom a
  | .ite c _ _, e => e = .inK c
  | .call f args rets, e => e = .call f args rets
  | .callIf c f args, e => e = .inK c ∨ e = .skip f args ∨ e = .call f args []
  | .dispatch _ fs args rets, e => ∃ f ∈ fs, e = .call f args rets
  | _, _ => False

end

public section

variable {σ : Val}

theorem evs_pre {o : Out} {pre : List Ev} {e : Ev} (h : e ∈ (o.pre pre).evs) :
    e ∈ pre ∨ (e ∈ o.evs ∧ ∀ y ∈ pre ++ o.evs, y ∈ (o.pre pre).evs) := by
  cases o <;> simp_all [Out.pre, Out.evs]

theorem evs_seq {o k : Out} {e : Ev} (h : e ∈ (o.seq k).evs) :
    (e ∈ o.evs ∧ ∀ y ∈ o.evs, y ∈ (o.seq k).evs) ∨
      (∃ es1, o = .fall es1 ∧ e ∈ k.evs ∧ ∀ y ∈ k.evs, y ∈ (o.seq k).evs) := by
  rcases o with es1 | ⟨es1, vs1⟩ | _
  · rcases k with es2 | ⟨es2, vs2⟩ | _ <;> simp_all [Out.seq, Out.pre, Out.evs]
  · left; simp_all [Out.seq, Out.evs]
  · simp [Out.seq, Out.evs] at h

theorem pick_evs {x : V} {args rets : List V} {e : Ev} :
    ∀ (fs : List String) (j : ℕ), e ∈ (pick σ x args rets j fs).evs → ∃ f ∈ fs, e = .call f args rets
  | [], _, h => by simp [pick, Out.evs] at h
  | f :: fs, j, h => by
    unfold pick at h
    split_ifs at h
    · simp only [Out.evs, List.mem_singleton] at h
      exact ⟨f, List.mem_cons_self, h⟩
    · obtain ⟨g, hg, rfl⟩ := pick_evs fs (j + 1) h
      exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩

/-- `walk1 σ s` falls through or returns, not getting stuck, when `walk σ (s :: ss)` does not. -/
theorem seq_ne_stuck {o k : Out} (h : o.seq k ≠ .stuck) (hr : ∀ es vs, o ≠ .ret es vs) :
    ∃ es1, o = .fall es1 ∧ k ≠ .stuck ∧ (o.seq k).evs = es1 ++ k.evs := by
  rcases o with es1 | ⟨es1, vs1⟩ | _
  · rcases k with es2 | ⟨es2, vs2⟩ | _ <;> simp_all [Out.seq, Out.pre, Out.evs]
  · exact absurd rfl (hr es1 vs1)
  · simp [Out.seq] at h

theorem pre_ne_stuck {o : Out} {pre : List Ev} (h : o.pre pre ≠ .stuck) :
    o ≠ .stuck ∧ (o.pre pre).evs = pre ++ o.evs := by
  cases o <;> simp_all [Out.pre, Out.evs]

/-- **A path through a block that does not get stuck passes its spine.** -/
theorem spineE_sub : ∀ (ss : List Stmt), walk σ ss ≠ .stuck → ∀ x ∈ spineE ss, x ∈ (walk σ ss).evs
  | [], _, x, hx => by simp [spineE] at hx
  | .atom b :: ss, h, x, hx => by
    rw [Bridge.walk_atom_cons] at h ⊢
    obtain ⟨h', he⟩ := pre_ne_stuck h
    rw [he]
    simp only [spineE, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_append_right _ (spineE_sub ss h' x hx)
  | .call f args rets :: ss, h, x, hx => by
    rw [Bridge.walk_call_cons] at h ⊢
    obtain ⟨h', he⟩ := pre_ne_stuck h
    rw [he]
    simp only [spineE, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_append_right _ (spineE_sub ss h' x hx)
  | .callIf c f args :: ss, h, x, hx => by
    rw [Bridge.walk_callIf_cons] at h ⊢
    obtain ⟨h', he⟩ := pre_ne_stuck h
    rw [he]
    exact List.mem_append_right _ (spineE_sub ss h' x hx)
  | .dispatch y fs args rets :: ss, h, x, hx => by
    rw [Bridge.walk_dispatch_cons] at h ⊢
    obtain ⟨es1, -, h', he⟩ := seq_ne_stuck h (fun es vs ↦ pick_ne_ret fs 0)
    rw [he]
    exact List.mem_append_right _ (spineE_sub ss h' x hx)
  | .ite c z n :: ss, h, x, hx => by
    simp only [spineE, Bool.cond_eq_ite, Bool.and_eq_true] at hx
    split at hx
    · rename_i hn
      rw [walk] at h ⊢
      obtain ⟨es1, -, h', he⟩ := seq_ne_stuck h (walk1_noRet (.ite c z n)
        (show ((noRet z && noRet n) && true) = true by simp [hn.1, hn.2]))
      rw [he]
      exact List.mem_append_right _ (spineE_sub ss h' x hx)
    · simp at hx
  | .match_ y arms :: ss, h, x, hx => by
    simp only [spineE, Bool.cond_eq_ite] at hx
    split at hx
    · rename_i hn
      rw [walk] at h ⊢
      obtain ⟨es1, -, h', he⟩ := seq_ne_stuck h (walk1_noRet (.match_ y arms)
        (show (noRetArms arms && true) = true by simp [hn]))
      rw [he]
      exact List.mem_append_right _ (spineE_sub ss h' x hx)
    · simp at hx
  | .ret _ :: _, _, x, hx => by simp [spineE] at hx

theorem ne_stuck_of_mem {o : Out} {e : Ev} (h : e ∈ o.evs) : o ≠ .stuck := by
  rintro rfl; simp [Out.evs] at h

section

variable {p : List Ev → Stmt → Bool}

mutual
/-- **Each event of a statement's path is emitted by a statement passing the check**, in a
context of the given one's events and the path's. -/
theorem allS_evs : ∀ (s : Stmt) (ctx : List Ev), allS p s ctx = true → ∀ e ∈ (walk1 σ s).evs,
    ∃ ctx' s', p ctx' s' = true ∧ Emits s' e ∧ ∀ x ∈ ctx', x ∈ ctx ∨ x ∈ (walk1 σ s).evs
  | .atom a, ctx, h, e, he => by
    simp only [walk1, Out.evs, List.mem_singleton] at he
    exact ⟨ctx, .atom a, h, he, fun x hx ↦ .inl hx⟩
  | .ite c z n, ctx, h, e, he => by
    replace h : (p ctx (.ite c z n) && allB p z (ctx ++ spineE z) && allB p n (ctx ++ spineE n)) = true := h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h0, hz⟩, hn⟩ := h
    rw [walk1] at he ⊢
    rcases evs_pre he with he | ⟨he, hsub⟩
    · simp only [List.mem_singleton] at he
      exact ⟨ctx, .ite c z n, h0, he, fun x hx ↦ .inl hx⟩
    · have key : ∀ (b : List Stmt), e ∈ (walk σ b).evs →
          (∀ y ∈ (walk σ b).evs, y ∈ ((walk σ b).pre [.inK c]).evs) →
          (∃ ctx' s', p ctx' s' = true ∧ Emits s' e ∧ ∀ x ∈ ctx', x ∈ ctx ++ spineE b ∨ x ∈ (walk σ b).evs) →
          ∃ ctx' s', p ctx' s' = true ∧ Emits s' e ∧ ∀ x ∈ ctx', x ∈ ctx ∨ x ∈ ((walk σ b).pre [.inK c]).evs := by
        rintro b heb hs ⟨ctx', s', hp, hem, hc⟩
        refine ⟨ctx', s', hp, hem, fun x hx ↦ ?_⟩
        rcases hc x hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact .inl hx
          · exact .inr (hs x (spineE_sub b (ne_stuck_of_mem heb) x hx))
        · exact .inr (hs x hx)
      split_ifs at he hsub ⊢
      · exact key z he (fun y hy ↦ hsub y (List.mem_append_right _ hy)) (allB_evs z _ hz e he)
      · exact key n he (fun y hy ↦ hsub y (List.mem_append_right _ hy)) (allB_evs n _ hn e he)
  | .match_ x arms, ctx, h, e, he => by
    replace h : (p ctx (.match_ x arms) && allA p arms ctx) = true := h
    simp only [Bool.and_eq_true] at h
    rw [walk1] at he ⊢
    exact allA_evs x arms 0 ctx h.2 e he
  | .call f args rets, ctx, h, e, he => by
    simp only [walk1, Out.evs, List.mem_singleton] at he
    exact ⟨ctx, .call f args rets, h, he, fun x hx ↦ .inl hx⟩
  | .callIf c f args, ctx, h, e, he => by
    refine ⟨ctx, .callIf c f args, h, ?_, fun x hx ↦ .inl hx⟩
    simp only [walk1, Out.evs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | he
    · exact .inl rfl
    · split_ifs at he
      · exact .inr (.inl he)
      · exact .inr (.inr he)
  | .dispatch y fs args rets, ctx, h, e, he => by
    rw [walk1] at he
    exact ⟨ctx, .dispatch y fs args rets, h, pick_evs fs 0 he, fun x hx ↦ .inl hx⟩
  | .ret _, _, _, e, he => by simp [walk1, Out.evs] at he

/-- **Each event of a block's path is emitted by a statement passing the check**, in a context of
the given one's events and the path's. -/
theorem allB_evs : ∀ (ss : List Stmt) (ctx : List Ev), allB p ss ctx = true → ∀ e ∈ (walk σ ss).evs,
    ∃ ctx' s', p ctx' s' = true ∧ Emits s' e ∧ ∀ x ∈ ctx', x ∈ ctx ∨ x ∈ (walk σ ss).evs
  | [], _, _, e, he => by simp [walk, Out.evs] at he
  | s :: ss, ctx, h, e, he => by
    replace h : (allS p s ctx && allB p ss ctx) = true := h
    simp only [Bool.and_eq_true] at h
    rw [walk] at he ⊢
    rcases evs_seq he with ⟨he, hsub⟩ | ⟨es1, -, he, hsub⟩
    · obtain ⟨ctx', s', hp, hem, hc⟩ := allS_evs s ctx h.1 e he
      exact ⟨ctx', s', hp, hem, fun x hx ↦ (hc x hx).imp id (hsub x)⟩
    · obtain ⟨ctx', s', hp, hem, hc⟩ := allB_evs ss ctx h.2 e he
      exact ⟨ctx', s', hp, hem, fun x hx ↦ (hc x hx).imp id (hsub x)⟩

theorem allA_evs (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) (ctx : List Ev), allA p arms ctx = true →
    ∀ e ∈ (walkArms σ x j arms).evs,
      ∃ ctx' s', p ctx' s' = true ∧ Emits s' e ∧ ∀ y ∈ ctx', y ∈ ctx ∨ y ∈ (walkArms σ x j arms).evs
  | [], _, _, _, e, he => by simp [walkArms, Out.evs] at he
  | a :: as, j, ctx, h, e, he => by
    replace h : (allB p a (ctx ++ spineE a) && allA p as ctx) = true := h
    simp only [Bool.and_eq_true] at h
    unfold walkArms at he ⊢
    split_ifs at he ⊢
    · obtain ⟨ctx', s', hp, hem, hc⟩ := allB_evs a _ h.1 e he
      refine ⟨ctx', s', hp, hem, fun y hy ↦ ?_⟩
      rcases hc y hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · exact .inl hy
        · exact .inr (spineE_sub a (ne_stuck_of_mem he) y hy)
      · exact .inr hy
    · exact allA_evs x as (j + 1) ctx h.2 e he
end

mutual
/-- **The `ret` a statement's returning path ends at passes the check**, in a context of the given
one's events and the path's. -/
theorem allS_ret : ∀ (s : Stmt) (ctx : List Ev) {es : List Ev} {vs : List V}, allS p s ctx = true →
    walk1 σ s = .ret es vs → ∃ ctx', p ctx' (.ret vs) = true ∧ ∀ x ∈ ctx', x ∈ ctx ∨ x ∈ es
  | .atom _, _, _, _, _, hw => by simp [walk1] at hw
  | .ite c z n, ctx, es, vs, h, hw => by
    replace h : (p ctx (.ite c z n) && allB p z (ctx ++ spineE z) && allB p n (ctx ++ spineE n)) = true := h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨-, hz⟩, hn⟩ := h
    rw [walk1] at hw
    obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
    have key : ∀ (b : List Stmt), walk σ b = .ret es' vs →
        (∃ ctx', p ctx' (.ret vs) = true ∧ ∀ x ∈ ctx', x ∈ ctx ++ spineE b ∨ x ∈ es') →
        ∃ ctx', p ctx' (.ret vs) = true ∧ ∀ x ∈ ctx', x ∈ ctx ∨ x ∈ [Ev.inK c] ++ es' := by
      rintro b hwb ⟨ctx', hp, hc⟩
      refine ⟨ctx', hp, fun x hx ↦ ?_⟩
      rcases hc x hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact .inl hx
        · have := spineE_sub b (by rw [hwb]; simp) x hx
          rw [hwb] at this
          exact .inr (List.mem_append_right _ this)
      · exact .inr (List.mem_append_right _ hx)
    split_ifs at hw'
    · exact key z hw' (allB_ret z _ hz hw')
    · exact key n hw' (allB_ret n _ hn hw')
  | .match_ x arms, ctx, es, vs, h, hw => by
    replace h : (p ctx (.match_ x arms) && allA p arms ctx) = true := h
    simp only [Bool.and_eq_true] at h
    rw [walk1] at hw
    exact allA_ret x arms 0 ctx h.2 hw
  | .call .., _, _, _, _, hw => by simp [walk1] at hw
  | .callIf .., _, _, _, _, hw => by simp [walk1] at hw
  | .dispatch y fs args rets, _, _, _, _, hw => by rw [walk1] at hw; exact absurd hw (pick_ne_ret fs 0)
  | .ret vs', ctx, es, vs, h, hw => by
    simp only [walk1, Out.ret.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨ctx, h, fun x hx ↦ .inl hx⟩

/-- **The `ret` a block's returning path ends at passes the check**, in a context of the given
one's events and the path's. -/
theorem allB_ret : ∀ (ss : List Stmt) (ctx : List Ev) {es : List Ev} {vs : List V}, allB p ss ctx = true →
    walk σ ss = .ret es vs → ∃ ctx', p ctx' (.ret vs) = true ∧ ∀ x ∈ ctx', x ∈ ctx ∨ x ∈ es
  | [], _, _, _, _, hw => by simp [walk] at hw
  | s :: ss, ctx, es, vs, h, hw => by
    replace h : (allS p s ctx && allB p ss ctx) = true := h
    simp only [Bool.and_eq_true] at h
    rw [walk] at hw
    rcases seq_eq_ret hw with ⟨es1, es2, -, h2, rfl⟩ | h1
    · obtain ⟨ctx', hp, hc⟩ := allB_ret ss ctx h.2 h2
      exact ⟨ctx', hp, fun x hx ↦ (hc x hx).imp id (List.mem_append_right _)⟩
    · exact allS_ret s ctx h.1 h1

theorem allA_ret (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) (ctx : List Ev) {es : List Ev} {vs : List V},
    allA p arms ctx = true → walkArms σ x j arms = .ret es vs →
      ∃ ctx', p ctx' (.ret vs) = true ∧ ∀ y ∈ ctx', y ∈ ctx ∨ y ∈ es
  | [], _, _, _, _, _, hw => by simp [walkArms] at hw
  | a :: as, j, ctx, es, vs, h, hw => by
    replace h : (allB p a (ctx ++ spineE a) && allA p as ctx) = true := h
    simp only [Bool.and_eq_true] at h
    unfold walkArms at hw
    split_ifs at hw
    · obtain ⟨ctx', hp, hc⟩ := allB_ret a _ h.1 hw
      refine ⟨ctx', hp, fun y hy ↦ ?_⟩
      rcases hc y hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · exact .inl hy
        · have := spineE_sub a (by rw [hw]; simp) y hy
          rw [hw] at this
          exact .inr this
      · exact .inr hy
    · exact allA_ret x as (j + 1) ctx h.2 hw
end

/-- **A body's check on a returning path**: each event of the path is emitted by a statement
passing `p` in a context the path passes. -/
theorem allB_body {body : List Stmt} (hc : allB p body (spineE body) = true) {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) : ∀ e ∈ es, ∃ ctx s, p ctx s = true ∧ Emits s e ∧ ∀ x ∈ ctx, x ∈ es := by
  intro e he
  have hsp := spineE_sub body (by rw [hw]; simp)
  rw [hw] at hsp
  obtain ⟨ctx, s, hp, hem, hctx⟩ := allB_evs body _ hc e (by rw [hw]; exact he)
  refine ⟨ctx, s, hp, hem, fun x hx ↦ ?_⟩
  rcases hctx x hx with hx | hx
  · exact hsp x hx
  · rwa [hw] at hx

/-- **A body's check on a returning path, at its `ret`.** -/
theorem allB_body_ret {body : List Stmt} (hc : allB p body (spineE body) = true) {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) : ∃ ctx, p ctx (.ret vs) = true ∧ ∀ x ∈ ctx, x ∈ es := by
  have hsp := spineE_sub body (by rw [hw]; simp)
  rw [hw] at hsp
  obtain ⟨ctx, hp, hctx⟩ := allB_ret body _ hc hw
  exact ⟨ctx, hp, fun x hx ↦ (hctx x hx).elim (hsp x) id⟩

end

end

end LeanVM.Guest.Memory
