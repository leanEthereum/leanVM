/-
  LeanVM.Guest.Backend.Complete.FrameBody

  The function level of the frame side: the walk's statement from the words of the placed body.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameWords
public import LeanVM.Guest.Backend.Complete.FrameInst
public import LeanVM.Guest.Backend.Complete.FrameStmt
public import LeanVM.Guest.Backend.Complete.FrameLocs
public import LeanVM.Guest.Backend.Complete.FrameOut

/-!
# A function's walk

`placeBody` binds the parameters to the argument cells, places the body, flushes the trace's end
and checks nothing is left. On the path of the instance, the parameters' binding starts the walk's
invariant (`winv_init`: the constraint `initC` gives each argument cell its parameter's word and a
registered loop helper's own pointer cell `g^fp`); the body's placement is the block lemma
(`BodyW`, the frame side's); what follows is off the path (the path returned). The final state is
the placement, so the block's words (`BlkW`) are the path's (`PathWords`) and the words of the
values it read (`RW`) give `FrameClauses`.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Binding the parameters -/

theorem forM_bindTo_st {ctx : Ctx} : ∀ (ps : List (V × ℕ)) (st : St),
    wpP (ps.forM fun b => bindTo b.1 (.cell (2 + b.2))) ctx st (fun _ st' =>
      st' = { st with locs := st'.locs } ∧ LocsLe st.locs st'.locs ∧
      (∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨
        ∃ b ∈ ps, b.1 = v ∧ l = .cell (2 + b.2)) ∧
      ∀ b ∈ ps, st'.locs[b.1]? = some (.cell (2 + b.2)))
  | [], st => wp_pure.mpr ⟨rfl, LocsLe.refl _, fun _ _ h => Or.inl h, fun _ h => nomatch h⟩
  | b :: ps, st => by
      show wpP (bindTo b.1 (.cell (2 + b.2)) >>= fun _ => ps.forM _) ctx st _
      refine wp_bind.mpr (wp_bindTo fun hnc => ?_)
      have hle : LocsLe st.locs (st.locs.insert b.1 (.cell (2 + b.2))) := fun v x hv => by
        rw [KMap.getElem?_insert]
        split
        · next he =>
          subst he
          rw [KMap.getElem?_eq_none_of_contains_eq_false hnc] at hv
          cases hv
        · exact hv
      refine wp_mono (forM_bindTo_st ps _) fun _ st' ⟨he, hl, hk, hall⟩ =>
        ⟨?_, hle.trans hl, fun v l hv => ?_, ?_⟩
      · rw [he]
      · rcases hk v l hv with h | ⟨b', hb', h1, h2⟩
        · simp only [KMap.getElem?_insert] at h
          split at h
          · next hvb => cases h; exact Or.inr ⟨b, List.mem_cons_self, hvb.symm, rfl⟩
          · exact Or.inl h
        · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', h1, h2⟩
      · intro b' hb'
        rcases List.mem_cons.mp hb' with rfl | hm
        · exact hl _ _ (by simp)
        · exact hall b' hm

theorem mem_zipIdx' {ps : List V} {b : V × ℕ} (h : b ∈ ps.zipIdx) :
    ∃ (k : ℕ) (hk : k < ps.length), b = (ps[k], k) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  have hi' : i < ps.length := by simpa using hi
  exact ⟨i, hi', by rw [List.getElem_zipIdx]; simp⟩

/-! ## The walk's start -/

/-- **The constraint the walk starts from**: each argument cell holds its parameter's word, a
registered loop helper's own pointer cell `g^fp`. -/
def initC (I : Inst) (ps : List V) (self : Option ℕ) (Ψ : ℕ → E) : Prop :=
  (∀ k (hk : k < ps.length), Ψ (2 + k) = I.σ ps[k]) ∧ ∀ o, self = some o → Ψ o = I.fpw

section Init

variable {loops : Loops} {sigs : SMap (ℕ × ℕ)} {tables : Tables} {tf : TracedFn} {I : Inst}
  {L₁ : VMap Loc}

/-- **The walk's invariant after the parameters' binding**, in lockstep with the scope walk's
start: the trace whole, the parameters in scope. -/
theorem winv_init (hS : Scoped tf)
    (hL : ∀ v l, L₁[v]? = some l → ∃ b ∈ tf.core.params.zipIdx, b.1 = v ∧ l = .cell (2 + b.2)) :
    WInv (ctxOf loops sigs tf) I
      (initC I tf.core.params (initSt loops tables tf).scope.selfFp)
      { initSt loops tables tf with locs := L₁ }
      ⟨tf.trace.toList, addLive {} tf.core.params, false⟩ := by
  obtain ⟨hnd, hnp⟩ := scoped_allocs hS
  have hnext : (initSt loops tables tf).next = 2 + tf.core.params.length + tf.rets +
      (if (loops[tf.core.name]?).any (·.registered) then 1 else 0) := rfl
  have hnext' : 2 + tf.core.params.length + tf.rets ≤ (initSt loops tables tf).next := by
    rw [hnext]; omega
  have hself : ∀ o, (initSt loops tables tf).scope.selfFp = some o →
      o = 2 + tf.core.params.length + tf.rets ∧
        (loops[tf.core.name]?).any (·.registered) = true := by
    intro o ho
    simp only [initSt, sigOf] at ho
    split at ho
    · next h => cases ho; exact ⟨rfl, h⟩
    · cases ho
  have hparam : ∀ v, (addLive {} tf.core.params).contains v = true → v ∈ tf.core.params :=
    fun v hv => (addLive_contains _ _ v hv).resolve_left (by simp [KMap.contains])
  have hloc : ∀ v l, L₁[v]? = some l → ∃ (k : ℕ) (hk : k < tf.core.params.length),
      tf.core.params[k] = v ∧
      l = .cell (2 + k) := by
    intro v l hv
    obtain ⟨b, hb, rfl, rfl⟩ := hL v l hv
    obtain ⟨k, hk, rfl⟩ := mem_zipIdx' hb
    exact ⟨k, hk, rfl, rfl⟩
  refine
    { cok := ⟨?_, ?_, ?_, ?_⟩
      rest := rfl
      vw := ?_
      two := by
        show 2 ≤ (initSt loops tables tf).next
        have := hnext'
        simp only [Cell] at *
        omega
      abi := hnext'
      fuel := by simp [initSt, ctxOf]
      ret := ?_
      nodup := hnd
      fresh := ?_
      chain := rfl
      pnt := ⟨fun _ _ h => by simp [initSt] at h, fun _ _ h => by simp [initSt] at h⟩
      lazy := rfl }
  · refine ⟨fun n => if h : 2 ≤ n ∧ n - 2 < tf.core.params.length then I.σ tf.core.params[n - 2]
      else I.fpw, fun k hk => ?_, fun o ho => ?_⟩
    · have hc : 2 ≤ 2 + k ∧ 2 + k - 2 < tf.core.params.length := ⟨by omega, by omega⟩
      simp only [hc]
      simp
    · obtain ⟨rfl, -⟩ := hself o ho
      have hc : ¬ (2 ≤ 2 + tf.core.params.length + tf.rets ∧
          2 + tf.core.params.length + tf.rets - 2 < tf.core.params.length) := by omega
      simp only [hc, dite_false]
  · intro Ψ c w hc ⟨h1, h2⟩
    have hc' : (initSt loops tables tf).next ≤ c := hc
    refine ⟨fun k hk => ?_, fun o ho => ?_⟩
    · show Function.update Ψ c w (2 + k) = _
      have hlt : 2 + k < c := lt_of_lt_of_le
        (show 2 + k < 2 + tf.core.params.length + tf.rets by omega) (hnext'.trans hc')
      rw [Function.update_of_ne (Nat.ne_of_lt hlt)]
      exact h1 k hk
    · obtain ⟨rfl, hr⟩ := hself o ho
      rw [hnext, hr] at hc'
      simp only [ite_true] at hc'
      show Function.update Ψ c w _ = _
      rw [Function.update_of_ne (Nat.ne_of_lt (show 2 + tf.core.params.length + tf.rets < c by
        simp only [Cell] at *; omega))]
      exact h2 _ ho
  · intro Ψ hΨ
    exact { consts := fun _ _ h => by simp [initSt] at h
            xors := fun _ _ h => by simp [initSt] at h
            muls := fun _ _ h => by simp [initSt] at h
            loads := fun _ _ h => by simp [initSt] at h
            mats := fun _ _ h => by simp [initSt] at h
            selfFp := fun o ho => hΨ.2 o ho }
  · exact { consts := fun _ _ h => by simp [initSt] at h
            xors := fun _ _ h => by simp [initSt] at h
            muls := fun _ _ h => by simp [initSt] at h
            loads := fun _ _ h => by simp [initSt] at h
            mats := fun _ _ h => by simp [initSt] at h
            selfFp := fun o ho => by
              obtain ⟨rfl, hr⟩ := hself o ho
              refine ⟨by omega, ?_⟩
              show _ < (initSt loops tables tf).next
              rw [hnext, hr]
              simp }
  · intro v l hv hl
    obtain ⟨k, hk, rfl, rfl⟩ := hloc v l hl
    refine ⟨by simp [locBase], ?_, fun Ψ hΨ => ?_⟩
    · show 2 + k < (initSt loops tables tf).next
      have := hnext'
      omega
    exact hΨ.1 k hk
  · intro _ Ψ k w hk ⟨h1, h2⟩
    have hk' : k < tf.rets := hk
    show initC I tf.core.params _ (Function.update Ψ (2 + tf.core.params.length + k) w)
    refine ⟨fun j hj => ?_, fun o ho => ?_⟩
    · rw [Function.update_of_ne (show 2 + j ≠ 2 + tf.core.params.length + k by omega)]
      exact h1 j hj
    · obtain ⟨rfl, -⟩ := hself o ho
      rw [Function.update_of_ne
        (show 2 + tf.core.params.length + tf.rets ≠ 2 + tf.core.params.length + k by omega)]
      exact h2 _ ho
  · intro v hv
    have hnv : v ∉ tf.core.params := fun hm => hnp v hm hv
    refine ⟨?_, ?_⟩
    · show L₁[v]? = none
      cases h : L₁[v]? with
      | none => rfl
      | some l =>
        obtain ⟨k, hk, rfl, -⟩ := hloc v l h
        exact absurd (List.getElem_mem hk) hnv
    · cases h : (addLive {} tf.core.params).contains v with
      | false => rfl
      | true => exact absurd (hparam v h) hnv

end Init

/-! ## The selectors a path reads -/

section Sels

variable {σ σ' : Val}

mutual
/-- The selectors on a statement's path depend only on its uses. -/
theorem sels1_congr : ∀ (s : Stmt), (∀ v ∈ Stmt.uses s, σ' v = σ v) → sels1 σ' s = sels1 σ s
  | .atom _, _ => rfl
  | .ite c z n, h => by
      simp only [Stmt.uses, List.mem_cons, List.mem_append] at h
      rw [sels1, sels1, h c (Or.inl rfl), pathSels_congr z fun v hv => h v (Or.inr (Or.inl hv)),
        pathSels_congr n fun v hv => h v (Or.inr (Or.inr hv))]
  | .match_ x arms, h => by
      simp only [Stmt.uses, List.mem_cons] at h
      rw [sels1, sels1, armSels_congr x (h x (Or.inl rfl)) arms 0 fun v hv => h v (Or.inr hv)]
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .dispatch .., _ => rfl
  | .ret _, _ => rfl

/-- The selectors on a block's path depend only on its uses. -/
theorem pathSels_congr : ∀ (ss : List Stmt), (∀ v ∈ Stmt.usesList ss, σ' v = σ v) →
    pathSels σ' ss = pathSels σ ss
  | [], _ => rfl
  | s :: ss, h => by
      simp only [Stmt.usesList, List.mem_append] at h
      rw [pathSels, pathSels, walk1_congr s fun v hv => h v (Or.inl hv),
        sels1_congr s fun v hv => h v (Or.inl hv), pathSels_congr ss fun v hv => h v (Or.inr hv)]

theorem armSels_congr (x : V) (hx : σ' x = σ x) : ∀ (arms : List (List Stmt)) (j : ℕ),
    (∀ v ∈ Stmt.usesArms arms, σ' v = σ v) → armSels σ' x j arms = armSels σ x j arms
  | [], _, _ => rfl
  | a :: as, j, h => by
      simp only [Stmt.usesArms, List.mem_append] at h
      rw [armSels, armSels, hx, pathSels_congr a fun v hv => h v (Or.inl hv),
        armSels_congr x hx as (j + 1) fun v hv => h v (Or.inr hv)]
end

mutual
/-- The selectors on a statement's path are among its uses. -/
theorem sels1_sub : ∀ (s : Stmt), ∀ v ∈ sels1 σ s, v ∈ Stmt.uses s
  | .atom _, _, h => by simp [sels1] at h
  | .ite c z n, v, h => by
      simp only [sels1] at h
      simp only [Stmt.uses, List.mem_cons, List.mem_append]
      split at h
      · exact Or.inr (Or.inl (pathSels_sub z v h))
      · exact Or.inr (Or.inr (pathSels_sub n v h))
  | .match_ x arms, v, h => by
      simp only [sels1, List.mem_cons] at h
      simp only [Stmt.uses, List.mem_cons]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (armSels_sub x arms 0 v h)
  | .call .., _, h => by simp [sels1] at h
  | .callIf .., _, h => by simp [sels1] at h
  | .dispatch x .., v, h => by
      simp only [sels1, List.mem_singleton] at h
      simp [Stmt.uses, h]
  | .ret _, _, h => by simp [sels1] at h

/-- The selectors on a block's path are among its uses. -/
theorem pathSels_sub : ∀ (ss : List Stmt), ∀ v ∈ pathSels σ ss, v ∈ Stmt.usesList ss
  | [], _, h => by simp [pathSels] at h
  | s :: ss, v, h => by
      simp only [pathSels] at h
      simp only [Stmt.usesList, List.mem_append]
      split at h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl (sels1_sub s v h)
        · exact Or.inr (pathSels_sub ss v h)
      · exact Or.inl (sels1_sub s v h)

theorem armSels_sub (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    ∀ v ∈ armSels σ x j arms, v ∈ Stmt.usesArms arms
  | [], _, _, h => by simp [armSels] at h
  | a :: as, j, v, h => by
      simp only [armSels] at h
      simp only [Stmt.usesArms, List.mem_append]
      split at h
      · exact Or.inl (pathSels_sub a v h)
      · exact Or.inr (armSels_sub x as (j + 1) v h)
end

end Sels
