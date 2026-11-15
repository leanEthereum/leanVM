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

/-! ## The statements the function level takes -/

/-- **A flush places no value but those its trace makes** (the flush analogue of `PlaceNew`). -/
def FlushNew : Prop :=
  ∀ (ctx : Ctx) (st : St) (up : List Stmt), wpP (flush up) ctx st fun _ st' =>
    ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest

/-- The walk's instance of a path with the callee frames `kfps`. -/
noncomputable def instK {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) (pf : Placed) (fp : ℕ)
    (hdr : E × E) (σ : Val) (es : List Ev) (kfps : List ℕ) : Inst :=
  { instOf W tf pf fp hdr σ es with kf := kfps }

/-- The memories of the walk's words: the frame words patched at the temporaries' cells. -/
def agK {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) (pf : Placed) (fp : ℕ) (hdr : E × E)
    (es : List Ev) (kfps : List ℕ) (I : Inst) :
    Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop :=
  fun σ' Ψ kh => AgOf W tf fp σ' es kfps hdr ⟨patchT I Ψ σ', kh⟩ pf.fn.frameSize

/-- **The block lemma at a function's body** (the frame side's): placing the body on the path of
the instance gives its words. -/
def BodyW : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → ∀ tf ∈ W.p, Scoped tf → ∀ pf, World.PlacedAs W tf pf →
  TmpsApart tf pf → NoSelfCall tf →
  ∀ (fp : ℕ), (tf.core.name = "main" → fp = 0) → ∀ (kfps : List ℕ) (hdr : E × E) (σ : Val)
    (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
    (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0))) →
    (∃ rd, (instOf W tf pf fp hdr σ es).Rd rd) →
    BlockW (World.cplSite W tf.core.name)
      (agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps)) (calls es)
      (ctxOf (loopTable W.p) (sigTable W.p) tf) (instK W tf pf fp hdr σ es kfps)
      (placeBlock tf.core.body) tf.core.body []

/-! ## Facts of the program -/

theorem loopTable_go_name : ∀ (fns : List TracedFn) (t : Loops) (g : String) (x : LoopInfo),
    (fns.foldl (fun table tf => if isLoopName tf.core.name then
      table.insert tf.core.name ⟨tf.loop.1, tf.loop.2⟩ else table) t)[g]? = some x →
    t[g]? = some x ∨ isLoopName g = true
  | [], _, _, _, h => Or.inl h
  | tf :: fns, t, g, x, h => by
      rw [List.foldl_cons] at h
      rcases loopTable_go_name fns _ g x h with h' | h'
      · split at h'
        · next hl =>
          rw [KMap.getElem?_insert] at h'
          split at h'
          · next he => exact Or.inr (he ▸ hl)
          · exact Or.inl h'
        · exact Or.inl h'
      · exact Or.inr h'

/-- **A function the loop table has is a loop helper by its name.** -/
theorem isLoopName_of_registered {fns : List TracedFn} {g : String}
    (h : ((loopTable fns)[g]?).any (·.registered) = true) : isLoopName g = true := by
  cases hx : (loopTable fns)[g]? with
  | none => rw [hx] at h; cases h
  | some x =>
    unfold loopTable at hx
    rcases loopTable_go_name fns {} g x hx with h' | h'
    · simp at h'
    · exact h'

/-! ## The clauses from the words of the values read -/

section Clauses

variable {κ₀ : ℕ} {W : World κ₀} {tf : TracedFn} {pf : Placed} {fp : ℕ} {hdr : E × E}
  {σ : Val} {es : List Ev} {vs : List V} {I : Inst}

/-- **The clauses of the frame**, from the words the walk gives: the values the path read (`RW`
at the body's end, whose places stay, `FlushNew`), the parameters (the initial constraint), the
temporaries (patched), a registered loop helper's own pointer cell, and the callee headers. -/
theorem frameClauses_of (hsc : Scoped tf) (hta : TmpsApart tf pf)
    (hpf : ∃ t t', placeFn (loopTable W.p) (sigTable W.p) t tf = .ok (pf, t'))
    (hI : I.tmps = Stmt.tmpsList tf.core.body ∧ I.locs = pf.locs ∧
      I.σ = zeroTmps (Stmt.tmpsList tf.core.body) σ ∧ I.fpw = ofK (addressOfIndex fp))
    (hw : walk σ tf.core.body = .ret es vs)
    {C₀ C' : (ℕ → E) → Prop} {Ψ : ℕ → E} (hΨ : C' Ψ) (hs : Stronger C' C₀)
    {self : Option ℕ} (hC₀ : ∀ Ψ, C₀ Ψ → initC I tf.core.params self Ψ)
    (hself : registered (loopTable W.p) tf.core.name → self = some (2 + tf.core.params.length))
    (hpar : ∀ k (hk : k < tf.core.params.length), cellP pf.locs tf.core.params[k] = some (2 + k))
    {st₂ : St} (hle : LocsLe st₂.locs pf.locs)
    (hnew : ∀ v, pf.locs[v]? ≠ none → st₂.locs[v]? ≠ none ∨ v ∈ allocsOf st₂.rest)
    (hrw : RW I C' st₂ (pathVals I.σ tf.core.body (.ret es vs)))
    {hs' : List (E × E)} (hhs : HsOk I (ctxOf (loopTable W.p) (sigTable W.p) tf) (calls es) hs')
    (hlen : hs'.length = (calls es).length) (hhdr : I.hdr = hdr)
    (σ' : Val) (hS : I.Same σ') :
    FrameClauses (loopTable W.p) tf pf fp σ' es vs hdr
      ⟨patchT I Ψ σ', fun i => hs'.getD i (0, 0)⟩ := by
  obtain ⟨hT, hL, hσ, hfpw⟩ := hI
  obtain ⟨t, t', hplace⟩ := hpf
  have hfresh := hta.fresh
  have hwi := walk_within (σ := σ) tf.core.body
  rw [hw] at hwi
  have hin : ∀ v n, cellP pf.locs v = some n → 2 ≤ n ∧ n < pf.fn.frameSize :=
    placeFn_inFrame _ _ _ _ _ _ hplace hsc
  -- the words of the values off the temporaries, at the frame words `Ψ`
  have hSv : ∀ v, v ∉ Stmt.tmpsList tf.core.body → σ' v = I.σ v := fun v hv => hS v (hT ▸ hv)
  have hpatch_off : ∀ n, ¬ I.tc n → patchT I Ψ σ' n = Ψ n := fun n hn => by simp [patchT, hn]
  have hpatch_tmp : ∀ t n, t ∈ Stmt.tmpsList tf.core.body → cellP pf.locs t = some n →
      patchT I Ψ σ' n = σ' t := by
    intro t n ht hc
    have htc : I.tc n := ⟨t, hT ▸ ht, hL ▸ hc⟩
    have hch := Classical.choose_spec htc
    have heq : Classical.choose htc = t := hta.inj _ (hT ▸ hch.1) t ht n (hL ▸ hch.2) hc
    simp [patchT, htc, heq]
  have hsels : pathSels σ' tf.core.body = pathSels I.σ tf.core.body :=
    pathSels_congr _ fun v hv => hSv v fun ht => (hfresh.2 v ht).1 hv
  -- a value the path read and the body names is placed by the body's end, with its word
  have hread : ∀ v ∈ pathVals I.σ tf.core.body (.ret es vs), v ∉ Stmt.tmpsList tf.core.body →
      ∀ l, pf.locs[v]? = some l → locW Ψ l = σ' v := by
    intro v hv hvt l hl
    obtain ⟨hna, hwd⟩ := hrw v hv
    have hl2 : st₂.locs[v]? = some l := by
      rcases hnew v (by rw [hl]; simp) with h | h
      · obtain ⟨l', hl'⟩ := Option.ne_none_iff_exists'.mp h
        rw [hle v l' hl'] at hl
        cases hl
        exact hl'
      · exact absurd h hna
    rw [(hwd (hT ▸ hvt) l hl2).2.2 Ψ hΨ, hSv v hvt]
  have hnamed : ∀ v ∈ readsP tf.core.params tf.core.body σ' es vs,
      v ∈ tf.core.params ∨ v ∈ Stmt.tmpsList tf.core.body ∨
        (v ∈ Stmt.usesList tf.core.body ∧ v ∈ pathVals I.σ tf.core.body (.ret es vs)) := by
    intro v hv
    simp only [readsP, List.mem_append, List.mem_flatMap] at hv
    rcases hv with (((hv | ⟨e, he, hv⟩) | hv) | ⟨e, he, hv⟩) | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inr ⟨hwi.1 e he v hv, by
        simp only [pathVals, outEs, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inl ⟨e, he, hv⟩)⟩)
    · exact Or.inr (Or.inr ⟨hwi.2.2 v hv, by
        simp only [pathVals, retVals, List.mem_append]
        exact Or.inl (Or.inr hv)⟩)
    · exact Or.inr (Or.inl (hwi.2.1.subset (List.mem_flatMap.mpr ⟨e, he, hv⟩)))
    · rw [hsels] at hv
      exact Or.inr (Or.inr ⟨pathSels_sub _ v hv, by
        simp only [pathVals, List.mem_append]
        exact Or.inr hv⟩)
  have hparamW : ∀ k (hk : k < tf.core.params.length), Ψ (2 + k) = σ' tf.core.params[k] := by
    intro k hk
    rw [(hC₀ Ψ (hs Ψ hΨ)).1 k hk, hSv _ fun ht => (hfresh.2 _ ht).2 (List.getElem_mem hk)]
  have hntc : ∀ v l, v ∈ Stmt.usesList tf.core.body ++ tf.core.params → pf.locs[v]? = some l →
      ¬ I.tc (locBase l) := fun v l hv hl ⟨t, ht, hc⟩ =>
    hta.apart hv hl (hT ▸ ht) (hL ▸ hc)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv n hn
    obtain ⟨h2, hlt⟩ := hin v n hn
    refine ⟨h2, hlt, ?_⟩
    have hl : pf.locs[v]? = some (.cell n) := by
      unfold cellP at hn
      split at hn
      · next m hm => cases hn; exact hm
      · cases hn
    rcases hnamed v hv with hp | ht | ⟨hu, hpv⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
      have := hpar k hk
      rw [hn] at this
      cases this
      have hn' := hntc _ _ (List.mem_append_right _ (List.getElem_mem hk)) hl
      simp only [locBase] at hn'
      show patchT I Ψ σ' (2 + k) = _
      rw [hpatch_off _ hn']
      exact hparamW k hk
    · exact hpatch_tmp v n ht hn
    · have hvt : v ∉ Stmt.tmpsList tf.core.body := fun ht => (hfresh.2 v ht).1 hu
      have hn' := hntc _ _ (List.mem_append_left _ hu) hl
      simp only [locBase] at hn'
      show patchT I Ψ σ' n = _
      rw [hpatch_off _ hn']
      exact hread v hpv hvt _ hl
  · intro v hv n e hl
    rcases hnamed v hv with hp | ht | ⟨hu, hpv⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
      have := hpar k hk
      unfold cellP at this
      rw [hl] at this
      cases this
    · obtain ⟨m, hm⟩ := hta.cell ht
      unfold cellP at hm
      rw [hl] at hm
      cases hm
    · have hvt : v ∉ Stmt.tmpsList tf.core.body := fun ht => (hfresh.2 v ht).1 hu
      have := hread v hpv hvt _ hl
      simp only [locW] at this
      show σ' v = patchT I Ψ σ' n * _
      have hn' := hntc _ _ (List.mem_append_left _ hu) hl
      simp only [locBase] at hn'
      rw [hpatch_off _ hn']
      exact this.symm
  · intro _ t ht n hn
    obtain ⟨h2, hlt⟩ := hin t n hn
    exact ⟨h2, hlt, hpatch_tmp t n ht hn⟩
  · intro hreg
    obtain ⟨-, -, -, -, -, hr, -⟩ := placeFn_ok hplace
    have hr0 : tf.rets = 0 := by simpa [sigOf] using hr hreg
    have hnt : ¬ I.tc (2 + tf.core.params.length) := fun ⟨t, ht, hc⟩ =>
      hta.self (hT ▸ ht) (by rw [hr0, Nat.add_zero, ← hL]; exact hc)
    show patchT I Ψ σ' (2 + tf.core.params.length) = _
    rw [hpatch_off _ hnt, (hC₀ Ψ (hs Ψ hΨ)).2 _ (hself hreg), hfpw]
  · intro i c hc hk
    have hi : i < hs'.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.mp hc).1
    show IsInK (hs'.getD i (0, 0)).1 ∧ IsInK (hs'.getD i (0, 0)).2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hhs.1 (fun hm => by rw [hhdr]; exact hk (by simpa [ctxOf] using hm)) _
      (List.getElem_mem hi)
  · intro i c hc hf
    have hi : i < hs'.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.mp hc).1
    show hs'.getD i (0, 0) = hdr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      hhs.2 i hi c hc (by simpa [ctxOf] using hf), hhdr]

end Clauses

end
end LeanVM.Guest.Backend.Complete
