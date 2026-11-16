/-
  LeanVM.Guest.Backend.Complete.ProgPlace

  What whole-program completeness needs of a compiled program and its placement: the functions
  found by name, the frame sizes of the layout, the parameters and returned values in their ABI
  cells, and no call of `main`.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgCompose
public import LeanVM.Guest.Backend.Complete.FrameBody
public import LeanVM.Guest.Memory.SizeTotal

/-!
# The program's facts

* `fnOf_spec`, `fnOf_of_mem`: `World.fnOf` finds every function of a compiled program, placed.
* `fsB_fn`, `fsB_main`: the layout's frame of a function is its placed frame, `main`'s with the
  jump tables after it from `tablesBase`.
* `placed_params`, `placed_rets`, `placed_size`: placement binds the parameters to the argument
  cells, every `return`'s values to the return cells, and its frame holds the ABI (with a
  registered loop helper's own pointer).
* `no_main_call`: no path calls `main` (`isCallee`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The returns and callees of a placed block -/

mutual
/-- The values of the `return`s of a statement. -/
def retS : Stmt → List (List V)
  | .ret vs => [vs]
  | .ite _ z n => retL z ++ retL n
  | .match_ _ arms => retA arms
  | _ => []

/-- The values of the `return`s of a block. -/
def retL : List Stmt → List (List V)
  | [] => []
  | s :: ss => retS s ++ retL ss

/-- The values of the `return`s of arms. -/
def retA : List (List Stmt) → List (List V)
  | [] => []
  | a :: as => retL a ++ retA as
end

/-- The values `vs` are bound to the return cells. -/
def RetIn (ctx : Ctx) (vs : List V) (locs : VMap Loc) : Prop :=
  ∀ k (hk : k < vs.length), locs[vs[k]]? = some (.cell (2 + ctx.argCells + k))

section Visit

variable {ctx : Ctx} {α β : Type}

theorem RetIn.mono {vs : List V} {l l' : VMap Loc} (h : LocsLe l l') (hr : RetIn ctx vs l) :
    RetIn ctx vs l' := fun k hk => h _ _ (hr k hk)

/-- A step that binds the values, then steps that keep the places. -/
theorem wp_est {m : P α} {f : α → P β} {st : St} {vs : List V}
    (hm : wpP m ctx st fun _ s => RetIn ctx vs s.locs) (hf : ∀ a s, MonoAt ctx s (f a)) :
    wpP (m >>= f) ctx st fun _ s => RetIn ctx vs s.locs :=
  wp_bind.mpr (wp_mono hm fun a s h => wp_mono (hf a s) fun _ _ h' => h.mono h'.2)

/-- A step that binds the values, then steps that keep the places but maybe not the next cell. -/
theorem wp_estL {m : P α} {f : α → P β} {st : St} {vs : List V}
    (hm : wpP m ctx st fun _ s => RetIn ctx vs s.locs)
    (hf : ∀ a s, wpP (f a) ctx s fun _ s' => LocsLe s.locs s'.locs) :
    wpP (m >>= f) ctx st fun _ s => RetIn ctx vs s.locs :=
  wp_bind.mpr (wp_mono hm fun a s h => wp_mono (hf a s) fun _ _ h' => h.mono h')

/-- Steps before the one that binds them. -/
theorem wp_pass {m : P α} {f : α → P β} {st : St} {Q : β → St → Prop}
    (hf : ∀ a s, wpP (f a) ctx s Q) : wpP (m >>= f) ctx st Q :=
  wp_bind.mpr fun a s _ => hf a s

/-- A step that checks a fact, then any steps. -/
theorem wp_estC {m : P α} {f : α → P β} {st : St} {p : Prop} (hm : wpP m ctx st fun _ _ => p) :
    wpP (m >>= f) ctx st fun _ _ => p :=
  wp_bind.mpr (wp_mono hm fun _ _ h => fun _ _ _ => h)

theorem mapM_cellAtR : ∀ (vs : List V) (st : St), wpP (vs.mapM cellAt) ctx st fun cs st' =>
    st' = st ∧ cs.length = vs.length ∧
      ∀ k (hk : k < vs.length) (hk' : k < cs.length), st.locs[vs[k]]? = some (.cell cs[k])
  | [], st => wp_pure.mpr ⟨rfl, rfl, fun k hk => absurd hk (by simp)⟩
  | v :: vs, st => by
    rw [List.mapM_cons]
    refine wp_bind.mpr ?_
    unfold cellAt
    refine wp_bind.mpr (wp_get.mpr ?_)
    split
    · next n hn =>
      refine wp_pure.mpr (wp_bind.mpr (wp_mono (mapM_cellAtR vs st)
        fun cs st' ⟨he, hl, hc⟩ => wp_pure.mpr ⟨he, by simp [hl], fun k hk hk' => ?_⟩))
      cases k with
      | zero => simpa using hn
      | succ k => simpa using hc k (by simpa using hk) (by simpa using hk')
    · exact wp_failP

/-- `inBlock` of a block that binds the values. -/
theorem inBlock_ret {m : P Unit} {vs : List V}
    (hr : ∀ st, wpP m ctx st fun _ s => RetIn ctx vs s.locs) (st : St) :
    wpP (inBlock m) ctx st fun _ s => RetIn ctx vs s.locs := by
  unfold inBlock
  refine wp_pass fun _ _ => ?_
  refine wp_bind.mpr (wp_get.mpr ?_)
  refine wp_pass fun _ _ => ?_
  refine wp_est (hr _) fun _ s => ?_
  mono_straight

/-- A `match` whose arms bind the values. -/
theorem placeMatch_ret {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))} {vs : List V} {st : St}
    (hA : ∀ base exit st, wpP (armsAt base exit) ctx st fun _ s => RetIn ctx vs s.locs) :
    wpP (placeMatch x n rest entered chained armsAt) ctx st fun _ s => RetIn ctx vs s.locs := by
  unfold placeMatch
  repeat' (first
    | refine wp_est (hA _ _ _) fun _ _ => by mono_straight
    | refine wp_pass fun _ _ => ?_
    | split)

/-- Every success keeps the places. -/
def LocsAt (ctx : Ctx) (s : St) (m : P α) : Prop := wpP m ctx s fun _ s' => LocsLe s.locs s'.locs

theorem LocsAt.of_mono {m : P α} {s : St} (hm : MonoAt ctx s m) : LocsAt ctx s m :=
  wp_mono hm fun _ _ h => h.2

theorem LocsAt.bindA {m : P α} {f : α → P β} {s : St} (hm : LocsAt ctx s m)
    (hf : ∀ a s', LocsAt ctx s' (f a)) : LocsAt ctx s (m >>= f) :=
  wp_bind.mpr (wp_mono hm fun a s' h => wp_mono (hf a s') fun _ _ h' => h.trans h')

theorem LocsAt.pure {a : α} {s : St} : LocsAt ctx s (Pure.pure a : P α) :=
  wp_pure.mpr (LocsLe.refl _)

theorem LocsAt.get_bind {f : St → P β} {s : St} (h : LocsAt ctx s (f s)) :
    LocsAt ctx s (get >>= f) :=
  wp_bind.mpr (wp_get.mpr h)

theorem LocsAt.mod_bind {g : St → St} {f : Unit → P β} {s : St} (hg : LocsLe s.locs (g s).locs)
    (h : LocsAt ctx (g s) (f ())) : LocsAt ctx s (modify g >>= f) :=
  wp_bind.mpr (wp_modify.mpr (wp_mono h fun _ _ h' => hg.trans h'))

theorem placeArmsL (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit) (s : St) :
    LocsAt ctx s (placeArms arms j n base exit) :=
  wp_mono (placeArms_mono arms j n base exit s) fun _ _ h => h.2.1

mutual
/-- **Every `return` of a placed block binds its values to the return cells.** -/
theorem blockR : ∀ (ss : List Stmt) (st : St), ∀ vs ∈ retL ss,
    wpP (placeBlock ss) ctx st fun _ s => RetIn ctx vs s.locs
  | [], _, vs, h => by simp [retL] at h
  | s :: rest, st, vs, h => by
      rw [placeBlock]
      simp only [retL, List.mem_append] at h
      rcases h with h | h
      · exact wp_est (stmtR s rest st vs h) fun _ s =>
          MonoAt.bind endStmt_mono fun _ st₂ _ => placeBlock_mono rest st₂
      · exact wp_pass fun _ _ => wp_pass fun _ _ => blockR rest _ vs h

theorem stmtR : ∀ (s : Stmt) (rest : List Stmt) (st : St), ∀ vs ∈ retS s,
    wpP (placeStmt s rest) ctx st fun _ s => RetIn ctx vs s.locs
  | .atom _, _, _, vs, h => by simp [retS] at h
  | .call .., _, _, vs, h => by simp [retS] at h
  | .callIf .., _, _, vs, h => by simp [retS] at h
  | .dispatch .., _, _, vs, h => by simp [retS] at h
  | .ite c z nz, rest, st, vs, h => by
      have hnz : ∀ st, MonoAt ctx st (inBlock (placeBlock nz)) := fun st =>
        wp_mono (inBlock_mono (fun st => placeBlock_mono nz st) st) fun _ _ h => h.1
      simp only [retS, List.mem_append] at h
      rw [placeStmt]
      rcases h with h | h
      · have hzR := inBlock_ret (fun st => blockR z st vs h)
        repeat' (first
          | refine wp_est (hzR _) fun _ _ => by
              repeat' (first | refine MonoAt.bind (hnz _) fun _ _ _ => ?_ | mono_step)
          | refine wp_pass fun _ _ => ?_)
      · have hnzR := inBlock_ret (fun st => blockR nz st vs h)
        repeat' (first
          | refine wp_est (hnzR _) fun _ _ => by mono_straight
          | exact wp_failP
          | refine wp_pass fun _ _ => ?_
          | split)
        all_goals simp_all [retL]
  | .match_ x arms, rest, st, vs, h => by
      simp only [retS] at h
      rw [placeStmt]
      refine wp_pass fun _ _ => ?_
      refine wp_pass fun _ _ => ?_
      refine wp_pass fun _ _ => ?_
      exact placeMatch_ret fun base exit st => armsR arms 0 arms.length base exit st vs h
  | .ret vs', rest, st, vs, h => by
      simp only [retS, List.mem_singleton] at h
      subst h
      rw [placeStmt]
      refine wp_pass fun _ _ => ?_
      refine wp_bind.mpr (wp_read.mpr ?_)
      refine wp_bind.mpr (wp_mono (mapM_cellAtR vs _) fun cs s ⟨hs, hl, hc⟩ => ?_)
      dsimp only
      split
      · exact wp_bind.mpr wp_failP
      · next hne =>
        have hcs : cs = (List.range ctx.retCells).map (2 + ctx.argCells + ·) := by simpa using hne
        refine wp_mono (show MonoAt ctx s _ by mono_straight) fun _ s' h' => RetIn.mono h'.2 ?_
        intro k hk
        subst hs
        rw [hc k hk (hl ▸ hk)]
        simp [hcs]

theorem armsR : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit) (st : St),
    ∀ vs ∈ retA arms, wpP (placeArms arms j n base exit) ctx st fun _ s => RetIn ctx vs s.locs
  | [], _, _, _, _, _, vs, h => by simp [retA] at h
  | arm :: more, j, n, base, exit, st, vs, h => by
      simp only [retA, List.mem_append] at h
      have hL : ∀ e s, LocsAt ctx s (placeArms more (j + 1) n base e) := fun e s =>
        placeArmsL more (j + 1) n base e s
      rw [placeArms]
      rcases h with h | h
      · have hM : ∀ st, wpP (inBlock (placeBlock arm)) ctx st fun _ s => RetIn ctx vs s.locs :=
          inBlock_ret (fun st => blockR arm st vs h)
        generalize placeArms more (j + 1) n base = PA at hL ⊢
        generalize inBlock (placeBlock arm) = IB at hM ⊢
        refine wp_pass fun _ _ => ?_
        refine wp_estL (hM _) fun blk s => ?_
        show LocsAt ctx s _
        have tail : ∀ (e : ArmExit) (top : Cell) (leave : List PStmt) (s₁ : St),
            LocsAt ctx s₁ (do
              let blocks ← PA e
              modify fun s => { s with next := max s.next top }
              pure ((blk ++ leave) :: blocks)) := fun e top leave s₁ =>
          LocsAt.bindA (hL _ _) fun _ _ => LocsAt.mod_bind (LocsLe.refl _) LocsAt.pure
        dsimp only
        split
        · refine LocsAt.bindA (LocsAt.of_mono ?_) fun _ _ => ?_
          · mono_straight
          simp only [pure_bind]
          exact LocsAt.get_bind (tail _ _ _ _)
        · simp only [pure_bind]
          exact LocsAt.get_bind (tail _ _ _ _)
      · have hM := fun e st => armsR more (j + 1) n base e st vs h
        generalize placeArms more (j + 1) n base = PA at hL hM ⊢
        generalize inBlock (placeBlock arm) = IB
        refine wp_pass fun _ blk => wp_pass fun blk _ => ?_
        have tail : ∀ (e : ArmExit) (leave : List PStmt) (s₁ : St),
            wpP (do
              let __do_lift ← get
              let blocks ← PA e
              modify fun s => { s with next := max s.next __do_lift.next }
              pure ((blk ++ leave) :: blocks)) ctx s₁ fun _ s => RetIn ctx vs s.locs :=
          fun e leave s₁ => wp_bind.mpr (wp_get.mpr (wp_estL (hM _ _) fun _ _ =>
            LocsAt.mod_bind (LocsLe.refl _) LocsAt.pure))
        dsimp only
        split
        · refine wp_pass fun _ _ => ?_
          simp only [pure_bind]
          exact tail _ _ _
        · simp only [pure_bind]
          exact tail _ _ _
end


/-! ## No call of `main` -/

/-- `inBlock` of a block that checks a fact. -/
theorem inBlock_C {m : P Unit} {p : Prop} (hr : ∀ st, wpP m ctx st fun _ _ => p) (st : St) :
    wpP (inBlock m) ctx st fun _ _ => p := by
  unfold inBlock
  refine wp_pass fun _ _ => ?_
  refine wp_bind.mpr (wp_get.mpr ?_)
  refine wp_pass fun _ _ => ?_
  exact wp_estC (hr _)

/-- A `match` whose arms check a fact. -/
theorem placeMatch_C {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))} {p : Prop} {st : St}
    (hA : ∀ base exit st, wpP (armsAt base exit) ctx st fun _ _ => p) :
    wpP (placeMatch x n rest entered chained armsAt) ctx st fun _ _ => p := by
  unfold placeMatch
  repeat' (first
    | exact wp_estC (hA _ _ _)
    | refine wp_pass fun _ _ => ?_
    | split)

mutual
/-- **A placed block calls no `main`.** -/
theorem blockC : ∀ (ss : List Stmt) (st : St), ∀ g ∈ Stmt.blockCallees ss,
    wpP (placeBlock ss) ctx st fun _ _ => g ≠ "main"
  | [], _, g, h => by simp [Stmt.blockCallees] at h
  | s :: rest, st, g, h => by
      rw [placeBlock]
      simp only [Stmt.blockCallees, List.mem_append] at h
      rcases h with h | h
      · exact wp_estC (stmtC s rest st g h)
      · exact wp_pass fun _ _ => wp_pass fun _ _ => blockC rest _ g h

theorem stmtC : ∀ (s : Stmt) (rest : List Stmt) (st : St), ∀ g ∈ Stmt.callees s,
    wpP (placeStmt s rest) ctx st fun _ _ => g ≠ "main"
  | .atom _, _, _, g, h => by simp [Stmt.callees] at h
  | .ret _, _, _, g, h => by simp [Stmt.callees] at h
  | .ite c z nz, rest, st, g, h => by
      simp only [Stmt.callees, List.mem_append] at h
      rw [placeStmt]
      rcases h with h | h
      · have hzR := inBlock_C (fun st => blockC z st g h)
        repeat' (first
          | exact wp_estC (hzR _)
          | refine wp_pass fun _ _ => ?_)
      · have hnzR := inBlock_C (fun st => blockC nz st g h)
        repeat' (first
          | exact wp_estC (hnzR _)
          | exact wp_failP
          | refine wp_pass fun _ _ => ?_
          | split)
        all_goals simp_all [Stmt.blockCallees]
  | .match_ x arms, rest, st, g, h => by
      simp only [Stmt.callees] at h
      rw [placeStmt]
      refine wp_pass fun _ _ => wp_pass fun _ _ => wp_pass fun _ _ => ?_
      exact placeMatch_C fun base exit st => armsC arms 0 arms.length base exit st g h
  | .call f args rets, rest, st, g, h => by
      simp only [Stmt.callees, List.mem_singleton] at h
      subst h
      rw [placeStmt]
      refine wp_pass fun _ _ => ?_
      refine wp_bind.mpr (wp_read.mpr ?_)
      dsimp only
      split
      · exact wp_bind.mpr wp_failP
      · next hc => exact fun _ _ _ => by simp_all [isCallee]
  | .callIf c f args, rest, st, g, h => by
      simp only [Stmt.callees, List.mem_singleton] at h
      subst h
      rw [placeStmt]
      refine wp_pass fun _ _ => ?_
      refine wp_bind.mpr (wp_read.mpr ?_)
      dsimp only
      split
      · exact wp_bind.mpr wp_failP
      · next hc => exact fun _ _ _ => by simp_all [isCallee]
  | .dispatch x fs args rets, rest, st, g, h => by
      simp only [Stmt.callees] at h
      rw [placeStmt]
      refine wp_pass fun _ _ => ?_
      refine wp_bind.mpr (wp_read.mpr ?_)
      dsimp only
      split
      · exact wp_bind.mpr wp_failP
      · split
        · exact wp_bind.mpr wp_failP
        · next hc =>
          have := List.all_eq_true.mp (by simpa using hc) g h
          exact fun _ _ _ => by simp_all [isCallee]

theorem armsC : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit) (st : St),
    ∀ g ∈ Stmt.armsCallees arms, wpP (placeArms arms j n base exit) ctx st fun _ _ => g ≠ "main"
  | [], _, _, _, _, _, g, h => by simp [Stmt.armsCallees] at h
  | arm :: more, j, n, base, exit, st, g, h => by
      simp only [Stmt.armsCallees, List.mem_append] at h
      rw [placeArms]
      rcases h with h | h
      · exact wp_pass fun _ _ => wp_estC (inBlock_C (fun st => blockC arm st g h) _)
      · have hM := fun e st => armsC more (j + 1) n base e st g h
        generalize placeArms more (j + 1) n base = PA at hM ⊢
        generalize inBlock (placeBlock arm) = IB
        refine wp_pass fun _ _ => wp_pass fun _ _ => ?_
        repeat' (first
          | exact wp_estC (hM _ _)
          | refine wp_pass fun _ _ => ?_
          | split)
end

end Visit

/-! ## The returned values of a path -/

theorem pre_retP {es : List Ev} {o : Out} {es' : List Ev} {vs : List V} (h : o.pre es = .ret es' vs) :
    ∃ es0, o = .ret es0 vs := by
  cases o with
  | fall _ => cases h
  | ret es0 vs0 => cases h; exact ⟨es0, rfl⟩
  | stuck => cases h

theorem seq_retP {o k : Out} {es : List Ev} {vs : List V} (h : o.seq k = .ret es vs) :
    (∃ e, o = .ret e vs) ∨ ∃ e, k = .ret e vs := by
  cases o with
  | fall e0 =>
    obtain ⟨e1, he⟩ := pre_retP h
    exact Or.inr ⟨e1, he⟩
  | ret e0 vs0 =>
    simp only [Out.seq, Out.ret.injEq] at h
    exact Or.inl ⟨e0, by rw [h.2]⟩
  | stuck => cases h

theorem pick_not_retP {σ : Val} {x : V} {args rets : List V} {es : List Ev} {vs : List V} :
    ∀ (fs : List String) (j : ℕ), pick σ x args rets j fs ≠ .ret es vs
  | [], _, h => by simp [pick] at h
  | f :: fs, j, h => by
    unfold pick at h
    split at h
    · cases h
    · exact pick_not_retP fs (j + 1) h

mutual
theorem walk1_retP {σ : Val} : ∀ (s : Stmt) {es : List Ev} {vs : List V}, walk1 σ s = .ret es vs →
    vs ∈ retS s
  | .atom _, _, _, h => by simp [walk1] at h
  | .ite c z n, es, vs, h => by
    simp only [walk1] at h
    obtain ⟨es0, h0⟩ := pre_retP h
    simp only [retS, List.mem_append]
    split_ifs at h0
    · exact Or.inl (walk_retP z h0)
    · exact Or.inr (walk_retP n h0)
  | .match_ x arms, es, vs, h => by
    simp only [walk1] at h
    exact walkArms_retP x arms 0 h
  | .call .., _, _, h => by simp [walk1] at h
  | .callIf .., _, _, h => by simp [walk1] at h
  | .dispatch x fs args rets, _, _, h => by
    simp only [walk1] at h; exact absurd h (pick_not_retP fs 0)
  | .ret vs', es, vs, h => by
    simp only [walk1, Out.ret.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [retS]

/-- **The values a path returns are a `return`'s.** -/
theorem walk_retP {σ : Val} : ∀ (ss : List Stmt) {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → vs ∈ retL ss
  | [], _, _, h => by simp [walk] at h
  | s :: ss, es, vs, h => by
    simp only [walk] at h
    simp only [retL, List.mem_append]
    rcases seq_retP h with ⟨e, he⟩ | ⟨e, he⟩
    · exact Or.inl (walk1_retP s he)
    · exact Or.inr (walk_retP ss he)

theorem walkArms_retP {σ : Val} (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {es : List Ev}
    {vs : List V}, walkArms σ x j arms = .ret es vs → vs ∈ retA arms
  | [], _, _, _, h => by simp [walkArms] at h
  | a :: as, j, es, vs, h => by
    unfold walkArms at h
    simp only [retA, List.mem_append]
    split_ifs at h
    · exact Or.inl (walk_retP a h)
    · exact Or.inr (walkArms_retP x as (j + 1) h)
end

/-! ## A placed function -/

section Fn

variable {loops : Loops} {sigs : SMap (ℕ × ℕ)} {t t' : Tables} {tf : TracedFn} {pf : Placed}

theorem placeBody_rest (st : St) : MonoAt (ctxOf loops sigs tf) st (do
    placeBlock tf.core.body
    flush []
    if !(← get).rest.isEmpty then failP "the trace goes on past the function") :=
  MonoAt.bind (placeBlock_mono _ _) fun _ _ _ => MonoAt.bind flush_mono fun _ _ _ => by
    mono_straight

/-- **Placement binds the parameters to the argument cells**, every `return`'s values to the
return cells, and its frame holds the ABI. -/
theorem placeFn_abi (h : placeFn loops sigs t tf = .ok (pf, t')) :
    (∀ k (hk : k < tf.core.params.length), cellP pf.locs tf.core.params[k] = some (2 + k)) ∧
    (∀ vs ∈ retL tf.core.body, ∀ k (hk : k < vs.length),
      cellP pf.locs vs[k] = some (2 + tf.core.params.length + k)) ∧
    2 + tf.core.params.length + tf.rets +
      (if (loops[tf.core.name]?).any (·.registered) then 1 else 0) ≤ pf.fn.frameSize := by
  obtain ⟨st', hrun, rfl, -, -, -, -⟩ := placeFn_ok h
  refine ⟨fun k hk => ?_, fun vs hv k hk => ?_, ?_⟩
  · have hw : wpP (placeBody tf) (ctxOf loops sigs tf) (initSt loops t tf) fun _ s =>
        s.locs[tf.core.params[k]]? = some (.cell (2 + k)) := by
      unfold placeBody
      exact wp_bind.mpr (wp_mono (forM_bindTo_st tf.core.params.zipIdx _) fun _ s₁ ⟨_, _, _, hP⟩ =>
        wp_mono (placeBody_rest s₁) fun _ _ h => h.2 _ _ (hP (tf.core.params[k], k)
          (List.mem_iff_getElem.mpr ⟨k, by simpa using hk, by simp⟩)))
    simp [cellP, hw () st' hrun]
  · have hw : wpP (placeBody tf) (ctxOf loops sigs tf) (initSt loops t tf)
        fun _ s => RetIn (ctxOf loops sigs tf) vs s.locs := by
      unfold placeBody
      exact wp_pass fun _ _ => wp_est (blockR _ _ vs hv) fun _ _ =>
        MonoAt.bind flush_mono fun _ _ _ => by mono_straight
    simp [cellP, hw () st' hrun k hk, ctxOf, sigOf]
  · have hw : wpP (placeBody tf) (ctxOf loops sigs tf) (initSt loops t tf) fun _ s =>
        (initSt loops t tf).next ≤ s.next := by
      unfold placeBody
      exact wp_bind.mpr (wp_mono (forM_bindTo_st tf.core.params.zipIdx _) fun _ s₁ ⟨he, _, _, _⟩ =>
        wp_mono (placeBody_rest s₁) fun _ _ h => by rw [he] at h; exact h.1)
    have := hw () st' hrun
    simpa [initSt, sigOf] using this

end Fn

/-! ## The program -/

section Program

variable {κ₀ : ℕ} {W : World κ₀}

theorem fnOf_spec {f : String} {tf : TracedFn} {pf : Placed} (h : W.fnOf f = some (tf, pf)) :
    tf ∈ W.p ∧ tf.core.name = f ∧ World.PlacedAs W tf pf ∧ W.locs f = pf.locs := by
  unfold World.fnOf at h
  split at h
  · next tf' pf' h1 h2 =>
    cases h
    have ht := List.find?_some h1
    have hp := List.find?_some h2
    simp only [beq_iff_eq] at ht hp
    refine ⟨List.mem_of_find?_eq_some h1, ht, ⟨List.mem_of_find?_eq_some h2, by rw [hp, ht]⟩, ?_⟩
    simp [World.locs, h2]
  · cases h

theorem placed_names (hW : W.Compiled) :
    W.placed.map (·.fn.name) = W.p.map (·.core.name) ∧ (W.p.map (·.core.name)).Nodup := by
  obtain ⟨placed, tables, hpp, -, -, -⟩ := lowerProgram_ok hW.1
  obtain ⟨-, -, hnd, -, hpf⟩ := placeProgram_ok hpp
  obtain ⟨-, hall⟩ := placeFns_spec _ _ hpf
  have hplaced : W.placed = placed := by simp [World.placed, hpp]
  exact ⟨hplaced ▸ forall₂_names hall, hnd⟩

theorem fnOf_of_mem (hW : W.Compiled) {tf : TracedFn} (htf : tf ∈ W.p) :
    ∃ pf, W.fnOf tf.core.name = some (tf, pf) ∧ World.PlacedAs W tf pf := by
  obtain ⟨hn, hnd⟩ := placed_names hW
  have h1 : W.p.find? (·.core.name == tf.core.name) = some tf := by
    cases h : W.p.find? (·.core.name == tf.core.name) with
    | none =>
      have := List.find?_eq_none.mp h tf htf
      simp at this
    | some tf' =>
      have ht := List.find?_some h
      simp only [beq_iff_eq] at ht
      rw [eq_of_name hnd (List.mem_of_find?_eq_some h) htf ht]
  have hmem : tf.core.name ∈ W.placed.map (·.fn.name) := by
    rw [hn]; exact List.mem_map_of_mem htf
  obtain ⟨pf, hpf, hpn⟩ := List.mem_map.mp hmem
  cases h2 : W.placed.find? (·.fn.name == tf.core.name) with
  | none =>
    have := List.find?_eq_none.mp h2 pf hpf
    simp [hpn] at this
  | some pf' =>
    have hp := List.find?_some h2
    simp only [beq_iff_eq] at hp
    refine ⟨pf', ?_, List.mem_of_find?_eq_some h2, hp⟩
    simp [World.fnOf, h1, h2]

/-- The placement of a function of a compiled program succeeds. -/
theorem placed_of (hW : W.Compiled) {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (hpa : World.PlacedAs W tf pf) :
    ∃ ti ti', placeFn (loopTable W.p) (sigTable W.p) ti tf = .ok (pf, ti') := by
  obtain ⟨pre, post, f, hat⟩ := fnAt_of_placedAs hW htf hpa
  obtain ⟨ti, ti', hplace, -⟩ := hat.placed
  exact ⟨ti, ti', hplace⟩

theorem placed_params (hW : W.Compiled) {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (hpa : World.PlacedAs W tf pf) :
    ∀ k (hk : k < tf.core.params.length), cellP pf.locs tf.core.params[k] = some (2 + k) := by
  obtain ⟨ti, ti', h⟩ := placed_of hW htf hpa
  exact (placeFn_abi h).1

theorem placed_rets (hW : W.Compiled) {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (hpa : World.PlacedAs W tf pf) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ tf.core.body = .ret es vs) :
    ∀ k (hk : k < vs.length), cellP pf.locs vs[k] = some (2 + tf.core.params.length + k) := by
  obtain ⟨ti, ti', h⟩ := placed_of hW htf hpa
  exact (placeFn_abi h).2.1 vs (walk_retP _ hw)

theorem placed_size (hW : W.Compiled) {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (hpa : World.PlacedAs W tf pf) :
    2 + tf.core.params.length ≤ pf.fn.frameSize ∧
      (registered (loopTable W.p) tf.core.name → 2 + tf.core.params.length < pf.fn.frameSize) := by
  obtain ⟨ti, ti', h⟩ := placed_of hW htf hpa
  have := (placeFn_abi h).2.2
  refine ⟨by split at this <;> omega, fun hr => ?_⟩
  have hr' : ((loopTable W.p)[tf.core.name]?).any (·.registered) = true := hr
  simp only [hr', ↓reduceIte] at this
  omega

/-- **No path of a compiled program calls `main`.** -/
theorem no_main_call (hW : W.Compiled) {tf : TracedFn} (htf : tf ∈ W.p) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ tf.core.body = .ret es vs) : ∀ c ∈ calls es, c.f ≠ "main" := by
  intro c hc
  obtain ⟨pf, -, hpa⟩ := fnOf_of_mem hW htf
  obtain ⟨ti, ti', h⟩ := placed_of hW htf hpa
  obtain ⟨st', hrun, -, -, -, -, -⟩ := placeFn_ok h
  have hcf : c.f ∈ Stmt.blockCallees tf.core.body :=
    walk_callees (σ := σ) tf.core.body (by rw [hw]; exact hc)
  have hw : wpP (placeBody tf) (ctxOf (loopTable W.p) (sigTable W.p) tf)
      (initSt (loopTable W.p) ti tf) fun _ _ => c.f ≠ "main" := by
    unfold placeBody
    exact wp_pass fun _ _ => wp_estC (blockC _ _ c.f hcf)
  exact hw () st' hrun

/-- **The layout's frame of a function but `main`** is its placed frame. -/
theorem fsB_fn (hW : W.Compiled) {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (hpa : World.PlacedAs W tf pf) (hm : tf.core.name ≠ "main") :
    W.fsB tf.core.name = pf.fn.frameSize := by
  obtain ⟨placed, tables, hpp, hfns, -, -⟩ := lowerProgram_ok hW.1
  obtain ⟨hmain, -, hnd, -, hpf⟩ := placeProgram_ok hpp
  obtain ⟨-, hall⟩ := placeFns_spec _ _ hpf
  obtain ⟨hlen, hget⟩ := forall₂_getElem hall
  have hplaced : W.placed = placed := by simp [World.placed, hpp]
  obtain ⟨hmem, hname⟩ := hpa
  rw [hplaced] at hmem
  obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hmem
  have hi : i < W.p.length := hlen ▸ hi'
  obtain ⟨ti, ti', hplace, -⟩ := hget i hi hi'
  have hpn := placeFn_name hplace
  obtain rfl : W.p[i] = tf :=
    eq_of_name hnd (List.getElem_mem hi) htf (by rw [← hpn.1, hname])
  have hi0 : i ≠ 0 := by
    rintro rfl
    have h0 : W.p[0].core.name = "main" := by
      rw [List.head?_map, List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at hmain
      simpa using hmain
    exact hm h0
  have hsplit : W.fns = (placed.take i).map (fun pf => (emitFn pf.fn).1) ++
      (emitFn placed[i].fn).1 :: (placed.drop (i + 1)).map (fun pf => (emitFn pf.fn).1) := by
    have e : placed = placed.take i ++ placed[i] :: placed.drop (i + 1) := by
      rw [← List.drop_eq_getElem_cons hi', List.take_append_drop]
    rw [hfns]
    conv_lhs => rw [e]
    rw [List.map_append, List.map_cons]
  have hpre : (placed.take i).map (fun pf => (emitFn pf.fn).1) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.take_eq_nil_iff, not_or]
    exact ⟨hi0, List.ne_nil_of_length_pos (by omega)⟩
  obtain ⟨pre', hs'⟩ := withTables_keep W.slots hsplit hpre
  have hfr := layout_frame (withTables W.fns W.slots).2 (World.nodup hW) hs'
  have hn : (emitFn placed[i].fn).1.name = W.p[i].core.name := hpn.1
  show W.layout.frame.getD W.p[i].core.name 0 = placed[i].fn.frameSize
  rw [World.layout, layoutOf, KMap.getD_eq_getD_getElem?, ← hn, hfr]
  rfl

/-- **`main`'s frame in the layout** is its placed frame and the jump tables after it, from
`tablesBase`. -/
theorem fsB_main (hW : W.Compiled) {tf : TracedFn} {pf : Placed}
    (hpa : World.PlacedAs W tf pf) (hm : tf.core.name = "main") :
    W.layout.tablesBase = pf.fn.frameSize ∧ W.fsB "main" = pf.fn.frameSize + W.slots.size := by
  obtain ⟨placed, tables, hpp, hfns, -, -⟩ := lowerProgram_ok hW.1
  obtain ⟨hn, hnd⟩ := placed_names hW
  have hplaced : W.placed = placed := by simp [World.placed, hpp]
  rw [hplaced] at hn
  obtain ⟨hmem, hname⟩ := hpa
  rw [hplaced] at hmem
  have hmain := (World.names hW).2.2.2
  obtain ⟨q, rest, hq⟩ : ∃ q rest, placed = q :: rest := by
    cases h : placed with
    | nil => rw [h] at hmem; cases hmem
    | cons q rest => exact ⟨q, rest, rfl⟩
  have hqn : q.fn.name = "main" := by
    have := congrArg List.head? hn
    rw [hq, hmain] at this
    simpa using this
  obtain rfl : pf = q := List.inj_on_of_nodup_map (hn ▸ hnd) hmem (by rw [hq]; exact List.mem_cons_self)
    (by rw [hname, hm, hqn])
  have hfns' : W.fns = (emitFn pf.fn).1 :: rest.map (fun pf => (emitFn pf.fn).1) := by
    rw [hfns, hq, List.map_cons]
  have hndw := World.nodup hW
  have hmn : (emitFn pf.fn).1.name = "main" := hqn
  cases he : W.slots.isEmpty with
  | false =>
    have hsplit0 : (withTables W.fns W.slots).1 = [⟨"__jump_tables",
        W.slots.zipIdx.map fun (kv, j) => (⟨.set ((emitFn pf.fn).1.frameSize + j) kv, []⟩ : LInstr),
          (emitFn pf.fn).1.frameSize + W.slots.size⟩] ++
        ({ (emitFn pf.fn).1 with frameSize := (emitFn pf.fn).1.frameSize + W.slots.size } ::
          rest.map (fun pf => (emitFn pf.fn).1)) := by
      rw [hfns']
      simp [withTables, he]
    refine ⟨?_, ?_⟩
    · rw [World.layout, layoutOf, layout_tablesBase, hfns']
      simp [withTables, he]
      rfl
    · have hfr := layout_frame (withTables W.fns W.slots).2 hndw hsplit0
      show W.layout.frame.getD "main" 0 = _
      rw [World.layout, layoutOf, KMap.getD_eq_getD_getElem?, ← hmn]
      rw [show (emitFn pf.fn).1.name = ({ (emitFn pf.fn).1 with
        frameSize := (emitFn pf.fn).1.frameSize + W.slots.size } : Lowered).name from rfl, hfr]
      rfl
  | true =>
    have hsz : W.slots.size = 0 := by simpa using he
    have hsplit0 : (withTables W.fns W.slots).1 = [] ++
        ((emitFn pf.fn).1 :: rest.map (fun pf => (emitFn pf.fn).1)) := by
      rw [hfns']
      simp [withTables, he]
    refine ⟨?_, ?_⟩
    · rw [World.layout, layoutOf, layout_tablesBase, hfns']
      simp [withTables, he]
      rfl
    · have hfr := layout_frame (withTables W.fns W.slots).2 hndw hsplit0
      show W.layout.frame.getD "main" 0 = _
      rw [World.layout, layoutOf, KMap.getD_eq_getD_getElem?, ← hmn, hfr, hsz]
      rfl

end Program

end
end LeanVM.Guest.Backend.Complete
