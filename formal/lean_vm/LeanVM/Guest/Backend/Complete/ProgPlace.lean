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

theorem mapM_cellAt : ∀ (vs : List V) (st : St), wpP (vs.mapM cellAt) ctx st fun cs st' =>
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
      refine wp_pure.mpr (wp_bind.mpr (wp_mono (mapM_cellAt vs st)
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
      refine wp_bind.mpr (wp_mono (mapM_cellAt vs _) fun cs s ⟨hs, hl, hc⟩ => ?_)
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

end Visit

end
end LeanVM.Guest.Backend.Complete
