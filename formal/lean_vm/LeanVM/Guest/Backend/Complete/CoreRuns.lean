/-
  LeanVM.Guest.Backend.Complete.CoreRuns
  Placement puts every `frameAddr` run of a function in consecutive cells.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgPlace
public import LeanVM.Guest.Backend.Sound.Atoms

/-!
# `frameAddr` runs in consecutive cells

A path's atoms are its body's (`walk_atomsK`). Placing `frameAddr p run` checks the run's cells
consecutive (`consecutiveFrom`) and fails otherwise, and later steps keep every cell bound
(`LocsLe`), so in a placed function every `frameAddr` run of its body lies in consecutive cells
(`placeFn_runs`, by the recursion `blockFa`, `stmtFa`, `armsFa` over the placed block, as
`ProgPlace.lean`'s `blockR` for the returns).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The atoms of a block -/

mutual
/-- The atoms of a statement. -/
def sAtomsK : Stmt → List Atom
  | .atom a => [a]
  | .ite _ z n => lAtomsK z ++ lAtomsK n
  | .match_ _ arms => aAtomsK arms
  | _ => []

/-- The atoms of a block. -/
def lAtomsK : List Stmt → List Atom
  | [] => []
  | s :: ss => sAtomsK s ++ lAtomsK ss

/-- The atoms of arms. -/
def aAtomsK : List (List Stmt) → List Atom
  | [] => []
  | a :: as => lAtomsK a ++ aAtomsK as
end

section Atoms

variable {σ : Val}

theorem evs_seq_memK {o k : Out} {e : Ev} (h : e ∈ (o.seq k).evs) : e ∈ o.evs ∨ e ∈ k.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp_all [Out.seq, Out.pre, Out.evs]

theorem evs_pre_memK {o : Out} {es : List Ev} {e : Ev} (h : e ∈ (o.pre es).evs) :
    e ∈ es ∨ e ∈ o.evs := by
  rcases o with es' | ⟨es', vs⟩ | _ <;> simp_all [Out.pre, Out.evs]

theorem pick_noAtomK {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ) {a : Atom},
    Ev.atom a ∉ (pick σ x args rets j gs).evs
  | [], _, a => by simp [pick, Out.evs]
  | g :: gs, j, a => by
    unfold pick
    split_ifs
    · simp [Out.evs]
    · exact pick_noAtomK gs (j + 1)

mutual
/-- **A statement's path's atoms are its atoms.** -/
theorem walk1_atomsK : ∀ (s : Stmt) {a : Atom}, Ev.atom a ∈ (walk1 σ s).evs → a ∈ sAtomsK s
  | .atom b, a, h => by
    simp only [walk1, Out.evs, List.mem_singleton, Ev.atom.injEq] at h
    simp [sAtomsK, h]
  | .ite c z m, a, h => by
    rw [walk1] at h
    rcases evs_pre_memK h with h | h
    · simp at h
    · simp only [sAtomsK, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_atomsK z h)
      · exact Or.inr (walk_atomsK m h)
  | .match_ x arms, a, h => by
    rw [walk1] at h
    exact walkArms_atomsK x arms 0 h
  | .call .., a, h => by simp [walk1, Out.evs] at h
  | .callIf c f args, a, h => by
    rw [walk1] at h
    split_ifs at h <;> simp [Out.evs] at h
  | .dispatch x gs args rets, a, h => by
    rw [walk1] at h
    exact absurd h (pick_noAtomK gs 0)
  | .ret _, a, h => by simp [walk1, Out.evs] at h

/-- **A block's path's atoms are its atoms.** -/
theorem walk_atomsK : ∀ (ss : List Stmt) {a : Atom}, Ev.atom a ∈ (walk σ ss).evs → a ∈ lAtomsK ss
  | [], a, h => by simp [walk, Out.evs] at h
  | s :: ss, a, h => by
    rw [walk] at h
    simp only [lAtomsK, List.mem_append]
    rcases evs_seq_memK h with h | h
    · exact Or.inl (walk1_atomsK s h)
    · exact Or.inr (walk_atomsK ss h)

theorem walkArms_atomsK (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {a : Atom},
    Ev.atom a ∈ (walkArms σ x j arms).evs → a ∈ aAtomsK arms
  | [], _, a, h => by simp [walkArms, Out.evs] at h
  | b :: bs, j, a, h => by
    unfold walkArms at h
    simp only [aAtomsK, List.mem_append]
    split_ifs at h
    · exact Or.inl (walk_atomsK b h)
    · exact Or.inr (walkArms_atomsK x bs (j + 1) h)
end

end Atoms

/-! ## Runs in consecutive cells -/

/-- The values `run` are bound to consecutive cells. -/
def RunIn (run : List V) (locs : VMap Loc) : Prop :=
  ∃ b, ∀ k (hk : k < run.length), locs[run[k]]? = some (.cell (b + k))

section Visit

variable {ctx : Ctx} {α β : Type}

theorem RunIn.mono {run : List V} {l l' : VMap Loc} (h : LocsLe l l') (hr : RunIn run l) :
    RunIn run l' :=
  let ⟨b, hb⟩ := hr
  ⟨b, fun k hk => h _ _ (hb k hk)⟩

theorem wp_estF {m : P α} {f : α → P β} {st : St} {run : List V}
    (hm : wpP m ctx st fun _ s => RunIn run s.locs) (hf : ∀ a s, MonoAt ctx s (f a)) :
    wpP (m >>= f) ctx st fun _ s => RunIn run s.locs :=
  wp_bind.mpr (wp_mono hm fun a s h => wp_mono (hf a s) fun _ _ h' => h.mono h'.2)

theorem wp_estLF {m : P α} {f : α → P β} {st : St} {run : List V}
    (hm : wpP m ctx st fun _ s => RunIn run s.locs)
    (hf : ∀ a s, wpP (f a) ctx s fun _ s' => LocsLe s.locs s'.locs) :
    wpP (m >>= f) ctx st fun _ s => RunIn run s.locs :=
  wp_bind.mpr (wp_mono hm fun a s h => wp_mono (hf a s) fun _ _ h' => h.mono h')

theorem inBlock_fa {m : P Unit} {run : List V}
    (hr : ∀ st, wpP m ctx st fun _ s => RunIn run s.locs) (st : St) :
    wpP (inBlock m) ctx st fun _ s => RunIn run s.locs := by
  unfold inBlock
  refine wp_pass fun _ _ => ?_
  refine wp_bind.mpr (wp_get.mpr ?_)
  refine wp_pass fun _ _ => ?_
  refine wp_estF (hr _) fun _ s => ?_
  mono_straight

theorem placeMatch_fa {x : V} {n : ℕ} {rest : List Stmt} {entered : Option (ℕ × Cell)}
    {chained : Bool} {armsAt : Cell → ArmExit → P (List (List PStmt))} {run : List V} {st : St}
    (hA : ∀ base exit st, wpP (armsAt base exit) ctx st fun _ s => RunIn run s.locs) :
    wpP (placeMatch x n rest entered chained armsAt) ctx st fun _ s => RunIn run s.locs := by
  unfold placeMatch
  repeat' (first
    | refine wp_estF (hA _ _ _) fun _ _ => by mono_straight
    | refine wp_pass fun _ _ => ?_
    | split)

/-- **Placing a `frameAddr` binds its run to consecutive cells.** -/
theorem placeAtom_fa (p : V) (run : List V) (st : St) :
    wpP (placeAtom (.frameAddr p run)) ctx st fun _ s => RunIn run s.locs := by
  have key : ∀ (base : Cell) (k : P Unit) (s : St), (∀ s', MonoAt ctx s' k) →
      wpP (do
        let cs ← run.mapM cellAt
        if (!consecutiveFrom base cs) = true then do
          failP "addr of cells that are no run"
          k
        else k) ctx s fun _ s => RunIn run s.locs := by
    intro base k s hk
    refine wp_bind.mpr (wp_mono (mapM_cellAtR run _) fun cs s₁ ⟨hs, hl, hc⟩ => ?_)
    split
    · exact wp_bind.mpr wp_failP
    · next hcons =>
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hcons
      refine wp_mono (hk _) fun _ s' h' => RunIn.mono h'.2 ⟨base, fun j hj => ?_⟩
      subst hs
      rw [hc j hj (hl ▸ hj), consecutiveFrom_getElem hcons j (hl ▸ hj)]
  unfold placeAtom
  simp only
  refine wp_bind.mpr fun lz s₀ _ => ?_
  cases lz
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine wp_bind.mpr (wp_get.mpr ?_)
    split
    · refine wp_bind.mpr (wp_get.mpr ?_)
      split
      · refine wp_bind.mpr fun b s₁ _ => ?_
        dsimp only
        split
        · exact wp_bind.mpr wp_failP
        · exact key _ _ s₁ fun s' => by mono_straight
      · exact wp_failP
    · exact wp_failP
  · simp only [↓reduceIte]
    cases hr : run.head? with
    | none => exact wp_failP
    | some r0 =>
      simp only
      refine wp_bind.mpr fun base s₁ _ => ?_
      dsimp only
      exact key base _ s₁ fun s' => by mono_straight

mutual
/-- **Every `frameAddr` run of a placed block is in consecutive cells.** -/
theorem blockFa : ∀ (ss : List Stmt) (st : St) (p : V) (run : List V),
    Atom.frameAddr p run ∈ lAtomsK ss → wpP (placeBlock ss) ctx st fun _ s => RunIn run s.locs
  | [], _, _, _, h => by simp [lAtomsK] at h
  | s :: rest, st, p, run, h => by
      rw [placeBlock]
      simp only [lAtomsK, List.mem_append] at h
      rcases h with h | h
      · exact wp_estF (stmtFa s rest st p run h) fun _ s =>
          MonoAt.bind endStmt_mono fun _ st₂ _ => placeBlock_mono rest st₂
      · exact wp_pass fun _ _ => wp_pass fun _ _ => blockFa rest _ p run h

theorem stmtFa : ∀ (s : Stmt) (rest : List Stmt) (st : St) (p : V) (run : List V),
    Atom.frameAddr p run ∈ sAtomsK s → wpP (placeStmt s rest) ctx st fun _ s => RunIn run s.locs
  | .atom a, rest, st, p, run, h => by
      simp only [sAtomsK, List.mem_singleton] at h
      subst h
      rw [placeStmt]
      exact wp_pass fun _ _ => placeAtom_fa p run _
  | .call .., _, _, _, _, h => by simp [sAtomsK] at h
  | .callIf .., _, _, _, _, h => by simp [sAtomsK] at h
  | .dispatch .., _, _, _, _, h => by simp [sAtomsK] at h
  | .ret _, _, _, _, _, h => by simp [sAtomsK] at h
  | .ite c z nz, rest, st, p, run, h => by
      have hnz : ∀ st, MonoAt ctx st (inBlock (placeBlock nz)) := fun st =>
        wp_mono (inBlock_mono (fun st => placeBlock_mono nz st) st) fun _ _ h => h.1
      simp only [sAtomsK, List.mem_append] at h
      rw [placeStmt]
      rcases h with h | h
      · have hzR := inBlock_fa (fun st => blockFa z st p run h)
        repeat' (first
          | refine wp_estF (hzR _) fun _ _ => by
              repeat' (first | refine MonoAt.bind (hnz _) fun _ _ _ => ?_ | mono_step)
          | refine wp_pass fun _ _ => ?_)
      · have hnzR := inBlock_fa (fun st => blockFa nz st p run h)
        repeat' (first
          | refine wp_estF (hnzR _) fun _ _ => by mono_straight
          | exact wp_failP
          | refine wp_pass fun _ _ => ?_
          | split)
        all_goals simp_all [lAtomsK]
  | .match_ x arms, rest, st, p, run, h => by
      simp only [sAtomsK] at h
      rw [placeStmt]
      refine wp_pass fun _ _ => ?_
      refine wp_pass fun _ _ => ?_
      refine wp_pass fun _ _ => ?_
      exact placeMatch_fa fun base exit st => armsFa arms 0 arms.length base exit st p run h

theorem armsFa : ∀ (arms : List (List Stmt)) (j n : ℕ) (base : Cell) (exit : ArmExit) (st : St)
    (p : V) (run : List V), Atom.frameAddr p run ∈ aAtomsK arms →
    wpP (placeArms arms j n base exit) ctx st fun _ s => RunIn run s.locs
  | [], _, _, _, _, _, _, _, h => by simp [aAtomsK] at h
  | arm :: more, j, n, base, exit, st, p, run, h => by
      simp only [aAtomsK, List.mem_append] at h
      have hL : ∀ e s, LocsAt ctx s (placeArms more (j + 1) n base e) := fun e s =>
        placeArmsL more (j + 1) n base e s
      rw [placeArms]
      rcases h with h | h
      · have hM : ∀ st, wpP (inBlock (placeBlock arm)) ctx st fun _ s => RunIn run s.locs :=
          inBlock_fa (fun st => blockFa arm st p run h)
        generalize placeArms more (j + 1) n base = PA at hL ⊢
        generalize inBlock (placeBlock arm) = IB at hM ⊢
        refine wp_pass fun _ _ => ?_
        refine wp_estLF (hM _) fun blk s => ?_
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
      · have hM := fun e st => armsFa more (j + 1) n base e st p run h
        generalize placeArms more (j + 1) n base = PA at hL hM ⊢
        generalize inBlock (placeBlock arm) = IB
        refine wp_pass fun _ blk => wp_pass fun blk _ => ?_
        have tail : ∀ (e : ArmExit) (leave : List PStmt) (s₁ : St),
            wpP (do
              let __do_lift ← get
              let blocks ← PA e
              modify fun s => { s with next := max s.next __do_lift.next }
              pure ((blk ++ leave) :: blocks)) ctx s₁ fun _ s => RunIn run s.locs :=
          fun e leave s₁ => wp_bind.mpr (wp_get.mpr (wp_estLF (hM _ _) fun _ _ =>
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

section Fn

variable {loops : Loops} {sigs : SMap (ℕ × ℕ)} {t t' : Tables} {tf : TracedFn} {pf : Placed}

/-- **A placed function's `frameAddr` runs are in consecutive cells.** -/
theorem placeFn_runs (h : placeFn loops sigs t tf = .ok (pf, t')) {p : V} {run : List V}
    (ha : Atom.frameAddr p run ∈ lAtomsK tf.core.body) :
    ∃ b, ∀ k (hk : k < run.length), pf.locs[run[k]]? = some (.cell (b + k)) := by
  obtain ⟨st', hrun, rfl, -, -, -, -⟩ := placeFn_ok h
  have hw : wpP (placeBody tf) (ctxOf loops sigs tf) (initSt loops t tf)
      fun _ s => RunIn run s.locs := by
    unfold placeBody
    exact wp_pass fun _ _ => wp_estF (blockFa _ _ p run ha) fun _ _ =>
      MonoAt.bind flush_mono fun _ _ _ => by mono_straight
  exact hw () st' hrun

end Fn

end
end LeanVM.Guest.Backend.Complete
