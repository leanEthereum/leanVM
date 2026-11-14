/-
  LeanVM.Guest.Backend.Sound.Body

  Placement is sound: every statement, every block, a function's body.
-/

module

public import LeanVM.Guest.Backend.Sound.Blocks

/-!
# Placement of a block, and of a function
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : Std.HashMap V Loc} {ctx : Ctx} {C : CallRel}
  {U : String → List E → Prop} {slots : Array KVal} {B : ℕ}

mutual
/-- **Placement of a statement is sound**: every success lays placed statements that mean it. -/
theorem placeStmt_lays (env : PlaceEnv Γ fp ctx C U slots B)
    (hnc : ∀ e ∈ ctx.trace.toList, e.isChain = false) : ∀ (s : Stmt) (rest : List Stmt) (st : St),
    LaysAt Γ fp F ctx slots B True st (placeStmt s rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) s) (StmtS C Γ.L.read (valP Γ.L fp F) s rest)
  | .atom a, rest, st => atom_lays env hnc a rest st
  | .ite c z nz, rest, st =>
      ite_lays env hnc c z nz rest st (placeBlock_lays env hnc z) (placeBlock_lays env hnc nz)
  | .match_ x arms, rest, st => match_lays hnc env x arms rest st (arms_lays env hnc arms)
  | .call f args rets, rest, st => call_lays env hnc f args rets rest st
  | .callIf c f args, rest, st => callIf_lays env hnc c f args rest st
  | .dispatch x fs args rets, rest, st => dispatch_lays env hnc x fs args rets rest st
  | .ret vs, rest, st => ret_lays hnc vs rest st

/-- **Placement of a block is sound.** -/
theorem placeBlock_lays (env : PlaceEnv Γ fp ctx C U slots B)
    (hnc : ∀ e ∈ ctx.trace.toList, e.isChain = false) : ∀ (ss : List Stmt) (st : St),
    LaysAt Γ fp F ctx slots B True st (placeBlock ss)
      (OblList C U Γ.L.read (valP Γ.L fp F) ss)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) ss next kret)
  | [], st => by
      rw [placeBlock]
      exact LaysAt.ofSpec (Q := fun _ => True) (SpecAt.pure fun _ _ _ => trivial)
        fun _ _ _ g next kret hG hn => hn hG
  | s :: rest, st => by
      rw [placeBlock]
      intro hpl
      refine wp_bind.mpr fun _ st1 he1 => wp_bind.mpr fun _ st2 he2 _ st3 he3 => ?_
      obtain ⟨hp1, l1⟩ := placeStmt_lays env hnc s rest st hpl _ st1 he1
      have e2 := endStmt_spec (Γ := Γ) (fp := fp) (F := F) st1 _ st2 he2
      obtain ⟨hp3, l3⟩ := placeBlock_lays env hnc rest st2 (hp1.of_same e2.same) _ st3 he3
      refine ⟨hp3, ((l1.suffix e2).cons l3).imp (fun g h => h) fun next kret h => ?_⟩
      exact h fun hr hk => by
        subst hr
        exact hk

theorem arms_lays (env : PlaceEnv Γ fp ctx C U slots B)
    (hnc : ∀ e ∈ ctx.trace.toList, e.isChain = false) :
    ∀ (arms : List (List Stmt)) (arm : List Stmt), arm ∈ arms → ∀ st₀,
    LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)
  | [], _, h => nomatch h
  | a :: as, arm, h => fun st₀ =>
      (List.mem_cons.mp h).elim (fun e => e ▸ placeBlock_lays env hnc a st₀)
        (fun h' => arms_lays env hnc as arm h' st₀)
end

end
end LeanVM.Guest.Backend
