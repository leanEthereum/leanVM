/-
  LeanVM.Guest.Backend.Sound.Body

  Placement is sound: every block, chains of `match`es included.
-/

module

public import LeanVM.Guest.Backend.Sound.Chain

/-!
# Placement of a block

One mutual recursion over the core IR: a block is its first statement then the rest, except that
a block whose first `match` begins a chain is placed with the `match`es after it as one statement
(`match_block_lays`), the chain staying open in the walk while they are placed (`OpenOK`).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : VMap Loc} {ctx : Ctx} {C : CallRel}
  {U : String → List E → Prop} {slots : Array KVal} {B : ℕ}

mutual
/-- **Placement of a block is sound**: every success lays placed statements that mean it. -/
theorem placeBlock_lays (env : PlaceEnv Γ fp ctx C U slots B) : ∀ (ss : List Stmt) (st : St),
    LaysAt Γ fp F ctx slots B True st (placeBlock ss)
      (OblList C U Γ.L.read (valP Γ.L fp F) ss)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) ss next kret)
  | [], st => by
      rw [placeBlock]
      exact LaysAt.ofSpec (Q := fun _ => True) (SpecAt.pure fun _ _ _ => trivial)
        fun _ _ _ g next kret hG hn => hn hG
  | .match_ x arms :: rest, st =>
      match_block_lays env x arms rest st (arms_lays env arms) (placeBlock_lays env rest)
        (open_ok env rest)
  | .atom a :: rest, st => LaysAt.seq (atom_lays env a rest st) (placeBlock_lays env rest)
  | .ite c z nz :: rest, st =>
      LaysAt.seq (ite_lays env c z nz rest st (placeBlock_lays env z) (placeBlock_lays env nz))
        (placeBlock_lays env rest)
  | .call f args rets :: rest, st =>
      LaysAt.seq (call_lays env f args rets rest st) (placeBlock_lays env rest)
  | .callIf c f args :: rest, st =>
      LaysAt.seq (callIf_lays env c f args rest st) (placeBlock_lays env rest)
  | .dispatch x fs args rets :: rest, st =>
      LaysAt.seq (dispatch_lays env x fs args rets rest st) (placeBlock_lays env rest)
  | .ret vs :: rest, st => LaysAt.seq (ret_lays vs rest st) (placeBlock_lays env rest)

theorem arms_lays (env : PlaceEnv Γ fp ctx C U slots B) :
    ∀ (arms : List (List Stmt)) (arm : List Stmt), arm ∈ arms → ∀ st₀,
    LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)
  | [], _, h => nomatch h
  | a :: as, arm, h => fun st₀ =>
      (List.mem_cons.mp h).elim (fun e => e ▸ placeBlock_lays env a st₀)
        (fun h' => arms_lays env as arm h' st₀)

/-- **A block an open chain enters is sound.** -/
theorem open_ok (env : PlaceEnv Γ fp ctx C U slots B) :
    ∀ ss : List Stmt, OpenOK Γ fp F ctx C U slots B ss
  | [] => trivial
  | .match_ x arms :: rest =>
      open_step env x arms rest (arms_lays env arms) (placeBlock_lays env rest) (open_ok env rest)
  | .atom _ :: _ => trivial
  | .ite .. :: _ => trivial
  | .call .. :: _ => trivial
  | .callIf .. :: _ => trivial
  | .dispatch .. :: _ => trivial
  | .ret _ :: _ => trivial
end

end
end LeanVM.Guest.Backend
