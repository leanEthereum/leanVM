/-
  LeanVM.Guest.B1.Sig.ArmCostB2C

  `verify_lean_xmss`'s separately counted arms (`B2C.costW`) at each opcode: the chosen-arm cost
  walk of `ArmCost` at the table's counts for that opcode.
-/

module

public import LeanVM.Guest.B1.Sig.ArmCost
public import LeanVM.Guest.B2C.Defs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

noncomputable section

/-- The table of separately counted arms at one opcode. -/
def tabOp (acs : List (ℕ × List (List ℕ))) (op : Opcode) : ℕ → Option (List ℕ) :=
  fun i => (armRaw acs i).map fun cs => cs.map fun l => l.getD (opIdx op) 0

theorem nth_getD_map (i : ℕ) : ∀ (cs : List (List ℕ)) (k : ℕ),
    (nth cs k []).getD i 0 = (cs.map fun l => l.getD i 0).getD k 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: cs, k + 1 => nth_getD_map i cs k

section Bridge

variable (acs : List (ℕ × List (List ℕ))) (σ : Val) (op : Opcode)

mutual
theorem cost1_eq : ∀ s : Stmt, cost1 acs σ s op = cw1 (tabOp acs op) σ s
  | .atom _ => rfl
  | .ite c z n => by
      rw [cost1, cw1]
      split
      · exact costW_eq z
      · exact costW_eq n
  | .match_ x arms => by
      rw [cost1, cw1]
      exact costArms_eq x arms 0 (armRaw acs x.idx)
  | .call .. => rfl
  | .callIf .. => rfl
  | .dispatch .. => rfl
  | .ret _ => rfl

theorem costW_eq : ∀ ss : List Stmt, costW acs σ ss op = cwList (tabOp acs op) σ ss
  | [] => by rw [costW, cwList]; rfl
  | s :: ss => by
      rw [costW, cwList]
      show cost1 acs σ s op + costW acs σ ss op = _
      rw [cost1_eq s, costW_eq ss]

theorem costArms_eq (x : V) : ∀ (arms : List (List Stmt)) (k : ℕ) (key : Option (List (List ℕ))),
    costArms acs σ x key k arms op =
      cwArms (tabOp acs op) σ x (key.map fun cs => cs.map fun l => l.getD (opIdx op) 0) k arms
  | [], _, _ => by rw [costArms, cwArms]; rfl
  | a :: as, k, key => by
      rw [costArms, cwArms]
      split
      · show (match key with
          | some cs => (nth cs k []).getD (opIdx op) 0
          | none => 0) + costW acs σ a op = _
        rw [costW_eq a]
        cases key with
        | none => rfl
        | some cs => simp only [Option.map_some, Option.getD_some, nth_getD_map]
      · exact costArms_eq x as (k + 1) key
end

end Bridge

/-- **`verify_lean_xmss`'s separately counted arms**, at opcode `op` on a valid instance: at most
the matches' bases plus `136` steps, against a table bounded per arm by a base per match and `B`
per chain step. -/
theorem xmss_costW_le (acs : List (ℕ × List (List ℕ))) (op : Opcode) (A : ℕ → ℕ) (B : ℕ)
    (hA : ∀ q ∈ xMatches, ∀ k < q.2,
      ((tabOp acs op q.1.idx).map fun l => l.getD k 0).getD 0 ≤ A q.1.idx + B * armSteps q.2 k)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node f σ bufs kids).Valid coreProgram rd args rets) (hf : f = "verify_lean_xmss") :
    costW acs σ (coreOf 17).body op ≤ (xMatches.map fun q => A q.1.idx).sum + 136 * B := by
  rw [show (coreOf 17).body = Data.core16.body from rfl, costW_eq]
  exact xmss_cw_valid _ A B hA hv hf

/-! ## At the generated table -/

/-- The per-step charge: one compression per chain step for `blake2s`, none otherwise. -/
def armB : Opcode → ℕ
  | .blake2s => 1
  | _ => 0

/-- A match's base at `op`: its arms' largest count beyond their steps' charge. -/
def armA (op : Opcode) (i : ℕ) : ℕ :=
  match tabOp (nth Data.cplArms 17 []) op i with
  | none => 0
  | some l => ((List.range l.length).map fun k => l.getD k 0 - armB op * armSteps l.length k).foldr max 0

/-- **`verify_lean_xmss`'s separately counted arms, per opcode.** -/
def xmssArmC (op : Opcode) : ℕ := (xMatches.map fun q => armA op q.1.idx).sum + 136 * armB op

theorem xmssArm_hA (op : Opcode) : ∀ q ∈ xMatches, ∀ k < q.2,
    ((tabOp (nth Data.cplArms 17 []) op q.1.idx).map fun l => l.getD k 0).getD 0 ≤
      armA op q.1.idx + armB op * armSteps q.2 k := by
  cases op <;> decide +kernel

theorem xmssArmC_spec : ∀ op σ bufs kids rd args rets,
    (Memory.Tree.node "verify_lean_xmss" σ bufs kids).Valid coreProgram rd args rets →
      costW (nth Data.cplArms 17 []) σ (coreOf 17).body op ≤ xmssArmC op :=
  fun op _ _ _ _ _ _ hv => xmss_costW_le _ op _ _ (xmssArm_hA op) hv rfl

theorem xmssArmC_val : xmssArmC = fun op => [40, 80, 149, 0, 40, 136].getD (opIdx op) 0 := by
  funext op
  cases op <;> decide +kernel

end
end
end LeanVM.Guest.B1.Sig
