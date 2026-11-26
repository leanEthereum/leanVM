/-
  LeanVM.Guest.B1.Main.MainGoalsHL5T

  `main`'s honest children loop, its trees exposed: each iteration's node and its hinted counts
  (`L5Hinted w`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5
public import LeanVM.Guest.B1.Main.MainHonestT
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop4»

/-!
# The children loop's trees

`L5Node k Px Ps Pv Tt`: a `main_loop4` node whose valuation holds child `k`'s hinted counts
(`child_meta` at `v18`, `v19`), its last child (the tail call's tree) satisfying `Tt`.
`L5From ex es m c`: the `m` iterations from child `c`, each `L5Node`. `L5Hinted w`: the honest
run's, child `c`'s counts its statement's lists' lengths.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul exists_of_length_succ
  fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtL completeAtL_tail Returns Kid OutsOk
  CallsMatch RegionsOk outRegion DisjL Within disj_append disj_nil kidsFromIn_of_kidsD regionsOk_of
  within_append bufL bufL_within bufL_disj bufL_region LowDef)

@[expose] public section

/-- `main_loop4`'s events at `σ`: its block's, then its tail call's. -/
noncomputable def l5Evs (σ : Val) : List Ev := (l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)

/-- **`main_loop4`'s calls at `σ`**, in order: the two claim lists' digests, the statement's digest,
`verify_sub`, the tail call (taken when `v59 ≠ 0`). -/
noncomputable def l5CallList (σ : Val) : List Call :=
  [⟨"child_claim_list_digest", [.n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "base"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "child_meta[0]")], [.n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1")], true⟩,
    ⟨"child_claim_list_digest", [.n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "cs_0~2"), .n (val% «main_loop4» "lean_sphincs_slots_g"), .n (val% «main_loop4» "child_meta[1]")], [.n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1")], true⟩,
    ⟨"statement_digest", [.n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1"), .n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1"), .n (val% «main_loop4» "pi_0~2"), .n (val% «main_loop4» "pi_0~3"), .n (val% «main_loop4» "carried")],
      [.n (val% «main_loop4» "pi_0"), .n (val% «main_loop4» "pi_1")], true⟩,
    ⟨"verify_sub", [.n (val% «main_loop4» "pi_0"), .n (val% «main_loop4» "pi_1"), .n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "g_squares"), .n (val% «main_loop4» "s18#5")], [], true⟩,
    ⟨name% «main_loop4», [.n (val% «main_loop4» "s21#4"), .n (val% «main_loop4» "bound"), .n (val% «main_loop4» "written"), .n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "lean_sphincs_slots_g"), .n (val% «main_loop4» "child_carried"), .n (val% «main_loop4» "da_digests"), .n (val% «main_loop4» "seed_0"),
      .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "child_pi"), .n (val% «main_loop4» "g_squares"), .n (val% «main_loop4» "child_fresh")], [], decide (σ (.n (val% «main_loop4» "s21#2")) ≠ 0)⟩]

theorem l5_calls (σ : Val) : calls (l5Evs σ) = l5CallList σ := by
  obtain ⟨-, -, -, hpc⟩ := Main.straight_parts σ _ l5Pre_straight
  rw [l5Evs, hpc, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.callS =
    [(none, "child_claim_list_digest", [.n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "base"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "child_meta[0]")], [.n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1")]),
      (none, "child_claim_list_digest", [.n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "cs_0~2"), .n (val% «main_loop4» "lean_sphincs_slots_g"), .n (val% «main_loop4» "child_meta[1]")], [.n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1")]),
      (none, "statement_digest", [.n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "cx_0"), .n (val% «main_loop4» "cx_1"), .n (val% «main_loop4» "cs_0"), .n (val% «main_loop4» "cs_1"), .n (val% «main_loop4» "pi_0~2"), .n (val% «main_loop4» "pi_0~3"), .n (val% «main_loop4» "carried")],
        [.n (val% «main_loop4» "pi_0"), .n (val% «main_loop4» "pi_1")]),
      (none, "verify_sub", [.n (val% «main_loop4» "pi_0"), .n (val% «main_loop4» "pi_1"), .n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "g_squares"), .n (val% «main_loop4» "s18#5")], []),
      (some (.n (val% «main_loop4» "s21#2")), name% «main_loop4», [.n (val% «main_loop4» "s21#4"), .n (val% «main_loop4» "bound"), .n (val% «main_loop4» "written"), .n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "lean_sphincs_slots_g"),
          .n (val% «main_loop4» "child_carried"),
        .n (val% «main_loop4» "da_digests"), .n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"), .n (val% «main_loop4» "child_pi"), .n (val% «main_loop4» "g_squares"), .n (val% «main_loop4» "child_fresh")], [])] from rfl]
  rfl

/-- The predicates on the block's four calls' trees: `Pv` on `verify_sub`'s. -/
def l5Ts4 (Px Ps Pv : Tree → Prop) : List (Tree → Prop) :=
  [Px, Ps, fun _ => True, Pv]

/-- **The predicates on `main_loop4`'s calls' trees**, aligned with `l5CallList`: `Px`, `Ps` on the
claim lists' digests', `Pv` on `verify_sub`'s, `Tt` on the tail call's, none on the statement
digest's. -/
def l5Ts (Px Ps Pv Tt : Tree → Prop) : List (Tree → Prop) := l5Ts4 Px Ps Pv ++ [Tt]

/-- **A `main_loop4` node for child `k`**: at a valuation `σ` holding `k`'s hinted counts
(`child_meta`'s `g^ex`, `g^es` at `v18`, `v19`), its walk's calls `l5CallList σ`, its children
satisfying `KidsT (l5CallList σ) (l5Ts Px Ps Pv Tt)`. -/
def L5Node (k : KidH) (Px Ps Pv Tt : Tree → Prop) (t : Tree) : Prop :=
  ∃ σ bufs ks, t = .node name% «main_loop4» σ bufs ks ∧ σ (.n (val% «main_loop4» "child_meta[0]")) = gen ^ k.ex ∧
    σ (.n (val% «main_loop4» "child_meta[1]")) = gen ^ k.es ∧ calls (l5Evs σ) = l5CallList σ ∧ KidsT (l5CallList σ) (l5Ts Px Ps Pv Tt) ks

/-- **The `m` iterations from child `c`**: each a `main_loop4` node at a valuation holding its
child's hinted counts (`ex c`, `es c`), its walk's calls `l5CallList σ`, its claim lists' and
`verify_sub` calls' trees satisfying `Pxs c`, `Pss c`, `Pvs c` and its tail call's the next
iteration's. -/
def L5From (ex es : ℕ → ℕ) (Pxs Pss Pvs : ℕ → Tree → Prop) : ℕ → ℕ → Tree → Prop
  | 0, _, _ => False
  | m + 1, c, t => ∃ σ bufs ks, t = .node name% «main_loop4» σ bufs ks ∧ σ (.n (val% «main_loop4» "child_meta[0]")) = gen ^ ex c ∧
      σ (.n (val% «main_loop4» "child_meta[1]")) = gen ^ es c ∧ calls (l5Evs σ) = l5CallList σ ∧
      KidsT (l5CallList σ) (l5Ts (Pxs c) (Pss c) (Pvs c) (L5From ex es Pxs Pss Pvs m (c + 1))) ks

/-- **The honest children loop's trees**: iteration `c < nc` is a `main_loop4` node whose hinted
counts are child `c`'s statement's lists' lengths, in the exponent (`g^|xmss|`, `g^|sphincs|`),
its calls' trees satisfying `Pxs c`, `Pss c`, `Pvs c`, its tail call's the next iteration's. -/
def L5Hinted (w : NodeWitness) (Pxs Pss Pvs : ℕ → Tree → Prop) : Tree → Prop :=
  L5From (hEx w) (hEs w) Pxs Pss Pvs w.children.length 0

variable (fs : String → ℕ) (cert : String → V → ℕ)

variable {fs cert}

end
end LeanVM.Guest.B1.Main
