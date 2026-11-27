/-
  LeanVM.Guest.B1.Main.KidsAt

  `main`'s children loop `main_loop4` toward the uniform placed form: a child's honest data, what
  it needs of the caller's words, and the loop's body.
-/

module

public import LeanVM.Guest.B1.Main.KidBlockC
public import LeanVM.Guest.B1.Main.KidsT
public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop4»
import LeanVM.Guest.StmtsAppend

/-!
# The children, placed

`KidH`: a child's honest data (its counts, its base `written[c]`, its two claim lists' digests, its
DA digest, its deferred claim's cells), and what it determines: the statement's digest `pi`.
`KidOkC`: what child `c` needs of the caller's words `Lin` (the running counts, the statement's
digest in `child_pi_table`, the DA digest in `da_digests`, the deferred cells) and of its callees
not lifted here (the two `child_claim_list_digest` calls and `verify_sub`, as `CompleteAtD`
hypotheses). `l5Pre_straight`, `l5Body_split`, `l5_loop`: `main_loop4`'s body, a straight
iteration and its tail call.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul exists_of_length_succ fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtL completeAtL_tail Returns Kid OutsOk CallsMatch
  RegionsOk outRegion DisjL Within disj_append disj_nil kidsFromIn_of_kidsD regionsOk_of within_append
  LowDef)

@[expose] public section

/-! ## A child's honest data -/

/-- **A child's honest data.** -/
structure KidH where
  ex : ℕ
  es : ℕ
  base : E
  cx : E × E
  cs : E × E
  da : E × E
  defer : List E

namespace KidH

/-- The child's statement's digest. -/
def pi (k : KidH) (s0 s1 : E) : E × E :=
  digestHalves (keccak256
    (stmtBytes [s0, s1, k.cx.1, k.cx.2, k.cs.1, k.cs.2, k.da.1, k.da.2] k.defer))

end KidH

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **What child `c` needs**: its counts' bounds, the caller's words (the
running counts at `g^W`, the DA digest at `g^(D + 2c)`, the statement's digest at `g^(Pi + 2c)`,
the deferred cells at `g^(Cr + 24c)`) and their addresses in `Lin`, and its callees
`child_claim_list_digest` (twice) and `verify_sub` complete reading `Lin`. -/
structure KidOkC (Lin : Layout) (W D Pi Cr : ℕ) (lxt cover lxs lst spc lss s0 s1 gsq cfresh : E)
    (c : ℕ) (k : KidH) : Prop where
  ex_lt : k.ex < 2 ^ 23
  es_lt : k.es < 2 ^ 23
  defer_len : k.defer.length = 24
  mem : ∀ rd, MemL rd Lin →
    LoadHolds rd (gen ^ W) c k.base ∧
    LoadHolds rd (gen ^ W) (c + 1) (k.base * (gen ^ k.ex * gen ^ k.es)) ∧
    LoadHolds rd (gen ^ D) (2 * c) k.da.1 ∧
    LoadHolds rd (gen ^ D) (2 * c + 1) k.da.2 ∧
    LoadHolds rd (gen ^ Pi) (2 * c) (k.pi s0 s1).1 ∧
    LoadHolds rd (gen ^ Pi) (2 * c + 1) (k.pi s0 s1).2 ∧
    ReadsAt rd (gen ^ (Cr + 24 * c)) k.defer
  reg : RegionL Lin (W + c) ∧ RegionL Lin (W + c + 1) ∧ RegionL Lin (D + 2 * c) ∧
    RegionL Lin (D + 2 * c + 1) ∧ RegionL Lin (Pi + 2 * c) ∧ RegionL Lin (Pi + 2 * c + 1)
  hX : CompleteAtD fs cert 23 "child_claim_list_digest" Lin [lxt, cover, k.base, lxs, gen ^ k.ex]
    (Returns [k.cx.1, k.cx.2])
  hS : CompleteAtD fs cert 23 "child_claim_list_digest" Lin
    [lst, spc, k.base * gen ^ k.ex, lss, gen ^ k.es] (Returns [k.cs.1, k.cs.2])
  hV : CompleteAtD fs cert 20 "verify_sub" Lin
    [(k.pi s0 s1).1, (k.pi s0 s1).2, s0, s1, gsq, cfresh * gen ^ (24 * c)] (Returns [])

theorem gen_sq' (j : ℕ) : gen ^ j * gen ^ j = gen ^ (2 * j) := by rw [← pow_add, two_mul]

/-- A statement of `main_loop4`'s block: an atom or a call. -/
def l5Kind : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | _ => false

set_option maxRecDepth 100000 in
theorem l5_kinds : l5Pre.all l5Kind = true := by decide +kernel

theorem l5Pre_straight : (l5Pre ++ [l5Tail]).all Main.Stmt.straight = true := by decide

theorem l5Body_split : l5Body = (l5Pre ++ [l5Tail]) ⧺ [.ret []] := by
  simp [l5Body]

theorem find_l5 : coreProgram.find? name% «main_loop4» = some (coreProgram.getD idx% «main_loop4»
    default) :=
  find_of_idx l5_idx

theorem l5_loop : coreProgram.loop name% «main_loop4» = true := by
  rw [Program.loop_of_find? find_l5, Fn.loop, l5_body, fn_name_of_find find_l5]
  simp [l5Tail]

end
end LeanVM.Guest.B1.Main
