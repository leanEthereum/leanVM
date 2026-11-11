/-
  LeanVM.Guest.B1.Digest.Interface

  The interface of B1's digest functions (the statement's digest, the claim lists' digests, the
  DA root list's digest, a DA slot's coverage): what each computes, and the statements that its
  core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Sponge
public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier

/-!
# The digests: meanings (TRIAGE G #86-89, #94, #95)

For each function of the guest (`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM
`40f877dc`, G below) its meaning `Meaning…` on its argument and return words, and two
statements on its core IR relation (`coreProgram.Rel`): `…_sound_Spec`, the relation gives the
meaning, and `…_complete_Spec`, the meaning (with what memory an honest run holds) gives the
relation. A `…_Spec` is a definition (a `Prop`); its proof is the theorem `…_holds` of the
family's modules.

| function | G | core | meaning |
| --- | --- | --- | --- |
| `statement_digest` | 3934-3973 | `core21` | Keccak-256 of the eight header cells and the 24 deferred cells, three limbs each (`statementDigest`, N:197) |
| `list_split` | 3982-3997 | `core22` | `n = 136 · bigs + 17 · groups + rest`, `bigs < 2^20`, `groups < 8`, `rest < 17` |
| `claim_list_digest` | 4000-4043 | `core23` | Keccak-256 of the `4n` canonical cells of the list (`claimListDigest`, `claimListDigest`, N:172-180) |
| `child_claim_list_digest` | 4062-4197 | `core24` | the same over cells read at hinted slots of this node's table, each slot marked in the coverage table (by hinted indices, `child_claim_list_any`, or by hinted gaps, `child_claim_list_mono`) |

**Cells and bytes.** A cell holds sixteen bytes, limbs `0` and `1` (`Value.Keccak.cellsBytes`;
the `KECCAK` instruction makes every cell it reads canonical, `AllCanonical`). A digest's two
cells are `digestHalves` (`digestCells`); a deferred cell is a full field element, hashed as its
three limbs (`E.toBytes`, `pack_pair`).

**The memory.** A range check (`assert log x < log b`) is an exact relation on the memory read
(`RangeChecked`); on a memory image of `2^κ` words, `16 ≤ κ ≤ 32` (`MemOk`, as every valid
execution's is), it says `x = g^e` with `e` below the bound's log (`BelowLog`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Shared vocabulary -/

/-- The reader is a memory image of `2^κ` words, `1 ≤ κ ≤ 32`, as every valid execution's is. -/
def MemOk (rd : Reader) : Prop := ∃ κ, 1 ≤ κ ∧ κ ≤ 32 ∧ ∃ L : MemoryImage κ, rd = L.read

/-- A digest's two cells (`digestHalves`), as a list. -/
def digestCells (d : Digest) : List E := [(digestHalves d).1, (digestHalves d).2]

/-- `x = g^e` with `e` below the log of the bound `b`, as a range check against `b · g⁻¹`
establishes on a memory image of at most `2^32` words: `b = g^(e + e' + 1)`, `e, e' < 2^32`. -/
def BelowLog (b : E) (e : ℕ) : Prop := e < 2 ^ 32 ∧ ∃ e' < 2 ^ 32, b = gen ^ (e + e' + 1)

/-- `g⁻¹`, the word a runtime range bound is multiplied by (`assert log x < log b`). -/
abbrev ginvW : E := word 9223372036854775821 0 0

/-! ## `statement_digest` (G:4058-4097, TRIAGE #86) -/

/-- `DEFER_STMT_CELLS`: the cells of a statement's deferred claim, `BYTECODE_VARS = 23`
coordinates and the value. -/
abbrev deferStmtCells : ℕ := 24

/-- The bytes `statement_digest` hashes: the header cells (the seed, the two claim lists' digests,
the DA digest), then the deferred cells, three limbs each. `24` is even: no zero partner. -/
def stmtBytes (hdr defer : List E) : List UInt8 := cellsBytes hdr ++ defer.flatMap E.toBytes

/-- **`statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer)`**: the 24
deferred cells at `defer`; the eight header cells are canonical (the `KECCAK` reads them), and the
function returns the two cells of the Keccak-256 digest of the header cells and the deferred
cells' limbs. -/
def MeaningStatementDigest (rd : Reader) : List E → List E → Prop
  | [s0, s1, x0, x1, y0, y1, a0, a1, dp], rets => ∃ cells : List E,
      cells.length = deferStmtCells ∧ ReadsAt rd dp cells ∧
      AllCanonical [s0, s1, x0, x1, y0, y1, a0, a1] ∧
      rets = digestCells (keccak256 (stmtBytes [s0, s1, x0, x1, y0, y1, a0, a1] cells))
  | _, _ => False

/-- `statement_digest`'s core IR gives its meaning. -/
def statement_digest_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "statement_digest" args rets → MeaningStatementDigest rd args rets

/-- `statement_digest`'s meaning gives its core IR. -/
def statement_digest_complete_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    MeaningStatementDigest rd args rets → coreProgram.Rel rd "statement_digest" args rets

/-! ## `list_split` (G:4106-4121, TRIAGE #87) -/

/-- `CLAIM_GROUP`: claims hashed a loop frame of a list's rest. -/
abbrev claimGroup : ℕ := 17

/-- `BIG_GROUPS`: groups of a big frame. -/
abbrev bigGroups : ℕ := 8

/-- `CLAIM_BIG = CLAIM_GROUP · BIG_GROUPS`: claims hashed a loop frame of a list's bulk. -/
abbrev claimBig : ℕ := 136

/-- A bound on an honest count's big frames in `list_split`, above the `2^23 / 136` of a count
below the coverage table's `2^23` (`GuestLimits.coverageSlotsBelow2Pow23`): `assert_gpow` accepts
`g^a` in any memory of at least `2^20` cells, which these completeness proofs assume (`20 ≤ κ`). -/
abbrev bigFramesCap : ℕ := 1048576

/-- **`list_split(n_g)`**: `n_g = g^(136 a + 17 b + c)` with `a < 2^32` (`assert_gpow`: `g^a` an
address of the memory), `b < 8`, `c < 17`, and the function returns `g^a`, `g^b`, `g^c`. -/
def MeaningListSplit : List E → List E → Prop
  | [ng], rets => ∃ a < 2 ^ 32, ∃ b < bigGroups, ∃ c < claimGroup,
      ng = gen ^ (claimBig * a + claimGroup * b + c) ∧ rets = [gen ^ a, gen ^ b, gen ^ c]
  | _, _ => False

/-- **`list_split(n_g)` on an honest count**: as `MeaningListSplit`, `a < 2^20` (`bigFramesCap`, below
the `2^20` cells of memory these proofs assume). -/
def MeaningListSplitC : List E → List E → Prop
  | [ng], rets => ∃ a < bigFramesCap, ∃ b < bigGroups, ∃ c < claimGroup,
      ng = gen ^ (claimBig * a + claimGroup * b + c) ∧ rets = [gen ^ a, gen ^ b, gen ^ c]
  | _, _ => False

/-- `list_split`'s core IR gives its meaning, on a memory image. -/
def list_split_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "list_split" args rets → MeaningListSplit args rets

/-- `list_split`'s meaning gives its core IR, on a memory defined below `2^20`. -/
def list_split_complete_Spec : Prop :=
  ∀ (rd : Reader), (∀ i < 2 ^ 20, (rd (addressOfIndex i)).isSome) → ∀ (args rets : List E),
    MeaningListSplitC args rets → coreProgram.Rel rd "list_split" args rets

/-! ## `claim_list_digest` (G:4124-4167, TRIAGE #88) -/

/-- The `4n` cells of `n` claims at `entries` are canonical, and `rets` is the two cells of their
Keccak-256 digest (an empty list: the empty string's). -/
def ClaimListOut (rd : Reader) (entries : E) (n : ℕ) (rets : List E) : Prop :=
  ∃ cells : List E, cells.length = 4 * n ∧ ReadsAt rd entries cells ∧ AllCanonical cells ∧
    rets = digestCells (keccak256 (cellsBytes cells))

/-- **`claim_list_digest(entries, n_g)`**: `n_g = g^n` for a count `n < 136 · 2^32`, and the
function returns the digest of the `n` claims at `entries` (`ClaimListOut`). -/
def MeaningClaimListDigest (rd : Reader) : List E → List E → Prop
  | [entries, ng], rets => ∃ n < claimBig * 2 ^ 32, ng = gen ^ n ∧ ClaimListOut rd entries n rets
  | _, _ => False

/-- `claim_list_digest`'s core IR gives its meaning, on a memory image. -/
def claim_list_digest_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "claim_list_digest" args rets → MeaningClaimListDigest rd args rets

/-! ## `child_claim_list_digest` (G:4186-4321, TRIAGE #89) -/

/-- The slot `e` lies below the log of the region's size `b`: `b = g^L`, `e < L < 2^33`. -/
def SlotBelow (b : E) (e : ℕ) : Prop := ∃ L < 2 ^ 33, b = gen ^ L ∧ e < L

/-- **A child's claim list rebuilt from this node's table**: claim `j < n` sits at slot `o j` of
the table at `entries` (its four cells at `entries · g^(4 o j)`), the slot below the log of
`limit` and marked in the region's coverage slot `region · g^(o j)`. The walk by hinted indices
(`child_claim_list_any`) marks claim `j` with `base · g^j`; the walk by hinted gaps
(`child_claim_list_mono`, `mono`) marks every claim with `base`, its slots strictly increasing.
The `4n` cells are canonical and `rets` is the two cells of their Keccak-256 digest. -/
def ChildListOut (rd : Reader) (entries region base limit : E) (n : ℕ) (rets : List E) : Prop :=
  ∃ (mono : Bool) (o : ℕ → ℕ) (cells : List E), cells.length = 4 * n ∧ AllCanonical cells ∧
    (mono = true → ∀ i j, i < j → j < n → o i < o j) ∧
    (∀ j < n, SlotBelow limit (o j) ∧
      LoadHolds rd region (o j) (base * gen ^ (if mono then 0 else j)) ∧
      ∀ c < 4, LoadHolds rd entries (4 * o j + c) (cells.getD (4 * j + c) 0)) ∧
    rets = digestCells (keccak256 (cellsBytes cells))

/-- **`child_claim_list_digest(entries, region, base, limit_g, n_g)`**: at `n_g = g^n`,
`n < 2^32` (the caller's `assert_gpow`), the function returns the digest of the claims rebuilt at
hinted slots (`ChildListOut`), by either walk (the prover's hint `child_mono`). -/
def MeaningChildClaimListDigest (rd : Reader) : List E → List E → Prop
  | [entries, region, base, limit, ng], rets => ∀ n < 2 ^ 32,
      ng = gen ^ n → ChildListOut rd entries region base limit n rets
  | _, _ => False

/-- `child_claim_list_digest`'s core IR gives its meaning, on a memory image. -/
def child_claim_list_digest_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "child_claim_list_digest" args rets →
      MeaningChildClaimListDigest rd args rets

/-! ## The functions, found -/

theorem find_statement_digest : coreProgram.find? "statement_digest" = some Data.core21 :=
  Program.find?_of_indexOf? (j := 21) (by decide +kernel) rfl

theorem find_list_split : coreProgram.find? "list_split" = some Data.core22 :=
  Program.find?_of_indexOf? (j := 22) (by decide +kernel) rfl

theorem find_claim_list_digest : coreProgram.find? "claim_list_digest" = some Data.core23 :=
  Program.find?_of_indexOf? (j := 23) (by decide +kernel) rfl

theorem find_child_claim_list_digest :
    coreProgram.find? "child_claim_list_digest" = some Data.core24 :=
  Program.find?_of_indexOf? (j := 24) (by decide +kernel) rfl

end
end LeanVM.Guest.B1.Digest
