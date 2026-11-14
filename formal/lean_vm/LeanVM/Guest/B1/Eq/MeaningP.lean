/-
  LeanVM.Guest.B1.Eq.MeaningP

  The interface of B1's multilinear primitives: what each computes, and the statement that its
  core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# Multilinear primitives: meanings (TRIAGE G #25-29)

For each function of the guest (`lean_ethereum.py`, G below) its meaning
on its argument and return words, and `…_Spec`, the statement that its core IR relation is that
meaning (proved as `…_holds`). The inline helpers `eqtree`, `eqtree_frame`
 have no core function of their own; their expansions are templates of
`B1/Eq/Templates.lean`.

| function | meaning |
| --- | --- |
| `eq_prefix_run__L{n}` | `chain[j] = seed · Π_{k<j} (a_k + b1_k)`, `j ≤ n` |
| `eq_prefix_chain` | `count = g^n`, `n < 41`, and `eq_prefix_run__L{n}` |
| `plus_one_run__L{n}` | `out[k] = 1 + src[k]`, `k < n` |
| `rs_eq_rows__L{n}` | one row of `ringWeight`'s products over `n ≤ 8` coordinates |
| `rs_eq_run` | the rows of `ringWeight`'s products, eight coordinates a row |
| `fold_final_msg__L{n}` | `multilinearEval` |

With `b1_k = 1 + b_k`, `a_k + b1_k` is the factor `1 + a_k + b_k` of `eqEval`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `eq_prefix_run`, `eq_prefix_chain` (TRIAGE #25, #26) -/

/-- The prefix product `seed · Π_{k<j} (as[k] + bs[k])`, left to right. -/
def prefixProd (seed : E) (as bs : List E) (j : ℕ) : E :=
  (List.zipWith (· + ·) (as.take j) (bs.take j)).foldl (· * ·) seed

/-- The words at `a`, `b1` below `n` and the prefix products at `chain`, `j ≤ n`. -/
def EqPrefix (rd : Reader) (chain seed a b1 : E) (n : ℕ) : Prop :=
  ∃ as bs : List E, as.length = n ∧ bs.length = n ∧ ReadsAt rd a as ∧ ReadsAt rd b1 bs ∧
    ∀ j ≤ n, LoadHolds rd chain j (prefixProd seed as bs j)

/-- **`eq_prefix_run(chain, seed, a, b1, n)`**: the prefix products; it returns `0`. -/
def MeaningEqPrefixRun (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [chain, seed, a, b1], rets => EqPrefix rd chain seed a b1 n ∧ rets = [0]
  | _, _ => False

/-- The specializations' names, `eq_prefix_run__L{n}`, `n ≤ 40` (`eq_prefix_chain`'s dispatch
list; a name built by `++ toString` does not reduce in a `module`'s kernel). -/
def eqPrefixRunNames : List String :=
    ["eq_prefix_run__L0", "eq_prefix_run__L1", "eq_prefix_run__L2", "eq_prefix_run__L3",
      "eq_prefix_run__L4", "eq_prefix_run__L5", "eq_prefix_run__L6", "eq_prefix_run__L7",
      "eq_prefix_run__L8", "eq_prefix_run__L9", "eq_prefix_run__L10", "eq_prefix_run__L11",
      "eq_prefix_run__L12", "eq_prefix_run__L13", "eq_prefix_run__L14", "eq_prefix_run__L15",
      "eq_prefix_run__L16", "eq_prefix_run__L17", "eq_prefix_run__L18", "eq_prefix_run__L19",
      "eq_prefix_run__L20", "eq_prefix_run__L21", "eq_prefix_run__L22", "eq_prefix_run__L23",
      "eq_prefix_run__L24", "eq_prefix_run__L25", "eq_prefix_run__L26", "eq_prefix_run__L27",
      "eq_prefix_run__L28", "eq_prefix_run__L29", "eq_prefix_run__L30", "eq_prefix_run__L31",
      "eq_prefix_run__L32", "eq_prefix_run__L33", "eq_prefix_run__L34", "eq_prefix_run__L35",
      "eq_prefix_run__L36", "eq_prefix_run__L37", "eq_prefix_run__L38", "eq_prefix_run__L39",
      "eq_prefix_run__L40"]

/-- `eq_prefix_run__L{n}`'s core IR is its meaning, `n ≤ 40`. -/
def eq_prefix_run_SpecP (P : Program) : Prop :=
  ∀ n ≤ 40, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (eqPrefixRunNames.getD n "") args rets ↔
      MeaningEqPrefixRun n rd args rets

/-- **`eq_prefix_chain(chain, seed, a, b1, count_g)`**: `count_g = g^n` with `n < 41`
(`assert log(count_g) < EQ_CHAIN_ARMS`, its range check's memory facts kept), and the prefix
products up to `n`. -/
def MeaningEqPrefixChain (rd : Reader) : List E → List E → Prop
  | [chain, seed, a, b1, cg], rets =>
      rets = [] ∧ RangeChecked rd cg (gen ^ 40) ∧ ∃ n < 41, cg = gen ^ n ∧ EqPrefix rd chain seed a b1 n
  | _, _ => False

/-- `eq_prefix_chain`'s core IR is its meaning. -/
def eq_prefix_chain_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "eq_prefix_chain" args rets ↔ MeaningEqPrefixChain rd args rets

/-! ## `plus_one_run` (TRIAGE #27) -/

/-- **`plus_one_run(out, src, n)`**: `out[k] = 1 + src[k]`, `k < n`; it returns `0`. -/
def MeaningPlusOneRun (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [out, src], rets => (∃ xs : List E, xs.length = n ∧ ReadsAt rd src xs ∧
      ReadsAt rd out (xs.map (1 + ·))) ∧ rets = [0]
  | _, _ => False

/-- The specializations' names, `plus_one_run__L{n}`, `n ≤ 33`. -/
def plusOneRunNames : List String :=
    ["plus_one_run__L0", "plus_one_run__L1", "plus_one_run__L2", "plus_one_run__L3",
      "plus_one_run__L4", "plus_one_run__L5", "plus_one_run__L6", "plus_one_run__L7",
      "plus_one_run__L8", "plus_one_run__L9", "plus_one_run__L10", "plus_one_run__L11",
      "plus_one_run__L12", "plus_one_run__L13", "plus_one_run__L14", "plus_one_run__L15",
      "plus_one_run__L16", "plus_one_run__L17", "plus_one_run__L18", "plus_one_run__L19",
      "plus_one_run__L20", "plus_one_run__L21", "plus_one_run__L22", "plus_one_run__L23",
      "plus_one_run__L24", "plus_one_run__L25", "plus_one_run__L26", "plus_one_run__L27",
      "plus_one_run__L28", "plus_one_run__L29", "plus_one_run__L30", "plus_one_run__L31",
      "plus_one_run__L32", "plus_one_run__L33"]

/-- `plus_one_run__L{n}`'s core IR is its meaning, `n ≤ 33`. -/
def plus_one_run_SpecP (P : Program) : Prop :=
  ∀ n ≤ 33, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (plusOneRunNames.getD n "") args rets ↔
      MeaningPlusOneRun n rd args rets

/-! ## `rs_eq_run` (TRIAGE #28) -/

/-- Row entry `k` after the coordinates `i < j`: `c · Π_{i<j} (z_i^(2^k) + p_i)`, left to right
(`p_i = 1 + r'_i`, the factor `1 + r_i^(2^k) + r'_i` of `ringWeight`). -/
def ringRow (c : E) (zs ps : List E) (k : ℕ) : E :=
  (List.zipWith (fun z p ↦ z ^ 2 ^ k + p) zs ps).foldl (· * ·) c

/-- **`rs_eq_rows(row, zs, ps, n)`**: at `n = 0` it
returns `row`; otherwise the `n` words `zs`, `ps` at `zs`, `ps` and the 64 words `c` at `row`; the
next row, from `row·g^64`, holds `ringRow c[k] zs ps k` at `k < 64`, and it returns `row·g^64`. -/
def MeaningRsEqRows (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [row, z, p], rets => (n = 0 ∧ rets = [row]) ∨
      (0 < n ∧ ∃ zs ps c : List E, zs.length = n ∧ ps.length = n ∧ c.length = 64 ∧
        ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd row c ∧
        (∀ k < 64, LoadHolds rd row (64 + k) (ringRow (c.getD k 0) zs ps k)) ∧
        rets = [row * gen ^ 64])
  | _, _ => False

/-- The specializations' names, `rs_eq_rows__L{n}`, `n ≤ 8` (`RS_CHUNK = 8`). -/
def rsEqRowsNames : List String :=
  ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
    "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7", "rs_eq_rows__L8"]

/-- `rs_eq_rows__L{n}`'s core IR is its meaning, `n ≤ 8`. -/
def rs_eq_rows_SpecP (P : Program) : Prop :=
  ∀ n ≤ 8, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (rsEqRowsNames.getD n "") args rets ↔ MeaningRsEqRows n rd args rets

/-- **`rs_eq_run(chain, z_vals, point1, count_g)`**:
`count_g = g^count`, `count < 64`; the words `zs`, `ps` at `z_vals`, `point1` below `count`; row
`h` of `chain` (64 words from `chain·g^(64·h)`), `1 ≤ h ≤ ⌈count/8⌉`, is row `0` times the
products over the first `min(8h, count)` coordinates (`RS_CHUNK = 8` coordinates a row, the
last row the remainder's); it returns the last row, `chain·g^(64·⌈count/8⌉)`. -/
def MeaningRsEqRun (rd : Reader) : List E → List E → Prop
  | [chain, z, p1, cg], rets =>
      ∃ count < 64, cg = gen ^ count ∧ ∃ zs ps c : List E, zs.length = count ∧
        ps.length = count ∧ c.length = 64 ∧ ReadsAt rd z zs ∧ ReadsAt rd p1 ps ∧
        (0 < count → ReadsAt rd chain c) ∧
        (∀ h, 1 ≤ h → h ≤ (count + 7) / 8 → ∀ k < 64,
          LoadHolds rd chain (64 * h + k)
            (ringRow (c.getD k 0) (zs.take (min (8 * h) count)) (ps.take (min (8 * h) count)) k)) ∧
        rets = [chain * gen ^ (64 * ((count + 7) / 8))]
  | _, _ => False

/-- `rs_eq_run`'s core IR is its meaning. -/
def rs_eq_run_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "rs_eq_run" args rets ↔ MeaningRsEqRun rd args rets

/-! ## `fold_final_msg` (TRIAGE #29) -/

/-- **`fold_final_msg(msg, point, n)`**: the `2^n` words at `msg` folded at the `n` words at
`point`: `multilinearEval`. -/
def MeaningFoldFinalMsg (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [msg, point], rets => ∃ m ps : List E, m.length = 2 ^ n ∧ ps.length = n ∧ ReadsAt rd msg m ∧
      ReadsAt rd point ps ∧ rets = [multilinearEval m ps]
  | _, _ => False

/-- The specializations' names, `fold_final_msg__L{n}`, `2 ≤ n ≤ 5`. -/
def foldFinalMsgNames : List (String × ℕ) :=
  [("fold_final_msg__L2", 2), ("fold_final_msg__L3", 3), ("fold_final_msg__L4", 4),
    ("fold_final_msg__L5", 5)]

/-- `fold_final_msg__L{n}`'s core IR is its meaning, `2 ≤ n ≤ 5`. -/
def fold_final_msg_SpecP (P : Program) : Prop :=
  ∀ p ∈ foldFinalMsgNames, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd p.1 args rets ↔ MeaningFoldFinalMsg p.2 rd args rets

end
end LeanVM.Guest.B1
