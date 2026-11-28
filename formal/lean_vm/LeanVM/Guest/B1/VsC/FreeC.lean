/-
  LeanVM.Guest.B1.VsC.FreeC

  Callees with no witness hint and every computed hint pinned locally complete wherever their
  meaning holds: `eq_prefix_run`, `eq_prefix_chain`, `rs_eq_rows`, `verify_merkle_cap`.
-/

module

public import LeanVM.Guest.Complete.AggFree
public import LeanVM.Guest.Memory.GuestWf
public import LeanVM.Guest.B1.Eq.EqPrefix
public import LeanVM.Guest.B1.Eq.RsRows
public import LeanVM.Guest.B1.Merkle.CapLinksAll
import LeanVM.Guest.CoreRef

/-!
# Free callees, complete from their meanings

Each function below has no witness hint in its subtree and every computed hint pinned locally
(`freeAt`, by the kernel per specialization), and the guest stream proves its relation equivalent to
its meaning. So `callCompletes_free` gives: on every memory where the meaning holds of the call's
words, it completes, popping nothing, every node exact (`FreePost`). The meanings are the guest
stream's (`MeaningEqPrefixRun`, `MeaningEqPrefixChain`, `MeaningRsEqRows`, `MeaningVerifyMerkleCap`):
the caller supplies the words they read, as `Pre`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A free callee completes wherever a meaning implying its relation holds.** -/
theorem free_complete {kd : ℕ} {name : String} (hf : NoWitG name ∧ ExactFreeG name)
    {M : Reader → List E → List E → Prop}
    (hm : ∀ rd args rets, M rd args rets → coreProgram.Rel rd name args rets) (args rets : List E) :
    CallCompletes kd name args rets (fun rd ↦ M rd args rets) FreePost :=
  callCompletes_free coreProgram_wf hf.1 hf.2 fun rd _ h ↦ hm rd args rets h

/-! ## `eq_prefix_run` -/

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_0 : NoWitG (eqPrefixRunNames.getD 0 "") ∧ ExactFreeG (eqPrefixRunNames.getD 0 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L0" idx% «eq_prefix_run__L0» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_1 : NoWitG (eqPrefixRunNames.getD 1 "") ∧ ExactFreeG (eqPrefixRunNames.getD 1 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L1" idx% «eq_prefix_run__L1» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_2 : NoWitG (eqPrefixRunNames.getD 2 "") ∧ ExactFreeG (eqPrefixRunNames.getD 2 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L2" idx% «eq_prefix_run__L2» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_3 : NoWitG (eqPrefixRunNames.getD 3 "") ∧ ExactFreeG (eqPrefixRunNames.getD 3 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L3" idx% «eq_prefix_run__L3» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_4 : NoWitG (eqPrefixRunNames.getD 4 "") ∧ ExactFreeG (eqPrefixRunNames.getD 4 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L4" idx% «eq_prefix_run__L4» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_5 : NoWitG (eqPrefixRunNames.getD 5 "") ∧ ExactFreeG (eqPrefixRunNames.getD 5 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L5" idx% «eq_prefix_run__L5» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_6 : NoWitG (eqPrefixRunNames.getD 6 "") ∧ ExactFreeG (eqPrefixRunNames.getD 6 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L6" idx% «eq_prefix_run__L6» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_7 : NoWitG (eqPrefixRunNames.getD 7 "") ∧ ExactFreeG (eqPrefixRunNames.getD 7 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L7" idx% «eq_prefix_run__L7» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_8 : NoWitG (eqPrefixRunNames.getD 8 "") ∧ ExactFreeG (eqPrefixRunNames.getD 8 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L8" idx% «eq_prefix_run__L8» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_9 : NoWitG (eqPrefixRunNames.getD 9 "") ∧ ExactFreeG (eqPrefixRunNames.getD 9 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L9" idx% «eq_prefix_run__L9» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_10 : NoWitG (eqPrefixRunNames.getD 10 "") ∧ ExactFreeG (eqPrefixRunNames.getD 10 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L10" idx% «eq_prefix_run__L10» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_11 : NoWitG (eqPrefixRunNames.getD 11 "") ∧ ExactFreeG (eqPrefixRunNames.getD 11 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L11" idx% «eq_prefix_run__L11» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_12 : NoWitG (eqPrefixRunNames.getD 12 "") ∧ ExactFreeG (eqPrefixRunNames.getD 12 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L12" idx% «eq_prefix_run__L12» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_13 : NoWitG (eqPrefixRunNames.getD 13 "") ∧ ExactFreeG (eqPrefixRunNames.getD 13 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L13" idx% «eq_prefix_run__L13» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_14 : NoWitG (eqPrefixRunNames.getD 14 "") ∧ ExactFreeG (eqPrefixRunNames.getD 14 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L14" idx% «eq_prefix_run__L14» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_15 : NoWitG (eqPrefixRunNames.getD 15 "") ∧ ExactFreeG (eqPrefixRunNames.getD 15 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L15" idx% «eq_prefix_run__L15» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_16 : NoWitG (eqPrefixRunNames.getD 16 "") ∧ ExactFreeG (eqPrefixRunNames.getD 16 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L16" idx% «eq_prefix_run__L16» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_17 : NoWitG (eqPrefixRunNames.getD 17 "") ∧ ExactFreeG (eqPrefixRunNames.getD 17 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L17" idx% «eq_prefix_run__L17» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_18 : NoWitG (eqPrefixRunNames.getD 18 "") ∧ ExactFreeG (eqPrefixRunNames.getD 18 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L18" idx% «eq_prefix_run__L18» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_19 : NoWitG (eqPrefixRunNames.getD 19 "") ∧ ExactFreeG (eqPrefixRunNames.getD 19 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L19" idx% «eq_prefix_run__L19» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_20 : NoWitG (eqPrefixRunNames.getD 20 "") ∧ ExactFreeG (eqPrefixRunNames.getD 20 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L20" idx% «eq_prefix_run__L20» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_21 : NoWitG (eqPrefixRunNames.getD 21 "") ∧ ExactFreeG (eqPrefixRunNames.getD 21 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L21" idx% «eq_prefix_run__L21» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_22 : NoWitG (eqPrefixRunNames.getD 22 "") ∧ ExactFreeG (eqPrefixRunNames.getD 22 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L22" idx% «eq_prefix_run__L22» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_23 : NoWitG (eqPrefixRunNames.getD 23 "") ∧ ExactFreeG (eqPrefixRunNames.getD 23 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L23" idx% «eq_prefix_run__L23» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_24 : NoWitG (eqPrefixRunNames.getD 24 "") ∧ ExactFreeG (eqPrefixRunNames.getD 24 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L24" idx% «eq_prefix_run__L24» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_25 : NoWitG (eqPrefixRunNames.getD 25 "") ∧ ExactFreeG (eqPrefixRunNames.getD 25 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L25" idx% «eq_prefix_run__L25» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_26 : NoWitG (eqPrefixRunNames.getD 26 "") ∧ ExactFreeG (eqPrefixRunNames.getD 26 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L26" idx% «eq_prefix_run__L26» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_27 : NoWitG (eqPrefixRunNames.getD 27 "") ∧ ExactFreeG (eqPrefixRunNames.getD 27 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L27" idx% «eq_prefix_run__L27» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_28 : NoWitG (eqPrefixRunNames.getD 28 "") ∧ ExactFreeG (eqPrefixRunNames.getD 28 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L28" idx% «eq_prefix_run__L28» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_29 : NoWitG (eqPrefixRunNames.getD 29 "") ∧ ExactFreeG (eqPrefixRunNames.getD 29 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L29" idx% «eq_prefix_run__L29» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_30 : NoWitG (eqPrefixRunNames.getD 30 "") ∧ ExactFreeG (eqPrefixRunNames.getD 30 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L30" idx% «eq_prefix_run__L30» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_31 : NoWitG (eqPrefixRunNames.getD 31 "") ∧ ExactFreeG (eqPrefixRunNames.getD 31 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L31" idx% «eq_prefix_run__L31» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_32 : NoWitG (eqPrefixRunNames.getD 32 "") ∧ ExactFreeG (eqPrefixRunNames.getD 32 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L32" idx% «eq_prefix_run__L32» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_33 : NoWitG (eqPrefixRunNames.getD 33 "") ∧ ExactFreeG (eqPrefixRunNames.getD 33 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L33" idx% «eq_prefix_run__L33» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_34 : NoWitG (eqPrefixRunNames.getD 34 "") ∧ ExactFreeG (eqPrefixRunNames.getD 34 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L34" idx% «eq_prefix_run__L34» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_35 : NoWitG (eqPrefixRunNames.getD 35 "") ∧ ExactFreeG (eqPrefixRunNames.getD 35 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L35" idx% «eq_prefix_run__L35» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_36 : NoWitG (eqPrefixRunNames.getD 36 "") ∧ ExactFreeG (eqPrefixRunNames.getD 36 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L36" idx% «eq_prefix_run__L36» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_37 : NoWitG (eqPrefixRunNames.getD 37 "") ∧ ExactFreeG (eqPrefixRunNames.getD 37 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L37" idx% «eq_prefix_run__L37» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_38 : NoWitG (eqPrefixRunNames.getD 38 "") ∧ ExactFreeG (eqPrefixRunNames.getD 38 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L38" idx% «eq_prefix_run__L38» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_39 : NoWitG (eqPrefixRunNames.getD 39 "") ∧ ExactFreeG (eqPrefixRunNames.getD 39 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L39" idx% «eq_prefix_run__L39» = true)

set_option maxRecDepth 100000 in
theorem eq_prefix_run_free_40 : NoWitG (eqPrefixRunNames.getD 40 "") ∧ ExactFreeG (eqPrefixRunNames.getD 40 "") :=
  free_of (by decide +kernel : freeAt "eq_prefix_run__L40" idx% «eq_prefix_run__L40» = true)

theorem eq_prefix_run_free : ∀ n < 41, NoWitG (eqPrefixRunNames.getD n "") ∧ ExactFreeG (eqPrefixRunNames.getD n "") := by
  intro n hn
  interval_cases n
  exacts [eq_prefix_run_free_0, eq_prefix_run_free_1, eq_prefix_run_free_2, eq_prefix_run_free_3, eq_prefix_run_free_4, eq_prefix_run_free_5, eq_prefix_run_free_6, eq_prefix_run_free_7, eq_prefix_run_free_8, eq_prefix_run_free_9, eq_prefix_run_free_10, eq_prefix_run_free_11, eq_prefix_run_free_12, eq_prefix_run_free_13, eq_prefix_run_free_14, eq_prefix_run_free_15, eq_prefix_run_free_16, eq_prefix_run_free_17, eq_prefix_run_free_18, eq_prefix_run_free_19, eq_prefix_run_free_20, eq_prefix_run_free_21, eq_prefix_run_free_22, eq_prefix_run_free_23, eq_prefix_run_free_24, eq_prefix_run_free_25, eq_prefix_run_free_26, eq_prefix_run_free_27, eq_prefix_run_free_28, eq_prefix_run_free_29, eq_prefix_run_free_30, eq_prefix_run_free_31, eq_prefix_run_free_32, eq_prefix_run_free_33, eq_prefix_run_free_34, eq_prefix_run_free_35, eq_prefix_run_free_36, eq_prefix_run_free_37, eq_prefix_run_free_38, eq_prefix_run_free_39, eq_prefix_run_free_40]

/-- **Every `eq_prefix_run__L{n}` completes**, `n ≤ 40`, where its meaning holds. -/
theorem eq_prefix_run_complete (kd : ℕ) : ∀ n ≤ 40, ∀ args rets : List E,
    CallCompletes kd (eqPrefixRunNames.getD n "") args rets
      (fun rd ↦ MeaningEqPrefixRun n rd args rets) FreePost :=
  fun n hn ↦ free_complete (eq_prefix_run_free n (by omega)) fun rd args rets h ↦
    (eq_prefix_run_holds n hn rd args rets).mpr h

/-! ## `eq_prefix_chain` -/

set_option maxRecDepth 100000 in
theorem eq_prefix_chain_free : NoWitG "eq_prefix_chain" ∧ ExactFreeG "eq_prefix_chain" :=
  free_of (by decide +kernel : freeAt "eq_prefix_chain" idx% «eq_prefix_chain» = true)

/-- **`eq_prefix_chain` completes** where its meaning holds. -/
theorem eq_prefix_chain_complete (kd : ℕ) (args rets : List E) :
    CallCompletes kd "eq_prefix_chain" args rets (fun rd ↦ MeaningEqPrefixChain rd args rets) FreePost :=
  free_complete eq_prefix_chain_free (fun rd args rets h ↦ (eq_prefix_chain_holds rd args rets).mpr h)
    args rets

/-! ## `rs_eq_rows` -/

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_0 : NoWitG (rsEqRowsNames.getD 0 "") ∧ ExactFreeG (rsEqRowsNames.getD 0 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L0" idx% «rs_eq_rows__L0» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_1 : NoWitG (rsEqRowsNames.getD 1 "") ∧ ExactFreeG (rsEqRowsNames.getD 1 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L1" idx% «rs_eq_rows__L1» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_2 : NoWitG (rsEqRowsNames.getD 2 "") ∧ ExactFreeG (rsEqRowsNames.getD 2 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L2" idx% «rs_eq_rows__L2» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_3 : NoWitG (rsEqRowsNames.getD 3 "") ∧ ExactFreeG (rsEqRowsNames.getD 3 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L3" idx% «rs_eq_rows__L3» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_4 : NoWitG (rsEqRowsNames.getD 4 "") ∧ ExactFreeG (rsEqRowsNames.getD 4 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L4" idx% «rs_eq_rows__L4» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_5 : NoWitG (rsEqRowsNames.getD 5 "") ∧ ExactFreeG (rsEqRowsNames.getD 5 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L5" idx% «rs_eq_rows__L5» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_6 : NoWitG (rsEqRowsNames.getD 6 "") ∧ ExactFreeG (rsEqRowsNames.getD 6 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L6" idx% «rs_eq_rows__L6» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_7 : NoWitG (rsEqRowsNames.getD 7 "") ∧ ExactFreeG (rsEqRowsNames.getD 7 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L7" idx% «rs_eq_rows__L7» = true)

set_option maxRecDepth 100000 in
theorem rs_eq_rows_free_8 : NoWitG (rsEqRowsNames.getD 8 "") ∧ ExactFreeG (rsEqRowsNames.getD 8 "") :=
  free_of (by decide +kernel : freeAt "rs_eq_rows__L8" idx% «rs_eq_rows__L8» = true)

theorem rs_eq_rows_free : ∀ n < 9, NoWitG (rsEqRowsNames.getD n "") ∧ ExactFreeG (rsEqRowsNames.getD n "") := by
  intro n hn
  interval_cases n
  exacts [rs_eq_rows_free_0, rs_eq_rows_free_1, rs_eq_rows_free_2, rs_eq_rows_free_3, rs_eq_rows_free_4, rs_eq_rows_free_5, rs_eq_rows_free_6, rs_eq_rows_free_7, rs_eq_rows_free_8]

/-- **Every `rs_eq_rows__L{n}` completes**, `n ≤ 8`, where its meaning holds. -/
theorem rs_eq_rows_complete (kd : ℕ) : ∀ n ≤ 8, ∀ args rets : List E,
    CallCompletes kd (rsEqRowsNames.getD n "") args rets
      (fun rd ↦ MeaningRsEqRows n rd args rets) FreePost :=
  fun n hn ↦ free_complete (rs_eq_rows_free n (by omega)) fun rd args rets h ↦
    (rs_eq_rows_holds n hn rd args rets).mpr h

/-! ## `verify_merkle_cap` -/

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_free_0 : NoWitG ((merkleCapNames.map Prod.fst).getD 0 "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD 0 "") :=
  free_of (by decide +kernel : freeAt "verify_merkle_cap__L2" idx% «verify_merkle_cap__L2» = true)

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_free_1 : NoWitG ((merkleCapNames.map Prod.fst).getD 1 "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD 1 "") :=
  free_of (by decide +kernel : freeAt "verify_merkle_cap__L3" idx% «verify_merkle_cap__L3» = true)

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_free_2 : NoWitG ((merkleCapNames.map Prod.fst).getD 2 "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD 2 "") :=
  free_of (by decide +kernel : freeAt "verify_merkle_cap__L4" idx% «verify_merkle_cap__L4» = true)

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_free_3 : NoWitG ((merkleCapNames.map Prod.fst).getD 3 "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD 3 "") :=
  free_of (by decide +kernel : freeAt "verify_merkle_cap__L5" idx% «verify_merkle_cap__L5» = true)

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_free_4 : NoWitG ((merkleCapNames.map Prod.fst).getD 4 "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD 4 "") :=
  free_of (by decide +kernel : freeAt "verify_merkle_cap__L6" idx% «verify_merkle_cap__L6» = true)

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_free_5 : NoWitG ((merkleCapNames.map Prod.fst).getD 5 "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD 5 "") :=
  free_of (by decide +kernel : freeAt "verify_merkle_cap__L7" idx% «verify_merkle_cap__L7» = true)

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_free_6 : NoWitG ((merkleCapNames.map Prod.fst).getD 6 "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD 6 "") :=
  free_of (by decide +kernel : freeAt "verify_merkle_cap__L8" idx% «verify_merkle_cap__L8» = true)

theorem verify_merkle_cap_free : ∀ n < 7, NoWitG ((merkleCapNames.map Prod.fst).getD n "") ∧ ExactFreeG ((merkleCapNames.map Prod.fst).getD n "") := by
  intro n hn
  interval_cases n
  exacts [verify_merkle_cap_free_0, verify_merkle_cap_free_1, verify_merkle_cap_free_2, verify_merkle_cap_free_3, verify_merkle_cap_free_4, verify_merkle_cap_free_5, verify_merkle_cap_free_6]

/-- **Every `verify_merkle_cap__L{D}` completes**, `2 ≤ D ≤ 8`, where its meaning holds (the
caller's cap and flags, every pair hashing to its parent). -/
theorem verify_merkle_cap_complete (kd : ℕ) : ∀ p ∈ merkleCapNames, ∀ args rets : List E,
    CallCompletes kd p.1 args rets (fun rd ↦ MeaningVerifyMerkleCap p.2 rd args rets) FreePost := by
  intro p hp args rets
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hl : merkleCapNames.length = 7 := rfl
  have hf := verify_merkle_cap_free i (by omega)
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map] at hf
  exact free_complete hf (fun rd args rets h ↦ (verify_merkle_cap_holds _ hp rd args rets).mpr h)
    args rets

end
end LeanVM.Guest.B1.VsC
