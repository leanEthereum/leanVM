/-
  LeanVM.Guest.B1.VsC.EqChainA

  `eq_prefix_chain` completes placed, its dispatch's `eq_prefix_run__L{n}` a leaf.
-/

module

public import LeanVM.Guest.B1.VsC.FreeC
public import LeanVM.Guest.B1.VsC.SqueezeFwd
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Complete.TransferA
public import LeanVM.Guest.Complete.LeafA
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«eq_prefix_chain»
import LeanVM.Guest.Data.ValNames.«eq_prefix_run__L»

/-!
# `eq_prefix_chain`, placed

`eq_prefix_chain(chain, seed, a, b1, g^n)`, `n ≤ 40`, has no words of its own: it range-checks
`n < 41` and dispatches `eq_prefix_run__L{n}`, a straight leaf storing the prefix products into
`chain[0 ..= n]` from `a[0 .. n)`, `b1[0 .. n)`. Its layout-free completeness (`callCompletes0_free`,
the guest stream's `eq_prefix_chain_holds`) is placed by `callAtA_of_callCompletes0`, from the
shape every valid tree has (`epc_shape`): block its frame, its leaf at the aligned base past it
(`epcEnd`), its loads the leaf's, in the caller's three arrays.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem epr_fn_0 : coreProgram.find? (eqPrefixRunNames.getD 0 "") = some fn% «eq_prefix_run__L0» ∧
    (fn% «eq_prefix_run__L0»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L0»).body = epBody 0 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L0») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_1 : coreProgram.find? (eqPrefixRunNames.getD 1 "") = some fn% «eq_prefix_run__L1» ∧
    (fn% «eq_prefix_run__L1»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L1»).body = epBody 1 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L1») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_2 : coreProgram.find? (eqPrefixRunNames.getD 2 "") = some fn% «eq_prefix_run__L2» ∧
    (fn% «eq_prefix_run__L2»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L2»).body = epBody 2 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L2») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_3 : coreProgram.find? (eqPrefixRunNames.getD 3 "") = some fn% «eq_prefix_run__L3» ∧
    (fn% «eq_prefix_run__L3»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L3»).body = epBody 3 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L3») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_4 : coreProgram.find? (eqPrefixRunNames.getD 4 "") = some fn% «eq_prefix_run__L4» ∧
    (fn% «eq_prefix_run__L4»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L4»).body = epBody 4 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L4») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_5 : coreProgram.find? (eqPrefixRunNames.getD 5 "") = some fn% «eq_prefix_run__L5» ∧
    (fn% «eq_prefix_run__L5»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L5»).body = epBody 5 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L5») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_6 : coreProgram.find? (eqPrefixRunNames.getD 6 "") = some fn% «eq_prefix_run__L6» ∧
    (fn% «eq_prefix_run__L6»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L6»).body = epBody 6 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L6») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_7 : coreProgram.find? (eqPrefixRunNames.getD 7 "") = some fn% «eq_prefix_run__L7» ∧
    (fn% «eq_prefix_run__L7»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L7»).body = epBody 7 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L7») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_8 : coreProgram.find? (eqPrefixRunNames.getD 8 "") = some fn% «eq_prefix_run__L8» ∧
    (fn% «eq_prefix_run__L8»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L8»).body = epBody 8 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L8») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_9 : coreProgram.find? (eqPrefixRunNames.getD 9 "") = some fn% «eq_prefix_run__L9» ∧
    (fn% «eq_prefix_run__L9»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L9»).body = epBody 9 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L9») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_10 : coreProgram.find? (eqPrefixRunNames.getD 10 "") = some fn% «eq_prefix_run__L10» ∧
    (fn% «eq_prefix_run__L10»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L10»).body = epBody 10 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L10») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_11 : coreProgram.find? (eqPrefixRunNames.getD 11 "") = some fn% «eq_prefix_run__L11» ∧
    (fn% «eq_prefix_run__L11»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L11»).body = epBody 11 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L11») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_12 : coreProgram.find? (eqPrefixRunNames.getD 12 "") = some fn% «eq_prefix_run__L12» ∧
    (fn% «eq_prefix_run__L12»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L12»).body = epBody 12 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L12») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_13 : coreProgram.find? (eqPrefixRunNames.getD 13 "") = some fn% «eq_prefix_run__L13» ∧
    (fn% «eq_prefix_run__L13»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L13»).body = epBody 13 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L13») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_14 : coreProgram.find? (eqPrefixRunNames.getD 14 "") = some fn% «eq_prefix_run__L14» ∧
    (fn% «eq_prefix_run__L14»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L14»).body = epBody 14 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L14») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_15 : coreProgram.find? (eqPrefixRunNames.getD 15 "") = some fn% «eq_prefix_run__L15» ∧
    (fn% «eq_prefix_run__L15»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L15»).body = epBody 15 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L15») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_16 : coreProgram.find? (eqPrefixRunNames.getD 16 "") = some fn% «eq_prefix_run__L16» ∧
    (fn% «eq_prefix_run__L16»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L16»).body = epBody 16 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L16») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_17 : coreProgram.find? (eqPrefixRunNames.getD 17 "") = some fn% «eq_prefix_run__L17» ∧
    (fn% «eq_prefix_run__L17»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L17»).body = epBody 17 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L17») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_18 : coreProgram.find? (eqPrefixRunNames.getD 18 "") = some fn% «eq_prefix_run__L18» ∧
    (fn% «eq_prefix_run__L18»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L18»).body = epBody 18 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L18») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_19 : coreProgram.find? (eqPrefixRunNames.getD 19 "") = some fn% «eq_prefix_run__L19» ∧
    (fn% «eq_prefix_run__L19»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L19»).body = epBody 19 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L19») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_20 : coreProgram.find? (eqPrefixRunNames.getD 20 "") = some fn% «eq_prefix_run__L20» ∧
    (fn% «eq_prefix_run__L20»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L20»).body = epBody 20 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L20») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_21 : coreProgram.find? (eqPrefixRunNames.getD 21 "") = some fn% «eq_prefix_run__L21» ∧
    (fn% «eq_prefix_run__L21»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L21»).body = epBody 21 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L21») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_22 : coreProgram.find? (eqPrefixRunNames.getD 22 "") = some fn% «eq_prefix_run__L22» ∧
    (fn% «eq_prefix_run__L22»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L22»).body = epBody 22 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L22») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_23 : coreProgram.find? (eqPrefixRunNames.getD 23 "") = some fn% «eq_prefix_run__L23» ∧
    (fn% «eq_prefix_run__L23»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L23»).body = epBody 23 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L23») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_24 : coreProgram.find? (eqPrefixRunNames.getD 24 "") = some fn% «eq_prefix_run__L24» ∧
    (fn% «eq_prefix_run__L24»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L24»).body = epBody 24 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L24») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_25 : coreProgram.find? (eqPrefixRunNames.getD 25 "") = some fn% «eq_prefix_run__L25» ∧
    (fn% «eq_prefix_run__L25»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L25»).body = epBody 25 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L25») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_26 : coreProgram.find? (eqPrefixRunNames.getD 26 "") = some fn% «eq_prefix_run__L26» ∧
    (fn% «eq_prefix_run__L26»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L26»).body = epBody 26 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L26») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_27 : coreProgram.find? (eqPrefixRunNames.getD 27 "") = some fn% «eq_prefix_run__L27» ∧
    (fn% «eq_prefix_run__L27»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L27»).body = epBody 27 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L27») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_28 : coreProgram.find? (eqPrefixRunNames.getD 28 "") = some fn% «eq_prefix_run__L28» ∧
    (fn% «eq_prefix_run__L28»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L28»).body = epBody 28 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L28») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_29 : coreProgram.find? (eqPrefixRunNames.getD 29 "") = some fn% «eq_prefix_run__L29» ∧
    (fn% «eq_prefix_run__L29»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L29»).body = epBody 29 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L29») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_30 : coreProgram.find? (eqPrefixRunNames.getD 30 "") = some fn% «eq_prefix_run__L30» ∧
    (fn% «eq_prefix_run__L30»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L30»).body = epBody 30 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L30») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_31 : coreProgram.find? (eqPrefixRunNames.getD 31 "") = some fn% «eq_prefix_run__L31» ∧
    (fn% «eq_prefix_run__L31»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L31»).body = epBody 31 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L31») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_32 : coreProgram.find? (eqPrefixRunNames.getD 32 "") = some fn% «eq_prefix_run__L32» ∧
    (fn% «eq_prefix_run__L32»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L32»).body = epBody 32 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L32») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_33 : coreProgram.find? (eqPrefixRunNames.getD 33 "") = some fn% «eq_prefix_run__L33» ∧
    (fn% «eq_prefix_run__L33»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L33»).body = epBody 33 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L33») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_34 : coreProgram.find? (eqPrefixRunNames.getD 34 "") = some fn% «eq_prefix_run__L34» ∧
    (fn% «eq_prefix_run__L34»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L34»).body = epBody 34 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L34») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_35 : coreProgram.find? (eqPrefixRunNames.getD 35 "") = some fn% «eq_prefix_run__L35» ∧
    (fn% «eq_prefix_run__L35»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L35»).body = epBody 35 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L35») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_36 : coreProgram.find? (eqPrefixRunNames.getD 36 "") = some fn% «eq_prefix_run__L36» ∧
    (fn% «eq_prefix_run__L36»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L36»).body = epBody 36 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L36») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_37 : coreProgram.find? (eqPrefixRunNames.getD 37 "") = some fn% «eq_prefix_run__L37» ∧
    (fn% «eq_prefix_run__L37»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L37»).body = epBody 37 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L37») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_38 : coreProgram.find? (eqPrefixRunNames.getD 38 "") = some fn% «eq_prefix_run__L38» ∧
    (fn% «eq_prefix_run__L38»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L38»).body = epBody 38 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L38») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_39 : coreProgram.find? (eqPrefixRunNames.getD 39 "") = some fn% «eq_prefix_run__L39» ∧
    (fn% «eq_prefix_run__L39»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L39»).body = epBody 39 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L39») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn_40 : coreProgram.find? (eqPrefixRunNames.getD 40 "") = some fn% «eq_prefix_run__L40» ∧
    (fn% «eq_prefix_run__L40»).params = [.n 0, .n 1, .n 2, .n 3] ∧ (fn% «eq_prefix_run__L40»).body = epBody 40 :=
  ⟨coreProgram_find?_at (j := idx% «eq_prefix_run__L40») rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem epr_fn : ∀ n ≤ 40, ∃ f : Fn, coreProgram.find? (eqPrefixRunNames.getD n "") = some f ∧
    f.params = [.n 0, .n 1, .n 2, .n 3] ∧ f.body = epBody n := by
  intro n hn
  interval_cases n
  exacts [⟨_, epr_fn_0⟩, ⟨_, epr_fn_1⟩, ⟨_, epr_fn_2⟩, ⟨_, epr_fn_3⟩, ⟨_, epr_fn_4⟩, ⟨_, epr_fn_5⟩, ⟨_, epr_fn_6⟩, ⟨_, epr_fn_7⟩, ⟨_, epr_fn_8⟩, ⟨_, epr_fn_9⟩, ⟨_, epr_fn_10⟩, ⟨_, epr_fn_11⟩, ⟨_, epr_fn_12⟩, ⟨_, epr_fn_13⟩, ⟨_, epr_fn_14⟩, ⟨_, epr_fn_15⟩, ⟨_, epr_fn_16⟩, ⟨_, epr_fn_17⟩, ⟨_, epr_fn_18⟩, ⟨_, epr_fn_19⟩, ⟨_, epr_fn_20⟩, ⟨_, epr_fn_21⟩, ⟨_, epr_fn_22⟩, ⟨_, epr_fn_23⟩, ⟨_, epr_fn_24⟩, ⟨_, epr_fn_25⟩, ⟨_, epr_fn_26⟩, ⟨_, epr_fn_27⟩, ⟨_, epr_fn_28⟩, ⟨_, epr_fn_29⟩, ⟨_, epr_fn_30⟩, ⟨_, epr_fn_31⟩, ⟨_, epr_fn_32⟩, ⟨_, epr_fn_33⟩, ⟨_, epr_fn_34⟩, ⟨_, epr_fn_35⟩, ⟨_, epr_fn_36⟩, ⟨_, epr_fn_37⟩, ⟨_, epr_fn_38⟩, ⟨_, epr_fn_39⟩, ⟨_, epr_fn_40⟩]

theorem epBody_ok : ∀ n ≤ 40, (atomsOf (epBody n)).all (loadInB [(0, n + 1), (2, n), (3, n)]) = true ∧
    (retOf (epBody n)).isSome = true := by
  have h : (List.range 41).all (fun n => (atomsOf (epBody n)).all (loadInB [(0, n + 1), (2, n), (3, n)]) &&
      (retOf (epBody n)).isSome) = true := by decide +kernel
  intro n hn
  have := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true] using this

theorem epr_loop {f : Fn} {n : ℕ} (h : f.body = epBody n) : f.loop = false := by
  unfold Fn.loop
  rw [h, epBody, List.reverse_append]
  simp

set_option maxRecDepth 100000 in
theorem epc_pureIn : coreProgram.PureIn ("eq_prefix_chain" :: eqPrefixRunNames) :=
  Tables.pureIn_of_pureInB (by decide +kernel)

theorem eprNames_length : eqPrefixRunNames.length = 41 := rfl

theorem eprNames_get {n : ℕ} (hn : n ≤ 40) : eqPrefixRunNames[n]! = eqPrefixRunNames.getD n "" := by
  rw [List.getD_eq_getElem _ _ (by rw [eprNames_length]; omega), getElem!_pos eqPrefixRunNames n
    (by rw [eprNames_length]; omega)]

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **Every valid tree of `eq_prefix_run__L{n}`** reading `a`, `b1` and storing into `chain` has
block its frame, ends at its cursor, loads in the region of those cells and hints nothing. -/
theorem epr_shape {n : ℕ} (hn : n ≤ 40) {args rets : List E} {R : ℕ → Prop} (hal : args.length = 4)
    (hptr : ∀ q ∈ [(0, n + 1), (2, n), (3, n)], ∀ off < q.2,
      ∃ i, (args.getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i)
    {rd : Reader} {t : Tree} (hn' : t.name = eqPrefixRunNames.getD n "") (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (c : ℕ) :
    t.block fs coreProgram.loop = fs (eqPrefixRunNames.getD n "") ∧ t.endA fs coreProgram.loop al c = c ∧
      t.LoadsR coreProgram R ∧ t.HintsR coreProgram R := by
  obtain ⟨f, hf, hpf, hbf⟩ := epr_fn n hn
  obtain ⟨hL, hr⟩ := epBody_ok n hn
  rw [← hbf] at hL hr
  have hparams : f.params = (List.range args.length).map V.n := by rw [hpf, hal]; rfl
  have hlp : coreProgram.loop (eqPrefixRunNames.getD n "") = false := by
    rw [Program.loop_of_find? hf]; exact epr_loop hbf
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  have hnc : ∀ fn' σ es vs, coreProgram.find? (eqPrefixRunNames.getD n "") = some fn' →
      walk σ fn'.body = .ret es vs → calls es = [] := by
    intro fn' σ es vs hfn hw
    rw [hf] at hfn
    cases hfn
    have hb' : f.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    rw [hb', walk_atoms] at hw
    cases hw
    exact calls_atoms _
  have hmem : eqPrefixRunNames.getD n "" ∈ "eq_prefix_chain" :: eqPrefixRunNames := by
    refine List.mem_cons_of_mem _ ?_
    rw [List.getD_eq_getElem _ _ (by rw [eprNames_length]; omega)]
    exact List.getElem_mem _
  obtain ⟨h1, h2⟩ := block_endA_leaf (fs := fs) (al := al) epc_pureIn hmem hlp hnc hn' hv hb c
  have hargs : ∀ q ∈ [(0, n + 1), (2, n), (3, n)], q.1 < args.length := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp [hal]
  obtain ⟨h3, h4⟩ := loadsR_hintsR_of_loadIn R R hf hparams hL hr hargs hptr hn' hv
  exact ⟨h1, h2, h3, h4⟩

/-! ## `eq_prefix_chain` -/

/-- `eq_prefix_chain`'s statements before its dispatch: the bound, the range check. -/
def epcPre : List Stmt :=
  [.atom (.const (.n (val% «eq_prefix_chain» "s0#0")) (word (2 ^ 40) 0)),
    .atom (.rangeCheck (.n (val% «eq_prefix_chain» "count_g")) (.n (val% «eq_prefix_chain» "s0#1")) (.n (val% «eq_prefix_chain» "s0#2")) (.n (val% «eq_prefix_chain» "s0#3")) (.n (val% «eq_prefix_chain» "s0#0")))]

/-- The dispatch's arguments. -/
def epcArgs : List V :=
  [.n (val% «eq_prefix_chain» "chain"), .n (val% «eq_prefix_chain» "seed"), .n (val% «eq_prefix_chain» "a"), .n (val% «eq_prefix_chain» "b1")]

theorem epc_body : (fn% «eq_prefix_chain»).body = epcPre ++
    .dispatch (.n (val% «eq_prefix_chain» "count_g")) eqPrefixRunNames epcArgs [.n (val% «eq_prefix_chain» "done")] ::
      ([] ++ [.ret []]) := by
  rw [eq_prefix_chain_body]; rfl

theorem epc_params : (fn% «eq_prefix_chain»).params = [.n 0, .n 1, .n 2, .n 3, .n 4] := rfl

theorem epc_not_loop : coreProgram.loop "eq_prefix_chain" = false := by
  rw [Program.loop_of_find? find_eq_prefix_chain]
  unfold Fn.loop
  rw [eq_prefix_chain_body]
  rfl

/-- The end of `eq_prefix_chain`'s subtree from its cursor `c`: its leaf at the aligned base. -/
def epcEnd (fs : String → ℕ) (al : String → Bool) (n c : ℕ) : ℕ :=
  allocBase (al (eqPrefixRunNames.getD n "")) c + fs (eqPrefixRunNames.getD n "")

/-- **Every valid tree of `eq_prefix_chain`** at `g^n` has block its frame, ends at `epcEnd`, and
loads only the leaf's cells. -/
theorem epc_shape {n : ℕ} (hn : n ≤ 40) {chain seed a b1 : E} {R : ℕ → Prop}
    (hptr : ∀ q ∈ [(0, n + 1), (2, n), (3, n)], ∀ off < q.2,
      ∃ i, ([chain, seed, a, b1].getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i)
    {rd : Reader} {t : Tree} (hn' : t.name = "eq_prefix_chain")
    (hv : t.Valid coreProgram rd [chain, seed, a, b1, gen ^ n] []) (hb : t.BufsOk coreProgram) (c : ℕ) :
    t.block fs coreProgram.loop = fs "eq_prefix_chain" ∧ t.endA fs coreProgram.loop al c = epcEnd fs al n c ∧
      t.LoadsR coreProgram R ∧ t.HintsR coreProgram R := by
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
  simp only [Tree.name] at hn'
  subst hn'
  obtain ⟨fn, hfn, hpar, es, vs, hw, -, -, hk⟩ := hv
  rw [find_eq_prefix_chain, Option.some.injEq] at hfn
  subst hfn
  rw [epc_params] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2, h3, h4⟩ := hpar
  have hw0 : walk σ (fn% «eq_prefix_chain»).body = .ret (epcPre.flatMap (slEvs σ) ++
      .call eqPrefixRunNames[n]! epcArgs [.n (val% «eq_prefix_chain» "done")] ::
        ([] : List Stmt).flatMap (slEvs σ)) [] := by
    rw [epc_body]
    exact walk_dispatch σ epcPre [] rfl rfl _ eqPrefixRunNames _ _ _ (i := n)
      (by rw [eprNames_length]; omega) (by rw [eprNames_length]; norm_num)
      (by show σ (.n 4) = _; rw [h4, gen_pow_eq_ofK])
  rw [hw0] at hw
  cases hw
  have hev : (Memory.Tree.node "eq_prefix_chain" σ bufs kids).events coreProgram =
      epcPre.flatMap (slEvs σ) ++ .call eqPrefixRunNames[n]! epcArgs [.n (val% «eq_prefix_chain» "done")] ::
        ([] : List Stmt).flatMap (slEvs σ) := Complete.events_node find_eq_prefix_chain hw0
  have hal : allocs σ (epcPre.flatMap (slEvs σ) ++ .call eqPrefixRunNames[n]! epcArgs [.n (val% «eq_prefix_chain» "done")] ::
      ([] : List Stmt).flatMap (slEvs σ)) = [] := rfl
  have hcl : calls (epcPre.flatMap (slEvs σ) ++ .call eqPrefixRunNames[n]! epcArgs [.n (val% «eq_prefix_chain» "done")] ::
      ([] : List Stmt).flatMap (slEvs σ)) = [⟨eqPrefixRunNames[n]!, epcArgs, [.n (val% «eq_prefix_chain» "done")], true⟩] := rfl
  rw [Tree.BufsOk, hev, hal] at hb
  obtain ⟨rfl, hbk⟩ := hb
  rw [hcl] at hk
  rcases kids with _ | ⟨t1, _ | ⟨t2, ks⟩⟩ <;> try (simp [Tree.KidsValid] at hk; done)
  rw [Tree.KidsValid, Tree.KidsValid] at hk
  obtain ⟨hn1, hv1, -⟩ := hk
  simp only [↓reduceIte] at hv1
  rw [Tree.BufsOkKids] at hbk
  obtain ⟨hb1, -⟩ := hbk
  rw [eprNames_get hn] at hn1
  have ha : epcArgs.map σ = [chain, seed, a, b1] := by
    simp only [epcArgs, List.map_cons, List.map_nil]
    rw [show σ (.n (val% «eq_prefix_chain» "chain")) = σ (.n 0) from rfl, h0,
      show σ (.n (val% «eq_prefix_chain» "seed")) = σ (.n 1) from rfl, h1,
      show σ (.n (val% «eq_prefix_chain» "a")) = σ (.n 2) from rfl, h2,
      show σ (.n (val% «eq_prefix_chain» "b1")) = σ (.n 3) from rfl, h3]
  rw [ha] at hv1
  obtain ⟨hB1, hE1, hL1, hH1⟩ := epr_shape (fs := fs) (al := al) hn rfl hptr hn1 hv1 hb1
    (allocBase (al (eqPrefixRunNames.getD n "")) c + fs (eqPrefixRunNames.getD n ""))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Tree.block, epc_not_loop]; simp
  · rw [endA_node, epc_not_loop]
    simp only [Bool.false_eq_true, ↓reduceIte, List.sum_nil, add_zero, endF_cons, endF_nil, hn1, hB1, hE1]
    rfl
  · rw [Tree.LoadsR, hev]
    refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids, Tree.LoadsRKids]; exact ⟨hL1, trivial⟩⟩
    simp [loadAddrs, epcPre, slEvs, Ev.loadAddr?] at hA
  · rw [Tree.HintsR, hev]
    refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids, Tree.HintsRKids]; exact ⟨hH1, trivial⟩⟩
    simp [heapHintAddrs, epcPre, slEvs, Ev.hintAddrs] at hA

/-- **`eq_prefix_chain` completes placed** at `g^n`, `n ≤ 40`: the prefix products of `as`, `bs`
from `seed` at `chain[0 ..= n]` its caller's words, the three arrays' cells in `R`. -/
theorem eq_prefix_chain_placed {k : ℕ} (hk : 6 ≤ k) {n : ℕ} (hn : n ≤ 40) {chain seed a b1 : E}
    {as bs : List E} (has : as.length = n) (hbs : bs.length = n) {R : ℕ → Prop}
    (hptr : ∀ q ∈ [(0, n + 1), (2, n), (3, n)], ∀ off < q.2,
      ∃ i, ([chain, seed, a, b1].getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) (fp c : ℕ) :
    CallAtA fs al cert k "eq_prefix_chain" [chain, seed, a, b1, gen ^ n] [] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd a as ∧ ReadsAt rd b1 bs ∧ ∀ j ≤ n, LoadHolds rd chain j (prefixProd seed as bs j))
      PostQuiet (fs "eq_prefix_chain") fp c (epcEnd fs al n c) := by
  have h0 : CallCompletes0 k "eq_prefix_chain" [chain, seed, a, b1, gen ^ n] []
      (fun rd => ReadsAt rd a as ∧ ReadsAt rd b1 bs ∧ ∀ j ≤ n, LoadHolds rd chain j (prefixProd seed as bs j))
      FreePost := callCompletes0_free coreProgram_wf eq_prefix_chain_free.1 eq_prefix_chain_free.2 fun rd hl hp => by
    refine (eq_prefix_chain_holds rd _ _).mpr ⟨rfl, ?_, n, by omega, rfl, as, bs, has, hbs, hp.1, hp.2.1, hp.2.2⟩
    have h41 : 41 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    obtain ⟨r1, r2, r3⟩ := rc_complete_low hl h41 (show n < 41 by omega)
    exact ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact r1, by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact r2, r3⟩
  refine callAtA_of_callCompletes0 epc_pureIn List.mem_cons_self
    (le_trans (le_allocBase _ c) (Nat.le_add_right _ _)) (h0.mono (fun _ h => h) fun _ _ _ h => h)
    fun rd t _ _ hn' hv hb _ => epc_shape hn hptr hn' hv hb c

end
end LeanVM.Guest.B1.VsC
