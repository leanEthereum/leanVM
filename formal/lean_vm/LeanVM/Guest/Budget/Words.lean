/-
  LeanVM.Guest.Budget.Words

  The memory conjunct of the count over the core IR: `main`'s tree's aligned words, and so the
  executor's memory, within the node's count once its cost at the certificates' padded weights is;
  and the form of the hand bounds left for the functions the static checker does not certify.
-/

module

public import LeanVM.Guest.Memory.GuestWordsA
public import LeanVM.Guest.Memory.Image
public import LeanVM.Guest.Budget.Count

/-!
# `main`'s words within the count

`wordsA_le_of_cost`: a valid tree whose cost at the certificates' padded weights
(`fsPad fsW alW`, `Memory/GuestWordsA.lean`) is at most `N` has at most `N` aligned words, at any
frame sizes `fs ≤ fsW` with tails at most their frames and aligned flags `al ≤ alW`;
`logMem_wordsA_le`: so its memory's log size (`logMem`, b2c's `HonestA`) is at most every `k ≥ 23`
with `N ≤ 2^k`, `RunWithinCount`'s memory conjunct (in the lead's form with `23 ≤ k`).

What is left is `MainCostWithin`: on `main`'s honest tree at a node, its cost at `fsPad fsW alW`
within `nodeWords` of the node's items. Its callees the static checker certifies are bounded by
`wa_cost_le_of_stat`, `wa_cost_le_of_loop` (`exponent_tables` `4401`, `statement_digest` `148`,
`aggregate_claims` `3122 + 907 m` at `m` children, the raw signatures' loops `1327` and `7315` an
iteration, the slots' loops `16`); the others, by `HandCost` each, are the functions
`scripts/count/words.py --report` lists: `main`, its children's loop `__loop4_main`,
`claim_list_digest`, `child_claim_list_digest`, `da_verify` (a size or a loop's end read from the
node's hints), and in `verify_sub`'s subtree `open_stacked__L0 ..= L14` (sizes read from the rate's
tables), `link_rounds__*`, `squeeze_packed`, `verify_keccak`, `rs_eq_run` (sizes `g^n` built from
hinted bits), `ring_rows` (a loop's end read from memory) and their callers `link_row_side__*`,
`check_stack_terminal`, `verify_sub`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **A hand bound**: every valid tree of `f`, its `HeapBuf`s its paths', on arguments and a memory
satisfying `Pre`, costs at most `B args` at the certificates' padded weights. -/
def HandCost (f : String) (Pre : Reader → List E → Prop) (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.Valid coreProgram rd args rets →
    t.BufsOk coreProgram → Pre rd args → t.cost coreProgram true (fsPad fsW alW) ≤ B args

/-- **`main`'s cost within the count** (open): `main`'s tree `T` for a node of items `it` costs at
most the node's words at the certificates' padded weights. -/
def MainCostWithin (T : Tree) (it : NodeItems) : Prop :=
  T.cost coreProgram true (fsPad fsW alW) ≤ nodeWords it

variable {fs : String → ℕ} {lp al : String → Bool}

/-- **A tree's aligned words from its cost.** -/
theorem wordsA_le_of_cost (hfs : ∀ g, fs g ≤ fsW g) (hal : ∀ g, al g = true → alW g = true)
    (htl : ∀ f, fs (tailKey f) ≤ fs f) {T : Tree} (hb : T.BufsOk coreProgram) {N : ℕ}
    (hc : T.cost coreProgram true (fsPad fsW alW) ≤ N) : T.wordsA fs lp al ≤ N :=
  (wordsA_le_cost htl hb).trans ((cost_mono (fsPad_le hfs hal) T).trans hc)

/-- **The memory's log size within the count**: at every `k ≥ 23` holding the count. -/
theorem logMem_wordsA_le (hfs : ∀ g, fs g ≤ fsW g) (hal : ∀ g, al g = true → alW g = true)
    (htl : ∀ f, fs (tailKey f) ≤ fs f) {T : Tree} (hb : T.BufsOk coreProgram) {it : NodeItems}
    (hc : MainCostWithin T it) :
    ∀ k, 23 ≤ k → nodeWords it ≤ 2 ^ k → logMem (T.wordsA fs lp al) ≤ k :=
  fun _ h23 hk ↦ logMem_le_iff.mpr ⟨h23, (wordsA_le_of_cost hfs hal htl hb hc).trans hk⟩


/-! ## The hand functions over virtual parameters

A hand function is checked over virtual parameters (`Memory/StaticSound.lean`'s `Hand`, `CheckedH`):
values of its body (a count split from hinted bits, a size loaded from a table) taken as further
parameters. Its callers see an outer certificate in its arguments; that the inner bound at the node's
values is within the outer one is the node's `HandFact`, a fact about the honest valuation. -/

/-- **The guest's check with hand functions**, from `wa_checked`: certificates `cert` agreeing with
the certified ones, and each hand function passing its inner check. -/
theorem wa_checkedH {cert : String → Cert} {H : String → Option Hand} {A : String → Prop}
    (hagree : ∀ g, waCertOf g ≠ .none → cert g = waCertOf g)
    (hnone : ∀ g, H g = none → cert g = waCertOf g)
    (hhand : ∀ fn ∈ coreProgram, ¬ A fn.name → ∀ h, H fn.name = some h → ∃ look wl,
      LookOk look cert ∧ WlOk wl (fsPad fsW alW) ∧ chkHand look wl true h (fsPad fsW alW fn.name) fn = true) :
    CheckedH coreProgram true cert (fsPad fsW alW) H A :=
  checkedH_of wa_checked hagree hnone hhand

/-- **`main`'s cost within the count from the hand check**: `main` a hand function, every node below
it with its hand fact, and its inner bound at its virtual parameters' values within the node's words. -/
theorem mainCostWithin_of_hand {cert : String → Cert} {H : String → Option Hand} {A : String → Prop}
    (hchk : CheckedH coreProgram true cert (fsPad fsW alW) H A) {h : Hand} (hH : H "main" = some h)
    (hA : ¬ A "main") {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Tree} {args rets : List E}
    (hv : (Memory.Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Memory.Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hev : Memory.Tree.EveryKids (HandFact coreProgram cert H A) kids)
    (hpre : ArgsPre h.pre (args ++ h.vps.map σ)) {it : NodeItems}
    (hle : h.b.eval (args ++ h.vps.map σ) ≤ nodeWords it) :
    MainCostWithin (Memory.Tree.node "main" σ bufs kids) it :=
  (cost_le_of_hand hchk hH hA hv hb hev hpre).trans hle

end

end LeanVM.Guest.Budget
