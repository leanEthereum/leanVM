module

public import LeanVM.Cost.Bounds.Guest.Whir
public import LeanVM.Cost.Bounds.Guest.Stmt
public import LeanVM.Cost.Bounds.Guest.Xmss
public import LeanVM.Cost.Decoder.Witness

/-!
# Bounds on the guest decoder's prices: each callee's witness off its frame

`Cost/Decoder/Frames.lean`: a callee's witness at its call's frame `Vn k args rets`, a closure of
the frame map whose application costs at most `F + 9` (`F` the frame map's price), and the closures
`decWitNC` hands to `decWitC` (`decWitNC.lam0 … lam2`), the callees' witness functions but the
signatures' readers, which the decoder's top passes (`xmssAtFrameT`, `sphincsAtFrameT`, their
frames looked up once, `Bounds/Guest/DecTop.lean`):

* the readers' tables `Tb` (`ReaderTabsOK`, `readerTabs_ok`),
  `daAtFrame_cost` (`dvWitNC`'s price `DW` at the frame a parameter, `daFrame_runs`, `daFrame_cost`:
  the frame's spec and price for `Da.lean`'s bound), `proofAtFrame_cost`, `hintsAtFrame_cost`;
* `wD_cost`, `wV_cost`, `wA_cost`: the three closures `decWitNC` builds for `decWitC`,
  their prices.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram) {G : ℕ}

/-- The readers' tables, their entries small (`readerTabs_ok`). -/
structure ReaderTabsOK (Tb : ReaderTabs) : Prop where
  xmss : XmssTabsOK Tb.xmss
  sphincs : SpTabsOK Tb.sphincs
  whir : WhirTabsOK Tb.whir

theorem readerTabs_ok : ReaderTabsOK readerTabs := ⟨xmssTabs_ok, spTabs_ok, whirTabs_ok⟩

/-- **The readers' tables, built once per decoding** (`readerTabsC`): at most `32900`. -/
theorem readerTabs_cost (hP : Includes P Decoder.readerTabsC.costDeps) :
    machineCost P Decoder.readerTabsC.costIdx [] ≤ 32900 := by
  rw [Decoder.readerTabsC.costEq P hP]
  have := xmssTabs_cost P (by includes)
  have := spTabs_cost P (by includes)
  have := whirTabs_cost P (by includes)
  omega

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

omit hF in
/-- **The DA matrix off `da_verify`'s frame** (`daAtFrameC`), the logarithm's tables `D` given,
`da_verify`'s witness (`dvWitNC`) at that frame at most `DW` (`Bounds/Guest/Da.lean`): `DW + 10`. -/
theorem daAtFrame_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.daAtFrameC.costDeps) (DW : ℕ)
    (hDW : ∀ args rets : List E, args.length + rets.length ≤ 16 → machineCost P Decoder.dvWitNC.costIdx
      [encodeValue D, .closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets],
        VnV] ≤ DW) (args rets : List E) (hlen : args.length + rets.length ≤ 16) :
    machineCost P Decoder.daAtFrameC.costIdx [encodeValue D, VnV, encodeValue args, encodeValue rets] ≤
      DW + 10 := by
  rw [Decoder.daAtFrameC.costEq P hP D Vn VnV hVn]
  have := hDW args rets hlen
  omega

omit hF in
/-- `da_verify`'s frame (`daAtFrameC.lam0`), the valuation `dvWitNC` takes: its spec. -/
theorem daFrame_runs (hP : Includes P Decoder.daAtFrameC.lam0.costDeps) (args rets : List E) (v : V) :
    RunsApp P (.closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets])
      [encodeValue v] (encodeValue (Vn 28 args rets v)) :=
  RunsApp.of_spec (Decoder.daAtFrameC.lam0.costSpec P hP Vn VnV hVn _ _ v)

/-- `da_verify`'s frame (`daAtFrameC.lam0`): its price `F + 9`. -/
theorem daFrame_cost (hP : Includes P Decoder.daAtFrameC.lam0.costDeps) (args rets : List E)
    (hlen : args.length + rets.length ≤ 16) (v : V) :
    appCost P (.closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets])
      [encodeValue v] ≤ F + 9 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    Decoder.daAtFrameC.lam0.costEq P hP Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
  have := hF 28 args rets v (by norm_num) hlen; omega

/-- **A child's proof off its `verify_sub` frame** (`proofAtFrameC`), the readers' tables `Tb`
given, the cursor's length at the frame at most `L`: `vsPiPrice R (F + 9) F C L + 13`. -/
theorem proofAtFrame_cost (hP : Includes P Decoder.proofAtFrameC.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) {rd : Reader}
    {rdV : MachineValue} (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) {cl : E → E → ℕ} {clV : MachineValue}
    (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
    {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
    {L : ℕ} (hL32 : L ≤ 2 ^ 32) (args : List E) (hlen : args.length ≤ 16)
    (hL : cl (Vn 19 args [] (.n 25)) (Vn 19 args [] (.n 1928)) ≤ L) :
    machineCost P Decoder.proofAtFrameC.costIdx [encodeValue Tb, rdV, VnV, clV, encodeValue args] ≤
      vsPiPrice R (F + 9) F C L + 13 := by
  rw [Decoder.proofAtFrameC.costEq P hP Tb rd rdV hrd Vn VnV hVn cl clV hcl]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 19 args [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.proofAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v] ≤ F + 9 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.proofAtFrameC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF 19 args [] v (by norm_num) (by simpa using hlen); omega
  have := vsPiOfN_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) Tb.whir hTb.whir
  omega

/-- **The batching's hints off `aggregate_claims`' frame** (`hintsAtFrameC`):
`47·F + 46·R + 138487`. -/
theorem hintsAtFrame_cost (hP : Includes P Decoder.hintsAtFrameC.costDeps) {rd : Reader}
    {rdV : MachineValue} (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) (args : List E)
    (hlen : args.length ≤ 16) :
    machineCost P Decoder.hintsAtFrameC.costIdx [rdV, VnV, encodeValue args] ≤
      47 * F + 46 * R + 138487 := by
  rw [Decoder.hintsAtFrameC.costEq P hP rd rdV hrd Vn VnV hVn]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.hintsAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 34 args [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.hintsAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.hintsAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v] ≤ F + 9 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.hintsAtFrameC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF 34 args [] v (by norm_num) (by simpa using hlen); omega
  have := aggHints_cost P hσ hS hrd hR (by includes)
  omega

end Frames

/-! ## The callees' witness functions `decWitNC` passes -/

section Closures

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL32 : L ≤ 2 ^ 32)

include hVn in
/-- The DA witness function (`decWitNC.lam0`), the logarithm's tables `D` given, `dvWitNC` at
`da_verify`'s frame at most `DW`: `DW + 17`. -/
theorem wD_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.decWitNC.lam0.costDeps) (DW : ℕ)
    (hDW : ∀ args rets : List E, args.length + rets.length ≤ 16 → machineCost P Decoder.dvWitNC.costIdx
      [encodeValue D, .closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets],
        VnV] ≤ DW) (args rets : List E) (hlen : args.length + rets.length ≤ 16) :
    appCost P (.closure Decoder.decWitNC.lam0.costIdx [encodeValue D, VnV])
      [encodeValue args, encodeValue rets] ≤ DW + 17 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decWitNC.lam0.costEq P hP D Vn VnV hVn, List.length_cons, List.length_cons, List.length_nil]
  have := daAtFrame_cost P hVn D (by includes) DW hDW args rets hlen
  omega

include hVn hF hrd hR hcl hC hL32 in
/-- The child proofs' witness function (`decWitNC.lam1`), the readers' tables `Tb` given, the
cursor's length at `verify_sub`'s frame at most `L`: `vsPiPrice R (F + 9) F C L + 23`. -/
theorem wV_cost (hP : Includes P Decoder.decWitNC.lam1.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) (args : List E) (hlen : args.length ≤ 16)
    (hL : cl (Vn 19 args [] (.n 25)) (Vn 19 args [] (.n 1928)) ≤ L) :
    appCost P (.closure Decoder.decWitNC.lam1.costIdx [encodeValue Tb, rdV, VnV, clV])
      [encodeValue args] ≤ vsPiPrice R (F + 9) F C L + 23 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append, Decoder.decWitNC.lam1.costEq P hP Tb rd rdV hrd Vn VnV hVn cl clV hcl, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
  have := proofAtFrame_cost P hVn hF (by includes) Tb hTb hrd hR hcl hC hL32 args hlen hL
  omega

include hVn hF hrd hR in
/-- The batching hints' witness function (`decWitNC.lam2`): `47·F + 46·R + 138493`. -/
theorem wA_cost (hP : Includes P Decoder.decWitNC.lam2.costDeps) (args : List E)
    (hlen : args.length ≤ 16) :
    appCost P (.closure Decoder.decWitNC.lam2.costIdx [rdV, VnV]) [encodeValue args] ≤
      47 * F + 46 * R + 138493 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decWitNC.lam2.costEq P hP rd rdV hrd Vn VnV hVn, List.length_cons, List.length_cons, List.length_nil]
  have := hintsAtFrame_cost P hVn hF (by includes) hrd hR args hlen
  omega

end Closures

end

end LeanVM.Cost.Bounds.Guest
