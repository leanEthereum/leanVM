/-
  LeanVM.Protocol.EndToEnd.Front.TablePhase

  The verifier program's table sumcheck specified on the oracle protocol's relations: from the bus
  seam at what the bus phase read to the table seam at the protocol's output, given the algebraic
  identities between the program's computations and the protocol's verdicts.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.BusPhase
public import LeanVM.Protocol.EndToEnd.Front.TableArk
public import LeanVM.Protocol.EndToEnd.Front.TableTerms

/-!
# The table sumcheck on doom

`tablePhase layout bus` (`verifier.py:1380-1388` and `599-628`) is the oracle protocol's
`tableSumcheck` (`LeanVM.Protocol.TableSumcheck`) on the wire: the batching challenge `ξ`, the
plain sumcheck of four coefficients per round (one left out on the wire), the evaluations of every
table's columns, and the final check. Its doom is stated on the protocol's relations at the
protocol's statement `(input, busOut …)` of what the bus phase read (`BusWit`):

* `ξ`: from the bus seam to the sumcheck's input relation, charged `L₀ · (B + 2) / |E|`
  (`xi_escape`);
* the rounds: `wireSumcheckSpec` on the protocol's family, each charged `L₀ · 3 / |E|`;
* the evaluations and the check: the protocol's last message and its check (`finalValues_keep`),
  to the table seam at `tableOut`.

The program computes the target, the final check's value and the claims its own way. The four
identities that make them the protocol's are `TableFid` (the number of rounds is `τ_max`; the
target is the protocol's batched claim; the final check's value is the protocol's formula; every
claim of the protocol's output is among the program's, through a column numbering `colOf`); they
are statements about the instance and the layout only, discharged for leanISA separately.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.TableSumcheck
open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## The program's quantities -/

/-- The number of constraints, `Σ n_constraints`. -/
def nCons : ℕ := (tables.map Table.nConstraints).sum

/-- The constraint powers of `ξ`. -/
def cpsOf (ξ : E) : List E := (powers ξ (nCons + 3)).take nCons

/-- The form powers of `ξ`. -/
def fpsOf (ξ : E) : List E := (powers ξ (nCons + 3)).drop nCons

/-- The rows of the final loop at the point `point` (the challenges reversed). -/
def rowsOf (layout : Verifier.Layout) (bus : BusResult) (point : List E) :
    List (Table × ℕ × List Form × E) :=
  List.zip tables (List.zip layout.tableLogHeights
    (List.zip bus.forms (Verifier.tableWeights layout.tableLogHeights bus.point point)))

theorem tables_width_pos : ∀ t ∈ tables, 0 < t.width := by decide

theorem rowsOf_width_pos (layout : Verifier.Layout) (bus : BusResult) (point : List E) :
    ∀ r ∈ rowsOf layout bus point, 0 < r.1.width := fun _ hr ↦
  tables_width_pos _ (List.of_mem_zip hr).1

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (layout : Verifier.Layout)

/-- The protocol's statement after the bus phase, on what it read. -/
def busStmt (w : BusWit) : I.Stmt × BusOut I := (input, Bus.busOut hI (w.layer I input) (w.vals I))

/-- The sumcheck's statement after its rounds. -/
def tableStmt (w : BusWit) (ξ : E) (ch : List E) (claim : E) :
    SumcheckRound.Stmt (Data I) E I.τmax :=
  ((busStmt I hI input w, ξ), (vecOf I.τmax ch, claim))

/-- **The program's computations are the protocol's**: the identities between the table phase's
target, final check and claims and the protocol's batched claim, formula and output claims, at
what the bus phase read. `colOf` numbers the protocol's columns as the program does. -/
structure TableFid (colOf : I.ColumnId → ℕ) (w : BusWit) : Prop where
  /-- The rounds: `max` of the heights is `τ_max`. -/
  rounds : layout.tableLogHeights.foldl max 0 = I.τmax
  /-- The target is the protocol's batched claim. -/
  target : ∀ ξ, dot (fpsOf ξ) (w.result layout).totals =
    powerBatch (claimed I (busStmt I hI input w)) ξ
  /-- The final check's value is the protocol's formula. -/
  formula : ∀ ξ (ch : List E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf layout (w.result layout) ch.reverse) evs →
    (pyTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse (rowsOf layout (w.result layout) ch.reverse) evs
      0 0 []).1 = formula I (busStmt I hI input w, ξ) (vecOf I.τmax ch).reverse
        (vecOf I.tableColumns evs.flatten)
  /-- The protocol's output claims are among the program's. -/
  claims : ∀ ξ (ch : List E) (claim : E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf layout (w.result layout) ch.reverse) evs →
    ∀ c ∈ (tableOut I (tableStmt I hI input w ξ ch claim)
      (vecOf I.tableColumns evs.flatten)).2.columns.toList,
      (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
        (w.result layout).claims ++ (pyTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse
          (rowsOf layout (w.result layout) ch.reverse) evs 0 0 []).2

/-- **The table seam on the wire**: the protocol's output at what was read is doomed, its input
statement is `input`, and its claims are among the program's. -/
def TablePost (colOf : I.ColumnId → ℕ) (claims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ (W : Word) (tout : I.Stmt × TableOut I), firstWord h = some W ∧
    RelDoom (cands W) (Seam.table I) tout ∧ tout.1 = input ∧
    ∀ c ∈ tout.2.columns.toList, (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      claims

variable {εmax : ℝ≥0∞}

/-- What the table sumcheck's rounds and final values give: the evaluations read, the claims
the program makes of them, and the table seam's doom at the protocol's output. -/
def TableSumcheckPost (w : BusWit) (ξ : E) (claims' : List Verifier.ColumnClaim) (h : List Ev) :
    Prop :=
  ∃ ch claim evs, ReadShape (rowsOf layout (w.result layout) ch.reverse) evs ∧
    ch.length = I.τmax ∧
    claims' = (pyTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse
      (rowsOf layout (w.result layout) ch.reverse) evs 0 0 []).2 ∧
    HDoom cands (Seam.table I) (tableOut I (tableStmt I hI input w ξ ch claim)
      (vecOf I.tableColumns evs.flatten)) h

/-- **The table sumcheck's rounds and final values** (`table_sumcheck`, `verifier.py:599-628`),
from doom on the sumcheck's input relation after `ξ`: the plain sumcheck, each round charged
`L₀ · 3 / |E|`, then the evaluations and the final check. -/
noncomputable def tableSumcheckSpec (colOf : I.ColumnId → ℕ) (w : BusWit)
    (fid : TableFid I hI input layout colOf w) (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) (ξ : E) :
    Spec (Verifier.tableSumcheck layout.tableLogHeights (w.result layout).forms (cpsOf ξ)
        (fpsOf ξ) (w.result layout).point (dot (fpsOf ξ) (w.result layout).totals))
      (HDoom cands (SumcheckRound.rel (tableFamily I) 0)
        ((busStmt I hI input w, ξ), (#v[], dot (fpsOf ξ) (w.result layout).totals)))
      (TableSumcheckPost I hI cands input layout w ξ) εmax
      (sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T) T :=
  let s := busStmt I hI input w
  let bus := w.result layout
  let n := layout.tableLogHeights.foldl max 0
  (wireSumcheckSpec (T := T) (tableFamily I) cands (tableFamily_consistent I hd)
    (tableFamily_sound I) hfin hcard (by norm_num) he (s, ξ) (List.replicate n none) 0 #v[]
    (dot (fpsOf ξ) bus.totals) (by simp [n, fid.rounds]) (fun k hk ↦ by
      have hk' : k < I.τmax := by simpa [n, fid.rounds] using hk
      simp [tableFamily, Sumcheck.family, Sumcheck.domain, Sumcheck.unitWeights, wireDomain,
        hk'])).bind' fun ⟨ch, claim⟩ ↦
    let P := SumcheckPost (tableFamily I) cands (s, ξ) I.τmax #v[] (ch, claim)
    let rows := rowsOf layout bus ch.reverse
    ((tableTermsSpec hT P (fun _ _ hp ↦ ⟨hp.1, hp.2.append _⟩) (cpsOf ξ) (fpsOf ξ) ch.reverse
      rows (rowsOf_width_pos layout bus _) 0 0 []).mono (fun _ hp ↦ hp) (fun _ _ hp ↦ hp) le_rfl
      (rowsLead_le _ _) le_rfl).bind' fun ⟨final, claims⟩ ↦
    (Spec.require (c := final = claim) (Post := fun _ h ↦ ∃ evs, ReadShape rows evs ∧
        ch.length = I.τmax ∧
        claims = (pyTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse rows evs 0 0 []).2 ∧
        HDoom cands (Seam.table I) (tableOut I (tableStmt I hI input w ξ ch claim)
          (vecOf I.tableColumns evs.flatten)) h)
      (fun _ hp hc ↦ by
        obtain ⟨evs, hs, heq, hlen, W, hW, hR⟩ := hp
        have hl : ch.length = I.τmax := by simpa using hlen
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        simp only at hfst hsnd
        refine ⟨evs, hs, hl, hsnd, W, hW, finalValues_keep I hR _ ?_⟩
        rw [Sumcheck.finalCheck, decide_eq_true_eq]
        show formula I (s, ξ) (vecOf I.τmax ch).reverse (vecOf I.tableColumns evs.flatten) = claim
        rw [← fid.formula ξ ch evs hl hs, ← hfst, hc])).bind' fun _ ↦
    (Spec.ret (Post := TableSumcheckPost I hI cands input layout w ξ) claims).mono
      (fun _ ⟨evs, hs, hl, hc, hD⟩ ↦ ⟨ch, claim, evs, hs, hl, hc, hD⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl

open Classical in
/-- **The table sumcheck** (`tablePhase`, `verifier.py:1380-1388`, `599-628`) after the bus phase
read `w`: from the bus seam at `w` to the table seam on the wire. `ξ` is charged
`L₀ · (B + 2) / |E|`, each round `L₀ · 3 / |E|`. -/
noncomputable def tablePhaseSpec (colOf : I.ColumnId → ℕ) (w : BusWit)
    (fid : TableFid I hI input layout colOf w) (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) :
    Spec (tablePhase layout (w.result layout)) (BusAt I hI cands input w)
      (TablePost I cands input colOf) εmax
      (xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T)
      T :=
  let s := busStmt I hI input w
  (Spec.sampleE (xiError I L₀) (Post := fun ξ h ↦ HDoom cands
      (SumcheckRound.rel (tableFamily I) 0)
      ((s, ξ), (#v[], dot (fpsOf ξ) (w.result layout).totals)) h)
    (fun h₀ hp ↦ by
      obtain ⟨-, -, -, W, hW, hR⟩ := hp
      refine le_trans ?_ (xi_escape I (hfin W) (hcard W) s hR)
      gcongr with ξ _
      intro hD
      refine ⟨W, firstWord_append hW _, ?_⟩
      rw [fid.target ξ, Sumcheck.rel_zero]
      exact hD)).bind' fun ξ ↦
  (tableSumcheckSpec I hI cands input layout colOf w fid hd hfin hcard he hT ξ).bind'
    fun tableClaims ↦
  (Spec.ret (Post := TablePost I cands input colOf) ((w.result layout).claims ++ tableClaims)).mono
    (fun _ hp ↦ by
      obtain ⟨ch, claim, evs, hs, hl, rfl, W, hW, hR⟩ := hp
      exact ⟨W, _, hW, hR, rfl, fid.claims ξ ch claim evs hl hs⟩) (fun _ _ h ↦ h) le_rfl le_rfl
    le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
