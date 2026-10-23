/-
  LeanVM.Protocol.EndToEnd.Complete.BusLayout

  The verifier program's bus phase after its reads, and the blocks and depth of its layout at the
  leanISA instance: what the soundness and the completeness of the bus phase both read.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusTables

/-!
# The verifier's bus blocks

The tail of `verify_bus_balance` (`python-verifier/verifier.py:536-606` at leanVM
`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`) after its reads (`busOut`, `verifyBusBalance_eq`);
the table blocks of the three sides at the leanISA instance's sizes (`pushBlocks`, `pullBlocks`,
`countBlocks`: each table's at its log-height and row count, `layout_push`, …), the bus's depth
(`busDepth`) and the bounds on it; the empty forms the bus starts from (`forms0_*`) and the
blocks' owners (`*_owned`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

/-- The tail of `verify_bus_balance` after the reads: the claims, the point, the forms and the
totals (`verifier.py:572-606`). -/
def busOut (layout : Verifier.Layout) (alphas : List E) (beta : E)
    (point treeValues memory : List E)
    (memoryFinal bytecodeFinal : E) : BusResult :=
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let weights := eqKernel alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let claims : List Verifier.ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let fp := fingerprints weights memory memoryLow bytecodeLow
    (multilinearEval (layout.bytecode.map ofK) (bytecodeLow ++ alphas))
  let finalPc := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let r1 := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let r2 := accumulateSide r1.1 1 layout.pull pullLayout
    (fp finalPc memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let r3 := accumulateSide r2.1 2 layout.count countLayout [] [1] 0 point (treeValues.getD 2 0)
  ⟨claims, point, r3.1, [r1.2, r2.2, r3.2]⟩

/-- `verify_bus_balance` reads, then computes `busOut`. -/
theorem verifyBusBalance_eq (layout : Verifier.Layout) :
    verifyBusBalance .computed layout = (do
      let alphas ← Prog.sampleN busBits
      let beta ← Prog.sampleE
      let g ← verifyGkrGrandProducts
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth
      Prog.require (g.1 ≠ 0)
      let memory ← Prog.readN 3
      let memoryFinal ← Prog.readE
      let bytecodeFinal ← Prog.readE
      return busOut layout alphas beta g.2.1 g.2.2 memory memoryFinal bytecodeFinal) := by
  rfl

/-! ## The blocks and the depth -/

/-- The push side's table blocks. -/
def pushBlocks (s : Sizes) : List BusBlock :=
  (List.ofFn fun t : Fin 6 ↦
    (pySide t .push).map fun c ↦ (⟨s.τ t, s.rows t, c, t⟩ : BusBlock)).flatten

/-- The pull side's table blocks. -/
def pullBlocks (s : Sizes) : List BusBlock :=
  (List.ofFn fun t : Fin 6 ↦
    (pySide t .pull).map fun c ↦ (⟨s.τ t, s.rows t, c, t⟩ : BusBlock)).flatten

/-- The count side's blocks. -/
def countBlocks (s : Sizes) : List BusBlock :=
  (List.ofFn fun t : Fin 6 ↦ (tables.getD t default).countColumns.map fun l ↦
    (⟨s.τ t, s.rows t, [Form.col l], t⟩ : BusBlock)).flatten

theorem layout_push (prog : Program) (s : Sizes) : (verifierLayout prog s).push = pushBlocks s := by
  show (busBlocks (tableLogs s) (tableRows s)).1 = _
  rw [busBlocks_eq]; rfl

theorem layout_pull (prog : Program) (s : Sizes) : (verifierLayout prog s).pull = pullBlocks s := by
  show (busBlocks (tableLogs s) (tableRows s)).2.1 = _
  rw [busBlocks_eq]; rfl

theorem layout_count (prog : Program) (s : Sizes) :
    (verifierLayout prog s).count = countBlocks s := by
  show (busBlocks (tableLogs s) (tableRows s)).2.2 = _
  rw [busBlocks_eq]; rfl

/-- The framework blocks' log-sizes. -/
def fwLogs (prog : Program) (s : Sizes) : List ℕ := [0, s.logMem, prog.logSize]

/-- The bus's depth: the push side's. -/
def busDepth (prog : Program) (s : Sizes) : ℕ :=
  log2Ceil (blockTotal (sideSizes (fwLogs prog s) (pushBlocks s)))

theorem map_range_getD {α β' : Type} (l : List α) (d : α) (f : α → β') :
    (List.range l.length).map (fun b ↦ f (l.getD b d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem blockTotal_eq (sizes : List ℕ) : blockTotal sizes = (sizes.map (2 ^ ·)).sum := by
  rw [blockTotal, map_range_getD sizes 0 (2 ^ ·)]

theorem blockTotal_sideSizes (fw : List ℕ) (blocks : List BusBlock) :
    blockTotal (sideSizes fw blocks) =
      (fw.map (2 ^ ·)).sum + (blocks.map fun b ↦ 2 ^ b.logRows).sum := by
  rw [blockTotal_eq, sideSizes, List.map_append, List.sum_append, List.map_map]
  rfl

theorem sum_flatten_ofFn {α : Type} (f : Fin 6 → List α) (g : α → ℕ) :
    (((List.ofFn f).flatten).map g).sum = ∑ t : Fin 6, ((f t).map g).sum := by
  rw [List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Each table pulls as often as it pushes. -/
theorem length_pySide_pull : ∀ t : Fin 6, (pySide t .pull).length = (pySide t .push).length := by
  decide +kernel

/-- Each table has at least one count column per push, at most. -/
theorem length_countColumns_le :
    ∀ t : Fin 6, (tables.getD t default).countColumns.length ≤ (pySide t .push).length := by
  intro t
  rw [pyCountColumns t, List.length_map]
  revert t
  decide +kernel

/-- Each table pushes. -/
theorem pySide_push_ne_nil : ∀ t : Fin 6, pySide t .push ≠ [] := by
  decide +kernel

theorem total_pull (prog : Program) (s : Sizes) :
    blockTotal (sideSizes (fwLogs prog s) (pullBlocks s)) =
      blockTotal (sideSizes (fwLogs prog s) (pushBlocks s)) := by
  rw [blockTotal_sideSizes, blockTotal_sideSizes, pullBlocks, pushBlocks, sum_flatten_ofFn,
    sum_flatten_ofFn]
  congr 1

theorem total_count_le (prog : Program) (s : Sizes) :
    blockTotal (sideSizes [] (countBlocks s)) ≤
      blockTotal (sideSizes (fwLogs prog s) (pushBlocks s)) := by
  rw [blockTotal_sideSizes, blockTotal_sideSizes, countBlocks, pushBlocks, sum_flatten_ofFn,
    sum_flatten_ofFn]
  simp only [List.map_nil, List.sum_nil, zero_add, List.map_map, Function.comp_def,
    List.map_const', List.sum_replicate, smul_eq_mul]
  refine le_add_left (Finset.sum_le_sum fun t _ ↦ ?_)
  exact Nat.mul_le_mul_right _ (length_countColumns_le t)

theorem total_le_depth (prog : Program) (s : Sizes) :
    blockTotal (sideSizes (fwLogs prog s) (pushBlocks s)) ≤ 2 ^ busDepth prog s :=
  blockTotal_le _

/-- A size whose block is in the push side is at most the depth. -/
theorem le_busDepth (prog : Program) (s : Sizes) {v : ℕ}
    (h : 2 ^ v ≤ blockTotal (sideSizes (fwLogs prog s) (pushBlocks s))) : v ≤ busDepth prog s :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp (h.trans (total_le_depth prog s))

theorem logMem_le_busDepth (prog : Program) (s : Sizes) : s.logMem ≤ busDepth prog s := by
  refine le_busDepth prog s ?_
  rw [blockTotal_sideSizes, fwLogs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero]
  exact le_add_right (le_add_left (le_add_right le_rfl))

theorem logSize_le_busDepth (prog : Program) (s : Sizes) : prog.logSize ≤ busDepth prog s := by
  refine le_busDepth prog s ?_
  rw [blockTotal_sideSizes, fwLogs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero]
  exact le_add_right (le_add_left (le_add_left (le_add_right le_rfl)))

theorem tau_le_busDepth (prog : Program) (s : Sizes) (t : Fin 6) : s.τ t ≤ busDepth prog s := by
  refine le_busDepth prog s ?_
  rw [blockTotal_sideSizes, pushBlocks, sum_flatten_ofFn]
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (pySide_push_ne_nil t)
  have : 2 ^ s.τ t ≤
      (((pySide t .push).map fun c ↦ (⟨s.τ t, s.rows t, c, t⟩ : BusBlock)).map
        fun b ↦ 2 ^ b.logRows).sum := by
    rw [hc]; simp
  exact this.trans (le_add_left (Finset.single_le_sum (f := fun t' : Fin 6 ↦
    (((pySide t' .push).map fun c ↦ (⟨s.τ t', s.rows t', c, t'⟩ : BusBlock)).map
      fun b ↦ 2 ^ b.logRows).sum) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ t)))

variable (s : Sizes)

/-- The blocks of every side are owned by a table at its height. -/
theorem blocks_owned {α : Type} (f : Fin 6 → List α) (g : Fin 6 → α → List Form) :
    ∀ b ∈ (List.ofFn fun t : Fin 6 ↦
        (f t).map fun a ↦ (⟨s.τ t, s.rows t, g t a, t⟩ : BusBlock)).flatten,
      ∃ t : Fin 6, b = ⟨s.τ t, s.rows t, b.coordinates, t⟩ := by
  intro b hb
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hbl
  exact ⟨t, rfl⟩

theorem length_take_of_le {p : List E} {n : ℕ} (h : n ≤ p.length) : (p.take n).length = n := by
  rw [List.length_take]; omega

/-- The forms the bus starts from: every entry is the empty form. -/
theorem forms0_entry (t side : ℕ) :
    ((tables.map fun _ ↦ ([{}, {}, {}] : List Form)).getD t []).getD side {} = {} := by
  have hrow : ∀ r ∈ tables.map fun _ ↦ ([{}, {}, {}] : List Form), r = [{}, {}, {}] := by
    intro r hr
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hr
    rfl
  rw [show (tables.map fun _ ↦ ([{}, {}, {}] : List Form)).getD t [] =
    ((tables.map fun _ ↦ ([{}, {}, {}] : List Form))[t]?).getD [] from List.getD_eq_getElem?_getD]
  rcases h : (tables.map fun _ ↦ ([{}, {}, {}] : List Form))[t]? with _ | r
  · rfl
  · rw [hrow r (List.mem_of_getElem? h), Option.getD_some]
    rcases side with _ | _ | _ | side <;> rfl

theorem forms0_length : (tables.map fun _ ↦ ([{}, {}, {}] : List Form)).length = 6 := rfl

theorem forms0_row :
    ∀ t < 6, ((tables.map fun _ ↦ ([{}, {}, {}] : List Form)).getD t []).length = 3 := by
  intro t ht
  rw [List.getD_eq_getElem _ _ (by simpa [tables] using ht)]
  simp

theorem forms0_deg : FormsDeg2 (tables.map fun _ ↦ ([{}, {}, {}] : List Form)) := by
  intro t side term hterm
  rw [forms0_entry] at hterm
  simp at hterm

/-- Every block of a list owned by a table is owned below six. -/
theorem owner_lt_six {l : List BusBlock}
    (h : ∀ b ∈ l, ∃ t : Fin 6, b = ⟨s.τ t, s.rows t, b.coordinates, t⟩)
    (sels : List E) : ∀ x ∈ List.zip sels l, x.2.owner < 6 := by
  intro x hx
  obtain ⟨t, ht⟩ := h x.2 (List.of_mem_zip hx).2
  rw [ht]; exact t.isLt

/-- The zipped blocks of a side are owned by tables at their heights. -/
theorem zip_owned {l : List BusBlock}
    (h : ∀ b ∈ l, ∃ t : Fin 6, b = ⟨s.τ t, s.rows t, b.coordinates, t⟩)
    (sels : List E) :
    ∀ y ∈ List.zip sels l, ∃ t : Fin 6, y.2 = ⟨s.τ t, s.rows t, y.2.coordinates, t⟩ :=
  fun y hy ↦ h y.2 (List.of_mem_zip hy).2

theorem pushBlocks_owned :
    ∀ b ∈ pushBlocks s, ∃ t : Fin 6, b = ⟨s.τ t, s.rows t, b.coordinates, t⟩ :=
  blocks_owned s _ fun _ c ↦ c

theorem pullBlocks_owned :
    ∀ b ∈ pullBlocks s, ∃ t : Fin 6, b = ⟨s.τ t, s.rows t, b.coordinates, t⟩ :=
  blocks_owned s _ fun _ c ↦ c

theorem countBlocks_owned :
    ∀ b ∈ countBlocks s, ∃ t : Fin 6, b = ⟨s.τ t, s.rows t, b.coordinates, t⟩ :=
  blocks_owned s _ fun _ l ↦ [Form.col l]

variable {s}

theorem busLayout_depth_verifier (prog : Program) (s : Sizes) :
    (busLayout [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
      (verifierLayout prog s).push).depth = busDepth prog s := by
  rw [layout_push, busLayout_depth]
  rfl

end
end LeanVM.Protocol.EndToEnd.Complete
