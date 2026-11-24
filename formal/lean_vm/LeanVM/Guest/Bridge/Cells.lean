/-
  LeanVM.Guest.Bridge.Cells

  The hint bridge's cells: where a compiled hint's operands sit, and the inverse's `HintOk`.
-/

module

public import LeanVM.Guest.Bridge.Defs
public import LeanVM.Guest.Exact.Defs
public import LeanVM.Prover.ExecuteCompleteHint

/-!
# The hint bridge's cells

`compiles loc h h'` places every operand of the core hint `h` at a cell of `loc`. These are the lemmas `Bridge.PairCells` turns into `HintOk` for the executor's `h'`, kind by kind: where a compiled witness's destination sits (`compiles_stack`, `compiles_heap`, `words_heap`: a buffer's words are read at `g^(b + off + k)`), frame values in consecutive cells as a run (`consecutive_get`, `runOk_vals`), `log2Ceil`'s read of its bits (`log2CeilOf_eq`), and the inverse (`hintOk_inverse`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (Ctx St HintOk StreamNext RunOk maxCells PtrAt DestOk ExpAt AllocOk log2CeilOf
  wordNat bitWord)

public section

/-! ## Witnesses and the inverse -/

theorem consecutive_get {loc : ℕ → ℕ} : ∀ {b : ℕ} {vs : List V}, consecutive loc b vs = true →
    ∀ k (hk : k < vs.length), loc vs[k].idx = b + k
  | _, [], _, _, hk => (Nat.not_lt_zero _ hk).elim
  | b, v :: vs, e, k, hk => by
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at e
    cases k with
    | zero => exact e.1
    | succ k =>
      rw [List.getElem_cons_succ, consecutive_get e.2 k (by simpa using hk)]
      omega

/-- **A witness run into the frame**: the stream, the length, and each value's cell. -/
theorem compiles_stack {loc : ℕ → ℕ} {s s' : String} {vs : List V} {base len : ℕ}
    (h : compiles loc (.witness s (.stack vs)) (.witnessStack s' base len) = true) :
    s' = s ∧ len = vs.length ∧ ∀ k (hk : k < vs.length), loc vs[k].idx = base + k := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.symm, h.1.2.symm, consecutive_get h.2⟩

/-- **A witness run into a buffer**: the stream, the pointer's cell, the offset and the length. -/
theorem compiles_heap {loc : ℕ → ℕ} {s s' : String} {p : V} {off len ptr lo len' : ℕ}
    (h : compiles loc (.witness s (.heap p off len)) (.witnessHeap s' ptr lo len') = true) :
    s' = s ∧ ptr = loc p.idx ∧ lo = off ∧ len' = len := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.symm, h.1.1.2.symm, h.1.2.symm, h.2.symm⟩

/-- **A buffer's words are read at the pointer's cells**: `g^(b + off + k)` for a pointer `g^b`. -/
theorem words_heap {rd : Reader} {σ : Val} {p : V} {off len b : ℕ} (hp : σ p = ofK (g ^ b)) :
    (Dest.heap p off len).words rd σ = (List.range len).map fun k ↦ (rd (g ^ (b + off + k))).getD 0 := by
  simp only [Dest.words, hp]
  refine List.map_congr_left fun k _ ↦ ?_
  simp [addressOfIndex, ← pow_add, Nat.add_assoc]

/-- **`HintOk` of a computed hint, the inverse**: the input cell holding the input's word, the
destination's holding the output's, and the output the input's inverse (or `0`), as the honest
valuation states of a hint atom on its path. -/
theorem hintOk_inverse {loc : ℕ → ℕ} {x d : V} {x' d' : ℕ}
    (h : compiles loc (.inverse x d) (.inverse x' d') = true) {C : Ctx} {M : ℕ → E} {st : St}
    {σ : Val} (hx : st.mem.peek (st.fp + loc x.idx) = σ x) (hxc : st.fp + loc x.idx < maxCells)
    (hd : M (st.fp + loc d.idx) = σ d)
    (hc : st.fp + loc d.idx < maxCells) (hex : σ d = if σ x = 0 then 0 else (σ x)⁻¹) :
    HintOk C M st (.inverse x' d') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨hxc, hc, by rw [hd, hex, hx]⟩

/-! ## Destinations -/

theorem destOk_mono {s : St} {P Q : ℕ → Prop} (hPQ : ∀ b, P b → Q b) :
    ∀ {d : Prover.Exec.BitsDest}, DestOk s P d → DestOk s Q d
  | .stack _, h => hPQ _ h
  | .heap _, ⟨b, hb, hp⟩ => ⟨b, hb, hPQ b hp⟩

/-- Frame values in consecutive cells from `base`, held by the reference, are a run from
`fp + base`. -/
theorem runOk_vals {loc : ℕ → ℕ} {base : ℕ} {vs : List V} (hc : consecutive loc base vs = true)
    {M : ℕ → E} {fp : ℕ} {σ : Val} (hM : ∀ v ∈ vs, fp + loc v.idx < maxCells ∧ M (fp + loc v.idx) = σ v) :
    RunOk M (fp + base) (vs.map σ) := by
  intro k hk
  rw [List.length_map] at hk
  obtain ⟨h1, h2⟩ := hM _ (List.getElem_mem hk)
  rw [consecutive_get hc k hk, ← Nat.add_assoc] at h1 h2
  exact ⟨h1, by rw [List.getElem_map, h2]⟩

/-! ## Computed hints -/

/-- `log2Ceil`'s read of the bits at `b` is `⌈log₂⌉` of the integer of the words there. -/
theorem log2CeilOf_eq {m : Prover.Exec.Mem} {b n : ℕ} {ws : List E}
    (h : ∀ k < n, m.peek (b + k) = ws.getD k 0) : log2CeilOf m b n = clog2 (bitsNat ws n) := by
  unfold log2CeilOf clog2 bitsNat
  rw [List.foldl_ext _ _ _ fun a j hj ↦ by rw [h j (List.mem_range.mp hj)]]

end

end LeanVM.Guest.Bridge
