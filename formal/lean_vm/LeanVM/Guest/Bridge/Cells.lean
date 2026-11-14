/-
  LeanVM.Guest.Bridge.Cells

  The hint bridge's cells: an ISA hint compiling a core hint atom meets `HintOk` once the frame holds the atom's values at their cells and, for a computed hint, the atom is exact; for every kind of hint.
-/

module

public import LeanVM.Guest.Bridge.Defs
public import LeanVM.Guest.Exact.Defs
public import LeanVM.Prover.ExecuteCompleteHint

/-!
# The hint bridge's cells

`compiles loc h h'` places every operand of the core hint `h` at a cell of `loc`; these lemmas turn it into `HintOk` for the executor's `h'`, kind by kind, from the frame's cells (`st.mem.peek` at an input's cell, the reference `M` at an output's), the stream's next entry for a witness, and the atom's exactness (`Hint.Exact`, which `Tree.Exact` states of every hint on an honest path) for a computed hint.

* Destinations: `DestIn` (the reference holds a destination's words: frame values at their cells, or a buffer's words from its pointer plus the offset), `destOk_run` (then the ISA destination's run holds them), `DestMem` and `destOk_mem` (the same in the executor's memory, which `log2Ceil` reads).
* Witnesses: `hintOk_stack`, `hintOk_heap` (`words_heap`: a buffer's words are read at `g^(b + off + k)`).
* Computed hints: `hintOk_inverse`, `hintOk_limbs`, `hintOk_bits`, `hintOk_bitsExp`, `hintOk_digitsExp`, `hintOk_windowsExp`, `hintOk_log2Ceil`.
* Allocations: `hintOk_alloc`, `hintOk_allocDyn`, `hintOk_allocDyn_static`, from the reference holding `g^nextFree` at the pointer's cell, which the allocation track (`allocOk`, not yet written) is to supply.
* Hint-only cells: `locOf_cert` (the cell map is the certificate's at every value it places), `cellsFresh_lookup` (a hint-only cell is no certificate, header or plumbing cell).
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

/-- **The frame's run of a stack witness holds its values**: from the values at their cells. -/
theorem runOk_stack {loc : ℕ → ℕ} {s s' : String} {vs : List V} {base len : ℕ}
    (h : compiles loc (.witness s (.stack vs)) (.witnessStack s' base len) = true) {M : ℕ → E}
    {fp : ℕ} {σ : Val} (hM : ∀ v ∈ vs, M (fp + loc v.idx) = σ v) (hc : fp + base + len ≤ maxCells)
    (rd : Reader) : RunOk M (fp + base) ((Dest.stack vs).words rd σ) := by
  obtain ⟨-, rfl, hl⟩ := compiles_stack h
  intro k hk
  simp only [Dest.words, List.length_map] at hk ⊢
  refine ⟨by omega, ?_⟩
  rw [List.getElem_map, ← hM _ (List.getElem_mem hk), hl k hk, Nat.add_assoc]

/-- **`HintOk` of a stack witness hint**: the stream's next entry the atom's words, its values at
their cells. -/
theorem hintOk_stack {loc : ℕ → ℕ} {s s' : String} {vs : List V} {base len : ℕ}
    (h : compiles loc (.witness s (.stack vs)) (.witnessStack s' base len) = true) {C : Ctx}
    {M : ℕ → E} {st : St} {σ : Val} {rd : Reader}
    (hn : StreamNext C st s ((Dest.stack vs).words rd σ))
    (hM : ∀ v ∈ vs, M (st.fp + loc v.idx) = σ v) (hc : st.fp + base + len ≤ maxCells) :
    HintOk C M st (.witnessStack s' base len) := by
  obtain ⟨rfl, rfl, -⟩ := compiles_stack h
  exact ⟨_, hn, by simp [Dest.words], runOk_stack h hM hc rd⟩

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

/-- **`HintOk` of a heap witness hint**: the pointer's cell holding `g^b`, the stream's next entry
the atom's words, and the reference holding them from `g^(b + off)`. -/
theorem hintOk_heap {loc : ℕ → ℕ} {s s' : String} {p : V} {off len ptr lo len' : ℕ}
    (h : compiles loc (.witness s (.heap p off len)) (.witnessHeap s' ptr lo len') = true)
    {C : Ctx} {M : ℕ → E} {st : St} {σ : Val} {rd : Reader} {b : ℕ}
    (hp : PtrAt st (st.fp + loc p.idx) b) (hn : StreamNext C st s ((Dest.heap p off len).words rd σ))
    (hr : RunOk M (b + off) ((Dest.heap p off len).words rd σ)) :
    HintOk C M st (.witnessHeap s' ptr lo len') := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := compiles_heap h
  exact ⟨b, _, hp, hn, by simp [Dest.words], hr⟩

/-- **`HintOk` of a computed hint, the inverse**: the input cell holding the input's word, the
destination's holding the output's, and the output the input's inverse (or `0`), as the honest
valuation states of a hint atom on its path. -/
theorem hintOk_inverse {loc : ℕ → ℕ} {x d : V} {x' d' : ℕ}
    (h : compiles loc (.inverse x d) (.inverse x' d') = true) {C : Ctx} {M : ℕ → E} {st : St}
    {σ : Val} (hx : st.mem.peek (st.fp + loc x.idx) = σ x) (hd : M (st.fp + loc d.idx) = σ d)
    (hc : st.fp + loc d.idx < maxCells) (hex : σ d = if σ x = 0 then 0 else (σ x)⁻¹) :
    HintOk C M st (.inverse x' d') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨hc, by rw [hd, hex, hx]⟩


/-! ## Destinations -/

/-- **The reference holds a destination's words**: frame values at their cells, below `maxCells`,
or a buffer's words from its pointer `g^b` plus the offset. -/
def DestIn (loc : ℕ → ℕ) (M : ℕ → E) (st : St) (rd : Reader) (σ : Val) : Dest → Prop
  | .stack vs => ∀ v ∈ vs, st.fp + loc v.idx < maxCells ∧ M (st.fp + loc v.idx) = σ v
  | .heap p off len => ∃ b, PtrAt st (st.fp + loc p.idx) b ∧
      RunOk M (b + off) ((Dest.heap p off len).words rd σ)

/-- **The executor's memory holds a destination's words**: frame values at their cells, or a
buffer's words from its pointer `g^b` plus the offset. -/
def DestMem (loc : ℕ → ℕ) (st : St) (rd : Reader) (σ : Val) : Dest → Prop
  | .stack vs => ∀ v ∈ vs, st.mem.peek (st.fp + loc v.idx) = σ v
  | .heap p off len => ∃ b, PtrAt st (st.fp + loc p.idx) b ∧
      ∀ k < len, st.mem.peek (b + off + k) = ((Dest.heap p off len).words rd σ).getD k 0

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

theorem destOk_len {loc : ℕ → ℕ} {d : Dest} {bd : Prover.Exec.BitsDest} {pos n : ℕ}
    (h : destOk loc d bd pos n = true) (rd : Reader) (σ : Val) : (d.words rd σ).length = n := by
  cases d <;> cases bd <;> simp_all [destOk, Dest.words]

/-- **A compiled destination's run holds the words the reference holds at its cells.** -/
theorem destOk_run {loc : ℕ → ℕ} {d : Dest} {bd : Prover.Exec.BitsDest} {pos n : ℕ}
    (h : destOk loc d bd pos n = true) {M : ℕ → E} {st : St} {rd : Reader} {σ : Val}
    (hd : DestIn loc M st rd σ d) : DestOk st (fun b ↦ RunOk M (b + pos) (d.words rd σ)) bd := by
  cases d with
  | stack vs =>
    cases bd with
    | stack base =>
      simp only [destOk, Bool.and_eq_true, beq_iff_eq] at h
      show RunOk M (st.fp + base + pos) (vs.map σ)
      rw [Nat.add_assoc]
      exact runOk_vals h.2 hd
    | heap ptr => simp [destOk] at h
  | heap p off len =>
    cases bd with
    | stack base => simp [destOk] at h
    | heap ptr =>
      simp only [destOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact hd

/-- **A compiled destination's run, in the executor's memory, holds the words it holds at its
cells.** -/
theorem destOk_mem {loc : ℕ → ℕ} {d : Dest} {bd : Prover.Exec.BitsDest} {pos n : ℕ}
    (h : destOk loc d bd pos n = true) {st : St} {rd : Reader} {σ : Val}
    (hd : DestMem loc st rd σ d) :
    DestOk st (fun b ↦ ∀ k < n, st.mem.peek (b + pos + k) = (d.words rd σ).getD k 0) bd := by
  cases d with
  | stack vs =>
    cases bd with
    | stack base =>
      simp only [destOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hc⟩ := h
      intro k hk
      have hv := hd _ (List.getElem_mem hk)
      rw [consecutive_get hc k hk] at hv
      rw [Dest.words, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
        Option.map_some, Option.getD_some, ← hv]
      congr 1
      omega
    | heap ptr => simp [destOk] at h
  | heap p off len =>
    cases bd with
    | stack base => simp [destOk] at h
    | heap ptr =>
      simp only [destOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact hd

/-! ## Computed hints -/

/-- **`HintOk` of `limbs`**: the input at its cell, the limbs at theirs, the atom exact. -/
theorem hintOk_limbs {loc : ℕ → ℕ} {x : V} {ds : List V} {x' base len : ℕ}
    (h : compiles loc (.limbs x ds) (.fieldLimbs x' base len) = true) {C : Ctx} {M : ℕ → E}
    {st : St} {rd : Reader} {σ : Val} (hx : st.mem.peek (st.fp + loc x.idx) = σ x)
    (hd : DestIn loc M st rd σ (.stack ds)) (hex : (Core.Hint.limbs x ds).Exact rd σ) :
    HintOk C M st (.fieldLimbs x' base len) := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, hc⟩ := h
  have hr := runOk_vals hc hd
  simp only [Core.Hint.Exact] at hex
  rw [hex, ← hx] at hr
  exact hr

/-- **`HintOk` of `bits`**: the input at its cell, the destination's words at theirs, the atom
exact. -/
theorem hintOk_bits {loc : ℕ → ℕ} {v : V} {start nbits : ℕ} {d : Dest} {x : ℕ}
    {bd : Prover.Exec.BitsDest} {n : ℕ}
    (h : compiles loc (.bits v start nbits d) (.bitDecompose x bd n) = true) {C : Ctx} {M : ℕ → E}
    {st : St} {rd : Reader} {σ : Val} (hv : st.mem.peek (st.fp + loc v.idx) = σ v)
    (hd : DestIn loc M st rd σ d) (hex : (Core.Hint.bits v start nbits d).Exact rd σ) :
    HintOk C M st (.bitDecompose x bd n) := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hd'⟩ := h
  simp only [Core.Hint.Exact, Nat.zero_add] at hex
  simp only [HintOk]
  refine destOk_mono (fun b hb ↦ ?_) (destOk_run hd' hd)
  rwa [Nat.add_zero, hex, ← hv] at hb

/-- **`HintOk` of `bitsExp`**: the input at its cell, the destination's words at theirs, the atom
exact. -/
theorem hintOk_bitsExp {loc : ℕ → ℕ} {v : V} {nbits : ℕ} {d : Dest} {x : ℕ}
    {bd : Prover.Exec.BitsDest} {n : ℕ}
    (h : compiles loc (.bitsExp v nbits d) (.bitDecomposeExp x bd n) = true) {C : Ctx} {M : ℕ → E}
    {st : St} {rd : Reader} {σ : Val} (hv : st.mem.peek (st.fp + loc v.idx) = σ v)
    (hd : DestIn loc M st rd σ d) (hex : (Core.Hint.bitsExp v nbits d).Exact rd σ) :
    HintOk C M st (.bitDecomposeExp x bd n) := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, h62⟩, hd'⟩ := h
  obtain ⟨m, hm, hσ, hw⟩ := hex
  refine ⟨h62, m, ⟨by rw [hv, hσ], hm⟩, destOk_mono (fun b hb ↦ ?_) (destOk_run hd' hd)⟩
  rwa [Nat.add_zero, hw] at hb

/-- **`HintOk` of `digitsExp`**: the input and the start cell at their cells, the destination's
words at theirs, the atom exact. -/
theorem hintOk_digitsExp {loc : ℕ → ℕ} {v : V} {nbits ndigits digitBits start : ℕ}
    {sc : Option V} {d : Dest} {x : ℕ} {bd : Prover.Exec.BitsDest}
    {nbits' ndigits' digitBits' start' : ℕ} {sc' : Option ℕ}
    (h : compiles loc (.digitsExp v nbits ndigits digitBits start sc d)
      (.digitDecomposeExp x bd nbits' ndigits' digitBits' start' sc') = true) {C : Ctx}
    {M : ℕ → E} {st : St} {rd : Reader} {σ : Val} (hv : st.mem.peek (st.fp + loc v.idx) = σ v)
    (hs : ∀ c, sc = some c → st.mem.peek (st.fp + loc c.idx) = σ c)
    (hd : DestIn loc M st rd σ d) (hex : (Core.Hint.digitsExp v nbits ndigits digitBits start sc d).Exact rd σ) :
    HintOk C M st (.digitDecomposeExp x bd nbits' ndigits' digitBits' start' sc') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, h62⟩, hsc⟩, hd'⟩ := h
  obtain ⟨m, s, hm, hσ, hst, hw⟩ := hex
  refine ⟨h62, m, s, ⟨by rw [hv, hσ], hm⟩, ?_, destOk_mono (fun b hb ↦ ?_) (destOk_run hd' hd)⟩
  · cases sc with
    | none => cases sc' with
      | none => exact hst
      | some _ => simp [startOk] at hsc
    | some c => cases sc' with
      | none => simp [startOk] at hsc
      | some c' =>
        simp only [startOk, beq_iff_eq] at hsc
        subst hsc
        exact ⟨by rw [hs c rfl, hst.2], hst.1⟩
  · rwa [Nat.add_zero, hw] at hb

/-- **`HintOk` of `windowsExp`**: the input at its cell, the destination's words at theirs, the
atom exact. -/
theorem hintOk_windowsExp {loc : ℕ → ℕ} {v : V} {start width count : ℕ} {d : Dest} {x : ℕ}
    {bd : Prover.Exec.BitsDest} {pos start' width' count' : ℕ}
    (h : compiles loc (.windowsExp v start width count d) (.windowsExp x bd pos start' width' count') = true)
    {C : Ctx} {M : ℕ → E} {st : St} {rd : Reader} {σ : Val}
    (hv : st.mem.peek (st.fp + loc v.idx) = σ v) (hd : DestIn loc M st rd σ d)
    (hex : (Core.Hint.windowsExp v start width count d).Exact rd σ) :
    HintOk C M st (.windowsExp x bd pos start' width' count') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hd'⟩ := h
  simp only [Core.Hint.Exact] at hex
  simp only [HintOk]
  refine destOk_mono (fun b hb ↦ ?_) (destOk_run hd' hd)
  rwa [hex, ← hv] at hb

/-- `log2Ceil`'s read of the bits at `b` is `⌈log₂⌉` of the integer of the words there. -/
theorem log2CeilOf_eq {m : Prover.Exec.Mem} {b n : ℕ} {ws : List E}
    (h : ∀ k < n, m.peek (b + k) = ws.getD k 0) : log2CeilOf m b n = clog2 (bitsNat ws n) := by
  unfold log2CeilOf clog2 bitsNat
  rw [List.foldl_ext _ _ _ fun a j hj ↦ by rw [h j (List.mem_range.mp hj)]]

/-- **`HintOk` of `log2Ceil`**: the bits at their cells in the executor's memory, the output at
its cell, the atom exact. -/
theorem hintOk_log2Ceil {loc : ℕ → ℕ} {b : Dest} {nbits floor : ℕ} {dst : V}
    {bd : Prover.Exec.BitsDest} {dst' nbits' floor' : ℕ}
    (h : compiles loc (.log2Ceil b nbits floor dst) (.log2Ceil bd dst' nbits' floor') = true)
    {C : Ctx} {M : ℕ → E} {st : St} {rd : Reader} {σ : Val} (hb : DestMem loc st rd σ b)
    (hdst : st.fp + loc dst.idx < maxCells) (hM : M (st.fp + loc dst.idx) = σ dst)
    (hex : (Core.Hint.log2Ceil b nbits floor dst).Exact rd σ) :
    HintOk C M st (.log2Ceil bd dst' nbits' floor') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hd', rfl⟩, rfl⟩, rfl⟩ := h
  simp only [Core.Hint.Exact] at hex
  show DestOk st (fun a ↦ st.fp + loc dst.idx < maxCells ∧ M (st.fp + loc dst.idx) =
    ofK (g ^ max (log2CeilOf st.mem a nbits) floor)) bd
  refine destOk_mono (fun a ha ↦ ⟨hdst, ?_⟩) (destOk_mem hd' hb)
  rw [hM, hex, log2CeilOf_eq (fun k hk ↦ by simpa using ha k hk)]

/-! ## Allocations -/

/-- **`HintOk` of `alloc`**: the reference holding the bump pointer at the pointer's cell (the
allocation track's fact), the reservation in range. -/
theorem hintOk_alloc {loc : ℕ → ℕ} {d : V} {n p n' : ℕ}
    (h : compiles loc (.alloc d n) (.alloc p n') = true) {C : Ctx} {M : ℕ → E} {st : St}
    (hc : st.fp + loc d.idx < maxCells) (hM : M (st.fp + loc d.idx) = ofK (g ^ st.nextFree))
    (hn : st.nextFree + n < maxCells) : HintOk C M st (.alloc p n') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact .inr ⟨hc, hn, hM⟩

/-- **`HintOk` of `allocDyn`**: the size at its cell, `g^k`, and the reference holding the bump
pointer at the pointer's cell, the reservation in range. -/
theorem hintOk_allocDyn {loc : ℕ → ℕ} {d n : V} {p n' : ℕ}
    (h : compiles loc (.allocDyn d n) (.allocDyn p n') = true) {C : Ctx} {M : ℕ → E} {st : St}
    {σ : Val} {k : ℕ} (hs : st.mem.peek (st.fp + loc n.idx) = σ n) (hk : σ n = ofK (g ^ k))
    (hkc : k < maxCells) (hc : st.fp + loc d.idx < maxCells)
    (hM : M (st.fp + loc d.idx) = ofK (g ^ st.nextFree)) (hn : st.nextFree + k < maxCells) :
    HintOk C M st (.allocDyn p n') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨k, ⟨by rw [hs, hk], hkc⟩, .inr ⟨hc, hn, hM⟩⟩

/-- **`HintOk` of an `allocDyn` compiled to a static `alloc`**: the reference holding the bump
pointer at the pointer's cell, the reservation in range. -/
theorem hintOk_allocDyn_static {loc : ℕ → ℕ} {d n : V} {p sz : ℕ}
    (h : compiles loc (.allocDyn d n) (.alloc p sz) = true) {C : Ctx} {M : ℕ → E} {st : St}
    (hc : st.fp + loc d.idx < maxCells) (hM : M (st.fp + loc d.idx) = ofK (g ^ st.nextFree))
    (hn : st.nextFree + sz < maxCells) : HintOk C M st (.alloc p sz) := by
  simp only [compiles, beq_iff_eq] at h
  subst h
  exact .inr ⟨hc, hn, hM⟩

/-! ## Hint-only cells -/

theorem cellsFresh_lookup {locs plumb : List ℕ} {extra : List (ℕ × ℕ)}
    (h : cellsFresh locs plumb extra = true) {i c : ℕ} (hl : extra.lookup i = some c) :
    locs.getD i 0 < 2 ∧ 2 ≤ c ∧ c ∉ locs ∧ c ∉ plumb := by
  induction extra with
  | nil => simp at hl
  | cons q extra ih =>
    simp only [cellsFresh, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨q1, q2⟩ := q
    by_cases hq : i = q1
    · subst hq
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
      subst hl
      simpa [and_assoc] using h.1
    · rw [List.lookup, show (i == q1) = false from beq_false_of_ne hq] at hl
      exact ih h.2 hl

/-- **The cell map is the certificate's** at every value the certificate places. -/
theorem locOf_cert {locs plumb : List ℕ} {extra : List (ℕ × ℕ)} (h : cellsFresh locs plumb extra = true)
    {i : ℕ} (hi : 2 ≤ locs.getD i 0) : locOf locs extra i = locs.getD i 0 := by
  unfold locOf
  cases hl : extra.lookup i with
  | none => rfl
  | some c => exact absurd (cellsFresh_lookup h hl).1 (by omega)

end

end LeanVM.Guest.Bridge
