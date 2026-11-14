/-
  LeanVM.Guest.Bridge.PairCells

  `Bridge.Cells`' computed hints' `HintOk` lemmas over destination predicates whose bodies importers see.
-/

module

public import LeanVM.Guest.Bridge.Cells

/-!
# The computed hints' cells, exposed

`Bridge.Cells` states the reference's and the executor's hold on a destination (`DestIn`, `DestMem`) without exposing them, so no importer can build one; `DestR` and `DestM` are the same predicates, exposed, with the same lemmas (`hintOkR_*`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (Ctx St HintOk StreamNext RunOk maxCells PtrAt DestOk ExpAt AllocOk log2CeilOf
  wordNat bitWord)

public section

/-! ## Destinations -/

/-- **The reference holds a destination's words**: frame values at their cells, below `maxCells`,
or a buffer's words from its pointer `g^b` plus the offset. -/
@[expose] def DestR (loc : ℕ → ℕ) (M : ℕ → E) (st : St) (rd : Reader) (σ : Val) : Dest → Prop
  | .stack vs => ∀ v ∈ vs, st.fp + loc v.idx < maxCells ∧ M (st.fp + loc v.idx) = σ v
  | .heap p off len => ∃ b, PtrAt st (st.fp + loc p.idx) b ∧
      RunOk M (b + off) ((Dest.heap p off len).words rd σ)

/-- **The executor's memory holds a destination's words**: frame values at their cells, or a
buffer's words from its pointer `g^b` plus the offset. -/
@[expose] def DestM (loc : ℕ → ℕ) (st : St) (rd : Reader) (σ : Val) : Dest → Prop
  | .stack vs => ∀ v ∈ vs, st.mem.peek (st.fp + loc v.idx) = σ v
  | .heap p off len => ∃ b, PtrAt st (st.fp + loc p.idx) b ∧
      ∀ k < len, st.mem.peek (b + off + k) = ((Dest.heap p off len).words rd σ).getD k 0

/-- **A compiled destination's run holds the words the reference holds at its cells.** -/
theorem destOk_runR {loc : ℕ → ℕ} {d : Dest} {bd : Prover.Exec.BitsDest} {pos n : ℕ}
    (h : destOk loc d bd pos n = true) {M : ℕ → E} {st : St} {rd : Reader} {σ : Val}
    (hd : DestR loc M st rd σ d) : DestOk st (fun b ↦ RunOk M (b + pos) (d.words rd σ)) bd := by
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
theorem destOk_memR {loc : ℕ → ℕ} {d : Dest} {bd : Prover.Exec.BitsDest} {pos n : ℕ}
    (h : destOk loc d bd pos n = true) {st : St} {rd : Reader} {σ : Val}
    (hd : DestM loc st rd σ d) :
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
theorem hintOkR_limbs {loc : ℕ → ℕ} {x : V} {ds : List V} {x' base len : ℕ}
    (h : compiles loc (.limbs x ds) (.fieldLimbs x' base len) = true) {C : Ctx} {M : ℕ → E}
    {st : St} {rd : Reader} {σ : Val} (hx : st.mem.peek (st.fp + loc x.idx) = σ x)
    (hd : DestR loc M st rd σ (.stack ds)) (hex : (Core.Hint.limbs x ds).Exact rd σ) :
    HintOk C M st (.fieldLimbs x' base len) := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, hc⟩ := h
  have hr := runOk_vals hc hd
  simp only [Core.Hint.Exact] at hex
  rw [hex, ← hx] at hr
  exact hr

/-- **`HintOk` of `bits`**: the input at its cell, the destination's words at theirs, the atom
exact. -/
theorem hintOkR_bits {loc : ℕ → ℕ} {v : V} {start nbits : ℕ} {d : Dest} {x : ℕ}
    {bd : Prover.Exec.BitsDest} {n : ℕ}
    (h : compiles loc (.bits v start nbits d) (.bitDecompose x bd n) = true) {C : Ctx} {M : ℕ → E}
    {st : St} {rd : Reader} {σ : Val} (hv : st.mem.peek (st.fp + loc v.idx) = σ v)
    (hd : DestR loc M st rd σ d) (hex : (Core.Hint.bits v start nbits d).Exact rd σ) :
    HintOk C M st (.bitDecompose x bd n) := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hd'⟩ := h
  simp only [Core.Hint.Exact, Nat.zero_add] at hex
  simp only [HintOk]
  refine destOk_mono (fun b hb ↦ ?_) (destOk_runR hd' hd)
  rwa [Nat.add_zero, hex, ← hv] at hb

/-- **`HintOk` of `bitsExp`**: the input at its cell, the destination's words at theirs, the atom
exact. -/
theorem hintOkR_bitsExp {loc : ℕ → ℕ} {v : V} {nbits : ℕ} {d : Dest} {x : ℕ}
    {bd : Prover.Exec.BitsDest} {n : ℕ}
    (h : compiles loc (.bitsExp v nbits d) (.bitDecomposeExp x bd n) = true) {C : Ctx} {M : ℕ → E}
    {st : St} {rd : Reader} {σ : Val} (hv : st.mem.peek (st.fp + loc v.idx) = σ v)
    (hd : DestR loc M st rd σ d) (hex : (Core.Hint.bitsExp v nbits d).Exact rd σ) :
    HintOk C M st (.bitDecomposeExp x bd n) := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, h62⟩, hd'⟩ := h
  obtain ⟨m, hm, hσ, hw⟩ := hex
  refine ⟨h62, m, ⟨by rw [hv, hσ], hm⟩, destOk_mono (fun b hb ↦ ?_) (destOk_runR hd' hd)⟩
  rwa [Nat.add_zero, hw] at hb

/-- **`HintOk` of `digitsExp`**: the input and the start cell at their cells, the destination's
words at theirs, the atom exact. -/
theorem hintOkR_digitsExp {loc : ℕ → ℕ} {v : V} {nbits ndigits digitBits start : ℕ}
    {sc : Option V} {d : Dest} {x : ℕ} {bd : Prover.Exec.BitsDest}
    {nbits' ndigits' digitBits' start' : ℕ} {sc' : Option ℕ}
    (h : compiles loc (.digitsExp v nbits ndigits digitBits start sc d)
      (.digitDecomposeExp x bd nbits' ndigits' digitBits' start' sc') = true) {C : Ctx}
    {M : ℕ → E} {st : St} {rd : Reader} {σ : Val} (hv : st.mem.peek (st.fp + loc v.idx) = σ v)
    (hs : ∀ c, sc = some c → st.mem.peek (st.fp + loc c.idx) = σ c)
    (hd : DestR loc M st rd σ d) (hex : (Core.Hint.digitsExp v nbits ndigits digitBits start sc d).Exact rd σ) :
    HintOk C M st (.digitDecomposeExp x bd nbits' ndigits' digitBits' start' sc') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, h62⟩, hsc⟩, hd'⟩ := h
  obtain ⟨m, s, hm, hσ, hst, hw⟩ := hex
  refine ⟨h62, m, s, ⟨by rw [hv, hσ], hm⟩, ?_, destOk_mono (fun b hb ↦ ?_) (destOk_runR hd' hd)⟩
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
theorem hintOkR_windowsExp {loc : ℕ → ℕ} {v : V} {start width count : ℕ} {d : Dest} {x : ℕ}
    {bd : Prover.Exec.BitsDest} {pos start' width' count' : ℕ}
    (h : compiles loc (.windowsExp v start width count d) (.windowsExp x bd pos start' width' count') = true)
    {C : Ctx} {M : ℕ → E} {st : St} {rd : Reader} {σ : Val}
    (hv : st.mem.peek (st.fp + loc v.idx) = σ v) (hd : DestR loc M st rd σ d)
    (hex : (Core.Hint.windowsExp v start width count d).Exact rd σ) :
    HintOk C M st (.windowsExp x bd pos start' width' count') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hd'⟩ := h
  simp only [Core.Hint.Exact] at hex
  simp only [HintOk]
  refine destOk_mono (fun b hb ↦ ?_) (destOk_runR hd' hd)
  rwa [hex, ← hv] at hb

/-- **`HintOk` of `log2Ceil`**: the bits at their cells in the executor's memory, the output at
its cell, the atom exact. -/
theorem hintOkR_log2Ceil {loc : ℕ → ℕ} {b : Dest} {nbits floor : ℕ} {dst : V}
    {bd : Prover.Exec.BitsDest} {dst' nbits' floor' : ℕ}
    (h : compiles loc (.log2Ceil b nbits floor dst) (.log2Ceil bd dst' nbits' floor') = true)
    {C : Ctx} {M : ℕ → E} {st : St} {rd : Reader} {σ : Val} (hb : DestM loc st rd σ b)
    (hdst : st.fp + loc dst.idx < maxCells) (hM : M (st.fp + loc dst.idx) = σ dst)
    (hex : (Core.Hint.log2Ceil b nbits floor dst).Exact rd σ) :
    HintOk C M st (.log2Ceil bd dst' nbits' floor') := by
  simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hd', rfl⟩, rfl⟩, rfl⟩ := h
  simp only [Core.Hint.Exact] at hex
  show DestOk st (fun a ↦ st.fp + loc dst.idx < maxCells ∧ M (st.fp + loc dst.idx) =
    ofK (g ^ max (log2CeilOf st.mem a nbits) floor)) bd
  refine destOk_mono (fun a ha ↦ ⟨hdst, ?_⟩) (destOk_memR hd' hb)
  rw [hM, hex, log2CeilOf_eq (fun k hk ↦ by simpa using ha k hk)]

end

end LeanVM.Guest.Bridge
