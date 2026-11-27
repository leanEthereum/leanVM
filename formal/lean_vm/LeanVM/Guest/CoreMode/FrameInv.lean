module

public import LeanVM.Guest.CoreMode.FrameFact
public import LeanVM.Guest.Local.Hop

/-!
# The local frame check's invariant

A local certificate names, for each offset `d` of a function, the facts its instruction
establishes (`gens d`), and for each fact an instruction reads, the instruction `d` that
established it. What makes that sound is a run's history, not a state: at an executor state at
offset `i`, the offsets the frame has run since its entry form a list of hops of the layout
(`Layout.Hop`) from `0` to `i`, and every fact established at one of them before `i` holds
(`PathInv`). Then:

* `pathInv_zero`: at the entry, the entry's facts holding.
* `PathInv.wit`: a fact established at an offset `d` whose run's block's range holds `i`, with
  `d < i`, holds: the run passed `d` (`Layout.visits`).
* `PathInv.step`: a hop from `i` to `j`, the memory growing in the same frame, keeps the invariant
  once the facts `i` establishes hold after its step.

The facts are monotone in the memory (`FFact.Holds.mono`): cells written stay written, and the
reference's words do not depend on time.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Guest.Local LeanVM.Guest.Local.Layout
open LeanVM.Guest.Mode (written_mono)

public section

variable {κ : ℕ} {img : MemoryImage κ}

/-- **A fact holds in any larger memory of the same frame.** -/
theorem FFact.Holds.mono {s s' : Prover.Exec.St} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) :
    ∀ {f : FFact}, f.Holds img s → f.Holds img s'
  | .w o, h => by
    show s'.mem.written (s'.fp + o) = true
    rw [hfp]; exact written_mono hle h
  | .q a o, h => fun hl ↦ by
    obtain ⟨p, x, h1, h2, h3⟩ := h hl
    exact ⟨p, x, by rw [hfp]; exact hle.get _ _ h1, h2, written_mono hle h3⟩
  | .nz o, h => by show ∃ v, Rd img s'.fp o = some v ∧ v ≠ 0; rw [hfp]; exact h
  | .s a o, h => by
    show o < hqLim → ∃ p, Rd img s'.fp a = some p ∧ _ ; rw [hfp]; exact h
  | .cp t c, h => by show ∃ v, Rd img s'.fp t = some v ∧ Rd img s'.fp c = some v; rw [hfp]; exact h
  | .one c x, h => by show ∃ v, Rd img s'.fp x = some v ∧ Rd img s'.fp c = some (1 + v); rw [hfp]; exact h
  | .env o v, h => by
    show img.read (g ^ s'.fp * addressOfIndex o) = some (v.val (g ^ s'.fp)); rw [hfp]; exact h
  | .mem a off v, h => by
    show ∃ p, img.read (g ^ s'.fp * addressOfIndex a) = some p ∧ _; rw [hfp]; exact h
  | .ins pc i, h => by show Guest.Holds img pc (g ^ s'.fp) i; rw [hfp]; exact h

/-! ## Paths -/

theorem hops_append {P : ℕ → ℕ → Prop} : ∀ (a : ℕ) (t : List ℕ) (j : ℕ), Hops P a t → P (lastOf a t) j →
    Hops P a (t ++ [j])
  | _, [], _, _, h => ⟨h, trivial⟩
  | _, v :: t, j, ⟨h1, h2⟩, h => ⟨h1, hops_append v t j h2 h⟩

theorem lastOf_append : ∀ (a : ℕ) (t : List ℕ) (j : ℕ), lastOf a (t ++ [j]) = j
  | _, [], _ => rfl
  | _, v :: t, j => lastOf_append v t j

/-- **The invariant at offset `i`**: a list of hops from `0` to `i`, every fact the entry
establishes (`ent`) holding, and every fact an earlier offset of the list establishes. -/
def PathInv (L : Layout) (ent : List FFact) (gens : ℕ → List FFact) (i : ℕ) (s : Prover.Exec.St) : Prop :=
  ∃ t, Hops (Hop L) 0 t ∧ lastOf 0 t = i ∧ (∀ f ∈ ent, f.Holds img s) ∧
    ∀ d ∈ (0 :: t), d ≠ i → ∀ f ∈ gens d, f.Holds img s

variable {L : Layout} {ent : List FFact} {gens : ℕ → List FFact}

theorem pathInv_zero {s : Prover.Exec.St} (h : ∀ f ∈ ent, f.Holds img s) :
    PathInv (img := img) L ent gens 0 s :=
  ⟨[], trivial, rfl, h, fun d hd hne ↦ by simp at hd; exact absurd hd hne⟩

/-- **A fact an earlier offset of the current block's path established holds.** -/
theorem PathInv.wit (hL : L.ok = true) {i : ℕ} {s : Prover.Exec.St} (h : PathInv (img := img) L ent gens i s)
    {d r : ℕ} (hr : L.InRun r d) (hdi : d < i) (hce : i < (L.blk (L.run r).b).ce) {f : FFact} (hf : f ∈ gens d) :
    f.Holds img s := by
  obtain ⟨t, hh, hl, -, hg⟩ := h
  have hv := visits hL hr 0 t hh (Nat.zero_le d) (by rw [hl]; exact hdi) (Or.inr (by rw [hl]; exact hce))
  exact hg d hv (by omega) f hf

theorem PathInv.entHolds {i : ℕ} {s : Prover.Exec.St} (h : PathInv (img := img) L ent gens i s) :
    ∀ f ∈ ent, f.Holds img s :=
  let ⟨_, _, _, he, _⟩ := h; he

/-- **A hop keeps the invariant**, the memory growing in the frame, once the facts `i` establishes
hold after its step. -/
theorem PathInv.step {i j : ℕ} {s s' : Prover.Exec.St} (h : PathInv (img := img) L ent gens i s)
    (hop : Hop L i j) (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) (hi : ∀ f ∈ gens i, f.Holds img s') :
    PathInv (img := img) L ent gens j s' := by
  obtain ⟨t, hh, hl, he, hg⟩ := h
  refine ⟨t ++ [j], hops_append 0 t j hh (by rw [hl]; exact hop), lastOf_append 0 t j,
    fun f hf ↦ (he f hf).mono hle hfp, fun d hd hne f hf ↦ ?_⟩
  by_cases hdi : d = i
  · subst hdi; exact hi f hf
  · have hd' : d ∈ (0 :: t) := by
      rcases List.mem_cons.mp hd with rfl | hd
      · exact List.mem_cons_self
      · rcases List.mem_append.mp hd with hd | hd
        · exact List.mem_cons_of_mem _ hd
        · simp at hd; exact absurd hd hne
    exact (hg d hd' hdi f hf).mono hle hfp

end

end LeanVM.Guest.CoreMode
