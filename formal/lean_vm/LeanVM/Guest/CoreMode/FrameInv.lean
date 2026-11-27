module

public import LeanVM.Guest.CoreMode.FrameFact
public import LeanVM.Guest.Local.Arm

/-!
# The local frame check's invariant

A local certificate names, for each offset `d` of a function, the facts its instruction
establishes (`gens d`), and for each fact an instruction reads, the instruction `d` that
established it, or, for a fact every arm of a nested statement establishes, one instruction per
arm. What makes that sound is a run's history, not a state: at an executor state at offset `i`,
the offsets the frame has run since its entry form a list of hops of the layout (`Layout.Hop`),
each an edge `E` of the code, from `0` to `i`, and every fact established at one of them before
`i` holds (`PathInv`). Then:

* `pathInv_zero`: at the entry, the entry's facts holding.
* `PathInv.wit`: a fact established at an offset `d` whose run's block's range holds `i`, with
  `d < i`, holds: the run passed `d` (`Layout.visits`).
* `PathInv.join`: a fact established on each arm's path of a nested statement whose anchor and
  join are on the current path, every edge out of the anchor landing before the join, holds: the
  run between them passed one arm's path (`Layout.arm_passes`).
* `PathInv.step`: a hop that is an edge, from `i` to `j`, the memory growing in the same frame,
  keeps the invariant once the facts `i` establishes hold after its step.

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

theorem hops_mono {P Q : ℕ → ℕ → Prop} (hpq : ∀ a b, P a b → Q a b) :
    ∀ (a : ℕ) (t : List ℕ), Hops P a t → Hops Q a t
  | _, [], _ => trivial
  | _, v :: t, ⟨h1, h2⟩ => ⟨hpq _ _ h1, hops_mono hpq v t h2⟩

theorem lastOf_mem : ∀ (a : ℕ) (t : List ℕ), lastOf a t ∈ a :: t
  | _, [] => List.mem_cons_self
  | _, v :: t => List.mem_cons_of_mem _ (lastOf_mem v t)

/-- Every offset after the first of a list of forward hops is past it. -/
theorem hops_gt {P : ℕ → ℕ → Prop} (hP : ∀ a b, P a b → a < b) :
    ∀ (a : ℕ) (t : List ℕ), Hops P a t → ∀ x ∈ t, a < x
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, v :: t, ⟨h1, h2⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hP _ _ h1
    · exact lt_trans (hP _ _ h1) (hops_gt hP v t h2 x hx)

/-- **The hops between two offsets of a list of forward hops.** -/
theorem hops_seg {P : ℕ → ℕ → Prop} (hP : ∀ a b, P a b → a < b) :
    ∀ (a : ℕ) (t : List ℕ), Hops P a t → ∀ u ∈ a :: t, ∀ k ∈ a :: t, u < k →
      ∃ s, Hops P u s ∧ lastOf u s = k ∧ ∀ x ∈ s, x ∈ a :: t
  | a, [], _, u, hu, k, hk, huk => by simp at hu hk; omega
  | a, v :: t, ⟨h1, h2⟩, u, hu, k, hk, huk => by
    have hgt := hops_gt hP v t h2
    rcases List.mem_cons.mp hu with rfl | hu
    · rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · rcases List.mem_cons.mp hk with rfl | hk'
        · exact ⟨[k], ⟨h1, trivial⟩, rfl, fun x hx ↦ by simp at hx; subst hx; simp⟩
        · obtain ⟨s, hs, hl, hm⟩ := hops_seg hP v t h2 v List.mem_cons_self k hk (hgt k hk')
          exact ⟨v :: s, ⟨h1, hs⟩, hl, fun x hx ↦ by
            rcases List.mem_cons.mp hx with rfl | hx
            · simp
            · exact List.mem_cons_of_mem _ (hm x hx)⟩
    · have hak : k ≠ a := by
        have := hops_gt hP a (v :: t) ⟨h1, h2⟩ u hu; omega
      have hk' : k ∈ v :: t := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h hak
        · exact h
      obtain ⟨s, hs, hl, hm⟩ := hops_seg hP v t h2 u hu k hk' huk
      exact ⟨s, hs, hl, fun x hx ↦ List.mem_cons_of_mem _ (hm x hx)⟩

/-- Tiles of `[y, v)` start at most at its end. -/
theorem tiles_le' {L : Layout} {v : ℕ} : ∀ {y : ℕ} {cs : List ℕ}, tiles L v y cs = true → y ≤ v
  | y, [], h => by simp only [tiles, Nat.beq_eq] at h; omega
  | y, c :: cs, h => by
    simp only [tiles, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    have := tiles_le' h.2; omega

/-- **The invariant at offset `i`**: a list of hops from `0` to `i`, each a hop of the layout and
an edge `E` of the code, every fact the entry establishes (`ent`) holding, and every fact an
earlier offset of the list establishes. -/
def PathInv (L : Layout) (E : ℕ → ℕ → Prop) (ent : List FFact) (gens : ℕ → List FFact) (i : ℕ)
    (s : Prover.Exec.St) : Prop :=
  ∃ t, Hops (fun a b ↦ Hop L a b ∧ E a b) 0 t ∧ lastOf 0 t = i ∧ (∀ f ∈ ent, f.Holds img s) ∧
    ∀ d ∈ (0 :: t), d ≠ i → ∀ f ∈ gens d, f.Holds img s

variable {L : Layout} {E : ℕ → ℕ → Prop} {ent : List FFact} {gens : ℕ → List FFact}

theorem pathInv_zero {s : Prover.Exec.St} (h : ∀ f ∈ ent, f.Holds img s) :
    PathInv (img := img) L E ent gens 0 s :=
  ⟨[], trivial, rfl, h, fun d hd hne ↦ by simp at hd; exact absurd hd hne⟩

/-- An offset whose run's block's range holds `i`, at or before `i`, is on the path. -/
theorem PathInv.mem (hL : L.ok = true) {i : ℕ} {t : List ℕ}
    (hh : Hops (fun a b ↦ Hop L a b ∧ E a b) 0 t) (hl : lastOf 0 t = i)
    {d r : ℕ} (hr : L.InRun r d) (hdi : d ≤ i) (hce : d = i ∨ i < (L.blk (L.run r).b).ce) : d ∈ 0 :: t := by
  rcases hce with rfl | hce
  · exact hl ▸ lastOf_mem 0 t
  rcases Nat.lt_or_ge d i with hlt | hge
  · exact visits hL hr 0 t (hops_mono (fun _ _ h ↦ h.1) 0 t hh) (Nat.zero_le d) (by rw [hl]; exact hlt)
      (Or.inr (by rw [hl]; exact hce))
  · have : d = i := by omega
    exact this ▸ hl ▸ lastOf_mem 0 t

/-- **A fact an earlier offset of the current block's path established holds.** -/
theorem PathInv.wit (hL : L.ok = true) {i : ℕ} {s : Prover.Exec.St} (h : PathInv (img := img) L E ent gens i s)
    {d r : ℕ} (hr : L.InRun r d) (hdi : d < i) (hce : i < (L.blk (L.run r).b).ce) {f : FFact} (hf : f ∈ gens d) :
    f.Holds img s := by
  obtain ⟨t, hh, hl, -, hg⟩ := h
  exact hg d (PathInv.mem hL hh hl hr hdi.le (Or.inr hce)) (by omega) f hf

/-- **A fact every arm of a nested statement establishes holds past its join** (a join fact): the
anchor `u` and the join `j` on the current path, the arms tiling the offsets between them, every
edge out of `u` landing before `j`, and in each arm an offset `d < i` of its own path establishing
`f`. -/
theorem PathInv.join (hL : L.ok = true) {i : ℕ} {s : Prover.Exec.St} (h : PathInv (img := img) L E ent gens i s)
    {u j ru rj : ℕ} {arms : List ℕ} (ht : tiles L j (u + 1) arms = true)
    (hru : L.InRun ru u) (hui : u < i) (hcu : i < (L.blk (L.run ru).b).ce)
    (hrj : L.InRun rj j) (hji : j ≤ i) (hcj : j = i ∨ i < (L.blk (L.run rj).b).ce)
    (hnext : ∀ v, E u v → v < j) {f : FFact}
    (hw : ∀ c ∈ arms, ∃ d r, L.InRun r d ∧ (L.run r).b = c ∧ d < i ∧ f ∈ gens d) : f.Holds img s := by
  obtain ⟨t, hh, hl, -, hg⟩ := h
  have hu := PathInv.mem hL hh hl hru hui.le (Or.inr hcu)
  have hj := PathInv.mem hL hh hl hrj hji hcj
  have huj : u < j := by have := tiles_le' ht; omega
  obtain ⟨sg, hs, hsl, hsm⟩ := hops_seg (fun _ _ h ↦ h.1.1) 0 t hh u hu j hj huj
  cases sg with
  | nil => simp [lastOf] at hsl; omega
  | cons v sg =>
    have hv : v < j := hnext v hs.1.2
    obtain ⟨c, hc, hpass⟩ := arm_passes hL ht (hops_mono (fun _ _ h ↦ h.1) u (v :: sg) hs) hsl hv
    obtain ⟨d, r, hr, hb, hdi, hf⟩ := hw c hc
    exact hg d (hsm d (hpass d r hr hb)) (by omega) f hf

theorem PathInv.entHolds {i : ℕ} {s : Prover.Exec.St} (h : PathInv (img := img) L E ent gens i s) :
    ∀ f ∈ ent, f.Holds img s :=
  let ⟨_, _, _, he, _⟩ := h; he

/-- **A hop that is an edge keeps the invariant**, the memory growing in the frame, once the facts
`i` establishes hold after its step. -/
theorem PathInv.step {i j : ℕ} {s s' : Prover.Exec.St} (h : PathInv (img := img) L E ent gens i s)
    (hop : Hop L i j) (he : E i j) (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp)
    (hi : ∀ f ∈ gens i, f.Holds img s') : PathInv (img := img) L E ent gens j s' := by
  obtain ⟨t, hh, hl, hent, hg⟩ := h
  refine ⟨t ++ [j], hops_append 0 t j hh (by rw [hl]; exact ⟨hop, he⟩), lastOf_append 0 t j,
    fun f hf ↦ (hent f hf).mono hle hfp, fun d hd hne f hf ↦ ?_⟩
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
