/-
  LeanVM.Guest.B1.Place.OsKidsO

  `OsKids` and `OsKidsB` at an optional bound: the callees in sequence, with or without a words
  bound by name.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsB
public import LeanVM.Guest.B1.Place.HelperAt

/-!
# Callees in sequence at an optional bound

`Bd : Option (String → ℕ)`: no bound, or each callee `f` within `Bk f` words. A callee is
`CompleteAtO … (Bd.map (· f))`, `level_positions` `CompleteAtPO`.

* `os_kids_blockO`: `os_kids_block` / `os_kids_blockB`.
* `OsLvKOkO`, `os_levels_kidsO`: `os_levels_kids` / `os_levels_kidsB`; the total within the calls'
  `max (fs f) (Bk f)` when bounded.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem CompleteAtPO.toP {f : String} {Lin : ℕ → Layout} {args rets : List E} {Lout : ℕ → Layout}
    (h : CompleteAtPO fs cert κ f Lin args rets Lout none) :
    OsCompleteAtP fs cert κ f Lin args rets Lout := fun fp ↦
  let ⟨n, Lown, hW, hD, _, hr⟩ := h fp
  ⟨n, Lown, hW, hD, hr⟩

theorem CompleteAtPO.toPB {f : String} {Lin : ℕ → Layout} {args rets : List E} {Lout : ℕ → Layout}
    {B : ℕ} (h : CompleteAtPO fs cert κ f Lin args rets Lout (some B)) :
    OsCompleteAtPB fs cert κ f Lin args rets Lout B := fun fp ↦
  let ⟨n, Lown, hW, hD, hn, hr⟩ := h fp
  ⟨n, Lown, hW, hD, hn B rfl, hr⟩

/-- **Calls complete on fixed words, within their bounds when given**, placed from `b`. -/
theorem os_kids_blockO (Lk : Layout) (σ : Val) (cs : List Call) (Bd : Option (String → ℕ))
    (hc : ∀ c ∈ cs, c.taken = true →
      CompleteAtO fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bd.map (· c.f)))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout), Within L b N ∧ DisjL L ∧
      (∀ Bk ∈ Bd, N ≤ (cs.map fun c => max (fs c.f) (Bk c.f)).sum) ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
      MemL rd L → MemL rd Lk → (∀ i, RegionL Lk i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b N (fun _ => False) := by
  cases Bd with
  | none =>
    obtain ⟨N, L, hW, hD, hK⟩ := os_kids_block (fs := fs) (cert := cert) κ Lk σ cs
      (fun c hc' ht ↦ (hc c hc' ht).toD) b
    exact ⟨N, L, hW, hD, fun _ h ↦ absurd h (by simp), hK⟩
  | some Bk =>
    obtain ⟨N, L, hW, hD, hN, hK⟩ := os_kids_blockB (fs := fs) (cert := cert) κ Lk σ cs Bk
      (fun c hc' ht ↦ (hc c hc' ht).toB) b
    exact ⟨N, L, hW, hD, fun B h ↦ by simp only [Option.mem_def, Option.some.injEq] at h; subst h; exact hN, hK⟩

/-- `OsLvKOk` at an optional bound. -/
structure OsLvKOkO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (Bd : Option (String → ℕ)) (k : OsLvK) : Prop where
  A : ∀ c ∈ k.A, c.taken = true →
    CompleteAtO fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bd.map (· c.f))
  taken : k.sq.taken = true
  sq : CompleteAtPO fs cert κ k.sq.f (fun p => Lk ++ W p) (k.sq.args.map σ) (k.sq.rets.map σ) S
    (Bd.map (· k.sq.f))
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtO fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ))
      (Bd.map (· c.f))

/-- **The levels' callees in sequence at an optional bound.** -/
theorem os_levels_kidsO (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) (Bd : Option (String → ℕ))
    (ks : List OsLvK) (l0 : ℕ)
    (hok : ∀ i (h : i < ks.length), OsLvKOkO fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) Bd ks[i])
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
      (∀ Bk ∈ Bd, N ≤ ((ks.flatMap OsLvK.calls).map fun c => max (fs c.f) (Bk c.f)).sum) ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
        (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
        (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
        KidsFromIn coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvK.calls) b N (fun _ => False) := by
  cases Bd with
  | none =>
    obtain ⟨N, L, ps, hps, hW, hD, hK⟩ := os_levels_kids (fs := fs) (cert := cert) κ σ Lk W S ks l0
      (fun i h ↦ let o := hok i h
        ⟨fun c hc ht ↦ (o.A c hc ht).toD, o.taken, o.sq.toP, fun p c hc ht ↦ (o.B p c hc ht).toD⟩) b
    exact ⟨N, L, ps, hps, hW, hD, fun _ h ↦ absurd h (by simp), hK⟩
  | some Bk =>
    obtain ⟨N, L, ps, hps, hW, hD, hN, hK⟩ := os_levels_kidsB (fs := fs) (cert := cert) κ σ Lk W S Bk
      ks l0 (fun i h ↦ let o := hok i h
        ⟨fun c hc ht ↦ (o.A c hc ht).toB, o.taken, o.sq.toPB, fun p c hc ht ↦ (o.B p c hc ht).toB⟩) b
    exact ⟨N, L, ps, hps, hW, hD, fun B h ↦ by simp only [Option.mem_def, Option.some.injEq] at h; subst h; exact hN, hK⟩

end
end LeanVM.Guest.B1
