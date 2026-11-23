/-
  LeanVM.Guest.B1.Whir.RoundSound

  A fold round, inline in `open_stacked` (`osRoundCore`), gives `opening_round`'s meaning.
-/

module

public import LeanVM.Guest.B1.Whir.Round
public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Vc

/-!
# The inline fold round, soundly

`GcOk C rd σ`: every inline `grind_check` holding at `σ` passes its proof of work (`gcOk_of`, on a
memory image whose tables hold the windows). `osRoundCore_mean`: the round's statements at `σ`,
its capacity cells `cap` holding `fs`, the zero run's cells past its first zero, give
`MeaningOpeningRound` on the words `fs ++ [cb·g^co, claim, tabs, fold_challenges·g^i,
round_coefs·g^(2i)]` and the capacity after `β`, the cursor five words on and the folded claim.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **Every inline `grind_check` holding at `σ` passes its proof of work.** -/
def GcOk (C : CallRel) (rd : Reader) (σ : Val) : Prop :=
  ∀ (b o : ℕ) (w tabs : V), b ∈ grindBitsDeployed → WinTabs rd (σ tabs) →
    AllOk C rd σ (gcInlineT b o w tabs) → ((σ w).limb 0).lane.toNat % 2 ^ b = 0

theorem renameList_isAtom (r : V → V) :
    ∀ (ss : List Stmt), ss.all Stmt.isAtom = true → (Stmt.renameList r ss).all Stmt.isAtom = true
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Stmt.renameList, List.all_cons, renameList_isAtom r ss h.2, Bool.and_true]
    cases s <;> simp_all [Stmt.rename, Stmt.isAtom]

theorem renameArms_isAtom (r : V → V) : ∀ (arms : List (List Stmt)),
    (arms.all fun a ↦ a.all Stmt.isAtom) = true →
      ((Stmt.renameArms r arms).all fun a ↦ a.all Stmt.isAtom) = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Stmt.renameArms, List.all_cons, renameList_isAtom r a h.1, renameArms_isAtom r as h.2,
      Bool.and_self]

theorem renameList_flat (r : V → V) :
    ∀ (ss : List Stmt), ss.all Stmt.flat = true → (Stmt.renameList r ss).all Stmt.flat = true
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Stmt.renameList, List.all_cons, renameList_flat r ss h.2, Bool.and_true]
    cases s with
    | match_ x arms => exact renameArms_isAtom r arms h.1
    | _ => simp_all [Stmt.rename, Stmt.flat]

theorem gcPre_flat (b : ℕ) : (gcPre b).all Stmt.flat = true := by
  simp only [gcPre, gcHead, gcTailPre, List.all_append, List.all_cons, List.all_nil, Stmt.flat,
    Bool.and_true, Bool.true_and, List.all_eq_true, List.mem_flatten, List.mem_map, List.mem_range]
  rintro s ⟨l, ⟨i, -, rfl⟩, hs⟩
  simp only [gcIterAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem gcInlineT_flat (b o : ℕ) (w tabs : V) : (gcInlineT b o w tabs).all Stmt.flat = true :=
  renameList_flat _ _ (gcPre_flat b)

/-- **Inline grinds pass** on a memory image of `2^κ ≥ 2^11` words. -/
theorem gcOk_of {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ) : GcOk C L.read σ := by
  intro b o w tabs hb ht h
  have hh := (holdsList_flat (C := C) (rd := L.read) (σ := σ) _ (gcInlineT_flat b o w tabs) True
    (fun _ ↦ True)).mpr ⟨h, trivial⟩
  exact (gcInline_sound hκ hκ11 L hb ht hh).1

/-- **A fold round inline gives `opening_round`'s meaning.** -/
theorem osRoundCore_mean (hgc : GcOk C rd σ) (hwt : WinTabs rd (σ (.n osTabs)))
    {b p cb co claim i : ℕ} {cap : List ℕ} {f0 f1 f2 f3 f4 : E}
    (hcap : cap.map (fun j ↦ σ (.n j)) = [f0, f1, f2, f3, f4])
    (hp : σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧ σ (.n (p + 4)) = 0)
    (hok : AllOk C rd σ (osRoundCore b p cb co claim i cap)) :
    MeaningOpeningRound rd
      [f0, f1, f2, f3, f4, σ (.n cb) * gen ^ co, σ (.n claim), σ (.n osTabs),
        σ (.n osFch) * gen ^ i, σ (.n osCoefs) * gen ^ (2 * i)]
      ((List.range 5).map (fun j ↦ σ (.n (osRoundC b + 8 + j))) ++
        [σ (.n cb) * gen ^ co * gen ^ 5, σ (.n (osRoundD b + 9))]) := by
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4, cap = [c0, c1, c2, c3, c4] := by
    match cap, hcap with
    | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcap
  obtain ⟨h0, h1, h2, h3, h4⟩ := hcap
  unfold osRoundCore at hok
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨hrd, hka⟩, hg⟩, hkc⟩ := hok
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.flatten_cons, List.flatten_nil, List.append_nil, allOk_cons, allOk_nil,
    and_true, stmtOk_atom, holds_load, holds_copy, holds_const, osLd, osCp, osCst] at hrd
  obtain ⟨lu, cu, ku, lw, cw, kw, lc0, cc0, kc0, lc1, cc1, kc1⟩ := hrd
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_copy, holds_const,
    osLd, osCp, osCst, osKeccak] at hka
  obtain ⟨kA, ln, cn, kn, kB⟩ := hka
  have G := hgc foldGrind (b + 46) (.n (b + 33 + 1)) (.n osTabs) (by decide) hwt hg
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add,
    osLd, osMul, osAdd, osKeccak] at hkc
  obtain ⟨kC, sα, sα', sβ, m0, a1, a2, m3, a4, a5, m6, a7, m8, a9⟩ := hkc
  set u0 := σ (.n (b + 5))
  set w := σ (.n (b + 8))
  set x0 := σ (.n (b + 11))
  set x1 := σ (.n (b + 14))
  set n2 := σ (.n (b + 30))
  -- the four scalars' permutation
  have oA := (keccakA_perm kA).2.2
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, cu, ku, cw, kw, cc0, kc0,
    cc1, kc1, h0, h1, h2, h3, h4] at oA
  set S1 := permOf [u0, word 0 1, w, word 0 1, x0, word 0 1, x1, word 0 1, f0, f1, f2, f3, f4]
  have oA' : ∀ k (hk : k < 13), σ (.n (b + 17 + k)) = cellsOfState S1 false ⟨k, hk⟩ := fun k hk ↦ by
    simpa [osRun] using outs_eq oA ⟨k, hk⟩ (by simp [osRun, hk])
  -- the nonce's permutation
  have hs2 : rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1] =
      ⟨[f0, f1, f2, f3, f4], [(u0, dsObserve), (w, dsObserve), (x0, dsObserve), (x1, dsObserve)]⟩ := by
    rw [rdS2, absorbAll_four]
  have hN : (rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1]).nonceState n2 =
      permOf [n2, word 0 4, 0, 0, 0, 0, 0, 0, cellsOfState S1 false 8, cellsOfState S1 false 9,
        cellsOfState S1 false 10, cellsOfState S1 false 11, cellsOfState S1 false 12] := by
    rw [hs2]
    simp [Fs.nonceState, Fs.absorb, rateScalars, perm_eq_cells, pendCells, capOf, scalarCells_eq, S1]
    rfl
  have oB := (keccakA_perm kB).2.2
  simp only [List.map_cons, List.map_nil, cn, kn, p1, p2, p3, p4] at oB
  rw [oA' 8 (by decide), oA' 9 (by decide), oA' 10 (by decide), oA' 11 (by decide),
    oA' 12 (by decide)] at oB
  rw [show (⟨8, _⟩ : Fin 13) = 8 from rfl, show (⟨9, _⟩ : Fin 13) = 9 from rfl,
    show (⟨10, _⟩ : Fin 13) = 10 from rfl, show (⟨11, _⟩ : Fin 13) = 11 from rfl,
    show (⟨12, _⟩ : Fin 13) = 12 from rfl, ← hN] at oB
  have oB' : ∀ k (hk : k < 13), σ (.n (b + 33 + k)) =
      cellsOfState ((rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1]).nonceState n2) false ⟨k, hk⟩ := fun k hk ↦ by
    simpa [osRun] using outs_eq oB ⟨k, hk⟩ (by simp [osRun, hk])
  have hb7 : foldGrind ≠ 0 := by decide
  have hfg : _root_.LeanVM.Parameters.Whir.foldGrindingBits = foldGrind := rfl
  obtain ⟨gok, hα, hs3⟩ := grindSqueeze_cells hb7 n2 _ _ (oB' 0 (by decide)) (oB' 1 (by decide)) G
  -- the squeeze of `β`
  have oC := (keccakA_perm kC).2.2
  simp only [List.map_cons, List.map_nil, p1, p2, p3, p4] at oC
  rw [oB' 8 (by decide), oB' 9 (by decide), oB' 10 (by decide), oB' 11 (by decide),
    oB' 12 (by decide)] at oC
  have hsq : ((⟨capOf ((rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1]).nonceState n2), []⟩ : Fs)).perm = permOf ([0, 0, 0, 0, 0, 0, 0, 0] ++ capOf ((rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1]).nonceState n2)) := by
    rw [perm_eq_cells _ (by simp)]; rfl
  have oC' : ∀ k (hk : k < 13), σ (.n (osRoundC b + k)) =
      cellsOfState ((⟨capOf ((rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1]).nonceState n2), []⟩ : Fs)).perm false ⟨k, hk⟩ := by
    intro k hk
    rw [hsq]
    simpa [osRun, capOf] using outs_eq oC ⟨k, hk⟩ (by simp [osRun, hk])
  refine ⟨u0, w, x0, x1, n2, ?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [loadHolds_mul_gen_pow]
    interval_cases k
    · simpa using lu
    · simpa using lw
    · simpa using lc0
    · simpa using lc1
    · simpa using ln
  · simp only [rdG2, hfg, hα, hs3, Fs.squeeze]
    have q0 : σ (.n (osRoundC b)) =
        cellsOfState ((⟨capOf ((rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1]).nonceState n2), []⟩ : Fs)).perm
          false 0 := oC' 0 (by decide)
    have hcapP : capOf ((⟨capOf ((rdS2 [f0, f1, f2, f3, f4] [u0, w, x0, x1]).nonceState n2), []⟩ : Fs)).perm =
        (List.range 5).map (fun j ↦ σ (.n (osRoundC b + 8 + j))) := by
      have e8 : σ (.n (osRoundC b + 8 + 0)) = _ := oC' 8 (by decide)
      have e9 : σ (.n (osRoundC b + 8 + 1)) = _ := oC' 9 (by decide)
      have e10 : σ (.n (osRoundC b + 8 + 2)) = _ := oC' 10 (by decide)
      have e11 : σ (.n (osRoundC b + 8 + 3)) = _ := oC' 11 (by decide)
      have e12 : σ (.n (osRoundC b + 8 + 4)) = _ := oC' 12 (by decide)
      rw [List.range_succ, List.range_succ, List.range_succ, List.range_succ, List.range_succ,
        List.range_zero]
      simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil]
      rw [e8, e9, e10, e11, e12]
      rfl
    refine ⟨hfg ▸ gok, ?_, ?_, ?_, ?_⟩
    · rw [loadHolds_mul_gen_pow, Nat.add_zero]; simpa using sα
    · rw [loadHolds_mul_gen_pow, Nat.add_zero]; simpa using sα'
    · rw [loadHolds_mul_gen_pow, Keccak.challengeOf_cells, ← q0]; simpa using sβ
    · rw [hcapP]
      simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
      refine ⟨trivial, ?_⟩
      rw [a9, a1, m0, m8, a7, a4, a2, m3, m6, a5, Keccak.challengeOf_cells, ← q0]
      simp only [roundClaim]

end
end LeanVM.Guest.B1.Whir
