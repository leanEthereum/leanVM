/-
  LeanVM.Guest.B1.Digest.LoopAtB

  A loop of atoms placing nothing, complete within a bound before the memory: its frame once per
  iteration and once for the phantom tail (`loopA_stepAt`, `loopA_completeAt`, same proofs).
-/

module

public import LeanVM.Guest.B1.Digest.LoopAt
public import LeanVM.Guest.Budget.Bounded

/-!
# Loops of atoms, placed within bounds

`loopA_completeAtB`: `loopA_completeAt` within `(m - k + 1) · fs f` words: one frame per
iteration from `g^k`, one for the call not entered at the end.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtD CompleteAtDTB Returns DisjL Within disj_append within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **One step of a loop of atoms, placed**: the block at `g^k` and the rest of the loop. -/
theorem loopA_stepAtB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hA : (loopPre fn).all isAtomS = true)
    (hU : (atomsIn (loopPre fn)).all atomUnplaced = true) {κ : ℕ} {Lin : Layout} {N : E}
    {rest : List E} {m k : ℕ} (hN : N = gen ^ m) (hm : m < 2 ^ 34) (hkm : k + 1 ≤ m)
    (hblk : LoopBlockIn κ fn Lin k N rest)
    {Bt : ℕ} (hBt : k + 1 = m → fs f ≤ Bt)
    (htail : k + 1 < m →
      CompleteAtDTB fs cert κ f Lin (gen ^ (k + 1) :: N :: rest) (Returns []) (fun _ => True) Bt) :
    CompleteAtDTB fs cert κ f Lin (gen ^ k :: N :: rest) (Returns []) (fun _ => True) (fs f + Bt) := by
  have hloop : coreProgram.loop f = true := by
    have hok' := hok
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨-, hok'⟩ := hok'
    split at hok'
    · rename_i pre c g args hsl
      simp only [Bool.and_eq_true, beq_iff_eq] at hok'
      obtain ⟨hbody, -⟩ := splitLoopF_eq hsl
      rw [Program.loop_of_find? hf, Fn.loop, hbody, fn_name_of_find' hf]
      simp [hok'.1.1.1.1]
    · exact absurd hok' (by simp)
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  split at hok
  · rename_i pre c g args hsl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hgf, hlen⟩, htl⟩, hg⟩, hc⟩ := hok
    subst hgf
    obtain ⟨hbody, -⟩ := splitLoopF_eq hsl
    have hpre : loopPre fn = pre := by simp [loopPre, hsl]
    unfold LoopBlockIn at hblk
    rw [hpre] at hA hU hblk
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      obtain ⟨n, hn⟩ : ∃ n, fn.params.length = n + 2 := ⟨fn.params.length - 2, by omega⟩
      intro fp
      -- the rest of the loop
      obtain ⟨nt, Lt, hnt, hWt, hDt, hRt⟩ : ∃ nt Lt, nt ≤ Bt ∧ Within Lt (fp + fs g) nt ∧ DisjL Lt ∧
          ∀ rd, LowDef κ rd → MemL rd (Lt ++ Lin) →
            if decide (k + 1 ≠ m) = true then
              RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs g) nt g
                (gen ^ (k + 1) :: N :: rest) []
            else nt = fs g := by
        by_cases hlast : k + 1 = m
        · exact ⟨fs g, [], hBt hlast, fun q hq => by simp at hq, List.Pairwise.nil, fun _ _ _ => by
            simp [hlast]⟩
        · obtain ⟨nt, Lt, rt, Lot, hnt, ⟨rfl, rfl⟩, hW, hD, hR⟩ := htail (by omega) (fp + fs g)
          refine ⟨nt, Lt, hnt, by simpa using hW, by simpa using hD, fun rd hl hm => ?_⟩
          simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte]
          exact (hR rd hl (by simpa using hm)).relAtIn
      refine ⟨fs g + nt, Lt, [], [], by omega, ⟨rfl, rfl⟩, by simpa using hWt.mono (by omega) (by omega),
        by simpa using hDt, fun rd hlow hm => ?_⟩
      simp only [List.nil_append] at hm
      obtain ⟨hmt, hLin⟩ := memL_append.mp hm
      have ht := hRt rd hlow (memL_append.mpr ⟨hmt, hLin⟩)
      obtain ⟨σ, hp, hat, hload⟩ := hblk rd hlow hLin
      have hx0 : σ (V.n 0) = gen ^ k := by
        have := congrArg List.head? hp
        rw [hpar, hn, List.range_succ_eq_map] at this
        simpa using this
      have hx1 : σ (V.n 1) = N := by
        have := congrArg (fun l => l.tail.head?) hp
        rw [hpar, hn, List.range_succ_eq_map, List.range_succ_eq_map] at this
        simpa using this
      have hcv : σ c = gen ^ (k + 1) + gen ^ m := by
        rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hx1, hN, gen_pow_mul_gen]
      have hargs : args.map σ = gen ^ (k + 1) :: N :: rest := by
        obtain ⟨a0, rs, rfl⟩ : ∃ a0 rs, args = a0 :: rs := by
          cases args with
          | nil => simp at hlen; omega
          | cons a0 rs => exact ⟨a0, rs, rfl⟩
        simp only [List.headD_cons] at hg
        simp only [List.tail_cons] at htl
        have hps : fn.params.tail.map σ = N :: rest := by
          have := congrArg List.tail hp
          rwa [← List.map_tail] at this
        rw [List.map_cons, genMul_sound hg hat, hx0, htl, hps, gen_pow_mul_gen]
      -- the path
      have hstr : (pre ++ [Stmt.callIf c g args]).all Main.Stmt.straight = true := by
        rw [List.all_append, isAtomS_straight hA]; rfl
      have hw := Main.walk_straight σ [] _ hstr
      rw [show pre ++ [Stmt.callIf c g args] ++ [Stmt.ret []] =
        pre ++ [Stmt.callIf c g args, Stmt.ret []] by simp, ← hbody] at hw
      obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ hstr
      have hfil : ∀ {β : Type} (h : Stmt → Option β), (∀ a, h (.atom a) = none) →
          pre.filterMap h = [] := by
        intro β h hh
        refine List.filterMap_eq_nil_iff.mpr fun s hs => ?_
        have := List.all_eq_true.mp hA s hs
        cases s <;> simp only [isAtomS, Bool.false_eq_true] at this
        exact hh _
      have hpreA : pre.filterMap Main.Stmt.allocSz = [] := by
        refine List.filterMap_eq_nil_iff.mpr fun s hs => ?_
        have h1 := List.all_eq_true.mp hA s hs
        cases s with
        | atom a =>
          have hu := List.all_eq_true.mp hU a (Da.mem_atomsIn hs)
          cases a with
          | hint hh => cases hh <;> first | rfl | simp [atomUnplaced] at hu
          | _ => rfl
        | _ => simp [isAtomS] at h1
      have hpreF : pre.filterMap Main.Stmt.addrS = [] := by
        refine List.filterMap_eq_nil_iff.mpr fun s hs => ?_
        have h1 := List.all_eq_true.mp hA s hs
        cases s with
        | atom a =>
          have hu := List.all_eq_true.mp hU a (Da.mem_atomsIn hs)
          cases a with
          | frameAddr => simp [atomUnplaced] at hu
          | _ => rfl
        | _ => simp [isAtomS] at h1
      have hpreC : pre.filterMap Main.Stmt.callS = [] := hfil _ fun _ => rfl
      have hal : allocs σ ((pre ++ [Stmt.callIf c g args]).flatMap (Main.slEvs σ)) = [] := by
        rw [hpa, List.filterMap_append, hpreA]; rfl
      have htk : decide (σ c ≠ 0) = decide (k + 1 ≠ m) := by
        rw [hcv]
        refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
          fun h he => h ?_⟩
        exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
      have hcalls : calls ((pre ++ [Stmt.callIf c g args]).flatMap (Main.slEvs σ)) =
          [] ++ [⟨g, args, [], decide (k + 1 ≠ m)⟩] := by
        rw [hpc, List.filterMap_append, hpreC]
        simp [Main.Stmt.callS, Main.mkCall, htk]
      have hev : ∀ e ∈ (pre ++ [Stmt.callIf c g args]).flatMap (Main.slEvs σ), e.Holds rd σ := by
        refine slEvs_holds fun s hs => ?_
        rcases List.mem_append.mp hs with hs | hs
        · have := List.all_eq_true.mp hA s hs
          cases s <;> simp only [isAtomS, Bool.false_eq_true] at this
          exact hat _ (Da.mem_atomsIn hs)
        · rw [List.mem_singleton] at hs
          subst hs
          show IsInK (σ c)
          rw [hcv]; exact gen_pow_add_isInK _ _
      have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
        (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (Rt := RegionL Lin)
        (Dt := RegionL []) (fp := fp) (m := nt) (N := 0) (args := gen ^ k :: N :: rest)
        coreProgram_wf hf hloop hp hw rfl hev hcalls
        (by
          by_cases hlast : k + 1 = m
          · simpa [hlast] using ht
          · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
            rw [hargs]; exact ht)
        (by rw [hal, hpd, List.filterMap_append, hpreA]; rfl)
        (fun q hq => by
          rw [hpad, List.filterMap_append, hpreF] at hq
          simp [Main.Stmt.addrS] at hq)
        (by rw [hal]; exact ⟨rfl, fun _ h => h⟩)
        (fun i hi => Or.inl hi)
        (fun A hA' => by
          rw [B1.loadAddrs_straight σ _ hstr, List.filterMap_append] at hA'
          simp only [List.filterMap_cons, List.filterMap_nil, B1.Stmt.loadS, List.append_nil,
            List.mem_map] at hA'
          obtain ⟨q, hq, rfl⟩ := hA'
          obtain ⟨i, hi, hr⟩ := hload q hq
          exact ⟨i, hi, Or.inr (Or.inl hr)⟩)
        (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
      rw [hal] at h
      refine RelAtIn.relAtInT ?_
      simpa using h
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-- **A loop of atoms is complete, placed**, from every counter below its end. -/
theorem loopA_completeAtB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hA : (loopPre fn).all isAtomS = true)
    (hU : (atomsIn (loopPre fn)).all atomUnplaced = true) {κ : ℕ} {Lin : Layout} {N : E}
    {rest : List E} {m : ℕ} (hN : N = gen ^ m) (hm : m < 2 ^ 34)
    (hblk : ∀ k < m, LoopBlockIn κ fn Lin k N rest) :
    ∀ k < m, CompleteAtDTB fs cert κ f Lin (gen ^ k :: N :: rest) (Returns []) (fun _ => True)
      ((m - k + 1) * fs f) := by
  have key : ∀ t k, k + 1 + t = m →
      CompleteAtDTB fs cert κ f Lin (gen ^ k :: N :: rest) (Returns []) (fun _ => True)
        ((t + 2) * fs f) := by
    intro t
    induction t with
    | zero => intro k hk
              have := loopA_stepAtB fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega))
                (Bt := fs f) (fun _ => le_rfl) fun h => absurd h (by omega)
              exact this.mono (by rw [show (0 + 2) * fs f = fs f + fs f by ring]) fun _ h => h
    | succ t ih => intro k hk
                   have := loopA_stepAtB fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega))
                     (Bt := (t + 2) * fs f) (fun h => absurd h (by omega)) fun _ => ih (k + 1) (by omega)
                   exact this.mono (by rw [show (t + 1 + 2) * fs f = fs f + (t + 2) * fs f by ring])
                     fun _ h => h
  intro k hk
  exact (key (m - k - 1) k (by omega)).mono (by rw [show m - k - 1 + 2 = m - k + 1 by omega])
    fun _ h => h

end
end LeanVM.Guest.B1.Digest
