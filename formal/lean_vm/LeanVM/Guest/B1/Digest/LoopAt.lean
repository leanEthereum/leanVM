/-
  LeanVM.Guest.B1.Digest.LoopAt

  A loop helper whose block is atoms placing nothing, in the uniform placed form: the rest of the
  loop right after its frame, its block's loads in the caller's words.
-/

module

public import LeanVM.Guest.B1.Digest.PlacedLib
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.B1.Digest.ClaimListCChk
public import LeanVM.Guest.B1.Main.KidsT

/-!
# Loops of atoms, placed

`loopA_completeAt`: a loop helper (`loopShapeF`) whose block is atoms placing nothing is
`CompleteAtD` from every counter `g^k`, `k < m`, to its end `g^m`, when at every counter and on
every memory defined below `2^κ` holding the caller's words `Lin`, some valuation of the block
holds and its loads read `Lin` (its range checks reading below `2^κ` are no loads). The run at
`g^(k+1)` has its frames right after the iteration's (`relAtIn_of_walk_loop`, `CompleteAtL`),
by induction from the end; `loopA_stepAt` takes any bound `Bd` on the words.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtD CompleteAtL completeAtL_tail Returns DisjL Within
  disj_append within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **A block of a loop of atoms at the counter `g^k`**: a valuation of it holds and its loads
read the caller's words. -/
def LoopBlockIn (κ : ℕ) (fn : Fn) (Lin : Layout) (k : ℕ) (N : E) (rest : List E) : Prop :=
  ∀ rd, LowDef κ rd → MemL rd Lin → ∃ σ : Val, fn.params.map σ = gen ^ k :: N :: rest ∧
    (∀ a ∈ atomsIn (loopPre fn), a.Holds rd σ) ∧
    ∀ q ∈ (loopPre fn).filterMap B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧ RegionL Lin i

theorem isAtomS_straight : ∀ {ss : List Stmt}, ss.all isAtomS = true → ss.all Main.Stmt.straight = true
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, isAtomS_straight h.2⟩
    cases s <;> simp_all [isAtomS, Main.Stmt.straight]

theorem fn_name_of_find' {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) :
    fn.name = f := by
  have := List.find?_some h
  simpa using this

/-- **One step of a loop of atoms, placed**: the block at `g^k` and the rest of the loop. -/
theorem loopA_stepAt {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hA : (loopPre fn).all isAtomS = true)
    (hU : (atomsIn (loopPre fn)).all atomUnplaced = true) {κ : ℕ} {Lin : Layout} {N : E}
    {rest : List E} {m k : ℕ} (hN : N = gen ^ m) (hm : m < 2 ^ 34) (hkm : k + 1 ≤ m)
    (hblk : LoopBlockIn κ fn Lin k N rest) {Bd Bd' : ℕ → Prop}
    (hBd : ∀ x, (k + 1 < m → Bd' x) → (k + 1 = m → x = fs f) → Bd (fs f + x))
    (htail : k + 1 < m →
      CompleteAtL fs cert κ f Lin (gen ^ (k + 1) :: N :: rest) (Returns []) (fun _ => True) Bd') :
    CompleteAtL fs cert κ f Lin (gen ^ k :: N :: rest) (Returns []) (fun _ => True) Bd := by
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
      -- the rest of the loop
      obtain ⟨Bt, hRest⟩ := completeAtL_tail (fs := fs) (cert := cert) (g := g) (last := k + 1 = m)
        fun h => htail (by omega)
      refine ⟨fs g + Bt, fun fp cur hc => ?_⟩
      obtain ⟨nt, Lt, hlt, hBdt, hWt, hDt, hRt⟩ := hRest (fp + fs g) cur (by omega)
      refine ⟨nt, Lt, [], [], ?_, ⟨rfl, rfl⟩, by simpa using hWt, by simpa using hDt,
        fun rd hlow hm => ?_⟩
      · rw [Nat.add_assoc]
        refine hBd _ (fun h => hBdt (by omega)) fun h => ?_
        obtain ⟨rfl, rfl⟩ := hlt h
        rfl
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
        (Dt := RegionL []) (fp := fp) (c := cur) (Bt := Bt) (m := nt) (N := 0)
        (args := gen ^ k :: N :: rest)
        coreProgram_wf hf hloop hp hw rfl hev hcalls
        (by
          rw [hal]
          by_cases hlast : k + 1 = m
          · simpa [hlast] using ht
          · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
            rw [hargs]; simpa using ht.relAtInC)
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
      simpa using h.relAtInCT
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-- **A loop of atoms is complete, placed**, from every counter below its end. -/
theorem loopA_completeAt {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hA : (loopPre fn).all isAtomS = true)
    (hU : (atomsIn (loopPre fn)).all atomUnplaced = true) {κ : ℕ} {Lin : Layout} {N : E}
    {rest : List E} {m : ℕ} (hN : N = gen ^ m) (hm : m < 2 ^ 34)
    (hblk : ∀ k < m, LoopBlockIn κ fn Lin k N rest) :
    ∀ k < m, CompleteAtD fs cert κ f Lin (gen ^ k :: N :: rest) (Returns []) := by
  have key : ∀ t k, k + 1 + t = m → CompleteAtL fs cert κ f Lin (gen ^ k :: N :: rest)
      (Returns []) (fun _ => True) (fun _ => True) := by
    intro t
    induction t with
    | zero => intro k hk
              exact loopA_stepAt fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega))
                (Bd' := fun _ => True) (fun _ _ _ => trivial) fun h => absurd h (by omega)
    | succ t ih => intro k hk
                   exact loopA_stepAt fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega))
                     (fun _ _ _ => trivial) fun _ => ih (k + 1) (by omega)
  intro k hk
  exact (key (m - k - 1) k (by omega)).toD

end
end LeanVM.Guest.B1.Digest
