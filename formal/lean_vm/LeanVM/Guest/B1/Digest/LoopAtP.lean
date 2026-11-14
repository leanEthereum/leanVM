/-
  LeanVM.Guest.B1.Digest.LoopAtP

  A loop helper whose block is atoms placing nothing, placed within its frames by a tree popping its blocks'
  entries in order (`loopA_stepAt`, `loopA_completeAtB` with `relAtInP_of_walk_loop`).
-/

module

public import LeanVM.Guest.B1.Digest.LoopAtB
public import LeanVM.Guest.B1.Main.RelAtInP
public import LeanVM.Guest.B1.Main.MainPops
public import LeanVM.Guest.Budget.BoundedL

/-!
# Loops of atoms, placed with their pops

* `blockPops rd σ ss`: a block of atoms' entries at `σ` (its skeleton spliced, `Main.spliceS`);
* `blockPops_wit`: on a valuation evaluated by `Fwd`, a block whose witness hints are `L`'s stack hints pops their
  oracle's words;
* `LoopBlockInP … bp`: `LoopBlockIn`, the block popping `bp`;
* `loopA_stepAtP`, `loopA_completeAtBP`: `loopA_stepAt`, `loopA_completeAtB` by trees popping the blocks' entries,
  iteration by iteration.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtD CompleteAtDTBR CompleteAtLR completeAtLR_tail Returns DisjL Within
  disj_append within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append spliceS)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds)

@[expose] public section

/-- **A block's entries** at `σ`: its skeleton spliced with no callee. -/
noncomputable def blockPops (rd : Reader) (σ : Val) (ss : List Stmt) : List Pop :=
  spliceS rd σ (ss.filterMap Main.Stmt.popS) []

theorem popS_atoms {ss : List Stmt} (h : ss.all isAtomS = true) : ∀ x ∈ ss.filterMap Main.Stmt.popS, x.isSome := by
  intro x hx
  obtain ⟨st, hst, hx⟩ := List.mem_filterMap.mp hx
  have := List.all_eq_true.mp h st hst
  cases st with
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | witness s d => simp only [Main.Stmt.popS, Option.some.injEq] at hx; rw [← hx]; rfl
      | _ => simp [Main.Stmt.popS] at hx
    | _ => simp [Main.Stmt.popS] at hx
  | _ => simp [isAtomS] at this

theorem spliceS_snoc_none {rd : Reader} {σ : Val} (p : List Pop) :
    ∀ xs : List (Option (String × Dest)), (∀ x ∈ xs, x.isSome) →
      spliceS rd σ (xs ++ [none]) [p] = spliceS rd σ xs [] ++ p
  | [], _ => by simp [spliceS]
  | some (s, d) :: xs, h => by
    simp only [List.cons_append, spliceS, List.cons_append]
    rw [spliceS_snoc_none p xs fun x hx => h x (List.mem_cons_of_mem _ hx)]
  | none :: _, h => by simp at h

/-- **A block of atoms, then a call**: its entries, then the callee's. -/
theorem splice_atoms_call {rd : Reader} {σ : Val} {pre : List Stmt} (hA : pre.all isAtomS = true) (c : V)
    (g : String) (args : List V) (p : List Pop) :
    splice rd σ ((pre ++ [Stmt.callIf c g args]).flatMap (Main.slEvs σ)) ([] ++ [p]) = blockPops rd σ pre ++ p := by
  have hstr : (pre ++ [Stmt.callIf c g args]).all Main.Stmt.straight = true := by
    rw [List.all_append, isAtomS_straight hA]; rfl
  rw [Main.splice_straight _ hstr, List.filterMap_append, List.nil_append]
  exact spliceS_snoc_none p _ (popS_atoms hA)

/-- **The witness hints of an evaluated block**: on a valuation good for an oracle `w`, a block of atoms whose
skeleton is `L`'s stack hints pops their oracle's words. -/
theorem blockPops_wit {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {pre : List Stmt}
    (hg : ∀ a ∈ atomsIn pre, Fwd.Good rd S w σ a) {L : List (String × List V)}
    (hL : pre.filterMap Main.Stmt.popS = L.map fun x => some (x.1, .stack x.2)) :
    blockPops rd σ pre = L.map fun x => (x.1, x.2.map fun v => w v.idx) := by
  have hm : ∀ x ∈ L, ∀ v ∈ x.2, σ v = w v.idx := by
    intro x hx v hv
    have h1 : some (x.1, Dest.stack x.2) ∈ pre.filterMap Main.Stmt.popS := by
      rw [hL]; exact List.mem_map_of_mem hx
    obtain ⟨st, hst, hpop⟩ := List.mem_filterMap.mp h1
    cases st with
    | atom a =>
      cases a with
      | hint hh =>
        cases hh with
        | witness s d =>
          simp only [Main.Stmt.popS, Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          exact hg _ (Da.mem_atomsIn hst) v hv
        | _ => simp [Main.Stmt.popS] at hpop
      | _ => simp [Main.Stmt.popS] at hpop
    | _ => simp [Main.Stmt.popS] at hpop
  unfold blockPops
  rw [hL]
  clear hL
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons, spliceS, Dest.words]
    rw [ih fun y hy => hm y (List.mem_cons_of_mem _ hy), List.map_congr_left (hm x List.mem_cons_self)]

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`LoopBlockIn`, the block popping `bp`.** -/
def LoopBlockInP (κ : ℕ) (fn : Fn) (Lin : Layout) (k : ℕ) (N : E) (rest : List E) (bp : List Pop) : Prop :=
  ∀ rd, LowDef κ rd → MemL rd Lin → ∃ σ : Val, fn.params.map σ = gen ^ k :: N :: rest ∧
    (∀ a ∈ atomsIn (loopPre fn), a.Holds rd σ) ∧
    (∀ q ∈ (loopPre fn).filterMap B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
      RegionL Lin i) ∧
    blockPops rd σ (loopPre fn) = bp

/-- **One step of a loop of atoms, placed with its pops**: the block at `g^k` popping `bp`, then the rest of the
loop popping `pt`. -/
theorem loopA_stepAtP {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hA : (loopPre fn).all isAtomS = true)
    (hU : (atomsIn (loopPre fn)).all atomUnplaced = true) {κ : ℕ} {Lin : Layout} {N : E}
    {rest : List E} {m k : ℕ} (hN : N = gen ^ m) (hm : m < 2 ^ 34) (hkm : k + 1 ≤ m) {bp pt : List Pop}
    (hblk : LoopBlockInP κ fn Lin k N rest bp) {Bd Bd' : ℕ → Prop}
    (hBd : ∀ x, (k + 1 < m → Bd' x) → (k + 1 = m → x = fs f) → Bd (fs f + x))
    (htail : k + 1 < m →
      CompleteAtLR fs cert κ f Lin (gen ^ (k + 1) :: N :: rest) (Returns [])
        (fun rd t => t.pops coreProgram rd = pt) Bd') :
    CompleteAtLR fs cert κ f Lin (gen ^ k :: N :: rest) (Returns [])
      (fun rd t => t.pops coreProgram rd = bp ++ if k + 1 < m then pt else []) Bd := by
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
    unfold LoopBlockInP at hblk
    rw [hpre] at hA hU hblk
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      obtain ⟨n, hn⟩ : ∃ n, fn.params.length = n + 2 := ⟨fn.params.length - 2, by omega⟩
      obtain ⟨Bt, hRest⟩ := completeAtLR_tail (fs := fs) (cert := cert) (g := g) (last := k + 1 = m)
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
      obtain ⟨σ, hp, hat, hload, hbp⟩ := hblk rd hlow hLin
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
      have h := relAtInP_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
        (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (Rt := RegionL Lin)
        (Dt := RegionL []) (fp := fp) (c := cur) (Bt := Bt) (m := nt) (N := 0)
        (args := gen ^ k :: N :: rest) (pss := []) (pt := if k + 1 < m then pt else [])
        coreProgram_wf hf hloop hp hw rfl hev hcalls
        (by
          rw [hal]
          by_cases hlast : k + 1 = m
          · simpa [hlast] using ht
          · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
            rw [ite_eq_left (show k + 1 < m by omega), hargs]; simpa using ht)
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
        (by rw [splice_atoms_call hA, hbp])
      rw [hal] at h
      simpa using h
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-- **A loop of atoms is complete, placed, within its frames, with its pops**: from every counter `g^k` below its
end, by a tree popping the blocks' entries `bp k ..< bp m` in order. -/
theorem loopA_completeAtBP {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hA : (loopPre fn).all isAtomS = true)
    (hU : (atomsIn (loopPre fn)).all atomUnplaced = true) {κ : ℕ} {Lin : Layout} {N : E}
    {rest : List E} {m : ℕ} (hN : N = gen ^ m) (hm : m < 2 ^ 34) {bp : ℕ → List Pop}
    (hblk : ∀ k < m, LoopBlockInP κ fn Lin k N rest (bp k)) :
    ∀ k < m, CompleteAtDTBR fs cert κ f Lin (gen ^ k :: N :: rest) (Returns [])
      (fun rd t => t.pops coreProgram rd = (List.range' k (m - k)).flatMap bp) ((m - k + 1) * fs f) := by
  have key : ∀ t k, k + 1 + t = m → CompleteAtLR fs cert κ f Lin (gen ^ k :: N :: rest)
      (Returns []) (fun rd t' => t'.pops coreProgram rd = (List.range' k (t + 1)).flatMap bp)
      (· ≤ (t + 2) * fs f) := by
    intro t
    induction t with
    | zero =>
      intro k hk
      refine (loopA_stepAtP fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega)) (pt := [])
        (Bd' := fun _ => True) (fun x _ hx => by rw [hx (by omega)]; omega)
        fun h => absurd h (by omega)).mono (fun _ h => h) fun rd t' h => ?_
      rw [h]
      simp
    | succ t ih =>
      intro k hk
      refine (loopA_stepAtP fs cert hf hok hA hU hN hm (by omega) (hblk k (by omega))
        (fun x hx _ => ?_) fun _ => ih (k + 1) (by omega)).mono (fun _ h => h) fun rd t' h => ?_
      · have := hx (by omega)
        rw [show (t + 1 + 2) * fs f = (t + 2) * fs f + fs f by ring]
        omega
      · rw [h, ite_eq_left (show k + 1 < m by omega)]
        conv_rhs => rw [List.range'_succ, List.flatMap_cons]
  intro k hk
  obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
  rw [show k + 1 + t - k + 1 = t + 2 by omega, show k + 1 + t - k = t + 1 by omega]
  exact (key t k rfl).toDTBR

end
end LeanVM.Guest.B1.Digest
