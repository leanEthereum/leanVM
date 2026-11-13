/-
  LeanVM.Guest.B1.Da.ColLoopAt

  `da_verify`'s column loop `da_verify_loop1` (G:4297-4298) placed, by trees of its honest shape,
  within its words bound before the memory, for the budget.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.DvBound
public import LeanVM.Guest.B1.Da.AtT
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.Data.NameStrings

/-!
# The column loop, within its bound

`da_verify_loop1(xb, …)` (`l18Body`): column `log xb` (`da_verify_column` on the loop's seven
words), then the next counter `xb·g` and the tail call while `xb·g ≠ g^128`.

* `l18σ k ps`: its valuation at the counter `g^k`, `ps` the other six words.
* `l18NH k Tc Tt`: an iteration's honest shape: a node at the counter `g^k` whose column is by a
  tree of `Tc`, whose tail call (taken unless `k + 1 = 128`) by a tree of `Tt`.
* `l18From Tc t k`: `t` iterations from `k`, each of that shape (`False` past the last).
* `l18_stepAtTB`, `l18_completeAtTB`: one iteration, and the loop from every `k < 128`, within
  `clB fs "da_verify_loop1" Bc (128 - k)` when every column is within `Bc` by a tree of `Tc`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtDTB Returns DisjL Within disj_append within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-- `da_verify_loop1`'s statements before its `ret`. -/
def l18Pre : List Stmt := l18Body.dropLast

theorem l18Body_split : l18Body = l18Pre ++ [.ret []] := rfl

theorem l18Pre_straight : l18Pre.all Main.Stmt.straight = true := rfl

theorem find_l18 : coreProgram.find? name% «da_verify_loop1» = some (coreProgram.getD
    idx% «da_verify_loop1» default) :=
  find_of_idx dv_loops_idx.2.1

theorem l18_body : Fn.body (coreProgram.getD idx% «da_verify_loop1» default) = l18Body := by
  have h := l18_ok
  simp only [l18Ok, Bool.and_eq_true] at h
  exact stmtsEqb_sound h.2

theorem l18_params : (coreProgram.getD idx% «da_verify_loop1» default).params = (List.range 7).map
    V.n := by
  have h := l18_ok
  simp only [l18Ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem l18_loop : coreProgram.loop name% «da_verify_loop1» = true := by
  rw [Program.loop_of_find? find_l18, Fn.loop, l18_body, fn_name_of_find find_l18]
  simp [l18Body]

/-- `da_verify_loop1`'s valuation at the counter `g^k`. -/
def l18σ (k : ℕ) (ps : List E) : Val :=
  Val.ofArgs ([gen ^ k] ++ ps ++ [word 2 0, gen ^ k * word 2 0, word 325 0,
    gen ^ k * word 2 0 + word 325 0, word 2 0, gen ^ k * word 2 0])

/-- An iteration's calls: the column, then the tail call, taken unless `k + 1 = 128`. -/
def l18Calls (k : ℕ) : List Call :=
  [⟨"da_verify_column", (List.range 7).map V.n, [], true⟩] ++
    [⟨name% «da_verify_loop1», .n 12 :: (List.range 6).map fun i => V.n (i + 1), [],
        decide (k + 1 ≠ 128)⟩]

/-- **An iteration's honest shape.** -/
def l18NH (k : ℕ) (Tc Tt : Tree → Prop) : Tree → Prop :=
  NodeHonest coreProgram name% «da_verify_loop1» (fun σ => σ (.n 0) = gen ^ k) (fun _ => l18Calls k)
    (fun _ => []) [Tc, Tt]

/-- **`t` iterations from `k`**, each of its honest shape; none (`False`) past the last, so the last
iteration's tail call is not taken. -/
def l18From (Tc : Tree → Prop) : ℕ → ℕ → Tree → Prop
  | 0, _ => fun _ => False
  | t + 1, k => l18NH k Tc (l18From Tc t (k + 1))

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
/-- **One iteration of the column loop, placed, by a tree of its honest shape.** -/
theorem l18_stepAtTB {Bc Bt : ℕ} {Tc Tt : Tree → Prop} {ps : List E} (hps : ps.length = 6)
    {Lin : Layout} {k : ℕ} (hk : k + 1 ≤ 128)
    (hcol : CompleteAtDTB fs cert 16 "da_verify_column" Lin (gen ^ k :: ps) (Returns []) Tc Bc)
    (htail : k + 1 < 128 →
      CompleteAtDTB fs cert 16 name% «da_verify_loop1» Lin (gen ^ (k + 1) :: ps) (Returns []) Tt Bt)
    (hBt : fs name% «da_verify_loop1» ≤ Bt) :
    CompleteAtDTB fs cert 16 name% «da_verify_loop1» Lin (gen ^ k :: ps) (Returns []) (l18NH k Tc
        Tt)
      (fs name% «da_verify_loop1» + Bt + Bc) := by
  intro fp
  -- the rest of the loop
  obtain ⟨nt, Lt, hnt, hWt, hDt, hRt⟩ : ∃ nt Lt, nt ≤ Bt ∧ Within Lt (fp + fs
      name% «da_verify_loop1») nt ∧
      DisjL Lt ∧ ∀ rd, B1.LowDef 16 rd → MemL rd (Lt ++ Lin) →
        if decide (k + 1 ≠ 128) = true then
          RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs
              name% «da_verify_loop1») nt
            name% «da_verify_loop1» (gen ^ (k + 1) :: ps) [] Tt
        else nt = fs name% «da_verify_loop1» := by
    by_cases hlast : k + 1 = 128
    · exact ⟨fs name% «da_verify_loop1», [], hBt, fun q hq => by simp at hq, List.Pairwise.nil,
                                                                   fun _ _ _ => by
        simp [hlast]⟩
    · obtain ⟨nt, Lt, rt, Lot, hntB, ⟨rfl, rfl⟩, hW, hD, hR⟩ := htail (by omega) (fp + fs
                                                                            name% «da_verify_loop1»)
      refine ⟨nt, Lt, hntB, by simpa using hW, by simpa using hD, fun rd hl hm => ?_⟩
      simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte]
      exact hR rd hl (by simpa using hm)
  -- the column
  obtain ⟨nc, Lc, rc, Loc, hncB, ⟨rfl, rfl⟩, hWc, hDc, hRc⟩ := hcol (fp + fs
      name% «da_verify_loop1» + nt)
  simp only [List.nil_append] at hWc hDc hRc
  refine ⟨fs name% «da_verify_loop1» + nt + nc, Lt ++ Lc, [], [], by omega, ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append hDt hDc hWt hWc le_rfl, fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWt.mono (by omega) (by omega), hWc.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := memL_append.mp hm
  obtain ⟨hmt, hmc⟩ := memL_append.mp hm1
  have ht := hRt rd hlow (memL_append.mpr ⟨hmt, hLin⟩)
  have hc := hRc rd hlow (memL_append.mpr ⟨hmc, hLin⟩)
  obtain ⟨p1, p2, p3, p4, p5, p6, rfl⟩ : ∃ p1 p2 p3 p4 p5 p6, ps = [p1, p2, p3, p4, p5, p6] := by
    match ps, hps with
    | [p1, p2, p3, p4, p5, p6], _ => exact ⟨p1, p2, p3, p4, p5, p6, rfl⟩
  -- the path
  set σ := l18σ k [p1, p2, p3, p4, p5, p6] with hσ
  have hw' := Main.walk_straight σ [] l18Pre l18Pre_straight
  rw [← l18Body_split, ← l18_body] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ l18Pre_straight
  have h10 : σ (.n 10) = gen ^ (k + 1) + gen ^ 128 := by
    show gen ^ k * word 2 0 + word 325 0 = _
    rw [word_gen, gen_pow_mul_gen, word_g128]
  have htk : decide (σ (.n 10) ≠ 0) = decide (k + 1 ≠ 128) := by
    rw [h10]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by norm_num) (e_add_eq_zero_iff.mp he)
  have hcalls : calls (l18Pre.flatMap (Main.slEvs σ)) = l18Calls k := by
    rw [hpc, show l18Pre.filterMap Main.Stmt.callS =
      [(none, "da_verify_column", (List.range 7).map V.n, []),
        (some (.n 10), name% «da_verify_loop1», .n 12 :: (List.range 6).map fun k => V.n (k + 1),
            [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, htk, l18Calls, List.cons_append,
      List.nil_append]
  have hal : allocs σ (l18Pre.flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show l18Pre.filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have hev : ∀ e ∈ l18Pre.flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    simp only [l18Pre, l18Body, List.dropLast, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, l18σ, ofArgs_n, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [word_gen, gen_pow_mul_gen, word_g128]
    exact gen_pow_add_isInK _ _
  have hargs : (.n 12 :: (List.range 6).map fun k => V.n (k + 1)).map σ =
      gen ^ (k + 1) :: [p1, p2, p3, p4, p5, p6] := by
    show [gen ^ k * word 2 0, p1, p2, p3, p4, p5, p6] = _
    rw [word_gen, gen_pow_mul_gen]
  have h := relAtInWT_of_walk_loop (P := coreProgram) (Ts := [Tc]) (Tt := Tt) (fs := fs)
    (cert := cert) (σ := σ) (rd := rd) (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False)
    (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp) (m := nt) (N := nc)
    (args := gen ^ k :: [p1, p2, p3, p4, p5, p6]) coreProgram_wf find_l18 l18_loop
    (by rw [l18_params]; rfl) hw' rfl hev (by rw [hcalls]; rfl)
    (by
      by_cases hlast : k + 1 = 128
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [hargs]; exact ht)
    (by rw [hal, hpd, show l18Pre.filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show l18Pre.filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    rfl
    (by
      rw [hal]
      refine ⟨nc, 0, RegionL Lin, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), ?_,
        ⟨rfl, fun i hi => hi.elim⟩⟩
      simp only [ite_true, List.sum_nil, Nat.add_zero]
      exact relAtInT_dmono hc fun _ h => h.elim)
    (fun i hi => Or.inl hi)
    (fun A hA => by
      rw [B1.loadAddrs_straight σ _ l18Pre_straight,
        show l18Pre.filterMap B1.Stmt.loadS = [] from rfl] at hA
      simp at hA)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  have h' := relAtInT_nodeHonest (Q := fun σ => σ (.n 0) = gen ^ k)
    (cs := fun _ => l18Calls k) (bs := fun _ => []) (Ts := [Tc, Tt]) h find_l18 hw' rfl
    (by rw [hcalls]) hal (by simp [l18Calls])
  rw [hal] at h'
  simp only [List.sum_nil, Nat.add_zero] at h'
  exact h'

/-- **The column loop is complete, placed, by trees of its honest shape** (`l18From`), from every
counter `a ≤ k < 128`, **within `clB`**, when its columns are by trees of `Tc` within `Bc`. -/
theorem l18_completeAtTB {Bc : ℕ} {Tc : Tree → Prop} {ps : List E} (hps : ps.length = 6)
    {Lin : Layout} {a : ℕ}
    (hcol : ∀ k, a ≤ k → k < 128 →
      CompleteAtDTB fs cert 16 "da_verify_column" Lin (gen ^ k :: ps) (Returns []) Tc Bc) :
    ∀ k, a ≤ k → k < 128 →
      CompleteAtDTB fs cert 16 name% «da_verify_loop1» Lin (gen ^ k :: ps) (Returns [])
        (l18From Tc (128 - k) k) (clB fs name% «da_verify_loop1» Bc (128 - k)) := by
  have key : ∀ t k, a ≤ k → k + 1 + t = 128 →
      CompleteAtDTB fs cert 16 name% «da_verify_loop1» Lin (gen ^ k :: ps) (Returns [])
        (l18From Tc (t + 1) k) (clB fs name% «da_verify_loop1» Bc (t + 1)) := by
    intro t
    induction t with
    | zero =>
      intro k hak hk
      have h := l18_stepAtTB (Tt := l18From Tc 0 (k + 1)) (Bt := fs name% «da_verify_loop1») fs
          cert hps
        (by omega) (hcol k hak (by omega)) (fun h => absurd h (by omega)) le_rfl
      exact h.mono (by simp only [clB]; omega) fun _ h => h
    | succ t ih =>
      intro k hak hk
      have h := l18_stepAtTB fs cert hps (by omega) (hcol k hak (by omega))
        (fun _ => ih (k + 1) (by omega) (by omega)) (by simp only [clB]; omega)
      exact h.mono (by simp only [clB]; rw [Nat.add_mul (t + 1) 1]; omega) fun _ h => h
  intro k hak hk
  have := key (128 - k - 1) k hak (by omega)
  rwa [show 128 - k - 1 + 1 = 128 - k by omega] at this

end
end LeanVM.Guest.B1.Da
