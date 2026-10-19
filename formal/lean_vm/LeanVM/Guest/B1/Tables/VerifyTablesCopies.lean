/-
  LeanVM.Guest.B1.Tables.VerifyTablesCopies

  `verify_tables`' copies of its selectors into the tables' `eq_hi`, and the blocks' log-heights
  from `block_kappa`.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesAir
public import LeanVM.Guest.B1.Tables.VerifyTablesSel
public import LeanVM.Guest.B1.Tables.VerifyTablesSpec

/-!
# Copies and log-heights

Each table's `eq_hi` (`vtEqhiVars`) is a copy, through at most two copies, of its block's
selector (`vt_eqhi`): the push and pull blocks of table `t` share the push block's selector,
`3 + pushStart t + k`, the count blocks `37 + countStart t + k`. Block `b`'s log-height is
`vtKs logMem τ b` (`blockKappas`), the push side's `[0, logMem, 18]` and then each block's
owner's height (`vtKs_push`, `vtKs_count`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Copies -/

/-- The copies from the selectors to the `eq_hi`: `(statement, destination, source)`. -/
def vtCopies : List (ℕ × ℕ × ℕ) :=
  [(2, 21, 16), (3, 22, 17), (4, 23, 18),
    (1837, 2105, 2100), (1867, 2134, 2129), (1897, 2163, 2158), (1927, 2192, 2187), (1957, 2221,
    2216), (1987, 2250, 2245), (2017, 2279, 2274), (2047, 2308, 2303), (2077, 2337, 2332),
    (2107, 2366, 2361), (2137, 2395, 2390), (2167, 2424, 2419), (2197, 2453, 2448), (2227, 2482,
    2477), (2257, 2511, 2506), (2287, 2540, 2535), (2317, 2569, 2564), (2347, 2598, 2593),
    (2377, 2627, 2622), (2407, 2656, 2651), (2437, 2685, 2680), (2467, 2714, 2709), (2497, 2743,
    2738), (2527, 2772, 2767), (2557, 2801, 2796), (2587, 2830, 2825), (2617, 2859, 2854),
    (2647, 2888, 2883), (2677, 2917, 2912), (2707, 2946, 2941), (2737, 2975, 2970), (2767, 3004,
    2999), (2797, 3033, 3028), (2827, 3062, 3057), (3226, 3469, 2105), (3231, 3476, 2134),
    (3236, 3483, 2163), (3241, 3490, 2192), (3246, 3497, 2221), (3251, 3504, 2250), (3256, 3511,
    2279), (3261, 3518, 2308), (3266, 3525, 2337), (3271, 3532, 2366), (3276, 3539, 2395),
    (3281, 3546, 2424), (3286, 3553, 2453), (3291, 3560, 2482), (3296, 3567, 2511), (3301, 3574,
    2540), (3306, 3581, 2569), (3311, 3588, 2598), (3316, 3595, 2627), (3321, 3602, 2656),
    (3326, 3609, 2685), (3331, 3616, 2714), (3336, 3623, 2743), (3341, 3630, 2772), (3346, 3637,
    2801), (3351, 3644, 2830), (3356, 3651, 2859), (3361, 3658, 2888), (3366, 3665, 2917),
    (3371, 3672, 2946), (3376, 3679, 2975), (3381, 3686, 3004), (3386, 3693, 3033), (3391, 3700,
    3062), (3425, 3733, 3729), (3455, 3762, 3757), (3485, 3791, 3786), (3515, 3820, 3815),
    (3545, 3849, 3844), (3575, 3878, 3873), (3605, 3907, 3902), (3635, 3936, 3931), (3665, 3965,
    3960), (3695, 3994, 3989), (3725, 4023, 4018), (3755, 4052, 4047), (3785, 4081, 4076),
    (3815, 4110, 4105), (3845, 4139, 4134), (3875, 4168, 4163), (3905, 4197, 4192), (3935, 4226,
    4221), (3965, 4255, 4250), (3995, 4284, 4279), (4025, 4313, 4308), (4055, 4342, 4337),
    (4085, 4371, 4366), (4115, 4400, 4395), (4145, 4429, 4424), (4175, 4458, 4453), (4205, 4487,
    4482), (4235, 4516, 4511)]

theorem vt_copies_ok : vtCopies.all (fun c => stmtsEqb [.atom (.copy (.n c.2.1) (.n c.2.2))]
    ((vtPre.drop c.1).take 1)) = true := by decide +kernel

/-- Follow the copies back from `v`, at most `fuel` of them. -/
def vtResolve : ℕ → ℕ → ℕ
  | 0, v => v
  | fuel + 1, v => match vtCopies.find? (·.2.1 = v) with
    | some c => vtResolve fuel c.2.2
    | none => v

theorem vt_resolve {rd : Reader} {σ : Val} (h : VtHolds rd σ) :
    ∀ fuel v, σ (.n v) = σ (.n (vtResolve fuel v))
  | 0, v => rfl
  | fuel + 1, v => by
    unfold vtResolve
    split
    · next c hc =>
      have hm := List.mem_of_find?_eq_some hc
      have hv : c.2.1 = v := by simpa using List.find?_some hc
      have hok := List.all_eq_true.mp vt_copies_ok c hm
      have := h.atom c.1 (.copy (.n c.2.1) (.n c.2.2)) hok
      simp only [Atom.Holds] at this
      rw [← hv, this]
      exact vt_resolve h fuel c.2.2
    · rfl

/-- The first push block of each table, and its count blocks'. -/
def pushStart : List ℕ := [0, 5, 10, 13, 18, 23]
def countStart : List ℕ := [0, 4, 8, 10, 14, 18]

/-- The selector index of block `k` of table `t` on side `s`. -/
def eqhiSel (t s k : ℕ) : ℕ :=
  if s = 2 then 37 + countStart.getD t 0 + k else 3 + pushStart.getD t 0 + k

theorem vt_eqhi_ok : ∀ t < 6, ∀ s < 3, ∀ k < ((vtEqhiVars.getD t []).getD s []).length,
    vtResolve 2 (((vtEqhiVars.getD t []).getD s []).getD k 0) =
      selVal.getD (eqhiSel t s k) 0 + 23 := by decide +kernel

/-- **The `eq_hi`**: each is its block's selector. -/
theorem vt_eqhi {rd : Reader} {σ : Val} (h : VtHolds rd σ) {t s k : ℕ} (ht : t < 6) (hs : s < 3)
    (hk : k < ((vtEqhiVars.getD t []).getD s []).length) :
    σ (.n (((vtEqhiVars.getD t []).getD s []).getD k 0)) =
      σ (.n (selVal.getD (eqhiSel t s k) 0 + 23)) := by
  rw [vt_resolve h 2, vt_eqhi_ok t ht s hs k hk]

/-- The GKR values' copies. -/
theorem vt_tree_copies {rd : Reader} {σ : Val} (h : VtHolds rd σ) :
    σ (.n 21) = σ (.n 16) ∧ σ (.n 22) = σ (.n 17) ∧ σ (.n 23) = σ (.n 18) := by
  have := vt_resolve h 1
  exact ⟨this 21, this 22, this 23⟩

/-! ## Log-heights -/

/-- Block `b`'s log-height, over `[0, log_mem, τ_0, …, τ_5]` (`blockKappas`). -/
def vtKs (logMem : ℕ) (τ : ℕ → ℕ) (b : ℕ) : ℕ :=
  (0 :: logMem :: (List.range 6).map τ).getD (blockKappaSrc.getD b 0) 0 + blockKappaAdj.getD b 0

theorem vt_src_bound : ∀ b < 102, blockKappaSrc.getD b 0 < 8 ∧
    (blockKappaAdj.getD b 0 = 0 ∨ (blockKappaAdj.getD b 0 = 18 ∧ blockKappaSrc.getD b 0 = 0)) := by
  decide +kernel

theorem vtKs_lt {logMem : ℕ} {τ : ℕ → ℕ} (hm : logMem ≤ 32) (hτ : ∀ t < 6, τ t < 29) :
    ∀ b < 102, vtKs logMem τ b < 34 := by
  intro b hb
  obtain ⟨h8, ha⟩ := vt_src_bound b hb
  unfold vtKs
  generalize blockKappaSrc.getD b 0 = s at h8 ha
  rcases ha with ha | ⟨ha, rfl⟩
  · rw [ha, add_zero]
    match s, h8 with
    | 0, _ => simp
    | 1, _ => simpa using (by omega : logMem < 34)
    | s + 2, h8 =>
      have e : (0 :: logMem :: (List.range 6).map τ).getD (s + 2) 0 = τ s := by
        simp [List.getElem?_range (show s < 6 by omega)]
      have := hτ s (by omega); omega
  · rw [ha]; simp

theorem vt_src_push : (List.range 37).map (fun b => (blockKappaSrc.getD b 0, blockKappaAdj.getD b 0)) =
    [(0, 0), (1, 0), (0, 18)] ++ layoutPushOwners.map (fun t => (t + 2, 0)) := by decide +kernel

theorem vt_src_count : (List.range 28).map (fun i => (blockKappaSrc.getD (74 + i) 0,
    blockKappaAdj.getD (74 + i) 0)) = layoutCountOwners.map (fun t => (t + 2, 0)) := by decide +kernel

theorem vt_owners_lt : (∀ t ∈ layoutPushOwners, t < 6) ∧ ∀ t ∈ layoutCountOwners, t < 6 := by
  decide +kernel

theorem vtKs_getD {logMem : ℕ} {τ : ℕ → ℕ} {t : ℕ} (ht : t < 6) :
    (0 :: logMem :: (List.range 6).map τ).getD (t + 2) 0 + 0 = τ t := by
  simp [List.getElem?_range ht]

/-- The push side's log-heights. -/
theorem vtKs_push (logMem : ℕ) (τ : ℕ → ℕ) :
    (List.range 37).map (vtKs logMem τ) = [0, logMem, 18] ++ layoutPushOwners.map τ := by
  have e : (List.range 37).map (vtKs logMem τ) =
      ((List.range 37).map (fun b => (blockKappaSrc.getD b 0, blockKappaAdj.getD b 0))).map
        (fun p => (0 :: logMem :: (List.range 6).map τ).getD p.1 0 + p.2) := by
    rw [List.map_map]; rfl
  rw [e, vt_src_push, List.map_append, List.map_map]
  refine congrArg₂ (· ++ ·) (by simp) (List.map_congr_left fun t ht => ?_)
  exact vtKs_getD (vt_owners_lt.1 t ht)

/-- The count side's log-heights. -/
theorem vtKs_count (logMem : ℕ) (τ : ℕ → ℕ) :
    (List.range 28).map (fun i => vtKs logMem τ (74 + i)) = layoutCountOwners.map τ := by
  have e : (List.range 28).map (fun i => vtKs logMem τ (74 + i)) =
      ((List.range 28).map (fun i => (blockKappaSrc.getD (74 + i) 0,
        blockKappaAdj.getD (74 + i) 0))).map
        (fun p => (0 :: logMem :: (List.range 6).map τ).getD p.1 0 + p.2) := by
    rw [List.map_map]; rfl
  rw [e, vt_src_count, List.map_map]
  exact List.map_congr_left fun t ht => vtKs_getD (vt_owners_lt.2 t ht)

/-- **`block_kappa`** holds `g^(vtKs …)`, from `dims_g`. -/
theorem vt_kappas {rd : Reader} {bk : E} {logMem : ℕ} {τ : ℕ → ℕ}
    (h : ReadsAt rd bk (blockKappas (gen ^ logMem) ((List.range 6).map fun t => gen ^ τ t))) :
    ∀ b < 102, LoadHolds rd bk b (gen ^ vtKs logMem τ b) := by
  intro b hb
  have := h b (by simp [blockKappas]; omega)
  simp only [blockKappas, List.getElem_map, List.getElem_range] at this
  convert this using 1
  obtain ⟨h8, -⟩ := vt_src_bound b hb
  unfold vtKs kappaBase
  rw [pow_add]
  congr 1
  generalize blockKappaSrc.getD b 0 = s at h8
  match s, h8 with
  | 0, _ => simp
  | 1, _ => simp
  | s + 2, h8 =>
    simp [List.getElem?_range (show s < 6 by omega)]

end
end LeanVM.Guest.B1.VerifySub
