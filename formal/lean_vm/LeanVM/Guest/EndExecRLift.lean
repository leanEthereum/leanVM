/-
  LeanVM.Guest.EndExecRLift

  The runs of a lift (`Res.liftB`), sound at the honest frames.
-/

module

public import LeanVM.Guest.EndExecRBlk
public import LeanVM.Guest.EndExecRVk

/-!
# The runs of a lift

A lift of a frame is `[v] = g^k·[u]`, `[u] = g^a`. `lift_rres`: the runs `liftShape` names lie in
theirs: `g^c·P` up to `a` inside `P` up to `a + k` (`c ≤ k`), the point `[u]·P` at `a < a + k`, and
for `k = 1`, `P` up to `a + 1` inside `P` up to `a` and the point at `a`. `LiftAt`: a lift at every
honest frame of its function. `lifts_ok`: `verify_keccak`'s, `y_g = g·pack_g` and
`tau_g = g^4·pack_g` (`vk_vals`, `vk_cells`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (liftB liftShape)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- **A lift at the honest frames** of function `j`: `[u] = g^a` and `[v] = g^(a + k)`. -/
def LiftAt (A : String → FnAl) (j : ℕ) (vu vv : V) (k : ℕ) : Prop :=
  ∀ (r : Ref) (K : Mode.Cert) (i : ℕ) (e : Bridge.Ent), r.Ok → TopAt A r K i e j → ∃ a,
    refMem r.img (e.I.fp + cellJ j vu) = ofK (Parameters.g ^ a) ∧
    refMem r.img (e.I.fp + cellJ j vv) = ofK (Parameters.g ^ (a + k)) ∧ a + k < 2 ^ 62

end

public section

section

variable {M : ℕ → E} {fp : ℕ}

/-- **The runs of a lift** (`liftShape`): on a frame whose `[u]` is `g^a` and `[v]` is `g^(a + k)`. -/
theorem lift_rres {u v k a : ℕ} (hu : M (fp + u) = ofK (Parameters.g ^ a))
    (hv : M (fp + v) = ofK (Parameters.g ^ (a + k))) (hlt : a + k < 2 ^ 62) {x : Mode.Res}
    (hx : liftShape u v k x = true) : RRes M fp x := by
  have iu : RIdx M fp (.ex (.fr u) 0) a := ⟨_, a, hu, rfl, by omega, rfl⟩
  have iv : RIdx M fp (.ex (.fr v) 0) (a + k) := ⟨_, a + k, hv, rfl, hlt, rfl⟩
  have eu := ridx_ex_fr hu (by omega)
  have ev := ridx_ex_fr hv hlt
  match x, hx with
  | .sub ⟨⟨afp, ak, abs⟩, alo, ahi, aS, ad⟩ [⟨⟨bfp, bk, bbs⟩, blo, bhi, bS, bd⟩], hx =>
    simp only [liftShape, decide_eq_true_eq] at hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩ := hx
    show RSub M fp _ _
    rcases h with ⟨hk, rfl, rfl⟩ | ⟨hk, rfl, hbs, rfl⟩
    · refine ⟨0, a, rfl, iu, fun vq hvq jj _ hj ↦ ⟨_, List.mem_singleton_self _,
        fun vb ylo yhi hvb hlo hhi ↦ ⟨jj + ak, ?_, ?_, ?_⟩⟩⟩
      · change ylo = 0 at hlo; omega
      · rw [ev yhi hhi]; omega
      · obtain ⟨w, hw, rfl⟩ := hvq
        obtain ⟨w', hw', rfl⟩ := hvb
        rw [rbs_uniq hw hw']
        simp only [ofK_gpow]
        ring
    · refine ⟨0, 1, rfl, rfl, fun vq hvq jj _ hj ↦ ⟨_, List.mem_singleton_self _,
        fun vb ylo yhi hvb hlo hhi ↦ ⟨a, ?_, ?_, ?_⟩⟩⟩
      · change ylo = 0 at hlo; omega
      · rw [ev yhi hhi]; omega
      · obtain rfl : jj = 0 := by omega
        obtain ⟨w, hw, rfl⟩ := hvq
        obtain ⟨w', hw', rfl⟩ := hvb
        rcases hbs with rfl | rfl
        · obtain ⟨u', w1, hu', hw1, rfl⟩ := hw
          change M (fp + u) = u' at hu'
          rw [rbs_uniq hw1 hw', ← hu', hu]
          simp only [ofK_gpow]
          ring
        · obtain ⟨u', w1, hu', hw1, rfl⟩ := rbs_snoc hw
          change M (fp + u) = u' at hu'
          rw [rbs_uniq hw1 hw', ← hu', hu]
          simp only [ofK_gpow]
          ring
  | .sub ⟨⟨afp, ak, abs⟩, alo, ahi, aS, ad⟩ [⟨bq, blo, bhi, bS, bd⟩, ⟨⟨cfp, ck, cbs⟩, clo, chi, cS, cd⟩], hx =>
    simp only [liftShape, decide_eq_true_eq] at hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcs, rfl, rfl, rfl, rfl⟩ := hx
    show RSub M fp _ _
    refine ⟨0, a + 1, rfl, iv, fun vq hvq jj _ hj ↦ ?_⟩
    by_cases hja : jj < a
    · refine ⟨_, List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨jj, ?_, ?_, ?_⟩⟩
      · change ylo = 0 at hlo; omega
      · rw [eu yhi hhi]; exact hja
      · rw [rmono_uniq hvq hvb]
    · obtain rfl : jj = a := by omega
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨0, ?_, ?_, ?_⟩⟩
      · change ylo = 0 at hlo; omega
      · change yhi = 1 at hhi; omega
      · obtain ⟨w, hw, rfl⟩ := hvq
        obtain ⟨w', hw', rfl⟩ := hvb
        rcases hcs with rfl | rfl
        · obtain ⟨u', w1, hu', hw1, rfl⟩ := hw'
          change M (fp + u) = u' at hu'
          rw [rbs_uniq hw hw1, ← hu', hu]
          simp only [ofK_gpow]
          ring
        · obtain ⟨u', w1, hu', hw1, rfl⟩ := rbs_snoc hw'
          change M (fp + u) = u' at hu'
          rw [rbs_uniq hw hw1, ← hu', hu]
          simp only [ofK_gpow]
          ring
  | .sub _ [], hx => simp [liftShape] at hx
  | .sub _ (_ :: _ :: _ :: _), hx => simp [liftShape] at hx
  | .lt _ _, hx => simp [liftShape] at hx
  | .nz _, hx => simp [liftShape] at hx
  | .name _, hx => simp [liftShape] at hx

end

/-- **`verify_keccak`'s lifts**: `y_g = g·pack_g` and `tau_g = g^4·pack_g`. -/
theorem lift_vk {A : String → FnAl} :
    LiftAt A (fn_idx% «verify_keccak») (.n 19) (.n 21) 1 ∧ LiftAt A (fn_idx% «verify_keccak») (.n 19) (.n 6) 4 := by
  have hn : (coreOf (fn_idx% «verify_keccak»)).name = name% «verify_keccak» := by decide +kernel
  obtain ⟨c6, -, -, c19, c21, -⟩ := vk_cellsJ
  refine ⟨fun r K i e hr t ↦ ?_, fun r K i e hr t ↦ ?_⟩ <;>
    obtain ⟨-, p, τ, hτ9, hτ28, -, -, h6, h19, h21, -⟩ := vk_vals t hr hn <;>
    obtain ⟨m6, -, m19, m21, -, -⟩ := vk_cells t hr hn <;>
    refine ⟨τ - 4, by rw [c19, m19, h19, ofK_gpow], ?_, by omega⟩
  · rw [c21, m21, h21, ofK_gpow, show τ - 4 + 1 = τ - 3 by omega]
  · rw [c6, m6, h6, ofK_gpow, show τ - 4 + 4 = τ by omega]

/-- **The frames' lifts at the honest frames.** -/
theorem lifts_ok {A : String → FnAl} : ∀ p ∈ Res.lifts, LiftAt A p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp only [Res.lifts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact lift_vk

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **A run of a lift at an honest frame.** -/
theorem lift_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : liftB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hpx
  obtain ⟨rfl, hsh⟩ := hpx
  obtain ⟨a, hu, hv, hlt⟩ := lifts_ok p hp r K i e hr t
  exact lift_rres hu hv hlt hsh

end

end LeanVM.Guest.EndExec
