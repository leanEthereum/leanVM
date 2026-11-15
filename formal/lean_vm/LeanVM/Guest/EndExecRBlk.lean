/-
  LeanVM.Guest.EndExecRBlk

  Runs cut into blocks by a split (`Res.blkB`), sound at the honest frames.
-/

module

public import LeanVM.Guest.EndExecRSplit
public import LeanVM.Guest.EndExecRA
public import LeanVM.Guest.Res.SubDefs

/-!
# Runs cut into blocks

`blk_rres`: on a frame whose `[n]` is `g^(K·a + b)`, `[s] = g^a` and `[r] = g^b`, the run of stride `S`
from `d` up to `[n]`'s exponent lies in `blkRes`'s runs: a point `c < K·a` is `c = K·(c / K) + c % K`,
offset `(c % K)·S + d` of block `c / K < a`; a point `K·a ≤ c` is `c - K·a < b` past `[s]^(K·S)`.
`blk_top`: at an honest frame, from the frame's split (`splits_ok`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (blkB blkRes)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

section

variable {M : ℕ → E} {fp : ℕ}

theorem ridx_ex_fr {o a : ℕ} (h : M (fp + o) = ofK (Parameters.g ^ a)) (ha : a < 2 ^ 62) :
    ∀ y, RIdx M fp (.ex (.fr o) 0) y → y = a := fun y hy ↦ by
  obtain ⟨v, e', hv, hve, he', hx⟩ := hy
  change M (fp + o) = v at hv
  rw [h, hve] at hv
  have := gpow_inj (by omega) (by omega) (ofK_injective hv)
  omega

/-- **A run cut into blocks by a split**: `[n] = g^(K·a + b)`, `[s] = g^a`, `[r] = g^b`. -/
theorem blk_rres {T : Base} {s r n K S d a b : ℕ} (hs : M (fp + s) = ofK (Parameters.g ^ a))
    (hr : M (fp + r) = ofK (Parameters.g ^ b)) (hn : M (fp + n) = ofK (Parameters.g ^ (K * a + b)))
    (hlt : K * a + b < 2 ^ 62) : RRes M fp (blkRes T s r n K S d) := by
  refine ⟨0, K * a + b, rfl, ⟨_, K * a + b, hn, rfl, hlt, rfl⟩, fun vq hvq c _ hc ↦ ?_⟩
  by_cases hca : c < K * a
  · have hK : 0 < K := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hca
    have ha : a < 2 ^ 62 := by have := Nat.le_mul_of_pos_left a hK; omega
    refine ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨c % K, List.mem_range.mpr (Nat.mod_lt _ hK), rfl⟩),
      fun vb ylo yhi hvb hlo hhi ↦ ⟨c / K, ?_, ?_, ?_⟩⟩
    · change ylo = 0 at hlo; rw [hlo]; exact Nat.zero_le _
    · rw [ridx_ex_fr hs ha yhi hhi]
      exact (Nat.div_lt_iff_lt_mul hK).mpr (by rw [mul_comm]; exact hca)
    · rw [rmono_uniq hvq hvb]
      have e : S * c + d = K * S * (c / K) + (c % K * S + d) := by
        nth_rw 1 [← Nat.div_add_mod c K]; ring
      rw [e]
  · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun vb ylo yhi hvb hlo hhi ↦
      ⟨c - K * a, ?_, ?_, ?_⟩⟩
    · change ylo = 0 at hlo; rw [hlo]; exact Nat.zero_le _
    · rw [ridx_ex_fr hr (by omega) yhi hhi]; omega
    · obtain ⟨wq, ⟨u, w, hu, hw, rfl⟩, rfl⟩ := hvq
      obtain ⟨wb, ⟨u', w', hu', ⟨u2, w2, hu2, hw2, rfl⟩, rfl⟩, rfl⟩ := hvb
      change w = 1 at hw
      change w2 = 1 at hw2
      change M (fp + s) = u2 at hu2
      subst hw hw2
      rw [rbase_uniq hu' hu, ← hu2, hs]
      have e : S * c + d = a * (K * S) + (S * (c - K * a) + d) := by
        have h' : c = K * a + (c - K * a) := by omega
        nth_rw 1 [h']; ring
      simp only [ofK_gpow]
      rw [e, pow_add, pow_mul]
      ring

end

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **A run cut into blocks at an honest frame.** -/
theorem blk_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : blkB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [blkB] at hx
    split at hx
    · obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpx
      obtain ⟨rfl, hxe⟩ := hpx
      obtain ⟨a0, b0, hs, hr', hn, hlt⟩ := splits_ok p hp r K i e hr t
      rw [hxe]
      exact blk_rres hs hr' hn hlt
    · cases hx
  | .lt _ _, hx => simp [blkB] at hx
  | .nz _, hx => simp [blkB] at hx
  | .name _, hx => simp [blkB] at hx

end

end LeanVM.Guest.EndExec
