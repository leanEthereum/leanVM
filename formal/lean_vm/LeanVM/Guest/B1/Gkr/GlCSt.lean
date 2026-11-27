/-
  LeanVM.Guest.B1.Gkr.GlCSt

  The rounds' states `gkSt` from a later round on, and rounds between two records as
  `TbGkrRoundsOut`.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCRound

/-!
# Rounds' states, shifted

* `gkSt_addN`, `gkP_addN`: the state after `a + q` rounds is the state after `q` rounds of the
  words and factors from `a` on, from the state after `a`;
* `glc_tb`: the `n` rounds from `a` between a record after `a` rounds and one `t` records on after
  `a + n`, with their words, factors and challenges in memory, are `TbGkrRoundsOut n t`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

theorem gkSt_addN (Cf : ℕ → List E) (ef : ℕ → E) (c : E) (s : Fs) (a : ℕ) :
    ∀ q, gkSt Cf ef c s (a + q) = gkSt (fun i ↦ Cf (a + i)) (fun i ↦ ef (a + i))
      (gkSt Cf ef c s a).1 (gkSt Cf ef c s a).2 q
  | 0 => rfl
  | q + 1 => by
    rw [← Nat.add_assoc]
    simp only [gkSt]
    rw [gkSt_addN Cf ef c s a q]

theorem gkP_addN (Cf : ℕ → List E) (ef : ℕ → E) (c : E) (s : Fs) (a q : ℕ) :
    gkP Cf ef c s (a + q) = gkP (fun i ↦ Cf (a + i)) (fun i ↦ ef (a + i))
      (gkSt Cf ef c s a).1 (gkSt Cf ef c s a).2 q := by
  simp only [gkP, gkSt_addN]

/-- **Rounds between two records**, from `gkSt`'s states. -/
theorem glc_tb {rd : Reader} {rec cur pt : E} {Cf : ℕ → List E} {ef : ℕ → E} {c : E}
    {cap0 : List E} {a n t : ℕ} (h4 : ∀ q, (Cf q).length = 4)
    (hc0 : CapAt rd rec 0 1 (gkSt Cf ef c ⟨cap0, []⟩ a).2.cap)
    (hu0 : LoadHolds rd rec 5 (cur * gen ^ (4 * a)))
    (hl0 : LoadHolds rd rec 6 (gkSt Cf ef c ⟨cap0, []⟩ a).1)
    (hc1 : CapAt rd (rec * gen ^ (7 * t)) 0 1 (gkSt Cf ef c ⟨cap0, []⟩ (a + n)).2.cap)
    (hu1 : LoadHolds rd (rec * gen ^ (7 * t)) 5 (cur * gen ^ (4 * (a + n))))
    (hl1 : LoadHolds rd (rec * gen ^ (7 * t)) 6 (gkSt Cf ef c ⟨cap0, []⟩ (a + n)).1)
    (hw : ∀ q < n, ∀ i < 4, LoadHolds rd (cur * gen ^ (4 * a)) (4 * q + i) ((Cf (a + q)).getD i 0))
    (he : ∀ q < n, LoadHolds rd pt q (ef (a + q)))
    (hch : ∀ q < n, LoadHolds rd (pt * gen ^ 42) q
      (challengeOf (gkP Cf ef c ⟨cap0, []⟩ (a + q)))) :
    TbGkrRoundsOut n t rd rec pt := by
  set St := gkSt Cf ef c ⟨cap0, []⟩ a with hSt
  have hS2 : St.2 = ⟨St.2.cap, []⟩ := gkSt_empty Cf ef c cap0 a
  let Cg : ℕ → List E := fun i ↦ Cf (a + i)
  let eg : ℕ → E := fun i ↦ ef (a + i)
  have hrun1 : (gkrRun ((List.range n).map Cg) ((List.range n).map eg) St.1 ⟨St.2.cap, []⟩).1 =
      (List.range n).map fun q ↦ challengeOf (gkP Cf ef c ⟨cap0, []⟩ (a + q)) := by
    rw [gkrRun_range1]
    refine List.map_congr_left fun q _ ↦ ?_
    rw [gkP_addN, ← hSt, ← hS2]
  have hrun2 : (gkrRun ((List.range n).map Cg) ((List.range n).map eg) St.1 ⟨St.2.cap, []⟩).2 =
      gkSt Cf ef c ⟨cap0, []⟩ (a + n) := by
    rw [gkrRun_range2, gkSt_addN, ← hSt, ← hS2]
  refine ⟨St.2.cap, cur * gen ^ (4 * a), St.1, (List.range n).map Cg, (List.range n).map eg,
    hc0, hu0, hl0, by simp, fun cl hcl ↦ ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hcl; exact h4 _
  · intro k hk
    rw [flatten4_length Cg (fun q ↦ h4 _) n] at hk
    have := hw (k / 4) (by omega) (k % 4) (by omega)
    rw [show 4 * (k / 4) + k % 4 = k by omega] at this
    have e := flatten4_get Cg (fun q ↦ h4 _) n (k / 4) (k % 4) (by omega) (by omega)
    rw [show 4 * (k / 4) + k % 4 = k by omega] at e
    rw [← List.getD_eq_getElem _ 0, e]
    exact this
  · intro k hk
    simp only [List.length_map, List.length_range] at hk
    simpa [eg] using he k hk
  · rw [hrun1]
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    simpa using hch k hk
  · rw [hrun2, capAt_mul_gen_pow] at *
    simpa using hc1
  · rw [loadHolds_mul_gen_pow] at hu1
    rw [show cur * gen ^ (4 * a) * gen ^ (4 * n) = cur * gen ^ (4 * (a + n)) by ring]
    exact hu1
  · rw [hrun2]; rw [loadHolds_mul_gen_pow] at hl1; exact hl1

end
end LeanVM.Guest.B1.Tables
