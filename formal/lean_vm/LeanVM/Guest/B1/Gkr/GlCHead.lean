/-
  LeanVM.Guest.B1.Gkr.GlCHead

  A radix-four layer's prefix (`glPre`), completely: on its equations and the slot of
  `L = 2j + 2 - o`, the combiner's permutation, the values, the point row, the head record's
  pointer and the combined claim.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCRound
public import LeanVM.Guest.B1.Gkr.Layer

/-!
# A radix-four layer's prefix, completely

`glc_pre`: on `glPre`'s equations (its ten reads not stores), the parameters `layers`, `rounds`,
`pts`, `x_j = g^j`, `start_g = g^(2 - o)` and the slot of `L = 2j + 2 - o` (`GkSlot`), the prefix
holds; its values are the slot's pointer `layers·g^(10L)` (`15`), the cursor (`21`), the
combiner `s.squeeze.1` (`40`) and the capacity after it (`35 ..`), the position (`44`), the
point row `pts·g^(40(j + 1))` (`53`), the head record `rounds·pos` (`54`), the combined claim
(`58`) and the zeros (`23 .. 26`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {S : List Atom}
  {w : ℕ → E}

/-- The prefix's reads: the slot's capacity and cursor, its values and position. -/
def glPreKeys : List (ℕ × ℕ × ℕ) :=
  (List.range 6).map (fun k ↦ (16 + k, 15, k)) ++ (List.range 4).map (fun k ↦ (41 + k, 15, 6 + k))

theorem glPre_atoms : ∀ s ∈ glPre, ∃ a, s = .atom a := by
  intro s hs
  have : glPre.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by decide
  have h := List.all_eq_true.mp this s hs
  cases s with
  | atom a => exact ⟨a, rfl⟩
  | _ => simp at h

/-- **The prefix, completely.** -/
theorem glc_pre (hG : ∀ s ∈ glPre, GoodS rd S w σ s)
    (hk : ∀ k ∈ glPreKeys, some k ∉ S.map loadKey) {layers rounds pts : E} {j o : ℕ} (ho : o < 2)
    (e0 : σ (.n 0) = layers) (e1 : σ (.n 1) = rounds) (e2 : σ (.n 2) = pts)
    (e4 : σ (.n 4) = gen ^ j) (e5 : σ (.n 5) = gen ^ (2 - o))
    {s : Fs} {cur : E} {st : GkrState} {pos : E}
    (hS : GkSlot rd layers (2 * j + 2 - o) s cur st (pts * gen ^ (40 * (j + 1))) pos) :
    Stmt.HoldsList C rd σ glPre True kret ∧
      σ (.n 15) = layers * gen ^ (10 * (2 * j + 2 - o)) ∧ σ (.n 21) = cur ∧
      σ (.n 40) = s.squeeze.1 ∧ (glCap 35).map σ = s.squeeze.2.cap ∧ σ (.n 44) = pos ∧
      σ (.n 53) = pts * gen ^ (40 * (j + 1)) ∧ σ (.n 54) = rounds * pos ∧
      σ (.n 58) = polyEval st.values s.squeeze.1 ∧
      σ (.n 23) = 0 ∧ σ (.n 24) = 0 ∧ σ (.n 25) = 0 ∧ σ (.n 26) = 0 := by
  have g : ∀ a, Stmt.atom a ∈ glPre → Good rd S w σ a := fun a ha ↦ hG _ ha
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, -, -, hpos⟩ := hS
  set L := 2 * j + 2 - o with hL
  have m9 := good_mul (g (.mul (.n 9) (.n 4) (.n 4)) (by simp [glPre])) (by omega) (by omega)
  have m10 := good_mul (g (.mul (.n 10) (.n 9) (.n 5)) (by simp [glPre])) (by omega) (by omega)
  have m11 := good_mul (g (.mul (.n 11) (.n 10) (.n 10)) (by simp [glPre])) (by omega) (by omega)
  have m12 := good_mul (g (.mul (.n 12) (.n 11) (.n 11)) (by simp [glPre])) (by omega) (by omega)
  have m13 := good_mul (g (.mul (.n 13) (.n 12) (.n 10)) (by simp [glPre])) (by omega) (by omega)
  have m14 := good_mul (g (.mul (.n 14) (.n 13) (.n 13)) (by simp [glPre])) (by omega) (by omega)
  have m15 := good_mul (g (.mul (.n 15) (.n 0) (.n 14)) (by simp [glPre])) (by omega) (by omega)
  have e10 : σ (.n 10) = gen ^ L := by
    rw [m10, m9, e4, e5, ← pow_add, ← pow_add, show j + j + (2 - o) = L by omega]
  have e15 : σ (.n 15) = layers * gen ^ (10 * L) := by
    rw [m15, m14, m13, m12, m11, e10, e0, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have ld : ∀ k v, LoadHolds rd layers (10 * L + k) v → LoadHolds rd (σ (.n 15)) k v := by
    intro k v h; rw [e15, tb_loadHolds_mul_gen_pow]; exact h
  have key : ∀ k ∈ glPreKeys, some k ∉ S.map loadKey := hk
  have r16 : ∀ k < 5, σ (.n (16 + k)) = s.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 15)) k (σ (.n (16 + k))) := fun k hk' ↦
    good_read (g (.load (.n (16 + k)) (.n 15) k) (by
        interval_cases k <;> simp [glPre]))
      (key _ (by simp [glPreKeys]; omega)) (ld k _ (hcap k hk'))
  obtain ⟨e21, l21⟩ := good_read (g (.load (.n 21) (.n 15) 5) (by simp [glPre]))
    (key _ (by simp [glPreKeys])) (ld 5 _ hcur)
  have c22 : σ (.n 22) = word 1 0 := g (.const (.n 22) (word 1 0)) (by simp [glPre])
  have c23 : σ (.n 23) = word 0 0 := g (.const (.n 23) (word 0 0)) (by simp [glPre])
  have c24 : σ (.n 24) = word 0 0 := g (.const (.n 24) (word 0 0)) (by simp [glPre])
  have c25 : σ (.n 25) = word 0 0 := g (.const (.n 25) (word 0 0)) (by simp [glPre])
  have c26 : σ (.n 26) = word 0 0 := g (.const (.n 26) (word 0 0)) (by simp [glPre])
  rw [tb_word_zero] at c23 c24 c25 c26
  -- the combiner's permutation
  have hcapE : ((List.range 5).map fun k ↦ V.n (16 + k)).map σ = s.cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    exact List.map_congr_left fun k hk' => (r16 k (List.mem_range.mp hk')).1
  obtain ⟨k27, -⟩ := keccak_good (rd := rd) (S := S) (w := w) (g (.keccak [.n 23, .n 23, .n 23,
    .n 23, .n 23, .n 24, .n 25, .n 26, .n 16, .n 17, .n 18, .n 19, .n 20] (lyOuts 27) false false)
    (by simp [glPre, lyOuts, List.range_succ]))
  obtain ⟨hP, hQ⟩ := ly_keccak k27
  have hins : ([V.n 23, .n 23, .n 23, .n 23, .n 23, .n 24, .n 25, .n 26, .n 16, .n 17, .n 18,
      .n 19, .n 20] : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [hpe, ← hcapE, ← ly_zero_rate c23 c24 c25 c26]
    simp [List.range_succ]
  rw [hins] at hP hQ
  have c40 : σ (.n 40) = σ (.n 27) := g (.copy (.n 40) (.n 27)) (by simp [glPre])
  have e40 : σ (.n 40) = s.squeeze.1 := by
    rw [c40]; exact challengeT_value (σ := σ) (s0 := .n 27) (b := 27) rfl (hP 0 (by omega))
  have hcap35 : (glCap 35).map σ = s.squeeze.2.cap := by
    have := hQ
    simp only [lyCap, glCap] at this ⊢
    rw [show s.squeeze.2.cap = capOf (permOf (rateOf s.pend ++ s.cap)) from by
      simp [Fs.squeeze, Fs.perm]]
    rw [← this]
  -- the values and the position
  have rv : ∀ k < 4, ∀ v, LoadHolds rd layers (10 * L + (6 + k)) v →
      σ (.n (41 + k)) = v ∧ LoadHolds rd (σ (.n 15)) (6 + k) (σ (.n (41 + k))) := fun k hk' v hv ↦
    good_read (g (.load (.n (41 + k)) (.n 15) (6 + k)) (by interval_cases k <;> simp [glPre]))
      (key _ (by simp [glPreKeys]; omega)) (ld (6 + k) _ hv)
  obtain ⟨e41, l41⟩ := rv 0 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 0 (by omega))
  obtain ⟨e42, l42⟩ := rv 1 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 1 (by omega))
  obtain ⟨e43, l43⟩ := rv 2 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 2 (by omega))
  obtain ⟨e44, l44⟩ := rv 3 (by omega) _ hpos
  -- the point row, the head and the claim
  have c45 : σ (.n 45) = word 2 0 := g (.const (.n 45) (word 2 0)) (by simp [glPre])
  have m46 := good_mul (g (.mul (.n 46) (.n 4) (.n 45)) (by simp [glPre])) (by omega) (by omega)
  have m47 := good_mul (g (.mul (.n 47) (.n 46) (.n 46)) (by simp [glPre])) (by omega) (by omega)
  have m48 := good_mul (g (.mul (.n 48) (.n 47) (.n 47)) (by simp [glPre])) (by omega) (by omega)
  have m49 := good_mul (g (.mul (.n 49) (.n 48) (.n 46)) (by simp [glPre])) (by omega) (by omega)
  have m50 := good_mul (g (.mul (.n 50) (.n 49) (.n 49)) (by simp [glPre])) (by omega) (by omega)
  have m51 := good_mul (g (.mul (.n 51) (.n 50) (.n 50)) (by simp [glPre])) (by omega) (by omega)
  have m52 := good_mul (g (.mul (.n 52) (.n 51) (.n 51)) (by simp [glPre])) (by omega) (by omega)
  have m53 := good_mul (g (.mul (.n 53) (.n 2) (.n 52)) (by simp [glPre])) (by omega) (by omega)
  have m54 := good_mul (g (.mul (.n 54) (.n 1) (.n 44)) (by simp [glPre])) (by omega) (by omega)
  have m55 := good_mul (g (.mul (.n 55) (.n 40) (.n 43)) (by simp [glPre])) (by omega) (by omega)
  have a56 : σ (.n 56) = σ (.n 42) + σ (.n 55) := g (.add (.n 56) (.n 42) (.n 55)) (by simp [glPre])
  have m57 := good_mul (g (.mul (.n 57) (.n 40) (.n 56)) (by simp [glPre])) (by omega) (by omega)
  have a58 : σ (.n 58) = σ (.n 41) + σ (.n 57) := g (.add (.n 58) (.n 41) (.n 57)) (by simp [glPre])
  have e53 : σ (.n 53) = pts * gen ^ (40 * (j + 1)) := by
    rw [m53, m52, m51, m50, m49, m48, m47, m46, c45, tb_word_gen, e4, e2, ← pow_succ]
    ring
  have e54 : σ (.n 54) = rounds * pos := by rw [m54, e1, e44]
  have e58 : σ (.n 58) = polyEval st.values s.squeeze.1 := by
    obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a58, m57, a56, m55, e41, e42, e43, e40, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring
  refine ⟨?_, e15, e21, e40, hcap35, e44, e53, e54, e58, c23, c24, c25, c26⟩
  refine holdsList_straightN _ (by decide) ?_ trivial
  simp only [glPre, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, SHolds, Atom.Holds]
  exact ⟨m9, m10, m11, m12, m13, m14, m15, (r16 0 (by omega)).2, (r16 1 (by omega)).2,
    (r16 2 (by omega)).2, (r16 3 (by omega)).2, (r16 4 (by omega)).2, l21, c22,
    by rw [c23, tb_word_zero], by rw [c24, tb_word_zero], by rw [c25, tb_word_zero],
    by rw [c26, tb_word_zero], k27, c40, l41, l42, l43, l44, c45, m46, m47, m48, m49, m50, m51,
    m52, m53, m54, m55, a56, m57, a58⟩

end
end LeanVM.Guest.B1.Tables
