/-
  LeanVM.Guest.B1.Gkr.GlCHead

  A radix-four layer's prefix (`glPre`), completely: on its equations and the slot of
  `L = 2j + 2 - o`, the combiner's permutation, the values, the point row, the head record's
  pointer and the combined claim.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCRound
public import LeanVM.Guest.B1.Gkr.Layer
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»

/-!
# A radix-four layer's prefix, completely

`glc_pre`: on `glPre`'s equations (its ten reads not stores), the parameters `layers`, `rounds`,
`pts`, `x_j = g^j`, `start_g = g^(2 - o)` and the slot of `L = 2j + 2 - o` (`GkSlot`), the prefix
holds; its values are the slot's pointer `layers·g^(10L)` (`15`), the cursor (`21`), the
combiner `s.squeeze.1` (`27`) and the capacity after it (`35 ..`), the position (`43`), the
point row `pts·g^(40(j + 1))` (`52`), the head record `rounds·pos` (`53`), the combined claim
(`57`) and the zeros (`23 .. 26`).
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
  (List.range 6).map (fun k ↦ (16 + k, 15, k)) ++ (List.range 4).map (fun k ↦ (40 + k, 15, 6 + k))

/-- **The prefix, completely.** -/
theorem glc_pre (hG : ∀ s ∈ glPre, GoodS rd S w σ s)
    (hk : ∀ k ∈ glPreKeys, some k ∉ S.map loadKey) {layers rounds pts : E} {j o : ℕ} (ho : o < 2)
    (e0 : σ (.n (valf% «gkr_layer» "layers")) = layers) (e1 : σ (.n (valf% «gkr_layer» "rounds")) = rounds) (e2 : σ (.n (valf% «gkr_layer» "gkr_pts")) = pts)
    (e4 : σ (.n (valf% «gkr_layer» "x_j")) = gen ^ j) (e5 : σ (.n (valf% «gkr_layer» "start_g")) = gen ^ (2 - o))
    {s : Fs} {cur : E} {st : GkrState} {pos : E}
    (hS : GkSlot rd layers (2 * j + 2 - o) s cur st (pts * gen ^ (40 * (j + 1))) pos) :
    Stmt.HoldsList C rd σ glPre True kret ∧
      σ (.n (valf% «gkr_layer» "layer")) = layers * gen ^ (10 * (2 * j + 2 - o)) ∧ σ (.n (valf% «gkr_layer» "s4#0")) = cur ∧
      σ (.n (valf% «gkr_layer» "nxt[0]@1")) = s.squeeze.1 ∧ (glCap (valf% «gkr_layer» "nxt[8]@1")).map σ = s.squeeze.2.cap ∧ σ (.n (valf% «gkr_layer» "round_pos")) = pos ∧
      σ (.n (valf% «gkr_layer» "point_row")) = pts * gen ^ (40 * (j + 1)) ∧ σ (.n (valf% «gkr_layer» "head")) = rounds * pos ∧
      σ (.n (valf% «gkr_layer» "claim@2")) = polyEval st.values s.squeeze.1 ∧
      σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) = 0 ∧ σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) = 0 ∧ σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) = 0 ∧ σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) = 0 := by
  have g : ∀ a, Stmt.atom a ∈ glPre → Good rd S w σ a := fun a ha ↦ hG _ ha
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, -, -, hpos⟩ := hS
  set L := 2 * j + 2 - o with hL
  have m9 := good_mul (g (.mul (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "x_j"))) (by simp [glPre])) (by omega) (by omega)
  have m10 := good_mul (g (.mul (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "start_g"))) (by simp [glPre])) (by omega) (by omega)
  have m11 := good_mul (g (.mul (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer"))) (by simp [glPre])) (by omega) (by omega)
  have m12 := good_mul (g (.mul (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "layer~0"))) (by simp [glPre])) (by omega) (by omega)
  have m13 := good_mul (g (.mul (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "x_layer"))) (by simp [glPre])) (by omega) (by omega)
  have m14 := good_mul (g (.mul (.n (valf% «gkr_layer» "layer~3")) (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~2"))) (by simp [glPre])) (by omega) (by omega)
  have m15 := good_mul (g (.mul (.n (valf% «gkr_layer» "layer")) (.n (valf% «gkr_layer» "layers")) (.n (valf% «gkr_layer» "layer~3"))) (by simp [glPre])) (by omega) (by omega)
  have e10 : σ (.n (valf% «gkr_layer» "x_layer")) = gen ^ L := by
    rw [m10, m9, e4, e5, ← pow_add, ← pow_add, show j + j + (2 - o) = L by omega]
  have e15 : σ (.n (valf% «gkr_layer» "layer")) = layers * gen ^ (10 * L) := by
    rw [m15, m14, m13, m12, m11, e10, e0, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have ld : ∀ k v, LoadHolds rd layers (10 * L + k) v → LoadHolds rd (σ (.n (valf% «gkr_layer» "layer"))) k v := by
    intro k v h; rw [e15, loadHolds_mul_gen_pow]; exact h
  have key : ∀ k ∈ glPreKeys, some k ∉ S.map loadKey := hk
  have r16 : ∀ k < 5, σ (.n ((valf% «gkr_layer» "sp[0]@1") + k)) = s.cap.getD k 0 ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "layer"))) k (σ (.n ((valf% «gkr_layer» "sp[0]@1") + k))) := fun k hk' ↦
    good_read (g (.load (.n (16 + k)) (.n (valf% «gkr_layer» "layer")) k) (by
        interval_cases k <;> simp [glPre]))
      (key _ (by simp [glPreKeys]; omega)) (ld k _ (hcap k hk'))
  obtain ⟨e21, l21⟩ := good_read (g (.load (.n (valf% «gkr_layer» "s4#0")) (.n (valf% «gkr_layer» "layer")) 5) (by simp [glPre]))
    (key _ (by simp [glPreKeys])) (ld 5 _ hcur)
  have c22 : σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0")) = word 1 0 := g (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0")) (word 1 0)) (by simp [glPre])
  have c23 : σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) = word 0 0 := g (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) (word 0 0)) (by simp [glPre])
  have c24 : σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) = word 0 0 := g (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) (word 0 0)) (by simp [glPre])
  have c25 : σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) = word 0 0 := g (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) (word 0 0)) (by simp [glPre])
  have c26 : σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) = word 0 0 := g (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) (word 0 0)) (by simp [glPre])
  rw [word_zero] at c23 c24 c25 c26
  -- the combiner's permutation
  have hcapE : ((List.range 5).map fun k ↦ V.n ((valf% «gkr_layer» "sp[0]@1") + k)).map σ = s.cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    exact List.map_congr_left fun k hk' => (r16 k (List.mem_range.mp hk')).1
  obtain ⟨k27, -⟩ := keccak_good (rd := rd) (S := S) (w := w) (g (.keccak [.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"),
    .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]"), .n (valf% «gkr_layer» "sp[0]@1"), .n (valf% «gkr_layer» "sp[1]@1"), .n (valf% «gkr_layer» "sp[2]@1"), .n (valf% «gkr_layer» "sp[3]@1"), .n (valf% «gkr_layer» "sp[4]@1")] (lyOuts (valf% «gkr_layer» "nxt[0]@1")) false false)
    (by simp [glPre, lyOuts, List.range_succ]))
  obtain ⟨hP, hQ⟩ := ly_keccak k27
  have hins : ([V.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]"), .n (valf% «gkr_layer» "sp[0]@1"), .n (valf% «gkr_layer» "sp[1]@1"), .n (valf% «gkr_layer» "sp[2]@1"),
      .n (valf% «gkr_layer» "sp[3]@1"), .n (valf% «gkr_layer» "sp[4]@1")] : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [hpe, ← hcapE, ← ly_zero_rate c23 c24 c25 c26]
    simp [List.range_succ]
  rw [hins] at hP hQ
  have e40 : σ (.n (valf% «gkr_layer» "nxt[0]@1")) = s.squeeze.1 := by
    exact challengeT_value (σ := σ) (s0 := .n (valf% «gkr_layer» "nxt[0]@1")) (b := 27) rfl (hP 0 (by omega))
  have hcap35 : (glCap (valf% «gkr_layer» "nxt[8]@1")).map σ = s.squeeze.2.cap := by
    have := hQ
    simp only [lyCap, glCap] at this ⊢
    rw [show s.squeeze.2.cap = capOf (permOf (rateOf s.pend ++ s.cap)) from by
      simp [Fs.squeeze, Fs.perm]]
    rw [← this]
  -- the values and the position
  have rv : ∀ k < 4, ∀ v, LoadHolds rd layers (10 * L + (6 + k)) v →
      σ (.n ((valf% «gkr_layer» "layer_vals[0]") + k)) = v ∧ LoadHolds rd (σ (.n (valf% «gkr_layer» "layer"))) (6 + k) (σ (.n ((valf% «gkr_layer» "layer_vals[0]") + k))) := fun k hk' v hv ↦
    good_read (g (.load (.n (40 + k)) (.n (valf% «gkr_layer» "layer")) (6 + k)) (by interval_cases k <;> simp [glPre]))
      (key _ (by simp [glPreKeys]; omega)) (ld (6 + k) _ hv)
  obtain ⟨e41, l41⟩ := rv 0 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 0 (by omega))
  obtain ⟨e42, l42⟩ := rv 1 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 1 (by omega))
  obtain ⟨e43, l43⟩ := rv 2 (by omega) _ (by rw [← Nat.add_assoc]; exact hval 2 (by omega))
  obtain ⟨e44, l44⟩ := rv 3 (by omega) _ hpos
  -- the point row, the head and the claim
  have c45 : σ (.n (valf% «gkr_layer» "point_row~0")) = word 2 0 := g (.const (.n (valf% «gkr_layer» "point_row~0")) (word 2 0)) (by simp [glPre])
  have m46 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "point_row~0"))) (by simp [glPre])) (by omega) (by omega)
  have m47 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "point_row~1"))) (by simp [glPre])) (by omega) (by omega)
  have m48 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~2"))) (by simp [glPre])) (by omega) (by omega)
  have m49 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~1"))) (by simp [glPre])) (by omega) (by omega)
  have m50 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~4"))) (by simp [glPre])) (by omega) (by omega)
  have m51 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~5"))) (by simp [glPre])) (by omega) (by omega)
  have m52 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row~7")) (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~6"))) (by simp [glPre])) (by omega) (by omega)
  have m53 := good_mul (g (.mul (.n (valf% «gkr_layer» "point_row")) (.n (valf% «gkr_layer» "gkr_pts")) (.n (valf% «gkr_layer» "point_row~7"))) (by simp [glPre])) (by omega) (by omega)
  have m54 := good_mul (g (.mul (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "rounds")) (.n (valf% «gkr_layer» "round_pos"))) (by simp [glPre])) (by omega) (by omega)
  have m55 := good_mul (g (.mul (.n (valf% «gkr_layer» "claim@1~0")) (.n (valf% «gkr_layer» "nxt[0]@1")) (.n (valf% «gkr_layer» "layer_vals[2]"))) (by simp [glPre])) (by omega) (by omega)
  have a56 : σ (.n (valf% «gkr_layer» "claim@1")) = σ (.n (valf% «gkr_layer» "layer_vals[1]")) + σ (.n (valf% «gkr_layer» "claim@1~0")) := g (.add (.n (valf% «gkr_layer» "claim@1")) (.n (valf% «gkr_layer» "layer_vals[1]")) (.n (valf% «gkr_layer» "claim@1~0"))) (by simp [glPre])
  have m57 := good_mul (g (.mul (.n (valf% «gkr_layer» "claim@2~0")) (.n (valf% «gkr_layer» "nxt[0]@1")) (.n (valf% «gkr_layer» "claim@1"))) (by simp [glPre])) (by omega) (by omega)
  have a58 : σ (.n (valf% «gkr_layer» "claim@2")) = σ (.n (valf% «gkr_layer» "layer_vals[0]")) + σ (.n (valf% «gkr_layer» "claim@2~0")) := g (.add (.n (valf% «gkr_layer» "claim@2")) (.n (valf% «gkr_layer» "layer_vals[0]")) (.n (valf% «gkr_layer» "claim@2~0"))) (by simp [glPre])
  have e53 : σ (.n (valf% «gkr_layer» "point_row")) = pts * gen ^ (40 * (j + 1)) := by
    rw [m53, m52, m51, m50, m49, m48, m47, m46, c45, word_gen, e4, e2, ← pow_succ]
    ring
  have e54 : σ (.n (valf% «gkr_layer» "head")) = rounds * pos := by rw [m54, e1, e44]
  have e58 : σ (.n (valf% «gkr_layer» "claim@2")) = polyEval st.values s.squeeze.1 := by
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
    by rw [c23, word_zero], by rw [c24, word_zero], by rw [c25, word_zero],
    by rw [c26, word_zero], k27, l41, l42, l43, l44, c45, m46, m47, m48, m49, m50, m51,
    m52, m53, m54, m55, a56, m57, a58⟩

end
end LeanVM.Guest.B1.Tables
