/-
  LeanVM.Protocol.Whir.Sound.DescentT

  The descent across levels over arrays: the next level's message by the additive NTT.
-/

module

public import LeanVM.Protocol.Whir.Sound.DescentA
public import LeanVM.Prover.Ntt

/-!
# The descent across levels over arrays

The step up a level (`upAt`) evaluates, on the level's domain, the message whose block `u` is
the next level's lane `u`'s low part, plus `Ŵ_κ` times the high part. Over arrays (`upAtA`): the
low parts by the inverse transform (`novelInvE`), the message (`msgA`) evaluated by the additive
NTT limb by limb (`Prover.ntt`, `Prover.Enc.ntt_getD`), `Ŵ_κ(x)` and the novel basis at `x` from
the table of `Ŵ_c` on the basis (`Prover.hatAt`). The final polynomial is evaluated from the same
table (`polyOfAtH`). So the descent across levels over arrays (`descendTraceA`) is the descent over
values with one-error decoding (`descendTraceA_eq`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open LeanVM.Prover Polynomial Finset

@[expose] public section

/-- `X_c(x_x)` from the table of `Ŵ_i` on the basis. -/
def novelAtH (c x : ℕ) : K := ∏ i ∈ range 64, if c.testBit i then hatAt i x else 1

/-- The polynomial of novel coefficients `cs` at `x_x`, from the table. -/
def polyOfAtH (cs : List E) (x : ℕ) : E :=
  ((List.range cs.length).map fun c ↦
    let a := cs.getD c 0
    let v := ofK (novelAtH c x)
    a * v).sum

theorem sum_range_eq_list (f : ℕ → E) : ∀ n, ∑ c ∈ range n, f c = ((List.range n).map f).sum
  | 0 => rfl
  | n + 1 => by
    rw [sum_range_succ, sum_range_eq_list f n, List.range_succ, List.map_append, List.sum_append]
    simp

theorem novelAtH_eq (c x : ℕ) : novelAtH c x = novelAt c (K.ofBits x) := by
  unfold novelAtH novelAt
  refine prod_congr rfl fun i hi ↦ ?_
  rw [Enc.hatAt_eq (mem_range.mp hi)]

theorem polyOfAtH_eq (cs : List E) (x : ℕ) : polyOfAtH cs x = polyOfAt cs (K.ofBits x) := by
  unfold polyOfAtH polyOfAt
  rw [sum_range_eq_list]
  simp only [novelAtH_eq]

/-- The message of the step up: entry `u + 2^m w` is entry `w` of the low part of lane `u` of the
next level's tuple `VA'`, read off its first `2^κ'` columns. -/
def msgA (κ κ' m : ℕ) (VA' : AV) : Array E :=
  let inv := Array.ofFn fun u : Fin (2 ^ m) ↦
    novelInvE κ' (Array.ofFn fun v : Fin (2 ^ κ') ↦ (VA'.getD v #[]).getD u 0)
  Array.ofFn fun j : Fin (2 ^ κ) ↦ (inv.getD (j % 2 ^ m) #[]).getD (j / 2 ^ m) 0

/-- **The step up a level over arrays**: one lane on the `2^(κ+R)` columns. -/
def upAtA (κ κ' m R : ℕ) (VA' : AV) (high : List E) : AV :=
  let g := msgA κ κ' m VA'
  let tw := nttTwiddles (κ + R) κ
  let l0 := ntt tw κ R (g.map fun e ↦ e.limb 0)
  let l1 := ntt tw κ R (g.map fun e ↦ e.limb 1)
  Array.ofFn fun x : Fin (2 ^ (κ + R)) ↦
    let lo := E.ofLimbs (l0.getD x 0) (l1.getD x 0)
    let hv := ofK (hatAt κ x)
    let p := polyOfAtH high x
    let t := hv * p
    #[lo + t]

theorem toAV_zero {n : ℕ} (f : (Fin 0 → Bool) → Fin n → E) :
    toAV n 0 f = Array.ofFn fun x : Fin n ↦ #[f (fun i ↦ i.elim0) x] := by
  unfold toAV
  congr 1
  funext x
  have hc : ∀ k, (bitsEquiv 0).symm k = (fun i : Fin 0 ↦ i.elim0) := fun k ↦ funext fun i ↦ i.elim0
  simp only [hc]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

theorem limbArr_getD (i : Fin 2) (y : Array E) (j : ℕ) :
    (limbArr i y).getD j 0 = (y.getD j 0).limb i := by
  unfold limbArr
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases y[j]? <;> simp [limb_zero]

theorem msgA_getD {κ' m : ℕ} {n' : ℕ} (hn' : 2 ^ κ' ≤ n') (V' : (Fin m → Bool) → Fin n' → E)
    (p : Fin (m + κ') → Bool) :
    (msgA (m + κ') κ' m (toAV n' m V')).getD (bitsToNat p) 0 =
      joinMsg rfl (fun u w ↦ (novelInvE κ' (Array.ofFn fun v : Fin (2 ^ κ') ↦
        V' u (Fin.castLE hn' v))).getD (bitsToNat w) 0) p := by
  set u : Fin m → Bool := fun i ↦ p (Fin.castAdd κ' i)
  set w : Fin κ' → Bool := fun i ↦ p (Fin.natAdd m i)
  have hp : bitsToNat p = bitsToNat u + 2 ^ m * bitsToNat w := by
    rw [← bitsToNat_append]
    congr 1
    exact (Fin.append_castAdd_natAdd).symm
  have hu := bitsToNat_lt u
  have hmod : bitsToNat p % 2 ^ m = bitsToNat u := by
    rw [hp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
  have hdiv : bitsToNat p / 2 ^ m = bitsToNat w := by
    rw [hp, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add]
  unfold msgA joinMsg
  simp only [Fin.cast_eq_self]
  rw [Enc.getD_ofFn _ _ _ (bitsToNat_lt p)]
  simp only [hmod, hdiv]
  rw [Enc.getD_ofFn _ _ _ hu]
  congr 2
  congr 1
  funext v
  have := rep_toAV V' u (Fin.castLE hn' v)
  rw [this]
  rfl

/-- **The step up a level over arrays is `upAt`.** -/
theorem upAtA_eq {κ' m R : ℕ} {n' : ℕ} (hn' : 2 ^ κ' ≤ n') (h64 : m + κ' + R ≤ 64) (hR : 1 ≤ R)
    (V' : (Fin m → Bool) → Fin n' → E) (high : List E) :
    upAtA (m + κ') κ' m R (toAV n' m V') high =
      toAV (2 ^ (m + κ' + R)) 0 fun _ x ↦ upAt κ' m hn' rfl V' high (K.ofBits x) := by
  rw [toAV_zero]
  dsimp only [upAtA]
  congr 1
  funext x
  congr 1
  refine congrArg (fun z : E ↦ [z]) ?_
  rw [upAt, Enc.hatAt_eq (by omega), polyOfAtH_eq]
  refine congrArg (fun z : E ↦ z + ofK (normVanishingAt (m + κ') (K.ofBits x)) *
    polyOfAt high (K.ofBits x)) ?_
  rw [Enc.ntt_getD (by omega) _ x.isLt, Enc.ntt_getD (by omega) _ x.isLt]
  symm
  refine (ofLimbs_limb _).symm.trans ?_
  refine congrArg₂ E.ofLimbs ?_ ?_ <;>
  · rw [limb_sum, Complete.encKAt]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [limb_mul_ofK, ← limbArr, limbArr_getD, msgA_getD hn' V' p]

theorem upAtA_eq' {κ κ' m R : ℕ} {n' : ℕ} (hn' : 2 ^ κ' ≤ n') (hκ : κ = m + κ')
    (h64 : κ + R ≤ 64) (hR : 1 ≤ R) (V' : (Fin m → Bool) → Fin n' → E) (high : List E) :
    upAtA κ κ' m R (toAV n' m V') high =
      toAV (2 ^ (κ + R)) 0 fun _ x ↦ upAt κ' m hn' hκ V' high (K.ofBits x) := by
  subst hκ
  exact upAtA_eq hn' h64 hR V' high

/-! ## Across levels -/

/-- **The descent across levels, over arrays.** -/
def descendTraceA (codes : ℕ → LevelCode) (OAs : List AV) :
    WhirTrace → ℕ → Option (ℕ × AV)
  | .final rounds folded, i => descendRoundsA (codes i).dom (codes i).deg (codes i).thr
      (OAs.getD i #[]) rounds 0
      (Array.ofFn fun x : Fin (codes i).n ↦ #[polyOfAtH folded x])
  | .mid rounds high rest, i => (descendTraceA codes OAs rest (i + 1)).bind fun T' ↦
      if T'.1 = (codes (i + 1)).ℓ ∧ (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ then
        descendRoundsA (codes i).dom (codes i).deg (codes i).thr (OAs.getD i #[])
          rounds 0 (upAtA (codes i).κ (codes (i + 1)).κ (codes (i + 1)).ℓ (codes i).R T'.2 high)
      else none

/-- **The descent across levels over arrays is the descent over values**, with one-error
decoding. -/
theorem descendTraceA_eq (codes : ℕ → LevelCode) (cs : List (ℕ × ℕ × Word)) {OAs : List AV}
    (hO : ∀ i j (v : Fin (codes i).n), laneO i cs (codes i).n j v =
      ((OAs.getD i #[]).getD v #[]).getD j 0) :
    ∀ (tr : WhirTrace) (i : ℕ), descendTraceA codes OAs tr i =
      (descendTraceV newtonValsDecoder codes cs tr i).map toAVS
  | .final rounds folded, i => by
    have hV : (Array.ofFn fun x : Fin (codes i).n ↦ #[polyOfAtH folded x]) =
        toAV (codes i).n 0 fun _ x ↦ polyOfAt folded (K.ofBits x) := by
      rw [toAV_zero]
      simp only [polyOfAtH_eq]
    rw [descendTraceA, descendTraceV, hV,
      descendRoundsA_eq _ _ _ (hO i)]
  | .mid rounds high rest, i => by
    rw [descendTraceA, descendTraceV, descendTraceA_eq codes cs hO rest (i + 1)]
    rcases descendTraceV newtonValsDecoder codes cs rest (i + 1) with _ | ⟨k, V'⟩
    · rfl
    · simp only [Option.map_some, Option.bind_some, toAVS]
      by_cases h1 : k = (codes (i + 1)).ℓ
      · subst h1
        by_cases h2 : (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ
        · rw [ite_eq_left ⟨rfl, h2⟩, dite_eq_left ⟨rfl, h2⟩,
            upAtA_eq' (two_pow_le_n (codes (i + 1))) h2 (codes i).h64 (codes i).hR V' high]
          exact descendRoundsA_eq _ _ _ (hO i) rounds 0 _
        · rw [ite_eq_right fun h ↦ h2 h.2, dite_eq_right fun h ↦ h2 h.2]
          rfl
      · rw [ite_eq_right fun h ↦ h1 h.1, dite_eq_right fun h ↦ h1 h.1]
        rfl

end
end LeanVM.Protocol.Whir.Sound
