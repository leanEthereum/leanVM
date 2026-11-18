/-
  LeanVM.Protocol.Whir.Sound.DescentV

  The descent over values: each tuple carried as its values on the level's domain, each round's
  near tuple decoded over values, each level's low part read off the values on `U_κ`. It is the
  descent over polynomials, evaluated.
-/

module

public import LeanVM.Protocol.Whir.Sound.Descent
public import LeanVM.Protocol.Whir.Sound.LowMsgC

/-!
# The descent over values

The descent (`descendTrace`) carries polynomial tuples, but reads them only through their values
on the level's domain: the agreement set of a round is where the values agree with the fold
(`agreeV_valsT`), a round's near tuple is the decoder's, evaluated (`ValsDecoder`), the next
level up is
read through its low part, which is the inverse transform of its values on `U_κ`
(`lowMsg_eq_novelInvE`), and its high part and the final polynomial are sums over the novel basis
at the point. So the descent over values (`descendRoundsV`, `descendTraceV`), which is computable,
is the descent with the decoder, evaluated (`descendRoundsV_eq`,
`descendTraceV_eq`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Polynomial

@[expose] public section

variable {n : ℕ}

/-- A tuple's values on the domain. -/
noncomputable def valsT (dom : Fin n ↪ E) {m : ℕ} (U : (Fin m → Bool) → E[X]) :
    (Fin m → Bool) → Fin n → E :=
  fun r x ↦ (U r).eval (dom x)

/-- The columns where every lane's values agree with the word. -/
def agreeV {m : ℕ} (V Q : (Fin m → Bool) → Fin n → E) : Finset (Fin n) :=
  Finset.univ.filter fun x ↦ ∀ r, V r x = Q r x

theorem agreeV_valsT (dom : Fin n ↪ E) {m : ℕ} (U : (Fin m → Bool) → E[X])
    (Q : (Fin m → Bool) → Fin n → E) : agreeV (valsT dom U) Q = agreeT dom U Q := by
  ext x
  rw [mem_agreeT, agreeV, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ x, h⟩⟩

/-! ## Decoders over values -/

/-- **A near-tuple decoder over values**: the decoder `D`'s output, evaluated on the domain. -/
structure ValsDecoder (D : NearDecoder) where
  /-- The decoder over values. -/
  decV : ∀ {n m : ℕ}, (Fin n ↪ E) → ℕ → ((Fin (m + 1) → Bool) → Fin n → E) → Finset (Fin n) →
    Option ((Fin (m + 1) → Bool) → Fin n → E)
  /-- It is `D`'s, evaluated. -/
  eq : ∀ {n m : ℕ} (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E)
    (S : Finset (Fin n)), decV dom d Q S = (D.dec dom d Q S).map (valsT dom)

/-! ## Within a level -/

variable {D : NearDecoder} (W : ValsDecoder D)

/-- **The descent within a level, over values.** -/
def descendRoundsV (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) (O : ℕ → Fin n → E)
    (rs : List FoldRound) (m : ℕ) (V : (Fin m → Bool) → Fin n → E) :
    Option (Σ k, (Fin k → Bool) → Fin n → E) :=
  match _h : rs.getLast? with
  | none => some ⟨m, V⟩
  | some r =>
    let Q := rowsOf (m + 1) (foldsA dom rs.dropLast O)
    let S := agreeV V (foldQ dom r.alpha r.beta Q)
    if thr (rs.dropLast.length + 1) ≤ S.card then
      (W.decV dom d Q S).bind fun T ↦ descendRoundsV dom d thr O rs.dropLast (m + 1) T
    else none
termination_by rs.length
decreasing_by
  have : rs ≠ [] := fun h0 ↦ by simp [h0] at _h
  simp only [List.length_dropLast]
  have := List.length_pos_of_ne_nil this
  omega

theorem descendRoundsV_nil (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) (O : ℕ → Fin n → E) (m : ℕ)
    (V : (Fin m → Bool) → Fin n → E) : descendRoundsV W dom d thr O [] m V = some ⟨m, V⟩ := by
  rw [descendRoundsV]; rfl

theorem descendRoundsV_concat (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) (O : ℕ → Fin n → E)
    (rs : List FoldRound) (r : FoldRound) (m : ℕ) (V : (Fin m → Bool) → Fin n → E) :
    descendRoundsV W dom d thr O (rs ++ [r]) m V =
      if thr (rs.length + 1) ≤ (agreeV V (foldQ dom r.alpha r.beta
          (rowsOf (m + 1) (foldsA dom rs O)))).card then
        (W.decV dom d (rowsOf (m + 1) (foldsA dom rs O))
          (agreeV V (foldQ dom r.alpha r.beta (rowsOf (m + 1) (foldsA dom rs O))))).bind
          fun T ↦ descendRoundsV W dom d thr O rs (m + 1) T
      else none := by
  rw [descendRoundsV]
  split
  · rename_i h; simp at h
  · rename_i r' h
    simp only [List.getLast?_concat, Option.some.injEq] at h
    subst h
    simp only [List.dropLast_concat]

/-- The values of a tuple, with its lane count. -/
noncomputable def valsS (dom : Fin n ↪ E) (T : Σ k, (Fin k → Bool) → E[X]) :
    Σ k, (Fin k → Bool) → Fin n → E :=
  ⟨T.1, valsT dom T.2⟩

/-- **The descent within a level over values is the decoder's, evaluated.** -/
theorem descendRoundsV_eq (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) (O : ℕ → Fin n → E) :
    ∀ (rs : List FoldRound) (m : ℕ) (U : (Fin m → Bool) → E[X]),
      descendRoundsV W dom d thr O rs m (valsT dom U) =
        (descendRounds D dom d thr O rs m U).map (valsS dom) := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro m U
    rw [descendRoundsV_nil, descendRounds_nil]
    rfl
  | append_singleton rs r ih =>
    intro m U
    rw [descendRoundsV_concat, descendRounds_concat, agreeV_valsT]
    split_ifs
    · rw [W.eq]
      rcases D.dec dom d (rowsOf (m + 1) (foldsA dom rs O))
        (agreeT dom U (foldQ dom r.alpha r.beta (rowsOf (m + 1) (foldsA dom rs O)))) with _ | T
      · rfl
      · exact ih (m + 1) T
    · rfl

/-! ## Across levels -/

/-- The final polynomial's value at `x_v`. -/
def polyOfAt (cs : List E) (x : K) : E :=
  ∑ c ∈ Finset.range cs.length, cs.getD c 0 * ofK (novelAt c x)

/-- **The next level up, over values**: at `x`, the message of the next level's tuple, read off its
values on `U_κ'`, in the level's novel basis, plus `Ŵ_κ(x)` times the high part. -/
def upAt (κ' m : ℕ) {n' : ℕ} (hn' : 2 ^ κ' ≤ n') {κ : ℕ} (hκ : κ = m + κ')
    (V' : (Fin m → Bool) → Fin n' → E) (high : List E) (x : K) : E :=
  (∑ p : Fin κ → Bool, joinMsg hκ (fun u w ↦ (novelInvE κ' (Array.ofFn fun v : Fin (2 ^ κ') ↦
      V' u (Fin.castLE hn' v))).getD (bitsToNat w) 0) p * ofK (novelAt (bitsToNat p) x)) +
    ofK (normVanishingAt κ x) * polyOfAt high x

/-- `2^κ ≤ 2^(κ+R)`. -/
theorem two_pow_le_n (P : LevelCode) : 2 ^ P.κ ≤ P.n :=
  Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)

/-- **The descent across levels, over values.** -/
def descendTraceV (codes : ℕ → LevelCode) (cs : List (ℕ × ℕ × Word)) :
    WhirTrace → (i : ℕ) → Option (Σ k, (Fin k → Bool) → Fin (codes i).n → E)
  | .final rounds folded, i => descendRoundsV W (codes i).dom (codes i).deg (codes i).thr
      (laneO i cs (codes i).n) rounds 0 fun _ x ↦ polyOfAt folded (K.ofBits x)
  | .mid rounds high rest, i => (descendTraceV codes cs rest (i + 1)).bind fun T' ↦
      if h : T'.1 = (codes (i + 1)).ℓ ∧ (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ then
        descendRoundsV W (codes i).dom (codes i).deg (codes i).thr (laneO i cs (codes i).n) rounds 0
          fun _ x ↦ upAt (codes (i + 1)).κ (codes (i + 1)).ℓ (two_pow_le_n (codes (i + 1))) h.2
            (h.1 ▸ T'.2) high (K.ofBits x)
      else none

theorem polyOfAt_eq (cs : List E) (x : K) : polyOfAt cs x = (polyOf cs).eval (ofK x) :=
  (eval_polyOf cs x).symm

/-- **The next level up, evaluated.** -/
theorem upAt_eq (P' : LevelCode) (m : ℕ) {κ : ℕ} (hκ : κ = m + P'.κ) (hm : m ≤ 64)
    (hκ64 : κ ≤ 64) (T' : (Fin m → Bool) → E[X]) (high : List E) (x : K) :
    upAt P'.κ m (two_pow_le_n P') hκ (valsT P'.dom T') high x =
      (msgPoly κ (joinMsg hκ (msgT P'.κ T')) + hatE κ * polyOf high).eval (ofK x) := by
  have hv : ∀ u, (Array.ofFn fun v : Fin (2 ^ P'.κ) ↦
      valsT P'.dom T' u (Fin.castLE (two_pow_le_n P') v)) = valsU P'.κ (T' u) := fun u ↦ rfl
  rw [eval_add, eval_mul, eval_hatE, eval_msgPoly, ← polyOfAt_eq]
  unfold upAt
  refine congrArg (· + _) (Finset.sum_congr rfl fun p _ ↦ congrArg (· * _) ?_)
  simp only [joinMsg, msgT, hv]
  rw [lowMsg_eq_novelInvE (by have := P'.h64; omega)]

/-- **The descent across levels over values is the decoder's, evaluated.** -/
theorem descendTraceV_eq (codes : ℕ → LevelCode) (cs : List (ℕ × ℕ × Word)) :
    ∀ (tr : WhirTrace) (i : ℕ), descendTraceV W codes cs tr i =
      (descendTrace D codes cs tr i).map (valsS (codes i).dom)
  | .final rounds folded, i => by
    have hU : (fun (_ : Fin 0 → Bool) (x : Fin (codes i).n) ↦ polyOfAt folded (K.ofBits x)) =
        valsT (codes i).dom (fun _ ↦ polyOf folded) := by
      funext _ x
      rw [polyOfAt_eq]
      rfl
    rw [descendTraceV, descendTrace, hU, descendRoundsV_eq W]
  | .mid rounds high rest, i => by
    rw [descendTraceV, descendTrace, descendTraceV_eq codes cs rest (i + 1)]
    rcases descendTrace D codes cs rest (i + 1) with _ | ⟨k, T⟩
    · rfl
    · simp only [Option.map_some, Option.bind_some, valsS]
      by_cases h1 : k = (codes (i + 1)).ℓ
      · subst h1
        by_cases h2 : (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ
        · rw [dite_eq_left ⟨rfl, h2⟩, dite_eq_left ⟨rfl, h2⟩]
          have hU : (fun (_ : Fin 0 → Bool) (x : Fin (codes i).n) ↦
              upAt (codes (i + 1)).κ (codes (i + 1)).ℓ (two_pow_le_n (codes (i + 1))) h2
                (valsT (codes (i + 1)).dom T) high (K.ofBits x)) =
              valsT (codes i).dom (fun _ ↦ msgPoly (codes i).κ (joinMsg h2
                (msgT (codes (i + 1)).κ T)) + hatE (codes i).κ * polyOf high) := by
            funext _ x
            exact upAt_eq (codes (i + 1)) _ h2 (by have := (codes i).h64; omega)
              (by have := (codes i).h64; omega) T high (K.ofBits x)
          have := descendRoundsV_eq W (codes i).dom (codes i).deg (codes i).thr
            (laneO i cs (codes i).n) rounds 0 (fun _ ↦ msgPoly (codes i).κ (joinMsg h2
              (msgT (codes (i + 1)).κ T)) + hatE (codes i).κ * polyOf high)
          rw [← hU] at this
          exact this
        · simp only [h2, and_false, ↓reduceDIte, Option.map_none]
      · have h : ¬ (k = (codes (i + 1)).ℓ ∧
            (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ) := fun h ↦ h1 h.1
        simp only [h, ↓reduceDIte, Option.map_none]

end
end LeanVM.Protocol.Whir.Sound
