/-
  LeanVM.Prover.Gkr

  The executable batched GKR (`Statement/Prover/Gkr.lean`) makes the moves of the
  specification's honest GKR (`hGkr`), and ends at the leaves' extensions at its point.
-/

module

public import LeanVM.Prover.GkrRound

/-!
# The batched GKR

* `getD_treeLayers`: the stored layers are the specification's `up k L`;
* `corr_gkrStep`: one step (`gkrStepA`) makes the moves of `hStep`, to the same state, whose values
  are the layers' extensions at its point;
* `corr_gkrLayers`: the walk;
* `corr_gkrA`: **the GKR makes the moves of `hGkr`**, to the same result, the point of `D`
  coordinates and the values the three leaf lists' extensions there.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd.Complete Finset

@[expose] public section

/-! ## The layers -/

theorem toList_mulPairsA (t : Array E) : (mulPairsA t).toList = mulPairs t.toList := by
  apply List.ext_getElem (by simp [mulPairsA, length_mulPairs])
  intro i h1 h2
  have hi : i < t.size / 2 := by simpa [mulPairsA] using h1
  have h := getD_mulPairs t.toList i (by simp; omega)
  rw [List.getD_eq_getElem _ _ h2] at h
  rw [h]
  simp [mulPairsA, List.getD_eq_getElem?_getD, show 2 * i < t.size by omega,
    show 2 * i + 1 < t.size by omega]

/-- **The stored layers are the tree's.** -/
theorem getD_treeLayers : ∀ (n : ℕ) (t : Array E) (k : ℕ), k ≤ n →
    ((treeLayers n t).getD k #[]).toList = up k t.toList
  | 0, t, k, hk => by
    obtain rfl : k = 0 := by omega
    rfl
  | n + 1, t, 0, _ => rfl
  | n + 1, t, k + 1, hk => by
    rw [treeLayers, List.getD_cons_succ, getD_treeLayers n (mulPairsA t) k (by omega),
      toList_mulPairsA, up_add k 1, up_succ 0]
    rfl

/-- The root of a tree is the leaves' product. -/
theorem root_eq_prod {A : List (Array E)} {L : List E} {D : ℕ} (hL : L.length = 2 ^ D)
    (hA : ∀ k ≤ D, (A.getD k #[]).toList = up k L) : (A.getD D #[]).getD 0 0 = L.prod := by
  have hl := length_up D 0 L (by rw [hL, zero_add])
  have hp := prod_up D 0 L (by rw [hL, zero_add])
  rw [getD_toList, hA D le_rfl]
  rcases hu : up D L with _ | ⟨a, _ | ⟨b, t⟩⟩
  · rw [hu] at hl; simp at hl
  · rw [hu] at hp; simpa using hp
  · rw [hu] at hl; simp at hl

/-! ## One step -/

/-- The invariant of a step's sumcheck after the challenges `pre`: the remaining coordinates, and
the three folded layers. -/
def StepInv (C₀ C₁ C₂ : List E) (h : ℕ) (p pre : List E) (st : GkrFold) : Prop :=
  pre.length ≤ p.length ∧ st.rest = p.drop pre.length ∧
    TabInv C₀ st.t₀ h pre (p.length - pre.length) ∧ TabInv C₁ st.t₁ h pre (p.length - pre.length) ∧
    TabInv C₂ st.t₂ h pre (p.length - pre.length)

/-- **One step makes the moves of `hStep`**, to the same state: its point has the layer's
coordinates, its values the layers' extensions there. -/
theorem corr_gkrStep {L₀ L₁ L₂ : List E} {D k h : ℕ} (h₀ : L₀.length = 2 ^ D)
    (h₁ : L₁.length = 2 ^ D) (h₂ : L₂.length = 2 ^ D) {T₀ T₁ T₂ : Array E}
    (hT₀ : T₀.toList = up k L₀) (hT₁ : T₁.toList = up k L₁) (hT₂ : T₂.toList = up k L₂)
    (s : GkrState) (hs : s.point.length + k + h = D) (hh : h ≤ 2) :
    Corr (fun a b ↦ a = b ∧ b.point.length + k = D ∧
        b.values = [multilinearEval (up k L₀) b.point, multilinearEval (up k L₁) b.point,
          multilinearEval (up k L₂) b.point])
      (gkrStepA T₀ T₁ T₂ h s) (hStep L₀ L₁ L₂ k h s) := by
  have hC : ∀ L : List E, L.length = 2 ^ D → (up k L).length = 2 ^ (h + s.point.length) :=
    fun L hL ↦ length_up k (h + s.point.length) L (by rw [hL]; congr 1; omega)
  have hC' : ∀ L : List E, L.length = 2 ^ D → ∀ pre : List E, pre.length < s.point.length →
      (up k L).length = 2 ^ (h + pre.length + 1 + (s.point.length - (pre.length + 1))) :=
    fun L hL pre hpre ↦ by rw [hC L hL]; congr 1; omega
  have hcount : 2 ^ h + 1 ≤ 2 ^ 192 := by
    have : 2 ^ h ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hh
    have : 2 ^ 2 + 1 ≤ 2 ^ 192 := by norm_num
    omega
  unfold gkrStepA hStep
  refine Corr.bind_same _ fun c ↦ ?_
  have hround : ∀ pre st, StepInv (up k L₀) (up k L₁) (up k L₂) h s.point pre st →
      pre.length < s.point.length → (gkrRound h c st).length = 2 ^ h + 1 ∧
        ∀ x, polyEval (gkrRound h c st) x =
          stepClaim (up k L₀) (up k L₁) (up k L₂) h s.point c (pre ++ [x]) := by
    rintro pre st ⟨-, hrest, hI₀, hI₁, hI₂⟩ hlt
    have hr : s.point.length - pre.length = s.point.length - (pre.length + 1) + 1 := by omega
    rw [hr] at hI₀ hI₁ hI₂
    exact ⟨length_gkrRound h c st, fun x ↦ gkrRound_eval hrest (hC' L₀ h₀ pre hlt)
      (hC' L₁ h₁ pre hlt) (hC' L₂ h₂ pre hlt) hI₀ hI₁ hI₂ x⟩
  have hfold : ∀ pre st c', StepInv (up k L₀) (up k L₁) (up k L₂) h s.point pre st →
      pre.length < s.point.length →
      StepInv (up k L₀) (up k L₁) (up k L₂) h s.point (pre ++ [c']) (gkrFold h st c') := by
    rintro pre st c' ⟨-, hrest, hI₀, hI₁, hI₂⟩ hlt
    have hr : s.point.length - pre.length = s.point.length - (pre.length + 1) + 1 := by omega
    rw [hr] at hI₀ hI₁ hI₂
    have hr' : s.point.length - (pre ++ [c']).length = s.point.length - (pre.length + 1) := by
      simp
    refine ⟨by simp; omega, by simp [gkrFold, hrest, List.tail_drop], ?_, ?_, ?_⟩ <;>
      rw [hr'] <;> simp only [gkrFold]
    · exact tabInv_fold (hC' L₀ h₀ pre hlt) hI₀ c'
    · exact tabInv_fold (hC' L₁ h₁ pre hlt) hI₁ c'
    · exact tabInv_fold (hC' L₂ h₂ pre hlt) hI₂ c'
  have hinit : StepInv (up k L₀) (up k L₁) (up k L₂) h s.point [] ⟨T₀, T₁, T₂, s.point⟩ :=
    ⟨Nat.zero_le _, rfl, tabInv_init hT₀ (hC L₀ h₀), tabInv_init hT₁ (hC L₁ h₁),
      tabInv_init hT₂ (hC L₂ h₂)⟩
  refine Corr.bind (fun a b hab ↦ ?_) _ _
    (corr_sumcheckBy_lt (2 ^ h + 1) (by have := Nat.one_le_two_pow (n := h); omega) hcount _
      (gkrRound h c) (gkrFold h) _
      s.point.length hround hfold (s.point.map some) [] ⟨T₀, T₁, T₂, s.point⟩ hinit (by simp))
  obtain ⟨hab, hlen, -, -, hI₀, hI₁, hI₂⟩ := hab
  simp only [List.nil_append, List.length_map] at hlen hI₀ hI₁ hI₂
  rw [hlen, Nat.sub_self] at hI₀ hI₁ hI₂
  rw [toList_eq_child hI₀, toList_eq_child hI₁, toList_eq_child hI₂, hab]
  refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦
    Corr.bind_allRet (fun y hy ↦ ?_) _ (allRet_sampleN h)
  have hx : b.1.length = s.point.length := by rw [← hab, hlen]
  refine ⟨rfl, by simp only [List.length_append, hy, hx]; omega, ?_⟩
  simp only
  rw [multilinearEval_child (hC L₀ h₀) hx hy, multilinearEval_child (hC L₁ h₁) hx hy,
    multilinearEval_child (hC L₂ h₂) hx hy]

/-! ## The walk -/

/-- The walk's invariant `n` levels above the leaves: the point has the layer's coordinates, and
below the roots the values are the layers' extensions there. -/
def LayerInv (L₀ L₁ L₂ : List E) (D n : ℕ) (s : GkrState) : Prop :=
  s.point.length + n = D ∧ (n < D → s.values = [multilinearEval (up n L₀) s.point,
    multilinearEval (up n L₁) s.point, multilinearEval (up n L₂) s.point])

/-- **The walk makes the moves of `hLayers`.** -/
theorem corr_gkrLayers {L₀ L₁ L₂ : List E} {D : ℕ} (h₀ : L₀.length = 2 ^ D)
    (h₁ : L₁.length = 2 ^ D) (h₂ : L₂.length = 2 ^ D) {A₀ A₁ A₂ : List (Array E)}
    (hA₀ : ∀ k ≤ D, (A₀.getD k #[]).toList = up k L₀)
    (hA₁ : ∀ k ≤ D, (A₁.getD k #[]).toList = up k L₁)
    (hA₂ : ∀ k ≤ D, (A₂.getD k #[]).toList = up k L₂) :
    ∀ (n : ℕ) (s : GkrState), LayerInv L₀ L₁ L₂ D n s →
      Corr (fun a b ↦ a = b ∧ LayerInv L₀ L₁ L₂ D 0 b)
        (gkrLayersA A₀ A₁ A₂ n s) (hLayers L₀ L₁ L₂ n s)
  | 0, s, hQ => ⟨rfl, hQ⟩
  | 1, s, hQ => by
    have hD := hQ.1
    simp only [gkrLayersA, hLayers]
    refine Corr.bind (fun a b hab ↦ ?_) _ _
      (corr_gkrStep h₀ h₁ h₂ (hA₀ 0 (by omega)) (hA₁ 0 (by omega)) (hA₂ 0 (by omega)) s
        (by omega) (by norm_num))
    obtain ⟨rfl, hpl, hv⟩ := hab
    exact corr_gkrLayers h₀ h₁ h₂ hA₀ hA₁ hA₂ 0 a ⟨hpl, fun _ ↦ hv⟩
  | n + 2, s, hQ => by
    have hD := hQ.1
    simp only [gkrLayersA, hLayers]
    split_ifs
    · refine Corr.bind (fun a b hab ↦ ?_) _ _
        (corr_gkrStep h₀ h₁ h₂ (hA₀ (n + 1) (by omega)) (hA₁ (n + 1) (by omega))
          (hA₂ (n + 1) (by omega)) s (by omega) (by norm_num))
      obtain ⟨rfl, hpl, hv⟩ := hab
      exact corr_gkrLayers h₀ h₁ h₂ hA₀ hA₁ hA₂ (n + 1) a ⟨hpl, fun _ ↦ hv⟩
    · refine Corr.bind (fun a b hab ↦ ?_) _ _
        (corr_gkrStep h₀ h₁ h₂ (hA₀ n (by omega)) (hA₁ n (by omega)) (hA₂ n (by omega)) s
          (by omega) (by norm_num))
      obtain ⟨rfl, hpl, hv⟩ := hab
      exact corr_gkrLayers h₀ h₁ h₂ hA₀ hA₁ hA₂ n a ⟨hpl, fun _ ↦ hv⟩

/-! ## The GKR -/

/-- **The batched GKR makes the moves of `hGkr`**, to the same result: the third root, a point of
`D` coordinates, and the three leaf lists' extensions there. -/
theorem corr_gkrA {L₀ L₁ L₂ : List E} {D : ℕ} (hD : 0 < D) (h₀ : L₀.length = 2 ^ D)
    (h₁ : L₁.length = 2 ^ D) (h₂ : L₂.length = 2 ^ D) {A₀ A₁ A₂ : List (Array E)}
    (hA₀ : ∀ k ≤ D, (A₀.getD k #[]).toList = up k L₀)
    (hA₁ : ∀ k ≤ D, (A₁.getD k #[]).toList = up k L₁)
    (hA₂ : ∀ k ≤ D, (A₂.getD k #[]).toList = up k L₂) :
    Corr (fun a b ↦ a = b ∧ b.2.1.length = D ∧
        b.2.2 = [multilinearEval L₀ b.2.1, multilinearEval L₁ b.2.1, multilinearEval L₂ b.2.1])
      (gkrA D A₀ A₁ A₂) (hGkr D L₀ L₁ L₂) := by
  unfold gkrA hGkr
  simp only [root_eq_prod h₀ hA₀, root_eq_prod h₂ hA₂]
  refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ Corr.bind (fun a b hab ↦ ?_) _ _
    (corr_gkrLayers h₀ h₁ h₂ hA₀ hA₁ hA₂ D _ ⟨by simp, fun h ↦ absurd h (lt_irrefl D)⟩)
  obtain ⟨rfl, hpl, hv⟩ := hab
  exact ⟨rfl, by simpa using hpl, hv hD⟩

end
end LeanVM.Prover
