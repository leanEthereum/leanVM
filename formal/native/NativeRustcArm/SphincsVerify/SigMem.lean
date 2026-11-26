module

public import NativeRustcArm.SphincsVerify.Basic
public import NativeRustc.Sphincs.Verify

/-!
# The parsed signature's bytes in the frame

`sigMem r.sig`, the 7740 bytes at `base + 484` (`length_sigMem`): FORS tree `c`'s path node `z`
at `176 c + 16 z` and its secret at `176 c + 160` (`sigMem_path`, `sigMem_secret`), the paths'
node `j` at `4224 + 16 j` (`sigMem_node`, a layer's path: `path_getD`), the randomizer at `4640`
(`sigMem_randomizer`), layer `l`'s chain value `i` at `4656 + 1028 l + 16 i` and its counter at
`4656 + 1028 l + 1024` (`sigMem_wots`, `sigMem_counter`); each value 16 bytes.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs

public section

/-! ## Lists of equal chunks -/

theorem length_flatten_uniform {α : Type} {n : Nat} :
    ∀ (L : List (List α)), (∀ x ∈ L, x.length = n) → L.flatten.length = n * L.length
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append, h x List.mem_cons_self,
      length_flatten_uniform L fun y hy ↦ h y (List.mem_cons_of_mem _ hy), List.length_cons]
    rw [Nat.mul_succ]
    omega

theorem drop_take_append_left {α : Type} (x y : List α) {k m : Nat} (h : k + m ≤ x.length) :
    ((x ++ y).drop k).take m = (x.drop k).take m := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- **Bytes `k .. k + m` of chunk `i`** of a flattened list of `n`-byte chunks. -/
theorem drop_take_flatten {α : Type} {n : Nat} :
    ∀ (L : List (List α)), (∀ x ∈ L, x.length = n) → ∀ {i k m : Nat} (hi : i < L.length),
      k + m ≤ n → (L.flatten.drop (n * i + k)).take m = (L[i].drop k).take m
  | [], _, _, _, _, hi, _ => absurd hi (by simp)
  | x :: L, h, 0, k, m, _, hkm => by
    rw [List.flatten_cons, Nat.mul_zero, Nat.zero_add,
      drop_take_append_left _ _ (by rw [h x List.mem_cons_self]; omega)]
    rfl
  | x :: L, h, i + 1, k, m, hi, hkm => by
    rw [List.flatten_cons, show n * (i + 1) + k = x.length + (n * i + k) by
      rw [h x List.mem_cons_self, Nat.mul_succ]; omega, List.drop_length_add_append,
      drop_take_flatten L (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) (by simpa using hi) hkm]
    rfl

theorem getD_eq_getElem' {α : Type} (L : List α) (d : α) {i : Nat} (hi : i < L.length) :
    L.getD i d = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem length_slice {b : List UInt8} {off len : Nat} (h : off + len ≤ b.length) :
    (slice b off len).length = len := by
  simp only [slice, List.length_take, List.length_drop]
  omega

/-! ## The parsed signature -/

theorem sigLayerOff_le {l : Nat} (hl : l < 3) :
    sigLayerOff l + 1028 + 16 * layerHeights.getD l 0 ≤ 7740 := by
  interval_cases l <;> decide

namespace Run

variable (r : Run)

theorem sig_fors : r.sig.fors = (List.range 24).map fun c ↦ (⟨slice r.sigBytes (16 + 176 * c) 16,
    (List.range 10).map fun z ↦ slice r.sigBytes (32 + 176 * c + 16 * z) 16⟩ : ForsTreeOpening) :=
  rfl

theorem sig_paths : r.sig.paths = (List.range 3).flatMap fun l ↦
    (List.range (layerHeights.getD l 0)).map fun z ↦
      slice r.sigBytes (sigLayerOff l + 1028 + 16 * z) 16 := rfl

theorem sig_layers : r.sig.layers = (List.range 3).map fun l ↦
    (⟨be32Of (slice r.sigBytes (sigLayerOff l) 4), (List.range 64).map fun i ↦
      slice r.sigBytes (sigLayerOff l + 4 + 16 * i) 16⟩ : LayerSignature) := rfl

theorem length_fors : r.sig.fors.length = 24 := by simp [sig_fors]

theorem length_paths : r.sig.paths.length = 26 := by
  rw [sig_paths, show List.range 3 = [0, 1, 2] from rfl]
  simp [layerHeights]

theorem length_layers : r.sig.layers.length = 3 := by simp [sig_layers]

/-- Opening `c`. -/
theorem fors_getD {c : Nat} (hc : c < 24) : r.sig.fors.getD c ⟨[], []⟩ =
    ⟨slice r.sigBytes (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice r.sigBytes (32 + 176 * c + 16 * z) 16⟩ := by
  rw [getD_eq_getElem' _ _ (by rw [length_fors]; exact hc)]
  simp [sig_fors]

/-- Layer `l`. -/
theorem layerSig_eq {l : Nat} (hl : l < 3) : r.layerSig l =
    ⟨be32Of (slice r.sigBytes (sigLayerOff l) 4), (List.range 64).map fun i ↦
      slice r.sigBytes (sigLayerOff l + 4 + 16 * i) 16⟩ := by
  rw [layerSig, getD_eq_getElem' _ _ (by rw [length_layers]; exact hl)]
  simp [sig_layers]

theorem length_openingMem : ∀ o ∈ r.sig.fors, (openingMem o).length = 176 := by
  intro o ho
  rw [sig_fors, List.mem_map] at ho
  obtain ⟨c, hc, rfl⟩ := ho
  rw [List.mem_range] at hc
  have hb := r.hsig
  simp only [openingMem, List.length_append]
  rw [length_flatten_uniform _ (n := 16) (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [List.mem_range] at hz
      exact length_slice (by omega)), length_slice (by omega)]
  simp

theorem layers_getElem {l : Nat} (hl : l < r.sig.layers.length) :
    r.sig.layers[l] = r.layerSig l := (getD_eq_getElem' _ _ hl).symm

theorem length_wots {l : Nat} (hl : l < 3) : (r.layerSig l).wots.length = 64 := by
  rw [r.layerSig_eq hl]
  simp

/-- Layer `l`'s chain value `i`: 16 bytes. -/
theorem length_wots_getD {l i : Nat} (hl : l < 3) (hi : i < 64) :
    ((r.layerSig l).wots.getD i []).length = 16 := by
  have hb := r.hsig
  have := sigLayerOff_le hl
  rw [r.layerSig_eq hl, getD_eq_getElem' _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  exact length_slice (by omega)

theorem length_wots_mem {l : Nat} (hl : l < 3) : ∀ x ∈ (r.layerSig l).wots, x.length = 16 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [r.length_wots hl] at hi
  rw [← getD_eq_getElem' _ [] (by rw [r.length_wots hl]; exact hi)]
  exact r.length_wots_getD hl hi

theorem length_layerMem : ∀ s ∈ r.sig.layers, (layerMem s).length = 1028 := by
  intro s hs
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hs
  have hl3 : l < 3 := by rwa [length_layers] at hl
  rw [r.layers_getElem hl, layerMem, List.length_append,
    length_flatten_uniform _ (r.length_wots_mem hl3), r.length_wots hl3]
  simp [le32, be32]

theorem length_node : ∀ x ∈ r.sig.paths, x.length = 16 := by
  intro x hx
  have hb := r.hsig
  rw [sig_paths, List.mem_flatMap] at hx
  obtain ⟨l, hl, hx⟩ := hx
  rw [List.mem_range] at hl
  rw [List.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [List.mem_range] at hz
  have := sigLayerOff_le hl
  exact length_slice (by omega)

theorem sig_randomizer : r.sig.randomizer = slice r.sigBytes 0 16 := by
  simp only [Run.sig, Signature.fromBytes]

theorem length_randomizer : r.sig.randomizer.length = 16 := by
  rw [sig_randomizer]
  exact length_slice (by rw [r.hsig]; omega)

theorem length_forsMem : ((r.sig.fors.map openingMem).flatten).length = 4224 := by
  rw [length_flatten_uniform (n := 176) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact r.length_openingMem o ho), List.length_map, length_fors]

theorem length_pathsMem : r.sig.paths.flatten.length = 416 := by
  rw [length_flatten_uniform _ r.length_node, length_paths]

theorem length_layersMem : ((r.sig.layers.map layerMem).flatten).length = 3084 := by
  rw [length_flatten_uniform (n := 1028) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact r.length_layerMem s hs), List.length_map, length_layers]

/-- **The parsed signature's 7740 bytes.** -/
theorem length_sigMem : (sigMem r.sig).length = 7740 := by
  rw [sigMem, List.length_append, List.length_append, List.length_append, r.length_forsMem,
    r.length_pathsMem, r.length_randomizer, r.length_layersMem]

/-- The bytes past the FORS openings, the paths and the randomizer: the layers'. -/
theorem sigMem_drop_layers (k : Nat) :
    (sigMem r.sig).drop (4656 + k) = ((r.sig.layers.map layerMem).flatten).drop k := by
  rw [sigMem, show 4656 + k = ((r.sig.fors.map openingMem).flatten).length +
      (r.sig.paths.flatten.length + (r.sig.randomizer.length + k)) by
    rw [r.length_forsMem, r.length_pathsMem, r.length_randomizer]; omega,
    List.drop_length_add_append, List.drop_length_add_append, List.drop_length_add_append]

/-- **Layer `l`'s chain value `i`** at `4656 + 1028 l + 16 i`. -/
theorem sigMem_wots {l i : Nat} (hl : l < 3) (hi : i < 64) :
    ((sigMem r.sig).drop (4656 + 1028 * l + 16 * i)).take 16 = (r.layerSig l).wots.getD i [] := by
  have hwl : ((r.layerSig l).wots.flatten).length = 1024 := by
    rw [length_flatten_uniform _ (r.length_wots_mem hl), r.length_wots hl]
  have hil : i < (r.layerSig l).wots.length := by rw [r.length_wots hl]; exact hi
  rw [Nat.add_assoc, sigMem_drop_layers,
    drop_take_flatten (n := 1028) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact r.length_layerMem s hs) (by simp [length_layers]; omega) (by omega),
    List.getElem_map, r.layers_getElem, layerMem, drop_take_append_left _ _ (by omega),
    show 16 * i = 16 * i + 0 from rfl,
    drop_take_flatten _ (r.length_wots_mem hl) hil (by omega), List.drop_zero,
    getD_eq_getElem' _ _ hil]
  exact List.take_of_length_le (by rw [r.length_wots_mem hl _ (List.getElem_mem _)])

/-- **Layer `l`'s counter** at `4656 + 1028 l + 1024`. -/
theorem sigMem_counter {l : Nat} (hl : l < 3) :
    ((sigMem r.sig).drop (4656 + 1028 * l + 1024)).take 4 = le32 (r.layerSig l).counter := by
  rw [Nat.add_assoc, sigMem_drop_layers,
    drop_take_flatten (n := 1028) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact r.length_layerMem s hs) (by simp [length_layers]; omega) (by omega),
    List.getElem_map, r.layers_getElem, layerMem,
    show 1024 = ((r.layerSig l).wots.flatten).length by
      rw [length_flatten_uniform _ (r.length_wots_mem hl), r.length_wots hl],
    List.drop_left]
  exact List.take_of_length_le (by simp [le32, be32])

/-- **The randomizer** at `4640`. -/
theorem sigMem_randomizer : ((sigMem r.sig).drop 4640).take 16 = r.sig.randomizer := by
  rw [sigMem, show 4640 = ((r.sig.fors.map openingMem).flatten).length +
      (r.sig.paths.flatten.length + 0) by rw [r.length_forsMem, r.length_pathsMem],
    List.drop_length_add_append, List.drop_length_add_append, List.drop_zero,
    List.take_append_of_le_length (by rw [r.length_randomizer]),
    List.take_of_length_le (by rw [r.length_randomizer])]

/-- Layer `l`'s path node `z`: node `(heights below l) + z` of the paths. -/
theorem path_getD {l z : Nat} (hz : z < layerHeights.getD l 0) :
    (r.sig.path l).getD z [] = r.sig.paths.getD ((layerHeights.take l).sum + z) [] := by
  rw [List.getD_eq_getElem?_getD] at hz
  simp only [Signature.path, List.getD_eq_getElem?_getD, List.getElem?_take, hz, ite_true,
    List.getElem?_drop]

/-- **The paths' node `j`** at `4224 + 16 j`. -/
theorem sigMem_node {j : Nat} (hj : j < 26) :
    ((sigMem r.sig).drop (4224 + 16 * j)).take 16 = r.sig.paths.getD j [] := by
  rw [sigMem, show 4224 + 16 * j = ((r.sig.fors.map openingMem).flatten).length + (16 * j + 0) by
      rw [r.length_forsMem]; omega,
    List.drop_length_add_append, drop_take_append_left _ _ (by rw [r.length_pathsMem]; omega),
    drop_take_flatten _ r.length_node (by rw [length_paths]; exact hj) (by omega), List.drop_zero,
    getD_eq_getElem' _ _ (by rw [length_paths]; exact hj)]
  exact List.take_of_length_le (by rw [r.length_node _ (List.getElem_mem _)])

/-- FORS tree `c`'s opening, its path then its secret. -/
theorem sigMem_opening {c k m : Nat} (hc : c < 24) (hkm : k + m ≤ 176) :
    ((sigMem r.sig).drop (176 * c + k)).take m =
      ((openingMem (r.sig.fors.getD c ⟨[], []⟩)).drop k).take m := by
  rw [sigMem, drop_take_append_left _ _ (by rw [r.length_forsMem]; omega),
    drop_take_flatten (n := 176) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨o, ho, rfl⟩ := hx
      exact r.length_openingMem o ho) (by simp [length_fors]; omega) hkm, List.getElem_map,
    getD_eq_getElem' _ _ (by rw [length_fors]; exact hc)]

theorem length_forsPath {c : Nat} (hc : c < 24) : (r.sig.fors.getD c ⟨[], []⟩).path.length = 10 := by
  rw [r.fors_getD hc]
  simp

/-- FORS tree `c`'s path node `z`: 16 bytes. -/
theorem length_forsPath_getD {c z : Nat} (hc : c < 24) (hz : z < 10) :
    ((r.sig.fors.getD c ⟨[], []⟩).path.getD z []).length = 16 := by
  have hb := r.hsig
  rw [r.fors_getD hc, getD_eq_getElem' _ _ (by simpa using hz)]
  simp only [List.getElem_map, List.getElem_range]
  exact length_slice (by omega)

/-- FORS tree `c`'s secret: 16 bytes. -/
theorem length_forsSecret {c : Nat} (hc : c < 24) :
    (r.sig.fors.getD c ⟨[], []⟩).secret.length = 16 := by
  have hb := r.hsig
  rw [r.fors_getD hc]
  exact length_slice (by omega)

theorem length_forsPath_mem {c : Nat} (hc : c < 24) :
    ∀ x ∈ (r.sig.fors.getD c ⟨[], []⟩).path, x.length = 16 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.getElem_of_mem hx
  rw [r.length_forsPath hc] at hz
  rw [← getD_eq_getElem' _ [] (by rw [r.length_forsPath hc]; exact hz)]
  exact r.length_forsPath_getD hc hz

/-- **FORS tree `c`'s path node `z`** at `176 c + 16 z`. -/
theorem sigMem_path {c z : Nat} (hc : c < 24) (hz : z < 10) :
    ((sigMem r.sig).drop (176 * c + 16 * z)).take 16 =
      (r.sig.fors.getD c ⟨[], []⟩).path.getD z [] := by
  have hpl : ((r.sig.fors.getD c ⟨[], []⟩).path.flatten).length = 160 := by
    rw [length_flatten_uniform _ (r.length_forsPath_mem hc), r.length_forsPath hc]
  have hzl : z < (r.sig.fors.getD c ⟨[], []⟩).path.length := by rw [r.length_forsPath hc]; exact hz
  rw [r.sigMem_opening hc (by omega), openingMem, drop_take_append_left _ _ (by omega),
    show 16 * z = 16 * z + 0 from rfl,
    drop_take_flatten _ (r.length_forsPath_mem hc) hzl (by omega), List.drop_zero,
    getD_eq_getElem' _ _ hzl]
  exact List.take_of_length_le (by rw [r.length_forsPath_mem hc _ (List.getElem_mem _)])

/-- **FORS tree `c`'s secret** at `176 c + 160`. -/
theorem sigMem_secret {c : Nat} (hc : c < 24) :
    ((sigMem r.sig).drop (176 * c + 160)).take 16 = (r.sig.fors.getD c ⟨[], []⟩).secret := by
  have hpl : ((r.sig.fors.getD c ⟨[], []⟩).path.flatten).length = 160 := by
    rw [length_flatten_uniform _ (r.length_forsPath_mem hc), r.length_forsPath hc]
  rw [r.sigMem_opening hc (by omega), openingMem, ← hpl, List.drop_left,
    List.take_of_length_le (by rw [r.length_forsSecret hc])]

end Run

end

end NativeRustcArm.SphincsVerifyProof
