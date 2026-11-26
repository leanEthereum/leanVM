module

public import NativeRustc.Sphincs.Verify
import Mathlib.Tactic.IntervalCases

/-!
# The parsed signature in rustc's layout

`LeanSphincsSignature` as rustc lays it out in memory (`sigMem`, 7740 bytes): the 24 FORS
openings (`openingMem`: the path, then the secret, 176 bytes each), the 26 path nodes, the
randomizer, the three layers (`layerMem`: 64 chain values then the counter, `le32`, 1028 bytes
each). For the signature parsed from the input words `w` (`sigOf w`): FORS tree `c`'s path node
`z` at `176 c + 16 z` and its secret at `176 c + 160` (`sigMem_path`, `sigMem_secret`), the paths'
node `j` at `4224 + 16 j` (`sigMem_node`; a layer's path: `path_getD`), the randomizer at `4640`
(`sigMem_randomizer`), layer `l`'s chain value `i` at `4656 + 1028 l + 16 i` and its counter at
`4656 + 1028 l + 1024` (`sigMem_wots`, `sigMem_counter`); each value 16 bytes. Arch-independent:
the x86-64 proof's frame holds it at `20540`.
-/

namespace NativeRustc.Sphincs

open LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- `u32`'s bytes in memory. -/
def le32 (x : UInt32) : List UInt8 := (be32 x).reverse

/-- A FORS opening: its path, then its secret. -/
def openingMem (o : ForsTreeOpening) : List UInt8 := o.path.flatten ++ o.secret

/-- A layer's signature: its chain values, then its counter. -/
def layerMem (s : LayerSignature) : List UInt8 := s.wots.flatten ++ le32 s.counter

/-- **`LeanSphincsSignature` in rustc's layout**: the FORS openings, the paths, the randomizer,
the layers. -/
def sigMem (s : Signature) : List UInt8 :=
  (s.fors.map openingMem).flatten ++ (s.paths.flatten ++ (s.randomizer ++
    (s.layers.map layerMem).flatten))

/-- The signature parsed from the input words. -/
abbrev sigOf (w : Nat → UInt64) : Signature := Signature.fromBytes (sigBytes w)

/-- The signature parsed from raw signature bytes. -/
abbrev sigOfBytes (sb : List UInt8) : Signature := Signature.fromBytes sb

end

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

theorem length_sigBytes (w : Nat → UInt64) : (sigBytes w).length = 7740 := by
  rw [sigBytes_eq]
  simp only [List.length_append, length_headBytes, length_layerBytes]
  rfl

theorem sigLayerOff_le {l : Nat} (hl : l < 3) :
    sigLayerOff l + 1028 + 16 * layerHeights.getD l 0 ≤ 7740 := by
  interval_cases l <;> decide

namespace SigMem

variable (w : Nat → UInt64)

theorem sig_fors : (sigOf w).fors = (List.range 24).map fun c ↦
    (⟨slice (sigBytes w) (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice (sigBytes w) (32 + 176 * c + 16 * z) 16⟩ : ForsTreeOpening) :=
  rfl

theorem sig_paths : (sigOf w).paths = (List.range 3).flatMap fun l ↦
    (List.range (layerHeights.getD l 0)).map fun z ↦
      slice (sigBytes w) (sigLayerOff l + 1028 + 16 * z) 16 := rfl

theorem sig_layers : (sigOf w).layers = (List.range 3).map fun l ↦
    (⟨be32Of (slice (sigBytes w) (sigLayerOff l) 4), (List.range 64).map fun i ↦
      slice (sigBytes w) (sigLayerOff l + 4 + 16 * i) 16⟩ : LayerSignature) := rfl

theorem length_fors : (sigOf w).fors.length = 24 := by simp [sig_fors]

theorem length_paths : (sigOf w).paths.length = 26 := by
  simp [sig_paths, List.flatMap, layerHeights, show List.range 3 = [0, 1, 2] from rfl]

theorem length_layers : (sigOf w).layers.length = 3 := by simp [sig_layers]

/-- Opening `c`. -/
theorem fors_getD {c : Nat} (hc : c < 24) : (sigOf w).fors.getD c ⟨[], []⟩ =
    ⟨slice (sigBytes w) (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice (sigBytes w) (32 + 176 * c + 16 * z) 16⟩ := by
  rw [getD_eq_getElem' _ _ (by rw [length_fors]; exact hc)]
  simp [sig_fors]

/-- Layer `l`. -/
theorem layers_getD {l : Nat} (hl : l < 3) : (sigOf w).layers.getD l ⟨0, []⟩ =
    ⟨be32Of (slice (sigBytes w) (sigLayerOff l) 4), (List.range 64).map fun i ↦
      slice (sigBytes w) (sigLayerOff l + 4 + 16 * i) 16⟩ := by
  rw [getD_eq_getElem' _ _ (by rw [length_layers]; exact hl)]
  simp [sig_layers]

theorem length_openingMem : ∀ o ∈ (sigOf w).fors, (openingMem o).length = 176 := by
  intro o ho
  rw [sig_fors, List.mem_map] at ho
  obtain ⟨c, hc, rfl⟩ := ho
  rw [List.mem_range] at hc
  have hb := length_sigBytes w
  simp only [openingMem, List.length_append]
  rw [length_flatten_uniform _ (n := 16) (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [List.mem_range] at hz
      exact length_slice (by omega)), length_slice (by omega)]
  simp

theorem layers_getElem {l : Nat} (hl : l < (sigOf w).layers.length) :
    (sigOf w).layers[l] = (sigOf w).layers.getD l ⟨0, []⟩ := (getD_eq_getElem' _ _ hl).symm

theorem length_wots {l : Nat} (hl : l < 3) : ((sigOf w).layers.getD l ⟨0, []⟩).wots.length = 64 := by
  rw [layers_getD w hl]
  simp

/-- Layer `l`'s chain value `i`: 16 bytes. -/
theorem length_wots_getD {l i : Nat} (hl : l < 3) (hi : i < 64) :
    (((sigOf w).layers.getD l ⟨0, []⟩).wots.getD i []).length = 16 := by
  have hb := length_sigBytes w
  have := sigLayerOff_le hl
  rw [layers_getD w hl, getD_eq_getElem' _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  exact length_slice (by omega)

theorem length_wots_mem {l : Nat} (hl : l < 3) :
    ∀ x ∈ ((sigOf w).layers.getD l ⟨0, []⟩).wots, x.length = 16 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [length_wots w hl] at hi
  rw [← getD_eq_getElem' _ [] (by rw [length_wots w hl]; exact hi)]
  exact length_wots_getD w hl hi

theorem length_layerMem : ∀ s ∈ (sigOf w).layers, (layerMem s).length = 1028 := by
  intro s hs
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hs
  have hl3 : l < 3 := by rwa [length_layers] at hl
  rw [layers_getElem w hl, layerMem, List.length_append,
    length_flatten_uniform _ (length_wots_mem w hl3), length_wots w hl3]
  simp [le32, be32]

theorem length_node : ∀ x ∈ (sigOf w).paths, x.length = 16 := by
  intro x hx
  have hb := length_sigBytes w
  rw [sig_paths, List.mem_flatMap] at hx
  obtain ⟨l, hl, hx⟩ := hx
  rw [List.mem_range] at hl
  rw [List.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [List.mem_range] at hz
  have := sigLayerOff_le hl
  exact length_slice (by omega)

theorem sig_randomizer : (sigOf w).randomizer = slice (sigBytes w) 0 16 := by
  simp only [Signature.fromBytes]

theorem length_randomizer : (sigOf w).randomizer.length = 16 := by
  rw [sig_randomizer]
  exact length_slice (by rw [length_sigBytes]; omega)

theorem length_forsMem : (((sigOf w).fors.map openingMem).flatten).length = 4224 := by
  rw [length_flatten_uniform (n := 176) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact length_openingMem w o ho), List.length_map, length_fors]

theorem length_pathsMem : (sigOf w).paths.flatten.length = 416 := by
  rw [length_flatten_uniform _ (length_node w), length_paths]

theorem length_layersMem : (((sigOf w).layers.map layerMem).flatten).length = 3084 := by
  rw [length_flatten_uniform (n := 1028) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact length_layerMem w s hs), List.length_map, length_layers]

/-- **The parsed signature's 7740 bytes.** -/
theorem length_sigMem : (sigMem (sigOf w)).length = 7740 := by
  rw [sigMem, List.length_append, List.length_append, List.length_append, length_forsMem,
    length_pathsMem, length_randomizer, length_layersMem]

/-- The bytes past the FORS openings, the paths and the randomizer: the layers'. -/
theorem sigMem_drop_layers (k : Nat) :
    (sigMem (sigOf w)).drop (4656 + k) = (((sigOf w).layers.map layerMem).flatten).drop k := by
  rw [sigMem, show 4656 + k = (((sigOf w).fors.map openingMem).flatten).length +
      ((sigOf w).paths.flatten.length + ((sigOf w).randomizer.length + k)) by
    rw [length_forsMem, length_pathsMem, length_randomizer]; omega,
    List.drop_length_add_append, List.drop_length_add_append, List.drop_length_add_append]

/-- **Layer `l`'s chain value `i`** at `4656 + 1028 l + 16 i`. -/
theorem sigMem_wots {l i : Nat} (hl : l < 3) (hi : i < 64) :
    ((sigMem (sigOf w)).drop (4656 + 1028 * l + 16 * i)).take 16 =
      ((sigOf w).layers.getD l ⟨0, []⟩).wots.getD i [] := by
  have hil : i < ((sigOf w).layers.getD l ⟨0, []⟩).wots.length := by
    rw [length_wots w hl]; exact hi
  rw [Nat.add_assoc, sigMem_drop_layers,
    drop_take_flatten (n := 1028) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact length_layerMem w s hs) (by simp [length_layers]; omega) (by omega),
    List.getElem_map, layers_getElem w, layerMem, drop_take_append_left _ _ (by
      rw [length_flatten_uniform _ (length_wots_mem w hl), length_wots w hl]; omega),
    show 16 * i = 16 * i + 0 from rfl,
    drop_take_flatten _ (length_wots_mem w hl) hil (by omega), List.drop_zero,
    getD_eq_getElem' _ _ hil]
  exact List.take_of_length_le (by rw [length_wots_mem w hl _ (List.getElem_mem _)])

/-- **Layer `l`'s counter** at `4656 + 1028 l + 1024`. -/
theorem sigMem_counter {l : Nat} (hl : l < 3) :
    ((sigMem (sigOf w)).drop (4656 + 1028 * l + 1024)).take 4 =
      le32 ((sigOf w).layers.getD l ⟨0, []⟩).counter := by
  rw [Nat.add_assoc, sigMem_drop_layers,
    drop_take_flatten (n := 1028) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact length_layerMem w s hs) (by simp [length_layers]; omega) (by omega),
    List.getElem_map, layers_getElem w, layerMem,
    show 1024 = (((sigOf w).layers.getD l ⟨0, []⟩).wots.flatten).length by
      rw [length_flatten_uniform _ (length_wots_mem w hl), length_wots w hl],
    List.drop_left]
  exact List.take_of_length_le (by simp [le32, be32])

/-- **The randomizer** at `4640`. -/
theorem sigMem_randomizer : ((sigMem (sigOf w)).drop 4640).take 16 = (sigOf w).randomizer := by
  rw [sigMem, show 4640 = (((sigOf w).fors.map openingMem).flatten).length +
      ((sigOf w).paths.flatten.length + 0) by rw [length_forsMem, length_pathsMem],
    List.drop_length_add_append, List.drop_length_add_append, List.drop_zero,
    List.take_append_of_le_length (by rw [length_randomizer]),
    List.take_of_length_le (by rw [length_randomizer])]

/-- Layer `l`'s path node `z`: node `(heights below l) + z` of the paths. -/
theorem path_getD {l z : Nat} (hz : z < layerHeights.getD l 0) :
    ((sigOf w).path l).getD z [] = (sigOf w).paths.getD ((layerHeights.take l).sum + z) [] := by
  rw [List.getD_eq_getElem?_getD] at hz
  simp only [Signature.path, List.getD_eq_getElem?_getD, List.getElem?_take, hz, ite_true,
    List.getElem?_drop]

/-- **The paths' node `j`** at `4224 + 16 j`. -/
theorem sigMem_node {j : Nat} (hj : j < 26) :
    ((sigMem (sigOf w)).drop (4224 + 16 * j)).take 16 = (sigOf w).paths.getD j [] := by
  rw [sigMem, show 4224 + 16 * j = (((sigOf w).fors.map openingMem).flatten).length + (16 * j + 0) by
      rw [length_forsMem]; omega,
    List.drop_length_add_append, drop_take_append_left _ _ (by rw [length_pathsMem]; omega),
    drop_take_flatten _ (length_node w) (by rw [length_paths]; exact hj) (by omega),
    List.drop_zero, getD_eq_getElem' _ _ (by rw [length_paths]; exact hj)]
  exact List.take_of_length_le (by rw [length_node w _ (List.getElem_mem _)])

/-- FORS tree `c`'s opening, its path then its secret. -/
theorem sigMem_opening {c k m : Nat} (hc : c < 24) (hkm : k + m ≤ 176) :
    ((sigMem (sigOf w)).drop (176 * c + k)).take m =
      ((openingMem ((sigOf w).fors.getD c ⟨[], []⟩)).drop k).take m := by
  rw [sigMem, drop_take_append_left _ _ (by rw [length_forsMem]; omega),
    drop_take_flatten (n := 176) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨o, ho, rfl⟩ := hx
      exact length_openingMem w o ho) (by simp [length_fors]; omega) hkm, List.getElem_map,
    getD_eq_getElem' _ _ (by rw [length_fors]; exact hc)]

theorem length_forsPath {c : Nat} (hc : c < 24) :
    ((sigOf w).fors.getD c ⟨[], []⟩).path.length = 10 := by
  rw [fors_getD w hc]
  simp

/-- FORS tree `c`'s path node `z`: 16 bytes. -/
theorem length_forsPath_getD {c z : Nat} (hc : c < 24) (hz : z < 10) :
    (((sigOf w).fors.getD c ⟨[], []⟩).path.getD z []).length = 16 := by
  have hb := length_sigBytes w
  rw [fors_getD w hc, getD_eq_getElem' _ _ (by simpa using hz)]
  simp only [List.getElem_map, List.getElem_range]
  exact length_slice (by omega)

/-- FORS tree `c`'s secret: 16 bytes. -/
theorem length_forsSecret {c : Nat} (hc : c < 24) :
    ((sigOf w).fors.getD c ⟨[], []⟩).secret.length = 16 := by
  have hb := length_sigBytes w
  rw [fors_getD w hc]
  exact length_slice (by omega)

theorem length_forsPath_mem {c : Nat} (hc : c < 24) :
    ∀ x ∈ ((sigOf w).fors.getD c ⟨[], []⟩).path, x.length = 16 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.getElem_of_mem hx
  rw [length_forsPath w hc] at hz
  rw [← getD_eq_getElem' _ [] (by rw [length_forsPath w hc]; exact hz)]
  exact length_forsPath_getD w hc hz

/-- **FORS tree `c`'s path node `z`** at `176 c + 16 z`. -/
theorem sigMem_path {c z : Nat} (hc : c < 24) (hz : z < 10) :
    ((sigMem (sigOf w)).drop (176 * c + 16 * z)).take 16 =
      ((sigOf w).fors.getD c ⟨[], []⟩).path.getD z [] := by
  have hpl : (((sigOf w).fors.getD c ⟨[], []⟩).path.flatten).length = 160 := by
    rw [length_flatten_uniform _ (length_forsPath_mem w hc), length_forsPath w hc]
  have hzl : z < ((sigOf w).fors.getD c ⟨[], []⟩).path.length := by
    rw [length_forsPath w hc]; exact hz
  rw [sigMem_opening w hc (by omega), openingMem, drop_take_append_left _ _ (by omega),
    show 16 * z = 16 * z + 0 from rfl,
    drop_take_flatten _ (length_forsPath_mem w hc) hzl (by omega), List.drop_zero,
    getD_eq_getElem' _ _ hzl]
  exact List.take_of_length_le (by rw [length_forsPath_mem w hc _ (List.getElem_mem _)])

/-- **FORS tree `c`'s secret** at `176 c + 160`. -/
theorem sigMem_secret {c : Nat} (hc : c < 24) :
    ((sigMem (sigOf w)).drop (176 * c + 160)).take 16 = ((sigOf w).fors.getD c ⟨[], []⟩).secret := by
  have hpl : (((sigOf w).fors.getD c ⟨[], []⟩).path.flatten).length = 160 := by
    rw [length_flatten_uniform _ (length_forsPath_mem w hc), length_forsPath w hc]
  rw [sigMem_opening w hc (by omega), openingMem, ← hpl, List.drop_left,
    List.take_of_length_le (by rw [length_forsSecret w hc])]

end SigMem

namespace SigMemBytes

variable (sb : List UInt8)

theorem sig_fors : (sigOfBytes sb).fors = (List.range 24).map fun c ↦
    (⟨slice sb (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice sb (32 + 176 * c + 16 * z) 16⟩ : ForsTreeOpening) :=
  rfl

theorem sig_paths : (sigOfBytes sb).paths = (List.range 3).flatMap fun l ↦
    (List.range (layerHeights.getD l 0)).map fun z ↦
      slice sb (sigLayerOff l + 1028 + 16 * z) 16 := rfl

theorem sig_layers : (sigOfBytes sb).layers = (List.range 3).map fun l ↦
    (⟨be32Of (slice sb (sigLayerOff l) 4), (List.range 64).map fun i ↦
      slice sb (sigLayerOff l + 4 + 16 * i) 16⟩ : LayerSignature) := rfl

theorem length_fors : (sigOfBytes sb).fors.length = 24 := by simp [sig_fors]

theorem length_paths : (sigOfBytes sb).paths.length = 26 := by
  simp [sig_paths, List.flatMap, layerHeights, show List.range 3 = [0, 1, 2] from rfl]

theorem length_layers : (sigOfBytes sb).layers.length = 3 := by simp [sig_layers]

theorem fors_getD {c : Nat} (hc : c < 24) : (sigOfBytes sb).fors.getD c ⟨[], []⟩ =
    ⟨slice sb (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice sb (32 + 176 * c + 16 * z) 16⟩ := by
  rw [getD_eq_getElem' _ _ (by rw [length_fors]; exact hc)]
  simp [sig_fors]

theorem layers_getD {l : Nat} (hl : l < 3) : (sigOfBytes sb).layers.getD l ⟨0, []⟩ =
    ⟨be32Of (slice sb (sigLayerOff l) 4), (List.range 64).map fun i ↦
      slice sb (sigLayerOff l + 4 + 16 * i) 16⟩ := by
  rw [getD_eq_getElem' _ _ (by rw [length_layers]; exact hl)]
  simp [sig_layers]

theorem length_openingMem (hsb : sb.length = 7740) :
    ∀ o ∈ (sigOfBytes sb).fors, (openingMem o).length = 176 := by
  intro o ho
  rw [sig_fors, List.mem_map] at ho
  obtain ⟨c, hc, rfl⟩ := ho
  rw [List.mem_range] at hc
  simp only [openingMem, List.length_append]
  rw [length_flatten_uniform _ (n := 16) (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [List.mem_range] at hz
      exact length_slice (by omega)), length_slice (by omega)]
  simp

theorem layers_getElem {l : Nat} (hl : l < (sigOfBytes sb).layers.length) :
    (sigOfBytes sb).layers[l] = (sigOfBytes sb).layers.getD l ⟨0, []⟩ := (getD_eq_getElem' _ _ hl).symm

theorem length_wots {l : Nat} (hl : l < 3) : ((sigOfBytes sb).layers.getD l ⟨0, []⟩).wots.length = 64 := by
  rw [layers_getD sb hl]
  simp

theorem length_wots_getD (hsb : sb.length = 7740) {l i : Nat} (hl : l < 3) (hi : i < 64) :
    (((sigOfBytes sb).layers.getD l ⟨0, []⟩).wots.getD i []).length = 16 := by
  have := sigLayerOff_le hl
  rw [layers_getD sb hl, getD_eq_getElem' _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  exact length_slice (by omega)

theorem length_wots_mem (hsb : sb.length = 7740) {l : Nat} (hl : l < 3) :
    ∀ x ∈ ((sigOfBytes sb).layers.getD l ⟨0, []⟩).wots, x.length = 16 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [length_wots sb hl] at hi
  rw [← getD_eq_getElem' _ [] (by rw [length_wots sb hl]; exact hi)]
  exact length_wots_getD sb hsb hl hi

theorem length_layerMem (hsb : sb.length = 7740) :
    ∀ s ∈ (sigOfBytes sb).layers, (layerMem s).length = 1028 := by
  intro s hs
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hs
  have hl3 : l < 3 := by rwa [length_layers] at hl
  rw [layers_getElem sb hl, layerMem, List.length_append,
    length_flatten_uniform _ (length_wots_mem sb hsb hl3), length_wots sb hl3]
  simp [le32, be32]

theorem length_node (hsb : sb.length = 7740) : ∀ x ∈ (sigOfBytes sb).paths, x.length = 16 := by
  intro x hx
  rw [sig_paths, List.mem_flatMap] at hx
  obtain ⟨l, hl, hx⟩ := hx
  rw [List.mem_range] at hl
  rw [List.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [List.mem_range] at hz
  have := sigLayerOff_le hl
  exact length_slice (by omega)

theorem sig_randomizer : (sigOfBytes sb).randomizer = slice sb 0 16 := by
  simp only [Signature.fromBytes]

theorem length_randomizer (hsb : sb.length = 7740) : (sigOfBytes sb).randomizer.length = 16 := by
  rw [sig_randomizer]
  exact length_slice (by omega)

theorem length_forsMem (hsb : sb.length = 7740) :
    (((sigOfBytes sb).fors.map openingMem).flatten).length = 4224 := by
  rw [length_flatten_uniform (n := 176) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact length_openingMem sb hsb o ho), List.length_map, length_fors]

theorem length_pathsMem (hsb : sb.length = 7740) : (sigOfBytes sb).paths.flatten.length = 416 := by
  rw [length_flatten_uniform _ (length_node sb hsb), length_paths]

theorem length_layersMem (hsb : sb.length = 7740) :
    (((sigOfBytes sb).layers.map layerMem).flatten).length = 3084 := by
  rw [length_flatten_uniform (n := 1028) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact length_layerMem sb hsb s hs), List.length_map, length_layers]

theorem length_sigMem (hsb : sb.length = 7740) : (sigMem (sigOfBytes sb)).length = 7740 := by
  rw [sigMem, List.length_append, List.length_append, List.length_append, length_forsMem sb hsb,
    length_pathsMem sb hsb, length_randomizer sb hsb, length_layersMem sb hsb]

theorem sigMem_drop_layers (hsb : sb.length = 7740) (k : Nat) :
    (sigMem (sigOfBytes sb)).drop (4656 + k) = (((sigOfBytes sb).layers.map layerMem).flatten).drop k := by
  rw [sigMem, show 4656 + k = (((sigOfBytes sb).fors.map openingMem).flatten).length +
      ((sigOfBytes sb).paths.flatten.length + ((sigOfBytes sb).randomizer.length + k)) by
    rw [length_forsMem sb hsb, length_pathsMem sb hsb, length_randomizer sb hsb]; omega,
    List.drop_length_add_append, List.drop_length_add_append, List.drop_length_add_append]

theorem sigMem_wots (hsb : sb.length = 7740) {l i : Nat} (hl : l < 3) (hi : i < 64) :
    ((sigMem (sigOfBytes sb)).drop (4656 + 1028 * l + 16 * i)).take 16 =
      ((sigOfBytes sb).layers.getD l ⟨0, []⟩).wots.getD i [] := by
  have hil : i < ((sigOfBytes sb).layers.getD l ⟨0, []⟩).wots.length := by
    rw [length_wots sb hl]; exact hi
  rw [Nat.add_assoc, sigMem_drop_layers sb hsb,
    drop_take_flatten (n := 1028) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact length_layerMem sb hsb s hs) (by simp [length_layers]; omega) (by omega),
    List.getElem_map, layers_getElem sb, layerMem, drop_take_append_left _ _ (by
      rw [length_flatten_uniform _ (length_wots_mem sb hsb hl), length_wots sb hl]; omega),
    show 16 * i = 16 * i + 0 from rfl,
    drop_take_flatten _ (length_wots_mem sb hsb hl) hil (by omega), List.drop_zero,
    getD_eq_getElem' _ _ hil]
  exact List.take_of_length_le (by rw [length_wots_mem sb hsb hl _ (List.getElem_mem _)])

theorem sigMem_counter (hsb : sb.length = 7740) {l : Nat} (hl : l < 3) :
    ((sigMem (sigOfBytes sb)).drop (4656 + 1028 * l + 1024)).take 4 =
      le32 ((sigOfBytes sb).layers.getD l ⟨0, []⟩).counter := by
  rw [Nat.add_assoc, sigMem_drop_layers sb hsb,
    drop_take_flatten (n := 1028) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact length_layerMem sb hsb s hs) (by simp [length_layers]; omega) (by omega),
    List.getElem_map, layers_getElem sb, layerMem,
    show 1024 = (((sigOfBytes sb).layers.getD l ⟨0, []⟩).wots.flatten).length by
      rw [length_flatten_uniform _ (length_wots_mem sb hsb hl), length_wots sb hl],
    List.drop_left]
  exact List.take_of_length_le (by simp [le32, be32])

theorem sigMem_randomizer (hsb : sb.length = 7740) :
    ((sigMem (sigOfBytes sb)).drop 4640).take 16 = (sigOfBytes sb).randomizer := by
  rw [sigMem, show 4640 = (((sigOfBytes sb).fors.map openingMem).flatten).length +
      ((sigOfBytes sb).paths.flatten.length + 0) by
    rw [length_forsMem sb hsb, length_pathsMem sb hsb],
    List.drop_length_add_append, List.drop_length_add_append, List.drop_zero,
    List.take_append_of_le_length (by rw [length_randomizer sb hsb]),
    List.take_of_length_le (by rw [length_randomizer sb hsb])]

theorem path_getD {l z : Nat} (hz : z < layerHeights.getD l 0) :
    ((sigOfBytes sb).path l).getD z [] = (sigOfBytes sb).paths.getD ((layerHeights.take l).sum + z) [] := by
  rw [List.getD_eq_getElem?_getD] at hz
  simp only [Signature.path, List.getD_eq_getElem?_getD, List.getElem?_take, hz, ite_true,
    List.getElem?_drop]

theorem sigMem_node (hsb : sb.length = 7740) {j : Nat} (hj : j < 26) :
    ((sigMem (sigOfBytes sb)).drop (4224 + 16 * j)).take 16 = (sigOfBytes sb).paths.getD j [] := by
  rw [sigMem, show 4224 + 16 * j = (((sigOfBytes sb).fors.map openingMem).flatten).length + (16 * j + 0) by
      rw [length_forsMem sb hsb]; omega,
    List.drop_length_add_append, drop_take_append_left _ _ (by rw [length_pathsMem sb hsb]; omega),
    drop_take_flatten _ (length_node sb hsb) (by rw [length_paths]; exact hj) (by omega),
    List.drop_zero, getD_eq_getElem' _ _ (by rw [length_paths]; exact hj)]
  exact List.take_of_length_le (by rw [length_node sb hsb _ (List.getElem_mem _)])

theorem sigMem_opening (hsb : sb.length = 7740) {c k m : Nat} (hc : c < 24) (hkm : k + m ≤ 176) :
    ((sigMem (sigOfBytes sb)).drop (176 * c + k)).take m =
      ((openingMem ((sigOfBytes sb).fors.getD c ⟨[], []⟩)).drop k).take m := by
  rw [sigMem, drop_take_append_left _ _ (by rw [length_forsMem sb hsb]; omega),
    drop_take_flatten (n := 176) _ (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨o, ho, rfl⟩ := hx
      exact length_openingMem sb hsb o ho) (by simp [length_fors]; omega) hkm, List.getElem_map,
    getD_eq_getElem' _ _ (by rw [length_fors]; exact hc)]

theorem length_forsPath {c : Nat} (hc : c < 24) :
    ((sigOfBytes sb).fors.getD c ⟨[], []⟩).path.length = 10 := by
  rw [fors_getD sb hc]
  simp

theorem length_forsPath_getD (hsb : sb.length = 7740) {c z : Nat} (hc : c < 24) (hz : z < 10) :
    (((sigOfBytes sb).fors.getD c ⟨[], []⟩).path.getD z []).length = 16 := by
  rw [fors_getD sb hc, getD_eq_getElem' _ _ (by simpa using hz)]
  simp only [List.getElem_map, List.getElem_range]
  exact length_slice (by omega)

theorem length_forsSecret (hsb : sb.length = 7740) {c : Nat} (hc : c < 24) :
    ((sigOfBytes sb).fors.getD c ⟨[], []⟩).secret.length = 16 := by
  rw [fors_getD sb hc]
  exact length_slice (by omega)

theorem length_forsPath_mem (hsb : sb.length = 7740) {c : Nat} (hc : c < 24) :
    ∀ x ∈ ((sigOfBytes sb).fors.getD c ⟨[], []⟩).path, x.length = 16 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.getElem_of_mem hx
  rw [length_forsPath sb hc] at hz
  rw [← getD_eq_getElem' _ [] (by rw [length_forsPath sb hc]; exact hz)]
  exact length_forsPath_getD sb hsb hc hz

theorem sigMem_path (hsb : sb.length = 7740) {c z : Nat} (hc : c < 24) (hz : z < 10) :
    ((sigMem (sigOfBytes sb)).drop (176 * c + 16 * z)).take 16 =
      ((sigOfBytes sb).fors.getD c ⟨[], []⟩).path.getD z [] := by
  have hpl : (((sigOfBytes sb).fors.getD c ⟨[], []⟩).path.flatten).length = 160 := by
    rw [length_flatten_uniform _ (length_forsPath_mem sb hsb hc), length_forsPath sb hc]
  have hzl : z < ((sigOfBytes sb).fors.getD c ⟨[], []⟩).path.length := by
    rw [length_forsPath sb hc]; exact hz
  rw [sigMem_opening sb hsb hc (by omega), openingMem, drop_take_append_left _ _ (by omega),
    show 16 * z = 16 * z + 0 from rfl,
    drop_take_flatten _ (length_forsPath_mem sb hsb hc) hzl (by omega), List.drop_zero,
    getD_eq_getElem' _ _ hzl]
  exact List.take_of_length_le (by rw [length_forsPath_mem sb hsb hc _ (List.getElem_mem _)])

theorem sigMem_secret (hsb : sb.length = 7740) {c : Nat} (hc : c < 24) :
    ((sigMem (sigOfBytes sb)).drop (176 * c + 160)).take 16 = ((sigOfBytes sb).fors.getD c ⟨[], []⟩).secret := by
  have hpl : (((sigOfBytes sb).fors.getD c ⟨[], []⟩).path.flatten).length = 160 := by
    rw [length_flatten_uniform _ (length_forsPath_mem sb hsb hc), length_forsPath sb hc]
  rw [sigMem_opening sb hsb hc (by omega), openingMem, ← hpl, List.drop_left,
    List.take_of_length_le (by rw [length_forsSecret sb hsb hc])]

end SigMemBytes

end

end NativeRustc.Sphincs
