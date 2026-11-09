/-
  LeanVM.Protocol.Keccak.Bits

  The bit-level semantics of a Keccak-f round: the state's 1600 bits, the linear map
  `L = π ∘ ρ ∘ θ`, χ along the rows, ι, and the theorem that `Keccak.round` on 64-bit lanes is
  `ι ∘ χ ∘ L` on bits.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords

/-!
# Keccak-f on bits

The GKR reduction of `verifyKeccak` (`crates/verifier/src/keccak.rs` at leanVM `40f877dc`,
`doc/leanvm/body/c-keccak-gkr.tex`,
§`keccak:perm`) speaks of a state as `1600` bits, position `j = z + 64ℓ` being bit `z` (the
*slice*) of lane `ℓ`. A round maps a state `a` to

  `b = L(a)`,  `a'[j] = b[j] + (1 + b[along j 1]) · b[along j 2] + [j < 64] · RC[j]`,

`L = π ∘ ρ ∘ θ`, `along j k` the position `k` columns along in the same row and slice
(`keccakAlong`). This module proves it of the specification's `Keccak.round`, which computes on
`UInt64` lanes (`sbit_round`):

* `sbit a j`, bit `j` of a state;
* `thetaB`, `rhoPiSrc`, `Lb = thetaB ∘ rhoPiSrc` (position `j` of `L(a)` is position
  `rhoPiSrc j` of `θ(a)`), `chiB`, `roundB`;
* the stages of `Keccak.round` as functions (`Stage.theta`, `Stage.rhoPi`, `Stage.chi`,
  `Stage.iota`; `Keccak.round` is their composition by `rfl`) and the bits of each;
* the rounds of a segment (`roundsFrom`) and `keccakF` as two segments of twelve.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Lanes and bits -/

/-- A lane of a state is its entry. -/
theorem lane_eq (v : KeccakState) {i : ℕ} (hi : i < 25) : Keccak.lane v i = v[i] := by
  simp [Keccak.lane, Array.getD, hi]

/-- Bit `j = z + 64ℓ` of a state: bit `z` of lane `ℓ`. -/
def sbit (a : KeccakState) (j : ℕ) : Bool := (Keccak.lane a (j / 64)).toBitVec.getLsbD (j % 64)

theorem sbit_eq (a : KeccakState) (j : ℕ) :
    sbit a j = (Keccak.lane a (j / 64)).toBitVec.getLsbD (j % 64) := rfl

theorem sbit_lane (a : KeccakState) (l : ℕ) {z : ℕ} (hz : z < 64) :
    sbit a (64 * l + z) = (Keccak.lane a l).toBitVec.getLsbD z := by
  unfold sbit
  have h1 : (64 * l + z) / 64 = l := by omega
  have h2 : (64 * l + z) % 64 = z := by omega
  rw [h1, h2]

/-- `rot x n` holds at `z` the bit `z - n` of `x`, cyclically. -/
theorem rot_bit (x : UInt64) (n z : ℕ) (hn : n < 64) (hz : z < 64) :
    (Keccak.rot x n).toBitVec.getLsbD z = x.toBitVec.getLsbD ((z + 64 - n) % 64) := by
  unfold Keccak.rot
  split_ifs with h0
  · subst h0; congr 1; omega
  · simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      BitVec.getLsbD_or]
    rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
    have h1 : (n.toUInt64.toBitVec % 64).toNat = n := by
      simp [Nat.toUInt64]; omega
    have h2 : ((64 - n).toUInt64.toBitVec % 64).toNat = 64 - n := by
      simp [Nat.toUInt64]; omega
    rw [h1, h2, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases hzn : z < n
    · have : (z + 64 - n) % 64 = 64 - n + z := by omega
      simp [hzn, hz, this]
    · have : (z + 64 - n) % 64 = z - n := by omega
      have h3 : x.toBitVec.getLsbD (64 - n + z) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [hzn, hz, this, h3]

/-! ## `keccakAlong` -/

theorem keccakAlong_def (j k : ℕ) :
    keccakAlong j k = 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 := rfl

theorem keccakAlong_lt {j : ℕ} (k : ℕ) (hj : j < 1600) : keccakAlong j k < 1600 := by
  rw [keccakAlong_def]; omega

theorem keccakAlong_zero {j : ℕ} (hj : j < 1600) : keccakAlong j 0 = j := by
  rw [keccakAlong_def]; omega

/-- Going `k` columns along, then `5 - k`, comes back. -/
theorem keccakAlong_along {j k k' : ℕ} (hk : k + k' = 5) :
    keccakAlong (keccakAlong j k) k' = j := by
  rw [keccakAlong_def, keccakAlong_def]; omega

/-! ## The linear map, χ and ι on bits -/

/-- The θ column sum on bits: the parity of column `x` at slice `z`. -/
def colB (f : ℕ → Bool) (x z : ℕ) : Bool :=
  f (64 * x + z) ^^ f (64 * (x + 5) + z) ^^ f (64 * (x + 10) + z) ^^ f (64 * (x + 15) + z) ^^
    f (64 * (x + 20) + z)

/-- θ on bits: position `p` (lane `ℓ`, slice `z`, column `x = ℓ mod 5`) gains the columns
`x - 1` at `z` and `x + 1` at `z - 1`. -/
def thetaB (f : ℕ → Bool) (p : ℕ) : Bool :=
  f p ^^ colB f ((p / 64 % 5 + 4) % 5) (p % 64) ^^
    colB f ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64)

/-- The inverse of `KECCAK_PI` on lanes: lane `k` of `π(a)` is lane `piInv k` of `a`. -/
def piInv (k : ℕ) : ℕ := (3 * (k / 5) + k % 5) % 5 + 5 * (k % 5)

theorem piInv_lt {k : ℕ} : piInv k < 25 := by unfold piInv; omega

theorem keccakPi_piInv : ∀ k < 25, keccakPi (piInv k) = k := by decide

theorem piInv_keccakPi : ∀ i < 25, piInv (keccakPi i) = i := by decide

theorem keccakPi_lt : ∀ i < 25, keccakPi i < 25 := by decide

theorem keccakRho_lt (i : ℕ) : keccakRho.getD i 0 < 64 := by
  by_cases hi : i < 25
  · revert i; decide
  · have h : keccakRho.length ≤ i := by
      have : keccakRho.length = 25 := rfl
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    decide

/-- ρ and π on positions: position `j` of `ρπ(a)` is position `rhoPiSrc j` of `a`. -/
def rhoPiSrc (j : ℕ) : ℕ :=
  64 * piInv (j / 64) + (j % 64 + 64 - keccakRho.getD (piInv (j / 64)) 0) % 64

/-- Where ρ and π send position `p`: the inverse of `rhoPiSrc`. -/
def rhoPiDst (p : ℕ) : ℕ := 64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64

theorem rhoPiSrc_lt {j : ℕ} : rhoPiSrc j < 1600 := by
  have := @piInv_lt (j / 64)
  unfold rhoPiSrc; omega

theorem rhoPiDst_lt {p : ℕ} (hp : p < 1600) : rhoPiDst p < 1600 := by
  have := keccakPi_lt (p / 64) (by omega)
  unfold rhoPiDst; omega

theorem rhoPiSrc_dst {p : ℕ} (hp : p < 1600) : rhoPiSrc (rhoPiDst p) = p := by
  have hl : p / 64 < 25 := by omega
  have hr := keccakRho_lt (p / 64)
  have hpi := keccakPi_lt _ hl
  have h1 : rhoPiDst p / 64 = keccakPi (p / 64) := by unfold rhoPiDst; omega
  have h2 : rhoPiDst p % 64 = (p % 64 + keccakRho.getD (p / 64) 0) % 64 := by
    unfold rhoPiDst; omega
  unfold rhoPiSrc
  rw [h1, h2, piInv_keccakPi _ hl]
  omega

theorem rhoPiDst_src {j : ℕ} (hj : j < 1600) : rhoPiDst (rhoPiSrc j) = j := by
  have hl : j / 64 < 25 := by omega
  have hr := keccakRho_lt (piInv (j / 64))
  have h1 : rhoPiSrc j / 64 = piInv (j / 64) := by unfold rhoPiSrc; omega
  have h2 : rhoPiSrc j % 64 = (j % 64 + 64 - keccakRho.getD (piInv (j / 64)) 0) % 64 := by
    unfold rhoPiSrc; omega
  unfold rhoPiDst
  rw [h1, h2, keccakPi_piInv _ hl]
  omega

/-- `L = π ∘ ρ ∘ θ` on bits. -/
def Lb (f : ℕ → Bool) (j : ℕ) : Bool := thetaB f (rhoPiSrc j)

/-- χ on bits: `b[j] + (1 + b[along j 1]) · b[along j 2]`. -/
def chiB (b : ℕ → Bool) (j : ℕ) : Bool := b j ^^ (!b (keccakAlong j 1) && b (keccakAlong j 2))

/-- ι on bits: the round constant on lane `0`. -/
def iotaB (rc : UInt64) (j : ℕ) : Bool := decide (j < 64) && rc.toBitVec.getLsbD j

/-- A round on bits: `ι ∘ χ ∘ L`. -/
def roundB (rc : UInt64) (f : ℕ → Bool) (j : ℕ) : Bool := chiB (Lb f) j ^^ iotaB rc j

/-! ## The stages of `Keccak.round` -/

namespace Stage

/-- θ's column parities. -/
def colV (a : KeccakState) : Vector UInt64 5 := Vector.ofFn fun x ↦
  Keccak.lane a x ^^^ Keccak.lane a (x + 5) ^^^ Keccak.lane a (x + 10) ^^^
    Keccak.lane a (x + 15) ^^^ Keccak.lane a (x + 20)

/-- θ. -/
def theta (a : KeccakState) : KeccakState :=
  Vector.ofFn fun i ↦ Keccak.lane a i ^^^ (colV a).toArray.getD ((i.val + 4) % 5) 0 ^^^
    Keccak.rot ((colV a).toArray.getD ((i.val + 1) % 5) 0) 1

/-- ρ and π. -/
def rhoPi (a : KeccakState) : KeccakState :=
  (List.range 25).foldl
    (fun b i ↦ b.setIfInBounds (keccakPi i) (Keccak.rot (Keccak.lane a i) (keccakRho.getD i 0)))
    (Vector.replicate 25 0)

/-- χ. -/
def chi (b : KeccakState) : KeccakState :=
  Vector.ofFn fun i ↦ Keccak.lane b i ^^^ (~~~ Keccak.lane b (i.val - i.val % 5 + (i.val + 1) % 5) &&&
    Keccak.lane b (i.val - i.val % 5 + (i.val + 2) % 5))

/-- ι. -/
def iota (a : KeccakState) (rc : UInt64) : KeccakState := a.setIfInBounds 0 (Keccak.lane a 0 ^^^ rc)

/-- `Keccak.round` is the composition of its stages. -/
theorem round_eq (a : KeccakState) (rc : UInt64) :
    Keccak.round a rc = iota (chi (rhoPi (theta a))) rc := rfl

theorem colV_bit (a : KeccakState) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((colV a).toArray.getD x 0).toBitVec.getLsbD z = colB (sbit a) x z := by
  have h : (colV a).toArray.getD x 0 = (colV a)[x] := by simp [Array.getD, hx]
  rw [h]
  simp only [colV, Vector.getElem_ofFn, UInt64.toBitVec_xor, BitVec.getLsbD_xor, colB,
    sbit_lane a _ hz]

theorem sbit_theta (a : KeccakState) {p : ℕ} (hp : p < 1600) : sbit (theta a) p = thetaB (sbit a) p := by
  have hl : p / 64 < 25 := by omega
  have hz : p % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [sbit_eq (theta a) p, lane_eq _ hl]
  simp only [theta, Vector.getElem_ofFn, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  rw [rot_bit _ 1 _ (by omega) hz, colV_bit a (by omega) hz, colV_bit a (by omega) (by omega)]
  have e1 : (p / 64 + 4) % 5 = (p / 64 % 5 + 4) % 5 := by omega
  have e2 : (p / 64 + 1) % 5 = (p / 64 % 5 + 1) % 5 := by omega
  have e3 : (p % 64 + 64 - 1) % 64 = (p % 64 + 63) % 64 := by omega
  rw [e1, e2, e3]
  rfl

/-- A fold of writes whose targets miss `k` leaves entry `k`. -/
theorem foldl_set_miss (σ : ℕ → ℕ) (f : ℕ → UInt64) {k : ℕ} (hk : k < 25) :
    ∀ (l : List ℕ) (b : KeccakState), (∀ i ∈ l, σ i ≠ k) →
      (l.foldl (fun b i ↦ b.setIfInBounds (σ i) (f i)) b)[k] = b[k]
  | [], _, _ => rfl
  | i :: l, b, h => by
    rw [List.foldl_cons, foldl_set_miss σ f hk l _ (fun i' hi' ↦ h i' (by simp [hi'])),
      Vector.getElem_setIfInBounds hk, ite_eq_right (h i (by simp))]

/-- A fold of writes hitting `k` once, at `i₀`, leaves `f i₀` there. -/
theorem foldl_set_hit (σ : ℕ → ℕ) (f : ℕ → UInt64) {k i₀ : ℕ} (hk : k < 25) (hσ : σ i₀ = k) :
    ∀ (l : List ℕ) (b : KeccakState), i₀ ∈ l → (∀ i ∈ l, σ i = k → i = i₀) →
      (l.foldl (fun b i ↦ b.setIfInBounds (σ i) (f i)) b)[k] = f i₀
  | [], _, h, _ => by simp at h
  | i :: l, b, hmem, huniq => by
    rw [List.foldl_cons]
    by_cases hl : i₀ ∈ l
    · exact foldl_set_hit σ f hk hσ l _ hl fun i' hi' ↦ huniq i' (by simp [hi'])
    · have hi : i = i₀ := by
        rcases List.mem_cons.1 hmem with h | h
        · exact h.symm
        · exact absurd h hl
      subst hi
      rw [foldl_set_miss σ f hk l _ (fun i' hi' he ↦ hl (huniq i' (by simp [hi']) he ▸ hi')),
        Vector.getElem_setIfInBounds hk, ite_eq_left hσ]

theorem lane_rhoPi (a : KeccakState) {k : ℕ} (hk : k < 25) :
    Keccak.lane (rhoPi a) k =
      Keccak.rot (Keccak.lane a (piInv k)) (keccakRho.getD (piInv k) 0) := by
  rw [lane_eq _ hk, rhoPi]
  exact foldl_set_hit keccakPi (fun i ↦ Keccak.rot (Keccak.lane a i) (keccakRho.getD i 0)) hk
    (keccakPi_piInv k hk) _ _ (List.mem_range.2 piInv_lt) fun i hi he ↦ by
      rw [← he, piInv_keccakPi i (List.mem_range.1 hi)]

theorem sbit_rhoPi (a : KeccakState) {j : ℕ} (hj : j < 1600) : sbit (rhoPi a) j = sbit a (rhoPiSrc j) := by
  have hl : j / 64 < 25 := by omega
  have hz : j % 64 < 64 := Nat.mod_lt _ (by omega)
  have hr := keccakRho_lt (piInv (j / 64))
  unfold sbit
  rw [lane_rhoPi a hl, rot_bit _ _ _ hr hz]
  have h1 : rhoPiSrc j / 64 = piInv (j / 64) := by unfold rhoPiSrc; omega
  have h2 : rhoPiSrc j % 64 = (j % 64 + 64 - keccakRho.getD (piInv (j / 64)) 0) % 64 := by
    unfold rhoPiSrc; omega
  rw [h1, h2]

theorem sbit_chi (b : KeccakState) {j : ℕ} (hj : j < 1600) : sbit (chi b) j = chiB (sbit b) j := by
  have hl : j / 64 < 25 := by omega
  have hz : j % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [sbit_eq (chi b) j, lane_eq _ hl]
  simp only [chi, Vector.getElem_ofFn, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    UInt64.toBitVec_not, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hz,
    decide_true, Bool.true_and]
  unfold chiB
  have e : ∀ k, keccakAlong j k = 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 :=
    fun k ↦ keccakAlong_def j k
  rw [e 1, e 2, sbit_lane b _ hz, sbit_lane b _ hz]
  have e1 : j / 64 - j / 64 % 5 + (j / 64 + 1) % 5 = (j / 64 % 5 + 1) % 5 + 5 * (j / 64 / 5) := by
    omega
  have e2 : j / 64 - j / 64 % 5 + (j / 64 + 2) % 5 = (j / 64 % 5 + 2) % 5 + 5 * (j / 64 / 5) := by
    omega
  rw [e1, e2]
  rfl

theorem sbit_iota (a : KeccakState) (rc : UInt64) {j : ℕ} (hj : j < 1600) :
    sbit (iota a rc) j = (sbit a j ^^ iotaB rc j) := by
  have hl : j / 64 < 25 := by omega
  unfold sbit iota iotaB
  rw [lane_eq _ hl, Vector.getElem_setIfInBounds hl, ← lane_eq _ hl]
  by_cases h0 : j < 64
  · have hj0 : j / 64 = 0 := by omega
    have hjz : j % 64 = j := by omega
    simp only [hj0, ite_true, UInt64.toBitVec_xor, BitVec.getLsbD_xor, hjz, h0, decide_true,
      Bool.true_and]
  · have hj0 : ¬ 0 = j / 64 := by omega
    simp [hj0, h0]

end Stage

/-- **A round on bits.** Bit `j` of `Keccak.round a rc` is `ι ∘ χ ∘ L` of the bits of `a`
(`doc/leanvm`, eq. `keccak:eq:round`). -/
theorem sbit_round (a : KeccakState) (rc : UInt64) {j : ℕ} (hj : j < 1600) :
    sbit (Keccak.round a rc) j = roundB rc (sbit a) j := by
  rw [Stage.round_eq, Stage.sbit_iota _ _ hj, Stage.sbit_chi _ hj]
  unfold roundB chiB Lb
  rw [Stage.sbit_rhoPi _ hj, Stage.sbit_rhoPi _ (keccakAlong_lt 1 hj),
    Stage.sbit_rhoPi _ (keccakAlong_lt 2 hj), Stage.sbit_theta _ rhoPiSrc_lt,
    Stage.sbit_theta _ rhoPiSrc_lt, Stage.sbit_theta _ rhoPiSrc_lt]

/-! ## Segments of rounds -/

/-- `e` rounds from round `start`: rounds `start, …, start + e - 1` of `keccakF`. -/
def roundsFrom (start e : ℕ) (a : KeccakState) : KeccakState :=
  ((keccakRC.drop start).take e).foldl Keccak.round a

theorem roundsFrom_zero (start : ℕ) (a : KeccakState) : roundsFrom start 0 a = a := rfl

/-- One more round. -/
theorem roundsFrom_succ {start e : ℕ} (h : start + e < 24) (a : KeccakState) :
    roundsFrom start (e + 1) a =
      Keccak.round (roundsFrom start e a) (keccakRC.getD (start + e) 0) := by
  have hlen : keccakRC.length = 24 := rfl
  unfold roundsFrom
  rw [List.take_add_one, List.foldl_append, List.getElem?_drop,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- `keccakF` is twelve rounds, then the twelve others. -/
theorem keccakF_eq (a : KeccakState) : keccakF1600 a = roundsFrom 12 12 (roundsFrom 0 12 a) := by
  unfold keccakF1600 roundsFrom
  rw [← List.foldl_append]
  rfl

end
end LeanVM.Protocol.KeccakGkr
