/-
  LeanVM.Guest.B1.KeccakGkr.LayerCSpec

  `keccak_layer`'s honest valuation: the template evaluated from the arguments, its checker's
  count and its stores, for the two specializations.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock

/-!
# The honest valuation of a layer

`layerσ rd w args first`: `layerT first` evaluated (`Fwd.ev`) on the memory `rd` and the oracle
`w` from the arguments. The checker accepts the two specializations (`layer_chk`), whose stores
are `layerSt` (`layer_stores`): the next claim's record at `out`, the pack rounds' first record,
the local point, the next claim's lanes and flips. Every statement satisfies its
equations (`layer_good`), and the parameters are the arguments (`layer_param`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The stores of `layerT first`: the next claim's instance weights and `κ`, the pack rounds'
first record, the local point, the next claim's value, point, local point, lanes and flips. -/
def layerSt (first : ℕ) : List Atom :=
  (List.range 16).map (fun i ↦ .load (.n (rmfeStores.getD i 0)) (.n 12) (6 + i)) ++
  [.load (.n 958) (.n 12) 1,
    .load (.n 866) (.n 1053) 0, .load (.n 867) (.n 1053) 16, .load (.n 868) (.n 1053) 32,
    .load (.n 869) (.n 1053) 48, .load (.n 870) (.n 1053) 64, .load (.n 1055) (.n 1053) 80,
    .load (.n 1050) (.n 1053) 96, .load (.n 1056) (.n 1053) 112] ++
  (List.range 11).map (fun i ↦ .load (.n (1133 + 60 * i)) (.n 1081) i) ++
  [.load (.n (weightEnd first + 32)) (.n 12) 0, .load (.n 1052) (.n 12) 2,
    .load (.n 1081) (.n 12) 4] ++
  (List.range 25).map (fun i ↦ .load (.n (weightEnd first + 37 + 4 * i))
    (.n (weightEnd first + 33)) i) ++
  [.load (.n (weightEnd first + 33)) (.n 12) 3] ++
  (List.range 7).map (fun i ↦ .load (.n (topV (weightEnd first) + 46 + 43 * i))
    (.n (topV (weightEnd first) + 3)) i) ++
  [.load (.n (topV (weightEnd first) + 3)) (.n 12) 5]

/-- The checker's count after the body. -/
def layerN (first : ℕ) : ℕ := if first = 1 then 2475 else 2824

theorem layer_chk {first : ℕ} (hf : first < 2) :
    Fwd.chk 14 (layerT first) = some (layerN first) := by
  interval_cases first <;> decide +kernel

theorem layer_stores {first : ℕ} (hf : first < 2) :
    storesOf 14 (layerT first) = layerSt first := by
  interval_cases first <;> decide +kernel

/-- **The honest valuation of a layer.** -/
noncomputable def layerσ (rd : Reader) (w : ℕ → E) (args : List E) (first : ℕ) : Val :=
  B1.Val.ofArgs (ev rd w args (layerT first))

section
variable {rd : Reader} {w : ℕ → E} {args : List E} {first : ℕ}

theorem layer_good (hf : first < 2) (hl : args.length = 14) :
    ∀ s ∈ layerT first, GoodS rd (layerSt first) w (layerσ rd w args first) s := by
  have h := (ev_spec rd w (layerT first) args (by rw [hl]; exact layer_chk hf)).2.2
  rw [hl, layer_stores hf] at h
  exact h

theorem layer_param (hf : first < 2) (hl : args.length = 14) {i : ℕ}
    (hi : i < 14) : layerσ rd w args first (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact layer_chk hf) (by rw [hl]; exact hi)

theorem layerσ_idx (v : V) : layerσ rd w args first v = layerσ rd w args first (.n v.idx) :=
  rfl

end

end
end LeanVM.Guest.B1.VerifySub
