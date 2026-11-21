/-
  LeanVM.Guest.B1.KeccakGkr.LayerCSpec

  `keccak_layer`'s honest valuation: the template evaluated from the arguments, its checker's
  count and its stores, for the two specializations.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

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
  (List.range 16).map (fun i ↦ .load (.n (layOff first + rmfeStores.getD i 0)) (.n (valf% «keccak_layer» "out")) (6 + i)) ++
  [.load (.n (layOff first + 624)) (.n (valf% «keccak_layer» "out")) 1,
    .load (.n (layOff first + 539)) (.n (layOff first + 719)) 0,
    .load (.n (layOff first + 540)) (.n (layOff first + 719)) 16,
    .load (.n (layOff first + 541)) (.n (layOff first + 719)) 32,
    .load (.n (layOff first + 542)) (.n (layOff first + 719)) 48,
    .load (.n (layOff first + 543)) (.n (layOff first + 719)) 64,
    .load (.n (layOff first + 721)) (.n (layOff first + 719)) 80,
    .load (.n (layOff first + 716)) (.n (layOff first + 719)) 96] ++
  (List.range 11).map (fun i ↦ .load (.n (layOff first + 757 + 32 * i)) (.n (layOff first + 745)) i) ++
  [.load (.n (weightEnd first (layOff first) + 24)) (.n (valf% «keccak_layer» "out")) 0,
    .load (.n (layOff first + 718)) (.n (valf% «keccak_layer» "out")) 2, .load (.n (layOff first + 745)) (.n (valf% «keccak_layer» "out")) 4] ++
  (List.range 25).map (fun i ↦ .load (.n (weightEnd first (layOff first) + 29 + 4 * i))
    (.n (weightEnd first (layOff first) + 25)) i) ++
  [.load (.n (weightEnd first (layOff first) + 25)) (.n (valf% «keccak_layer» "out")) 3] ++
  (List.range 7).map (fun i ↦ .load (.n (topV (weightEnd first (layOff first)) + 46 + 43 * i))
    (.n (topV (weightEnd first (layOff first)) + 3)) i) ++
  [.load (.n (topV (weightEnd first (layOff first)) + 3)) (.n (valf% «keccak_layer» "out")) 5]

/-- The checker's count after the body. -/
def layerN (first : ℕ) : ℕ := if first = 1 then 1823 else 2152

theorem layer_chk {first : ℕ} (hf : first < 2) :
    Fwd.chk 16 (layerT first) = some (layerN first) := by
  interval_cases first <;> decide +kernel

theorem layer_stores {first : ℕ} (hf : first < 2) :
    storesOf 16 (layerT first) = layerSt first := by
  interval_cases first <;> decide +kernel

/-- **The honest valuation of a layer.** -/
noncomputable def layerσ (rd : Reader) (w : ℕ → E) (args : List E) (first : ℕ) : Val :=
  B1.Val.ofArgs (ev rd w args (layerT first))

section
variable {rd : Reader} {w : ℕ → E} {args : List E} {first : ℕ}

theorem layer_good (hf : first < 2) (hl : args.length = 16) :
    ∀ s ∈ layerT first, GoodS rd (layerSt first) w (layerσ rd w args first) s := by
  have h := (ev_spec rd w (layerT first) args (by rw [hl]; exact layer_chk hf)).2.2
  rw [hl, layer_stores hf] at h
  exact h

theorem layer_param (hf : first < 2) (hl : args.length = 16) {i : ℕ}
    (hi : i < 16) : layerσ rd w args first (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact layer_chk hf) (by rw [hl]; exact hi)

theorem layerσ_idx (v : V) : layerσ rd w args first v = layerσ rd w args first (.n v.idx) :=
  rfl

end

end
end LeanVM.Guest.B1.VerifySub
