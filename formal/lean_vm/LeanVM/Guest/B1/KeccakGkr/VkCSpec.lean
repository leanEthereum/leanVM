/-
  LeanVM.Guest.B1.KeccakGkr.VkCSpec

  `verify_keccak`'s honest valuation: the body evaluated from the arguments, its five pinned bits
  aside.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkT
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock

/-!
# The honest valuation of `verify_keccak`

The checker (`Fwd.chk`) accepts `vkT` but for the five checks `b·b = b` pinning the bits of `y`
(`pinB`), which define nothing. `vkEvL`: the body without them; `vkσ rd w args`: it evaluated
(`Fwd.ev`) from the arguments, the oracle `w` giving the bits, the buffers' bases and the callees'
returns. Every statement of the body but the pins satisfies its equations with the stores `vkSt`
(`vk_good`), and the parameters are the arguments (`vk_param`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A check `b·b = b`. -/
def pinB : Stmt → Bool
  | .atom (.mul d x y) => d == x && x == y
  | _ => false

/-- The body but its pinned bits. -/
def vkEvL : List Stmt := vkT.filter fun s ↦ !pinB s

theorem vk_chk : Fwd.chk 12 vkEvL = some 3373 := by decide +kernel

/-- The stores of the body. -/
def vkSt : List Atom := storesOf 12 vkEvL

/-- **The honest valuation of `verify_keccak`.** -/
noncomputable def vkσ (rd : Reader) (w : ℕ → E) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd w args vkEvL)

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vk_goodL (hl : args.length = 12) : ∀ s ∈ vkEvL, GoodS rd vkSt w (vkσ rd w args) s := by
  have h := (ev_spec rd w vkEvL args (by rw [hl]; exact vk_chk)).2.2
  rw [hl] at h
  exact h

/-- **Every statement of the body but the pins satisfies its equations.** -/
theorem vk_good (hl : args.length = 12) {s : Stmt} (hs : s ∈ vkT) (hp : pinB s = false) :
    GoodS rd vkSt w (vkσ rd w args) s :=
  vk_goodL hl s (List.mem_filter.mpr ⟨hs, by simp [hp]⟩)

theorem vk_param (hl : args.length = 12) {i : ℕ} (hi : i < 12) :
    vkσ rd w args (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact vk_chk) (by rw [hl]; exact hi)

theorem vkσ_idx (v : V) : vkσ rd w args v = vkσ rd w args (.n v.idx) := rfl

end

end
end LeanVM.Guest.B1.VerifySub
