/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.Fam

  `verify_keccak`'s own residual families (`CoreMode/FnReg.lean`): its reads past its layers' cursors and its exponents at `τ`.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `verify_keccak`'s layers' returned cursors, step `s`'s at index `s` (`EndExec.vk_rets`). -/
def vkCurs : List ℕ :=
  [val% «verify_keccak» "cursor@2", val% «verify_keccak» "cursor@3", val% «verify_keccak» "cursor@4",
    val% «verify_keccak» "cursor@5", val% «verify_keccak» "cursor@6", val% «verify_keccak» "cursor@7",
    val% «verify_keccak» "cursor@8", val% «verify_keccak» "cursor@9", val% «verify_keccak» "cursor@10",
    val% «verify_keccak» "cursor@11", val% «verify_keccak» "cursor@12", val% «verify_keccak» "cursor@13"]

/-- The order of `g`: exponents are taken modulo it. -/
def gOrd : ℕ := 2 ^ 64 - 1

/-- **`verify_keccak`'s values' exponents at `τ`** (`EndExec.vk_exps`), `y = τ - 3`: `tau_g`, `g^-4` (modulo the
order), `pack_g`, `y_g`, the pack rounds' step `g^(y / 8)` and remainder `g^(y % 8)`, and their bits' factors. -/
def vkTab (τ : ℕ) : List (ℕ × ℕ) :=
  [(val% «verify_keccak» "tau_g", τ), (val% «verify_keccak» "pack_g~0", gOrd - 4), (val% «verify_keccak» "pack_g", τ - 4),
    (val% «verify_keccak» "s5#1", τ - 3), (val% «verify_keccak» "step_g@2", (τ - 3) / 8), (val% «verify_keccak» "rem_g@3", (τ - 3) % 8),
    (val% «verify_keccak» "step_g@1", (τ - 3) / 8 % 2), (val% «verify_keccak» "step_g@2~3", 2 * ((τ - 3) / 16 % 2)),
    (val% «verify_keccak» "rem_g@1", (τ - 3) % 2), (val% «verify_keccak» "rem_g@2~3", 2 * ((τ - 3) / 2 % 2)),
    (val% «verify_keccak» "rem_g@3~3", 4 * ((τ - 3) / 4 % 2))]

/-- A value's exponent at `τ` (`vkTab`). -/
def vkE (τ v : ℕ) : Option ℕ := (vkTab τ).lookup v

/-- **A cell's exponent at `τ`**, its bases all of `vkE`'s, modulo the order. -/
def vkEv (τ : ℕ) (c : CCell) : Option ℕ :=
  (c.bases.foldr (fun b acc ↦ acc.bind fun a ↦ (vkE τ b.1).map fun e ↦ a + b.2 * e) (some c.off)).map (· % gOrd)

/-- A cell's bases `vkE` does not know, in order. -/
def vkU (τ : ℕ) (c : CCell) : List (ℕ × ℕ) := c.bases.filter fun b ↦ (vkE τ b.1).isNone

/-- A cell's part `vkE` knows. -/
def vkK (τ : ℕ) (c : CCell) : CCell := ⟨c.bases.filter fun b ↦ (vkE τ b.1).isSome, c.off⟩

/-- **A run inside a run at `τ`**, the known parts' and bounds' exponents given: the same bases `vkE` does not know,
each cell `kq + S·j` of the first, `lq ≤ j < hq`, a cell `kr + S'·j'` of the second, `lr ≤ j' < hr`. -/
def vkRun (τ : ℕ) (q r : CRun) (kq kr lq hq lr hr : ℕ) : Bool :=
  decide (vkU τ q.base = vkU τ r.base) && Nat.blt 0 r.stride && decide (hq < capE) &&
    decide (kq + q.stride * hq < capE) && decide (hr < capE) &&
    (List.range (hq - lq)).all fun t ↦
      decide (kr ≤ kq + q.stride * (lq + t)) && Nat.beq ((kq + q.stride * (lq + t) - kr) % r.stride) 0 &&
      decide (lr ≤ (kq + q.stride * (lq + t) - kr) / r.stride) &&
      decide ((kq + q.stride * (lq + t) - kr) / r.stride < hr)

/-- **A residual at `τ`**: an order of exponents `vkE` gives; a run inside a run (`vkRun`); either under branch
conditions. -/
def vkAt (τ : ℕ) : CRes → Bool
  | .lt a b => ((vkEv τ (idxC a)).bind fun u ↦ (vkEv τ (idxC b)).map fun v ↦
      decide (u < v) && decide (v < capE)).getD false
  | .subR q r => ((vkEv τ (vkK τ q.base)).bind fun kq ↦ (vkEv τ (vkK τ r.base)).bind fun kr ↦
      (vkEv τ (idxC q.lo)).bind fun lq ↦ (vkEv τ (idxC q.hi)).bind fun hq ↦ (vkEv τ (idxC r.lo)).bind fun lr ↦
      (vkEv τ (idxC r.hi)).map fun hr ↦ vkRun τ q r kq kr lq hq lr hr).getD false
  | .under _ r => vkAt τ r
  | _ => false

/-- **`verify_keccak`'s family** (`EndExec.vkQC_inst`): a read `c < (11 - s)·96 + 97` words past step `s`'s returned
cursor (`vkCurs`), one of its stream's, parameter `stream`'s `[0, 8192)`; else a residual that holds at every `τ` of
`[9, 28]` (`vkAt`); either under branch conditions. -/
def vkQC (fn : Fn) : CRes → Bool
  | .sub c q => fn.name == name% «verify_keccak» && decide (q = ⟨⟨[(val% «verify_keccak» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩) &&
      match c.bases with
      | [(x, 1)] => (List.range 12).any fun s ↦ Nat.beq (vkCurs.getD s 0) x && decide (c.off < (11 - s) * 96 + 97)
      | _ => false
  | .under _ r => vkQC fn r
  | r => fn.name == name% «verify_keccak» && (List.range 20).all fun i ↦ vkAt (9 + i) r

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family** (`vkQC`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «verify_keccak», vkQC)]

end

end LeanVM.Guest.CoreMode.Own.verify_keccak
