/-
  LeanVM.Guest.B1.KeccakGkr.VkCHon

  `verify_keccak`'s honest run: its data, read back from the accepting run, and what follows from
  it (the twelve layers' data, the openings, the results).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkInv
public import LeanVM.Guest.B1.KeccakGkr.LayerCHon

/-!
# `verify_keccak`'s honest run

`VkData`: `τ`, the carried capacity, the table sumcheck's point, the output lanes, and the words
the run reads (the committed word, the layers' words `Ts`, the openings' rounds, the word, the
slices). From them, on `keccakSeg`'s run:

* `seg`, `rl`, `s2`: the segment and lane coordinates squeezed, and the sponge after them;
* `c0`: the first claim; `chain k`: the claim and the sponge before layer `k`; `layer k`: layer
  `k`'s `LayerData`;
* `O`, `I`, `S`: the committed outputs' opening, the inputs' sumcheck and opening;
* `op`, `point`, `m0`, `capF`: the results.

`VkData.Ok`: what the honest run gives (`vi_seg`); `vkData_of_run`: an accepting run of
`keccakSeg` from a carried capacity is a `VkData`'s.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Tables

@[expose] public section

/-- **`verify_keccak`'s honest data.** -/
structure VkData where
  τ : ℕ
  f : List E
  chis : List E
  outs : List E
  committed : E
  Ts : List LT
  mO : List (E × E)
  word : E
  mI : List (E × E)
  mS : List (E × E)
  slices : List E

namespace VkData

variable (D : VkData)

/-- The instance coordinates. -/
def inst : List E := D.chis.take D.τ

/-- The segment squeezed, and the sponge after it. -/
def sq1 : List E × Fs := (⟨D.f, []⟩ : Fs).squeezeN keccakSegmentBits

/-- The lane coordinates squeezed, and the sponge after them. -/
def sq2 : List E × Fs := D.sq1.2.squeezeN keccakLaneBits

/-- The segment coordinate. -/
def seg : List E := D.sq1.1

/-- The lane coordinates. -/
def rl : List E := D.sq2.1

/-- The first claim. -/
def c0 : KeccakClaim := vkFirst D.inst D.outs D.committed D.seg D.rl

/-- The sponge the layers start from: the committed word waiting. -/
def S0 : Fs := D.sq2.2.absorb D.committed dsObserve

/-- The claim and the sponge before layer `k`. -/
def chain (k : ℕ) : KeccakClaim × Fs :=
  chainEnd ((List.range keccakDepth).take k) D.c0 D.S0 (D.Ts.take k)

/-- Layer `k`'s words. -/
def T (k : ℕ) : LT := D.Ts.getD k default

/-- **Layer `k`'s data.** -/
def layer (k : ℕ) : LayerData :=
  ⟨(D.chain k).2.cap, D.committed, (D.chain k).1, (D.T k).1, (D.T k).2.1, (D.T k).2.2.1,
    (D.T k).2.2.2⟩

/-- The claim and the sponge after the layers. -/
def L : KeccakClaim × Fs := chainEnd (List.range keccakDepth) D.c0 D.S0 D.Ts

/-- The committed outputs' opening. -/
def O : List E × E × Fs := plainRun D.mO D.committed D.L.2

/-- The inputs' sumcheck. -/
def I : List E × E × Fs := plainRun D.mI D.L.1.value (D.O.2.2.absorb D.word dsObserve)

/-- The inputs' opening. -/
def S : List E × E × Fs := plainRun D.mS D.I.2.1 D.I.2.2

/-- The committed outputs' point. -/
def op : List E := D.inst.take 4 ++ D.inst.drop 4 ++ D.O.1

/-- The inputs' point. -/
def point : List E := D.I.1 ++ D.L.1.point.take (D.τ - 4) ++ D.S.1

/-- The ring map's first challenge and the sponge after it. -/
def fin : E × Fs := (D.S.2.2.absorbAll D.slices dsObserve).squeeze

/-- The words the run reads. -/
def xs : List E :=
  [D.committed] ++ D.Ts.flatMap ltXs ++ D.mO.flatMap (fun m ↦ [m.1, m.2]) ++ [D.word] ++
    D.mI.flatMap (fun m ↦ [m.1, m.2]) ++ D.mS.flatMap (fun m ↦ [m.1, m.2]) ++ D.slices

/-- **What the honest run gives.** -/
def Ok : Prop :=
  9 ≤ D.τ ∧ D.τ ≤ 28 ∧ D.τ ≤ D.chis.length ∧ D.outs.length = 25 ∧ D.f.length = 5 ∧
    AllCanonical D.f ∧
    ChainOk D.τ (List.range keccakDepth) D.c0 D.S0 D.Ts ∧
    D.mO.length = 6 ∧ D.mI.length = 4 ∧ D.mS.length = 6 ∧ D.slices.length = 64 ∧
    ((foldAll D.O.1 (keccakSlotWeights D.τ D.c0 1 1)).headD []).headD 0 * D.word = D.O.2.1 ∧
    multilinearEval D.L.1.mu D.I.1 *
      dot ((foldAll D.S.1 (keccakSlotWeights D.τ D.L.1 0 2)).headD []) D.slices = D.S.2.1

end VkData

set_option maxRecDepth 20000 in
/-- **An accepting run of `keccakSeg` is a `VkData`'s.** -/
theorem vkData_of_run {τ : ℕ} {f chis outs xs op point slices cap' : List E} {word m0 : E}
    (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (hchis : τ ≤ chis.length) (houts : outs.length = 25)
    (hf : f.length = 5) (hcan : AllCanonical f) (hc : ∃ sp, (⟨f, []⟩ : Fs).Carries sp)
    (h : RunsTo (keccakSeg τ (chis.take τ) outs) ⟨f, []⟩ xs
      (([⟨qkeccak, op, word⟩], point, slices), m0) ⟨cap', []⟩) :
    ∃ D : VkData, D.τ = τ ∧ D.f = f ∧ D.chis = chis ∧ D.outs = outs ∧ D.word = word ∧
      D.slices = slices ∧ D.Ok ∧ D.xs = xs ∧ D.op = op ∧ D.point = point ∧
      D.fin = (m0, ⟨cap', []⟩) := by
  obtain ⟨sp, hsp⟩ := hc
  have hT := runsTo_toT h hsp
  obtain ⟨committed, Ts, mO, mI, mS, hok, hmO, hmI, hmS, hsl, hchkO, hchkI, hfin, hxs, hop, hpt⟩ :=
    vi_seg hT
  refine ⟨⟨τ, f, chis, outs, committed, Ts, mO, word, mI, mS, slices⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨hτ1, hτ2, hchis, houts, hf, hcan, hok, hmO, hmI, hmS, hsl, hchkO, hchkI⟩, hxs.symm, hop.symm,
    hpt.symm, hfin⟩

end
end LeanVM.Guest.B1.VerifySub
