/-
  LeanVM.Guest.B1.Main.CompleteP

  Uniform placed completeness by trees whose pops are given (`CompleteAtDP`), and nodes popping given entries.
-/

module

public import LeanVM.Guest.B1.Main.RelAtInP
public import LeanVM.Guest.Memory.NoWitness

/-!
# Completeness with pops

`CompleteAtDP … ps`: `CompleteAtD` by a tree popping `ps rd` on each memory `rd` it serves. The entries are a function of the reader, as a heap witness hint's are read through it; the honest ones are usually constant.

* `kidsFromInP_dend`: `KidsFromInP` holds on a smaller domain `D'`;
* `relAtInP_of_node`: a function every call instance of which pops `ps`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`CompleteAtD` by a tree popping `ps rd` on the memory `rd`.** -/
def CompleteAtDP (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (ps : Reader → List Pop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Layout} {args : List E}
  {Out : List E → Layout → Prop} {ps : Reader → List Pop}

/-! ## Composition -/

theorem kidsFromInP_dend {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (pss : List (List Pop)) (Dacc : ℕ → Prop) (b n : ℕ) {D D' : ℕ → Prop}, (∀ i, D' i → D i) →
      KidsFromInP coreProgram fs cert rd σ R Dacc cs pss b n D →
      KidsFromInP coreProgram fs cert rd σ R Dacc cs pss b n D'
  | [], [], _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _ :: pss, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromInP_dend cs pss _ _ _ hD hk⟩
  | [], _ :: _, _, _, _, _, _, _, h | _ :: _, [], _, _, _, _, _, _, h => h.elim

/-! ## Regions and nodes -/

theorem RelAtInP.dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {rets : List E} {ps : List Pop}
    (h : RelAtInP coreProgram fs cert rd R D fp n f args rets ps) (hD : ∀ i, D' i → D i) :
    RelAtInP coreProgram fs cert rd R D' fp n f args rets ps :=
  let ⟨t, ⟨hn, hv, hb, hp, ht, hl, hd⟩, hT⟩ := h
  ⟨t, ⟨hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi)⟩, hT⟩

/-- **A function every call instance of which pops `ps`.** -/
theorem relAtInP_of_node {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {rets : List E} {ps : List Pop}
    (h : RelAtIn coreProgram fs cert rd R D fp n f args rets)
    (hn : ∀ τ bufs kids, (Memory.Tree.node f τ bufs kids).pops coreProgram rd = ps) :
    RelAtInP coreProgram fs cert rd R D fp n f args rets ps := by
  obtain ⟨t, ht, -⟩ := h.relAtInT
  refine ⟨t, ht, ?_⟩
  obtain ⟨hname, hv, -⟩ := ht
  cases t with
  | node g τ bufs kids => cases hname; exact hn τ bufs kids
  | phantom => exact hv.elim

end
end LeanVM.Guest.B1
