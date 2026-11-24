/-
  LeanVM.Guest.B1.KeccakGkr.FlatG

  Flat bodies placed when a callee's caller's words depend on the frame pointers of the callees
  before it (and its own), and the caller's own words on all of them.
-/

module

public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Memory.UniformF

/-!
# Callees reading earlier callees' buffers

`verify_keccak`'s layers each read the buffers the previous layer returned, which sit in that
layer's frame; and `verify_keccak`'s own claim records hold pointers into them. So a callee's
caller's words depend on the frame pointers of the callees up to it (`KidG.Lin ps`, `ps` the
frame pointers so far, its own last), and the caller's own words on all of them. A callee's
arguments may hold pointers into earlier callees' buffers too (`KidG.args ps`, `ps` the frame
pointers before it).

* `atAllG pre ks fps`: the calls placed at `fps`, each reading its words at the prefix of frame
  pointers so far (after `pre`).
* a flat function is complete, placed, its own buffers' words depending on the
  callees' frame pointers, its callees reading the caller's words, its own buffers and the earlier
  callees' results, its statements holding with any calls' relation (the callees are placed apart).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A call whose arguments depend on the frame pointers of the calls before it, and whose caller's
words on those up to it. -/
structure KidG where
  f : String
  taken : Bool
  args : List ℕ → List E
  Lin : List ℕ → Layout
  Out : List ℕ → List E → Layout → Prop

/-- The calls placed at `fps`, after the frame pointers `pre`. -/
def atAllG : List ℕ → List KidG → List ℕ → List Kid
  | pre, k :: ks, p :: ps =>
    ⟨k.f, k.taken, k.args pre, k.Lin (pre ++ [p]), k.Out (pre ++ [p])⟩ :: atAllG (pre ++ [p]) ks ps
  | _, _, _ => []

/-- The buffers the entered calls return. -/
def takenOuts : List Kid → List (List E × Layout) → Layout
  | k :: ks, o :: os => (if k.taken then o.2 else []) ++ takenOuts ks os
  | _, _ => []

theorem takenOuts_sub : ∀ {ks : List Kid} {outs : List (List E × Layout)} {L : Layout},
    OutsIn ks outs L → ∀ q ∈ takenOuts ks outs, q ∈ L
  | k :: ks, o :: os, L, ⟨h, hs⟩, q, hq => by
    simp only [takenOuts, List.mem_append] at hq
    rcases hq with hq | hq
    · split at hq
      · rename_i ht; exact h ht q hq
      · simp at hq
    · exact takenOuts_sub hs q hq
  | [], _, _, _, q, hq => by simp [takenOuts] at hq
  | _ :: _, [], _, _, q, hq => by simp [takenOuts] at hq

theorem regionsOk_mono {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ {Dacc : ℕ → Prop} {ks : List Kid} {outs : List (List E × Layout)},
      RegionsOk R Dacc ks outs → RegionsOk R' Dacc ks outs
  | _, _ :: _, _ :: _, ⟨h, hs⟩ => ⟨fun ht i hi => (h ht i hi).imp_left (hR i), regionsOk_mono hR hs⟩
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial

variable {fs : String → ℕ} {cert : String → V → ℕ}

end
end LeanVM.Guest.B1
