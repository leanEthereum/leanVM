module

public import NativeRustcX64.XmssVerify.Bottom

/-!
# `xmss_verify`'s calls of `wots_leaf` (x86-64)

At the callee's entry RSP is the frame region's base (`q = 0`), the randomizer's and the chain
values' addresses on the stack at `8` and `16`: `wotsLeafPre`, the callee's precondition from
inputs in the frame; `values_of`: the chain values it reads.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc.Xmss

public section

variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

/-- An input of `wots_leaf` in the frame. -/
theorem wotsInput (P : Pre w m₀) (C : Common m₀ m) (hrsp : rspOf m = ad m₀ (fr + 0))
    {x n : Nat} (hx : 24 ≤ x) (h : x + n ≤ 5816) (hn : 0 < n) :
    WotsLeafPre.Input m (ad m₀ (fr + x)) n := by
  refine ⟨C.mapped P (by fro), P.ad_nw (by fro), ?_⟩
  rw [stackBelow_at hrsp (by decide), show wotsLeafStack = 3440 from rfl]
  exact P.apart_ad (by fro) (by fro) (by fro) hn (by decide)

/-- **`wots_leaf`'s precondition** at a call from the frame. -/
theorem wotsLeafPre (P : Pre w m₀) (C : Common m₀ m) (hrsp : rspOf m = ad m₀ (fr + 0))
    {o o1 o4 n5 o6 o7 : Nat} (h0 : reg m .rdi = ad m₀ (fr + o))
    (h1 : reg m .rsi = ad m₀ (fr + o1)) (h4 : reg m .r8 = ad m₀ (fr + o4))
    (h5 : (reg m .r9).toNat = n5)
    (h6 : BytesAt m.dmem (ad m₀ (fr + 8)) (regBytes (ad m₀ (fr + o6))))
    (h7 : BytesAt m.dmem (ad m₀ (fr + 16)) (regBytes (ad m₀ (fr + o7))))
    (ho : 24 ≤ o) (ho1 : 24 ≤ o1) (ho4 : 24 ≤ o4) (ho6 : 24 ≤ o6) (ho7 : 24 ≤ o7)
    (h : o + 75 ≤ 5816) (h1' : o1 + 16 ≤ 5816) (h4' : o4 + n5 ≤ 5816) (h6' : o6 + 16 ≤ 5816)
    (h7' : o7 + 16 * 58 ≤ 5816) (hn5 : 0 < n5) : WotsLeafPre m := by
  have e8 : rspOf m + 8#64 = ad m₀ (fr + 8) := by rw [hrsp, ad_add]
  have e16 : rspOf m + 16#64 = ad m₀ (fr + 16) := by rw [hrsp, ad_add]
  refine ⟨stackOk_at P C hrsp (by omega) (by decide), rcAt_at P C hrsp (by omega) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e8]; exact C.mapped P (by fro)
  · rw [hrsp]; exact P.ad_nw (by fro)
  · rw [h0]; exact wotsInput P C hrsp ho h (by omega)
  · rw [h1]; exact wotsInput P C hrsp ho1 h1' (by omega)
  · rw [h4, h5]; exact wotsInput P C hrsp ho4 h4' hn5
  · rw [WotsLeafPre.rndPtr, e8, ptrAt_of h6]; exact wotsInput P C hrsp ho6 h6' (by omega)
  · rw [WotsLeafPre.valuesPtr, e16, ptrAt_of h7]; exact wotsInput P C hrsp ho7 h7' (by omega)
  · simp only [h0, h1, h4, h5, WotsLeafPre.rndPtr, WotsLeafPre.valuesPtr,
      e8, e16, ptrAt_of h6, ptrAt_of h7]
    apply gotAt_at P C hrsp (by omega) (by decide) (by decide)
    intro l hl a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact got_apart P hl (by fro) (by dsimp; decide)
    · exact got_apart P hl (by fro) (by dsimp; decide)
    · exact got_apart P hl (by fro) hn5
    · exact got_apart P hl (by fro) (by dsimp; decide)
    · exact got_apart P hl (by fro) (by dsimp; decide)
    · exact got_apart P hl (by fro) (by dsimp; decide)

omit [Labels] in
/-- The chain values `wots_leaf` reads from a layer's bytes in the frame. -/
theorem values_of {bs : List UInt8} {c : Nat} (hc : c + 1200 ≤ bs.length) {o : Nat}
    (h : BytesAt m.dmem (ad m₀ (fr + o)) (takeLayer bs c).1.memBytes) :
    ((List.range 58).map fun i ↦
      bytesOf m.dmem (ad m₀ (fr + o + 256) + BitVec.ofNat 64 (16 * i)) 16) =
      (takeLayer bs c).1.chainValues := by
  apply List.ext_getElem (by simp [takeLayer])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  have hv := layer_value hc h (i := i) h1
  have hl : ((takeLayer bs c).1.chainValues.getD i []).length = 16 := by
    simp only [takeLayer, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range h1, Option.map_some, Option.getD_some]
    exact length_slice (by omega)
  have := hv.bytesOf
  rw [hl, ad_add] at this
  rw [ad_add, show fr + o + 256 + 16 * i = fr + o + (256 + 16 * i) by omega,
    this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

end

end NativeRustcX64.Xmss.XmssVerify
