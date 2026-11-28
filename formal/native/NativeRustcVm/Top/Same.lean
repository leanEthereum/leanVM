module

public import NativeRustcVm.Tables.Same
public import NativeRustcVm.KeccakGkr.Rep
public import NativeRustcVm.Ring.Rep
public import NativeRustcVm.Layout.Values

/-!
# The phases' results over bytes that stayed the same

`verify_execution` keeps each phase's result in its working area while later phases run: the
tables' evaluations (`TableEvalsAt.of_same`), the Keccak output (`KeccakOutAt.of_same`), the ring
switch's output (`RingWAt.of_same`), the out-of-domain claim (`OodAt.of_same`) hold in a memory
whose bytes over them are the same.
-/

namespace NativeRustcVm.Top

open NativeVm.Model NativeRustcVm.Layout NativeRustcVm.Tables
open NativeRustcVm.Transcript (off)

public section

variable {d d' : Mem 64} {p : BitVec 64}

theorem TableEvalsAt.of_same {ev : Array (Array EW × Array EW)} (h : TableEvalsAt d p ev)
    (hs : Same d d' p tableEvalsBytes) : TableEvalsAt d' p ev := by
  refine ⟨h.1, fun i hi ↦ ?_⟩
  have h6 : ev.size = 6 := h.1
  obtain ⟨h1, h2⟩ := h.2 i hi
  have hs' := hs.sub (o := tableEvalBytes * i) (k := tableEvalBytes) (by
    unfold tableEvalsBytes nTables tableEvalBytes; omega)
  exact ⟨BufEWAt.of_same h1 hs' (by decide),
    BufEWAt.of_same h2 (hs'.sub (o := valuesOff) (k := 1480) (by decide)) (by decide)⟩

theorem KeccakOutAt.of_same {pt sl : Array EW} (h : KeccakGkr.KeccakOutAt d p pt sl)
    (hs : Same d d' p KeccakGkr.outBytes) : KeccakGkr.KeccakOutAt d' p pt sl := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨BufEWAt.of_same h1 hs (by decide), h2, EWsAt.of_same h3
    (hs.sub (o := KeccakGkr.slicesOff) (k := 1024) (by decide)) ?_⟩
  simp [h2]

theorem RingWAt.of_same {x : EW} {cs : Array EW} (h : Ring.RingWAt d p x cs)
    (hs : Same d d' p Ring.ringWBytes) : Ring.RingWAt d' p x cs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨EWAt.of_same h1 hs (by decide), h2, EWsAt.of_same h3
    (hs.sub (o := 16) (k := 1024) (by decide)) ?_⟩
  simp [h2, Ring.coeffCount]

theorem EqClaimAt.of_same {z : Array EW} {v : EW} (h : EqClaimAt d p z v)
    (hs : Same d d' p eqClaimBytes) : EqClaimAt d' p z v :=
  ⟨BufEWAt.of_same h.1 hs (by decide), EWAt.of_same h.2 (hs.sub (o := 488) (k := 16) (by decide))
    le_rfl⟩

theorem OodAt.of_same {c : StackClaimW} (h : OodAt d p c) (hs : Same d d' p eqClaimBytes) :
    OodAt d' p c := by
  obtain ⟨z, hz, h⟩ := h
  exact ⟨z, hz, EqClaimAt.of_same h hs⟩

end

end NativeRustcVm.Top
