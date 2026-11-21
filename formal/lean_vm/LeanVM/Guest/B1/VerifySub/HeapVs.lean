/-
  LeanVM.Guest.B1.VerifySub.HeapVs

  An honest child's `verify_sub` node pops the child's advised sizes: its own `zeta` buffer's, then its
  `verify_tables` callee's three.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteBTE
public import LeanVM.Guest.B1.VerifySub.ChildHeap
public import LeanVM.Guest.B1.VerifySub.HeapNoAdv
public import LeanVM.Guest.Memory.HeapOne
public import LeanVM.Guest.Memory.AdvFreeOk

/-!
# `verify_sub`'s advised sizes

`vs_heap`: a valid `verify_sub` node with the honest buffers `vsSizes S.d`, whose valid `verify_tables` callees
pop their own advised sizes of `S.H.sizes`, one of them among its callees, pops `childHeapH`: its other callees
are in `AdvFree` (`vs_advFreeBut`, `advFreeOk`) and its paths call `verify_tables` at most once (`vs_vtBound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **An honest child's `verify_sub` node pops its advised sizes.** -/
theorem vs_heap {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) {rd : Reader} {σ : Val} {ks : List Tree} {args rets : List E}
    (hv : (Memory.Tree.node "verify_sub" σ (vsSizes S.d) ks).Valid coreProgram rd args rets)
    (hvt : ∀ k ∈ ks, k.name = "verify_tables" → (∃ a r, k.Valid coreProgram rd a r) →
      k.heapPops heapSlots = (heapSlots "verify_tables").map (advEntry S.H.sizes))
    {t0 : Tree} (h0 : t0 ∈ ks) (h0n : t0.name = "verify_tables") (h0v : ∃ a r, t0.Valid coreProgram rd a r) :
    (Memory.Tree.node "verify_sub" σ (vsSizes S.d) ks).heapPops heapSlots = childHeapH bytecode c := by
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkk⟩ := hv
  have efn : fn = fn% «verify_sub» := Option.some.inj (hf.symm.trans find_vs)
  subst efn
  have hcs : ∀ c ∈ calls es, AdvFree c.f ∨ c.f = "verify_tables" := fun c hc =>
    (advFreeBut_calls vs_advFreeBut vs_name hf hw c hc).imp_right List.mem_singleton.mp
  have hcnt := (calls_count "verify_tables" hw).trans_eq vs_vtBound
  rw [heapPops_node, heapPopsKids_one (advFree_callsIn advFreeOk) (fun _ h => advFree_slots advFreeOk h) hkk hcs hcnt
    hvt h0 h0n h0v]
  have hd := S.d_bounds hbl
  have hn : S.H.n ≤ 30 := S.nT_le hbl
  have e5 : advEntry (vsSizes S.d) 5 = [Hints.count S.d] := by
    rw [advEntry, show (vsSizes S.d)[5]? = some S.d from rfl, Option.map_some, Option.toList_some,
      Hints.count, LeanVM.Protocol.Verifier.gpow, LeanVM.Guest.Value.gen_pow_eq_ofK]
  have eH : ∀ k m, S.H.sizes[k]? = some m → m < 2 ^ 128 → advEntry S.H.sizes k = [Hints.count m] := fun k m h _hm => by
    rw [advEntry, h, Option.map_some, Option.toList_some, Hints.count, LeanVM.Protocol.Verifier.gpow,
      LeanVM.Guest.Value.gen_pow_eq_ofK]
  rw [show heapSlots "verify_sub" = [5] from rfl, show heapSlots "verify_tables" = [108, 109, 111] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [e5, eH 108 (7 * (S.H.n + 1)) rfl (by omega), eH 109 (S.H.n + 1) rfl (by omega),
    eH 111 (S.H.n + 1) rfl (by omega), childHeapH, S.hann]
  have hh : S.layout.tableLogHeights.foldl max 0 = S.H.n := by
    show S.layout.tableLogHeights.foldl max 0 = S.hs.foldl max 0
    rw [S.hlayout]; rfl
  simp only [hh, List.map_cons, List.map_nil]
  rw [Nat.mul_comm (S.H.n + 1) 7]
  rfl

end

end LeanVM.Guest.B1.VerifySub
