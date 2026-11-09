/-
  LeanVM.Guest.Budget.Main

  `main`'s weight and words on its tree, call by call: its own frame's, its `HeapBuf`s, and its
  callees' bounds at the calls `mCalls`.
-/

module

public import LeanVM.Guest.Budget.Kids
public import LeanVM.Guest.B1.Main.MainAt

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (mEvs mCalls MainIn walk_main find_main)

@[expose] public section

variable {rd : Reader} {σ : Val} {bufs : List ℕ} {ks : List Tree} {m : MainIn}

/-- `main`'s node, valid with its path's `HeapBuf`s: its callees valid at `mCalls`, its `HeapBuf`s
its walk's. -/
theorem main_node (hv : (Memory.Tree.node "main" σ bufs ks).Valid coreProgram rd [] [])
    (hb : (Memory.Tree.node "main" σ bufs ks).BufsOk coreProgram) (hc : calls (mEvs σ) = mCalls σ m) :
    Tree.KidsValid coreProgram rd σ (mCalls σ m) ks ∧ Tree.BufsOkKids coreProgram ks ∧
      bufs = allocs σ (mEvs σ) := by
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
  rw [find_main, Option.some.injEq] at hf
  subst hf
  rw [walk_main, Out.ret.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  rw [hc] at hk
  obtain ⟨hbufs, hbk⟩ := hb
  refine ⟨hk, hbk, ?_⟩
  rw [hbufs, events_node find_main (walk_main σ)]

/-- **`main`'s weight**: its frame's, and its callees' bounds call by call. -/
theorem main_weight_le (ω : String → ℕ) (W : Call → ℕ) (Ts : List (Tree → Prop))
    (hv : (Memory.Tree.node "main" σ bufs ks).Valid coreProgram rd [] [])
    (hb : (Memory.Tree.node "main" σ bufs ks).BufsOk coreProgram) (hc : calls (mEvs σ) = mCalls σ m)
    (hl : (mCalls σ m).length ≤ Ts.length) (hT : KidsT (mCalls σ m) Ts ks)
    (hB : ∀ c T, (c, T) ∈ (mCalls σ m).zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E),
      t.name = c.f → t.Valid coreProgram rd (c.args.map σ) rets → t.BufsOk coreProgram → T t →
        t.weight ω ≤ W c) :
    (Memory.Tree.node "main" σ bufs ks).weight ω ≤ ω "main" + callsW W (mCalls σ m) := by
  obtain ⟨hk, hbk, -⟩ := main_node hv hb hc
  rw [Tree.weight]
  exact Nat.add_le_add_left (kids_weight_leT ω W _ Ts ks hk hbk hl hT hB) _

end
end LeanVM.Guest.Budget
