/-
  Rv64mc.Proof.Runtime.SavedT

  What a total proof cut into parts keeps of memory across its parts, for any number of saved registers: the saved
  registers' slots (`Saved`: the word at `top + c` is `v`, for the offsets `cs` and values `vs` taken in order) and
  the frame, the code, the static data with them (`MemOk`). Each part's proof carries `MemOk` across a callee
  (`MemOk.call`), a store into what the function allocated (`MemOk.fresh`) and a store into the frame below the
  slots (`MemOk.slot`), each from bounds on the frame (`F` bytes) and on the slots (the `K` bytes below `top`), which
  `slots_le` checks once per function (`slots_in`).

  `Saved top cs vs M` unfolds, for literal lists, into one equation per slot: `rv_introT` and `rv_symT`'s closer
  read the slots at the epilogue as they read a function's own conjunction, and a part's goal of `Saved` is the
  closer's after `simp only [Saved]`.

  ## Main definitions

  * `Saved`, `MemOk`, `SlotsIn`

  ## Main results

  * `Saved.keep`, `slots_le`, `MemOk.call`, `MemOk.fresh`, `MemOk.slot`, `MemOk.next_le`
-/

import Rv64mc.Tactic.Heap

namespace Rv64mc.Proof.Runtime.SavedT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **The saved registers' slots**: the word at `top + c` is `v`, for the offsets `cs` and the values `vs` in
    order. -/
def Saved (top : Word) : List Word → List Word → MachineState → Prop
  | c :: cs, v :: vs, M => M.getMem (top + c) = v ∧ Saved top cs vs M
  | _, _, _ => True

/-- What every part keeps of memory: the frame (writing at most `out` besides the stack and what it allocates), the
    code, the static data, the saved registers' slots. -/
def MemOk (env : Env) (top : Word) (out : Word → Prop) (cs vs : List Word) (m M : MachineState) : Prop :=
  env.Frame top out m M ∧ M.code = m.code ∧ env.Static M ∧ Saved top cs vs M

/-- Every offset `c` names a slot among the `K` bytes below `top`: `2^64 - K ≤ c`, so `top + c = top - (2^64 - c)`
    for `K ≤ top`. -/
def SlotsIn (K : Nat) (cs : List Word) : Prop := ∀ c ∈ cs, 2 ^ 64 - K ≤ c.toNat

/-- `SlotsIn K cs` for literal offsets. -/
macro "slots_in" : tactic =>
  `(tactic| (simp only [SlotsIn, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    BitVec.toNat_ofNat]; omega))

/-- A slot's address, as a number. -/
theorem slot_toNat {top c : Word} {K : Nat} (hK : K ≤ top.toNat) (hc : 2 ^ 64 - K ≤ c.toNat) :
    (top + c).toNat = top.toNat - (2 ^ 64 - c.toNat) := by
  have := c.isLt
  rw [BitVec.toNat_add]
  omega

/-- **The slots kept** by a memory that agrees on the `K` bytes below `top`. -/
theorem Saved.keep {top : Word} {K : Nat} {M X : MachineState} (hK : K ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - K ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a) :
    ∀ {cs vs : List Word}, SlotsIn K cs → Saved top cs vs M → Saved top cs vs X
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | c :: cs, v :: vs, hs, ⟨h1, h2⟩ => by
    have hc := hs c (List.mem_cons_self ..)
    have e := slot_toNat hK hc
    have := c.isLt
    refine ⟨(hk _ (by omega) (by omega)).trans h1, Saved.keep hK hk (fun d hd => hs d (List.mem_cons_of_mem _ hd)) h2⟩

/-- `SlotsIn K cs` for literal offsets, by `slots_in`. -/
theorem slots_le {K : Nat} {cs : List Word} (h : SlotsIn K cs := by slots_in) : SlotsIn K cs := h

variable {env : Env} {top : Word} {out : Word → Prop} {cs vs : List Word} {m M : MachineState}

/-- **`MemOk` across a callee**, from a stack top no higher, each word of its `out` one the function may write, the
    slots kept. -/
theorem MemOk.call {K : Nat} {top' : Word} {X : MachineState} {out' : Word → Prop} (h : MemOk env top out cs vs m M)
    (hs : SlotsIn K cs) (hK : K ≤ top.toNat) (ht : top'.toNat ≤ top.toNat) (hf : env.Frame top' out' M X)
    (hc : X.code = M.code) (hst : env.Static X) (hout : ∀ a, out' a → env.MayWrite top out m X a)
    (hk : ∀ a : Word, top.toNat - K ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a) :
    MemOk env top out cs vs m X :=
  ⟨Tactic.frame_trans h.1 hf ht hout, hc.trans h.2.1, hst, h.2.2.2.keep hK hk hs⟩

/-- **`MemOk` across a store into what the function allocated**, `NEXT` kept. -/
theorem MemOk.fresh {K : Nat} {a v : Word} (h : MemOk env top out cs vs m M) (hs : SlotsIn K cs)
    (hlim : env.stackLimit.toNat + K ≤ top.toNat) (hlo : (env.next m).toNat ≤ a.toNat)
    (hhi : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env top out cs vs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hnM := h.1.2.1
  have hn : env.next (M.setMem a v) = env.next M := Tactic.next_setMem (Tactic.ne_of_toNat (by omega))
  refine ⟨⟨Tactic.frame_fresh h.1 hn.symm hlo (by rw [hn]; omega), by rw [MachineState.code_setMem]; exact h.2.1,
    Tactic.static_store h.2.2.1 (by omega), h.2.2.2.keep (by omega) (fun x h1 h2 => ?_) hs⟩, hn⟩
  exact MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))

/-- **`MemOk` across a store into the frame** (`F` bytes) below the slots (the `K` bytes below `top`), `NEXT`
    kept. -/
theorem MemOk.slot {K F : Nat} {a v : Word} (h : MemOk env top out cs vs m M) (hs : SlotsIn K cs)
    (hlim : env.stackLimit.toNat + F ≤ top.toNat) (hlo : top.toNat - F ≤ a.toNat) (hhi : a.toNat + 8 + K ≤ top.toNat) :
    MemOk env top out cs vs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hn : env.next (M.setMem a v) = env.next M := Tactic.next_setMem (Tactic.ne_of_toNat (by omega))
  refine ⟨⟨Tactic.frame_slot h.1 (by omega) (by omega), by rw [MachineState.code_setMem]; exact h.2.1,
    Tactic.static_store h.2.2.1 (by omega), h.2.2.2.keep (by omega) (fun x h1 h2 => ?_) hs⟩, hn⟩
  exact MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))

/-- `NEXT` at the entry at most `NEXT` now. -/
theorem MemOk.next_le (h : MemOk env top out cs vs m M) : (env.next m).toNat ≤ (env.next M).toNat := h.1.1

end Rv64mc.Proof.Runtime.SavedT
