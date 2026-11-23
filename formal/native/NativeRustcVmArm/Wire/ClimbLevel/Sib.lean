module

public import NativeRustcVmArm.Wire.ClimbLevel.Pair

/-!
# `climb_level`'s sibling steps

Node `i`'s sibling found among the nodes (`sibStep_found`) or read (`sibStep_read`), one node
more of `sibsM` (`sibsM_step`, `sibsM_none`); a key's low bit as the executor tests it
(`bit0_low`); a digest written by a block (`digest_write`); `Mid` kept by a block without
writes (`Mid.keep`).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

/-- **The sibling found**: node `j`, the first of key `k ^^^ 1`. -/
theorem sibStep_found {i j ci : Nat} (hi : i < ns.length) (hj : j < ns.length)
    (hk : ns[j].1 = ns[i].1 ^^^ 1) (hmiss : Miss ns i j) :
    sibStep B ns ns[i] ci = some ((ns[i].1, ns[j].2, true), ci) := by
  unfold sibStep
  rw [lookup_first ns _ j hj (fun j' hj' ↦ hmiss j' hj' (by omega) hi) hk]

/-- **The sibling read**: no node of key `k ^^^ 1`. -/
theorem sibStep_read {i ci : Nat} (hi : i < ns.length) (hmiss : Miss ns i ns.length) :
    sibStep B ns ns[i] ci = (rdDigest B ci).map fun p ↦ ((ns[i].1, p.1, false), p.2) := by
  unfold sibStep
  rw [lookup_none ns _ fun j' hj' ↦ hmiss j' hj' hj' hi]

/-- **One node more** of `sibsM`. -/
theorem sibsM_step {i : Nat} {sl : List (Nat × Digest × Bool)} {ci ci' : Nat}
    {q : Nat × Digest × Bool} (hs : sibsM B ns (ns.take i) c = some (sl, ci)) (hi : i < ns.length)
    (hq : sibStep B ns ns[i] ci = some (q, ci')) :
    sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci') := by
  rw [take_succ_eq hi, sibsM_snoc, hs]
  simp only [Option.bind_some, hq, Option.map_some]

/-- **No sibling** for node `i`: `None`. -/
theorem sibsM_none {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat}
    (hs : sibsM B ns (ns.take i) c = some (sl, ci)) (hi : i < ns.length)
    (hq : sibStep B ns ns[i] ci = none) : sibsM B ns ns c = none := by
  have h1 : sibsM B ns (ns.take (i + 1)) c = none := by
    rw [take_succ_eq hi, sibsM_snoc, hs]
    simp only [Option.bind_some, hq, Option.map_none]
  have e : sibsM B ns ns c = sibsM B ns (ns.take (i + 1) ++ ns.drop (i + 1)) c := by
    rw [List.take_append_drop]
  rw [e, sibsM_append, h1]
  rfl

/-- A word's low bit, as `tbnz w, #0` tests it. -/
theorem bit0_low (x : BitVec 64) : (Sym.low .W32 x).getLsbD 0 = decide (x.toNat % 2 = 1) := by
  show (x.take 32).toNat.testBit 0 = _
  rw [toNat_take', Nat.testBit_zero]
  congr 1
  apply propext
  omega

/-- **A digest written** by a block: four words, each a write of a value. -/
theorem digest_write [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (ho : o + 32 ≤ sz)
    {v1 v2 v3 v4 : Sym}
    (hw1 : ∀ i < 8, findWrite r (o + i) S.mem = some (v1, i))
    (hw2 : ∀ i < 8, findWrite r (o + 8 + i) S.mem = some (v2, i))
    (hw3 : ∀ i < 8, findWrite r (o + 16 + i) S.mem = some (v3, i))
    (hw4 : ∀ i < 8, findWrite r (o + 24 + i) S.mem = some (v4, i)) {dg : Digest}
    (e1 : UInt64.ofBitVec (v1.eval env) = dg[0]) (e2 : UInt64.ofBitVec (v2.eval env) = dg[1])
    (e3 : UInt64.ofBitVec (v3.eval env) = dg[2]) (e4 : UInt64.ofBitVec (v4.eval env) = dg[3]) :
    WordsAt m.dmem (b + BitVec.ofNat 64 o) dg.toList := by
  have w : ∀ {o' : Nat} {v : Sym} {u : UInt64}, o' + 8 ≤ sz →
      (∀ i < 8, findWrite r (o' + i) S.mem = some (v, i)) → UInt64.ofBitVec (v.eval env) = u →
      WordAt m.dmem (b + BitVec.ofNat 64 o') u := fun ho hw he ↦ by
    have h := hm.bytesAt_write hb ho hw
    rw [byteOf_range, he] at h
    exact h
  refine wordsAt_digest_iff.mpr ⟨w (by omega) hw1 e1, ?_, ?_, ?_⟩ <;>
    rw [NativeRustcVm.addr_add_add]
  · exact w (by omega) hw2 e2
  · exact w (by omega) hw3 e3
  · exact w (by omega) hw4 e4

/-- **`Mid` kept** by a block without writes. -/
theorem Mid.keep {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat}
    {q : Nat × Digest × Bool} {m m' : MachineData}
    (h : Mid m0 bp B c ns i sl ci q m) (hfr : Frm m0 m') (hd : m'.dmem = m.dmem)
    (hr : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X27, .X28, .X29],
      m'.regs.getXReg r = m.regs.getXReg r) :
    Mid m0 bp B c ns i sl ci q m' :=
  ⟨hfr, h.fx.keep fun r h ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp),
    h.lt, h.hs, by rw [hd]; exact h.rd, by rw [hd]; exact h.sb, by rw [hd]; exact h.nx, h.hl,
    h.key, by rw [hd]; exact h.dg, by rw [hr .X19 (by simp)]; exact h.x19,
    by rw [hr .X20 (by simp)]; exact h.x20, by rw [hr .X21 (by simp)]; exact h.x21,
    by rw [hr .X23 (by simp)]; exact h.x23, by rw [hr .X24 (by simp)]; exact h.x24⟩

/-- A parent of an even key: node `i`'s digest first. -/
theorem parent_even {x : Nat × Digest} {s : Nat × Digest × Bool} (h : x.1 % 2 = 0) :
    parentOf x s = [(x.1 >>> 1, NativeVm.Model.hashPair x.2 s.2.1)] := by
  unfold parentOf
  simp only [h, true_or, ↓reduceIte, keccak_pair]

/-- A parent of an odd key, its sibling read: the sibling's digest first. -/
theorem parent_odd {x : Nat × Digest} {s : Nat × Digest × Bool} (h : x.1 % 2 = 1)
    (hs : s.2.2 = false) : parentOf x s = [(x.1 >>> 1, NativeVm.Model.hashPair s.2.1 x.2)] := by
  unfold parentOf
  simp only [h, hs, or_true, ↓reduceIte, keccak_pair, show (1 : Nat) ≠ 0 by decide]

/-- No parent of an odd key whose sibling is a node. -/
theorem parent_none {x : Nat × Digest} {s : Nat × Digest × Bool} (h : x.1 % 2 = 1)
    (hs : s.2.2 = true) : parentOf x s = [] := by
  unfold parentOf
  simp only [h, hs, show (1 : Nat) ≠ 0 by decide, Bool.true_eq_false, or_self, ↓reduceIte]

end

end NativeRustcVmArm.Wire.ClimbLevel
