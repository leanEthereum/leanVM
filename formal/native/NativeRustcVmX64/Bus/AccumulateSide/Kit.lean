module

public import NativeRustcVmX64.Bus.AccumulateSide.Env
public import NativeRustcVm.Tables.Same

/-!
# `accumulate_side`: what its steps share (x86-64)

A location of a description evaluates to its value (`Holds.ev`); a value given (`holds_one`).
`eq_above`'s call (`eqAbove_pre`, `eqAbove_ret`) and the slices of the point it reads
(`slice_above`, `slice_above_nil`, `slice_low`). The forms over bytes that stayed the same
(`FormsAt.of_same`) and with one replaced (`FormsAt.modify`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open LeanVM.Protocol.Verifier (Placement)

public section

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
  {m : MachineData}

/-- **A location of a description** evaluates to its value. -/
theorem Holds.ev (h : Holds rs V D m) {s : Sym} {i : Nat} (hp : (s, i) ∈ D) (hs : isLoc s = true)
    (vs : Nat → BitVec 64) (ret : BitVec 64) : s.eval (Env.ofMachine m rs vs ret) = (V i).toBitVec := by
  have := h _ hp
  simp only [tval] at this
  rw [eval_loc hs, ← this]

/-- One location's value. -/
theorem holds_one {s : Sym} {i : Nat} (h : tval rs m s = V i) : Holds rs V [(s, i)] m :=
  fun p hp ↦ by
    simp only [List.mem_singleton] at hp
    subst hp
    exact h

/-- A location's value from its symbolic value. -/
theorem tval_of {s : Sym} {u : UInt64}
    {e : Env} {c : Sym} (h : tval rs m s = UInt64.ofBitVec (c.eval e))
    (hc : c.eval e = u.toBitVec) : tval rs m s = u := by
  rw [h, hc]

end

/-! ## Slices of the point -/

theorem ewsOf_drop (d : DataMem) (b : BitVec 64) (n k : Nat) :
    (NativeRustcVm.ewsOf d b (k + n)).drop k =
      NativeRustcVm.ewsOf d (b + BitVec.ofNat 64 (16 * k)) n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, NativeRustcVm.getElem_ewsOf]
  rw [NativeRustcVm.addr_add_add, Nat.mul_add]

/-- The elements from `x + 16·v`: `x`'s from `v`. -/
theorem slice_above {m : MachineData} {a n : BitVec 64} {v : Nat} (hv : v ≤ n.toNat)
    {a' n' : BitVec 64} (ha' : a' = a + BitVec.ofNat 64 (16 * v))
    (hn' : n'.toNat = n.toNat - v) :
    slice m a' n' = (slice m a n).extract v (slice m a n).size := by
  unfold slice
  rw [ha', hn', ← ewsOf_drop m.dmem a (n.toNat - v) v, show v + (n.toNat - v) = n.toNat by omega]
  simp

/-- An empty rest when `v > |x|`. -/
theorem slice_above_nil {m m' : MachineData} {a n : BitVec 64} {v : Nat} (hv : n.toNat < v)
    {a' n' : BitVec 64} (hn' : n'.toNat = 0) :
    slice m a' n' = (slice m' a n).extract v (slice m' a n).size := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp; omega) fun i h1 h2 ↦ by simp at h1

/-- `x.get(..v).unwrap_or(x)`: the first `min(v, |x|)` elements. -/
theorem slice_low {m : MachineData} {a n : BitVec 64} {v : Nat} {n' : BitVec 64}
    (hn' : n'.toNat = min v n.toNat) : slice m a n' = (slice m a n).extract 0 v := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp) fun i h1 h2 ↦ by simp

theorem slice_size (m : MachineData) (a n : BitVec 64) : (slice m a n).size = n.toNat := by
  simp [slice]

/-! ## `eq_eval_fn` for `eq_above` -/

/-- **`eq_eval_fn`'s precondition** at a call for `eq_above p` of the point (`pa`, `pn`). -/
theorem eqAbove_pre {st : MachineData} {p : Placement} {pa pn : BitVec 64}
    (hS : StackOk st eqEvalFnStack) (hpn : pn.toNat < 64)
    (hsl : SliceOk st pa pn eqEvalFnStack) (h8 : 8 ≤ (stackBelow st eqEvalFnStack).toNat)
    (h0 : (reg st .rdi).toNat = pn.toNat - p.variableCount)
    (h2 : reg st .rdx = if pn.toNat < p.variableCount then 8#64
      else pa + BitVec.ofNat 64 (16 * p.variableCount))
    (h3 : (reg st .rcx).toNat = pn.toNat - p.variableCount) : EqEvalFnOfEqAbovePre st := by
  refine ⟨hS, by rw [h0, h3]; omega, ?_⟩
  unfold SliceOk Readable OffStack
  by_cases hlt : pn.toNat < p.variableCount
  · simp only [hlt, ↓reduceIte] at h2
    rw [h2, h3, show pn.toNat - p.variableCount = 0 by omega, Nat.mul_zero]
    refine ⟨⟨fun j hj ↦ absurd hj (by omega), by unfold NoWrap; simp⟩, ?_⟩
    unfold Apart
    left
    simpa using h8
  · simp only [hlt, ↓reduceIte] at h2
    rw [h2, h3]
    obtain ⟨⟨hm, hnw⟩, hap⟩ := hsl
    unfold NoWrap at hnw
    unfold OffStack Apart at hap
    rcases NativeRustcVm.toNat_add_ofNat_le (a := pa) (i := 16 * p.variableCount)
      (by omega) with ha | ⟨ha0, hae⟩
    · refine ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩
      · rw [NativeRustcVm.addr_add_add]; exact hm _ (by omega)
      · unfold NoWrap; rw [ha]; omega
      · unfold Apart; rw [ha]; omega
    · have hz : pn.toNat - p.variableCount = 0 := by omega
      rw [hz, Nat.mul_zero]
      refine ⟨⟨fun j hj ↦ absurd hj (by omega), by unfold NoWrap; omega⟩, ?_⟩
      unfold Apart; rw [ha0]; omega

/-- **`eq_eval_fn`'s result** is `eq_above p` of the point (`pa`, `pn`). -/
theorem eqAbove_ret {st m' : MachineData} {p : Placement} {pa pn : BitVec 64}
    (h0 : (reg st .rdi).toNat = pn.toNat - p.variableCount)
    (h1 : (reg st .rsi).toNat = p.index >>> p.variableCount)
    (h2 : reg st .rdx = if pn.toNat < p.variableCount then 8#64
      else pa + BitVec.ofNat 64 (16 * p.variableCount))
    (h3 : (reg st .rcx).toNat = pn.toNat - p.variableCount)
    (hq : EqEvalFnOfEqAbovePost st m') : ewRet m' = eqAbove p (slice st pa pn) := by
  have hsz : (slice st pa pn).size = pn.toNat := slice_size st pa pn
  have hext : slice st (reg st .rdx) (reg st .rcx) =
      (slice st pa pn).extract p.variableCount (slice st pa pn).size := by
    by_cases hlt : pn.toNat < p.variableCount
    · exact slice_above_nil hlt (by omega)
    · simp only [hlt, ↓reduceIte] at h2
      exact slice_above (by omega) h2 h3
  rw [hq.1, h0, h1, hext]
  unfold eqAbove
  rw [hsz]

/-! ## The forms -/

/-- The forms over bytes that stayed the same. -/
theorem FormsAt.of_same {d d' : Mem 64} {a : BitVec 64} {G : Array (Array FormW)}
    (h : FormsAt d a G) (hs : Same d d' a formsBytes) : FormsAt d' a G := by
  have hf : formBufBytes = 5928 := rfl
  have hb : formsBytes = 106704 := rfl
  refine ⟨h.size, h.row_size, fun t ht s hs' ↦ ?_⟩
  have h1 := h.row_size t ht
  have h2 := h.size
  exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms t ht s hs')
    (hs.sub (by rw [hb, hf]; unfold nTables at h2; omega))

/-- **The forms with the owner's form of the side replaced.** -/
theorem FormsAt.modify {d d' : Mem 64} {a : BitVec 64} {G : Array (Array FormW)}
    (h : FormsAt d a G) {o s : Nat} (ho : o < G.size) (hs : s < G[o].size) (g : FormW → FormW)
    (hx : FormBufAt d' (off a (formBufBytes * (3 * o + s))) (g G[o][s]))
    {Z : BitVec 64 → Prop} (hnw : a.toNat + formsBytes ≤ 2 ^ 64)
    (hss : NativeRustcVm.SameOutside d d' fun q ↦
      NativeRustcVm.InRange (off a (formBufBytes * (3 * o + s))) formBufBytes q ∨ Z q)
    (hZ : ∀ j < formsBytes, ¬Z (a + BitVec.ofNat 64 j)) :
    FormsAt d' a (G.modify o fun row ↦ row.modify s g) := by
  have hG := h.size
  have hrow := h.row_size
  have hf : formBufBytes = 5928 := rfl
  have hfs : formsBytes = 106704 := rfl
  unfold nTables at hG
  have ho6 : o < 6 := by rw [hG] at ho; exact ho
  have hs3 : s < 3 := by rw [hrow o ho] at hs; exact hs
  have key : ∀ t s', t < 6 → s' < 3 → 3 * t + s' ≠ 3 * o + s →
      Same d d' (off a (formBufBytes * (3 * t + s'))) formBufBytes := by
    intro t s' ht hs' hne j hj
    rw [hf] at hj
    refine hss _ fun hq ↦ hq.elim (fun hq ↦ ?_)
      (fun hq ↦ hZ (5928 * (3 * t + s') + j) (by omega) ?_)
    · simp only [off, hf] at hq
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.inRange_iff (by
        unfold NativeRustcVm.NoWrap
        rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega),
        NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
        at hq
      omega
    · simp only [off, hf] at hq
      rwa [NativeRustcVm.addr_add_add] at hq
  refine ⟨by rw [Array.size_modify]; exact hG, fun t ht ↦ ?_, fun t ht s' hs' ↦ ?_⟩
  · rw [Array.size_modify] at ht
    rw [Array.getElem_modify]
    split
    · rw [Array.size_modify]; exact hrow t ht
    · exact hrow t ht
  · have ht' : t < G.size := by rw [Array.size_modify] at ht; exact ht
    have hr := hrow t ht'
    have ht6 : t < 6 := by rw [hG] at ht'; exact ht'
    simp only [Array.getElem_modify] at hs' ⊢
    by_cases hto : o = t
    · subst hto
      simp only [↓reduceIte, Array.size_modify] at hs' ⊢
      rw [Array.getElem_modify]
      by_cases hss' : s = s'
      · subst hss'
        simp only [↓reduceIte]
        exact hx
      · simp only [hss', ↓reduceIte]
        have hs3' : s' < 3 := by rw [hr] at hs'; exact hs'
        exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms o ht' s' hs')
          (key o s' ho6 hs3' (by omega))
    · simp only [hto, ↓reduceIte] at hs' ⊢
      have hs3' : s' < 3 := by rw [hr] at hs'; exact hs'
      exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms t ht' s' hs')
        (key t s' ht6 hs3' (by omega))

end

end NativeRustcVmX64.Bus.AccumulateSide
