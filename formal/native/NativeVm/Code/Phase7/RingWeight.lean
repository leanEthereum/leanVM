module

public import NativeVm.Code.Phase7.RingWE
public import NativeVm.Code.Data
public import NativeVm.Equiv.RingSwitch

/-!
# A stack claim's weight at a point, on the model's words

The kernels the stacked opening's basis evaluation (`BasisW.eval`) calls for each stack claim's
`StackWeight.eval`, stated on the model's arrays in memory (`EWArr`) and its words (`EW`), the
result's limbs in `r9`, `r10`:

* `weightEq_spec`: `weightEq`, the `.eq` weight of a column claim on the stack,
  `eqEval (stackPoint pl pt stackLog) x` (the out-of-domain claim's is `stackPoint ⟨0, 0⟩ z 0 = z`,
  `stackPoint_zero`); it writes no memory;
* `weightRing_spec`: `weightRing`, the ring-switched claim's `.ring pl r c` weight,
  `eqAbove pl x · ringWeight r (x.extract 0 vc) c`, through a buffer of `bufWords` words at `rbx`,
  the only words it writes.

Both keep `rdi` and `rsp` (`RegsFrame arrRegs`), never fail, and keep which words exist.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field NativeVm.Model LeanVM.Parameters
open LeanVM.Protocol.Verifier (Placement)
open NativeVm.Transcript (wd Fits Disj wd_ne_of_disj)

variable {s : QState} {F : QState → Prop}

/-! ## Frames -/

/-- A statement that writes neither `rdi` nor `rsp` keeps all but `arrRegs`. -/
theorem regsFrame_arr {c : Stmt} {s' : QState} (hdi : c.writes .rdi = false)
    (hsp : c.writes .rsp = false) (hw : ∀ r, c.writes r = false → s'.reg r = s.reg r) :
    RegsFrame arrRegs s s' := by
  intro r hr
  cases r <;> first
    | exact hw _ hdi
    | exact hw _ hsp
    | exact absurd (by simp [arrRegs]) hr

/-- The kernel's facts beside its result. -/
theorem WP.frames {c : Stmt} {P : QState → Prop} (hdi : c.writes .rdi = false)
    (hsp : c.writes .rsp = false) (h : WP c s P F) :
    WP c s (fun s' ↦ P s' ∧ s'.reg .rdi = s.reg .rdi ∧ RegsFrame arrRegs s s' ∧
      ∀ a, (s'.mem a).isSome = (s.mem a).isSome) F :=
  WP.mono (WP.withDom (WP.withWrites h)) (fun _ ⟨⟨hp, hw⟩, hd⟩ ↦
    ⟨hp, hw _ hdi, regsFrame_arr hdi hsp hw, hd⟩) fun _ h ↦ h

/-! ## Words -/

theorem toE_eq_eOf (x : EW) : x.toE = eOf x.c0 x.c1 := rfl

theorem regs_of_eOf {a b : UInt64} {v : EW} (h : eOf a b = v.toE) : a = v.c0 ∧ b = v.c1 := by
  rw [toE_eq_eOf] at h
  exact eOf_inj.mp h

theorem EArr_of_EWArr {mem : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW}
    (h : EWArr mem p xs) : EArr mem p (xs.toList.map EW.toE) := EWArr_iff_EArr.mp h

theorem length_map_toE (xs : Array EW) : (xs.toList.map EW.toE).length = xs.size := by simp

theorem stackPoint_zero (z : Array EW) : stackPoint ⟨0, 0⟩ z 0 = z := by
  simp [stackPoint, selectorPoint]

theorem toList_map_stackPoint (pl : Placement) (pt : Array EW) (sl : Nat) :
    (stackPoint pl pt sl).toList.map EW.toE =
      pt.toList.map EW.toE ++ LeanVM.Protocol.Verifier.selectorPoint (pl.index >>> pl.variableCount)
        (sl - pl.variableCount) := by
  rw [stackPoint, Array.toList_append, List.map_append, Equiv.toList_map_selectorPoint]

theorem toList_map_extract (x : Array EW) (n : Nat) :
    (x.extract 0 n).toList.map EW.toE = (x.toList.map EW.toE).take n := by
  simp [Array.toList_extract, List.extract_eq_take_drop, List.map_take]

/-! ## `.eq` -/

theorem weightEq_writes : weightEq.writes .rdi = false ∧ weightEq.writes .rsp = false := by
  decide

/-- **A column claim's weight on the stack.** -/
theorem weightEq_spec {pt x : Array EW} {pl : Placement} {sl : Nat}
    (hpt : EWArr s.mem (s.reg .r13) pt) (hx : EWArr s.mem (s.reg .r14) x)
    (h15 : s.reg .r15 = pt.size.toUInt64) (hbp : s.reg .rbp = x.size.toUInt64)
    (hsi : s.reg .rsi = pl.index.toUInt64) (hdx : s.reg .rdx = pl.variableCount.toUInt64)
    (hcx : s.reg .rcx = sl.toUInt64) (hptl : pt.size < 2 ^ 32) (hxl : x.size < 2 ^ 32)
    (hidx : pl.index < 2 ^ 64) (hvc : pl.variableCount < 2 ^ 64) (hsl : sl < 2 ^ 64) :
    WP weightEq s (fun s' ↦
      s'.reg .r9 = (StackWeight.eval (.eq (stackPoint pl pt sl)) x).c0 ∧
      s'.reg .r10 = (StackWeight.eval (.eq (stackPoint pl pt sl)) x).c1 ∧ s'.mem = s.mem ∧
      s'.reg .rdi = s.reg .rdi ∧ RegsFrame arrRegs s s') F := by
  refine WP.mono (WP.frames weightEq_writes.1 weightEq_writes.2 (weightEq_specE (F := F)
    (EArr_of_EWArr hpt) (EArr_of_EWArr hx) (by rw [length_map_toE]; exact h15)
    (by rw [length_map_toE]; exact hbp) hsi hdx hcx (by rw [length_map_toE]; omega)
    (by rw [length_map_toE]; omega) hidx hvc hsl)) (fun s' ⟨⟨he, hm⟩, hdi, hf, _⟩ ↦ ?_)
    fun _ h ↦ h
  have hv : eOf (s'.reg .r9) (s'.reg .r10) = (StackWeight.eval (.eq (stackPoint pl pt sl)) x).toE := by
    rw [he, StackWeight.eval, Equiv.toE_eqEval, toList_map_stackPoint]
  obtain ⟨h9, h10⟩ := regs_of_eOf hv
  exact ⟨h9, h10, hm, hdi, hf⟩

/-! ## `.ring` -/

theorem weightRing_writes : weightRing.writes .rdi = false ∧ weightRing.writes .rsp = false := by
  decide

theorem ne_of_disj {b p : UInt64} {n : Nat} (hfb : Fits b bufWords) (hfp : Fits p n)
    (hd : Disj b bufWords p n) : ∀ k < bufWords, ∀ j < n, ew b k ≠ ew p j :=
  fun _ hk _ hj ↦ wd_ne_of_disj hfb hfp hd hk hj

/-- **The ring-switched claim's weight.** -/
theorem weightRing_spec {pl : Placement} {r c x : Array EW} {buf : UInt64}
    (hr : EWArr s.mem (s.reg .r13) r) (h15 : s.reg .r15 = r.size.toUInt64)
    (hrl : r.size ≤ pointCap)
    (hx : EWArr s.mem (s.reg .r14) x) (hbp : s.reg .rbp = x.size.toUInt64) (hxl : x.size < 2 ^ 32)
    (hc : EWArr s.mem (s.reg .r11) c) (h12 : s.reg .r12 = c.size.toUInt64) (hcl : c.size < 2 ^ 32)
    (hsi : s.reg .rsi = pl.index.toUInt64) (hdx : s.reg .rdx = pl.variableCount.toUInt64)
    (hidx : pl.index < 2 ^ 64) (hvc : pl.variableCount < 2 ^ 64)
    (hbx : s.reg .rbx = buf) (hfb : Fits buf bufWords)
    (hdom : ∀ k < bufWords, (s.mem (wd buf k)).isSome)
    (hfr : Fits (s.reg .r13) (2 * r.size)) (hfx : Fits (s.reg .r14) (2 * x.size))
    (hfc : Fits (s.reg .r11) (2 * c.size))
    (hdr : Disj buf bufWords (s.reg .r13) (2 * r.size))
    (hdx' : Disj buf bufWords (s.reg .r14) (2 * x.size))
    (hdc : Disj buf bufWords (s.reg .r11) (2 * c.size)) :
    WP weightRing s (fun s' ↦
      s'.reg .r9 = (StackWeight.eval (.ring pl r c) x).c0 ∧
      s'.reg .r10 = (StackWeight.eval (.ring pl r c) x).c1 ∧ s'.reg .rdi = s.reg .rdi ∧
      RegsFrame arrRegs s s' ∧ (∀ a, (∀ k < bufWords, a ≠ wd buf k) → s'.mem a = s.mem a) ∧
      ∀ a, (s'.mem a).isSome = (s.mem a).isSome) F := by
  obtain ⟨vc, idx⟩ := pl
  have hp : pointCap = 36 := by decide
  refine WP.mono (WP.frames weightRing_writes.1 weightRing_writes.2 (weightRing_specE (F := F)
    (R := r.toList.map EW.toE) (C := c.toList.map EW.toE) (X := x.toList.map EW.toE)
    hbx rfl (by rw [length_map_toE]; exact h15) rfl (by rw [length_map_toE]; exact hbp) rfl
    (by rw [length_map_toE]; exact h12) hsi hdx (EArr_of_EWArr hr) (EArr_of_EWArr hx)
    (EArr_of_EWArr hc) (by rw [length_map_toE]; omega) (by rw [length_map_toE]; omega)
    (by rw [length_map_toE]; omega) hvc hidx hdom
    (by rw [length_map_toE]; exact ne_of_disj hfb hfr hdr)
    (by rw [length_map_toE]; exact ne_of_disj hfb hfx hdx')
    (by rw [length_map_toE]; exact ne_of_disj hfb hfc hdc)))
    (fun s' ⟨⟨he, hm⟩, hdi, hf, hd⟩ ↦ ?_) fun _ h ↦ h
  have hv : eOf (s'.reg .r9) (s'.reg .r10) = (StackWeight.eval (.ring ⟨vc, idx⟩ r c) x).toE := by
    rw [he, StackWeight.eval, Equiv.EW.toE_mul, Equiv.toE_eqAbove, Equiv.toE_ringWeight,
      toList_map_extract]
  obtain ⟨h9, h10⟩ := regs_of_eOf hv
  exact ⟨h9, h10, hdi, hf, hm, hd⟩

end NativeVm.Code.Ring
