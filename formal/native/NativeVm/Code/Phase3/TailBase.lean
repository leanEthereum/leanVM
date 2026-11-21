module

public import NativeVm.Code.Phase3.Frame
public import NativeVm.Code.Phase3.LayoutSide
public import NativeVm.Code.Phase3.Split

/-!
# Phase 3 after the transcript: what its parts keep

`tlW`: the words `tailCode` writes (the bus, the claims, the fingerprints and totals, phase 3's
slots, the sides' selectors, the sums and temporaries), as literal regions. `TlIn`: the values read
before `tailCode` (the layout, the sides' placements, the depth, the GKR point, the weights, `β`,
the trees' values, the memory's limbs and counters, the share) at their words; a run writing only
`tlW` keeps them (`TlIn.keep`). `tl_ops_wrote`: a straight-line program writing slots of several
regions.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {s s' : QState}

/-- The words `tailCode` writes: `busR`, `claimsR`, the fingerprints and totals, `valsR`, the
three sides' selectors and padding weights, the sums and temporaries. -/
def tlW : List Region := [⟨622, 13471⟩, ⟨15569, 12161⟩, ⟨52860, 18⟩, ⟨52880, 46⟩,
  ⟨53182, 210⟩, ⟨53694, 210⟩, ⟨54206, 210⟩, ⟨54462, 30976⟩]

theorem tl_within : ∀ r ∈ tlW, ∃ q ∈ rs3, Within r q := by
  intro r hr
  simp only [tlW, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h1 := busR_off; have h2 := busR_size; have h3 := claimsR_off; have h4 := claimsR_size
  have h5 := scratchR_off; have h6 := scratchR_size
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨busR, by simp, by unfold Within Region.stop; simp only; omega⟩
  · exact ⟨claimsR, by simp, by unfold Within Region.stop; simp only; omega⟩
  all_goals exact ⟨scratchR, by simp, by unfold Within Region.stop; simp only; omega⟩

theorem tl_ok : ∀ r ∈ tlW, Ok3 r := fun r hr ↦ by
  obtain ⟨q, hq, hw⟩ := tl_within r hr
  simp only [rs3, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact .inl hw
  · exact .inr (.inl hw)
  · exact .inr (.inr hw)

theorem tl_stop : ∀ r ∈ tlW, r.stop ≤ 2 ^ 61 := by decide

/-- A run keeps the words apart from the regions it writes. -/
theorem tl_same {ws : List Region} (hw : Wrote env ws s s') {a n : Nat}
    (hc : ∀ r ∈ ws, a + n ≤ r.off ∨ r.stop ≤ a) (ha : a + n ≤ 2 ^ 61)
    (hws : ∀ r ∈ ws, r.stop ≤ 2 ^ 61) : Same s.mem s'.mem (wd env.work a) n := fun k hk ↦ by
  rw [wd_wd]
  exact hw.word (fun r hr ↦ by have := hc r hr; omega) (by omega) hws

theorem tl_ewat {ws : List Region} (hw : Wrote env ws s s') {a : Nat} {x : EW}
    (hc : ∀ r ∈ ws, a + 2 ≤ r.off ∨ r.stop ≤ a) (ha : a + 2 ≤ 2 ^ 61)
    (hws : ∀ r ∈ ws, r.stop ≤ 2 ^ 61) (h : EWAt s.mem (wd env.work a) x) :
    EWAt s'.mem (wd env.work a) x :=
  h.congr (tl_same hw hc ha hws)

theorem tl_ewarr {ws : List Region} (hw : Wrote env ws s s') {a n : Nat} {xs : Array EW}
    (hc : ∀ r ∈ ws, a + n ≤ r.off ∨ r.stop ≤ a) (ha : a + n ≤ 2 ^ 61)
    (hws : ∀ r ∈ ws, r.stop ≤ 2 ^ 61) (hn : 2 * xs.size ≤ n) (h : EWArr s.mem (wd env.work a) xs) :
    EWArr s'.mem (wd env.work a) xs :=
  h.congr (tl_same hw hc ha hws) hn

theorem tl_natAt {ws : List Region} (hw : Wrote env ws s s') {a m : Nat}
    (hc : ∀ r ∈ ws, a + 1 ≤ r.off ∨ r.stop ≤ a) (ha : a + 1 ≤ 2 ^ 61)
    (hws : ∀ r ∈ ws, r.stop ≤ 2 ^ 61) (h : NatAt s.mem (wd env.work a) m) :
    NatAt s'.mem (wd env.work a) m :=
  h.congr ((tl_same hw hc ha hws).base (by omega) rfl)

/-- A run writing regions inside `tlW` writes `tlW`. -/
theorem tl_widen {ws : List Region} (hw : Wrote env ws s s') (h : ∀ r ∈ ws, ∃ q ∈ tlW, Within r q) :
    Wrote env tlW s s' := hw.widen h

/-- A register set before a run. -/
theorem tl_pre {ws : List Region} {r : Reg64} {v : UInt64} (hw : Wrote env ws (s.setReg r v) s')
    (hr : r ≠ .rdi) : Wrote env ws s s' :=
  ((Wrote.refl env ws s).setReg hr v).trans hw

/-! ## The values read before -/

/-- **The values read before `tailCode`**, at their words. -/
structure TlIn (env : Env) (inp : Input) (layout : LayoutW) (rate : Nat)
    (point weights trees memory : Array EW) (beta mf bf share : EW) (s : QState) : Prop where
  rdi : s.reg .rdi = env.ctx
  wp : s.mem (wd env.ctx ctxWork) = some env.work
  hin : Inputs env inp s.mem
  lay : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate
  sides : SidesAt s.mem env.work layout
  depth : NatAt s.mem (wd env.work 52879) point.size
  pt : EWArr s.mem (wd env.work 52704) point
  w : EWArr s.mem (wd env.work 52670) weights
  beta : EWAt s.mem (wd env.work 52702) beta
  trees : EWArr s.mem (wd env.work 52832) trees
  mem : EWArr s.mem (wd env.work 52840) memory
  mf : EWAt s.mem (wd env.work 52844) mf
  bf : EWAt s.mem (wd env.work 52846) bf
  share : EWAt s.mem (wd env.work 52848) share

theorem tl_layoutAt : layoutR.at env.work = wd env.work 69 := by rw [Region.at, layoutR_off]

theorem tl_placeAt (side : Nat) : (placeR side).at env.work = wd env.work (52926 + 512 * side) := by
  rw [Region.at, placeR_off]

/-- **A run writing only `tlW` keeps the values read before.** -/
theorem TlIn.keep {layout : LayoutW} {rate : Nat} {point weights trees memory : Array EW}
    {beta mf bf share : EW} (h : TlIn env inp layout rate point weights trees memory beta mf bf share s)
    (hps : point.size < 64) (hws : weights.size = 16) (hts : trees.size = 3) (hms : memory.size = 2)
    (hw : Wrote env tlW s s') :
    TlIn env inp layout rate point weights trees memory beta mf bf share s' := by
  have hdl := dataEnd_le inp.bytecode.size
  have hde := dataEnd_eq
  refine ⟨hw.rdi.trans h.rdi, ?_, h.hin.step3 tl_ok hw.step h.rdi, ?_, ?_,
    tl_natAt hw (by decide) (by norm_num) tl_stop h.depth,
    tl_ewarr hw (n := 128) (by decide) (by norm_num) tl_stop (by omega) h.pt,
    tl_ewarr hw (n := 32) (by decide) (by norm_num) tl_stop (by omega) h.w,
    tl_ewat hw (by decide) (by norm_num) tl_stop h.beta,
    tl_ewarr hw (n := 6) (by decide) (by norm_num) tl_stop (by omega) h.trees,
    tl_ewarr hw (n := 4) (by decide) (by norm_num) tl_stop (by omega) h.mem,
    tl_ewat hw (by decide) (by norm_num) tl_stop h.mf,
    tl_ewat hw (by decide) (by norm_num) tl_stop h.bf,
    tl_ewat hw (by decide) (by norm_num) tl_stop h.share⟩
  · refine (hw.mem _ fun r hr ⟨k, hk, e⟩ ↦ ?_).trans h.wp
    have hb := (tl_ok r hr).bounds
    unfold Region.stop at hb
    exact h.hin.ctx_ne_work (by rw [ctxEnd_val]; decide) (by omega) e
  · have hs := tl_same hw (a := 69) (n := 490) (by decide) (by norm_num) tl_stop
    rw [← tl_layoutAt] at hs
    exact h.lay.congr (by rwa [show layoutWords = 490 by rw [layoutWords, columnCount_val]])
  · refine h.sides.congr fun side hs ↦ ?_
    rw [tl_placeAt, placeR_size]
    exact tl_same hw (by interval_cases side <;> decide) (by omega) tl_stop

/-! ## Straight-line programs over several regions -/

/-- **A straight-line program** writing slots of the regions `ws` only. -/
theorem tl_ops_wrote (l : List EOp) {S : List Nat} {v : Nat → EW} {ws : List Region}
    {E : QState → Prop} (hws : ∀ r ∈ ws, Ok3 r) (hi : Inputs env inp s.mem)
    (h14 : s.reg .r14 = env.work) (hS : Holds s.mem env.work S v)
    (hSe : ∀ k ∈ S, k % 2 = 0 ∧ k + 1 < 2 ^ 60) (hval : opsValid l S = true)
    (hde : ∀ d ∈ opsDsts l, d % 2 = 0 ∧ ∃ r ∈ ws, r.off ≤ d ∧ d + 2 ≤ r.stop) :
    WP (opsCode l) s (fun s' ↦ Holds s'.mem env.work (opsDsts l ++ S) (opsRun l v) ∧
      Wrote env ws s s' ∧ RegsFrame opRegs s s') E := by
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  have hde' := dataEnd_eq
  have hb : ∀ d ∈ opsDsts l, ∃ r ∈ ws, r.off ≤ d ∧ d + 2 ≤ r.stop ∧ r.stop ≤ dataEnd :=
    fun d hd ↦ by
      obtain ⟨-, r, hr, h1, h2⟩ := hde d hd
      exact ⟨r, hr, h1, h2, (hws r hr).bounds.2⟩
  refine WP.mono (ops_spec l (lim := 2 ^ 60) (by norm_num) h14 hS hSe hval
    (fun d hd ↦ ⟨(hde d hd).1, by obtain ⟨r, -, -, h2, h3⟩ := hb d hd; omega⟩)
    (fun d hd ↦ by
      obtain ⟨r, hr, h1, h2, -⟩ := hb d hd
      exact ⟨hi.ok3_some' (hws r hr) (by omega), hi.ok3_some' (hws r hr) (by omega)⟩)) ?_
    fun _ h ↦ h
  rintro s' ⟨hH, hk, hsome, hout, hf⟩
  refine ⟨hH, ⟨hf .rdi (by decide), fun a ha ↦ ?_, hsome⟩, hf⟩
  by_cases hw : ∃ k < 2 ^ 60, a = wd env.work k
  · obtain ⟨k, hk', rfl⟩ := hw
    refine hk k hk' fun d hd ↦ ?_
    obtain ⟨r, hr, h1, h2, -⟩ := hb d hd
    unfold Region.stop at h2
    constructor
    · intro e
      exact ha r hr ⟨k - r.off, by omega, by congr 1; omega⟩
    · intro e
      exact ha r hr ⟨k - r.off, by omega, by congr 1; omega⟩
  · exact hout a fun k hk' e ↦ hw ⟨k, hk', e⟩

end NativeVm.Code.P3
