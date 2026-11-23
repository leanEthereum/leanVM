module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Segs

/-!
# `verify_layer` on x86-64: the state after the first check

`AfterA`: at `b44` (code index `370`), after `checkA` passed: the body (memory changed in the
stack and the front's outputs `wFront`), the `TState` after the product's read, the product in
the frame at `472`, the frame's words the rest reads (`backWords`; the assembly's `x(%rsp)` is the
frame's `x + 24`).

Tools for the rest: the body's outputs weakened (`Body.mono`), a state at a pc (`at_pc`), a call
from the frame's `16` writing its stack and `X` (`Body.callX`, `ts_callX`, `frSame_callX`), a
leaf call (`leafX`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The frame's words the rest reads: the `TState`, the point's elements, the scratch, the claim,
the claim's bit weights, the point's `Buf`, the instance weights' `Buf`. -/
def backWords (m0 : MachineData) : List (Nat × UInt64) :=
  [(40, .ofBitVec (tA m0)), (64, .ofBitVec (cA m0 + 288#64)), (80, .ofBitVec (sA m0)),
    (96, .ofBitVec (cA m0)), (120, .ofBitVec (sA m0 + 25600#64)),
    (128, .ofBitVec (cA m0 + 280#64)), (224, .ofBitVec (cA m0 + 16#64))]

/-- **After the first check** (`b44`, code index `370`): the body, the `TState` `s1` after the
product's read, the product `p` at the frame's `472`, the frame's words `backWords`. -/
structure AfterA (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW) (s1 : TState)
    (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s1
  prod : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 472) p.toList
  psize : p.size = 47
  fw : FWs m0 d.dmem (backWords m0)

end

public section

variable {m0 : MachineData}

theorem backWords_in : ∀ q ∈ backWords m0, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232 := by
  intro q hq
  simp only [backWords, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

section bw
variable {d : DataMem} (h : FWs m0 d (backWords m0))
include h
theorem bw40 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 40) (.ofBitVec (tA m0)) :=
  h (40, (.ofBitVec (tA m0))) (List.mem_cons_self)
theorem bw64 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 64) (.ofBitVec (cA m0 + 288#64)) :=
  h (64, (.ofBitVec (cA m0 + 288#64))) (List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem bw80 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 80) (.ofBitVec (sA m0)) :=
  h (80, (.ofBitVec (sA m0))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem bw96 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 96) (.ofBitVec (cA m0)) :=
  h (96, (.ofBitVec (cA m0))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem bw120 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 120) (.ofBitVec (sA m0 + 25600#64)) :=
  h (120, (.ofBitVec (sA m0 + 25600#64))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem bw128 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 128) (.ofBitVec (cA m0 + 280#64)) :=
  h (128, (.ofBitVec (cA m0 + 280#64))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem bw224 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 224) (.ofBitVec (cA m0 + 16#64)) :=
  h (224, (.ofBitVec (cA m0 + 16#64))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
end bw

/-- The body with more outputs. -/
theorem Body.mono {W W' : BitVec 64 → Prop} (hW : ∀ q, W q → W' q) {o : Nat} {d : MachineData}
    (hb : Body m0 W o d) : Body m0 W' o d :=
  ⟨hb.fr, fun q hq ↦ hb.same q fun h ↦ hq (h.elim .inl fun h ↦ .inr (hW q h))⟩

/-- A state at its pc. -/
theorem at_pc [Host] {R : MachineState → Prop} {st : MachineState} {x : Int64} (hpc : st.pc = x)
    (h : Eventually (step1 Host.exe) R ⟨st.data, x⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  exact h

theorem ewArg_c0 {x y : BitVec 64} {e : EW} (h : ewArg x y = e) : x = e.c0.toBitVec := by
  rw [← h]; rfl

theorem ewArg_c1 {x y : BitVec 64} {e : EW} (h : ewArg x y = e) : y = e.c1.toBitVec := by
  rw [← h]; rfl

/-- `Changes` with no output: the stack only. -/
theorem changes_stk {m m' : MachineData} {n : Nat} (h : Changes m m' n 0 0) :
    SameOutside m.dmem m'.dmem (InRange (stackBelow m n) n) :=
  NativeRustcVm.SameOutside.mono h fun q hq ↦ hq.elim
    (fun h ↦ absurd h (by unfold InRange; omega)) id

/-- `Writes` with one region as two ranges. -/
theorem writes1 {m m' : MachineData} {n : Nat} {x : BitVec 64} {len : Nat}
    (h : Writes m m' n [⟨x, len⟩]) :
    SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m n) n q ∨ InRange x len q) :=
  NativeRustcVm.SameOutside.mono h fun q ⟨r, hr, hq⟩ ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl hq
    · exact .inr hq

theorem bk_ite [Labels] {env : Env} (b : SBool) (x y : Sym) :
    (Sym.ite b x y).eval env = if b.eval env then x.eval env else y.eval env := by
  rw [Sym.eval]

theorem bk_not [Labels] {env : Env} (b : SBool) : (SBool.not b).eval env = !b.eval env := by
  rw [SBool.eval]

/-- A slice holding `xs`. -/
theorem slice_of {m : MachineData} {a : BitVec 64} {n : BitVec 64} {xs : Array EW}
    (h : NativeRustcVm.EWsAt m.dmem a xs.toList) (hn : n.toNat = xs.size) : slice m a n = xs := by
  unfold slice
  rw [hn, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt h, Array.toArray_toList]

/-- Element `i` of `xs` at the frame's `o`, its words loaded. -/
theorem ewsLoad [Labels] {d : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {xs : Array EW} {o : Nat}
    (h : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) o) xs.toList) {i : Nat}
    (hi : i < xs.size) {o0 o1 : Nat} (h0 : o0 = o + 16 * i) (h1 : o1 = o + 16 * i + 8) :
    (envB m0 d ex vars ret).load 0 o0 8 = (xs.getD i 0).c0.toBitVec ∧
      (envB m0 d ex vars ret).load 0 o1 8 = (xs.getD i 0).c1.toBitVec := by
  have := h.getElem (i := i) (by rw [Array.length_toList]; exact hi)
  rw [NativeRustcVm.ewAt_iff, Array.getElem_toList] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  have hb0 : (envB m0 d ex vars ret).base 0 = stackBelow m0 2016 := rfl
  subst h0 h1
  constructor
  · apply load_of_wordAt
    rw [hb0, show stackBelow m0 2016 + BitVec.ofNat 64 (o + 16 * i) =
      off (stackBelow m0 2016) o + BitVec.ofNat 64 (16 * i) by unfold off; bv_omega]
    exact this.1
  · apply load_of_wordAt
    rw [hb0, show stackBelow m0 2016 + BitVec.ofNat 64 (o + 16 * i + 8) =
      off (stackBelow m0 2016) o + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8 by
        unfold off; bv_omega]
    exact this.2

theorem ews_extract {d : DataMem} {x : BitVec 64} {xs : Array EW} (n : Nat)
    (h : NativeRustcVm.EWsAt d x xs.toList) : NativeRustcVm.EWsAt d x (xs.extract 0 n).toList := by
  rw [Array.toList_extract]
  simpa [List.extract] using h.take n

theorem beq_tbv (x y : UInt64) : (x.toBitVec == y.toBitVec) = (x == y) := by
  by_cases e : x = y
  · subst e; simp
  · have : x.toBitVec ≠ y.toBitVec := fun h ↦ e (UInt64.toBitVec_inj.mp h)
    simp [e, this]

theorem ew_beq (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  cases x; cases y; rfl

/-- `EW::mul`'s result as an element. -/
theorem mulE {m m' : MachineData} (h : EWMulPost m m') :
    ewArg (reg m' .rax) (reg m' .rdx) =
      ewArg (reg m .rdi) (reg m .rsi) * ewArg (reg m .rdx) (reg m .rcx) := by
  rw [h.1, h.2.1, ewArg_ew]
  rfl

/-- **A `Buf<EW, N>` in the frame** kept with its bytes. -/
theorem FrSame.buf {d d' : DataMem} {o N : Nat} (h : FrSame m0 d d' o (8 + 16 * N))
    {xs : List EW} (hb : NativeRustcVm.BufEWAt d (off (stackBelow m0 2016) o) N xs) :
    NativeRustcVm.BufEWAt d' (off (stackBelow m0 2016) o) N xs := by
  refine ⟨hb.1, h.word hb.2.1 (by omega), ?_⟩
  have e : off (stackBelow m0 2016) o + 8#64 = off (stackBelow m0 2016) (o + 8) :=
    NativeRustcVm.Transcript.off_add _ _ _
  have h2 := hb.2.2
  rw [e] at h2 ⊢
  exact (h.sub (o' := o + 8) (n' := 16 * N) (by omega) (by omega)).ews h2 (by have := hb.1; omega)

/-- The back's words kept with the frame's bytes `[40, 48)`, `[64, 232)`. -/
theorem FWs.bw_of {d d' : DataMem} (h1 : FrSame m0 d d' 40 8) (h2 : FrSame m0 d d' 64 168)
    (hw : FWs m0 d (backWords m0)) : FWs m0 d' (backWords m0) := by
  intro q hq
  simp only [backWords, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1.word (bw40 hw) (by decide)
  · exact (h2.sub (o' := 64) (n' := 8) (by decide) (by decide)).word (bw64 hw) (by decide)
  · exact (h2.sub (o' := 80) (n' := 8) (by decide) (by decide)).word (bw80 hw) (by decide)
  · exact (h2.sub (o' := 96) (n' := 8) (by decide) (by decide)).word (bw96 hw) (by decide)
  · exact (h2.sub (o' := 120) (n' := 8) (by decide) (by decide)).word (bw120 hw) (by decide)
  · exact (h2.sub (o' := 128) (n' := 8) (by decide) (by decide)).word (bw128 hw) (by decide)
  · exact (h2.sub (o' := 224) (n' := 8) (by decide) (by decide)).word (bw224 hw) (by decide)

/-- The frame's words `L` kept with a range covering their offsets `os`. -/
theorem FWs.keepR {L : List (Nat × UInt64)} {os : List Nat} (hos : L.map Prod.fst = os)
    {d d' : DataMem} {lo n : Nat} (hf : FrSame m0 d d' lo n)
    (hb : os.all (fun o ↦ decide (lo ≤ o ∧ o + 8 ≤ lo + n)) = true) (h : FWs m0 d L) :
    FWs m0 d' L :=
  h.keepIn hf fun q hq ↦ by
    have := List.all_eq_true.mp hb q.1 (hos ▸ List.mem_map_of_mem hq)
    simpa using this

/-- A word written at the frame's `o` updates the words `L` (`o` replaced). -/
theorem FWs.set {L L' : List (Nat × UInt64)} {d : DataMem} (h : FWs m0 d L)
    (h' : ∀ p ∈ L', p ∈ L ∨ NativeRustcVm.WordAt d (off (stackBelow m0 2016) p.1) p.2) :
    FWs m0 d L' := fun p hp ↦ (h' p hp).elim (h p) id

/-- Membership in a literal list of frame words. -/
macro "fw_mem" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-- **A block keeps the frame's words** `L` at the offsets `os` its writes miss. -/
theorem FWs.blkO [Labels] {L : List (Nat × UInt64)} {os : List Nat} (hos : L.map Prod.fst = os)
    {d d' : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (envB m0 d ex vars ret).WF)
    (hm : Match (envB m0 d ex vars ret) S d') (hin : writesIn S = true)
    (hmiss : os.all (fun o ↦ decide (o + 8 ≤ 2024) && missB o 8 S) = true)
    (h : FWs m0 d.dmem L) : FWs m0 d'.dmem L := fun p hp ↦ by
  have := List.all_eq_true.mp hmiss p.1 (hos ▸ List.mem_map_of_mem hp)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact (frSame_blk hwf hm hin this.1 this.2).word (h p hp) (Nat.le_refl 8)

theorem bk_load4 [Labels] {env : Env} {r o : Nat} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) :
    env.load r o 4 = BitVec.ofNat 64 w.toNat := by
  have h4 : NativeRustcVm.BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o)
      ((NativeRustcVm.wordBytes w).take 4) := fun i hi ↦ by
    rw [List.length_take, NativeRustcVm.length_wordBytes] at hi
    have := h i (by rw [NativeRustcVm.length_wordBytes]; omega)
    rw [List.getElem_take]
    exact this
  rw [Env.load_of_bytesAt (n := 4) (by rw [List.length_take, NativeRustcVm.length_wordBytes]; rfl)
    h4]
  rcases hw with rfl | rfl <;> decide

theorem bk_load1 [Labels] {env : Env} {r o : Nat} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) :
    env.load r o 1 = BitVec.ofNat 64 w.toNat := by
  have h1 : NativeRustcVm.BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o)
      ((NativeRustcVm.wordBytes w).take 1) := fun i hi ↦ by
    rw [List.length_take, NativeRustcVm.length_wordBytes] at hi
    have := h i (by rw [NativeRustcVm.length_wordBytes]; omega)
    rw [List.getElem_take]
    exact this
  rw [Env.load_of_bytesAt (n := 1) (by rw [List.length_take, NativeRustcVm.length_wordBytes]; rfl)
    h1]
  rcases hw with rfl | rfl <;> decide

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **A call** from the frame's `16` writing its `Sk` bytes of stack and `X`, `X` in the outputs
or the frame from `24`: the body at `24`. -/
theorem Body.callX (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {mc d' : MachineData} (hb : Body m0 W 16 mc) (hsv : Saved mc d')
    (hrsp : rspOf d' = rspOf mc + 8#64) {Sk : Nat} (hSk : 2000 + Sk ≤ 3232)
    {X : BitVec 64 → Prop}
    (hso : SameOutside mc.dmem d'.dmem (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ X q))
    (hX : ∀ q, X q → W q ∨ InRange (off (stackBelow m0 2016) 24) 1944 q) : Body m0 W 24 d' :=
  Body.call (geo_of hpre) hWo hb (by decide) hsv hrsp (by omega) hso hX

/-- **The `TState` kept** by a call from the frame's `16` writing its stack and `X` apart from the
`TState` and its area. -/
theorem ts_callX (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {mc : MachineData} {d' : DataMem} (hb : Body m0 W 16 mc)
    (hk : Kept mc.dmem d') {Sk : Nat} (hSk : 2000 + Sk ≤ 3232) {X : BitVec 64 → Prop}
    (hso : SameOutside mc.dmem d' (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ X q))
    (hXt : ∀ q, X q → ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q)
    {s' : TState} (h : TStateAt mc.dmem (tA m0) a s') : TStateAt d' (tA m0) a s' :=
  h.frame hk (fun q hq ↦ hq.elim (fun hq ↦ (ctx hpre (F := 2000) (by decide)).stack_not_t
    ((ctx hpre (F := 2000) (by decide)).inRange_callee (hb.at_ hpre hWo (by decide)) hSk hq).1)
    (hXt q)) hso

omit [Labels] in
/-- Frame bytes outside `[o, o + n)` are not in it. -/
theorem fr_miss (g : Geo m0) {o n j m : Nat} (hjm : j + m ≤ 2024) (hon : o + n ≤ 2024)
    (hd : j + m ≤ o ∨ o + n ≤ j) {q : BitVec 64} (hq : InRange (off (stackBelow m0 2016) o) n q) :
    ¬InRange (off (stackBelow m0 2016) j) m q := by
  have := g.top; have := g.hN
  by_cases hn : n = 0
  · subst hn; unfold InRange at hq; omega
  by_cases hm : m = 0
  · subst hm; unfold InRange; omega
  intro h'
  rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off, g.fa (by omega)] at hq
  rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off, g.fa (by omega)] at h'
  omega

/-- **A call writing the `TState`** keeps the frame's bytes from `24`. -/
theorem frSame_ts (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {mc : MachineData}
    {d' : DataMem} (hb : Body m0 W 16 mc) {Sk : Nat} (hSk : 2000 + Sk ≤ 3232)
    (hso : SameOutside mc.dmem d'
      (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ InRange (tA m0) tstateBytes q)) :
    FrSame m0 mc.dmem d' 24 2000 :=
  frSame_call (geo_of hpre) hb (by omega) hso (by decide) (by decide) fun q hq hq' ↦
    (frame_not_t hpre (fr_in (geo_of hpre) (by decide) hq')).1 hq

/-- **A range of the frame from `24`** for a callee from the frame's `16` using `Sk` bytes of
stack: mapped, not wrapping, apart from the callee's stack, the `TState`, the round constants. -/
theorem frArea (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {d : MachineData} (hb : Body m0 W 16 d) {Sk : Nat}
    (hSk : 2000 + Sk ≤ 3232) {o n : Nat} (ho : 24 ≤ o) (hon : o + n ≤ 2016) :
    OutOk d (tA m0) a (off (stackBelow m0 2016) o) n Sk := by
  have := (ctx hpre (F := 2000) (by decide)).outOk_frame (hb.at_ hpre hWo (by decide)) hSk
    (o := o - 16) (n := n) (by omega) (by omega)
  rwa [off_fr, show o - 16 + 16 = o by omega] at this

/-- **A range of the scratch**: mapped, not wrapping. -/
theorem scrOk (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {oo : Nat}
    {d : MachineData} (hb : Body m0 W oo d) {o n : Nat} (ho : o < 205824) (h : o + n ≤ 205824) :
    NativeRustcVm.Mapped d.dmem (sA m0 + BitVec.ofNat 64 o) n ∧
      NativeRustcVm.NoWrap (sA m0 + BitVec.ofNat 64 o) n := by
  have g := geo_of hpre
  have hok := areas_ok (pre_areas hpre) (r := ⟨sA m0, 205824⟩) (.inl (by simp))
  have := g.hs
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [NativeRustcVm.addr_add_add]
    exact hb.fr.kept _ (hok.1 _ (by dsimp only; omega))
  · unfold NativeRustcVm.NoWrap
    rw [g.sa (by omega)]
    omega

/-- A range of the scratch is apart from the frame's bytes. -/
theorem scr_not_fr (hpre : VerifyLayerPre a s c m0) {o n : Nat} (h : o + n ≤ 205824)
    {q : BitVec 64} (hq : InRange (sA m0 + BitVec.ofNat 64 o) n q) {j m : Nat}
    (hjm : j + m ≤ 2024) : ¬InRange (off (stackBelow m0 2016) j) m q := by
  have g := geo_of hpre
  have := g.hs; have := g.hss; have := g.hN; have := g.top
  by_cases hn : n = 0
  · subst hn; unfold InRange at hq; omega
  by_cases hm : m = 0
  · subst hm; unfold InRange; omega
  intro h'
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at hq
  rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off, g.fa (by omega)] at h'
  omega

/-- A range of the scratch misses the `TState` and its decoded area. -/
theorem scr_not_t (hpre : VerifyLayerPre a s c m0) {o n : Nat} (h : o + n ≤ 205824)
    {q : BitVec 64} (hq : InRange (sA m0 + BitVec.ofNat 64 o) n q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have g := geo_of hpre
  have := g.hs; have := g.ht; have := g.htsc
  have h0 := pre_apart hpre (w := ⟨sA m0, 205824⟩) (by simp) (r := a.region) (by simp)
  have hok := (pre_rok hpre (r := a.region) (by simp)).2
  simp only [NativeRustcVm.Transcript.DecArea.region] at h0 hok
  unfold NativeRustcVm.NoWrap at hok
  by_cases hn : n = 0
  · subst hn; unfold InRange at hq; omega
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at hq
  constructor
  · intro h'; rw [Sym.inRange_iff (by unfold tstateBytes; omega)] at h'
    unfold tstateBytes at h'; omega
  · intro h'; rw [Sym.inRange_iff hok] at h'; omega

/-- A range of the scratch's front part is an output of the front. -/
theorem scr_wFront (hpre : VerifyLayerPre a s c m0) {o n : Nat} (h1 : 51200 ≤ o)
    (h2 : o + n ≤ 140288) {q : BitVec 64} (hq : InRange (sA m0 + BitVec.ofNat 64 o) n q) :
    wFront m0 q := by
  have g := geo_of hpre
  have := g.hs
  by_cases hn : n = 0
  · subst hn; unfold InRange at hq; omega
  right
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at hq
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)]
  omega

/-- **The scratch's bytes kept by a block** writing the frame only. -/
theorem scr_blk0 (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d ex vars ret).WF) (hm : Match (envB m0 d ex vars ret) S d')
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true) {o : Nat}
    {bs : List UInt8} (ho : o < 205824) (hl : o + bs.length ≤ 205824)
    (h : NativeRustcVm.BytesAt d.dmem (sA m0 + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d'.dmem (sA m0 + BitVec.ofNat 64 o) bs :=
  h.of_sameOutside (hm.sameOutside hwf) fun i hi hw ↦ by
    have h1 := written0 (geo_of hpre) h0 hbr hw
    rw [← NativeRustcVm.Transcript.off_zero (stackBelow m0 2016)] at h1
    exact scr_not_fr hpre (o := o) (n := bs.length) hl
      (NativeRustcVm.Transcript.inRange_off_self hi (by omega)) (j := 0) (m := 2016) (by decide) h1

/-- **The scratch's elements kept by a block** writing the frame only. -/
theorem scr_blk0E (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d ex vars ret).WF) (hm : Match (envB m0 d ex vars ret) S d')
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true) {o : Nat}
    {xs : List EW} (ho : o < 205824) (hl : o + 16 * xs.length ≤ 205824)
    (h : NativeRustcVm.EWsAt d.dmem (sA m0 + BitVec.ofNat 64 o) xs) :
    NativeRustcVm.EWsAt d'.dmem (sA m0 + BitVec.ofNat 64 o) xs :=
  scr_blk0 hpre hwf hm h0 hbr ho (by rw [NativeRustcVm.length_ewsBytes]; exact hl) h

/-- **The scratch's elements kept by a call** from the frame's `16` writing its stack and `X`
apart from them. -/
theorem scr_call (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {mc : MachineData} {d' : DataMem} (hb : Body m0 W 16 mc)
    {Sk : Nat} (hSk : 2000 + Sk ≤ 3232) {X : BitVec 64 → Prop}
    (hso : SameOutside mc.dmem d' (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ X q))
    {o : Nat} {xs : List EW} (ho : o < 205824) (hl : o + 16 * xs.length ≤ 205824)
    (hX : ∀ q, X q → ¬InRange (sA m0 + BitVec.ofNat 64 o) (16 * xs.length) q)
    (h : NativeRustcVm.EWsAt mc.dmem (sA m0 + BitVec.ofNat 64 o) xs) :
    NativeRustcVm.EWsAt d' (sA m0 + BitVec.ofNat 64 o) xs := by
  have g := geo_of hpre
  refine NativeRustcVm.BytesAt.of_sameOutside h hso fun i hi hq ↦ ?_
  rw [NativeRustcVm.length_ewsBytes] at hi
  have hin : InRange (sA m0 + BitVec.ofNat 64 o) (16 * xs.length)
      (sA m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    NativeRustcVm.Transcript.inRange_off_self hi (by omega)
  rcases hq with hq | hq
  · have hcc := (ctx hpre (F := 2000) (by decide)).inRange_callee (hb.at_ hpre hWo (by decide)) hSk hq
    have hs := g.hss; have := g.hs; have hsb := g.sbN; have := g.hN; have := g.top
    have h1 : InRange (stackBelow m0 3232) 3232 (sA m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
      hcc.1
    have e : (sA m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i).toNat = (sA m0).toNat + o + i := by
      rw [NativeRustcVm.addr_add_add, g.sa (by omega)]; omega
    rw [Sym.inRange_iff (by omega), hsb, e] at h1
    omega
  · exact hX _ hq hin

/-- **A range of the scratch** for a callee from the frame's `16` using `Sk` bytes of stack:
mapped, not wrapping, apart from the callee's stack and return address. -/
theorem scrArea (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {d : MachineData} (hb : Body m0 W 16 d) {Sk : Nat}
    (hSk : 2000 + Sk ≤ 3232) {o n : Nat} (ho : o < 205824) (h : o + n ≤ 205824) :
    NativeRustcVm.Mapped d.dmem (sA m0 + BitVec.ofNat 64 o) n ∧
      NativeRustcVm.NoWrap (sA m0 + BitVec.ofNat 64 o) n ∧
      NativeRustcVm.Apart (sA m0 + BitVec.ofNat 64 o) n (stackBelow d Sk) (Sk + 8) := by
  have g := geo_of hpre
  have hap := areas_stack (pre_areas hpre) (w := ⟨sA m0, 205824⟩) (by simp)
  refine ⟨(scrOk hpre hb ho h).1, (scrOk hpre hb ho h).2, ?_⟩
  refine (ctx hpre (F := 2000) (by decide)).apart (hb.at_ hpre hWo (by decide)) hSk ?_
  have := g.hs
  unfold NativeRustcVm.Apart at hap ⊢
  dsimp only at hap
  rw [g.sa (by omega)]
  omega

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **A leaf call** from the frame's `16` (its stack changed only): the body at `24`, the frame's
bytes from `24` and the `TState` kept. -/
theorem leafX (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {Sk : Nat} (hSk : 2000 + Sk ≤ 3232)
    (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' → SameOutside m.dmem m'.dmem (InRange (stackBelow m Sk) Sk) ∧ Saved m m')
    {env : Env} {next : Int64} {st : MachineState} (hpc : PcOk env (.call l) next st)
    (hb : Body m0 W 16 st.data) (hP : P st.data) {R : MachineState → Prop}
    (cont : ∀ d', Q st.data d' → Body m0 W 24 d' → FrSame m0 st.data.dmem d'.dmem 24 2000 →
      (∀ s', TStateAt st.data.dmem (tA m0) a s' → TStateAt d'.dmem (tA m0) a s') →
      (∀ r, calleeSaved r = true → reg d' r = reg st.data r) →
      SameOutside st.data.dmem d'.dmem (InRange (stackBelow st.data Sk) Sk) →
      Eventually (step1 Host.exe) R ⟨d', next⟩) :
    Eventually (step1 Host.exe) R st :=
  call_then hpc hspec hP fun st' hpc' hrsp hq ↦ by
    obtain ⟨hso, hsv⟩ := hQ _ _ hq
    obtain ⟨hb', hfr, hts⟩ := Body.leaf hpre hWo hb hSk hsv hrsp hso
    exact at_pc hpc' (cont st'.data hq hb' hfr hts hsv.1 hso)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
