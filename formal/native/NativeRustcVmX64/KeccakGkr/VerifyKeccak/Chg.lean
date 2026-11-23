module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Base

/-!
# Changes of memory as lists of ranges (x86-64)

`Chg m0 d d' L O`: memory `d'` is `d` but in the stack below `verify_keccak`'s frame, in the frame
ranges `L` (offset, length) and in the ranges `O` (region `1` to `4`, offset, length) of the
regions it writes (`ob`, `rsz`). A block changes the frame ranges it writes (`chg_block`), a call
the frame below its RSP and its outputs (`chg_call`); changes compose (`Chg.trans`). Bytes a change
misses stay (`Chg.frame`, `Chg.regS`), the checks on the lists by `decide` (`okL`, `okO`, `missL`,
`missO`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeVm.Model
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

@[expose] public section

/-- Region `i`'s base (`1` to `4`: the `TState`, the scratch, the claims, the `KeccakOutW`). -/
def ob [Labels] (m0 : MachineData) : Nat → BitVec 64
  | 1 => reg m0 .rdi
  | 2 => reg m0 .r9
  | 3 => keccakClaims m0
  | 4 => keccakOutArg m0
  | _ => 0

/-- Region `i`'s size. -/
def rsz : Nat → Nat
  | 1 => 760
  | 2 => 205824
  | 3 => 97288
  | 4 => 1608
  | _ => 0

/-- The bytes a change may touch. -/
def ChgR [Labels] (m0 : MachineData) (L : List (Nat × Nat)) (O : List (Nat × Nat × Nat))
    (q : BitVec 64) : Prop :=
  InRange (stackBelow m0 verifyKeccakStack) (verifyKeccakStack - 3344) q ∨
    (∃ p ∈ L, InRange (off (fb m0) p.1) p.2 q) ∨
    (∃ o ∈ O, InRange (off (ob m0 o.1) o.2.1) o.2.2 q)

/-- **A change**: `d'` is `d` outside `ChgR m0 L O`. -/
def Chg [Labels] (m0 : MachineData) (d d' : DataMem) (L : List (Nat × Nat))
    (O : List (Nat × Nat × Nat)) : Prop :=
  SameOutside d d' (ChgR m0 L O)

/-- The frame ranges are in the frame. -/
def okL (L : List (Nat × Nat)) : Bool := L.all fun p ↦ decide (p.1 + p.2 ≤ 3344)

/-- The region ranges are in their regions. -/
def okO (O : List (Nat × Nat × Nat)) : Bool :=
  O.all fun o ↦ decide (1 ≤ o.1 ∧ o.1 ≤ 4 ∧ o.2.1 + o.2.2 ≤ rsz o.1 ∧ 0 < o.2.2)

/-- The frame range `o`, `n` misses `L`. -/
def missL (L : List (Nat × Nat)) (o n : Nat) : Bool :=
  L.all fun p ↦ decide (p.1 + p.2 ≤ o ∨ o + n ≤ p.1)

/-- The range `o`, `n` of region `i` misses `O`. -/
def missO (O : List (Nat × Nat × Nat)) (i o n : Nat) : Bool :=
  O.all fun p ↦ decide (p.1 ≠ i ∨ p.2.1 + p.2.2 ≤ o ∨ o + n ≤ p.2.1)

/-- The regions `O` names are written. -/
def wrO (wr : Nat → Bool) (O : List (Nat × Nat × Nat)) : Bool := O.all fun o ↦ wr o.1

/-- A template's words: in the frame from `oc`, missing `L`. -/
def tplMiss (oc : Nat) (L : List (Nat × Nat)) (T : SState) : Bool :=
  T.mem.all fun w ↦ w.r == 0 && decide (oc ≤ w.off) && decide (w.off + w.n ≤ 3344) &&
    missL L w.off w.n

/-- A block's writes as frame ranges. -/
def wsL (S : SState) : List (Nat × Nat) := S.mem.map fun w ↦ (w.off, w.n)

end

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

omit [Labels] in
theorem okL_mem {L : List (Nat × Nat)} (h : okL L = true) {p : Nat × Nat} (hp : p ∈ L) :
    p.1 + p.2 ≤ 3344 := by
  have := List.all_eq_true.mp h p hp
  simpa using this

omit [Labels] in
theorem okO_mem {O : List (Nat × Nat × Nat)} (h : okO O = true) {o : Nat × Nat × Nat}
    (ho : o ∈ O) : 1 ≤ o.1 ∧ o.1 ≤ 4 ∧ o.2.1 + o.2.2 ≤ rsz o.1 ∧ 0 < o.2.2 := by
  have := List.all_eq_true.mp h o ho
  simpa using this

omit [Labels] in
theorem missL_mem {L : List (Nat × Nat)} {o n : Nat} (h : missL L o n = true) {p : Nat × Nat}
    (hp : p ∈ L) : p.1 + p.2 ≤ o ∨ o + n ≤ p.1 := by
  have := List.all_eq_true.mp h p hp
  simpa using this

omit [Labels] in
theorem missO_mem {O : List (Nat × Nat × Nat)} {i o n : Nat} (h : missO O i o n = true)
    {p : Nat × Nat × Nat} (hp : p ∈ O) : p.1 ≠ i ∨ p.2.1 + p.2.2 ≤ o ∨ o + n ≤ p.2.1 := by
  have := List.all_eq_true.mp h p hp
  simpa using this

/-- The frame's base as a number. -/
theorem fb_toNat (c : Ctx a inst m0) : (fb m0).toNat = (rspOf m0).toNat - 3344 :=
  stackBelow_toNat (by have := c.sp; have := vk_eq; omega)

/-- Frame offset `o` as a number. -/
theorem off_fb (c : Ctx a inst m0) {o : Nat} (ho : o < 3368) :
    (off (fb m0) o).toNat = (rspOf m0).toNat - 3344 + o := by
  have h := fb_toNat c
  have := c.sp
  have := c.top
  have := vk_eq
  rw [toNat_add_ofNat _ _ (by omega), h]

theorem ob_W (c : Ctx a inst m0) {i : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    (ob m0 i).toNat + rsz i ≤ 2 ^ 64 := by
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact c.tW
  · exact c.sW
  · exact c.cW
  · exact c.oW

/-- A region is apart from the stack with the return address and from the stack arguments. -/
theorem ob_S (c : Ctx a inst m0) {i : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    (ob m0 i).toNat + rsz i ≤ (rspOf m0).toNat - verifyKeccakStack ∨
      (rspOf m0).toNat + 24 ≤ (ob m0 i).toNat := by
  have hK := c.K
  have har := c.ar
  have := c.sp
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · have := c.tS; have := c.tar; simp only [ob, rsz]; unfold Sep at *; omega
  · have := c.sS; have := c.sar; simp only [ob, rsz]; unfold Sep at *; omega
  · have := c.cS; have := c.car; simp only [ob, rsz]; unfold Sep at *; omega
  · have := c.oS; have := c.oar; simp only [ob, rsz]; unfold Sep at *; omega

/-- Two regions are apart. -/
theorem ob_sep (c : Ctx a inst m0) {i j : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (h1' : 1 ≤ j) (h4' : j ≤ 4)
    (hij : i ≠ j) : Sep (ob m0 i).toNat (rsz i) (ob m0 j).toNat (rsz j) := by
  have ts := c.ts; have tc := c.tc; have tou := c.tou; have sc := c.sc; have so := c.so
  have co := c.co
  unfold Sep at *
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
  simp only [ob, rsz] <;> omega

/-- **A change as numbers.** -/
theorem ChgR.nat (c : Ctx a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    (hL : okL L = true) (hO : okO O = true) {q : BitVec 64} (h : ChgR m0 L O q) :
    ((rspOf m0).toNat - verifyKeccakStack ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 3344) ∨
      (∃ p ∈ L, (rspOf m0).toNat - 3344 + p.1 ≤ q.toNat ∧
        q.toNat < (rspOf m0).toNat - 3344 + p.1 + p.2) ∨
      (∃ o ∈ O, (ob m0 o.1).toNat + o.2.1 ≤ q.toNat ∧
        q.toNat < (ob m0 o.1).toNat + o.2.1 + o.2.2) := by
  have hK := c.K
  have := c.sp
  have := c.top
  have := vk_eq
  rcases h with h | ⟨p, hp, h⟩ | ⟨o, ho, h⟩
  · rw [NativeRustcX64.Sym.inRange_iff (by omega), hK] at h
    exact .inl (by omega)
  · have := okL_mem hL hp
    have e := off_fb c (o := p.1) (by omega)
    rw [NativeRustcX64.Sym.inRange_iff (by rw [e]; omega), e] at h
    exact .inr (.inl ⟨p, hp, by omega⟩)
  · obtain ⟨h1, h4, hs, hp0⟩ := okO_mem hO ho
    have hw := ob_W c h1 h4
    have e : (off (ob m0 o.1) o.2.1).toNat = (ob m0 o.1).toNat + o.2.1 :=
      toNat_add_ofNat _ _ (by omega)
    rw [NativeRustcX64.Sym.inRange_iff (by rw [e]; omega), e] at h
    exact .inr (.inr ⟨o, ho, by omega⟩)

theorem Chg.nil (d : DataMem) : Chg m0 d d [] [] := fun _ _ ↦ rfl

theorem Chg.trans {d1 d2 d3 : DataMem} {L L' : List (Nat × Nat)} {O O' : List (Nat × Nat × Nat)}
    (h : Chg m0 d1 d2 L O) (h' : Chg m0 d2 d3 L' O') : Chg m0 d1 d3 (L ++ L') (O ++ O') := by
  intro q hq
  have h1 : ¬ChgR m0 L O q := fun hc ↦ hq (by
    rcases hc with hc | ⟨p, hp, hc⟩ | ⟨o, ho, hc⟩
    · exact .inl hc
    · exact .inr (.inl ⟨p, List.mem_append_left _ hp, hc⟩)
    · exact .inr (.inr ⟨o, List.mem_append_left _ ho, hc⟩))
  have h2 : ¬ChgR m0 L' O' q := fun hc ↦ hq (by
    rcases hc with hc | ⟨p, hp, hc⟩ | ⟨o, ho, hc⟩
    · exact .inl hc
    · exact .inr (.inl ⟨p, List.mem_append_right _ hp, hc⟩)
    · exact .inr (.inr ⟨o, List.mem_append_right _ ho, hc⟩))
  rw [h' q h2, h q h1]

/-- **Frame bytes a change misses** stay. -/
theorem Chg.frame (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {o n : Nat} (hm : missL L o n = true) (hon : o + n ≤ 3368) :
    NativeRustcVm.Layout.Same d d' (off (fb m0) o) n := by
  intro j hj
  refine h _ fun hc ↦ ?_
  have e := off_fb c (o := o + j) (by omega)
  rw [NativeRustcVm.Transcript.off_add] at hc
  rcases ChgR.nat c hL hO hc with hc | ⟨p, hp, hc⟩ | ⟨r, hr, hc⟩
  · rw [e] at hc; omega
  · have := missL_mem hm hp
    rw [e] at hc; omega
  · obtain ⟨h1, h4, hs, -⟩ := okO_mem hO hr
    have := ob_S c h1 h4
    have := vk_eq
    have := c.sp
    rw [e] at hc; omega

/-- **Region bytes a change misses** stay. -/
theorem Chg.regS (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hm : missO O i o n = true) (hon : o + n ≤ rsz i) :
    NativeRustcVm.Layout.Same d d' (off (ob m0 i) o) n := by
  intro j hj
  refine h _ fun hc ↦ ?_
  have hw := ob_W c h1 h4
  have e : (off (ob m0 i) (o + j)).toNat = (ob m0 i).toNat + (o + j) :=
    toNat_add_ofNat _ _ (by omega)
  rw [NativeRustcVm.Transcript.off_add] at hc
  have hS := ob_S c h1 h4
  have := vk_eq
  have := c.sp
  rcases ChgR.nat c hL hO hc with hc | ⟨p, hp, hc⟩ | ⟨r, hr, hc⟩
  · rw [e] at hc; omega
  · have := okL_mem hL hp
    rw [e] at hc; omega
  · obtain ⟨h1', h4', hs, -⟩ := okO_mem hO hr
    have hmr := missO_mem hm hr
    rw [e] at hc
    obtain ⟨ri, ro, rn⟩ := r
    simp only at h1' h4' hs hc hmr
    by_cases hij : ri = i
    · subst hij
      omega
    · have := ob_sep c h1 h4 h1' h4' (Ne.symm hij)
      unfold Sep at this
      omega

/-- **A change is in the stack or the written regions.** -/
theorem ChgR.wo (c : Ctx a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    (hL : okL L = true) (hO : okO O = true) {wr : Nat → Bool} (hw : wrO wr O = true)
    {q : BitVec 64} (h : ChgR m0 L O q) :
    InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨ outsOf (rsOf m0) wr q := by
  have hK := c.K
  have := c.sp
  have := c.top
  have := vk_eq
  rcases ChgR.nat c hL hO h with hc | ⟨p, hp, hc⟩ | ⟨o, ho, hc⟩
  · exact .inl (by rw [NativeRustcX64.Sym.inRange_iff (by omega), hK]; omega)
  · have := okL_mem hL hp
    exact .inl (by rw [NativeRustcX64.Sym.inRange_iff (by omega), hK]; omega)
  · right
    obtain ⟨h1, h4, hs, -⟩ := okO_mem hO ho
    have hwr : wr o.1 = true := List.all_eq_true.mp hw o ho
    have hW := ob_W c h1 h4
    refine ⟨o.1 - 1, (ob m0 o.1, rsz o.1), by rw [show o.1 - 1 + 1 = o.1 by omega]; exact hwr,
      ?_, by rw [NativeRustcX64.Sym.inRange_iff hW]; omega⟩
    rcases (by omega : o.1 = 1 ∨ o.1 = 2 ∨ o.1 = 3 ∨ o.1 = 4) with h | h | h | h <;>
      rw [h] <;> rfl

/-- **A template's words miss a change.** -/
theorem ChgR.wt (c : Ctx a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    (hL : okL L = true) (hO : okO O = true) {oc : Nat} {T : SState} (ht : tplMiss oc L T = true)
    {j : Nat} {v : Sym} {t : Nat} (hf : findWrite 0 j T.mem = some (v, t)) :
    oc ≤ j ∧ ¬ChgR m0 L O (stackBelow m0 3344 + BitVec.ofNat 64 j) := by
  obtain ⟨w, hw, -, h1, h2, -, -⟩ := findWrite_spec hf
  have hok := List.all_eq_true.mp ht w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, ho⟩, hn⟩, hm⟩ := hok
  refine ⟨by omega, fun hc ↦ ?_⟩
  have e := off_fb c (o := j) (by omega)
  have hc' := ChgR.nat c hL hO hc
  change (off (fb m0) j).toNat = _ at e
  have := vk_eq
  have := c.sp
  rcases hc' with hc | ⟨p, hp, hc⟩ | ⟨r, hr, hc⟩
  · rw [show stackBelow m0 3344 + BitVec.ofNat 64 j = off (fb m0) j from rfl, e] at hc; omega
  · have := missL_mem hm hp
    rw [show stackBelow m0 3344 + BitVec.ofNat 64 j = off (fb m0) j from rfl, e] at hc; omega
  · obtain ⟨h1', h4', hs, -⟩ := okO_mem hO hr
    have := ob_S c h1' h4'
    rw [show stackBelow m0 3344 + BitVec.ofNat 64 j = off (fb m0) j from rfl, e] at hc; omega

/-- **A block's change**: the frame ranges it writes. -/
theorem chg_block (c : Ctx a inst m0) {m m' : MachineData} {vals : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {srcRs : List (BitVec 64 × Nat)}
    (hm : Match (envZ m0 m 3344 3368 srcRs vals ret) S m')
    (hwf : (envZ m0 m 3344 3368 srcRs vals ret).WF) {wr : Nat → Bool}
    (hw : S.mem.all (writeOk 3344 (3368 :: (rsOf m0).map Prod.snd) wr) = true)
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) :
    Chg m0 m.dmem m'.dmem (wsL S) [] := by
  intro q hq
  refine hm.get?_mem0 hwf fun hW ↦ hq ?_
  obtain ⟨w, hwm, b, sz, hb, h1, h2⟩ := hW
  have hr : w.r = 0 := by simpa using List.all_eq_true.mp h0 w hwm
  have hok := List.all_eq_true.mp hw w hwm
  simp only [writeOk, hr, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    bne_iff_ne, ne_eq, not_true_eq_false, false_and, or_false, true_and] at hok
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  refine .inr (.inl ⟨(w.off, w.n), List.mem_map.mpr ⟨w, hwm, rfl⟩, ?_⟩)
  have e := off_fb c (o := w.off) (by omega)
  have hfb := fb_toNat c
  have := c.sp
  have := c.top
  have := vk_eq
  have hfb' : (stackBelow m0 3344).toNat = (rspOf m0).toNat - 3344 := hfb
  have e' : (stackBelow m0 3344 + BitVec.ofNat 64 w.off).toNat = (rspOf m0).toNat - 3344 + w.off := e
  show InRange (stackBelow m0 3344 + BitVec.ofNat 64 w.off) w.n q
  rw [NativeRustcX64.Sym.inRange_iff (by rw [e']; omega), e']
  change (stackBelow m0 3344).toNat + w.off ≤ q.toNat at h1
  change q.toNat < (stackBelow m0 3344).toNat + w.off + w.n at h2
  constructor <;> omega

/-- **A call's change**: the frame below its RSP (at the frame's offset `oc`), its outputs. -/
theorem chg_call (c : Ctx a inst m0) {mc m' : MachineData} {oc Sk : Nat}
    (hrsp : rspOf mc = stackBelow m0 (3344 - oc)) (hoc : oc ≤ 3344)
    (hS : 3344 - oc + Sk ≤ verifyKeccakStack) {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)}
    (hso : SameOutside mc.dmem m'.dmem
      (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ ChgR m0 L O q)) :
    Chg m0 mc.dmem m'.dmem ((0, oc) :: L) O := by
  intro q hq
  refine hso q fun h ↦ hq ?_
  rcases h with h | h
  · have hK := c.K
    have := c.sp
    have := c.top
    have := vk_eq
    have hb : (stackBelow m0 (3344 - oc)).toNat = (rspOf m0).toNat - (3344 - oc) :=
      stackBelow_toNat (by omega)
    have hmb : (stackBelow mc Sk).toNat = (rspOf m0).toNat - (3344 - oc) - Sk := by
      rw [stackBelow_toNat (by rw [hrsp, hb]; omega), hrsp, hb]
    rw [NativeRustcX64.Sym.inRange_iff (by rw [hmb]; omega), hmb] at h
    by_cases hq' : q.toNat < (rspOf m0).toNat - 3344
    · exact .inl (by rw [NativeRustcX64.Sym.inRange_iff (by omega), hK]; omega)
    · refine .inr (.inl ⟨(0, oc), List.mem_cons_self, ?_⟩)
      have e := off_fb c (o := 0) (by omega)
      show InRange (off (fb m0) 0) oc q
      rw [NativeRustcX64.Sym.inRange_iff (by rw [e]; omega), e]
      omega
  · rcases h with h | ⟨p, hp, h⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨p, List.mem_cons_of_mem _ hp, h⟩)
    · exact .inr (.inr h)

/-- A frame output of a callee is a change. -/
theorem chgR_frame {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {o n : Nat}
    (hp : (o, n) ∈ L) {q : BitVec 64} (h : InRange (off (fb m0) o) n q) : ChgR m0 L O q :=
  .inr (.inl ⟨(o, n), hp, h⟩)

/-- A region output of a callee is a change. -/
theorem chgR_reg {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {i o n : Nat}
    (hp : (i, o, n) ∈ O) {q : BitVec 64} (h : InRange (off (ob m0 i) o) n q) : ChgR m0 L O q :=
  .inr (.inr ⟨(i, o, n), hp, h⟩)

/-- A region output of a callee at the region's base is a change. -/
theorem chgR_reg0 {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {i n : Nat}
    (hp : (i, 0, n) ∈ O) {q : BitVec 64} (h : InRange (ob m0 i) n q) : ChgR m0 L O q :=
  .inr (.inr ⟨(i, 0, n), hp, by simpa [off] using h⟩)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
