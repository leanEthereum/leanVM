module

public import NativeRustcVmX64.Spec.KeccakGkr
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Model

/-!
# `verify_layer` on x86-64: the body's frame

The prologue pushes six registers and reserves 1944 bytes; the two `sumcheck` calls push 16 bytes
of stack arguments first. The frame (`Transcript.Frame`, 2016 bytes below the entry's RSP,
region 0 of every block's environment) has the stack arguments at `0` and `8` and a call's return
address at `0` (the `sumcheck`s) or `16` (the others), the body's locals from `24` (RSP at `24`
between calls, so the assembly's `x(%rsp)` is the frame's `x + 24`), the pushed registers at
`1968` to `2008` (`slots`), the return address at `2016`.

`Body m0 W o d`: the frame with RSP at offset `o`, memory changed only in the 3232 bytes of stack
and the outputs `W` (`wFront`: the `TState` and the scratch's layer weights and equality kernel,
before the claim is written; then `outs`: the `TState`, the claim, the scratch's `layerRegion`). The addresses as
numbers (`Geo`, from the precondition). A block keeps it (`Body.blk`), a call too (`Body.call`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes scratchBytes)

@[expose] public section

/-- The pushed registers' slots. -/
def slots : Slots :=
  [(2008, .rbp), (2000, .r15), (1992, .r14), (1984, .r13), (1976, .r12), (1968, .rbx)]

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The claim. -/
abbrev cA (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The scratch. -/
abbrev sA (m0 : MachineData) : BitVec 64 := reg m0 .r8
/-- The scratch's part `verify_layer` writes (`layerRegion`). -/
abbrev lA (m0 : MachineData) : BitVec 64 := sA m0 + BitVec.ofNat 64 25600

/-- What the body writes but the stack. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (tA m0) 760 q ∨ InRange (cA m0) 768 q ∨ InRange (lA m0) 114688 q

/-- The front's outputs: the `TState`, the scratch's layer weights and local equality kernel (the
claim and its bit weights untouched). -/
def wFront (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (tA m0) 760 q ∨ InRange (sA m0 + BitVec.ofNat 64 51200) 89088 q

/-- What memory may differ in from the entry's: the stack, the outputs `W`. -/
def Chg (m0 : MachineData) (W : BitVec 64 → Prop) (q : BitVec 64) : Prop :=
  InRange (stackBelow m0 3232) 3232 q ∨ W q

/-- **The body**, RSP at offset `o`, memory changed in the stack and `W` only. -/
structure Body (m0 : MachineData) (W : BitVec 64 → Prop) (o : Nat) (d : MachineData) : Prop where
  fr : Frame m0 2016 slots o d
  same : SameOutside m0.dmem d.dmem (Chg m0 W)

/-- **The addresses as numbers.** -/
structure Geo (m0 : MachineData) : Prop where
  hN : 3232 ≤ (rspOf m0).toNat
  top : (rspOf m0).toNat + 8 ≤ 2 ^ 64
  ht : (tA m0).toNat + 760 ≤ 2 ^ 64
  hc : (cA m0).toNat + 768 ≤ 2 ^ 64
  hs : (sA m0).toNat + 205824 ≤ 2 ^ 64
  hts : (tA m0).toNat + 760 ≤ (rspOf m0).toNat - 3232 ∨ (rspOf m0).toNat + 8 ≤ (tA m0).toNat
  hcs : (cA m0).toNat + 768 ≤ (rspOf m0).toNat - 3232 ∨ (rspOf m0).toNat + 8 ≤ (cA m0).toNat
  hss : (sA m0).toNat + 205824 ≤ (rspOf m0).toNat - 3232 ∨ (rspOf m0).toNat + 8 ≤ (sA m0).toNat
  htc : (tA m0).toNat + 760 ≤ (cA m0).toNat ∨ (cA m0).toNat + 768 ≤ (tA m0).toNat
  htsc : (tA m0).toNat + 760 ≤ (sA m0).toNat ∨ (sA m0).toNat + 205824 ≤ (tA m0).toNat
  hcsc : (cA m0).toNat + 768 ≤ (sA m0).toNat ∨ (sA m0).toNat + 205824 ≤ (cA m0).toNat

theorem stack_eq : verifyLayerStack = 3232 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 2016 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem slots_lo : ∀ p ∈ slots, 1968 ≤ p.1 := by decide

end

public section

variable {m0 : MachineData}

theorem Geo.sp_lt (m0 : MachineData) : (rspOf m0).toNat < 2 ^ 64 := (rspOf m0).isLt

/-- The frame's base as a number. -/
theorem Geo.fbN (g : Geo m0) : (stackBelow m0 2016).toNat = (rspOf m0).toNat - 2016 :=
  NativeRustcVm.toNat_sub_ofNat (by have := g.hN; omega)

/-- The stack's base as a number. -/
theorem Geo.sbN (g : Geo m0) : (stackBelow m0 3232).toNat = (rspOf m0).toNat - 3232 :=
  NativeRustcVm.toNat_sub_ofNat g.hN

/-- A frame address as a number. -/
theorem Geo.fa (g : Geo m0) {o : Nat} (ho : o < 2024) :
    (stackBelow m0 2016 + BitVec.ofNat 64 o).toNat = (rspOf m0).toNat - 2016 + o := by
  have := g.hN; have := g.top
  rw [NativeRustcVm.toNat_add_ofNat (by rw [g.fbN]; omega), g.fbN]

/-- An address of the scratch as a number. -/
theorem Geo.sa (g : Geo m0) {o : Nat} (ho : o < 205824) :
    (sA m0 + BitVec.ofNat 64 o).toNat = (sA m0).toNat + o := by
  have := g.hs
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]

/-- An address of the claim as a number. -/
theorem Geo.ca (g : Geo m0) {o : Nat} (ho : o < 768) :
    (cA m0 + BitVec.ofNat 64 o).toNat = (cA m0).toNat + o := by
  have := g.hc
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]

/-- An address of the `TState` as a number. -/
theorem Geo.ta (g : Geo m0) {o : Nat} (ho : o < 760) :
    (tA m0 + BitVec.ofNat 64 o).toNat = (tA m0).toNat + o := by
  have := g.ht
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]

theorem Geo.lN (g : Geo m0) : (lA m0).toNat = (sA m0).toNat + 25600 := g.sa (by omega)

/-- A frame byte is in the stack. -/
theorem Geo.frame_chg (g : Geo m0) {W : BitVec 64 → Prop} {q : BitVec 64}
    (h : InRange (stackBelow m0 2016) 2016 q) : Chg m0 W q :=
  .inl (inRange_frame_stack g.top g.hN (by decide) h)

/-- A byte of the frame below `2016` is no output. -/
theorem Geo.frame_not_outs (g : Geo m0) {j : Nat} (hj : j < 2024) :
    ¬outs m0 (stackBelow m0 2016 + BitVec.ofNat 64 j) := by
  have hf := g.fa (o := j) (by omega)
  have := g.hN; have := g.top; have := g.ht; have := g.hc; have := g.hs; have := g.hts
  have := g.hcs; have := g.hss; have hl := g.lN
  rintro (h | h | h)
  · rw [Sym.inRange_iff (by omega), hf] at h; omega
  · rw [Sym.inRange_iff (by omega), hf] at h; omega
  · rw [Sym.inRange_iff (by omega), hf, hl] at h; omega

/-- The entry's return address is not memory the body may change. -/
theorem Geo.ret_not_chg (g : Geo m0) {W : BitVec 64 → Prop} (hW : ∀ q, W q → outs m0 q)
    {j : Nat} (hj : j < 8) : ¬Chg m0 W (stackBelow m0 2016 + BitVec.ofNat 64 (2016 + j)) := by
  have hf := g.fa (o := 2016 + j) (by omega)
  have hs := g.sbN; have := g.hN; have := g.top
  rintro (h | h)
  · rw [Sym.inRange_iff (by omega), hf, hs] at h; omega
  · exact g.frame_not_outs (by omega) (hW _ h)

/-- A slot is not memory a callee at offset `oc` changes. -/
theorem Geo.slot_ne (g : Geo m0) {p : Nat × Reg64} (hp : p ∈ slots) {i : Nat} (hi : i < 8) :
    ¬outs m0 (off (stackBelow m0 2016) (p.1 + i)) := by
  have := slots_le p hp
  exact g.frame_not_outs (by omega)

end

/-! ## The precondition -/

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

omit [Labels] in
theorem areas_ok {m : MachineData} {n : Nat} {ws rs : List NativeRustcVm.Region}
    (h : Areas m n ws rs) {r : NativeRustcVm.Region} (hr : r ∈ ws ∨ r ∈ rs) : r.Ok m.dmem :=
  h.1 r (List.mem_append.mpr hr)

omit [Labels] in
theorem areas_ws {m : MachineData} {n : Nat} {ws rs : List NativeRustcVm.Region}
    (h : Areas m n ws rs) {i j : Nat} (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) :
    NativeRustcVm.Apart ws[i].addr ws[i].size ws[j].addr ws[j].size := by
  have h2 := NativeRustcVm.Disjoint.apart h.2.1 (i := i + 1) (j := j + 1) (by simp; omega)
    (by simp; omega) (by omega)
  simp only [List.getElem_cons_succ] at h2
  exact h2

omit [Labels] in
theorem areas_stack {m : MachineData} {n : Nat} {ws rs : List NativeRustcVm.Region}
    (h : Areas m n ws rs) {w : NativeRustcVm.Region} (hw : w ∈ ws) :
    NativeRustcVm.Apart w.addr w.size (stackBelow m n) (n + 8) := by
  have h1 := h.2.1
  rw [stackRegion, NativeRustcVm.disjoint_cons_iff] at h1
  have := (h1.1 w hw)
  simp only at this
  unfold NativeRustcVm.Apart at this ⊢
  omega

omit [Labels] in
theorem areas_rs {m : MachineData} {n : Nat} {ws rs : List NativeRustcVm.Region}
    (h : Areas m n ws rs) {w r : NativeRustcVm.Region} (hw : w ∈ stackRegion m n :: ws)
    (hr : r ∈ rs) : NativeRustcVm.Apart w.addr w.size r.addr r.size :=
  h.2.2 w hw r hr

/-- **The addresses of the precondition.** -/
theorem geo_of (h : VerifyLayerPre a s c m0) : Geo m0 := by
  obtain ⟨hS, -, -, -, -, -, -, -, -, hA, -⟩ := h
  have hN : 3232 ≤ (rspOf m0).toNat := by have := hS.1; rw [stack_eq] at this; exact this
  have hsb : (stackBelow m0 verifyLayerStack).toNat = (rspOf m0).toNat - 3232 := by
    rw [stack_eq]; exact NativeRustcVm.toNat_sub_ofNat hN
  have ht := (areas_ok hA (r := ⟨tA m0, tstateBytes⟩) (.inl (by simp))).2
  have hc := (areas_ok hA (r := ⟨cA m0, claimBytes⟩) (.inl (by simp))).2
  have hs := (areas_ok hA (r := ⟨sA m0, scratchBytes⟩) (.inl (by simp))).2
  have h1 := areas_stack hA (w := ⟨tA m0, tstateBytes⟩) (by simp)
  have h2 := areas_stack hA (w := ⟨cA m0, claimBytes⟩) (by simp)
  have h3 := areas_stack hA (w := ⟨sA m0, scratchBytes⟩) (by simp)
  have h4 := areas_ws hA (i := 0) (j := 1) (by simp) (by simp) (by omega)
  have h5 := areas_ws hA (i := 0) (j := 2) (by simp) (by simp) (by omega)
  have h6 := areas_ws hA (i := 1) (j := 2) (by simp) (by simp) (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h4 h5 h6
  unfold NativeRustcVm.NoWrap at ht hc hs
  unfold NativeRustcVm.Apart at h1 h2 h3 h4 h5 h6
  rw [hsb] at h1 h2 h3
  simp only [stack_eq, tstateBytes, claimBytes, scratchBytes] at *
  exact ⟨hN, hS.2.1, ht, hc, hs, by omega, by omega, by omega, h4, h5, h6⟩

end

/-! ## Blocks and calls -/

public section

variable {m0 : MachineData}

/-- **A call** from offset `oc` keeps the frame where the callee changes none of its slots' or
the return address's bytes: RSP `8` above. -/
theorem Frame.call_at {F oc : Nat} {sl : Slots} {d d' : MachineData} (hf : Frame m0 F sl oc d)
    (hs : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ sl, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F sl (oc + 8) d' := by
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hs.2, fun r hr hsl ↦ ?_⟩
  · rw [hrsp, hf.sp, off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
  · refine NativeRustcVm.Transcript.bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [NativeRustcVm.Transcript.off_add]
    exact hso _ (hR p hp i hi')
  · rw [hso _ (hRr j hj)]
    exact hf.ret j hj
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

variable [Labels]

/-- The frame's environment of a body, the regions `ex` beside. -/
abbrev envB (m0 d : MachineData) (ex : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64)
    (ret : BitVec 64) : Env :=
  frameEnv m0 d 2016 ex vars ret

/-- RSP of a body as the frame's pointer. -/
theorem Body.rsp {W : BitVec 64 → Prop} {o : Nat} {d : MachineData} (hb : Body m0 W o d) {ex : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    d.regs.get64 .rsp = (Sym.ptr 0 (o : Int)).eval (envB m0 d ex vars ret) :=
  hb.fr.rsp_eval

omit [Labels] in
/-- A block's writes in the frame below `2016` or in the outputs are changes the body allows. -/
theorem written_chg (g : Geo m0) {W : BitVec 64 → Prop} {d : MachineData} {ex : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hbr : belowRet 2016 S = true)
    (hex : ∀ w ∈ S.mem, w.r ≠ 0 → ∀ b sz, (envB m0 d ex vars ret).regions[w.r]? = some (b, sz) →
      ∀ q, b.toNat + w.off ≤ q.toNat → q.toNat < b.toNat + w.off + w.n → W q)
    {q : BitVec 64} (h : Written (envB m0 d ex vars ret) S q) : Chg m0 W q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  by_cases hr : w.r = 0
  · have := belowRet_spec hbr w hw hr
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine g.frame_chg ?_
    have hfb := g.fbN
    have := g.hN; have := g.top
    rw [Sym.inRange_iff (by omega)]
    omega
  · exact .inr (hex w hw hr b sz hb q h1 h2)

end

public section

variable {m0 : MachineData} [Host]

/-- **A block** of the body, its writes in the frame or the outputs. -/
theorem Body.blk (g : Geo m0) {W : BitVec 64 → Prop} {o o' : Nat} {d : MachineData}
    (hb : Body m0 W o d)
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hwf : (envB m0 d ex vars ret).WF) {ds : List Directive} {k : Nat} {S S' : SState} {x : Exit}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds S = some (S', x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (k + ds.length)).toBitVec)
    (hm : Match (envB m0 d ex vars ret) S d) (hmid : MidOk 2016 o' slots S' = true)
    (hex : ∀ w ∈ S'.mem, w.r ≠ 0 → ∀ b sz, (envB m0 d ex vars ret).regions[w.r]? = some (b, sz) →
      ∀ q, b.toNat + w.off ≤ q.toNat → q.toNat < b.toNat + w.off + w.n → W q)
    {R : MachineState → Prop}
    (cont : ∀ st, Match (envB m0 d ex vars ret) S' st.data →
      PcOk (envB m0 d ex vars ret) x (Host.addrOf (k + ds.length)) st → Body m0 W o' st.data →
      SameOutside d.dmem st.data.dmem (Written (envB m0 d ex vars ret) S') →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf k⟩ := by
  refine exec_then hk hrun hwf hret hm fun st hm' hpc ↦ cont st hm' hpc ⟨?_, fun q hq ↦ ?_⟩
    fun q hq ↦ hm'.get?_mem0 hwf hq
  · exact Frame.of_block hb.fr hwf hm' hmid slots_le
  · have hbr : belowRet 2016 S' = true := by
      simp only [MidOk, Bool.and_eq_true] at hmid
      exact hmid.1.1.1.2
    rw [hm'.get?_mem0 hwf fun hw ↦ hq (written_chg g hbr hex hw)]
    exact hb.same q hq

end

public section

variable {m0 : MachineData} [Labels]

omit [Labels] in
/-- No write outside region 0. -/
theorem hex0 {W : BitVec 64 → Prop} {d : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (h : S.mem.all (fun w ↦ w.r == 0) = true) :
    ∀ w ∈ S.mem, w.r ≠ 0 → ∀ b sz, (envB m0 d ex vars ret).regions[w.r]? = some (b, sz) →
      ∀ q, b.toNat + w.off ≤ q.toNat → q.toNat < b.toNat + w.off + w.n → W q := by
  intro w hw hr
  have := List.all_eq_true.mp h w hw
  simp only [beq_iff_eq] at this
  exact absurd this hr

omit [Labels] in
/-- **A call** from the body at offset `oc`, the callee using `Sk` bytes of stack below RSP and
writing `W` (outputs, or the frame's locals above its return address). -/
theorem Body.call (g : Geo m0) {W : BitVec 64 → Prop} (hWo : ∀ q, W q → outs m0 q) {oc : Nat}
    {mc d' : MachineData} (hb : Body m0 W oc mc)
    (hoc : oc + 8 ≤ 1968) (hs : Saved mc d') (hrsp : rspOf d' = rspOf mc + 8#64) {Sk : Nat}
    (hSk : 2016 - oc + Sk ≤ 3232) {Wc : BitVec 64 → Prop}
    (hso : SameOutside mc.dmem d'.dmem (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ Wc q))
    (hW : ∀ q, Wc q → W q ∨ InRange (off (stackBelow m0 2016) (oc + 8)) (1960 - oc) q) :
    Body m0 W (oc + 8) d' := by
  have hN := g.hN; have htop := g.top; have hfb := g.fbN; have hsb := g.sbN
  have hmsp : (rspOf mc).toNat = (rspOf m0).toNat - 2016 + oc := by
    rw [hb.fr.sp]; exact g.fa (by omega)
  have hcs : (stackBelow mc Sk).toNat = (rspOf m0).toNat - 2016 + oc - Sk :=
    by rw [stackBelow_toNat (by omega), hmsp]
  have hcin : ∀ q, InRange (stackBelow mc Sk) Sk q →
      (rspOf m0).toNat - 2016 + oc - Sk ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 2016 + oc :=
    fun q h ↦ by rw [Sym.inRange_iff (by omega), hcs] at h; omega
  have hWin : ∀ q, InRange (off (stackBelow m0 2016) (oc + 8)) (1960 - oc) q →
      (rspOf m0).toNat - 2016 + oc + 8 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 2016 + 1968 :=
    fun q h ↦ by rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off,
      g.fa (by omega)] at h; omega
  refine ⟨Frame.call_at hb.fr hs hrsp hso (fun p hp i hi h ↦ ?_) (fun j hj h ↦ ?_),
    fun q hq ↦ ?_⟩
  · have := slots_le p hp; have := slots_lo p hp
    have ha : (off (stackBelow m0 2016) (p.1 + i)).toNat = (rspOf m0).toNat - 2016 + (p.1 + i) :=
      g.fa (by omega)
    rcases h with h | h
    · have := hcin _ h; omega
    · rcases hW _ h with h | h
      · exact g.slot_ne hp hi (hWo _ h)
      · have := hWin _ h; omega
  · have ha : (off (stackBelow m0 2016) (2016 + j)).toNat = (rspOf m0).toNat - 2016 + (2016 + j) := g.fa (by omega)
    rcases h with h | h
    · have := hcin _ h; omega
    · rcases hW _ h with h | h
      · exact g.ret_not_chg hWo hj (.inr h)
      · have := hWin _ h; omega
  · rw [hso q fun h ↦ hq ?_]
    · exact hb.same q hq
    · rcases h with h | h
      · have := hcin _ h
        left
        rw [Sym.inRange_iff (by omega), hsb]
        omega
      · rcases hW _ h with h | h
        · exact .inr h
        · have := hWin _ h
          left
          rw [Sym.inRange_iff (by omega), hsb]
          omega

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
