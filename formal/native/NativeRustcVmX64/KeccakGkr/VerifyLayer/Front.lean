module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Exit
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Sums

/-!
# `verify_layer` on x86-64: the entry to the product's projection

The prologue (`b0`) pushes the registers, clears the product (47 elements at the frame's `472`)
and reads it (`read_scalars`); on `None` (`b1`) the exit. `b2` spills the arguments (`spills`)
and enters the projection's loop at `NativeRustcVmX64.Vm.VerifyLayer.label_4` (`PHead`, no term summed yet): `front`.

Tools: the frame's words (`FWs`, kept by a block missing them, `FWs.blk`; loaded, `fw_load`); the
`TState` kept by a block writing the frame only (`ts_blk0`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The frame's words `L` (offset, value). -/
def FWs (m0 : MachineData) (d : DataMem) (L : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ L, NativeRustcVm.WordAt d (off (stackBelow m0 2016) p.1) p.2

/-- A block's writes miss the frame's words `L`. -/
def missL (L : List (Nat × UInt64)) (S : SState) : Bool := L.all fun p ↦ missB p.1 8 S

/-- `logSteps - 4`, saturating. -/
def packV (m0 : MachineData) : UInt64 := ((reg m0 .rsi).toNat - 4).toUInt64

/-- The front's spilled words. -/
def spills (m0 : MachineData) (c : KeccakClaimW) : List (Nat × UInt64) :=
  [(24, packV m0), (32, c.mu.size.toUInt64), (40, .ofBitVec (tA m0)),
    (48, .ofBitVec (cA m0 + 24#64)), (56, .ofBitVec (reg m0 .rdx)),
    (64, .ofBitVec (cA m0 + 48#64)), (80, .ofBitVec (sA m0)), (96, .ofBitVec (cA m0)),
    (224, .ofBitVec (cA m0 + 16#64))]

/-- **The projection's state** with `j` terms summed: the body, the `TState`, the product, the
spills, RAX `16 j`, R14 `j`, RBX the instance weights' count rounded to even, R15 `RMFE_PROJECT`,
R12, R13 the sum. -/
structure PCore [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j : Nat) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s1
  prod : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 472) p.toList
  sp : FWs m0 d.dmem (spills m0 c)
  rax : reg d .rax = BitVec.ofNat 64 (16 * j)
  r14 : reg d .r14 = BitVec.ofNat 64 j
  rbx : reg d .rbx = BitVec.ofNat 64 (c.mu.size % 32 / 2 * 2)
  r15 : reg d .r15 = projectAddr
  acc : ewArg (reg d .r12) (reg d .r13) = xs (projTerm c.mu p) j
  lt : j < 47
  psize : p.size = 47

/-- **The projection's loop head** `NativeRustcVmX64.Vm.VerifyLayer.label_4`. -/
structure PHead [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j : Nat) (d : MachineData) : Prop where
  core : PCore m0 a c p s1 j d
  rsi : reg d .rsi = BitVec.ofNat 64 c.mu.size

end

public section

variable {m0 : MachineData}

theorem FWs.keep {d d' : DataMem} {L : List (Nat × UInt64)} (h : FWs m0 d L)
    (hk : ∀ p ∈ L, FrSame m0 d d' p.1 8) : FWs m0 d' L :=
  fun p hp ↦ FrSame.word (hk p hp) (h p hp) (Nat.le_refl 8)

/-- The spills' offsets. -/
theorem spills_in (c : KeccakClaimW) : ∀ q ∈ spills m0 c, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232 := by
  intro q hq
  simp only [spills, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem FWs.keepIn {d d' : DataMem} {L : List (Nat × UInt64)} (h : FWs m0 d L) {lo n : Nat}
    (hfr : FrSame m0 d d' lo n) (hL : ∀ q ∈ L, lo ≤ q.1 ∧ q.1 + 8 ≤ lo + n) : FWs m0 d' L :=
  h.keep fun q hq ↦ hfr.sub (hL q hq).1 (hL q hq).2

section spill
variable {d : DataMem} {c : KeccakClaimW} (h : FWs m0 d (spills m0 c))
include h
theorem sp24 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 24) (packV m0) :=
  h (24, (packV m0)) (List.mem_cons_self)
theorem sp32 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 32) c.mu.size.toUInt64 :=
  h (32, c.mu.size.toUInt64) (List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem sp40 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 40) (.ofBitVec (tA m0)) :=
  h (40, (.ofBitVec (tA m0))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem sp48 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 48) (.ofBitVec (cA m0 + 24#64)) :=
  h (48, (.ofBitVec (cA m0 + 24#64))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem sp56 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 56) (.ofBitVec (reg m0 .rdx)) :=
  h (56, (.ofBitVec (reg m0 .rdx))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem sp64 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 64) (.ofBitVec (cA m0 + 48#64)) :=
  h (64, (.ofBitVec (cA m0 + 48#64))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem sp80 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 80) (.ofBitVec (sA m0)) :=
  h (80, (.ofBitVec (sA m0))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem sp96 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 96) (.ofBitVec (cA m0)) :=
  h (96, (.ofBitVec (cA m0))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
theorem sp224 : NativeRustcVm.WordAt d (off (stackBelow m0 2016) 224) (.ofBitVec (cA m0 + 16#64)) :=
  h (224, (.ofBitVec (cA m0 + 16#64))) (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
end spill

variable [Labels]


/-- **A block keeps the frame's words** it misses. -/
theorem FWs.blk {d d' : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (envB m0 d ex vars ret).WF)
    (hm : Match (envB m0 d ex vars ret) S d') (hin : writesIn S = true)
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, p.1 + 8 ≤ 2024) (hmiss : missL L S = true)
    (h : FWs m0 d.dmem L) : FWs m0 d'.dmem L :=
  h.keep fun p hp ↦ frSame_blk hwf hm hin (hL p hp) (List.all_eq_true.mp hmiss p hp)

omit [Labels] in
/-- **A word of the frame, loaded** by a block. -/
theorem fload8 {d : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {o : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) o) w) :
    (envB m0 d ex vars ret).load 0 o 8 = w.toBitVec :=
  load_of_wordAt h

/-- **A frame word, loaded** by a block. -/
theorem fw_load {d : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {L : List (Nat × UInt64)} (h : FWs m0 d.dmem L) {o : Nat} {v : UInt64}
    (hp : (o, v) ∈ L) : (Sym.load 0 o 8).eval (envB m0 d ex vars ret) = v.toBitVec := by
  have hb : (envB m0 d ex vars ret).base 0 = stackBelow m0 2016 := rfl
  have hw := h _ hp
  rw [← hb] at hw
  exact load_of_wordAt hw

/-- A word written by a block at the frame's `o`. -/
theorem fw_write {d d' : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (envB m0 d ex vars ret) S d') {o : Nat}
    (hle : o + 8 ≤ 2024) {v : Sym} (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt d'.dmem (off (stackBelow m0 2016) o)
      (UInt64.ofBitVec (v.eval (envB m0 d ex vars ret))) :=
  wordAt_write hm (r := 0) rfl hle hw

end

/-! ## The `TState` across blocks -/

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The frame is apart from the `TState` and its decoded area. -/
theorem frame_not_t (hpre : VerifyLayerPre a s c m0) {q : BitVec 64}
    (h : InRange (stackBelow m0 2016) 2024 q) :
    ¬InRange (tA m0) 760 q ∧ ¬InRange a.words (8 * a.len) q := by
  have g := geo_of hpre
  have hfb := g.fbN; have := g.hN; have := g.top; have := g.ht; have := g.hts
  have h0 := pre_apart hpre (w := stackRegion m0 3232) (by simp) (r := a.region) (by simp)
  have hok := (pre_rok hpre (r := a.region) (by simp)).2
  simp only [stackRegion, NativeRustcVm.Transcript.DecArea.region] at h0 hok
  unfold NativeRustcVm.NoWrap at hok
  rw [g.sbN] at h0
  rw [Sym.inRange_iff (by omega), hfb] at h
  constructor
  · rw [Sym.inRange_iff (by omega)]; omega
  · rw [Sym.inRange_iff (by omega)]; omega

omit [Labels] in
/-- A write of a block writing region 0 only, below `2016`, is in the frame. -/
theorem written0 {d : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (g : Geo m0) (h0 : S.mem.all (fun w ↦ w.r == 0) = true)
    (hbr : belowRet 2016 S = true) {q : BitVec 64}
    (hq : Written (envB m0 d ex vars ret) S q) : InRange (stackBelow m0 2016) 2016 q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  have hr : w.r = 0 := by simpa using List.all_eq_true.mp h0 w hw
  have := belowRet_spec hbr w hw hr
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have hfb := g.fbN; have := g.hN; have := g.top
  rw [Sym.inRange_iff (by omega)]
  omega

/-- **The `TState` across a block** writing the frame only. -/
theorem ts_blk0 (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d ex vars ret).WF) (hm : Match (envB m0 d ex vars ret) S d')
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true) {s' : TState}
    (h : TStateAt d.dmem (tA m0) a s') : TStateAt d'.dmem (tA m0) a s' :=
  h.frame (hm.kept hwf)
    (fun _ hq ↦ frame_not_t hpre (inRange_mono (written0 (geo_of hpre) h0 hbr hq) (by decide)))
    fun _ hq ↦ hm.get?_mem0 hwf hq

/-- **A block writing the frame only keeps the body.** -/
theorem chg_written0 (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {d : MachineData}
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true) {q : BitVec 64}
    (hq : Written (envB m0 d ex vars ret) S q) : Chg m0 W q :=
  (geo_of hpre).frame_chg (written0 (geo_of hpre) h0 hbr hq)

/-- The front keeps the bytes in the claim. -/
theorem keepC (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → wFront m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d)
    {x : BitVec 64} {bs : List UInt8} (hx1 : (cA m0).toNat ≤ x.toNat)
    (hx2 : x.toNat + bs.length ≤ (cA m0).toNat + 768)
    (h : NativeRustcVm.BytesAt m0.dmem x bs) : NativeRustcVm.BytesAt d.dmem x bs := by
  have g := geo_of hpre
  refine h.of_sameOutside hb.same fun i hi hc ↦ ?_
  have hq : (x + BitVec.ofNat 64 i).toNat = x.toNat + i :=
    NativeRustcVm.toNat_add_ofNat (by have := g.hc; omega)
  have hsb := g.sbN; have := g.hN; have := g.top; have := g.hc; have := g.ht; have := g.hs
  have := g.hcs; have := g.htc; have := g.hcsc
  rcases hc with hc | hc
  · rw [Sym.inRange_iff (by omega), hsb, hq] at hc; omega
  · rcases hW _ hc with hc | hc
    · rw [Sym.inRange_iff (by omega), hq] at hc; omega
    · rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega), hq] at hc; omega

/-- The front keeps the bytes in the claim's bit weights. -/
theorem keepW (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → wFront m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d)
    {x : BitVec 64} {bs : List UInt8} (hx1 : (lA m0).toNat ≤ x.toNat)
    (hx2 : x.toNat + bs.length ≤ (lA m0).toNat + 25600)
    (h : NativeRustcVm.BytesAt m0.dmem x bs) : NativeRustcVm.BytesAt d.dmem x bs := by
  have g := geo_of hpre
  have hl := g.lN
  refine h.of_sameOutside hb.same fun i hi hc ↦ ?_
  have hq : (x + BitVec.ofNat 64 i).toNat = x.toNat + i :=
    NativeRustcVm.toNat_add_ofNat (by have := g.hs; omega)
  have hsb := g.sbN; have := g.hN; have := g.top; have := g.hc; have := g.ht; have := g.hs
  have := g.hss; have := g.htsc
  rcases hc with hc | hc
  · rw [Sym.inRange_iff (by omega), hsb, hq] at hc; omega
  · rcases hW _ hc with hc | hc
    · rw [Sym.inRange_iff (by omega), hq] at hc; omega
    · rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega), hq] at hc; omega

/-- **The claim, kept by the front.** -/
theorem Body.claim (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → wFront m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d) :
    ClaimAt d.dmem (cA m0) c := by
  have g := geo_of hpre
  have hc := g.hc
  obtain ⟨h1, ⟨h2, h3, h4⟩, ⟨h5, h6, h7⟩⟩ := pre_claim hpre
  unfold ClaimAt NativeRustcVm.BufEWAt
  simp only [NativeRustcVm.KeccakGkr.muOff, NativeRustcVm.KeccakGkr.pointOff,
    NativeRustcVm.KeccakGkr.muCap, NativeRustcVm.KeccakGkr.claimPointCap] at h2 h3 h4 h5 h6 h7 ⊢
  have hm := NativeRustcVm.length_ewsBytes c.mu.toList
  have hp := NativeRustcVm.length_ewsBytes c.point.toList
  have l1 := g.ca (o := 16) (by omega); have l2 := g.ca (o := 24) (by omega)
  have l3 := g.ca (o := 280) (by omega); have l4 := g.ca (o := 288) (by omega)
  have e2 : (NativeRustcVm.KeccakGkr.off (cA m0) 16 + 8#64) = cA m0 + BitVec.ofNat 64 24 := by
    unfold NativeRustcVm.KeccakGkr.off; bv_omega
  have e3 : (NativeRustcVm.KeccakGkr.off (cA m0) 280 + 8#64) = cA m0 + BitVec.ofNat 64 288 := by
    unfold NativeRustcVm.KeccakGkr.off; bv_omega
  refine ⟨keepC hpre hW hb (by omega) (by rw [NativeRustcVm.length_ewBytes]; omega) h1,
    ⟨h2, keepC hpre hW hb (by unfold NativeRustcVm.KeccakGkr.off; omega)
      (by unfold NativeRustcVm.KeccakGkr.off; rw [l1, NativeRustcVm.length_wordBytes]; omega) h3,
      ?_⟩, ⟨h5, keepC hpre hW hb (by unfold NativeRustcVm.KeccakGkr.off; omega)
      (by unfold NativeRustcVm.KeccakGkr.off; rw [l3, NativeRustcVm.length_wordBytes]; omega) h6,
      ?_⟩⟩
  · unfold NativeRustcVm.EWsAt at h4 ⊢
    rw [e2] at h4 ⊢
    exact keepC hpre hW hb (by omega) (by rw [l2, hm]; omega) h4
  · unfold NativeRustcVm.EWsAt at h7 ⊢
    rw [e3] at h7 ⊢
    exact keepC hpre hW hb (by omega) (by rw [l4, hp]; omega) h7

/-- **The claim's bit weights, kept by the front.** -/
theorem Body.weights (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → wFront m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d) :
    WeightsAt d.dmem (lA m0) c := by
  obtain ⟨hs, h⟩ := pre_w hpre
  refine ⟨hs, keepW hpre hW hb (by omega) ?_ h⟩
  rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hs]
  have : 16 * keccakBits = 25600 := by decide
  omega

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
