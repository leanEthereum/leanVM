module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Beta
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Index

/-! # Memory and register invariants of the layer weights loop -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

def lwF (eq : Array EW) (b : EW) (j : Nat) : EW :=
  eq.getD j 0 + b * (eq.getD (keccakAlong j 4) 0 + b * eq.getD (keccakAlong j 3) 0)

def weightWords (m0 : MachineData) (c : KeccakClaimW) (t : Array EW) (b : EW) :
    List (Nat × UInt64) :=
  [(24, b.c0), (40, b.c1), (56, .ofBitVec (sA m0 + BitVec.ofNat 64 107520)),
    (64, .ofBitVec (BitVec.ofNat 64 c.point.size)), (80, .ofBitVec (sA m0)),
    (88, .ofBitVec (sA m0 + BitVec.ofNat 64 51200)), (96, .ofBitVec (cA m0)),
    (120, .ofBitVec (sA m0 + BitVec.ofNat 64 25600)),
    (128, .ofBitVec (cA m0 + 280#64)), (224, .ofBitVec (cA m0 + 16#64))] ++ twl t

structure WMem (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch b : EW)
    (pt lp t : Array EW) (s6 : TState) (j : Nat) (d : DataMem) : Prop where
  ts : TStateAt d (tA m0) a s6
  fw : FWs m0 d (weightWords m0 c t b)
  mu : NativeRustcVm.BufEWAt d (off (stackBelow m0 2016) 1704) 16
    (keccakInstanceWeights ch).toList
  pt : NativeRustcVm.EWsAt d (off (stackBelow m0 2016) 1224) pt.toList
  eq : NativeRustcVm.EWsAt d (sA m0 + BitVec.ofNat 64 107520) (eqKernel lp).toList
  lw : ∀ i < j, NativeRustcVm.EWAt d (sA m0 + BitVec.ofNat 64 (51200 + 16 * i))
    (lwF (eqKernel lp) b i)

structure WHead (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch b : EW)
    (pt lp t : Array EW) (s6 : TState) (j : Nat) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  mem : WMem m0 a c ch b pt lp t s6 j d.dmem
  lt : j < 1600
  rbp : reg d .rbp = BitVec.ofNat 64 j
  rbx : reg d .rbx = BitVec.ofNat 64 (16 * j)
  r15 : reg d .r15 = sA m0
  r13 : reg d .r13 = BitVec.ofNat 64 288230376151711742

end

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {j : Nat}

theorem wfScratch (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {o : Nat}
    {d : MachineData} (hb : Body m0 W o d) {p n : Nat} (hp : p < 205824)
    (hn : p + n ≤ 205824) {ret : BitVec 64} :
    (envB m0 d [(sA m0 + BitVec.ofNat 64 p, n)] (fun _ ↦ 0) ret).WF := by
  have g := geo_of hpre
  have h := scrOk hpre hb hp hn
  apply wf1 (pre_stack hpre) hb h.1 h.2
  have := g.hss; have := g.hs; have := g.hN; have := g.top
  unfold NativeRustcVm.Apart
  rw [g.fbN, g.sa (by omega)]
  omega

theorem WMem.blk (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    (h : WMem m0 a c ch b pt lp t s6 j d.dmem) (hpt : pt.size ≤ 30) (hlp : lp.size = 11)
    (hj : j ≤ 1600) {ex : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d ex (fun _ ↦ 0) ret).WF)
    (hm : Match (envB m0 d ex (fun _ ↦ 0) ret) S d')
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true)
    (hin : writesIn S = true) (hmiss : missB 1224 744 S = true)
    (hwords : [24, 40, 56, 64, 80, 88, 96, 120, 128, 224, 72, 104, 112, 184, 192, 200].all
      (fun o ↦ decide (o + 8 ≤ 2024) && missB o 8 S) = true) :
    WMem m0 a c ch b pt lp t s6 j d'.dmem := by
  have hf := frSame_blk hwf hm hin (show 1224 + 744 ≤ 2024 by decide) hmiss
  refine ⟨ts_blk0 hpre hwf hm h0 hbr h.ts,
    FWs.blkO rfl hwf hm hin hwords h.fw,
    (hf.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
    (hf.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.pt
      (by rw [Array.length_toList]; omega),
    scr_blk0E hpre hwf hm h0 hbr (by decide) (by rw [eqK_len hlp]; decide) h.eq, ?_⟩
  intro i hi
  exact scr_blk0 hpre hwf hm h0 hbr (by omega) (by change 51200 + 16 * i + 16 ≤ 205824; omega)
    (h.lw i hi)

theorem WMem.leaf (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    (h : WMem m0 a c ch b pt lp t s6 j d.dmem) (hpt : pt.size ≤ 30) (hlp : lp.size = 11)
    (hj : j ≤ 1600) (hb : Body m0 (wFront m0) 16 d)
    (hf : FrSame m0 d.dmem d'.dmem 24 2000)
    (ht : TStateAt d'.dmem (tA m0) a s6) {Sk : Nat} (hSk : 2000 + Sk ≤ 3232)
    (hso : SameOutside d.dmem d'.dmem (InRange (stackBelow d Sk) Sk)) :
    WMem m0 a c ch b pt lp t s6 j d'.dmem := by
  have hs : SameOutside d.dmem d'.dmem
      (fun q ↦ InRange (stackBelow d Sk) Sk q ∨ False) :=
    NativeRustcVm.SameOutside.mono hso fun _ hq ↦ Or.inl hq
  refine ⟨ht, FWs.keepR
      (os := [24, 40, 56, 64, 80, 88, 96, 120, 128, 224, 72, 104, 112, 184, 192, 200])
      rfl hf (by decide +kernel) h.fw,
    (hf.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
    (hf.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.pt
      (by rw [Array.length_toList]; omega),
    scr_call hpre (wFront_outs hpre) hb hSk hs (by decide)
      (by rw [eqK_len hlp]; decide) (fun _ hq ↦ hq.elim) h.eq, ?_⟩
  intro i hi
  exact scr_call hpre (wFront_outs hpre) hb hSk hs
    (xs := [lwF (eqKernel lp) b i]) (by omega) (by simp only [List.length_singleton]; omega)
    (fun _ hq ↦ hq.elim) (h.lw i hi)

omit [Labels] in
theorem scratchLoads {d : MachineData} {xs : Array EW} {p i : Nat}
    (h : NativeRustcVm.EWsAt d.dmem (sA m0 + BitVec.ofNat 64 p) xs.toList) (hi : i < xs.size)
    {ret : BitVec 64} :
    (envB m0 d [(sA m0 + BitVec.ofNat 64 (p + 16 * i), 16)] (fun _ ↦ 0) ret).load 1 0 8 =
        (xs.getD i 0).c0.toBitVec ∧
      (envB m0 d [(sA m0 + BitVec.ofNat 64 (p + 16 * i), 16)] (fun _ ↦ 0) ret).load 1 8 8 =
        (xs.getD i 0).c1.toBitVec := by
  have he := h.getElem (i := i) (by rw [Array.length_toList]; exact hi)
  rw [NativeRustcVm.ewAt_iff, Array.getElem_toList] at he
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  constructor
  · apply load_of_wordAt
    change NativeRustcVm.WordAt d.dmem
      (sA m0 + BitVec.ofNat 64 (p + 16 * i) + BitVec.ofNat 64 0) _
    rw [BitVec.add_zero, ← NativeRustcVm.addr_add_add]
    exact he.1
  · apply load_of_wordAt
    change NativeRustcVm.WordAt d.dmem
      (sA m0 + BitVec.ofNat 64 (p + 16 * i) + BitVec.ofNat 64 8) _
    rw [← NativeRustcVm.addr_add_add]
    exact he.2

omit [Labels] in
theorem layerWeights_size (eq : Array EW) (b : EW) : (layerWeights eq b).size = 1600 := by
  rw [layerWeights, Array.size_map, Array.size_range]
  rfl

omit [Labels] in
theorem lw_ewsAt {eq : Array EW} {b : EW} {d : DataMem}
    (h : ∀ i < 1600, NativeRustcVm.EWAt d (sA m0 + BitVec.ofNat 64 (51200 + 16 * i))
      (lwF eq b i)) :
    NativeRustcVm.EWsAt d (sA m0 + BitVec.ofNat 64 51200) (layerWeights eq b).toList := by
  rw [NativeRustcVm.ewsAt_iff]
  intro i hi
  have hi' : i < 1600 := by rw [Array.length_toList, layerWeights_size] at hi; exact hi
  rw [NativeRustcVm.addr_add_add]
  have he : (layerWeights eq b).toList[i] = lwF eq b i := by simp [layerWeights, lwF]
  rw [he]
  exact h i hi'

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
