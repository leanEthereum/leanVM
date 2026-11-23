module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Defs
public import NativeRustcVm.Layout.RepLemmas
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Update

/-!
# `verify_layer`: memory in the body

A word of the frame as a block loads it (`fw_load`), the frame's words and a range kept by a change
that misses them (`FrameWords.of_same`, `same_frame`, `ewsAt_same`), the read-only regions never
written (`same_rs`), a `Buf<EW, N>` copied byte by byte (`BufEWAt.copy`), an element's sum
(`ew_add`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm (Region)
open NativeRustcVm.Layout (Same)
open NativeRustcVm.Transcript (tstateBytes DecArea)
open NativeRustcVm.KeccakGkr (claimBytes)

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **A word of the frame**, as a block of the body loads it. -/
theorem fw_load {env : Env} (hb : env.base 0 = base m0 2032) {o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (base m0 2032 + BitVec.ofNat 64 o) v) :
    env.load 0 o 8 = v.toBitVec :=
  Ring.load_word (by rw [hb]; exact h)

/-- A frame word of a list. -/
theorem FrameWords.get {d : DataMem} {b : BitVec 64} {ws : List (Nat × UInt64)}
    (h : Bus.FrameWords d b ws) {o : Nat} {v : UInt64} (hm : (o, v) ∈ ws) :
    NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) v :=
  h (o, v) hm

/-- **The frame's words kept** where the frame stayed the same. -/
theorem FrameWords.of_same {d d' : DataMem} {b : BitVec 64} {ws : List (Nat × UInt64)}
    (h : Bus.FrameWords d b ws) (hs : Same d d' b 2032) (hle : ∀ p ∈ ws, p.1 + 8 ≤ 2032) :
    Bus.FrameWords d' b ws := fun p hp ↦
  NativeRustcVm.Layout.WordAt.of_same (h p hp) (hs.sub (hle p hp)) (Nat.le_refl _)

/-- **Elements kept** where the range stayed the same. -/
theorem ewsAt_same {d d' : DataMem} {x : BitVec 64} {n : Nat} {xs : List EW}
    (h : NativeRustcVm.EWsAt d x xs) (hs : Same d d' x n) (hl : 16 * xs.length ≤ n) :
    NativeRustcVm.EWsAt d' x xs :=
  NativeRustcVm.Layout.BytesAt.of_same h hs (by rw [NativeRustcVm.length_ewsBytes]; exact hl)

/-- **The frame kept by a call** whose outputs miss it. -/
theorem same_frame (g : Geo m0) {m m' : MachineData} (hsp : m.regs.SP.toBitVec = base m0 2032)
    {n : Nat} (hn : n ≤ 1616) {W : BitVec 64 → Prop}
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m n) n q ∨ W q)
    (hW : ∀ j < 2032, ¬W (base m0 2032 + BitVec.ofNat 64 j)) :
    Same m.dmem m'.dmem (base m0 2032) 2032 := by
  have := g.hN; have := Geo.sp_lt m0; have hb := g.bN; have hst := g.stk hsp hn
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj h ↦ h.elim (fun h ↦ ?_) (hW j hj)
  exact notIn (by rw [hst]; omega) (by rw [hb]; omega) (by rw [hst, hb]; omega) h

/-- The `TState` misses the frame. -/
theorem t_not_frame (g : Geo m0) {j : Nat} (hj : j < 2032) :
    ¬InRange (tA m0) tstateBytes (base m0 2032 + BitVec.ofNat 64 j) := by
  have := g.hN; have := Geo.sp_lt m0; have hb := g.bN; have := g.ht; have := g.hts
  exact notIn (by simp only [tstateBytes]; omega) (by rw [hb]; omega)
    (by simp only [tstateBytes]; rw [hb]; omega)

/-- The claim misses the frame. -/
theorem c_not_frame (g : Geo m0) {j : Nat} (hj : j < 2032) {o n : Nat} (ho : o < 768)
    (hon : o + n ≤ 768) :
    ¬InRange (cA m0 + BitVec.ofNat 64 o) n (base m0 2032 + BitVec.ofNat 64 j) := by
  have := g.hN; have := Geo.sp_lt m0; have hb := g.bN; have := g.hc; have := g.hcs
  have e : (cA m0 + BitVec.ofNat 64 o).toNat = (cA m0).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  exact notIn (by rw [e]; omega) (by rw [hb]; omega) (by rw [e, hb]; omega)

/-- The scratch misses the frame. -/
theorem s_not_frame (g : Geo m0) {j : Nat} (hj : j < 2032) {o n : Nat} (ho : o < 205824)
    (hon : o + n ≤ 205824) :
    ¬InRange (sA m0 + BitVec.ofNat 64 o) n (base m0 2032 + BitVec.ofNat 64 j) := by
  have := g.hN; have := Geo.sp_lt m0; have hb := g.bN; have := g.hs; have := g.hss
  have e : (sA m0 + BitVec.ofNat 64 o).toNat = (sA m0).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  exact notIn (by rw [e]; omega) (by rw [hb]; omega) (by rw [e, hb]; omega)

/-- **The read-only regions** stay the same in the body. -/
theorem same_rs [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m)
    {r : Region} (hr : r ∈ [a.region, rcRegion, projectRegion, rhoRegion]) :
    Same m0.dmem m.dmem r.addr r.size := by
  have g := geo_of hpre
  obtain ⟨hS, -, -, -, -, -, -, -, -, hA⟩ := hpre
  have hnw : NativeRustcVm.NoWrap r.addr r.size := (hA.1 r (List.mem_append.mpr (.inr hr))).2
  have h0 := hA.2.2 _ List.mem_cons_self r hr
  have h1 := hA.2.2 ⟨tA m0, tstateBytes⟩ (by simp) r hr
  have h2 := hA.2.2 ⟨cA m0, claimBytes⟩ (by simp) r hr
  have h3 := hA.2.2 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩ (by simp) r hr
  have := g.hN; have := Geo.sp_lt m0; have hbn := g.bN; have := g.ht; have := g.hc; have := g.hs
  have hspn : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
  have hsb : (stackBelow m0 3648).toNat = m0.regs.SP.toNat - 3648 :=
    NativeRustcVm.toNat_sub_ofNat (by omega)
  have hb3 : (base m0 3648).toNat = m0.regs.SP.toNat - 3648 :=
    NativeRustcVm.toNat_sub_ofNat (by omega)
  unfold NativeRustcVm.NoWrap at hnw
  unfold Apart at h0 h1 h2 h3
  simp only [stackRegion, stack_eq, tstateBytes, claimBytes,
    NativeRustcVm.KeccakGkr.scratchBytes] at h0 h1 h2 h3
  rw [hsb] at h0
  refine NativeRustcVm.Layout.Same.of_sameOutside hb.same fun j hj h ↦ ?_
  have hj' : r.addr.toNat + j < 2 ^ 64 := by omega
  rcases h with h | h | h | h | h
  · rw [stack_eq] at h
    exact notIn (by rw [hb3]; omega) hj' (by rw [hb3]; omega) h
  · exact notIn (by rw [hbn]; omega) hj' (by rw [hbn]; omega) h
  · exact notIn (by simp only [tstateBytes]; omega) hj' (by simp only [tstateBytes]; omega) h
  · exact notIn (by simp only [claimBytes]; omega) hj' (by simp only [claimBytes]; omega) h
  · exact notIn (by rw [g.sa (by omega)]; omega) hj' (by rw [g.sa (by omega)]; omega) h

/-- **Bytes copied**: what `memcpy` wrote at `t` holds the bytes the source held. -/
theorem bytes_copy {d d' : DataMem} {src dst : BitVec 64} {n o : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d (src + BitVec.ofNat 64 o) bs)
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src n)) (hle : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (dst + BitVec.ofNat 64 o) bs := by
  intro i hi
  have := hc (o + i) (by simp [NativeRustcArm.bytesOf]; omega)
  rw [NativeRustcVm.addr_add_add, this]
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
  rw [← NativeRustcVm.addr_add_add, h i hi, Option.getD_some]

/-- **A `Buf<EW, N>` copied.** -/
theorem BufEWAt.copy {d d' : DataMem} {src dst : BitVec 64} {N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d src N xs)
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src (8 + 16 * N))) :
    NativeRustcVm.BufEWAt d' dst N xs := by
  obtain ⟨hl, hw, he⟩ := h
  refine ⟨hl, ?_, ?_⟩
  · have := bytes_copy (o := 0) (by rw [NativeRustcVm.addr_add_zero]; exact hw) hc
      (by rw [NativeRustcVm.length_wordBytes]; omega)
    rwa [NativeRustcVm.addr_add_zero] at this
  · exact bytes_copy (o := 8) he hc (by rw [NativeRustcVm.length_ewsBytes]; omega)

/-- An element's sum, limb by limb. -/
theorem ew_add (x y : EW) : x + y = ⟨x.c0 ^^^ y.c0, x.c1 ^^^ y.c1⟩ := rfl

/-- The decoded area's addresses. -/
theorem dec_geo [Labels] (hpre : VerifyLayerPre a s c m0) :
    a.words.toNat + 8 * a.len ≤ 2 ^ 64 ∧
      (a.words.toNat + 8 * a.len ≤ m0.regs.SP.toNat - 3648 ∨ m0.regs.SP.toNat ≤ a.words.toNat) ∧
      (a.words.toNat + 8 * a.len ≤ (cA m0).toNat ∨ (cA m0).toNat + 768 ≤ a.words.toNat) ∧
      (a.words.toNat + 8 * a.len ≤ (sA m0).toNat ∨ (sA m0).toNat + 205824 ≤ a.words.toNat) := by
  have g := geo_of hpre
  obtain ⟨hS, -, -, -, -, -, -, -, -, hA⟩ := hpre
  have hm : a.region ∈ [a.region, rcRegion, projectRegion, rhoRegion] := List.mem_cons_self
  have hnw := (hA.1 _ (List.mem_append.mpr (.inr hm))).2
  have h0 := hA.2.2 _ List.mem_cons_self _ hm
  have h2 := hA.2.2 ⟨cA m0, claimBytes⟩ (by simp) _ hm
  have h3 := hA.2.2 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩ (by simp) _ hm
  have := g.hN
  have hspn : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
  have hsb : (stackBelow m0 3648).toNat = m0.regs.SP.toNat - 3648 :=
    NativeRustcVm.toNat_sub_ofNat (by omega)
  unfold NativeRustcVm.NoWrap at hnw
  unfold Apart at h0 h2 h3
  simp only [stackRegion, stack_eq, claimBytes, NativeRustcVm.KeccakGkr.scratchBytes,
    NativeRustcVm.Transcript.DecArea.region] at h0 h2 h3 hnw
  rw [hsb] at h0
  refine ⟨hnw, by omega, by omega, by omega⟩

/-- The `TState` kept by a call from the body whose outputs miss it and its decoded area. -/
theorem tstate_keep [Labels] (hpre : VerifyLayerPre a s c m0) {m m' : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {n : Nat} (hn : n ≤ 1616) {W : BitVec 64 → Prop}
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m n) n q ∨ W q)
    (hk : Kept m.dmem m'.dmem)
    (hW : ∀ q, W q → ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q)
    {s' : TState} (h : NativeRustcVm.Transcript.TStateAt m.dmem (tA m0) a s') :
    NativeRustcVm.Transcript.TStateAt m'.dmem (tA m0) a s' := by
  have g := geo_of hpre
  obtain ⟨hw, hws, -, -⟩ := dec_geo hpre
  refine NativeRustcVm.Transcript.TStateAt.frame h hk (fun q hq ↦ ?_) hs
  rcases hq with hq | hq
  · have hst := g.stk hsp hn
    have := g.hN; have := g.ht; have := g.hts; have := Geo.sp_lt m0
    rw [Sym.inRange_iff (by rw [hst]; omega), hst] at hq
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have h' : InRange (tA m0) 760 q := h
      rw [Sym.inRange_iff (by omega)] at h'
      omega
    · have h' : InRange a.words (8 * a.len) q := h
      rw [Sym.inRange_iff hw] at h'
      omega
  · exact hW q hq

/-- The writes of a callee: its stack and its regions. -/
theorem writes_split [Labels] {m m' : MachineData} {n : Nat} {ws : List Region}
    (h : Writes m m' n ws) :
    SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m n) n q ∨ NativeRustcVm.InAny ws q :=
  NativeRustcVm.SameOutside.mono h fun q ⟨r, hr, hq⟩ ↦ by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact .inl hq
    · exact .inr ⟨r, hr, hq⟩

/-- A range of the scratch's `layerRegion` is an output. -/
theorem in_layer (g : Geo m0) {o n : Nat} (h1 : 25600 ≤ o) (h2 : o + n ≤ 140288) {q : BitVec 64}
    (h : InRange (sA m0 + BitVec.ofNat 64 o) n q) : outs m0 q := by
  right; right; right
  have := g.hs
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at h
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)]
  omega

/-- The frame and the claim as an environment's regions. -/
theorem wf_claim [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m) :
    (Env.ofMachine m [(base m0 2032, 2032), (cA m0, 768)]).WF := by
  have g := geo_of hpre
  have hS := hpre.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hA⟩ := hpre
  have hcok := hA.1 ⟨cA m0, claimBytes⟩ (by simp)
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := g.hc; have := g.hcs
  refine Env.wf_of ⟨⟨fun i hi ↦ hb.kept _ ((frame_mapped hS (by decide)) i hi),
    base_noWrap (by omega)⟩, ⟨fun i hi ↦ hb.kept _ (hcok.1 i hi), hcok.2⟩, trivial⟩ ?_
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  simp only [List.mem_singleton, forall_eq]
  unfold Apart
  rw [hbN]
  omega

/-- A body's state with the claim at X19. -/
theorem match_claim19 [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m)
    (hx : m.regs.X19 = m0.regs.X3) :
    Match (Env.ofMachine m [(base m0 2032, 2032), (cA m0, 768)]) claim19S m :=
  match_ofMachine (sregions := [(2032, true), (768, false)])
    (regions := [(base m0 2032, 2032), (cA m0, 768)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hpre.1 (by decide) (by decide), rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hb.sp]; simp)
    ⟨by simp only [Sym.eval, Env.base_ofMachine_eq]
        show (m.regs.X19).toBitVec = _
        rw [hx]; simp, trivial⟩ trivial trivial trivial

/-- A body's state with the claim's address at the frame's word `136`. -/
theorem match_claimF [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m)
    (hw : NativeRustcVm.WordAt m.dmem (base m0 2032 + BitVec.ofNat 64 136) m0.regs.X3) :
    Match (Env.ofMachine m [(base m0 2032, 2032), (cA m0, 768)]) claimFS m :=
  match_ofMachine (sregions := [(2032, true), (768, false)])
    (regions := [(base m0 2032, 2032), (cA m0, 768)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hpre.1 (by decide) (by decide), rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hb.sp]; simp)
    trivial trivial trivial
    ⟨by
        show Sym.eval _ (.load 0 136 8) = _
        rw [Sym.eval, fw_load rfl hw]
        simp, trivial⟩

/-- **A block writing only into the claim** keeps the body. -/
theorem Body.claimBlock [Labels] (hpre : VerifyLayerPre a s c m0) {m m' : MachineData}
    (hb : Body m0 m) {S S' : SState}
    (hm : Match (Env.ofMachine m [(base m0 2032, 2032), (cA m0, 768)]) S m)
    (hm' : Match (Env.ofMachine m [(base m0 2032, 2032), (cA m0, 768)]) S' m')
    (hsp : S'.sp = S.sp) (hw : S'.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 768)) = true) :
    Body m0 m' := by
  have g := geo_of hpre
  have := g.hN
  refine Fr.ofBlockW hb hm hm' (wf_claim hpre hb) rfl hsp (fun r hr ↦ by cases hr) rfl
    (by decide) (by rw [stack_eq]; omega) (fun p hp ↦ by have := slots_bound p hp; omega)
    fun w hwm ↦ ?_
  have h := List.all_eq_true.mp hw w hwm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  refine .inr ⟨by omega, fun b sz hb' ↦ ?_⟩
  rw [h.1] at hb'
  simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  refine ⟨h.2, fun i hi ↦ .inr (.inr (.inl ?_))⟩
  have := g.hc
  exact NativeRustcVm.inRange_add hi (by simp only [claimBytes]; omega)

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
