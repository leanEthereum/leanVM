import Rv64Verifier.Proofs.Pcs.VsoRunsK

/-!
# `verify_stacked_opening`'s level loop: from the opening to the Merkle checks' end

From `0x8000a790` (`Opened`): the grinding and the queries (`queriesU`, to `0x8000a9d8`), `lam`
and its powers (`lamPowersU`, to `0x8000aa14`), the Merkle checks (`merkle`, to `0x8000b0dc`).
`Merkled` is the state there, the mirror past `TM.merkleLeaves` (`RunsK` at `k = 1`). The
openings' memory `VsoOpenMem` is a hypothesis, which `VsoPre` is to carry.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Level `ℓ`'s message log after its folds. -/
abbrev mlOf (s : MachineState) (Wl : Model.Pcs.WhirLocals) (lf : List E) : ℕ :=
  (s.getReg .x12).toNat - (Wl.folds ++ lf).length

/-- The leaves of the phase the Merkle checks from `w` read. -/
def wordsAt (s w : MachineState) : List (List K) :=
  (phaseAt w (proofAt w (s.getReg .x10)) (w.getMem (s.getReg .x10 + 352)).toNat).map (·.leaf)

/-- At `0x8000b0dc`, level `ℓ`'s Merkle checks passed: opened at `u`, the queries `qs` drawn at
`v`, `lam` at `w`, the checks' end `m`. -/
structure Merkled (s : MachineState) (x : LCtx) (h t u v w m : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q res : List E)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (d : Digest) (qs : List Word) : Prop where
  op : Opened s x h t u ℓ Wl lf q res pend d
  qo : QOut s u v (mlOf s Wl lf + rtOf s ℓ) qs
  cnt : (cfgOf s).queries[ℓ]? = some qs.length
  lo : ∃ T, LamOut s v w T
  mi : MerkleIn s w ℓ (fcOf s ℓ)
  mo : MerkleOut s w m ℓ (fcOf s ℓ)
  qsw : w.readWords (w.getMem (s.getReg .x2 - 824)) (w.getReg .x26).toNat = qs
  value : RunsK s m ℓ 1 (Model.Pcs.afterWords (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ
    (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf res pend (eAt w (s.getReg .x2 - 384)) qs
    (wordsAt s w)) (nextRoots s ℓ d)
  /-- The residual's buffer and length, spilled by the grinding. -/
  rs : v.getMem (s.getReg .x2 - 968) = u.getReg .x1 ∧ v.getMem (s.getReg .x2 - 960) = u.getReg .x31

/-- The level's query depth fits a shift. -/
theorem mr_lt {s : MachineState} {QP QL : Word} (hc : Cfg s QP QL) {ℓ : ℕ} (hlt : ℓ < K0 s + 2)
    (Wl : Model.Pcs.WhirLocals) (lf : List E) : mlOf s Wl lf + rtOf s ℓ < 64 := by
  have hr : rtOf s ℓ ≤ (s.getReg .x13).toNat + 3 * (K0 s + 1) := by
    simp only [rtOf, Model.Pcs.ladderRates]
    cases ℓ with
    | zero => simp
    | succ i =>
      simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      omega
  have := hc.rate
  have := hc.logN
  simp only [mlOf, K0] at hr ⊢
  omega

/-- The slots the queries keep. -/
theorem QOut.keep {s u v : MachineState} {dd : ℕ} {qs : List Word} (hpre : VsoPre s)
    (hq : QOut s u v dd qs) (o : ℕ) (ho : o = 856 ∨ o = 840 ∨ o = 784 ∨ o = 792) :
    v.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := (hq.inv.heap hpre.heap).hi
  refine hq.fr _ fun i hi hw ↦ ?_
  rcases hw with (hw | hw | hw | hw) | (hw | hw | hw | hw | hw | hw | hw)
  · simp only [W] at hw; rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hS, hIs, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · simp only [W] at hw; rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hS, hIs, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb, hnx]
  · simp only [Fresh] at hw; rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw.2, hi, hb, hhi]

/-- The slots `lam` keeps. -/
theorem LamOut.keep {s v w : MachineState} {T : Model.TState} (hpre : VsoPre s)
    (hl : LamOut s v w T) (o : ℕ) (ho : o = 856 ∨ o = 840 ∨ o = 784) :
    w.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 o) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := (hl.inv.heap hpre.heap).hi
  refine hl.fr _ fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hS, hIs, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb, hnx]
  · simp only [Fresh] at hw; rcases ho with rfl | rfl | rfl <;> addr_omega [hw.2, hi, hb, hhi]

/-- The root misses what the queries write. -/
theorem QOut.root {s u v : MachineState} {dd : ℕ} {qs : List Word} (hpre : VsoPre s)
    (hinv : InvR s u (u.getMem nextAddr)) (hq : QOut s u v dd qs) :
    digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11) := by
  have hb := bounds hpre
  have hrs := hpre.rootSponge
  have hst := hpre.root.stack
  have hf := hpre.root.free
  rw [stackLo_vso, vso_stack] at hst
  simp only [Outside] at hf
  have hlo : heapNext s ≤ heapNext u := hinv.mono
  refine digest_keep hq.fr (root_bound hpre) fun y hy hw ↦ ?_
  rcases hw with (hw | hw | hw | hw) | (hw | hw | hw | hw | hw | hw | hw)
  · simp only [W] at hw; addr_omega [hy, hw, hrs]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · simp only [W] at hw; addr_omega [hy, hw, hrs]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hf.2]
  · simp only [Fresh] at hw
    rcases hf.1 with h1 | h1
    · addr_omega [hy, hw.1, h1, hlo]
    · addr_omega [hy, hw.2, h1, (hq.inv.heap hpre.heap).hi]

/-- The root misses what `lam` writes. -/
theorem LamOut.root {s v w : MachineState} {T : Model.TState} (hpre : VsoPre s)
    (hinv : InvR s v (v.getMem nextAddr)) (hl : LamOut s v w T) :
    digestAt w (s.getReg .x11) = digestAt v (s.getReg .x11) := by
  have hb := bounds hpre
  have hrs := hpre.rootSponge
  have hst := hpre.root.stack
  have hf := hpre.root.free
  rw [stackLo_vso, vso_stack] at hst
  simp only [Outside] at hf
  have hlo : heapNext s ≤ heapNext v := hinv.mono
  refine digest_keep hl.fr (root_bound hpre) fun y hy hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw
  · addr_omega [hy, hw, hrs]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hst, hb]
  · addr_omega [hy, hw, hf.2]
  · simp only [Fresh] at hw
    rcases hf.1 with h1 | h1
    · addr_omega [hy, hw.1, h1, hlo]
    · addr_omega [hy, hw.2, h1, (hl.inv.heap hpre.heap).hi]

/-- The queries' buffer, allocated since `u`: read where `lam` left it, and `Clear`. -/
theorem qbuf {s u v w : MachineState} {dd : ℕ} {qs : List Word} {T : Model.TState}
    (hpre : VsoPre s) (hu : HeapOk u) (hinv : InvR s u (u.getMem nextAddr))
    (hq : QOut s u v dd qs) (hl : LamOut s v w T) :
    w.readWords (w.getMem (s.getReg .x2 - 824)) (w.getReg .x26).toNat = qs ∧
    ((w.getReg .x26).toNat = 0 ∨
      Region (w.getMem (s.getReg .x2 - 824)) (8 * (w.getReg .x26).toNat) ∧
        Clear s (heapNext w) (w.getMem (s.getReg .x2 - 824)) (8 * (w.getReg .x26).toNat)) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsm := stack_mapped hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIf := hpre.self.free
  simp only [Outside] at hIf
  have hlo : heapNext s ≤ heapNext u := hinv.mono
  have hvhi := (hq.inv.heap hpre.heap).hi
  have hwhi := (hl.inv.heap hpre.heap).hi
  have hmw := hl.mono
  have hP : w.getMem (s.getReg .x2 - 824) = vecPtr v (s.getReg .x2 - 464) := by
    rw [hl.qp, hq.x1]
  obtain ⟨hal, hbuf⟩ := hq.vec.buf
  have hlt : qs.length < 2 ^ 64 := by
    rcases hbuf with h0 | ⟨-, h2⟩
    · omega
    · simp only [heapEnd] at hvhi; omega
  have hn : (w.getReg .x26).toNat = qs.length := by
    rw [hl.regs .x26 (by decide), hq.x26]
    exact Nat.mod_eq_of_lt hlt
  rw [hn, hP]
  rcases hbuf with h0 | ⟨h1, h2⟩
  · have e : qs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst e
    exact ⟨rfl, Or.inl rfl⟩
  have hhs := hu.lo
  have eR : w.readWords (vecPtr v (s.getReg .x2 - 464)) qs.length =
      v.readWords (vecPtr v (s.getReg .x2 - 464)) qs.length := by
    refine DFrame.readWords' hl.fr (fun a ha hw ↦ ?_) (by simp only [heapEnd] at hvhi; omega)
    rcases ha with ha | ha | ha | ha | ha | ha | ha
    · rcases hIf.1 with h | h
      · addr_omega [ha, hw, h, hS, hlo, h1]
      · addr_omega [ha, hw, h, hS, h2, hvhi]
    · addr_omega [ha, hw, hsm, h2, hvhi]
    · addr_omega [ha, hw, hsm, h2, hvhi]
    · addr_omega [ha, hw, hsm, h2, hvhi]
    · addr_omega [ha, hw, hsm, h2, hvhi]
    · addr_omega [ha, hw, h2, hvhi]
    · simp only [Fresh] at ha; addr_omega [ha.1, hw, h2]
  refine ⟨by rw [eR]; exact hq.vec.elems, Or.inr ⟨heap_region (by simp only [heapStart] at hhs; omega)
    (by omega) hal, ⟨⟨Or.inl (by omega), ?_, ?_⟩, ?_⟩⟩⟩
  · simp only [Apart]; simp only [heapEnd] at hvhi; omega
  · simp only [heapEnd] at hvhi; addr_omega [h2, hvhi]
  · rcases hIf.1 with h | h
    · simp only [Apart]; addr_omega [h, hS, hlo, h1]
    · simp only [Apart]; addr_omega [h, hS, h2, hvhi]

/-- **From the opening to the Merkle checks' end**: `0x8000a790` to `0x8000b0dc`, or an `Err`. -/
theorem levelMerkle (hD : DuplexSpec) (hA : AbsorbSpec) (hTA : TryAllocZeroedSpec)
    (hP : MultilinearContracts.PowersSpec)
    (hRF : ReserveFastSpec 0x8000c898) (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec)
    (hC : MemcmpSpec) {s : MachineState} {x : LCtx} {h t u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} (hpre : VsoPre s)
    (hOM : VsoOpenMem s (s.getReg .x10)) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (ho : Opened s x h t u ℓ Wl lf q res pend d) :
    ∃ m, Reaches Image.code u m ∧
      (FailR s m ∨ ∃ v w qs, Merkled s x h t u v w m ℓ Wl lf q res pend d qs) := by
  have hlt := ho.fo.head.lvl
  have hK0 := K0_lt s
  have hf := fcOf_eq s hlt
  have hmr := mr_lt hc hlt Wl lf
  obtain ⟨s184, s192, s200, s208, s216, s224, s240, s256⟩ := ho.slots hpre
  obtain ⟨v, r1, hv⟩ := queriesU hD hA hTA hpre hc ho.fo.head.cfg.config ho.inv ho.pc hlt hmr s184
    s240 s192 s208 ho.m168 s216 s224 ho.m248
  rcases hv with hv | ⟨cnt, qs, hcnt, hql, -, hq, hrun, hs1, hs2⟩
  · exact ⟨v, r1, Or.inl hv⟩
  obtain ⟨w, r2, hw⟩ := lamPowersU hD hP hpre hq.inv hq.pc
    ((hq.keep hpre 792 (by decide)).trans ho.m248) hq.x20
  rcases hw with hw | hl
  · exact ⟨w, r1.trans r2, Or.inl (Or.inl hw)⟩
  obtain ⟨T0, hT0⟩ := exists_TA v (s.getReg .x10)
  have hl0 := hl T0 hT0
  obtain ⟨hqsw, hqb⟩ := qbuf hpre ho.heap ho.inv hq hl0
  have kw (o : ℕ) (ho' : o = 856 ∨ o = 840 ∨ o = 784) :
      w.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
    (hl0.keep hpre o ho').trans (hq.keep hpre o (by rcases ho' with h | h | h <;> simp [h]))
  have hmi : MerkleIn s w ℓ (fcOf s ℓ) :=
    merkleIn_of hpre hOM hl0.inv hl0.pc hl0.sp (by rw [hl0.regs .x20 (by decide), hq.x20])
      ((kw 856 (by decide)).trans s184) ((kw 784 (by decide)).trans s256) (by omega)
      (by rw [hf]; split <;> omega) ((kw 840 (by decide)).trans s200) hqb (by
        have hb := bounds hpre
        obtain ⟨hnx, -⟩ := sfacts hpre
        have hS := Region.bounds hpre.self.ok.self
        have hIs := hpre.self.stack
        rw [stackLo_vso, vso_stack] at hIs
        have hhi := (hl0.inv.heap hpre.heap).hi
        rw [hl0.regs .x23 (by decide), hq.x23]
        refine (hl0.fr _ fun i hi hw ↦ ?_).symm
        rcases hw with hw | hw | hw | hw | hw | hw | hw
        · addr_omega [hw, hi, hS, hIs, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb, hnx]
        · simp only [Fresh] at hw; addr_omega [hw.2, hi, hb, hhi])
  obtain ⟨m, r3, hm⟩ := merkle hTA hRF hM hK hC hpre hmi
  rcases hm with hm | hout
  · exact ⟨m, r1.trans (r2.trans r3), Or.inl hm⟩
  refine ⟨m, r1.trans (r2.trans r3), Or.inr ⟨v, w, qs, ho, hq, hql ▸ hcnt, ⟨T0, hl0⟩, hmi, hout,
    hqsw, ?_, hs1, hs2⟩⟩
  have V0 := ho.value.toK
  rw [afterCommit_split hcnt] at V0
  have V1 : RunsK s v ℓ 0 (Model.Pcs.afterQueries (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ
      (fcOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf res pend qs) (nextRoots s ℓ d) :=
    V0.step (QOut.root hpre ho.inv hq) fun T hT ↦ by
      obtain ⟨T', hk, hT', p, r, o⟩ := hrun T hT
      exact ⟨T', by rw [bind_assoc]; exact hk _, hT', p, r, o⟩
  rw [Model.Pcs.afterQueries] at V1
  have V2 := V1.bind (eAt w (s.getReg .x2 - 384)) (LamOut.root hpre hq.inv hl0) fun T hT ↦
    ⟨_, by rw [sample_run, (hl T hT).lam], (hl T hT).tr, rfl, rfl, rfl⟩
  exact RunsK.merkle hpre hmi hout V2 hqsw (by rw [hf]; split <;> omega) hmr
    ((hl0.regs .x8 (by decide)).trans hq.x8)
    (levelShape_eq hc hlt (by rw [List.length_append, hnf, ho.fo.lfl]))

/-- **A level from its fold rounds' end to the Merkle checks' end**: `0x8000a304` to `0x8000b0dc`,
or an `Err`. -/
theorem levelFoldedMerkle (hNS : NextScalarsSpec) (hSm : SamplesSpec) (hN : NextScalarSpec)
    (hRP : RoundPolyErrSpec) (hG : GrowOneFreshSpec 0x8000c7d0 80 8) (hD : DuplexSpec)
    (hA : AbsorbSpec) (hTA : TryAllocZeroedSpec) (hP : MultilinearContracts.PowersSpec)
    (hRF : ReserveFastSpec 0x8000c898) (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec)
    (hC : MemcmpSpec) {s : MachineState} {x : LCtx} {h t : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s)
    (hOM : VsoOpenMem s (s.getReg .x10)) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (hf : Folded s x h t ℓ Wl lf q) :
    ∃ m, Reaches Image.code t m ∧ (FailR s m ∨ ∃ u v w res pend d qs,
      Merkled s x h t u v w m ℓ Wl lf q res pend d qs) := by
  obtain ⟨u, r1, hu⟩ := openLevel hNS hSm hN hRP hG hpre hc hnf hf
  rcases hu with hu | ⟨res, pend, d, ho⟩
  · exact ⟨u, r1, Or.inl hu⟩
  obtain ⟨m, r2, hm⟩ := levelMerkle hD hA hTA hP hRF hM hK hC hpre hOM hc hnf ho
  rcases hm with hm | ⟨v, w, qs, hm⟩
  · exact ⟨m, r1.trans r2, Or.inl hm⟩
  · exact ⟨m, r1.trans r2, Or.inr ⟨u, v, w, res, pend, d, qs, hm⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
