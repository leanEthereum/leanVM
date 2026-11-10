import Rv64Verifier.Proofs.Pcs.VsoFinalPush

/-!
# `verify_stacked_opening`'s final level: a tail round's next quadratic

With more rounds to come, `0x8000b9b8` moves the quadratic's value to `S - 464` and calls
`sumcheck_round_poly(S - 160, transcript, 3, S - 464, None)`, its `None` at `S - 384`;
`0x8000b9e8` takes its `Err` to `0x8000c084`, which returns it, or the new quadratic into
`S - 896` and `S - 808`. Either way round `i` ends at `0x8000b92c` (`TN`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `sumcheck_round_poly(3, claim, None)` into the frame, its `None` at `e`. -/
theorem callRoundPolyE (hRP : RoundPolyErrSpec) {s t : MachineState} {nx o cl e : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x8000c334)
    (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = s.getReg .x10) (hx12 : t.getReg .x12 = 3)
    (hx13 : t.getReg .x13 = cl) (hx14 : t.getReg .x14 = e) (hnone : t.getMem e = 0)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0)
    (hc : (s.getReg .x2 - 1040).toNat ≤ cl.toNat ∧ cl.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      cl.toNat % 8 = 0)
    (he : (s.getReg .x2 - 1040).toNat ≤ e.toNat ∧ e.toNat + 32 ≤ (s.getReg .x2 - 104).toNat ∧
      e.toNat % 8 = 0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a o 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
        Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t v a) ∧
      (vecCap v o = errNiche → v.getMem (o + 8) ≠ okTag) ∧
      (vecCap v o ≠ errNiche →
        VecOk v o 24 8 ∧ NewBuf t v (vecPtr v o) ((vecCap v o).toNat * 24) 8) ∧
      ∀ T, TranscriptAt t (s.getReg .x10) T →
        match (Model.TM.sumcheckRoundPoly 3 (eAt t cl) none).run T with
        | some (q, T') => vecCap v o ≠ errNiche ∧ NewVecE t v o q ∧
            TranscriptAt v (s.getReg .x10) T'
        | none => vecCap v o = errNiche)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, hro⟩ := sfacts hpre
  have hsp := hinv.sp
  have hI := hpre.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  rw [stackLo_vso, vso_stack] at hIs hPs
  simp only [ProofApart] at hPs
  obtain ⟨hTok, e0, e1, e2⟩ := trR_facts hpre hinv
  have hsu : heapNext s ≤ heapNext t := by
    have hn : heapNext t = nx.toNat := by simp only [heapNext, hinv.next]
    rw [hn]; exact hinv.mono
  have hsl : stackLo t roundPolyStack = s.getReg .x2 - 2464 := by
    simp only [stackLo, roundPolyStack, nextScalarsStack, shuntNextStack, nextScalarStack,
      absorbStack, duplexStack, keccakFStack, memStack, hsp]
    addr_omega [hb]
  have hpreR : RoundPolyPre t := {
    heap := hheap
    out := by rw [hx10]; exact stack_region hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb]) ho.2.2
    self := by rw [hx11]; exact hTok
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [hx10, hsl]; addr_omega [ho, hb]
    selfStack := by rw [hx11, hsl]; addr_omega [hIs, hb]
    outSelf := by rw [hx10, hx11]; addr_omega [ho, hIs, hb]
    proofStack := by
      rw [hx11, hsl]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [hPs.1, hb], by addr_omega [hPs.2, hb]⟩
    proofOut := by
      rw [hx11, hx10]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [hPs.1, ho, hb], by addr_omega [hPs.2, ho, hb]⟩
    outFree := by
      rw [hx10]; exact stack_outside hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb])
    selfFree := by rw [hx11]; exact outside_mono hI.free hsu
    proofFree := by rw [hx11, e0]; exact outside_mono hI.proofFree hsu
    streamFree := by rw [hx11, e1, e2]; exact outside_mono hI.streamFree hsu
    rodata := hinv.rodata' hpre
    outRodata := by rw [hx10]; addr_omega [hro, ho, hb]
    selfRodata := by rw [hx11]; exact hI.rodata
    count := by rw [hx12]; decide
    claim := by rw [hx13]; exact stack_region hpre (by addr_omega [hc, hb]) (by addr_omega [hc, hb]) hc.2.2
    eqFactor := by
      rw [hx14]; exact stack_region hpre (by addr_omega [he, hb]) (by addr_omega [he, hb]) he.2.2
    claimFree := by
      rw [hx13]; exact stack_outside hpre (by addr_omega [hc, hb]) (by addr_omega [hc, hb])
    eqFactorFree := by rw [hx14]; exact stack_outside hpre (by addr_omega [he, hb]) (by addr_omega [he, hb])
    claimStack := by rw [hx13, hsl]; addr_omega [hc, hb]
    eqFactorStack := by rw [hx14, hsl]; addr_omega [he, hb]
    claimSelf := by rw [hx13, hx11]; addr_omega [hc, hIs, hb]
    eqFactorSelf := by rw [hx14, hx11]; addr_omega [he, hIs, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, herr⟩ | hdead⟩ := hRP.call (Reaches.refl t) hpc hpreR
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have hfr := hpost.frame
  simp only [TFrame] at hfr
  rw [hx10, hx11, hsl] at hfr
  have hok := hpost.ok
  simp only [VecResult] at hok
  rw [hx10] at hok herr
  have hnone' : optEAt t (t.getReg .x14) = none := by
    rw [hx14, optEAt, ite_eq_left_of_eq_true _ _ (eq_true hnone)]
  refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr, herr, hok, fun T hT ↦ ?_⟩⟩
  have hv := hpost.value T (by rw [hx11]; exact hT)
  have h3 : ((3 : Word)).toNat = 3 := rfl
  rw [hx12, hx13, hnone', h3, hx10, hx11] at hv
  exact hv


/-- At `0x8000b92c`, round `i` done: `tf` drawn (`i + 1` of them), the target `rt` in `s10`,
`s11`, `S - 864`, the next quadratic `q` when another round comes. -/
structure TN (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (i : ℕ)
    (q tf : List E) (rt : E) : Prop extends TI OA s x u v Wl residual where
  pc : v.pc = 0x8000b92c
  ilt : i < mlF s Wl
  tfl : tf.length = i + 1
  x9 : v.getReg .x9 = x.FP
  x12 : v.getReg .x12 = BitVec.ofNat 64 (mlF s Wl)
  x18 : v.getReg .x18 = vecPtr v (s.getReg .x2 - 304)
  x19 : v.getReg .x19 = BitVec.ofNat 64 (24 * i)
  x20 : v.getReg .x20 = BitVec.ofNat 64 (i + 1)
  x21 : v.getReg .x21 = 0xffffffffffffffff
  x24 : v.getReg .x24 = s.getReg .x10
  x25 : v.getReg .x25 = s.getReg .x10 + 8
  m168 : v.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 (mlF s Wl)
  m224 : v.getMem (s.getReg .x2 - 816) = s.getReg .x10
  tail : TailV s u v tf
  trg : E.ofLimbs (BF64.ofBitVec (v.getReg .x26)) (BF64.ofBitVec (v.getReg .x27))
    (BF64.ofBitVec (v.getMem (s.getReg .x2 - 864))) = rt
  quad : i + 1 < mlF s Wl → QuadAt s v q
  value : RunsF OA s v (roundsK (cfgOf s) (basisOf s x) residual Wl (mlF s Wl) (i + 1) (q, tf, rt))

theorem roundsK_end (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (Wl : Model.Pcs.WhirLocals) (ml : ℕ) (st : List E × List E × E) :
    roundsK config basis residual Wl ml ml st = afterTail config basis residual Wl st.2.1 st.2.2 := by
  unfold roundsK
  rw [Nat.sub_self]
  simp only [Model.Pcs.TM.forRange, pure_bind]

/-- The last round's end. -/
theorem tLast {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} {i : ℕ} {q tf : List E}
    {c : E} (hq : TQ OA s x u v Wl residual i q tf c) (hpc : v.pc = 0x8000b92c)
    (hlast : i + 1 = mlF s Wl) :
    TN OA s x u v Wl residual i q (tf ++ [c]) (Model.polyEvalRust q c) where
  toTI := hq.toTI
  pc := hpc
  ilt := by omega
  tfl := by rw [List.length_append, hq.tfl]; rfl
  x9 := hq.x9
  x12 := hq.x12
  x18 := hq.x18
  x19 := hq.x19
  x20 := hq.x20
  x21 := hq.x21
  x24 := hq.x24
  x25 := hq.x25
  m168 := hq.m168
  m224 := hq.m224
  tail := hq.tail
  trg := hq.trg
  quad := fun h ↦ absurd h (by omega)
  value := by
    have hv := hq.value
    rw [sampledK_last _ _ _ _ hlast] at hv
    rw [hlast, roundsK_end]
    exact hv

/-- `0x8000b9b8`: the next quadratic, or its `Err` returned. -/
theorem tPoly (hRP : RoundPolyErrSpec) {OA : MachineState → Word → Model.TState → Prop}
    {s : MachineState} {x : LCtx} {u v : MachineState} {Wl : Model.Pcs.WhirLocals}
    {residual : List E} {i : ℕ} {q tf : List E} {c : E} (hpre : VsoPre s)
    (hq : TQ OA s x u v Wl residual i q tf c) (hpc : v.pc = 0x8000b9b8)
    (hmore : i + 1 < mlF s Wl) :
    ∃ w, Reaches Image.code v w ∧ (FailR s w ∨
      ∃ q', TN OA s x u w Wl residual i q' (tf ++ [c]) (Model.polyEvalRust q c)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hst.above
  rw [stackLo_vso] at hab
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hsp := hq.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b9b8_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000b9b8_keeps h₁
  have X₁ : DFrame v t₁ fun a ↦ Within a (s.getReg .x2 - 464) 88 := by
    have := DFrame.of_memFrame (b8000b9b8_frame h₁ (by rw [hsp]; addr_omega [hb]))
    rw [hsp] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  obtain ⟨T₁, n₁⟩ := hq.toTI.stepS hpre X₁ (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])))
    (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₁.sp
  have pe₁ : eAt t₁ (s.getReg .x2 - 464) = Model.polyEvalRust q c := by
    rw [← hq.trg]
    have m0 := b8000b9b8_m_x2_576 h₁
    have m1 := b8000b9b8_m_x2_584 h₁
    have m2 := b8000b9b8_m_x2_592 h₁
    rw [hsp] at m0 m1 m2
    unfold eAt
    rw [show s.getReg .x2 - 464 = s.getReg .x2 - BitVec.ofNat 64 1040 + 576 by addr_omega [hb],
      show s.getReg .x2 - BitVec.ofNat 64 1040 + 576 + 8 = s.getReg .x2 - BitVec.ofNat 64 1040 + 584 by
        addr_omega [hb],
      show s.getReg .x2 - BitVec.ofNat 64 1040 + 576 + 16 = s.getReg .x2 - BitVec.ofNat 64 1040 + 592 by
        addr_omega [hb], m0, m1, m2,
      show s.getReg .x2 - BitVec.ofNat 64 1040 + 176 = s.getReg .x2 - 864 by addr_omega [hb]]
  have hnone : t₁.getMem (s.getReg .x2 - 384) = 0 := by
    have := b8000b9b8_m_x2_656 h₁
    rw [hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 656 = s.getReg .x2 - 384 by
      addr_omega [hb]] at this
    exact this
  obtain ⟨t₂, r₂, hv₂⟩ := callRoundPolyE (o := s.getReg .x2 - 160) (cl := s.getReg .x2 - 464)
    (e := s.getReg .x2 - 384) hRP hpre (T₁.inv hpre) T₁.heap (b8000b9b8_pc h₁)
    (by rw [b8000b9b8_x10 h₁, hsp]; addr_omega [hb]) (by rw [b8000b9b8_x11 h₁, hq.x24])
    (b8000b9b8_x12 h₁) (by rw [b8000b9b8_x13 h₁, hsp]; addr_omega [hb])
    (by rw [b8000b9b8_x14 h₁, hsp]; addr_omega [hb]) hnone (by addr_omega [hb]) (by addr_omega [hb])
    (by addr_omega [hb])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, herr, hok, hval⟩
  · exact ⟨t₂, r₁.trans r₂, Or.inl (Or.inl hd)⟩
  have hhi₂ := hheap₂.hi
  simp only [heapEnd] at hab hhi₂
  have T₂ : TI OA s x u t₂ Wl residual := T₁.trans X₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp only [W]; addr_omega [ha, hS])))))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_trans T₁.mono ha.1, ha.2⟩)))))
    hheap₂ hmono₂ (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₂.sp
  have kw (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat ∨ (s.getReg .x2 - 376).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 160).toNat) : t₂.getMem y = v.getMem y := by
    rw [X₂.word (fun a ha hx ↦ by
      rcases hx with hx | hx | hx | hx | hx <;> rcases hy with hy | hy
      all_goals first
        | addr_omega [ha, hx, hy, hb]
        | addr_omega [ha, hx, hy, hb, hIs, hS]
        | addr_omega [ha, hx, hy, hb, hnx]
        | (simp only [Fresh] at hx; addr_omega [ha, hx.2, hy, hb, hhi₂, hab]))
      (by rcases hy with hy | hy <;> addr_omega [hy, hb])]
    exact X₁.word (fun a ha hx ↦ by rcases hy with hy | hy <;> addr_omega [ha, hx, hy, hb])
      (by rcases hy with hy | hy <;> addr_omega [hy, hb])
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000b9e8_spec
    (by rw [hpc₂, returnAddress_eq, b8000b9b8_x1 h₁]; decide) (by
      rv_eval [sp₂]; and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000b9e8_keeps h₃
  have X₃ : DFrame t₂ t₃ fun a ↦ Within a (s.getReg .x2 - 896) 8 ∨
      Within a (s.getReg .x2 - 808) 8 :=
    (holds_dframe h₃).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000b9e8, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp₂] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (by addr_omega [hw, hb])
  obtain ⟨T₃, n₃⟩ := T₂.stepS hpre X₃ (fun a ha ↦ by
    rcases ha with ha | ha <;> exact Or.inl (by addr_omega [ha, hb])) (k₃ .x2 (by decide))
  have hcap : t₂.getMem (t₂.getReg .x2 + 880) = vecCap t₂ (s.getReg .x2 - 160) := by
    rw [sp₂]; simp only [vecCap]; rv_eval []
  have hx21 : t₂.getReg .x21 = errNiche := by
    rw [hpres₂ .x21 (by decide), k₁ .x21 (by decide), hq.x21]; rfl
  by_cases he : vecCap t₂ (s.getReg .x2 - 160) = errNiche
  · -- the `Err`, returned
    obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000ba04_spec
      (b8000b9e8_pc_not_taken h₃ (by rw [hcap, he, hx21])) trivial
    have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₃.sp
    obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b8000c084_spec (b8000ba04_pc h₄) (by
      rv_eval [b8000ba04_keeps h₄ .x2 (by decide), sp₃]
      and_intros <;> valid_access hst.valid [hb])
    have hm (a : Word) : t₅.getMem a = t₃.getMem a := by
      rw [b8000c084_mem_same h₅, b8000ba04_mem_same h₄]
    have inv₅ : InvR s t₅ (t₃.getMem nextAddr) := Inv.same' (T₃.inv hpre) hm (by
      rw [b8000c084_keeps h₅ .x2 (by decide), b8000ba04_keeps h₄ .x2 (by decide)])
    obtain ⟨w, rw', hw⟩ := fail844 inv₅ (b8000c084_pc h₅) (by
      rw [b8000c084_x1 h₅, b8000ba04_keeps h₄ .x2 (by decide), sp₃,
        show s.getReg .x2 - BitVec.ofNat 64 1040 + 144 = s.getReg .x2 - 896 by addr_omega [hb],
        b8000ba04_mem_same h₄]
      have m := b8000b9e8_m_x2_144 h₃
      rw [sp₂, show s.getReg .x2 - BitVec.ofNat 64 1040 + 144 = s.getReg .x2 - 896 by
        addr_omega [hb], show s.getReg .x2 - BitVec.ofNat 64 1040 + 888 = s.getReg .x2 - 160 + 8 by
        addr_omega [hb]] at m
      rw [m]
      exact herr he)
    exact ⟨w, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans rw')))), Or.inl hw⟩
  -- the next quadratic
  have pc₃ : t₃.pc = 0x8000b92c :=
    b8000b9e8_pc_taken h₃ (by rw [hcap, hx21]; exact he)
  obtain ⟨hvo, hnb⟩ := hok he
  have hn₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, n₃]
  have k3w (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 896).toNat ∨ (s.getReg .x2 - 888).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 808).toNat ∨ (s.getReg .x2 - 800).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) : t₃.getMem y = t₂.getMem y :=
    X₃.word (fun a ha hx ↦ by
      rcases hy with hy | hy | hy <;> rcases hx with hx | hx <;> addr_omega [ha, hx, hy, hb])
      (by rcases hy with hy | hy | hy <;> addr_omega [hy, hb])
  have hX₂h (a : Word) (ha : Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a) :
      ¬ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext t₁) := by
    have hh1 := T₁.heap.hi
    simp only [heapEnd] at hh1
    rcases ha with ha | ha | ha | ha | ha
    · exact SS.heap hpre (Or.inr (Or.inl (by addr_omega [ha, hb]))) T₁.heap.hi
    · exact SS.heap hpre (Or.inr (Or.inr (Or.inr (by simp only [W]; addr_omega [ha, hS]))))
        T₁.heap.hi
    · exact SS.heap hpre (Or.inr (Or.inr (Or.inl ha))) T₁.heap.hi
    · intro ⟨h1, h2⟩; addr_omega [ha, h2, hh1, hnx, hab, hb]
    · intro ⟨_, h2⟩; simp only [Fresh] at ha; omega
  have tail₃ : TailV s u t₃ (tf ++ [c]) := by
    have t₁' := hq.tail.keep hq.heap hq.toTI.fin.su X₁ (fun a ha hw ↦ by addr_omega [ha, hw, hb])
      (fun a ha ↦ SS.heap hpre (Or.inr (Or.inl (by addr_omega [ha, hb]))) hq.heap.hi)
      (by addr_omega [hb]) (by simp only [heapNext, n₁]; rfl)
    have t₂' := t₁'.keep T₁.heap T₁.fin.su X₂ (fun a ha hw ↦ by
        rcases ha with ha | ha | ha | ha | ha
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb, hIs, hS]
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb, hnx]
        · simp only [Fresh] at ha; addr_omega [ha.2, hw, hb, hhi₂, hab])
      hX₂h (by addr_omega [hb]) hmono₂
    exact t₂'.keep T₂.heap T₂.fin.su X₃ (fun a ha hw ↦ by
        rcases ha with ha | ha <;> addr_omega [ha, hw, hb])
      (fun a ha ↦ SS.heap hpre (by rcases ha with ha | ha <;> exact Or.inl (by addr_omega [ha, hb]))
        T₂.heap.hi) (by addr_omega [hb]) (by rw [hn₃])
  have hreg (r : Reg) (h3 : t₃.getReg r = t₂.getReg r) (h2 : r ∈ calleeSaved)
      (h1 : t₁.getReg r = v.getReg r) : t₃.getReg r = v.getReg r := by
    rw [h3, hpres₂ r h2, h1]
  have hraw := hvo.raw
  have hlc := hvo.len
  simp only [RawVecOk, Buf] at hraw
  have hP : t₃.getMem (s.getReg .x2 - 896) = vecPtr t₂ (s.getReg .x2 - 160) := by
    have m := b8000b9e8_m_x2_144 h₃
    rw [sp₂, show s.getReg .x2 - BitVec.ofNat 64 1040 + 144 = s.getReg .x2 - 896 by
      addr_omega [hb], show s.getReg .x2 - BitVec.ofNat 64 1040 + 888 = s.getReg .x2 - 160 + 8 by
      addr_omega [hb]] at m
    exact m
  have hL : t₃.getMem (s.getReg .x2 - 808) = vecLen t₂ (s.getReg .x2 - 160) := by
    have m := b8000b9e8_m_x2_232 h₃
    rw [sp₂, show s.getReg .x2 - BitVec.ofNat 64 1040 + 232 = s.getReg .x2 - 808 by
      addr_omega [hb], show s.getReg .x2 - BitVec.ofNat 64 1040 + 896 = s.getReg .x2 - 160 + 16 by
      addr_omega [hb]] at m
    exact m
  have hsu₁ := T₁.su
  have hhv₂ := hheap₂.hi
  simp only [heapEnd] at hhv₂
  refine ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr ⟨vecEs t₂ (s.getReg .x2 - 160), {
    toTI := T₃
    pc := pc₃
    ilt := by omega
    tfl := by rw [List.length_append, hq.tfl]; rfl
    x9 := by rw [hreg .x9 (k₃ .x9 (by decide)) (by decide) (k₁ .x9 (by decide)), hq.x9]
    x12 := by
      rw [b8000b9e8_x12 h₃, sp₂, show s.getReg .x2 - BitVec.ofNat 64 1040 + 168 = s.getReg .x2 - 872 by
        addr_omega [hb], kw _ (Or.inl (by addr_omega [hb]))]
      exact hq.m168
    x18 := by
      rw [hreg .x18 (k₃ .x18 (by decide)) (by decide) (k₁ .x18 (by decide)), hq.x18]
      simp only [vecPtr]
      rw [k3w _ (Or.inr (Or.inr (by addr_omega [hb]))), kw _ (Or.inr (by addr_omega [hb]))]
    x19 := by rw [hreg .x19 (k₃ .x19 (by decide)) (by decide) (k₁ .x19 (by decide)), hq.x19]
    x20 := by rw [hreg .x20 (k₃ .x20 (by decide)) (by decide) (k₁ .x20 (by decide)), hq.x20]
    x21 := by rw [hreg .x21 (k₃ .x21 (by decide)) (by decide) (k₁ .x21 (by decide)), hq.x21]
    x24 := by rw [hreg .x24 (k₃ .x24 (by decide)) (by decide) (k₁ .x24 (by decide)), hq.x24]
    x25 := by rw [hreg .x25 (k₃ .x25 (by decide)) (by decide) (k₁ .x25 (by decide)), hq.x25]
    m168 := by
      rw [k3w _ (Or.inr (Or.inl (by addr_omega [hb]))), kw _ (Or.inl (by addr_omega [hb]))]
      exact hq.m168
    m224 := by
      rw [k3w _ (Or.inr (Or.inl (by addr_omega [hb]))), kw _ (Or.inl (by addr_omega [hb]))]
      exact hq.m224
    tail := tail₃
    trg := by
      rw [hreg .x26 (k₃ .x26 (by decide)) (by decide) (k₁ .x26 (by decide)),
        hreg .x27 (k₃ .x27 (by decide)) (by decide) (k₁ .x27 (by decide)),
        k3w _ (Or.inr (Or.inl (by addr_omega [hb]))), kw _ (Or.inl (by addr_omega [hb]))]
      exact hq.trg
    quad := fun _ ↦ by
      refine ⟨?_, by rw [hP]; exact hraw.1, ?_⟩
      · rw [hP, hL]
        refine DFrame.eList X₃ (fun y hy hx ↦ ?_) ?_
        · rcases hnb.2 with h0 | h0
          · simp only [Within] at hy; omega
          · rcases hx with hx | hx <;> simp only [Within] at hy <;>
              addr_omega [hy.1, hy.2, hx, hb, h0.2, hhv₂, hab, hlc]
        · rcases hnb.2 with h0 | h0
          · left; omega
          · right; omega
      · rw [hP, hL, hn₃]
        rcases hnb.2 with h0 | h0
        · left; omega
        · right; exact ⟨by omega, by omega⟩
    value := ?_ }⟩⟩
  refine hq.value.step fun T hT ↦ ?_
  have hT₁ := tr_keep hpre (hq.toTI.inv hpre) hT X₁ fun a ha ↦ Or.inl (by addr_omega [ha, hb])
  have hv := hval T hT₁
  rw [pe₁] at hv
  rw [sampledK_more _ _ _ _ hmore]
  cases hr : (Model.TM.sumcheckRoundPoly 3 (Model.polyEvalRust q c) none).run T with
  | none => rw [hr] at hv; exact absurd hv he
  | some p =>
    obtain ⟨q'', T'⟩ := p
    rw [hr] at hv
    obtain ⟨-, hnew, hT'⟩ := hv
    refine ⟨T', ?_, tr_keep hpre (T₂.inv hpre) hT' X₃ fun a ha ↦ by
      rcases ha with ha | ha <;> exact Or.inl (by addr_omega [ha, hb])⟩
    rw [run_bind_of hr, hnew.elems]

end Rv64Verifier.Proofs.Pcs.Vso
