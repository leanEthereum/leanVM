import Rv64Verifier.Proofs.Gkr.LayerModel
import Rv64Verifier.Proofs.Gkr.OpenStart
import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Blocks.F74

/-!
# `keccak::verify_layer`: the frame, the mirror's remaining run, the exits

Compiled at `0x8000f04c` (`Blocks/F74.lean`), a 1712-byte frame `f` below the entry's `sp` (`f + k`
is `sp - (1712 - k)`). Inside the body the frame is allocated and the callee-saved registers saved
(`Base`), and the mirror's run from the entry is a remaining computation's from where the
transcript stands (`Rest`). Every exit goes through `0x8001013c` (`exit`): with `Err` when the
mirror fails (`post_err`), with the claim when it returns it (`post_ok`). The prologue and the
first `next_scalars` (`to_scalars`), whose `Err` returns (`scalars_err`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem bounds {s : MachineState} (h : VerifyLayerPre s) :
    0xa0000000 + verifyLayerStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s verifyLayerStack).toNat = (s.getReg .x2).toNat - verifyLayerStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

/-- `0x8001013c`: the saved registers back, return. -/
theorem exit {s u : MachineState} (hpre : VerifyLayerPre s) (hpc : u.pc = 0x8001013c)
    (hsp : u.getReg .x2 = s.getReg .x2 - 1712) (h : Open.Saved s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  have hb := bounds hpre
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b8001013c_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have pc := b8001013c_pc h₁
  have y2 := b8001013c_x2 h₁
  have y8 := b8001013c_x8 h₁
  have y9 := b8001013c_x9 h₁
  have y18 := b8001013c_x18 h₁
  have y19 := b8001013c_x19 h₁
  have y20 := b8001013c_x20 h₁
  have y21 := b8001013c_x21 h₁
  have y22 := b8001013c_x22 h₁
  have y23 := b8001013c_x23 h₁
  have y24 := b8001013c_x24 h₁
  have y25 := b8001013c_x25 h₁
  have y26 := b8001013c_x26 h₁
  have y27 := b8001013c_x27 h₁
  rv_eval [hsp, h.ra, h.s0, h.s1, h.s2, h.s3, h.s4, h.s5, h.s6, h.s7, h.s8, h.s9, h.s10, h.s11]
    at pc y2 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
  refine ⟨t, hr, by rw [pc, returnAddress_eq], ?_, b8001013c_mem_same h₁⟩
  exact preserves_of y2 y8 y9 y18 y19 fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-! ## The body's state -/

/-- What `verify_layer` may write: `TFrame`'s ranges. -/
@[rv_addr] def LW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 96 ∨ Within a (s.getReg .x11 + 8) 344 ∨
    Within a (stackLo s verifyLayerStack) verifyLayerStack ∨ Within a nextAddr 8 ∨ Fresh s t a

/-- Inside the body: the frame allocated, the registers saved, what changed among `LW`. -/
structure Base (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 1712
  saved : Open.Saved s u
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (LW s u)

/-- The mirror. -/
def mir (s : MachineState) : TM KeccakClaim :=
  verifyLayerRust (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s))

/-- The mirror's run from the entry is `k`'s from where the transcript at `u` stands. -/
def Rest (s u : MachineState) (k : TM KeccakClaim) : Prop :=
  ∀ T, TranscriptAt s (s.getReg .x11) T →
    ∃ T', TranscriptAt u (s.getReg .x11) T' ∧ (mir s).run T = k.run T'

/-- The mirror fails. -/
def Fails (s : MachineState) : Prop := ∀ T, TranscriptAt s (s.getReg .x11) T → (mir s).run T = none

variable {α : Type}

theorem Rest.start (s : MachineState) : Rest s s (mir s) := fun T hT ↦ ⟨T, hT, rfl⟩

theorem Rest.step {s u v : MachineState} {m : TM α} {f : α → TM KeccakClaim} {x : α}
    (h : Rest s u (m >>= f))
    (hc : ∀ T, TranscriptAt u (s.getReg .x11) T →
      ∃ T', m.run T = some (x, T') ∧ TranscriptAt v (s.getReg .x11) T') : Rest s v (f x) := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  obtain ⟨T₂, e₂, hT₂⟩ := hc T₁ hT₁
  exact ⟨T₂, hT₂, e₁.trans (run_bind_some e₂)⟩

theorem Rest.fail {s u : MachineState} {m : TM α} {f : α → TM KeccakClaim}
    (h : Rest s u (m >>= f)) (hc : ∀ T, TranscriptAt u (s.getReg .x11) T → m.run T = none) :
    Fails s := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  exact e₁.trans (run_bind_none (hc T₁ hT₁))

theorem Rest.keep {s u v : MachineState} {k : TM KeccakClaim} (h : Rest s u k)
    (hk : ∀ T, TranscriptAt u (s.getReg .x11) T → TranscriptAt v (s.getReg .x11) T) :
    Rest s v k := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  exact ⟨T₁, hk T₁ hT₁, e₁⟩

theorem Rest.require_pass {s u : MachineState} {c : Prop} [Decidable c] {k : TM KeccakClaim}
    (h : Rest s u (TM.require c >>= fun _ ↦ k)) (hc : c) : Rest s u k := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  refine ⟨T₁, hT₁, e₁.trans ?_⟩
  rw [run_require]; simp only [hc, ↓reduceIte]

theorem Rest.require_fail {s u : MachineState} {c : Prop} [Decidable c] {k : TM KeccakClaim}
    (h : Rest s u (TM.require c >>= fun _ ↦ k)) (hc : ¬ c) : Fails s := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  rw [e₁, run_require]; simp only [hc, ↓reduceIte]

theorem Rest.congr {s u : MachineState} {k k' : TM KeccakClaim} (h : Rest s u k) (e : k = k') :
    Rest s u k' := e ▸ h

/-! ## Memory-equal states -/

theorem transcriptAt_congr {u t : MachineState} (h : ∀ a, t.getMem a = u.getMem a) {p : Word}
    {T : TState} (hT : TranscriptAt u p T) : TranscriptAt t p T := by
  obtain ⟨h1, h2, h3, h4⟩ := hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h1]; simp only [streamPtr, streamLen, proofAt, vecPtr, vecLen, eListAt, eAt, h]
  · rw [← h2]; simp only [spongeAt, stateAt, pendingAt, nPending, eAt, h]
  · rw [← h3, h]
  · rw [← h4, h]

theorem newVecE_congr {s u t : MachineState} (h : ∀ a, t.getMem a = u.getMem a) {a : Word}
    {xs : List E} (hv : NewVecE s u a xs) : NewVecE s t a xs := by
  obtain ⟨⟨hr, hl⟩, hb, he⟩ := hv
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa only [RawVecOk, Buf, heapNext, vecPtr, vecCap, h] using hr
  · simpa only [vecLen, vecCap, h] using hl
  · simpa only [NewBuf, heapNext, vecPtr, vecCap, h] using hb
  · rw [← he]; simp only [vecEs, vecPtr, vecLen, eListAt, eAt, h]

theorem claimOut_congr {s u t : MachineState} (h : ∀ a, t.getMem a = u.getMem a) {a : Word}
    {c : KeccakClaim} (hc : ClaimOut s u a c) : ClaimOut s t a c :=
  ⟨newVecE_congr h hc.mu, newVecE_congr h hc.point, newVecE_congr h hc.weights,
    by rw [← hc.value]; simp only [eAt, h]⟩

/-! ## The exits' contract -/

theorem lw_mono {s u t : MachineState} (hN : heapNext u ≤ heapNext t) {a : Word} (h : LW s u a) :
    LW s t a := by
  simp only [LW, Fresh] at h ⊢
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩)))

theorem post_err {s u t : MachineState} (B : Base s u) (hcap : u.getMem (s.getReg .x10) = errNiche)
    (hf : Fails s) (hsame : ∀ a, t.getMem a = u.getMem a) : VerifyLayerPost s t := by
  have hN : heapNext t = heapNext u := by simp only [heapNext, hsame]
  refine ⟨⟨by rw [hN]; exact B.heap.lo, by rw [hN]; exact B.heap.hi⟩, by rw [hN]; exact B.mono,
    fun T hT ↦ ?_, (B.frame.trans (DFrame.of_same hsame _) fun _ h ↦ h).mono fun a h ↦
      lw_mono (le_of_eq hN.symm) h⟩
  have e := hf T hT
  simp only [mir] at e
  rw [e]
  show t.getMem (s.getReg .x10) = _
  rw [hsame, hcap]

theorem post_ok {s u t : MachineState} (B : Base s u) {c : KeccakClaim}
    (hcap : u.getMem (s.getReg .x10) ≠ errNiche) (hr : Rest s u (pure c))
    (hc : ClaimOut s u (s.getReg .x10) c) (hsame : ∀ a, t.getMem a = u.getMem a) :
    VerifyLayerPost s t := by
  have hN : heapNext t = heapNext u := by simp only [heapNext, hsame]
  refine ⟨⟨by rw [hN]; exact B.heap.lo, by rw [hN]; exact B.heap.hi⟩, by rw [hN]; exact B.mono,
    fun T hT ↦ ?_, (B.frame.trans (DFrame.of_same hsame _) fun _ h ↦ h).mono fun a h ↦
      lw_mono (le_of_eq hN.symm) h⟩
  obtain ⟨T', hT', e⟩ := hr T hT
  simp only [mir] at e
  rw [e]
  refine ⟨?_, claimOut_congr hsame hc, transcriptAt_congr hsame hT'⟩
  show t.getMem (s.getReg .x10) ≠ _
  rw [hsame]; exact hcap

/-! ## What the body keeps -/

/-- Bytes apart from the result, the sponge and the stack, and outside the free heap, miss `LW`. -/
theorem missLW {s u : MachineState} (hu : HeapOk u) {lo : Word} {n : Nat}
    (h0 : Apart lo n (s.getReg .x10) 96) (h1 : Apart lo n (s.getReg .x11 + 8) 344)
    (h2 : Apart lo n (stackLo s verifyLayerStack) verifyLayerStack) (h3 : Outside s lo n)
    (hn : lo.toNat + n ≤ 2 ^ 64) : Misses (LW s u) lo n := fun y hy h ↦ by
  have := hu.hi
  obtain ⟨f1, f2⟩ := h3
  simp only [LW] at h
  rcases h with h | h | h | h | h <;> addr_omega [hy, h, h0, h1, h2, f1, f2, hn, this]

/-- The transcript's reads miss `LW`. -/
theorem readsLW {s u : MachineState} (hpre : VerifyLayerPre s) (hu : HeapOk u) :
    Misses (LW s u) (s.getReg .x11) 8 ∧ Misses (LW s u) (proofAt s (s.getReg .x11)) 48 ∧
      Misses (LW s u) (streamPtr s (s.getReg .x11)) (24 * streamLen s (s.getReg .x11)) := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hos := hpre.outSelf
  have hss := hpre.selfStack
  have hpo := hpre.proofOut
  have hps := hpre.proofStack
  have hpa := hpre.self.apart
  refine ⟨missLW hu (by addr_omega [hos]) (by addr_omega [hS]) (by addr_omega [hss])
    ⟨by have := hpre.selfFree.1; addr_omega [this], by have := hpre.selfFree.2; addr_omega [this]⟩
    (by addr_omega [hS]), missLW hu hpo.1 hpa.1 hps.1 hpre.proofFree (by addr_omega [hP]), ?_⟩
  rcases hpre.self.stream with h0 | hB
  · intro y hy; simp only [Within, h0] at hy; omega
  · exact missLW hu hpo.2 hpa.2 hps.2 hpre.streamFree (by addr_omega [hB])

theorem Base.reads {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) :
    proofAt u (s.getReg .x11) = proofAt s (s.getReg .x11) ∧
      streamPtr u (s.getReg .x11) = streamPtr s (s.getReg .x11) ∧
      streamLen u (s.getReg .x11) = streamLen s (s.getReg .x11) := by
  obtain ⟨r1, r2, -⟩ := readsLW hpre B.heap
  exact B.frame.stream' r1 (by addr_omega [hpre.self.self]) r2 (by addr_omega [hpre.self.proof])

theorem Base.tok {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) :
    TranscriptOk u (s.getReg .x11) := by
  obtain ⟨r1, r2, -⟩ := readsLW hpre B.heap
  exact B.frame.transcriptOk hpre.self r1 r2

theorem Base.rodata {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) : RodataOk u := by
  have hrs := hpre.stack.rodata
  have hS := hpre.self.self
  have := B.heap.hi
  exact hpre.rodata.dframe B.frame fun a ha hw ↦ by
    simp only [LW] at hw
    rcases hw with hw | hw | hw | hw | hw <;>
      addr_omega [ha, hw, hrs, hpre.outRodata, hpre.selfRodata, hS, this]

/-- A block or a call whose writes lie in `LW` and miss the saved registers. -/
theorem Base.next {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 1712) (hH : HeapOk v) (hN : heapNext u ≤ heapNext v)
    {W : Word → Prop} (F : DFrame u v W)
    (hW : ∀ a, W a → LW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104) : Base s v := by
  have hb := bounds hpre
  refine ⟨hx2, B.saved.keep (by omega) fun y h1 h2 ↦ F y fun i hi hw ↦ (hW _ hw).2 ?_, hH,
    B.mono.trans hN, (B.frame.mono fun a h ↦ lw_mono hN h).trans F fun a h ↦ (hW a h).1⟩
  addr_omega [h1, h2, hi, hb]

/-- A block that writes nothing. -/
theorem Base.same {s u v : MachineState} (B : Base s u) (hx2 : v.getReg .x2 = s.getReg .x2 - 1712)
    (hm : ∀ a, v.getMem a = u.getMem a) : Base s v := by
  have hN : heapNext v = heapNext u := by simp only [heapNext, hm]
  refine ⟨hx2, ?_, ⟨by rw [hN]; exact B.heap.lo, by rw [hN]; exact B.heap.hi⟩, by rw [hN]; exact B.mono,
    (B.frame.trans (DFrame.of_same hm _) fun _ h ↦ h).mono fun a h ↦ lw_mono (le_of_eq hN.symm) h⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := B.saved
  exact ⟨by rw [hm]; exact h0, by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3,
    by rw [hm]; exact h4, by rw [hm]; exact h5, by rw [hm]; exact h6, by rw [hm]; exact h7,
    by rw [hm]; exact h8, by rw [hm]; exact h9, by rw [hm]; exact h10, by rw [hm]; exact h11,
    by rw [hm]; exact h12⟩

/-- Writes to the frame's slots, below the saved registers. -/
theorem slots_lw {s v : MachineState} (hpre : VerifyLayerPre s) {a lo : Word} {n : Nat}
    (h1 : (s.getReg .x2).toNat - 1712 ≤ lo.toNat) (h2 : lo.toNat + n + 104 ≤ (s.getReg .x2).toNat)
    (ha : Within a lo n) : LW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> addr_omega [hb, h1, h2, ha]

/-- A transcript callee's frame, its result at `f + 1712 - K`. -/
theorem tframe_lw {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) {n k : Nat}
    (K : Nat) (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    (hx11 : u.getReg .x11 = s.getReg .x11) (hK : n + 104 ≤ K) (hK' : K ≤ 1712)
    (hk : k ≤ sumcheckStack) (hH : HeapOk v) (a : Word)
    (ha : Within a (u.getReg .x10) n ∨ Within a (u.getReg .x11 + 8) 344 ∨
      Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨ Fresh u v a) :
    LW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hm := B.mono
  have := hH.hi
  rw [hx10, hx11] at ha
  simp only [stackLo, B.x2] at ha
  simp only [LW, Fresh] at ha ⊢
  unfold verifyLayerStack at hb hss hnx hab ⊢
  rcases ha with h | h | h | h | h
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb, hK, hK']))), by addr_omega [h, hb, hK, hK']⟩
  · exact ⟨Or.inr (Or.inl h), by addr_omega [h, hb, hss, hS]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb, hk]))), by addr_omega [h, hb, hk]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by addr_omega [h, hb, hnx]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))), by addr_omega [h, hb, hab, this]⟩

/-- A transcript callee's precondition, its result at `f + 1712 - K`. -/
theorem Base.tpre {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) {n k : Nat}
    (K : Nat) (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    (hx11 : u.getReg .x11 = s.getReg .x11) (hK : n ≤ K) (hK' : K ≤ 1712) (hK8 : K % 8 = 0)
    (hk : k ≤ sumcheckStack) (hk8 : k % 8 = 0) : TPre n k u := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  obtain ⟨e0, e1, e2⟩ := B.reads hpre
  obtain ⟨r1, r2, -⟩ := readsLW hpre B.heap
  have hS8 : (s.getReg .x11).toNat + 8 ≤ 2 ^ 64 := by addr_omega [hS]
  have hP48 : (proofAt s (s.getReg .x11)).toNat + 48 ≤ 2 ^ 64 := by addr_omega [hpre.self.proof]
  unfold verifyLayerStack at hb hsm hss hnx hab hrs
  have hst : RtStack u k := hpre.stack.sub 1712 B.x2 (by unfold verifyLayerStack; omega)
    (by decide) hk8 (by decide) (by decide)
  refine {
    heap := B.heap
    out := by rw [hx10]; addr_omega [hb, hsm, hK, hK', hK8]
    self := by rw [hx11]; exact B.tok hpre
    stack := hst
    outStack := by rw [hx10]; simp only [stackLo, B.x2]; addr_omega [hb, hK, hK', hk]
    selfStack := by rw [hx11]; simp only [stackLo, B.x2]; addr_omega [hss, hb, hk]
    outSelf := by rw [hx10, hx11]; addr_omega [hss, hb, hK, hK', hS]
    proofStack := by
      rw [hx11]
      refine B.frame.proofApart r1 hS8 r2 hP48 (Open.ProofApart.mono' hpre.proofStack ?_ ?_) <;>
        simp only [stackLo, B.x2] <;> addr_omega [hb, hk]
    proofOut := by
      rw [hx11, hx10]
      refine B.frame.proofApart r1 hS8 r2 hP48 (Open.ProofApart.mono' hpre.proofStack ?_ ?_) <;>
        addr_omega [hb, hK, hK']
    outFree := by rw [hx10]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx, hK, hK']
    selfFree := by rw [hx11]; exact Open.outside_mono hpre.selfFree B.mono
    proofFree := by rw [hx11, e0]; exact Open.outside_mono hpre.proofFree B.mono
    streamFree := by rw [hx11, e1, e2]; exact Open.outside_mono hpre.streamFree B.mono
    rodata := B.rodata hpre
    outRodata := by rw [hx10]; addr_omega [hrs, hb, hK, hK']
    selfRodata := by rw [hx11]; exact hpre.selfRodata }

/-- The transcript's value is kept by a frame that misses it and the proof. -/
theorem Base.tat {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) (hH : HeapOk v)
    {W : Word → Prop} (F : DFrame u v W)
    (hW : ∀ a, W a → ¬ Within a (s.getReg .x11) 368 ∧ LW s v a) {T : TState}
    (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T := by
  have hS := hpre.self.self
  obtain ⟨e0, e1, e2⟩ := B.reads hpre
  obtain ⟨-, r2, r3⟩ := readsLW hpre hH
  exact F.transcriptAt hT (B.tok hpre) (fun y hy h ↦ (hW y h).1 (by addr_omega [hy, hS]))
    (fun y hy h ↦ r2 y (by rwa [e0] at hy) (hW y h).2)
    (fun y hy h ↦ r3 y (by rwa [e1, e2] at hy) (hW y h).2)
    (fun y hy h ↦ (hW y h).1 (by addr_omega [hy, hS]))

/-! ## Calls to `mul` -/

theorem heap_vmr {a : Word} {n : Nat} (h1 : heapStart ≤ a.toNat) (h2 : a.toNat + 8 * n ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : ValidMemRange a n := fun i hi ↦ by
  simp only [heapStart, heapEnd] at h1 h2
  have e : (a + BitVec.ofNat 64 (8 * i)).toNat = a.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by omega, by omega⟩, by omega⟩

theorem slot_vmr {s : MachineState} (hpre : VerifyLayerPre s) {K n : Nat} (hK : 8 * n ≤ K)
    (hK' : K ≤ 1712) (hK8 : K % 8 = 0) : ValidMemRange (s.getReg .x2 - BitVec.ofNat 64 K) n := by
  have hb := bounds hpre
  unfold verifyLayerStack at hb
  valid_sub hpre.stack.valid [hb, hK, hK', hK8]

/-- `mul`'s precondition from the body, the result at `f + 1712 - K`. -/
theorem mul_pre {s u : MachineState} (hpre : VerifyLayerPre s) (hx2 : u.getReg .x2 = s.getReg .x2 - 1712)
    (hro : RodataOk u) (K : Nat) (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    (hK : 24 ≤ K) (hK' : K ≤ 1712) (hK8 : K % 8 = 0)
    (hl : ValidMemRange (u.getReg .x11) 3) (hlS : Apart (u.getReg .x11) 24 (s.getReg .x2 - 2736) 1024)
    (hlo : Apart (u.getReg .x10) 24 (u.getReg .x11) 24)
    (hr : ValidMemRange (u.getReg .x12) 3) (hrS : Apart (u.getReg .x12) 24 (s.getReg .x2 - 2736) 1024)
    (hro' : Apart (u.getReg .x10) 24 (u.getReg .x12) 24) : MulPre u := by
  have hb := bounds hpre
  have hrs := hpre.stack.rodata
  unfold verifyLayerStack at hb hrs
  have hlo' : stackLo u mulStack = s.getReg .x2 - 2736 := by
    simp only [stackLo, hx2, mulStack]; rv_eval []
  have hst : RtStack u mulStack := hpre.stack.sub 1712 hx2 (by unfold verifyLayerStack; decide)
    (by decide) (by decide) (by decide) (by decide)
  exact {
    out := by rw [hx10]; exact slot_vmr hpre (by omega) hK' hK8
    lhs := hl
    rhs := hr
    stack := hst.toStackOk
    outLhs := hlo
    outRhs := hro'
    outStack := by rw [hlo', hx10]; addr_omega [hb, hK, hK']
    lhsStack := by rw [hlo']; exact hlS
    rhsStack := by rw [hlo']; exact hrS
    rodata := hro
    stackRodata := by rw [hlo']; addr_omega [hb, hrs] }

/-- `mul`'s frame: the result and its stack. -/
theorem mul_frame {s u t : MachineState} (hx2 : u.getReg .x2 = s.getReg .x2 - 1712)
    (h : MulPost u t) :
    DFrame u t fun a ↦ Within a (u.getReg .x10) 24 ∨ Within a (s.getReg .x2 - 2736) 1024 := by
  have e : stackLo u mulStack = s.getReg .x2 - 2736 := by
    simp only [stackLo, hx2, mulStack]; rv_eval []
  rw [← e]
  exact DFrame.of_two h.frame

/-! ## The claim -/

theorem missClaim {s u : MachineState} (hpre : VerifyLayerPre s) (hu : HeapOk u) :
    Misses (LW s u) (lClaim s) 96 :=
  missLW hu hpre.claimOut hpre.claimSelf hpre.claimStack hpre.claimFree
    (by have := hpre.claim; addr_omega [this])

/-- The elements of one of the claim's `Vec`s (at `lClaim s + k`) miss `LW`. -/
theorem missVec {s u : MachineState} (hu : HeapOk u) {a : Word} (hR : VecRegion s a)
    (hO : VecApart s a (s.getReg .x10) 96) (hS : VecApart s a (s.getReg .x11 + 8) 344)
    (hT : VecApart s a (stackLo s verifyLayerStack) verifyLayerStack) (hF : VecOutside s a) :
    Misses (LW s u) (vecPtr s a) (24 * (vecLen s a).toNat) := by
  rcases hR with h0 | hR
  · intro y hy; simp only [Within, h0] at hy; omega
  · exact missLW hu hO hS hT hF (by addr_omega [hR])

theorem Base.keep {s u : MachineState} (B : Base s u) {lo : Word} {n : Nat}
    (hm : Misses (LW s u) lo n) (hn : lo.toNat + n ≤ 2 ^ 64) {y : Word} (h1 : lo.toNat ≤ y.toNat)
    (h2 : y.toNat + 8 ≤ lo.toNat + n) : u.getMem y = s.getMem y :=
  B.frame y (hm.bytes h1 h2 hn)

theorem Base.eListAt {s u : MachineState} (B : Base s u) {lo : Word} {n : Nat}
    (hm : Misses (LW s u) lo (24 * n)) (hn : n = 0 ∨ lo.toNat + 24 * n ≤ 2 ^ 64) :
    eListAt u lo n = eListAt s lo n := by
  rcases hn with h0 | hn
  · subst h0; rfl
  · exact B.frame.eListAt (hm.bytes (Nat.le_refl _) (Nat.le_refl _) hn)

/-! ## Blocks that write the frame's slots -/

/-- A doubleword no write of the block lands on keeps its value. -/
theorem keep_of_writes {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t) {a : Word}
    (hw : ∀ k ∈ x.writes, k.eval s ≠ a) : t.getMem a = s.getMem a :=
  h.frame a fun k hk heq ↦ hw k hk heq.symm

/-- A block writing `n` bytes of the frame's slots from `lo`. -/
theorem Base.slots {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 1712) {lo : Word} {n : Nat} (f : MemFrame u v lo n)
    (h1 : (s.getReg .x2).toNat - 1712 ≤ lo.toNat) (h2 : lo.toNat + n + 104 ≤ (s.getReg .x2).toNat) :
    Base s v := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  unfold verifyLayerStack at hb hnx
  have hN : v.getMem nextAddr = u.getMem nextAddr := f _ (by addr_omega [hb, hnx, h1, h2])
  exact B.next hpre hx2
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f)
    fun a ha ↦ slots_lw hpre h1 h2 ha

theorem Base.slots_tat {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (Bv : Base s v) {lo : Word} {n : Nat} (f : MemFrame u v lo n)
    (h1 : (s.getReg .x2).toNat - 1712 ≤ lo.toNat) (h2 : lo.toNat + n + 104 ≤ (s.getReg .x2).toNat)
    {T : TState} (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  unfold verifyLayerStack at hb hss
  exact B.tat hpre Bv.heap (DFrame.of_memFrame f) (fun a ha ↦
    ⟨by addr_omega [ha, h1, h2, hb, hss, hS], (slots_lw hpre h1 h2 ha).1⟩) hT

end Rv64Verifier.Gkr.Layer
