import Rv64Verifier.Proofs.Gkr.KeccakModel
import Rv64Verifier.Proofs.Gkr.LayerStart
import Rv64Verifier.Blocks.F35

/-!
# `keccak::verify_keccak`: the frame, the mirror's remaining run, the exits

Compiled at `0x80008e34` (`Blocks/F35.lean`), a 5248-byte frame `f` below the entry's `sp` (`f + k`
is `sp - (5248 - k)`). Inside the body the frame is allocated and the callee-saved registers saved
(`Base`), and the mirror's run from the entry is a remaining computation's from where the
transcript stands (`Rest`). Every exit goes through `0x80009684` (`exit`): with `Err` when the
mirror fails (`post_err`), with the openings when it returns them (`post_ok`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem bounds {s : MachineState} (h : VerifyKeccakPre s) :
    0xa0000000 + verifyKeccakStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s verifyKeccakStack).toNat = (s.getReg .x2).toNat - verifyKeccakStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

/-- `0x80009684`: the saved registers back, return. -/
theorem exit {s u : MachineState} (hpre : VerifyKeccakPre s) (hpc : u.pc = 0x80009684)
    (hsp : u.getReg .x2 = s.getReg .x2 - 5248) (h : Open.Saved s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  have hb := bounds hpre
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b80009684_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have pc := b80009684_pc h₁
  have y2 := b80009684_x2 h₁
  have y8 := b80009684_x8 h₁
  have y9 := b80009684_x9 h₁
  have y18 := b80009684_x18 h₁
  have y19 := b80009684_x19 h₁
  have y20 := b80009684_x20 h₁
  have y21 := b80009684_x21 h₁
  have y22 := b80009684_x22 h₁
  have y23 := b80009684_x23 h₁
  have y24 := b80009684_x24 h₁
  have y25 := b80009684_x25 h₁
  have y26 := b80009684_x26 h₁
  have y27 := b80009684_x27 h₁
  rv_eval [hsp, h.ra, h.s0, h.s1, h.s2, h.s3, h.s4, h.s5, h.s6, h.s7, h.s8, h.s9, h.s10, h.s11]
    at pc y2 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
  refine ⟨t, hr, by rw [pc, returnAddress_eq], ?_, b80009684_mem_same h₁⟩
  exact preserves_of y2 y8 y9 y18 y19 fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-! ## The body's state -/

/-- What `verify_keccak` may write: `TFrame`'s ranges. -/
@[rv_addr] def KW (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 96 ∨ Within a (s.getReg .x11 + 8) 344 ∨
    Within a (stackLo s verifyKeccakStack) verifyKeccakStack ∨ Within a nextAddr 8 ∨ Fresh s t a

/-- Inside the body: the frame allocated, the registers saved, what changed among `KW`. -/
structure Base (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 5248
  saved : Open.Saved s u
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (KW s u)

/-- The instance and the output. -/
def instOf (s : MachineState) : List E := eListAt s (kInst s) (kInstLen s)
def outOf (s : MachineState) : List E := eListAt s (kOutput s) (kOutputLen s)

/-- The mirror. -/
def mir (s : MachineState) : TM KeccakOpenings := verifyKeccakRust (shapeOf s) (instOf s) (outOf s)

/-- The mirror's run from the entry is `k`'s from where the transcript at `u` stands. -/
def Rest (s u : MachineState) (k : TM KeccakOpenings) : Prop :=
  ∀ T, TranscriptAt s (s.getReg .x11) T →
    ∃ T', TranscriptAt u (s.getReg .x11) T' ∧ (mir s).run T = k.run T'

/-- The mirror fails. -/
def Fails (s : MachineState) : Prop := ∀ T, TranscriptAt s (s.getReg .x11) T → (mir s).run T = none

variable {α : Type}

theorem Rest.start (s : MachineState) : Rest s s (mir s) := fun T hT ↦ ⟨T, hT, rfl⟩

theorem Rest.step {s u v : MachineState} {m : TM α} {f : α → TM KeccakOpenings} {x : α}
    (h : Rest s u (m >>= f))
    (hc : ∀ T, TranscriptAt u (s.getReg .x11) T →
      ∃ T', m.run T = some (x, T') ∧ TranscriptAt v (s.getReg .x11) T') : Rest s v (f x) := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  obtain ⟨T₂, e₂, hT₂⟩ := hc T₁ hT₁
  exact ⟨T₂, hT₂, e₁.trans (Layer.run_bind_some e₂)⟩

theorem Rest.fail {s u : MachineState} {m : TM α} {f : α → TM KeccakOpenings}
    (h : Rest s u (m >>= f)) (hc : ∀ T, TranscriptAt u (s.getReg .x11) T → m.run T = none) :
    Fails s := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  exact e₁.trans (Layer.run_bind_none (hc T₁ hT₁))

theorem Rest.keep {s u v : MachineState} {k : TM KeccakOpenings} (h : Rest s u k)
    (hk : ∀ T, TranscriptAt u (s.getReg .x11) T → TranscriptAt v (s.getReg .x11) T) :
    Rest s v k := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  exact ⟨T₁, hk T₁ hT₁, e₁⟩

theorem Rest.require_pass {s u : MachineState} {c : Prop} [Decidable c] {k : TM KeccakOpenings}
    (h : Rest s u (TM.require c >>= fun _ ↦ k)) (hc : c) : Rest s u k := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  refine ⟨T₁, hT₁, e₁.trans ?_⟩
  rw [Layer.run_require]; simp only [hc, ↓reduceIte]

theorem Rest.require_fail {s u : MachineState} {c : Prop} [Decidable c] {k : TM KeccakOpenings}
    (h : Rest s u (TM.require c >>= fun _ ↦ k)) (hc : ¬ c) : Fails s := by
  intro T hT
  obtain ⟨T₁, hT₁, e₁⟩ := h T hT
  rw [e₁, Layer.run_require]; simp only [hc, ↓reduceIte]

theorem Rest.congr {s u : MachineState} {k k' : TM KeccakOpenings} (h : Rest s u k) (e : k = k') :
    Rest s u k' := e ▸ h

/-- The mirror at the entry, after the sizes' check. -/
theorem rest_start {s : MachineState} (hpre : VerifyKeccakPre s) :
    Rest s s (TM.require ((instOf s).length = (s.getReg .x12).toNat ∧ (outOf s).length = 25 ∧
      4 ≤ (s.getReg .x12).toNat) >>= fun _ ↦ kMain (s.getReg .x12).toNat (instOf s) (outOf s)) :=
  (Rest.start s).congr (by rw [mir, Open.shapeOf_eq hpre.depth, verifyKeccakRust_eq])

/-! ## The exits' contract -/

theorem kw_mono {s u t : MachineState} (hN : heapNext u ≤ heapNext t) {a : Word} (h : KW s u a) :
    KW s t a := by
  simp only [KW, Fresh] at h ⊢
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩)))

theorem post_err {s u t : MachineState} (B : Base s u) (hcap : u.getMem (s.getReg .x10) = errNiche)
    (hf : Fails s) (hsame : ∀ a, t.getMem a = u.getMem a) : VerifyKeccakPost s t := by
  have hN : heapNext t = heapNext u := by simp only [heapNext, hsame]
  refine ⟨⟨by rw [hN]; exact B.heap.lo, by rw [hN]; exact B.heap.hi⟩, by rw [hN]; exact B.mono,
    fun T hT ↦ ?_, (B.frame.trans (DFrame.of_same hsame _) fun _ h ↦ h).mono fun a h ↦
      kw_mono (le_of_eq hN.symm) h⟩
  have e := hf T hT
  simp only [mir, instOf, outOf] at e
  rw [e]
  show t.getMem (s.getReg .x10) = _
  rw [hsame, hcap]

theorem outputsAt_congr {s u t : MachineState} (h : ∀ a, t.getMem a = u.getMem a) {a : Word}
    {o : Option (List E × E)} (ho : OutputsAt s u a o) : OutputsAt s t a o := by
  rcases o with _ | ⟨pt, w⟩
  · show t.getMem a = _
    rw [h]; exact ho
  · obtain ⟨h1, h2, h3⟩ := ho
    refine ⟨?_, Layer.newVecE_congr h h2, ?_⟩
    · show t.getMem a ≠ _
      rw [h]; exact h1
    · rw [← h3]; simp only [eAt, h]

theorem post_ok {s u t : MachineState} (B : Base s u) {o : KeccakOpenings}
    (hcap : u.getMem (s.getReg .x10) ≠ errNiche) (hr : Rest s u (pure o))
    (h0 : NewVecE s u (s.getReg .x10) o.inputs.1) (h24 : NewVecE s u (s.getReg .x10 + 24) o.inputs.2)
    (h48 : OutputsAt s u (s.getReg .x10 + 48) o.outputs) (hsame : ∀ a, t.getMem a = u.getMem a) :
    VerifyKeccakPost s t := by
  have hN : heapNext t = heapNext u := by simp only [heapNext, hsame]
  refine ⟨⟨by rw [hN]; exact B.heap.lo, by rw [hN]; exact B.heap.hi⟩, by rw [hN]; exact B.mono,
    fun T hT ↦ ?_, (B.frame.trans (DFrame.of_same hsame _) fun _ h ↦ h).mono fun a h ↦
      kw_mono (le_of_eq hN.symm) h⟩
  obtain ⟨T', hT', e⟩ := hr T hT
  simp only [mir, instOf, outOf] at e
  rw [e]
  refine ⟨?_, Layer.newVecE_congr hsame h0, Layer.newVecE_congr hsame h24,
    outputsAt_congr hsame h48, Layer.transcriptAt_congr hsame hT'⟩
  show t.getMem (s.getReg .x10) ≠ _
  rw [hsame]; exact hcap

/-! ## What the body keeps -/

/-- Bytes apart from the result, the sponge and the stack, and outside the free heap, miss `KW`. -/
theorem missKW {s u : MachineState} (hu : HeapOk u) {lo : Word} {n : Nat}
    (h0 : Apart lo n (s.getReg .x10) 96) (h1 : Apart lo n (s.getReg .x11 + 8) 344)
    (h2 : Apart lo n (stackLo s verifyKeccakStack) verifyKeccakStack) (h3 : Outside s lo n)
    (hn : lo.toNat + n ≤ 2 ^ 64) : Misses (KW s u) lo n := fun y hy h ↦ by
  have := hu.hi
  obtain ⟨f1, f2⟩ := h3
  simp only [KW] at h
  rcases h with h | h | h | h | h <;> addr_omega [hy, h, h0, h1, h2, f1, f2, hn, this]

/-- The transcript's reads miss `KW`. -/
theorem readsKW {s u : MachineState} (hpre : VerifyKeccakPre s) (hu : HeapOk u) :
    Misses (KW s u) (s.getReg .x11) 8 ∧ Misses (KW s u) (proofAt s (s.getReg .x11)) 48 ∧
      Misses (KW s u) (streamPtr s (s.getReg .x11)) (24 * streamLen s (s.getReg .x11)) := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hos := hpre.outSelf
  have hss := hpre.selfStack
  have hpo := hpre.proofOut
  have hps := hpre.proofStack
  have hpa := hpre.self.apart
  refine ⟨missKW hu (by addr_omega [hos]) (by addr_omega [hS]) (by addr_omega [hss])
    ⟨by have := hpre.selfFree.1; addr_omega [this], by have := hpre.selfFree.2; addr_omega [this]⟩
    (by addr_omega [hS]), missKW hu hpo.1 hpa.1 hps.1 hpre.proofFree (by addr_omega [hP]), ?_⟩
  rcases hpre.self.stream with h0 | hB
  · intro y hy; simp only [Within, h0] at hy; omega
  · exact missKW hu hpo.2 hpa.2 hps.2 hpre.streamFree (by addr_omega [hB])

theorem Base.reads {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) :
    proofAt u (s.getReg .x11) = proofAt s (s.getReg .x11) ∧
      streamPtr u (s.getReg .x11) = streamPtr s (s.getReg .x11) ∧
      streamLen u (s.getReg .x11) = streamLen s (s.getReg .x11) := by
  obtain ⟨r1, r2, -⟩ := readsKW hpre B.heap
  exact B.frame.stream' r1 (by addr_omega [hpre.self.self]) r2 (by addr_omega [hpre.self.proof])

theorem Base.tok {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) :
    TranscriptOk u (s.getReg .x11) := by
  obtain ⟨r1, r2, -⟩ := readsKW hpre B.heap
  exact B.frame.transcriptOk hpre.self r1 r2

theorem Base.rodata {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) :
    RodataOk u := by
  have hrs := hpre.stack.rodata
  have hS := hpre.self.self
  have := B.heap.hi
  exact hpre.rodata.dframe B.frame fun a ha hw ↦ by
    simp only [KW] at hw
    rcases hw with hw | hw | hw | hw | hw <;>
      addr_omega [ha, hw, hrs, hpre.outRodata, hpre.selfRodata, hS, this]

/-- A block or a call whose writes lie in `KW` and miss the saved registers. -/
theorem Base.next {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hH : HeapOk v) (hN : heapNext u ≤ heapNext v)
    {W : Word → Prop} (F : DFrame u v W)
    (hW : ∀ a, W a → KW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104) : Base s v := by
  have hb := bounds hpre
  refine ⟨hx2, B.saved.keep (by omega) fun y h1 h2 ↦ F y fun i hi hw ↦ (hW _ hw).2 ?_, hH,
    B.mono.trans hN, (B.frame.mono fun a h ↦ kw_mono hN h).trans F fun a h ↦ (hW a h).1⟩
  addr_omega [h1, h2, hi, hb]

/-- A block that writes nothing. -/
theorem Base.same {s u v : MachineState} (B : Base s u) (hx2 : v.getReg .x2 = s.getReg .x2 - 5248)
    (hm : ∀ a, v.getMem a = u.getMem a) : Base s v := by
  have hN : heapNext v = heapNext u := by simp only [heapNext, hm]
  refine ⟨hx2, ?_, ⟨by rw [hN]; exact B.heap.lo, by rw [hN]; exact B.heap.hi⟩,
    by rw [hN]; exact B.mono,
    (B.frame.trans (DFrame.of_same hm _) fun _ h ↦ h).mono fun a h ↦ kw_mono (le_of_eq hN.symm) h⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := B.saved
  exact ⟨by rw [hm]; exact h0, by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3,
    by rw [hm]; exact h4, by rw [hm]; exact h5, by rw [hm]; exact h6, by rw [hm]; exact h7,
    by rw [hm]; exact h8, by rw [hm]; exact h9, by rw [hm]; exact h10, by rw [hm]; exact h11,
    by rw [hm]; exact h12⟩

/-- Writes to the frame's slots, below the saved registers. -/
theorem slots_kw {s v : MachineState} (hpre : VerifyKeccakPre s) {a lo : Word} {n : Nat}
    (h1 : (s.getReg .x2).toNat - 5248 ≤ lo.toNat) (h2 : lo.toNat + n + 104 ≤ (s.getReg .x2).toNat)
    (ha : Within a lo n) : KW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> addr_omega [hb, h1, h2, ha]

/-- A block writing `n` bytes of the frame's slots from `lo`. -/
theorem Base.slots {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) {lo : Word} {n : Nat} (f : MemFrame u v lo n)
    (h1 : (s.getReg .x2).toNat - 5248 ≤ lo.toNat) (h2 : lo.toNat + n + 104 ≤ (s.getReg .x2).toNat) :
    Base s v := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hb hnx
  have hN : v.getMem nextAddr = u.getMem nextAddr := f _ (by addr_omega [hb, hnx, h1, h2])
  exact B.next hpre hx2
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f)
    fun a ha ↦ slots_kw hpre h1 h2 ha

/-- A transcript callee's frame, its result at `f + 5248 - K`. -/
theorem tframe_kw {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) {n k : Nat}
    (K : Nat) (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    (hx11 : u.getReg .x11 = s.getReg .x11) (hK : n + 104 ≤ K) (hK' : K ≤ 5248)
    (hk : k ≤ openStack) (hH : HeapOk v) (a : Word)
    (ha : Within a (u.getReg .x10) n ∨ Within a (u.getReg .x11 + 8) 344 ∨
      Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨ Fresh u v a) :
    KW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hm := B.mono
  have := hH.hi
  rw [hx10, hx11] at ha
  simp only [stackLo, B.x2] at ha
  simp only [KW, Fresh] at ha ⊢
  unfold verifyKeccakStack at hb hss hnx hab ⊢
  rcases ha with h | h | h | h | h
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb, hK, hK']))), by addr_omega [h, hb, hK, hK']⟩
  · exact ⟨Or.inr (Or.inl h), by addr_omega [h, hb, hss, hS]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb, hk]))), by addr_omega [h, hb, hk]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by addr_omega [h, hb, hnx]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))), by addr_omega [h, hb, hab, this]⟩

/-- A transcript callee's precondition, its result at `f + 5248 - K`. -/
theorem Base.tpre {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) {n k : Nat}
    (K : Nat) (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    (hx11 : u.getReg .x11 = s.getReg .x11) (hK : n ≤ K) (hK' : K ≤ 5248) (hK8 : K % 8 = 0)
    (hk : k ≤ openStack) (hk8 : k % 8 = 0) : TPre n k u := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  obtain ⟨e0, e1, e2⟩ := B.reads hpre
  obtain ⟨r1, r2, -⟩ := readsKW hpre B.heap
  have hS8 : (s.getReg .x11).toNat + 8 ≤ 2 ^ 64 := by addr_omega [hS]
  have hP48 : (proofAt s (s.getReg .x11)).toNat + 48 ≤ 2 ^ 64 := by addr_omega [hpre.self.proof]
  unfold verifyKeccakStack at hb hsm hss hnx hab hrs
  have hst : RtStack u k := hpre.stack.sub 5248 B.x2 (by unfold verifyKeccakStack; omega)
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
theorem Base.tat {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) (hH : HeapOk v)
    {W : Word → Prop} (F : DFrame u v W)
    (hW : ∀ a, W a → ¬ Within a (s.getReg .x11) 368 ∧ KW s v a) {T : TState}
    (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T := by
  have hS := hpre.self.self
  obtain ⟨e0, e1, e2⟩ := B.reads hpre
  obtain ⟨-, r2, r3⟩ := readsKW hpre hH
  exact F.transcriptAt hT (B.tok hpre) (fun y hy h ↦ (hW y h).1 (by addr_omega [hy, hS]))
    (fun y hy h ↦ r2 y (by rwa [e0] at hy) (hW y h).2)
    (fun y hy h ↦ r3 y (by rwa [e1, e2] at hy) (hW y h).2)
    (fun y hy h ↦ (hW y h).1 (by addr_omega [hy, hS]))

theorem Base.slots_tat {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (Bv : Base s v) {lo : Word} {n : Nat} (f : MemFrame u v lo n)
    (h1 : (s.getReg .x2).toNat - 5248 ≤ lo.toNat) (h2 : lo.toNat + n + 104 ≤ (s.getReg .x2).toNat)
    {T : TState} (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  unfold verifyKeccakStack at hb hss
  exact B.tat hpre Bv.heap (DFrame.of_memFrame f) (fun a ha ↦
    ⟨by addr_omega [ha, h1, h2, hb, hss, hS], (slots_kw hpre h1 h2 ha).1⟩) hT

theorem Base.keep {s u : MachineState} (B : Base s u) {lo : Word} {n : Nat}
    (hm : Misses (KW s u) lo n) (hn : lo.toNat + n ≤ 2 ^ 64) {y : Word} (h1 : lo.toNat ≤ y.toNat)
    (h2 : y.toNat + 8 ≤ lo.toNat + n) : u.getMem y = s.getMem y :=
  B.frame y (hm.bytes h1 h2 hn)

theorem Base.eListAt {s u : MachineState} (B : Base s u) {lo : Word} {n : Nat}
    (hm : Misses (KW s u) lo (24 * n)) (hn : n = 0 ∨ lo.toNat + 24 * n ≤ 2 ^ 64) :
    eListAt u lo n = eListAt s lo n := by
  rcases hn with h0 | hn
  · subst h0; rfl
  · exact B.frame.eListAt (hm.bytes (Nat.le_refl _) (Nat.le_refl _) hn)

/-- The doubleword of the `checked` byte is kept. -/
theorem Base.byte {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) :
    u.getMem (s.getReg .x11 + 360) = s.getMem (s.getReg .x11 + 360) := by
  have hS := hpre.self.self
  have hos := hpre.outSelf
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  exact B.keep (missKW B.heap (by addr_omega [hos, hS]) (by addr_omega [hS]) (by addr_omega [hss, hS])
    ⟨by have := hsf.1; addr_omega [this, hS], by have := hsf.2; addr_omega [this, hS]⟩
    (by addr_omega [hS])) (by addr_omega [hS]) (le_refl _) (le_refl _)

/-- The instance's elements miss `KW`. -/
theorem missInst {s u : MachineState} (hpre : VerifyKeccakPre s) (hu : HeapOk u) :
    Misses (KW s u) (kInst s) (24 * kInstLen s) := by
  rcases hpre.inst with h0 | hR
  · intro y hy; simp only [Within, h0] at hy; omega
  · exact missKW hu hpre.instOut hpre.instSelf hpre.instStack hpre.instFree (by addr_omega [hR])

theorem missOutput {s u : MachineState} (hpre : VerifyKeccakPre s) (hu : HeapOk u) :
    Misses (KW s u) (kOutput s) (24 * kOutputLen s) := by
  rcases hpre.output with h0 | hR
  · intro y hy; simp only [Within, h0] at hy; omega
  · exact missKW hu hpre.outputOut hpre.outputSelf hpre.outputStack hpre.outputFree
      (by addr_omega [hR])

/-! ## Calls to `mul` -/

theorem slot_vmr {s : MachineState} (hpre : VerifyKeccakPre s) {K n : Nat} (hK : 8 * n ≤ K)
    (hK' : K ≤ 5248) (hK8 : K % 8 = 0) : ValidMemRange (s.getReg .x2 - BitVec.ofNat 64 K) n := by
  have hb := bounds hpre
  unfold verifyKeccakStack at hb
  valid_sub hpre.stack.valid [hb, hK, hK', hK8]

/-- `mul`'s precondition from the body, the result at `f + 5248 - K`. -/
theorem mul_pre {s u : MachineState} (hpre : VerifyKeccakPre s)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 5248) (hro : RodataOk u) (K : Nat)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    (hK : 24 ≤ K) (hK' : K ≤ 5248) (hK8 : K % 8 = 0)
    (hl : ValidMemRange (u.getReg .x11) 3) (hlS : Apart (u.getReg .x11) 24 (s.getReg .x2 - 6272) 1024)
    (hlo : Apart (u.getReg .x10) 24 (u.getReg .x11) 24)
    (hr : ValidMemRange (u.getReg .x12) 3) (hrS : Apart (u.getReg .x12) 24 (s.getReg .x2 - 6272) 1024)
    (hro' : Apart (u.getReg .x10) 24 (u.getReg .x12) 24) : MulPre u := by
  have hb := bounds hpre
  have hrs := hpre.stack.rodata
  unfold verifyKeccakStack at hb hrs
  have hlo' : stackLo u mulStack = s.getReg .x2 - 6272 := by
    simp only [stackLo, hx2, mulStack]; rv_eval []
  have hst : RtStack u mulStack := hpre.stack.sub 5248 hx2 (by unfold verifyKeccakStack; decide)
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
theorem mul_frame {s u t : MachineState} (hx2 : u.getReg .x2 = s.getReg .x2 - 5248)
    (h : MulPost u t) :
    DFrame u t fun a ↦ Within a (u.getReg .x10) 24 ∨ Within a (s.getReg .x2 - 6272) 1024 := by
  have e : stackLo u mulStack = s.getReg .x2 - 6272 := by
    simp only [stackLo, hx2, mulStack]; rv_eval []
  rw [← e]
  exact DFrame.of_two h.frame

/-! ## Steps of the body

A step (a block or a call) writes some of the frame's slots `rs` (as `(K, n)`: the `n` bytes from
`sp - K`), its callees' stack below the frame, `NEXT`, what it allocates, and, with `sp`, the
sponge (`SW`). What it keeps: the other slots (`SW.slot`), what was allocated before it
(`SW.buf`), what lies outside the free heap and apart from the frame and the sponge
(`SW.region`). -/

@[rv_addr] def Slots (s : MachineState) (rs : List (Nat × Nat)) (a : Word) : Prop :=
  ∃ p ∈ rs, Within a (s.getReg .x2 - BitVec.ofNat 64 p.1) p.2

/-- Inside the frame, below the saved registers. -/
def SlotsOk (rs : List (Nat × Nat)) : Bool := rs.all fun p ↦ p.2 + 104 ≤ p.1 && p.1 ≤ 5248

/-- The `m` bytes from `sp - J` miss the slots. -/
def SlotsSep (rs : List (Nat × Nat)) (J m : Nat) : Bool :=
  rs.all fun p ↦ J + p.2 ≤ p.1 || p.1 + m ≤ J

@[rv_addr] def SW (s u v : MachineState) (rs : List (Nat × Nat)) (sp : Bool) (a : Word) : Prop :=
  Slots s rs a ∨ Within a (stackLo s verifyKeccakStack) openStack ∨ Within a nextAddr 8 ∨
    Fresh u v a ∨ (sp = true ∧ Within a (s.getReg .x11 + 8) 344)

theorem slots_bounds {s : MachineState} (hpre : VerifyKeccakPre s) {rs : List (Nat × Nat)}
    (hok : SlotsOk rs = true) {a : Word} (h : Slots s rs a) :
    (s.getReg .x2).toNat - 5248 ≤ a.toNat ∧ a.toNat + 104 < (s.getReg .x2).toNat := by
  have hb := bounds hpre
  unfold verifyKeccakStack at hb
  obtain ⟨p, hp, hw⟩ := h
  have := List.all_eq_true.mp hok p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨h1, h2⟩ := this
  addr_omega [hw, hb, h1, h2]

theorem SW.kw {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) (hH : HeapOk v)
    (_hN : heapNext u ≤ heapNext v) {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true)
    {a : Word} (h : SW s u v rs sp a) : KW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hm := B.mono
  simp only [SW, KW, Fresh] at h ⊢
  unfold verifyKeccakStack at hb hss hnx hab ⊢
  rcases h with h | h | h | h | ⟨-, h⟩
  · have := slots_bounds hpre hok h
    exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [this, hb]))), by addr_omega [this, hb]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))), by addr_omega [h, hb]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by addr_omega [h, hb, hnx]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))), by
      have hhi := hH.hi; addr_omega [h, hb, hab, hhi]⟩
  · exact ⟨Or.inr (Or.inl h), by addr_omega [h, hb, hss, hS]⟩

theorem Base.step {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hH : HeapOk v) (hN : heapNext u ≤ heapNext v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) (F : DFrame u v (SW s u v rs sp)) :
    Base s v :=
  B.next hpre hx2 hH hN F fun _ h ↦ SW.kw hpre B hH hN hok h

/-- A slot the step does not write. -/
theorem SW.slot {s u v : MachineState} (hpre : VerifyKeccakPre s) (hH : HeapOk v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) {J m : Nat} (hJ : J ≤ 5248)
    (hm : m ≤ J) (hsep : SlotsSep rs J m = true) :
    Misses (SW s u v rs sp) (s.getReg .x2 - BitVec.ofNat 64 J) m := by
  intro y hy h
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hhi := hH.hi
  simp only [SW, Fresh] at h
  unfold verifyKeccakStack at hb hss hnx hab
  rcases h with ⟨p, hp, hw⟩ | h | h | h | ⟨-, h⟩
  · have h1 := List.all_eq_true.mp hok p hp
    have h2 := List.all_eq_true.mp hsep p hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1 h2
    obtain ⟨h1, h1'⟩ := h1
    rcases h2 with h2 | h2 <;> addr_omega [hw, hy, hb, h1, h1', h2, hJ, hm]
  · addr_omega [h, hy, hb, hJ, hm]
  · addr_omega [h, hy, hb, hnx, hJ, hm]
  · addr_omega [h, hy, hb, hab, hJ, hm, hhi]
  · addr_omega [h, hy, hb, hss, hS, hJ, hm]

/-- What was allocated since the entry. -/
theorem SW.buf {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) {p : Word} {N : Nat}
    (hp : NewBuf s u p N 8) : Misses (SW s u v rs sp) p N := by
  intro y hy h
  have hb := bounds hpre
  have hS := hpre.self.self
  have hsf := hpre.selfFree
  have hab := hpre.stack.above
  have hhi := B.heap.hi
  simp only [NewBuf] at hp
  simp only [SW, Fresh] at h
  unfold verifyKeccakStack at hb hab
  obtain ⟨f1, f2⟩ := hsf
  rcases hp with ⟨-, hp | hp⟩
  · simp only [Within, hp] at hy; omega
  rcases h with h | h | h | h | ⟨-, h⟩
  · have := slots_bounds hpre hok h
    addr_omega [this, hy, hp, hb, hab, hhi]
  · addr_omega [h, hy, hp, hb, hab, hhi]
  · addr_omega [h, hy, hp, hhi]
  · addr_omega [h, hy, hp]
  · addr_omega [h, hy, hp, hS, f1, hhi]

/-- Bytes outside the free heap, apart from the frame and the sponge. -/
theorem SW.region {s u v : MachineState} (B : Base s u) (hH : HeapOk v) {rs : List (Nat × Nat)} {sp : Bool}
    (hpre : VerifyKeccakPre s) (hok : SlotsOk rs = true) {lo : Word} {n : Nat}
    (h1 : Apart lo n (stackLo s verifyKeccakStack) verifyKeccakStack)
    (h2 : Apart lo n (s.getReg .x11 + 8) 344) (h3 : Outside s lo n) (hn : lo.toNat + n ≤ 2 ^ 64) :
    Misses (SW s u v rs sp) lo n := by
  intro y hy h
  have hb := bounds hpre
  have hm := B.mono
  obtain ⟨f1, f2⟩ := h3
  simp only [SW, Fresh] at h
  unfold verifyKeccakStack at hb h1
  rcases h with h | h | h | h | ⟨-, h⟩
  · have := slots_bounds hpre hok h
    addr_omega [this, hy, h1, hb, hn]
  · addr_omega [h, hy, h1, hb, hn]
  · addr_omega [h, hy, f2, hn]
  · have hhi := hH.hi; addr_omega [h, hy, f1, hn, hhi, hm]
  · addr_omega [h, hy, h2, hn]

theorem newVecE_step {s u v : MachineState} {a : Word} {xs : List E} (h : NewVecE s u a xs)
    {w : Word → Prop} (F : DFrame u v w) (hN : heapNext u ≤ heapNext v) (hhdr : Misses w a 24)
    (ha : a.toNat + 24 ≤ 2 ^ 64) (hbuf : Misses w (vecPtr u a) ((vecCap u a).toNat * 24))
    (hhi : heapNext u ≤ heapEnd) : NewVecE s v a xs := by
  have e0 : v.getMem a = u.getMem a := F a (hhdr.bytes (Nat.le_refl _) (by omega) ha)
  have e8 : v.getMem (a + 8) = u.getMem (a + 8) := F _ (hhdr.bytes (by addr_omega [ha])
    (by addr_omega [ha]) ha)
  have e16 : v.getMem (a + 16) = u.getMem (a + 16) := F _ (hhdr.bytes (by addr_omega [ha])
    (by addr_omega [ha]) ha)
  obtain ⟨⟨hr, hl⟩, hnb, he⟩ := h
  have ec : vecCap v a = vecCap u a := e0
  have ep : vecPtr v a = vecPtr u a := e8
  have el : vecLen v a = vecLen u a := e16
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, ec, ep] at hr ⊢; omega
  · rw [el, ec]; exact hl
  · simp only [NewBuf, ec, ep] at hnb ⊢; omega
  · rw [← he]
    simp only [vecEs, ep, el]
    rcases hnb.2 with h0 | hb
    · have : (vecLen u a).toNat = 0 := by omega
      rw [this]; rfl
    · exact F.eListAt (hbuf.bytes (Nat.le_refl _) (by omega) (by unfold heapEnd at hhi; omega))

theorem SW.tat {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) (hH : HeapOk v)
    (hN : heapNext u ≤ heapNext v) {rs : List (Nat × Nat)} (hok : SlotsOk rs = true)
    (F : DFrame u v (SW s u v rs false)) {T : TState} (hT : TranscriptAt u (s.getReg .x11) T) :
    TranscriptAt v (s.getReg .x11) T := by
  refine B.tat hpre hH F (fun a ha ↦ ⟨fun hw ↦ ?_, (SW.kw hpre B hH hN hok ha).1⟩) hT
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hm := B.mono
  obtain ⟨f1, f2⟩ := hsf
  simp only [SW, Fresh] at ha
  unfold verifyKeccakStack at hb hss
  rcases ha with h | h | h | h | ⟨h, -⟩
  · have := slots_bounds hpre hok h
    addr_omega [this, hw, hss, hb, hS]
  · addr_omega [h, hw, hss, hb, hS]
  · addr_omega [h, hw, f2]
  · have hhi := hH.hi; addr_omega [h, hw, f1, hS, hm, hhi]
  · cases h

/-- A callee's stack below the frame. -/
theorem stk_sw {s u : MachineState} (hpre : VerifyKeccakPre s)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 5248) {k : Nat} (hk : k ≤ openStack) {a : Word}
    (h : Within a (stackLo u k) k) : Within a (stackLo s verifyKeccakStack) openStack := by
  have hb := bounds hpre
  simp only [stackLo, hx2] at h ⊢
  unfold verifyKeccakStack at hb ⊢
  addr_omega [h, hb, hk]

/-- A callee's result in a slot. -/
theorem out_sw {s u : MachineState} {K n : Nat} (hx : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    {a : Word} (h : Within a (u.getReg .x10) n) : Slots s [(K, n)] a :=
  ⟨(K, n), List.mem_singleton_self _, by rw [← hx]; exact h⟩

/-- A transcript callee's frame, its result at `sp - K`. -/
theorem tframe_sw {s u v : MachineState} (hpre : VerifyKeccakPre s) {n k : Nat} (K : Nat)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 5248)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K) (hx11 : u.getReg .x11 = s.getReg .x11)
    (hk : k ≤ openStack) (a : Word)
    (ha : Within a (u.getReg .x10) n ∨ Within a (u.getReg .x11 + 8) 344 ∨
      Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨ Fresh u v a) : SW s u v [(K, n)] true a := by
  rcases ha with h | h | h | h | h
  · exact Or.inl (out_sw hx10 h)
  · rw [hx11] at h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
  · exact Or.inr (Or.inl (stk_sw hpre hx2 hk h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- An allocating callee's frame without the transcript, its result at `sp - K`. -/
theorem cframe_sw {s u v : MachineState} (hpre : VerifyKeccakPre s) {n k : Nat} (K : Nat)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 5248)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K) (hk : k ≤ openStack) (a : Word)
    (ha : Within a (u.getReg .x10) n ∨ Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨
      Fresh u v a) : SW s u v [(K, n)] false a := by
  rcases ha with h | h | h | h
  · exact Or.inl (out_sw hx10 h)
  · exact Or.inr (Or.inl (stk_sw hpre hx2 hk h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- A field callee's frame: its result at `sp - K`, its stack. -/
theorem fframe_sw {s u v : MachineState} (hpre : VerifyKeccakPre s) {n k : Nat} (K : Nat)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 5248)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K) (hk : k ≤ openStack) (a : Word)
    (ha : Within a (u.getReg .x10) n ∨ Within a (stackLo u k) k) : SW s u v [(K, n)] false a := by
  rcases ha with h | h
  · exact Or.inl (out_sw hx10 h)
  · exact Or.inr (Or.inl (stk_sw hpre hx2 hk h))

/-- A slot's doubleword the step does not write. -/
theorem SW.mem {s u v : MachineState} (hpre : VerifyKeccakPre s) (hH : HeapOk v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) {J : Nat} (hJ : J ≤ 5248)
    (h8 : 8 ≤ J) (hsep : SlotsSep rs J 8 = true) (F : DFrame u v (SW s u v rs sp)) :
    v.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 J) := by
  have hb := bounds hpre
  exact F _ ((SW.slot hpre hH hok hJ h8 hsep).bytes (Nat.le_refl _) (Nat.le_refl _)
    (by addr_omega [hb, hJ]))

/-- A slot's `E` the step does not write. -/
theorem SW.e {s u v : MachineState} (hpre : VerifyKeccakPre s) (hH : HeapOk v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) {J : Nat} (hJ : J ≤ 5248)
    (h24 : 24 ≤ J) (hsep : SlotsSep rs J 24 = true) (F : DFrame u v (SW s u v rs sp)) :
    eAt v (s.getReg .x2 - BitVec.ofNat 64 J) = eAt u (s.getReg .x2 - BitVec.ofNat 64 J) := by
  have hb := bounds hpre
  exact F.eAt ((SW.slot hpre hH hok hJ h24 hsep).bytes (Nat.le_refl _) (Nat.le_refl _)
    (by addr_omega [hb, hJ]))

/-- A slot's `Vec` the step does not write, its buffer allocated since the entry. -/
theorem SW.vec {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u) (hH : HeapOk v)
    (hN : heapNext u ≤ heapNext v) {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true)
    {J : Nat} (hJ : J ≤ 5248) (h24 : 24 ≤ J) (hsep : SlotsSep rs J 24 = true)
    (F : DFrame u v (SW s u v rs sp)) {xs : List E}
    (h : NewVecE s u (s.getReg .x2 - BitVec.ofNat 64 J) xs) :
    NewVecE s v (s.getReg .x2 - BitVec.ofNat 64 J) xs := by
  have hb := bounds hpre
  exact newVecE_step h F hN (SW.slot hpre hH hok hJ h24 hsep) (by addr_omega [hb, hJ])
    (SW.buf hpre B hok (by have := h.buf; simp only [NewBuf] at this ⊢; omega)) B.heap.hi

/-! ## Blocks that write slots -/

theorem slots_of {s : MachineState} (hpre : VerifyKeccakPre s) {rs : List (Nat × Nat)} {J : Nat}
    (h : rs.any (fun p ↦ decide (J ≤ p.1) && decide (p.1 < J + p.2) && decide (p.1 ≤ 5248)) = true) :
    Slots s rs (s.getReg .x2 - BitVec.ofNat 64 J) := by
  have hb := bounds hpre
  unfold verifyKeccakStack at hb
  obtain ⟨p, hp, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  exact ⟨p, hp, by addr_omega [hb, h1, h2, h3]⟩

/-- A block whose writes lie in slots. -/
theorem block_slots {x : Sym.Expect} {s u v : MachineState} (h : x.Holds u v)
    {rs : List (Nat × Nat)} (hw : ∀ k ∈ x.writes, Slots s rs (k.eval u)) : DFrame u v (Slots s rs) :=
  Open.dframe_of_writes h hw

theorem slots_sw {s u v : MachineState} {rs : List (Nat × Nat)} (F : DFrame u v (Slots s rs)) :
    DFrame u v (SW s u v rs false) :=
  F.mono fun _ h ↦ Or.inl h

theorem slots_next {s u v : MachineState} (hpre : VerifyKeccakPre s) {rs : List (Nat × Nat)}
    (hok : SlotsOk rs = true) (F : DFrame u v (Slots s rs)) :
    v.getMem nextAddr = u.getMem nextAddr := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hb hnx
  exact F _ fun i hi h ↦ by
    have := slots_bounds hpre hok h
    addr_omega [this, hb, hnx, hi]

theorem Base.block {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) {rs : List (Nat × Nat)} (hok : SlotsOk rs = true)
    (F : DFrame u v (Slots s rs)) : Base s v := by
  have hN := slots_next hpre hok F
  exact B.step hpre hx2
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) hok (slots_sw F)

theorem Base.block_tat {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    {rs : List (Nat × Nat)} (hok : SlotsOk rs = true) (F : DFrame u v (Slots s rs)) {T : TState}
    (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T := by
  have hN := slots_next hpre hok F
  exact SW.tat hpre B
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) hok (slots_sw F) hT

theorem SlotsSep.sub {rs : List (Nat × Nat)} {J m J' m' : Nat} (h : SlotsSep rs J m = true)
    (h1 : J' ≤ J) (h2 : m' + J ≤ m + J') : SlotsSep rs J' m' = true := by
  simp only [SlotsSep, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  intro p hp
  rcases h p hp with h | h
  · left; omega
  · right; omega

theorem SW.widen {s u v u' v' : MachineState} {rs rs' : List (Nat × Nat)} {sp sp' : Bool}
    (hrs : ∀ p ∈ rs, p ∈ rs') (hsp : sp = true → sp' = true) (hu : heapNext u' ≤ heapNext u)
    (hv : heapNext v ≤ heapNext v') {a : Word} (h : SW s u v rs sp a) : SW s u' v' rs' sp' a := by
  simp only [SW, Fresh] at h ⊢
  rcases h with ⟨p, hp, h⟩ | h | h | h | ⟨h1, h⟩
  · exact Or.inl ⟨p, hrs p hp, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hsp h1, h⟩)))

/-- Two steps in sequence. -/
theorem SW.trans {s u v w : MachineState} {rs₁ rs₂ rs : List (Nat × Nat)} {sp₁ sp₂ sp : Bool}
    (F₁ : DFrame u v (SW s u v rs₁ sp₁)) (F₂ : DFrame v w (SW s v w rs₂ sp₂))
    (h₁ : ∀ p ∈ rs₁, p ∈ rs) (h₂ : ∀ p ∈ rs₂, p ∈ rs) (hs₁ : sp₁ = true → sp = true)
    (hs₂ : sp₂ = true → sp = true) (hN₁ : heapNext u ≤ heapNext v) (hN₂ : heapNext v ≤ heapNext w) :
    DFrame u w (SW s u w rs sp) :=
  (F₁.mono fun _ h ↦ SW.widen h₁ hs₁ (le_refl _) hN₂ h).trans F₂
    fun _ h ↦ SW.widen h₂ hs₂ hN₁ (le_refl _) h

end Rv64Verifier.Gkr.Keccak
