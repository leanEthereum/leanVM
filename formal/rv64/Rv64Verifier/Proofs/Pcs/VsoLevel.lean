import Rv64Verifier.Proofs.Pcs.VsoOpenings

/-!
# `verify_stacked_opening`'s level loop: a level's head

From `0x8000a150` the function runs `verify_whir`'s level loop, its head at `0x8000a190`. The
mirror's locals (`WhirLocals`) in memory: the running quadratic's buffer and length in `x22`/`x23`
(its capacity is dropped), `folds` (`Vec<E>`) at `S - 688`, `glued` (`Vec<GluedClaim>`) at
`S - 664`. A `GluedClaim` is 88 bytes: the weight (56), the scalar (an `E`, at 56), `fold_start`
(at 80). The weight `Queries` holds the queries (`Vec<u64>`, at 0), their weights (`Vec<E>`, at
24) and `message_log` (at 48); `Ood` holds `-1` at 0 (a niche of the queries' capacity), then the
point (`Vec<E>`, at 8).

Each level overwrites the root, passed by reference, with its commitment: the loop's invariant
allows that write (`WR`, `InvR`, `FailR`). What the loop writes from the configured state `c` on
is `LM`: its frame but the slots it keeps (`S - 864`, `S - 848`..`S - 832`, `S - 800`,
`S - 776`..`S - 688`), the callees' stacks, `NEXT`, the heap from the mark `L` on (above the
ladders and the scales), the sponge and offsets, the root.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem vso_stack : vsoStack = 2464 := by
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack]
  decide

theorem stackLo_vso (s : MachineState) : stackLo s vsoStack = s.getReg .x2 - 2464 := by
  rw [vso_stack]; rfl

/-! ## The root's writes -/

/-- The sponge and offsets, and the root. -/
@[rv_addr] def WR (s : MachineState) (a : Word) : Prop := W s a ∨ Within a (s.getReg .x11) 32

/-- Inside the function, the root written. -/
abbrev InvR (s u : MachineState) (nx : Word) : Prop := InvW (WR s) s u nx

/-- A dead end, or an `Err` returned, the root written. -/
def FailR (s v : MachineState) : Prop :=
  Dead Image.code v ∨ (v.pc = 0x8000a0bc ∧ v.getReg .x10 ≠ okTag ∧ ∃ nx, InvR s v nx)

theorem InvW.widen {s u : MachineState} {nx : Word} {w w' : Word → Prop} (h : InvW w s u nx)
    (hw : ∀ a, w a → w' a) : InvW w' s u nx := by
  refine ⟨h.sp, h.slots, h.kept, h.mem.mono fun a ha ↦ ?_, h.next, h.mono, h.fits⟩
  rcases ha with ha | ha
  · exact Or.inl (hw a ha)
  · exact Or.inr ha

theorem Inv.toR {s u : MachineState} {nx : Word} (h : Inv s u nx) : InvR s u nx :=
  InvW.widen h fun _ ha ↦ Or.inl ha

theorem Fail.toR {s v : MachineState} (h : Fail s v) : FailR s v := by
  rcases h with h | ⟨h1, h2, nx, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, nx, h3.toR⟩

/-! ## What the function writes but the sponge -/

/-- The stack, `NEXT`, the heap allocated since the entry, the root. -/
def NS (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 2464 ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a (s.getReg .x11) 32

/-- What the entry's state holds apart from the stack, the free heap and the root misses `NS`. -/
theorem ns_misses {s : MachineState} {a : Word} {n : Nat}
    (hst : Apart a n (stackLo s vsoStack) vsoStack) (hf : Outside s a n)
    (hr : Apart a n (s.getReg .x11) 32) : Misses (NS s) a n := by
  rw [stackLo_vso, vso_stack] at hst
  simp only [Outside] at hf
  intro y hy hN
  rcases hN with hN | hN | hN | hN
  · addr_omega [hy, hN, hst]
  · addr_omega [hy, hN, hf.2]
  · rcases hf.1 with h1 | h1
    · addr_omega [hy, hN.1, h1]
    · addr_omega [hy, hN.2, h1]
  · addr_omega [hy, hN, hr]

/-- The transcript's facts inside the function, the root written. -/
theorem trR_facts {s u : MachineState} {nx : Word} (hpre : VsoPre s) (h : InvR s u nx) :
    TranscriptOk u (s.getReg .x10) ∧ proofAt u (s.getReg .x10) = proofAt s (s.getReg .x10) ∧
      streamPtr u (s.getReg .x10) = streamPtr s (s.getReg .x10) ∧
      streamLen u (s.getReg .x10) = streamLen s (s.getReg .x10) := by
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hpa := hpre.proofSponge
  have hrs := hpre.rootSelf
  have hrp := hpre.rootProof
  simp only [ProofApart] at hpa hrp
  have hP := Region.bounds hI.ok.proof
  have hm8 : Misses (Wr s vsoStack (WR s) nx) (s.getReg .x10) 8 := fun y hy hW ↦ by
    rcases hW with hW | hW
    · rcases hW with hW | hW
      · simp only [W] at hW; addr_omega [hy, hW, hS]
      · addr_omega [hy, hW, hrs]
    · exact src_misses h.fits hI.stack hI.free y (by addr_omega [hy, hS]) (Or.inr hW)
  have hm48 : Misses (Wr s vsoStack (WR s) nx) (proofAt s (s.getReg .x10)) 48 := fun y hy hW ↦ by
    rcases hW with hW | hW
    · rcases hW with hW | hW
      · simp only [W] at hW; addr_omega [hy, hW, hpa.1, hP]
      · addr_omega [hy, hW, hrp.1]
    · exact src_misses h.fits hI.proofStack.1 hI.proofFree y hy (Or.inr hW)
  obtain ⟨e0, e1, e2⟩ := h.mem.stream' hm8 (by omega) hm48 (by omega)
  exact ⟨h.mem.transcriptOk hI.ok hm8 hm48, e0, e1, e2⟩

/-- A step that writes within `NS` keeps what the transcript stands for. -/
theorem tr_keep {s u v : MachineState} {nx : Word} {X : Word → Prop} {T : Model.TState}
    (hpre : VsoPre s) (hinv : InvR s u nx) (hT : TranscriptAt u (s.getReg .x10) T)
    (hX : DFrame u v X) (hXs : ∀ a, X a → NS s a) : TranscriptAt v (s.getReg .x10) T := by
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  obtain ⟨hok, e0, e1, e2⟩ := trR_facts hpre hinv
  have hrs := hpre.rootSelf
  have hrp := hpre.rootProof
  simp only [ProofApart] at hrp
  have mX {a : Word} {n : Nat} (hst : Apart a n (stackLo s vsoStack) vsoStack) (hf : Outside s a n)
      (hr : Apart a n (s.getReg .x11) 32) : Misses X a n :=
    fun y hy hx ↦ ns_misses hst hf hr y hy (hXs y hx)
  have hself := mX hI.stack hI.free (by simp only [Apart] at hrs ⊢; omega)
  refine hX.transcriptAt hT hok (fun y hy ↦ hself y (by addr_omega [hy, hS]))
    (by rw [e0]; exact mX hI.proofStack.1 hI.proofFree (by simp only [Apart] at hrp ⊢; omega))
    (by rw [e1, e2]; exact mX hI.proofStack.2 hI.streamFree (by simp only [Apart] at hrp ⊢; omega))
    (fun y hy ↦ hself y (by addr_omega [hy, hS]))

/-- The root's digest, kept by a frame that misses it. -/
theorem digest_keep {u v : MachineState} {X : Word → Prop} {a : Word} (hX : DFrame u v X)
    (ha : a.toNat + 32 ≤ 2 ^ 64) (hm : ∀ y, Within y a 32 → ¬ X y) : digestAt v a = digestAt u a := by
  simp only [digestAt]
  congr 1
  funext i
  have hi := i.isLt
  rw [hX _ fun j hj hx ↦ hm _ (by addr_omega [ha, hi, hj]) hx]

/-- The entry's root misses what the function writes but the root itself. -/
theorem root_misses {s : MachineState} {nx : Word} (hpre : VsoPre s) (hfit : nx.toNat ≤ heapEnd) :
    ∀ y, Within y (s.getReg .x11) 32 → ¬ Wr s vsoStack (W s) nx y := by
  have hr := hpre.root
  have hrs := hpre.rootSponge
  have hst := hr.stack
  have hf := hr.free
  rw [stackLo_vso, vso_stack] at hst
  simp only [Outside] at hf
  intro y hy hW
  rcases hW with hW | hW | hW | hW
  · simp only [W] at hW; addr_omega [hy, hW, hrs]
  · rw [stackLo_vso, vso_stack] at hW; addr_omega [hy, hW, hst]
  · addr_omega [hy, hW, hf.2]
  · rcases hf.1 with h1 | h1
    · addr_omega [hy, hW.1, h1]
    · addr_omega [hy, hW.2, h1, hfit]

theorem root_bound {s : MachineState} (hpre : VsoPre s) :
    (s.getReg .x11).toNat + 32 ≤ 2 ^ 64 := by
  rcases hpre.root.region with h0 | h0
  · cases h0
  · have := Region.bounds h0; omega

/-! ## The loop's writes -/

/-- What the loop writes from the configured state on, `NEXT` at `hi`. -/
def LM (s : MachineState) (L : ℕ) (hi a : Word) : Prop :=
  Within a (s.getReg .x2 - 1040) 176 ∨ Within a (s.getReg .x2 - 856) 8 ∨
    Within a (s.getReg .x2 - 832) 32 ∨ Within a (s.getReg .x2 - 792) 16 ∨
    Within a (s.getReg .x2 - 688) 584 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a nextAddr 8 ∨ (L ≤ a.toNat ∧ a.toNat < hi.toNat) ∨ WR s a

theorem LM.mono {s : MachineState} {L : ℕ} {hi hi' a : Word} (hle : hi.toNat ≤ hi'.toNat)
    (h : LM s L hi a) : LM s L hi' a := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

/-- The function's invariant, the root written, from the configured state's. -/
theorem LM.inv {s c u : MachineState} {L : ℕ} (hpre : VsoPre s) (hc : Inv s c (c.getMem nextAddr))
    (hL : heapNext s ≤ L) (hfr : DFrame c u (LM s L (u.getMem nextAddr))) (hheap : HeapOk u)
    (hmono : heapNext c ≤ heapNext u) (hsp : u.getReg .x2 = c.getReg .x2) :
    InvR s u (u.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  have hrs := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hIs hrs
  have hhi := hheap.hi
  refine Inv.step' hpre hc.toR hfr (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hhi hsp
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hL ha.1, ha.2⟩))
    · exact Or.inl ha
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · addr_omega [ha.2, hb, hhi]
    · rcases ha with ha | ha
      · simp only [W] at ha; addr_omega [ha, hIs, hS, hb]
      · addr_omega [ha, hrs, hb]

/-- A doubleword of the slots the loop keeps. -/
theorem LM.keep {s c u : MachineState} {L : ℕ} {hi : Word} (hpre : VsoPre s)
    (hfr : DFrame c u (LM s L hi)) (hhi : hi.toNat ≤ heapEnd) {y : Word}
    (hy : (s.getReg .x2 - 864).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 856).toNat ∨
      (s.getReg .x2 - 848).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 832).toNat ∨
      (s.getReg .x2 - 800).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 792).toNat ∨
      (s.getReg .x2 - 776).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 688).toNat) :
    u.getMem y = c.getMem y := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  have hrs := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hIs hrs
  obtain ⟨hnx, -⟩ := sfacts hpre
  refine hfr y fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy, hnx]
  · addr_omega [hw.2, hi, hb, hy, hhi]
  · rcases hw with hw | hw
    · simp only [W] at hw; addr_omega [hw, hi, hb, hy, hIs, hS]
    · addr_omega [hw, hi, hb, hy, hrs]

/-- The loop keeps the configured state's `Kept`, `RP`, and the ladders. -/
theorem LM.kept {s b c u : MachineState} {L : ℕ} {hi QP QL : Word} (hpre : VsoPre s)
    (hfr : DFrame c u (LM s L hi)) (hL : hi.toNat ≤ heapEnd) (hk : Kept s b c QP QL) :
    Kept s b u QP QL := by
  have hb := bounds hpre
  have k (y : Word) (hy : (s.getReg .x2 - 776).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 688).toNat) : u.getMem y = c.getMem y :=
    LM.keep hpre hfr hL (Or.inr (Or.inr (Or.inr hy)))
  exact { b0 := by rw [k _ (by addr_omega [hb])]; exact hk.b0
          b1 := by rw [k _ (by addr_omega [hb])]; exact hk.b1
          b2 := by rw [k _ (by addr_omega [hb])]; exact hk.b2
          b3 := by rw [k _ (by addr_omega [hb])]; exact hk.b3
          b4 := by rw [k _ (by addr_omega [hb])]; exact hk.b4
          qp := by rw [LM.keep hpre hfr hL (by addr_omega [hb])]; exact hk.qp
          root := by rw [LM.keep hpre hfr hL (by addr_omega [hb])]; exact hk.root
          ql := by rw [LM.keep hpre hfr hL (by addr_omega [hb])]; exact hk.ql }

/-- Words allocated since the entry, below the mark, are kept. -/
theorem LM.words {s c u : MachineState} {L : ℕ} {hi p : Word} {n : ℕ} (hpre : VsoPre s)
    (hfr : DFrame c u (LM s L hi)) (hp1 : heapNext s ≤ p.toNat) (hp2 : p.toNat + 8 * n ≤ L)
    (hL : L ≤ heapEnd) : u.readWords p n = c.readWords p n := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIf := hI.free
  have hrf := hpre.root.free
  simp only [Outside] at hIf hrf
  obtain ⟨hnx, -⟩ := sfacts hpre
  refine DFrame.readWords' hfr (fun a ha hw ↦ ?_) (by simp only [heapEnd] at hL; omega)
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha
  · addr_omega [ha, hw, hb, hp2, hL]
  · addr_omega [ha, hw, hb, hp2, hL]
  · addr_omega [ha, hw, hb, hp2, hL]
  · addr_omega [ha, hw, hb, hp2, hL]
  · addr_omega [ha, hw, hb, hp2, hL]
  · addr_omega [ha, hw, hb, hp2, hL]
  · addr_omega [ha, hw, hnx, hp2, hL]
  · addr_omega [ha.1, hw, hp2]
  · rcases ha with ha | ha
    · simp only [W] at ha
      rcases hIf.1 with h1 | h1
      · addr_omega [ha, hw, h1, hp1, hS]
      · addr_omega [ha, hw, h1, hS, hp2, hL]
    · rcases hrf.1 with h1 | h1
      · addr_omega [ha, hw, h1, hp1]
      · addr_omega [ha, hw, h1, hp2, hL]

/-! ## The loop's values in memory -/

/-- A `Vec<E>` at `A` holding `xs`, its buffer from `L` on (or none). -/
structure VecEAt (u : MachineState) (A : Word) (L : ℕ) (xs : List E) : Prop where
  vec : VecOk u A 24 8
  elems : vecEs u A = xs
  lo : vecCap u A = 0 ∨ L ≤ (vecPtr u A).toNat

/-- The `GluedWeight` at `a`. -/
def weightAt (u : MachineState) (a : Word) : Model.Pcs.GluedWeightRust :=
  if u.getMem a = 0xffffffffffffffff then .ood (vecEs u (a + 8))
  else .queries (u.getMem (a + 48)).toNat (vecWords u a) (vecEs u (a + 24))

/-- The `GluedClaim` at `a`. -/
def gluedAt (u : MachineState) (a : Word) : Model.Pcs.GluedClaimRust :=
  ⟨eAt u (a + 56), (u.getMem (a + 80)).toNat, weightAt u a⟩

/-- `n` of them from `p`. -/
def gluedListAt (u : MachineState) (p : Word) (n : ℕ) : List Model.Pcs.GluedClaimRust :=
  (List.range n).map fun i ↦ gluedAt u (p + BitVec.ofNat 64 (88 * i))

/-- `y` is a byte the weight at `a` points to. -/
def InBufs (u : MachineState) (a y : Word) : Prop :=
  if u.getMem a = 0xffffffffffffffff then Within y (vecPtr u (a + 8)) (24 * (vecLen u (a + 8)).toNat)
  else Within y (vecPtr u a) (8 * (vecLen u a).toNat) ∨
    Within y (vecPtr u (a + 24)) (24 * (vecLen u (a + 24)).toNat)

/-- The weight at `a`'s buffers are aligned: the out-of-domain point's, or the queries' and their
weights'. -/
def WeightAligned (u : MachineState) (a : Word) : Prop :=
  if u.getMem a = 0xffffffffffffffff then (vecPtr u (a + 8)).toNat % 8 = 0
  else (vecPtr u a).toNat % 8 = 0 ∧ (vecPtr u (a + 24)).toNat % 8 = 0

/-- The `n`-th glued claim's address. -/
@[rv_addr] def gAddr (u : MachineState) (s : MachineState) (i : ℕ) : Word :=
  vecPtr u (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * i)

/-- The level a root was read at: its tree's height and leaf width. -/
def rootShape (s : MachineState) (ℓ : ℕ) : ℕ × ℕ :=
  ((s.getReg .x12).toNat - ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum +
      (Model.Pcs.ladderRates (s.getReg .x13).toNat (K0 s + 1)).getD ℓ 0,
    3 * 2 ^ (Model.Pcs.ladderFolds (K0 s + 1)).getD ℓ 0)

/-- From the entry, the mirror runs on as `m` on the transcript `u` stands for, at level `ℓ`: the
proof kept, `ℓ` phases of openings read, `ℓ + 1` roots, the last one the root's bytes in `u`. -/
def Runs (s u : MachineState) (ℓ : ℕ) (m : Model.TM Unit) : Prop :=
  ∀ T, TranscriptAt s (s.getReg .x10) T →
    VsoOpeningsAt s (s.getReg .x10) T →
    T.roots = [(digestAt s (s.getReg .x11),
      Model.stackShape (s.getReg .x12).toNat (s.getReg .x13).toNat)] →
    ∃ T', (Model.Pcs.verifyStackedOpeningRust (s.getReg .x12).toNat (s.getReg .x13).toNat
        (claimsOf s)).run T = m.run T' ∧
      TranscriptAt u (s.getReg .x10) T' ∧ T'.proof = T.proof ∧
      T'.openingOffset = T.openingOffset + ℓ ∧ T'.roots.length = ℓ + 1 ∧
      (T'.roots[ℓ]?).map Prod.fst = some (digestAt u (s.getReg .x11)) ∧
      (ℓ = 0 → T'.roots = T.roots) ∧ (0 < ℓ → (T'.roots[ℓ]?).map Prod.snd = some (rootShape s ℓ))

/-- One step of the mirror that keeps the proof, the roots and the opening offset. -/
theorem Runs.step {s u v : MachineState} {ℓ : ℕ} {m m' : Model.TM Unit} (h : Runs s u ℓ m)
    (hd : digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11))
    (hstep : ∀ T, TranscriptAt u (s.getReg .x10) T → ∃ T', m.run T = m'.run T' ∧
      TranscriptAt v (s.getReg .x10) T' ∧ T'.proof = T.proof ∧ T'.roots = T.roots ∧
      T'.openingOffset = T.openingOffset) : Runs s v ℓ m' := by
  intro T hT hO hr
  obtain ⟨T₁, e₁, hT₁, p₁, o₁, l₁, d₁, z₁, sh₁⟩ := h T hT hO hr
  obtain ⟨T₂, e₂, hT₂, p₂, r₂, o₂⟩ := hstep T₁ hT₁
  refine ⟨T₂, e₁.trans e₂, hT₂, p₂.trans p₁, by rw [o₂, o₁], by rw [r₂, l₁], ?_,
    fun h0 ↦ r₂.trans (z₁ h0), fun h0 ↦ by rw [r₂]; exact sh₁ h0⟩
  rw [r₂, hd, d₁]

theorem run_bind_of {α β : Type} {m : Model.TM α} {k : α → Model.TM β} {T T' : Model.TState} {a : α}
    (h : m.run T = some (a, T')) : (m >>= k).run T = (k a).run T' := by
  rw [StateT.run_bind, h]
  rfl

/-! ## A level's head -/

/-- What the loop fixes: the batched and the configured states, their words, the heap's mark. -/
structure LCtx where
  b : MachineState
  c : MachineState
  nxb : Word
  QP : Word
  QL : Word
  FP : Word
  RP : Word
  L : ℕ

/-- The mirror's batched basis. -/
def basisOf (s : MachineState) (x : LCtx) : List E → Option E :=
  Model.Pcs.stackBasisEvaluate (claimsOf s) (vecEs x.c (s.getReg .x2 - 728))

/-- The mirror's levels from `ℓ` on. -/
def levelsFrom (s : MachineState) (x : LCtx) (ℓ : ℕ) (Wl : Model.Pcs.WhirLocals) :
    Model.TM Unit :=
  Model.Pcs.whirLevelsRust (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ
    (((cfgOf s).folds.zip (cfgOf s).logInvRates).drop ℓ) Wl

/-- At `0x8000a190`, level `ℓ`'s head, the mirror's locals `Wl` in memory. -/
structure Head (s : MachineState) (x : LCtx) (u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) : Prop where
  cfg : Configured s x.b x.c x.nxb x.QP x.QL x.FP x.RP
  mark : x.FP.toNat + 8 * (K0 s + 2) ≤ x.L ∧ x.RP.toNat + 8 * (K0 s + 2) ≤ x.L ∧
    x.nxb.toNat ≤ x.L ∧ x.L ≤ heapNext x.c
  fr : DFrame x.c u (LM s x.L (u.getMem nextAddr))
  heap : HeapOk u
  mono : heapNext x.c ≤ heapNext u
  pc : u.pc = 0x8000a190
  sp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040
  x1 : u.getReg .x1 = BitVec.ofNat 64 (K0 s + 1)
  x5 : u.getReg .x5 = BitVec.ofNat 64 ℓ
  x8 : u.getReg .x8 = 0xffffffffffffffff
  x9 : u.getReg .x9 = x.FP
  x10 : u.getReg .x10 = x.RP
  x17 : u.getReg .x17 = 8
  x25 : u.getReg .x25 = s.getReg .x10 + 8
  x26 : u.getReg .x26 = s.getReg .x12
  x27 : u.getReg .x27 = s.getReg .x10
  lvl : ℓ < K0 s + 2
  m152 : u.getMem (s.getReg .x2 - 888) = BitVec.ofNat 64 (K0 s + 1)
  m160 : u.getMem (s.getReg .x2 - 880) = 0xffffffffaaaaaaab
  m224 : u.getMem (s.getReg .x2 - 816) = s.getReg .x10
  folds : VecEAt u (s.getReg .x2 - 688) x.L Wl.folds
  glued : VecOk u (s.getReg .x2 - 664) 88 8 ∧
    gluedListAt u (vecPtr u (s.getReg .x2 - 664)) (vecLen u (s.getReg .x2 - 664)).toNat = Wl.glued ∧
    (vecCap u (s.getReg .x2 - 664) = 0 ∨ x.L ≤ (vecPtr u (s.getReg .x2 - 664)).toNat)
  quad : eListAt u (u.getReg .x22) (u.getReg .x23).toNat = Wl.runningQuad ∧
    (u.getReg .x22).toNat % 8 = 0 ∧ ((u.getReg .x23).toNat = 0 ∨
      x.L ≤ (u.getReg .x22).toNat ∧ (u.getReg .x22).toNat + 24 * (u.getReg .x23).toNat ≤ heapNext u)
  /-- The folds', the glued claims' and the quadratic's buffers, pairwise apart. -/
  apart : Apart (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24)
      (vecPtr u (s.getReg .x2 - 664)) ((vecCap u (s.getReg .x2 - 664)).toNat * 88) ∧
    Apart (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24)
      (u.getReg .x22) (24 * (u.getReg .x23).toNat) ∧
    Apart (vecPtr u (s.getReg .x2 - 664)) ((vecCap u (s.getReg .x2 - 664)).toNat * 88)
      (u.getReg .x22) (24 * (u.getReg .x23).toNat)
  /-- Every glued claim's buffers lie in the heap from the mark on, apart from those three. -/
  frozen : ∀ i < (vecLen u (s.getReg .x2 - 664)).toNat, ∀ y, InBufs u (gAddr u s i) y →
    x.L ≤ y.toNat ∧ y.toNat < heapNext u ∧
    ¬ Within y (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24) ∧
    ¬ Within y (vecPtr u (s.getReg .x2 - 664)) ((vecCap u (s.getReg .x2 - 664)).toNat * 88) ∧
    ¬ Within y (u.getReg .x22) (24 * (u.getReg .x23).toNat)
  /-- And aligned. -/
  aligned : ∀ i < (vecLen u (s.getReg .x2 - 664)).toNat, WeightAligned u (gAddr u s i)
  value : Runs s u ℓ (levelsFrom s x ℓ Wl)

theorem K0_lt (s : MachineState) : K0 s + 2 < 2 ^ 64 := by
  simp only [K0]; have := (s.getReg .x12).isLt; omega

/-- **Into the level loop**: `0x8000a150` sets up the empty `folds` and `glued`, and the loop's
constants. -/
theorem init {s b c : MachineState} {nxb QP QL FP RP : Word} (hpre : VsoPre s)
    (hc : Configured s b c nxb QP QL FP RP) :
    ∃ L v, Reaches Image.code c v ∧ Head s ⟨b, c, nxb, QP, QL, FP, RP, L⟩ v 0
      ⟨eListAt c (c.getReg .x22) (c.getReg .x23).toNat, [], []⟩ := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hK := K0_lt s
  obtain ⟨L, hL1, hL2, hL3, hL4, hq8, hq⟩ := hc.mark
  have hsp : c.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := hc.inv.sp
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000a150_spec hc.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k := b8000a150_keeps ht
  have X : DFrame c t fun a ↦ Within a (s.getReg .x2 - 888) 16 ∨
      Within a (s.getReg .x2 - 816) 8 ∨ Within a (s.getReg .x2 - 688) 48 :=
    (holds_dframe ht).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a150, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rv_eval [hsp] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (Or.inl (by addr_omega [hw, hb]))
        | exact Or.inr (Or.inr (by addr_omega [hw, hb]))
  have nx : t.getMem nextAddr = c.getMem nextAddr := X _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb, hnx]
  have hn : heapNext t = heapNext c := by simp only [heapNext, nx]
  have hhc := hc.inv.heap hpre.heap
  have hhi := hhc.hi
  have m352 : vecCap t (s.getReg .x2 - 688) = 0 := by
    have := b8000a150_m_x2_352 ht; rw [hsp] at this; rv_eval [] at this; simp only [vecCap]; exact this
  have m360 : vecPtr t (s.getReg .x2 - 688) = 8 := by
    have := b8000a150_m_x2_360 ht; rw [hsp] at this; rv_eval [] at this; simp only [vecPtr]
    rv_eval [this]
  have m368 : vecLen t (s.getReg .x2 - 688) = 0 := by
    have := b8000a150_m_x2_368 ht; rw [hsp] at this; rv_eval [] at this; simp only [vecLen]
    rv_eval [this]
  have m376 : vecCap t (s.getReg .x2 - 664) = 0 := by
    have := b8000a150_m_x2_376 ht; rw [hsp] at this; rv_eval [] at this; simp only [vecCap]; exact this
  have m384 : vecPtr t (s.getReg .x2 - 664) = 8 := by
    have := b8000a150_m_x2_384 ht; rw [hsp] at this; rv_eval [] at this; simp only [vecPtr]
    rv_eval [this]
  have m392 : vecLen t (s.getReg .x2 - 664) = 0 := by
    have := b8000a150_m_x2_392 ht; rw [hsp] at this; rv_eval [] at this; simp only [vecLen]
    rv_eval [this]
  have hroot : digestAt t (s.getReg .x11) = digestAt s (s.getReg .x11) := by
    have hrs := hpre.root.stack
    rw [stackLo_vso, vso_stack] at hrs
    rw [digest_keep X (root_bound hpre) fun y hy hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [hy, hw, hrs, hb],
      digest_keep hc.inv.mem (root_bound hpre) (root_misses hpre hc.inv.fits)]
  have hquad : eListAt t (t.getReg .x22) (t.getReg .x23).toNat =
      eListAt c (c.getReg .x22) (c.getReg .x23).toNat := by
    rw [k .x22 (by decide), k .x23 (by decide)]
    rcases hq with h0 | h0
    · rw [h0]; rfl
    · exact X.eList (fun y hy hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [hy, hw, hb, h0.2, hhi])
        (Or.inr (by simp only [heapEnd] at hhi; omega))
  refine ⟨L, t, hr, {
    cfg := hc
    mark := ⟨hL1, hL2, hL3, hL4⟩
    fr := X.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
    heap := ⟨by rw [hn]; exact hhc.lo, by rw [hn]; exact hhi⟩
    mono := by rw [hn]
    pc := b8000a150_pc ht
    sp := (k .x2 (by decide)).trans hsp
    x1 := by rw [b8000a150_x1 ht, hc.x19]; addr_omega [hK]
    x5 := by rw [b8000a150_x5 ht]; rfl
    x8 := b8000a150_x8 ht
    x9 := by rw [k .x9 (by decide), hc.x9]
    x10 := by rw [b8000a150_x10 ht, hsp]; rv_eval []; exact hc.rp
    x17 := b8000a150_x17 ht
    x25 := by rw [k .x25 (by decide), hc.x25]
    x26 := by rw [k .x26 (by decide), hc.x26]
    x27 := by rw [k .x27 (by decide), hc.x27]
    lvl := by omega
    m152 := by
      have := b8000a150_m_x2_152 ht; rw [hsp, hc.x19] at this; rv_eval [] at this
      rw [this]; addr_omega [hK]
    m160 := by have := b8000a150_m_x2_160 ht; rw [hsp] at this; rv_eval [] at this; exact this
    m224 := by
      have := b8000a150_m_x2_224 ht; rw [hsp, hc.x27] at this; rv_eval [] at this; exact this
    folds := ⟨⟨⟨by rw [m360]; decide, Or.inl (by rw [m352]; rfl)⟩, by rw [m368, m352]⟩,
      by simp only [vecEs, m368]; rfl, Or.inl m352⟩
    glued := ⟨⟨⟨by rw [m384]; decide, Or.inl (by rw [m376]; rfl)⟩, by rw [m392, m376]⟩,
      by rw [m392]; rfl, Or.inl m376⟩
    quad := ⟨hquad, by rw [k .x22 (by decide)]; exact hq8, by
      rw [k .x22 (by decide), k .x23 (by decide), hn]; exact hq⟩
    apart := ⟨Or.inl (by rw [m352]; rfl), Or.inl (by rw [m352]; rfl), Or.inl (by rw [m376]; rfl)⟩
    frozen := fun i hi ↦ by rw [m392] at hi; exact absurd hi (Nat.not_lt_zero _)
    aligned := fun i hi ↦ by rw [m392] at hi; exact absurd hi (Nat.not_lt_zero _)
    value := fun T hT _ hroots ↦ by
      obtain ⟨T', e, hT', -, p, r, o⟩ := hc.value T hT
      refine ⟨T', e, tr_keep hpre hc.inv.toR hT' X fun a ha ↦ Or.inl (by
          rcases ha with ha | ha | ha <;> addr_omega [ha, hb]), p, by rw [o]; rfl,
        by rw [r, hroots]; rfl, ?_, fun _ ↦ r, fun h0 ↦ absurd h0 (Nat.lt_irrefl 0)⟩
      rw [r, hroots, hroot]
      rfl }⟩

end Rv64Verifier.Proofs.Pcs.Vso
