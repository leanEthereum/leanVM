import Rv64Verifier.Proofs.Transcript.TFrame
import Rv64Verifier.Proofs.Transcript.Samples
import Rv64Verifier.Blocks.F76

/-!
# `transcript::sumcheck`

```rust
let mut point = Vec::with_capacity(equalities.len());
for &equality in equalities {
    let message = transcript.sumcheck_round_poly(count, claim, equality)?;
    let challenge = transcript.sample();
    point.push(challenge);
    claim = poly_eval(&message, challenge);
}
Ok((point, claim))
```

compiled at `0x80010538` (`Blocks/F76.lean`), with `S` the entry's `sp` and `n` the number of
equalities: a 208-byte frame saving `ra`, `s0`..`s11`; `try_allocate_in(n)` into `S - 128`, a trap
on its error; the `Vec` at `S - 200` (capacity `n`, buffer in `s8`, length `0`), the result's
address at `S - 208`. The loop head `0x8001062c`: `s2` walks the equalities 32 bytes apart, `s11`
counts down `32` per round left, `s9`/`s10` are the length's offset and the length, `s1` the claim,
which `poly_eval` overwrites in place. A round: `sumcheck_round_poly` into `S - 128`, `-1` in its
capacity going to `0x800106d0` (the result's `Err`); `duplex`, the state's first three lanes into
`S - 128`; the push (`grow_one` never runs: the capacity is `n`); `poly_eval`. `0x80010698` writes
`Ok((point, claim))`, `0x800106e4` returns.

This file holds the mirror read round by round (`pre`), the frame (`V`, `Fr`), the callees'
preconditions and the two exits; `SumcheckRound` a round, `SumcheckSpec` the whole.
-/

namespace Rv64Verifier.Transcript.Sumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F76
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-! ## The mirror, round by round -/

/-- The equalities. -/
def eqsOf (s : MachineState) : List (Option E) :=
  optEListAt s (s.getReg .x14) (s.getReg .x15).toNat

/-- The first `i` rounds of the call's mirror. -/
def pre (s : MachineState) (i : Nat) : TM (List E × E) :=
  ((eqsOf s).take i).foldlM (TM.sumcheckRound (s.getReg .x13).toNat) ([], eAt s (s.getReg .x12))

theorem eqsOf_length (s : MachineState) : (eqsOf s).length = (s.getReg .x15).toNat := by
  simp [eqsOf, optEListAt]

theorem eqsOf_getElem (s : MachineState) {i : Nat} (h : i < (eqsOf s).length) :
    (eqsOf s)[i] = optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) := by
  simp [eqsOf, optEListAt]

theorem pre_all (s : MachineState) :
    pre s (s.getReg .x15).toNat = TM.sumcheck (eAt s (s.getReg .x12)) (s.getReg .x13).toNat
      (eqsOf s) := by
  rw [pre, ← eqsOf_length, List.take_length]
  rfl

theorem round_run (count : Nat) (acc : List E × E) (e : Option E) (T : TState) :
    (TM.sumcheckRound count acc e).run T =
      ((TM.sumcheckRoundPoly count acc.2 e).run T).bind fun r ↦
        some ((acc.1 ++ [(spSqueeze r.2.sponge).1], polyEvalRust r.1 (spSqueeze r.2.sponge).1),
          { r.2 with sponge := (spSqueeze r.2.sponge).2 }) := by
  simp only [TM.sumcheckRound, StateT.run_bind, StateT.run_pure]
  rfl

theorem pre_succ (s : MachineState) {i : Nat} (hi : i < (eqsOf s).length) (T : TState) :
    (pre s (i + 1)).run T = ((pre s i).run T).bind fun r ↦
      (TM.sumcheckRound (s.getReg .x13).toNat r.1 (eqsOf s)[i]).run r.2 := by
  simp only [pre, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.foldlM_append, StateT.run_bind, List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

theorem pre_succ' (s : MachineState) {i : Nat} (hi : i < (s.getReg .x15).toNat) (T : TState) :
    (pre s (i + 1)).run T = ((pre s i).run T).bind fun r ↦
      (TM.sumcheckRound (s.getReg .x13).toNat r.1
        (optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)))).run r.2 := by
  have hi' : i < (eqsOf s).length := by rw [eqsOf_length]; exact hi
  rw [pre_succ s hi', eqsOf_getElem s hi']

/-- A round that fails fails the call. -/
theorem sumcheck_none (s : MachineState) (i : Nat) {T : TState}
    (h : (pre s i).run T = none) :
    (TM.sumcheck (eAt s (s.getReg .x12)) (s.getReg .x13).toNat (eqsOf s)).run T = none := by
  have e : TM.sumcheck (eAt s (s.getReg .x12)) (s.getReg .x13).toNat (eqsOf s) =
      pre s i >>= fun acc ↦ ((eqsOf s).drop i).foldlM (TM.sumcheckRound (s.getReg .x13).toNat) acc := by
    rw [pre, ← List.foldlM_append, List.take_append_drop]
    rfl
  rw [e, StateT.run_bind, h]
  rfl

/-! ## Frames -/

theorem bounds {s : MachineState} (h : SumcheckPre s) :
    0xa0000000 + sumcheckStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s sumcheckStack).toNat = (s.getReg .x2).toNat - sumcheckStack :=
  h.toTPre.bounds (by decide) (by decide)

/-- What the function writes before its result: the claim, the sponge and offsets, the stack,
`NEXT` and the heap allocated. -/
def V (s u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x12) 24 ∨ Within a (s.getReg .x11 + 8) 344 ∨
    Within a (stackLo s sumcheckStack) sumcheckStack ∨ Within a nextAddr 8 ∨ Fresh s u a

theorem V.mono {s u v : MachineState} {a : Word} (h : heapNext u ≤ heapNext v) (hw : V s u a) :
    V s v a := by
  rcases hw with hw | hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)))

/-- A region apart from the claim, the transcript, the stack and the free heap misses `V`. -/
theorem V.miss {s u : MachineState} (hhi : heapNext u ≤ heapEnd) {lo : Word} {m : Nat}
    (h0 : Apart lo m (s.getReg .x12) 24) (h1 : Apart lo m (s.getReg .x11 + 8) 344)
    (h2 : Apart lo m (stackLo s sumcheckStack) sumcheckStack) (h3 : Outside s lo m)
    (hn : lo.toNat + m ≤ 2 ^ 64) : Misses (V s u) lo m := fun y hy hw ↦ by
  rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hy, hw, h0, h1, h2, h3, hn, hhi]

/-- The transcript's pointer, the `Proof` and the stream miss `V`. -/
theorem V.misses {s u : MachineState} (hpre : SumcheckPre s) (hhi : heapNext u ≤ heapEnd) :
    Misses (V s u) (s.getReg .x11) 8 ∧ Misses (V s u) (proofAt s (s.getReg .x11)) 48 ∧
      Misses (V s u) (streamPtr s (s.getReg .x11)) (24 * streamLen s (s.getReg .x11)) := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hpa := hpre.self.apart
  refine ⟨V.miss hhi (by addr_omega [hpre.claimSelf]) (by addr_omega [hS])
    (by addr_omega [hpre.selfStack]) (by addr_omega [hpre.selfFree]) (by addr_omega [hS]),
    V.miss hhi (by addr_omega [hpre.proofClaim]) (by addr_omega [hpa])
      (by addr_omega [hpre.proofStack]) (by addr_omega [hpre.proofFree]) (by addr_omega [hP]), ?_⟩
  rcases hpre.self.stream with h0 | hB
  · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
  · exact V.miss hhi (by addr_omega [hpre.proofClaim]) (by addr_omega [hpa])
      (by addr_omega [hpre.proofStack]) hpre.streamFree (by addr_omega [hB])

theorem V.ok {s u : MachineState} (hpre : SumcheckPre s) (hhi : heapNext u ≤ heapEnd)
    (F : DFrame s u (V s u)) : TranscriptOk u (s.getReg .x11) :=
  F.transcriptOk hpre.self (V.misses hpre hhi).1 (V.misses hpre hhi).2.1

theorem V.stream {s u : MachineState} (hpre : SumcheckPre s) (hhi : heapNext u ≤ heapEnd)
    (F : DFrame s u (V s u)) :
    proofAt u (s.getReg .x11) = proofAt s (s.getReg .x11) ∧
      streamPtr u (s.getReg .x11) = streamPtr s (s.getReg .x11) ∧
      streamLen u (s.getReg .x11) = streamLen s (s.getReg .x11) :=
  F.stream' (V.misses hpre hhi).1 (by addr_omega [hpre.self.self]) (V.misses hpre hhi).2.1
    (by addr_omega [hpre.self.proof])

theorem V.proofApart {s u : MachineState} (hpre : SumcheckPre s) (hhi : heapNext u ≤ heapEnd)
    (F : DFrame s u (V s u)) {lo : Word} {m : Nat}
    (ha : ProofApart s (s.getReg .x11) lo m) : ProofApart u (s.getReg .x11) lo m :=
  F.proofApart (V.misses hpre hhi).1 (by addr_omega [hpre.self.self]) (V.misses hpre hhi).2.1
    (by addr_omega [hpre.self.proof]) ha

theorem V.rodata {s u : MachineState} (hpre : SumcheckPre s) (hhi : heapNext u ≤ heapEnd)
    (F : DFrame s u (V s u)) : RodataOk u := by
  have hb := bounds hpre
  have hro := hpre.stack.rodata
  have hS := hpre.self.self
  exact hpre.rodata.dframe F fun a ha hw ↦ by
    rcases hw with hw | hw | hw | hw | hw <;>
      addr_omega [ha, hw, hro, hb, hpre.claimRodata, hpre.selfRodata, hS, hhi]

/-- What a step after the setup writes: the claim, the stack, `NEXT`, the heap below `hi`. -/
def Low (s : MachineState) (hi : Nat) (a : Word) : Prop :=
  Within a (s.getReg .x12) 24 ∨ Within a (stackLo s sumcheckStack) sumcheckStack ∨
    Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < hi)

theorem Low.toV {s v : MachineState} {hi : Nat} {a : Word} (h : hi ≤ heapNext v) (hw : Low s hi a) :
    V s v a := by
  rcases hw with hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)))

/-- A step that writes only the claim, the stack, `NEXT` and the heap allocated keeps the
transcript. -/
theorem Low.transcriptAt {s u v : MachineState} (hpre : SumcheckPre s) {hi : Nat}
    (hhi : hi ≤ heapEnd) (hu : heapNext u ≤ heapEnd) (F : DFrame s u (V s u))
    (G : DFrame u v (Low s hi)) {T : TState} (hT : TranscriptAt u (s.getReg .x11) T) :
    TranscriptAt v (s.getReg .x11) T := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hok := V.ok hpre hu F
  obtain ⟨e0, e1, e2⟩ := V.stream hpre hu F
  have ml (lo : Word) (m : Nat) (h0 : Apart lo m (s.getReg .x12) 24)
      (h2 : Apart lo m (stackLo s sumcheckStack) sumcheckStack) (h3 : Outside s lo m)
      (hn : lo.toNat + m ≤ 2 ^ 64) : Misses (Low s hi) lo m :=
    fun y hy hw ↦ by rcases hw with hw | hw | hw | hw <;> addr_omega [hy, hw, h0, h2, h3, hn, hhi]
  have mq : Misses (Low s hi) (proofAt s (s.getReg .x11)) 48 :=
    ml _ _ (by addr_omega [hpre.proofClaim]) (by addr_omega [hpre.proofStack])
      (by addr_omega [hpre.proofFree]) (by addr_omega [hP])
  refine G.transcriptAt hT hok (ml _ _ (by addr_omega [hpre.claimSelf])
    (by addr_omega [hpre.selfStack]) (by addr_omega [hpre.selfFree]) (by addr_omega [hS]))
    (by rw [e0]; exact mq) ?_
    (ml _ _ (by addr_omega [hpre.claimSelf, hS]) (by addr_omega [hpre.selfStack, hS])
      (by addr_omega [hpre.selfFree, hS]) (by addr_omega [hS]))
  rw [e1, e2]
  rcases hpre.self.stream with h0 | hB
  · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
  · exact ml _ _ (by addr_omega [hpre.proofClaim]) (by addr_omega [hpre.proofStack])
      hpre.streamFree (by addr_omega [hB])

/-- A callee's `TPre`: its stack below the frame, its result in the frame, the transcript. -/
theorem callee {n' k' : Nat} {s u : MachineState} (hpre : SumcheckPre s) (hu : HeapOk u)
    (mono : heapNext s ≤ heapNext u) (F : DFrame s u (V s u))
    (x2 : u.getReg .x2 = s.getReg .x2 - 208) (x11 : u.getReg .x11 = s.getReg .x11)
    (hk : k' ≤ roundPolyStack) (hk' : k' % 8 = 0)
    (ho : (s.getReg .x2).toNat - 208 ≤ (u.getReg .x10).toNat ∧
      (u.getReg .x10).toNat + n' ≤ (s.getReg .x2).toNat ∧ (u.getReg .x10).toNat % 8 = 0) :
    TPre n' k' u := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hS := hpre.self.self
  have hro := hst.rodata
  have hsl : stackLo u k' = s.getReg .x2 - BitVec.ofNat 64 208 - BitVec.ofNat 64 k' := by
    simp only [stackLo, x2]; rfl
  obtain ⟨e0, e1, e2⟩ := V.stream hpre hu.hi F
  have hj : 208 + k' ≤ sumcheckStack := by simp only [sumcheckStack]; omega
  have pa (lo : Word) (m : Nat) (h1 : (stackLo s sumcheckStack).toNat ≤ lo.toNat)
      (h2 : lo.toNat + m ≤ (stackLo s sumcheckStack).toNat + sumcheckStack) :
      ProofApart u (s.getReg .x11) lo m :=
    V.proofApart hpre hu.hi F (ProofApart.mono' hpre.proofStack h1 h2)
  have hm := hst.mapped (by decide) (by decide)
  exact {
    heap := hu
    out := by addr_omega [ho, hb, hm]
    self := by rw [x11]; exact V.ok hpre hu.hi F
    stack := hst.sub 208 (by rw [x2]; rfl) hj (by decide) hk' (by decide) (by decide)
    outStack := by rw [hsl]; addr_omega [ho, hb, hj]
    selfStack := by rw [hsl, x11]; addr_omega [hpre.selfStack, hb, hj]
    outSelf := by rw [x11]; addr_omega [ho, hpre.selfStack, hb, hj]
    proofStack := by rw [hsl, x11]; exact pa _ _ (by addr_omega [hb, hj]) (by addr_omega [hb, hj])
    proofOut := by rw [x11]; exact pa _ _ (by addr_omega [ho, hb, hj]) (by addr_omega [ho, hb, hj])
    outFree := by addr_omega [ho, hb, hst.above, hst.next, hj]
    selfFree := by rw [x11]; addr_omega [hpre.selfFree, mono]
    proofFree := by rw [x11, e0]; addr_omega [hpre.proofFree, mono]
    streamFree := by rw [x11, e1, e2]; addr_omega [hpre.streamFree, mono]
    rodata := V.rodata hpre hu.hi F
    outRodata := by addr_omega [ho, hro, hb, hj]
    selfRodata := by rw [x11]; exact hpre.selfRodata }

/-! ## The frame's state -/

/-- Inside the frame: `sp`, and the saved registers in place. -/
structure Saved (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 208
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : u.getMem (s.getReg .x2 - 64) = s.getReg .x22
  s7 : u.getMem (s.getReg .x2 - 72) = s.getReg .x23
  s8 : u.getMem (s.getReg .x2 - 80) = s.getReg .x24
  s9 : u.getMem (s.getReg .x2 - 88) = s.getReg .x25
  s10 : u.getMem (s.getReg .x2 - 96) = s.getReg .x26
  s11 : u.getMem (s.getReg .x2 - 104) = s.getReg .x27

theorem Saved.step {s u v : MachineState} (h : Saved s u) (hS : 104 ≤ (s.getReg .x2).toNat)
    (x2 : v.getReg .x2 = u.getReg .x2)
    (mem : ∀ y : Word, (s.getReg .x2).toNat - 104 ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2).toNat →
      v.getMem y = u.getMem y) : Saved s v where
  x2 := x2.trans h.x2
  ra := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.ra]
  s0 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s0]
  s1 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s1]
  s2 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s2]
  s3 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s3]
  s4 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s4]
  s5 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s5]
  s6 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s6]
  s7 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s7]
  s8 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s8]
  s9 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s9]
  s10 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s10]
  s11 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s11]

/-- The state inside the function: the frame, what was written so far (`V`), the heap. -/
structure Fr (s u : MachineState) : Prop where
  saved : Saved s u
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (V s u)

/-- A step whose writes `w` lie in `V` and miss the saved registers. -/
theorem Fr.step {s u v : MachineState} (h : Fr s u) (hS : 104 ≤ (s.getReg .x2).toNat)
    (x2 : v.getReg .x2 = u.getReg .x2) (hv : HeapOk v) (mono : heapNext u ≤ heapNext v)
    {w : Word → Prop} (G : DFrame u v w) (hw : ∀ a, w a → V s v a)
    (hsv : ∀ y : Word, (s.getReg .x2).toNat - 104 ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2).toNat →
      ∀ i < 8, ¬ w (y + BitVec.ofNat 64 i)) : Fr s v :=
  ⟨h.saved.step hS x2 fun y h1 h2 ↦ G y (hsv y h1 h2), hv, h.mono.trans mono,
    (h.frame.mono fun _ h' ↦ V.mono mono h').trans G hw⟩

/-- A step that writes nothing. -/
theorem Fr.same {s u v : MachineState} (h : Fr s u) (hS : 104 ≤ (s.getReg .x2).toNat)
    (x2 : v.getReg .x2 = u.getReg .x2) (hm : ∀ a, v.getMem a = u.getMem a) : Fr s v := by
  have nx : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact h.step hS x2 ⟨nx ▸ h.heap.lo, nx ▸ h.heap.hi⟩ (Nat.le_of_eq nx.symm)
    (DFrame.of_same hm (fun _ ↦ False)) (fun _ h ↦ h.elim) fun _ _ _ _ _ h ↦ h

/-- `0x800106e4`: the saved registers back, return. -/
theorem epilogue {s u : MachineState} (hpre : SumcheckPre s) (hpc : u.pc = 0x800106e4)
    (h : Saved s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  have hb := bounds hpre
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b800106e4_spec hpc (by
    rv_eval [h.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have pc := b800106e4_pc h₁
  have y2 := b800106e4_x2 h₁
  have y8 := b800106e4_x8 h₁
  have y9 := b800106e4_x9 h₁
  have y18 := b800106e4_x18 h₁
  have y19 := b800106e4_x19 h₁
  have y20 := b800106e4_x20 h₁
  have y21 := b800106e4_x21 h₁
  have y22 := b800106e4_x22 h₁
  have y23 := b800106e4_x23 h₁
  have y24 := b800106e4_x24 h₁
  have y25 := b800106e4_x25 h₁
  have y26 := b800106e4_x26 h₁
  have y27 := b800106e4_x27 h₁
  rv_eval [h.x2] at pc y2 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
  refine ⟨t, hr, by rw [pc, h.ra, returnAddress_eq], ?_, b800106e4_mem_same h₁⟩
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact y2
  · rw [y8, h.s0]
  · rw [y9, h.s1]
  · rw [y18, h.s2]
  · rw [y19, h.s3]
  · rw [y20, h.s4]
  · rw [y21, h.s5]
  · rw [y22, h.s6]
  · rw [y23, h.s7]
  · rw [y24, h.s8]
  · rw [y25, h.s9]
  · rw [y26, h.s10]
  · rw [y27, h.s11]

/-! ## The exits -/

/-- What the function may write: `SumcheckPost`'s frame. -/
def W (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 48 ∨ Within a (s.getReg .x12) 24 ∨ Within a (s.getReg .x11 + 8) 344 ∨
    Within a (stackLo s sumcheckStack) sumcheckStack ∨ Within a nextAddr 8 ∨ Fresh s t a

/-- `TranscriptAt` reads only memory. -/
theorem _root_.Rv64Verifier.Transcript.TranscriptAt.congr {u t : MachineState} {p : Word}
    {T : TState} (h : TranscriptAt u p T) (hm : ∀ a, t.getMem a = u.getMem a) :
    TranscriptAt t p T :=
  ⟨by simp only [streamPtr, streamLen, proofAt, vecPtr, vecLen, Rv64Verifier.eListAt,
      Rv64Verifier.eAt, hm]; exact h.stream,
    by simp only [spongeAt, stateAt, pendingAt, nPending, Rv64Verifier.eAt, hm]; exact h.sponge,
    by rw [hm]; exact h.streamOffset, by rw [hm]; exact h.openingOffset⟩

/-- The result written last: the frame, the heap, the transcript. -/
theorem out_post {s u t : MachineState} (hpre : SumcheckPre s) (h : Fr s u)
    (f : MemFrame u t (s.getReg .x10) 48) :
    HeapOk t ∧ heapNext s ≤ heapNext t ∧ DFrame s t (W s t) ∧ heapNext t = heapNext u ∧
      ∀ T, TranscriptAt u (s.getReg .x11) T → TranscriptAt t (s.getReg .x11) T := by
  have ho := hpre.out
  have hof := hpre.outFree
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]; rw [f _ (by addr_omega [ho, hof])]
  have hok := V.ok hpre h.heap.hi h.frame
  obtain ⟨e0, e1, e2⟩ := V.stream hpre h.heap.hi h.frame
  have mo (lo : Word) (m : Nat) (h0 : Apart lo m (s.getReg .x10) 48) (hm : lo.toNat + m ≤ 2 ^ 64) :
      Misses (Within · (s.getReg .x10) 48) lo m :=
    fun y hy h ↦ by addr_omega [hy, h, h0, hm]
  refine ⟨⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn ▸ h.mono, ?_, hn, fun T hT ↦ ?_⟩
  · refine (h.frame.mono fun a h' ↦ ?_).trans (DFrame.of_memFrame f) fun a h' ↦ Or.inl h'
    have h'' := V.mono (Nat.le_of_eq hn.symm) h'
    rcases h'' with h'' | h'' | h'' | h'' | h''
    · exact Or.inr (Or.inl h'')
    · exact Or.inr (Or.inr (Or.inl h''))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h''))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h''))))
  · have mq : Misses (Within · (s.getReg .x10) 48) (proofAt s (s.getReg .x11)) 48 :=
      mo _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hP])
    refine (DFrame.of_memFrame f).transcriptAt hT hok (mo _ _ (by addr_omega [hpre.outSelf])
      (by addr_omega [hS])) (by rw [e0]; exact mq)
      ?_ (mo _ _ (by addr_omega [hpre.outSelf, hS]) (by addr_omega [hS]))
    rw [e1, e2]
    rcases hpre.self.stream with h0 | hB
    · intro y hy; rw [h0] at hy; simp only [Within] at hy; omega
    · exact mo _ _ (by addr_omega [hpre.proofOut]) (by addr_omega [hB])

set_option maxHeartbeats 1000000 in
/-- `0x800106d0`: `sumcheck_round_poly` failed; the result's `Err`, then return. -/
theorem exitErr {s u : MachineState} (hpre : SumcheckPre s) (hpc : u.pc = 0x800106d0) (h : Fr s u)
    (outM : u.getMem (s.getReg .x2 - 208) = s.getReg .x10) (x23 : u.getReg .x23 ≠ errNiche)
    (fails : ∀ T, TranscriptAt s (s.getReg .x11) T →
      (TM.sumcheck (eAt s (s.getReg .x12)) (s.getReg .x13).toNat (eqsOf s)).run T = none) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ SumcheckPost s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have x2 := h.saved.x2
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800106d0_spec hpc (by
    rv_eval [x2, outM]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b800106d0_m0 h₁
  have m1 := b800106d0_m1 h₁
  have m2 := b800106d0_m2 h₁
  rw [x2, outM] at m0 m1 m2
  have f : MemFrame u u₁ (s.getReg .x10) 48 :=
    h₁.memFrame (by rv_eval [x2, outM]; and_intros <;> addr_omega [ho])
  have k₁ := b800106d0_keeps h₁
  have S₁ : Saved s u₁ := h.saved.step (by addr_omega [hb]) (k₁ .x2 (by decide)) fun y h1 h2 ↦
    f y (by addr_omega [h1, h2, hb, ho, hpre.outStack])
  obtain ⟨t, hr, pc, pres, hm⟩ := epilogue hpre (b800106d0_pc h₁) S₁
  obtain ⟨hp, mono, F, hn, -⟩ := out_post hpre h f
  have nx : heapNext t = heapNext u₁ := by simp only [heapNext, hm]
  have hc : vecCap t (s.getReg .x10) = errNiche := by simp only [vecCap, hm]; exact m2
  refine ⟨t, hr₁.trans hr, pc, pres, ⟨nx ▸ hp.lo, nx ▸ hp.hi⟩, nx ▸ mono, fun T hT ↦ ?_,
    (F.mono fun a h ↦ ?_).trans (DFrame.of_same hm _) fun _ h ↦ h, fun hne ↦ absurd hc hne,
    fun _ ↦ by rw [hm, m1]; exact x23⟩
  · rw [show optEListAt s (s.getReg .x14) (s.getReg .x15).toNat = eqsOf s from rfl, fails T hT]
    exact hc
  · rcases h with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, nx ▸ h.2⟩))))

/-- There are fewer than `2 ^ 32` equalities. -/
theorem n_lt {s : MachineState} (hpre : SumcheckPre s) : (s.getReg .x15).toNat < 2 ^ 32 := by
  rcases hpre.eqs with h | h
  · rw [h]; decide
  · simp only [Region, Mapped] at h; omega

/-- At `0x80010698`: every round done, the `Vec` at `S - 200`. -/
structure Exit (s u : MachineState) (ptr : Word) : Prop where
  fr : Fr s u
  x9 : u.getReg .x9 = s.getReg .x12
  outM : u.getMem (s.getReg .x2 - 208) = s.getReg .x10
  capM : u.getMem (s.getReg .x2 - 200) = s.getReg .x15
  ptrM : u.getMem (s.getReg .x2 - 192) = ptr
  lenM : u.getMem (s.getReg .x2 - 184) = s.getReg .x15
  buf : NewBuf s u ptr ((s.getReg .x15).toNat * 24) 8
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T',
    (pre s (s.getReg .x15).toNat).run T =
      some ((eListAt u ptr (s.getReg .x15).toNat, eAt u (s.getReg .x12)), T') ∧
    TranscriptAt u (s.getReg .x11) T'

set_option maxHeartbeats 1000000 in
/-- `0x80010698`: `Ok((point, claim))`, then return. -/
theorem exitOk {s u : MachineState} {ptr : Word} (hpre : SumcheckPre s) (hpc : u.pc = 0x80010698)
    (h : Exit s u ptr) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ SumcheckPost s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hc := hpre.claim
  have x2 := h.fr.saved.x2
  have x9 := h.x9
  have outM := h.outM
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010698_spec hpc (by
    rv_eval [x2, outM, x9]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho])
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have m0 := b80010698_m0 h₁
  have m1 := b80010698_m1 h₁
  have m2 := b80010698_m2 h₁
  have m3 := b80010698_m3 h₁
  have m4 := b80010698_m4 h₁
  have m5 := b80010698_m5 h₁
  rv_eval [x2, outM, x9, h.capM, h.ptrM, h.lenM] at m0 m1 m2 m3 m4 m5
  have f : MemFrame u u₁ (s.getReg .x10) 48 :=
    h₁.memFrame (by rv_eval [x2, outM]; and_intros <;> addr_omega [ho])
  have k₁ := b80010698_keeps h₁
  have S₁ : Saved s u₁ := h.fr.saved.step (by addr_omega [hb]) (k₁ .x2 (by decide)) fun y h1 h2 ↦
    f y (by addr_omega [h1, h2, hb, ho, hpre.outStack])
  obtain ⟨t, hr, pc, pres, hm⟩ := epilogue hpre (b80010698_pc h₁) S₁
  obtain ⟨hp, mono, F, hn, hT₁⟩ := out_post hpre h.fr f
  have nx : heapNext t = heapNext u₁ := by simp only [heapNext, hm]
  have hnl := n_lt hpre
  have hcap : vecCap t (s.getReg .x10) = s.getReg .x15 := by simp only [vecCap, hm]; exact m5
  have hptr : vecPtr t (s.getReg .x10) = ptr := by simp only [vecPtr, hm]; exact m4
  have hlen : vecLen t (s.getReg .x10) = s.getReg .x15 := by simp only [vecLen, hm]; exact m3
  have hne : s.getReg .x15 ≠ errNiche := fun e ↦ by
    have h1 : (errNiche : Word).toNat = 18446744073709551615 := rfl
    rw [e, h1] at hnl
    exact absurd hnl (by decide)
  have hbuf := h.buf
  have hlo := hpre.heap.lo
  have hof := hpre.outFree
  have hhi := h.fr.heap.hi
  simp only [NewBuf] at hbuf
  have nb : NewBuf s t ptr ((s.getReg .x15).toNat * 24) 8 := by
    simp only [NewBuf, nx, hn]; omega
  have el : eListAt t ptr (s.getReg .x15).toNat = eListAt u ptr (s.getReg .x15).toNat := by
    rw [(DFrame.of_same hm fun _ ↦ False).eListAt fun _ _ h ↦ h]
    exact (DFrame.of_memFrame f).eListAt fun i hi hw ↦ by addr_omega [hw, hi, hbuf, ho, hof, hhi]
  have ec : eAt t (s.getReg .x10 + 24) = eAt u (s.getReg .x12) := by
    refine eAt_congr ?_ ?_ ?_
    · rw [hm, m2]
    · rw [hm, show s.getReg .x10 + 24 + 8 = s.getReg .x10 + 32 by ring, m1]
    · rw [hm, show s.getReg .x10 + 24 + 16 = s.getReg .x10 + 40 by ring, m0]
  have hvo : VecOk t (s.getReg .x10) 24 8 := by
    refine ⟨?_, by rw [hlen, hcap]⟩
    simp only [RawVecOk, Buf, hptr, hcap, nx, hn]; omega
  refine ⟨t, hr₁.trans hr, pc, pres, ⟨nx ▸ hp.lo, nx ▸ hp.hi⟩, nx ▸ mono, fun T hT ↦ ?_,
    (F.mono fun a h ↦ ?_).trans (DFrame.of_same hm _) fun _ h ↦ h,
    fun _ ↦ ⟨hvo, by rw [hptr, hcap]; exact nb⟩, fun he ↦ absurd (hcap ▸ he) hne⟩
  · obtain ⟨T', hrun, hT'⟩ := h.value T hT
    rw [show optEListAt s (s.getReg .x14) (s.getReg .x15).toNat = eqsOf s from rfl, ← pre_all, hrun]
    refine ⟨by rw [hcap]; exact hne, ⟨hvo, by rw [hptr, hcap]; exact nb, ?_⟩, ec, ?_⟩
    · simp only [vecEs, hptr, hlen]; exact el
    · exact (hT₁ T' hT').congr hm
  · rcases h with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, nx ▸ h.2⟩))))

end Rv64Verifier.Transcript.Sumcheck
