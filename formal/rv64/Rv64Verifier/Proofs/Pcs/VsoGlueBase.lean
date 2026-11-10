import Rv64Verifier.Proofs.Pcs.VsoFinalToCheck

/-!
# `verify_stacked_opening`'s final level: the glued claims' loop, its frame and its pieces

From `TB`'s state `v` (`0x8000bab0`), the loop at `0x8000bb58` rebinds every glued claim at the
terminal point and adds it, scaled, to the weight at `S - 184`. `GLW` is what it writes from a
state whose `NEXT` is `lo` on, `GS` its frame from `v`. A queries weight runs `induced_weight`
inline, in three pieces: the subspace roots (`RootsSpec`, `0x8000bbb0` to `0x8000bdc0`), their
inverses (`InvsSpec`, to `0x8000be44`) and the queries' products (`ProdsSpec`, to `0x8000baf8`).
Each piece writes `GLW` from its own start, so the buffers allocated before it are kept.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## What the loop writes -/

/-- What the loop writes from `NEXT = lo` on, `NEXT` at `hi`: the scratch slots `S - 888`..`S - 864`,
`S - 856`..`S - 776`, `S - 464`..`S - 352` and `S - 256`..`S - 104`, the callees' stacks, `NEXT`,
the heap from `lo`. -/
def GLW (s : MachineState) (lo : ℕ) (hi a : Word) : Prop :=
  Within a (s.getReg .x2 - 888) 24 ∨ Within a (s.getReg .x2 - 856) 80 ∨
    Within a (s.getReg .x2 - 464) 112 ∨ Within a (s.getReg .x2 - 256) 152 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ (lo ≤ a.toNat ∧ a.toNat < hi.toNat)

theorem GLW.mono {s : MachineState} {lo lo' : ℕ} {hi hi' a : Word} (h1 : lo' ≤ lo)
    (h2 : hi.toNat ≤ hi'.toNat) (h : GLW s lo hi a) : GLW s lo' hi' a := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))

/-- The heap below `lo` misses it. -/
theorem GLW.low {s : MachineState} (hpre : VsoPre s) {lo : ℕ} {hi a : Word} (hlo : lo ≤ heapEnd)
    (h2 : a.toNat < lo) : ¬ GLW s lo hi a := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hlo hab
  intro h
  rcases h with h | h | h | h | h | h | h
  · addr_omega [h, h2, hlo, hab, hb]
  · addr_omega [h, h2, hlo, hab, hb]
  · addr_omega [h, h2, hlo, hab, hb]
  · addr_omega [h, h2, hlo, hab, hb]
  · addr_omega [h, h2, hlo, hab, hb]
  · addr_omega [h, h2, hlo]
  · omega

/-- The frame's other slots miss it. -/
theorem GLW.stk {s : MachineState} (hpre : VsoPre s) {lo : ℕ} {hi a : Word} (hhi : hi.toNat ≤ heapEnd)
    (hy : (s.getReg .x2 - 1040).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 888).toNat ∨
      (s.getReg .x2 - 864).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 856).toNat ∨
      (s.getReg .x2 - 776).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 464).toNat ∨
      (s.getReg .x2 - 352).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 256).toNat ∨
      (s.getReg .x2 - 104).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2).toNat) :
    ¬ GLW s lo hi a := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab hhi
  intro h
  rcases h with h | h | h | h | h | h | h <;> rcases hy with hy | hy | hy | hy | hy
  all_goals first
    | addr_omega [h, hy, hb]
    | addr_omega [h, hy, hb, hnx]
    | addr_omega [h.2, hy, hb, hab, hhi]

/-- The loop's writes are the tail's. -/
theorem GLW.tw {s u : MachineState} (hpre : VsoPre s) {lo : ℕ} {hi a : Word}
    (hlo : heapNext u ≤ lo) (h : GLW s lo hi a) : TW s u hi a := by
  have hb := bounds hpre
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inr (Or.inl (by addr_omega [h, hb]))
  · exact Or.inr (Or.inl (by addr_omega [h, hb]))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h.2⟩))))

/-! ## The loop's frame -/

/-- The loop's frame at `w`, from `v` on. -/
structure GS (s v w : MachineState) : Prop where
  inv : InvR s w (w.getMem nextAddr)
  fr : DFrame v w (GLW s (heapNext v) (w.getMem nextAddr))
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040
  sv : heapNext s ≤ heapNext v

section
variable {s v w : MachineState}

theorem GS.su (h : GS s v w) : heapNext s ≤ heapNext w := Nat.le_trans h.sv h.mono

/-- One more step whose writes are the loop's, from `w` on. -/
theorem GS.step (hpre : VsoPre s) (h : GS s v w) {w' : MachineState} {X : Word → Prop}
    (hX : DFrame w w' X) (hXs : ∀ a, X a → GLW s (heapNext w) (w'.getMem nextAddr) a)
    (hheap : HeapOk w') (hmono : heapNext w ≤ heapNext w') (hsp : w'.getReg .x2 = w.getReg .x2) :
    GS s v w' := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsu := h.su
  have hhi := hheap.hi
  refine ⟨Inv.step' hpre h.inv hX (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hhi hsp,
    (h.fr.mono fun a ha ↦ ha.mono (Nat.le_refl _) hmono).trans hX
      (fun a ha ↦ (hXs a ha).mono h.mono (Nat.le_refl _)), hheap, Nat.le_trans h.mono hmono,
    hsp.trans h.sp, h.sv⟩
  · rcases hXs a ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hsu ha.1, ha.2⟩))
  · rcases hXs a ha with ha | ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · have hab := hpre.stack.above
      rw [stackLo_vso] at hab
      simp only [heapEnd] at hhi hab
      addr_omega [ha.2, hb, hhi, hab]

/-- The loop's stack writes: its scratch slots and the callees' stacks. -/
def GLS (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 888) 24 ∨ Within a (s.getReg .x2 - 856) 80 ∨
    Within a (s.getReg .x2 - 464) 112 ∨ Within a (s.getReg .x2 - 256) 152 ∨
    Within a (s.getReg .x2 - 2464) 1424

theorem GLS.gw {a : Word} (lo : ℕ) (hi : Word) (h : GLS s a) : GLW s lo hi a := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- A step writing only the loop's stack slots: `NEXT` kept. -/
theorem GS.stepS (hpre : VsoPre s) (h : GS s v w) {w' : MachineState} {X : Word → Prop}
    (hX : DFrame w w' X) (hXs : ∀ a, X a → GLS s a) (hsp : w'.getReg .x2 = w.getReg .x2) :
    GS s v w' ∧ w'.getMem nextAddr = w.getMem nextAddr := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have nx : w'.getMem nextAddr = w.getMem nextAddr := hX _ fun i hi hw ↦ by
    rcases hXs _ hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hnx]
  have hn : heapNext w' = heapNext w := by simp only [heapNext, nx]
  exact ⟨h.step hpre hX (fun a ha ↦ (hXs a ha).gw (heapNext w) (w'.getMem nextAddr))
    ⟨by rw [hn]; exact h.heap.lo, by rw [hn]; exact h.heap.hi⟩ (by rw [hn]) hsp, nx⟩

/-- A step writing no memory. -/
theorem GS.same (hpre : VsoPre s) (h : GS s v w) {w' : MachineState}
    (hm : ∀ a, w'.getMem a = w.getMem a) (hsp : w'.getReg .x2 = w.getReg .x2) : GS s v w' :=
  (h.stepS hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) hsp).1

/-- A word of the heap allocated before `v` is kept. -/
theorem GS.keepLow (hpre : VsoPre s) (h : GS s v w) {y : Word} (h1 : heapNext s ≤ y.toNat)
    (h2 : y.toNat + 8 ≤ heapNext v) : w.getMem y = v.getMem y := by
  have hhi := h.heap.hi
  have hm := h.mono
  simp only [heapEnd] at hhi
  exact h.fr y fun i hi ↦ GLW.low (a := y + BitVec.ofNat 64 i) hpre (by simp only [heapEnd]; omega)
    (by addr_omega [h1, h2, hi, hhi, hm])

/-- `n` elements of the heap allocated before `v` are kept. -/
theorem GS.eListLow (hpre : VsoPre s) (h : GS s v w) {p : Word} {n : ℕ}
    (hn : n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + 24 * n ≤ heapNext v) :
    eListAt w p n = eListAt v p n := by
  have hhv := h.heap.hi
  have hm := h.mono
  simp only [heapEnd] at hhv
  rcases hn with h0 | h0
  · subst h0; rfl
  · exact DFrame.eList h.fr (fun y hy ↦ GLW.low (a := y) hpre (by simp only [heapEnd]; omega)
      (by simp only [Within] at hy; omega)) (Or.inr (by omega))

/-- A frame slot the loop does not write is kept. -/
theorem GS.keepStk (hpre : VsoPre s) (h : GS s v w) {y : Word}
    (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 888).toNat ∨
      (s.getReg .x2 - 864).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 856).toNat ∨
      (s.getReg .x2 - 776).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat ∨
      (s.getReg .x2 - 352).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 256).toNat ∨
      (s.getReg .x2 - 104).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
    w.getMem y = v.getMem y := by
  have hb := bounds hpre
  refine h.fr y fun i hi ↦ GLW.stk hpre h.heap.hi ?_
  rcases hy with hy | hy | hy | hy | hy
  · exact Or.inl (by addr_omega [hy, hi, hb])
  · exact Or.inr (Or.inl (by addr_omega [hy, hi, hb]))
  · exact Or.inr (Or.inr (Or.inl (by addr_omega [hy, hi, hb])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hi, hb]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hy, hi, hb]))))

end

/-- From `TB`'s state: the frame, empty. -/
theorem GS.init {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E}
    (hpre : VsoPre s) (h : TB OA s x u v Wl residual tf rt w0) : GS s v v :=
  ⟨h.toTI.inv hpre, DFrame.refl _ _, h.heap, Nat.le_refl _, h.sp, h.toTI.su⟩

/-- The tail's invariant, through the loop. -/
theorem GS.ti {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E}
    (hpre : VsoPre s) (h0 : TB OA s x u v Wl residual tf rt w0) (h : GS s v w) :
    TI OA s x u w Wl residual :=
  h0.toTI.trans h.fr (fun _ ha ↦ GLW.tw hpre h0.mono ha) h.heap h.mono (h.sp.trans h0.sp.symm)

/-! ## The pieces of a queries weight -/

/-- The slots the loop keeps through a queries weight: the end, the claim, the point's suffix, the
scalar and the weight. -/
@[rv_addr] def GK (s : MachineState) (y : Word) : Prop :=
  y = s.getReg .x2 - 880 ∨ y = s.getReg .x2 - 872 ∨ y = s.getReg .x2 - 848 ∨
    y = s.getReg .x2 - 232 ∨ y = s.getReg .x2 - 224 ∨ y = s.getReg .x2 - 216 ∨
    y = s.getReg .x2 - 184 ∨ y = s.getReg .x2 - 176 ∨ y = s.getReg .x2 - 168

/-- `GK`, the queries' and their weights' pointers, the point's length and the fold start. -/
@[rv_addr] def GK2 (s : MachineState) (y : Word) : Prop :=
  GK s y ∨ y = s.getReg .x2 - 856 ∨ y = s.getReg .x2 - 824 ∨ y = s.getReg .x2 - 816 ∨
    y = s.getReg .x2 - 808

/-- At `0x8000bbb0`: the queries weight of the claim at `a`, its message log `n` the length of
the point's suffix, `x9` the fold start and `x18` the point's length. -/
structure QA (s v w : MachineState) (a : Word) (n : ℕ) : Prop where
  gs : GS s v w
  pc : w.pc = 0x8000bbb0
  x8 : w.getReg .x8 = a
  x26 : w.getReg .x26 = BitVec.ofNat 64 n
  x18 : (w.getReg .x18).toNat = (w.getReg .x9).toNat + n
  claim : heapNext s ≤ a.toNat ∧ a.toNat + 88 ≤ heapNext v ∧ a.toNat % 8 = 0

/-- At `0x8000bdc0`: the subspace roots `rs`, `x20` of them in a buffer at `x21` allocated since
`w`; `x19` and `x23` the query weights' and the queries' counts, their pointers at `S - 824` and
`S - 856`, the point's length and the fold start at `S - 816` and `S - 808`. -/
structure QR (s v w w' : MachineState) (a : Word) (n : ℕ) (rs : List K) : Prop where
  gs : GS s v w'
  fr : DFrame w w' (GLW s (heapNext w) (w'.getMem nextAddr))
  pc : w'.pc = 0x8000bdc0
  roots : Model.Pcs.subspaceRootsRust n = some rs
  rlen : rs.length = n + 1
  x20 : w'.getReg .x20 = BitVec.ofNat 64 (n + 1)
  x21 : (w'.getReg .x21).toNat % 8 = 0 ∧ heapNext w ≤ (w'.getReg .x21).toNat ∧
    (w'.getReg .x21).toNat + 8 * (n + 1) ≤ heapNext w'
  rmem : kListAt w' (w'.getReg .x21) (n + 1) = rs
  x19 : w'.getReg .x19 = w.getMem (a + 40)
  x23 : w'.getReg .x23 = w.getMem (a + 16)
  x26 : w'.getReg .x26 = BitVec.ofNat 64 n
  m856 : w'.getMem (s.getReg .x2 - 856) = w.getMem (a + 8)
  m824 : w'.getMem (s.getReg .x2 - 824) = w.getMem (a + 32)
  m816 : w'.getMem (s.getReg .x2 - 816) = w.getReg .x18
  m808 : w'.getMem (s.getReg .x2 - 808) = w.getReg .x9
  keep : ∀ y, GK s y → w'.getMem y = w.getMem y

/-- `0x8000bbb0` to `0x8000bdc0`: `subspace_roots(n)`. -/
def RootsSpec : Prop :=
  ∀ s v w a n, VsoPre s → QA s v w a n →
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ ∃ rs, QR s v w w' a n rs)

/-- At `0x8000bdc0`: the roots `rs`, `x20` of them, at `x21`, in the heap before `w`. -/
structure QB (s v w : MachineState) (n : ℕ) (rs : List K) : Prop where
  gs : GS s v w
  pc : w.pc = 0x8000bdc0
  x20 : w.getReg .x20 = BitVec.ofNat 64 (n + 1)
  x21 : (w.getReg .x21).toNat % 8 = 0 ∧ heapNext s ≤ (w.getReg .x21).toNat ∧
    (w.getReg .x21).toNat + 8 * (n + 1) ≤ heapNext w
  rmem : kListAt w (w.getReg .x21) (n + 1) = rs

/-- At `0x8000be44`: the roots' inverses in a buffer at `S - 784`'s pointer allocated since `w`;
`x22 = 0`, the registers the loop goes on with kept. -/
structure QI (s v w w' : MachineState) (n : ℕ) (rs : List K) : Prop where
  gs : GS s v w'
  fr : DFrame w w' (GLW s (heapNext w) (w'.getMem nextAddr))
  pc : w'.pc = 0x8000be44
  x19 : w'.getReg .x19 = w.getReg .x19
  x20 : w'.getReg .x20 = w.getReg .x20
  x21 : w'.getReg .x21 = w.getReg .x21
  x23 : w'.getReg .x23 = w.getReg .x23
  x26 : w'.getReg .x26 = w.getReg .x26
  x22 : w'.getReg .x22 = 0
  ip : (w'.getMem (s.getReg .x2 - 784)).toNat % 8 = 0 ∧
    heapNext w ≤ (w'.getMem (s.getReg .x2 - 784)).toNat ∧
    (w'.getMem (s.getReg .x2 - 784)).toNat + 8 * (n + 1) ≤ heapNext w'
  imem : kListAt w' (w'.getMem (s.getReg .x2 - 784)) (n + 1) = rs.map (·⁻¹)
  keep : ∀ y, GK2 s y → w'.getMem y = w.getMem y

/-- `0x8000bdc0` to `0x8000be44`: `roots.iter().map(|value| value.inv()).collect()`. -/
def InvsSpec : Prop :=
  ∀ s v w n rs, VsoPre s → QB s v w n rs →
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ QI s v w w' n rs)

/-- `induced_weight`'s sum, the roots `rs` known. -/
def inducedFold (rs : List K) (xs : List E) (qs : List (BitVec 64)) (qw : List E) : E :=
  (qw.zip qs).foldl (fun total (weight, query) ↦
    let acc := xs.zipIdx.foldl (fun (acc : E × K) (challenge, coordinate) ↦
      (acc.1 * (1 + challenge * ofK (1 + acc.2 * (rs.map (·⁻¹)).getD coordinate 0)),
        acc.2 * acc.2 + rs.getD coordinate 0 * acc.2)) (weight, BF64.ofBitVec query)
    total + acc.1) 0

theorem inducedWeight_eq {n : ℕ} {rs : List K} {xs : List E} {qs : List (BitVec 64)} {qw : List E}
    (hx : xs.length = n) (hr : Model.Pcs.subspaceRootsRust n = some rs) :
    Model.Pcs.inducedWeightRust n qs qw xs = some (inducedFold rs xs qs qw) := by
  simp only [Model.Pcs.inducedWeightRust, hx, ↓reduceIte, hr, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- At `0x8000be44`: the roots `rs` at `x21` and their inverses at `S - 784`'s pointer, `x20 = n + 1`
of each, `x22 = 0`, `x26 = n`; the point's suffix `xs` at `S - 848`'s pointer, `n` of them (the
point's length and the fold start at `S - 816` and `S - 808`); `x19` query weights `qw` at
`S - 824`'s pointer and `x23` queries `qs` at `S - 856`'s; all in the heap before `w`. -/
structure QC (s v w : MachineState) (n : ℕ) (rs : List K) (xs : List E) (qs : List (BitVec 64))
    (qw : List E) : Prop where
  gs : GS s v w
  pc : w.pc = 0x8000be44
  rlen : rs.length = n + 1
  x20 : w.getReg .x20 = BitVec.ofNat 64 (n + 1)
  x21 : (w.getReg .x21).toNat % 8 = 0 ∧ heapNext s ≤ (w.getReg .x21).toNat ∧
    (w.getReg .x21).toNat + 8 * (n + 1) ≤ heapNext w
  rmem : kListAt w (w.getReg .x21) (n + 1) = rs
  x22 : w.getReg .x22 = 0
  x26 : w.getReg .x26 = BitVec.ofNat 64 n
  ip : (w.getMem (s.getReg .x2 - 784)).toNat % 8 = 0 ∧
    heapNext s ≤ (w.getMem (s.getReg .x2 - 784)).toNat ∧
    (w.getMem (s.getReg .x2 - 784)).toNat + 8 * (n + 1) ≤ heapNext w
  imem : kListAt w (w.getMem (s.getReg .x2 - 784)) (n + 1) = rs.map (·⁻¹)
  plen : (w.getMem (s.getReg .x2 - 816)).toNat = (w.getMem (s.getReg .x2 - 808)).toNat + n
  pt : (w.getMem (s.getReg .x2 - 848)).toNat % 8 = 0 ∧ (n = 0 ∨
    heapNext s ≤ (w.getMem (s.getReg .x2 - 848)).toNat ∧
    (w.getMem (s.getReg .x2 - 848)).toNat + 24 * n ≤ heapNext w)
  xs : eListAt w (w.getMem (s.getReg .x2 - 848)) n = xs
  wp : (w.getMem (s.getReg .x2 - 824)).toNat % 8 = 0 ∧ ((w.getReg .x19).toNat = 0 ∨
    heapNext s ≤ (w.getMem (s.getReg .x2 - 824)).toNat ∧
    (w.getMem (s.getReg .x2 - 824)).toNat + 24 * (w.getReg .x19).toNat ≤ heapNext w)
  qw : eListAt w (w.getMem (s.getReg .x2 - 824)) (w.getReg .x19).toNat = qw
  qp : (w.getMem (s.getReg .x2 - 856)).toNat % 8 = 0 ∧ ((w.getReg .x23).toNat = 0 ∨
    heapNext s ≤ (w.getMem (s.getReg .x2 - 856)).toNat ∧
    (w.getMem (s.getReg .x2 - 856)).toNat + 8 * (w.getReg .x23).toNat ≤ heapNext w)
  qs : w.readWords (w.getMem (s.getReg .x2 - 856)) (w.getReg .x23).toNat = qs

/-- At `0x8000baf8`: the weight's value `val` in `x23`, `x25`, `x24`, the slots `GK` kept. -/
structure QO (s v w w' : MachineState) (val : E) : Prop where
  gs : GS s v w'
  pc : w'.pc = 0x8000baf8
  value : E.ofLimbs (BF64.ofBitVec (w'.getReg .x23)) (BF64.ofBitVec (w'.getReg .x25))
    (BF64.ofBitVec (w'.getReg .x24)) = val
  keep : ∀ y, GK s y → w'.getMem y = w.getMem y

/-- `0x8000be44` to `0x8000baf8`: the queries' products, summed. -/
def ProdsSpec : Prop :=
  ∀ s v w n rs xs qs qw, VsoPre s → QC s v w n rs xs qs qw →
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ QO s v w w' (inducedFold rs xs qs qw))

end Rv64Verifier.Proofs.Pcs.Vso
