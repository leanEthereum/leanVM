import Rv64Verifier.Proofs.Pcs.VsoFoldLoop
import Rv64Verifier.Proofs.Pcs.VsoQueries

/-!
# `verify_stacked_opening`'s level loop: what a level opens

After its fold rounds (`0x8000a304`) a level reads its residual (the final level) or commits to
the next level's root, samples the out-of-domain point, reads its value and the intro message
(`0x8000a534`), and goes on at `0x8000a790` (`Opened`). The next root lives in the frame until
the level's end copies it over the root: its bytes `0..6` at `S - 592`, then doublewords at
`S - 944` (bytes `7..14`), `S - 952` (`15..22`), `S - 920` (byte `23`) and `S - 936`
(`24..31`) (`NR`). The pending claims (`Vec<(Vec<E>, GluedWeight)>`, 80-byte elements) are at
`S - 616`, the residual's buffer and length in `ra`/`t6`.

The commitment appends to the transcript's roots, so the mirror's relation carries the roots read
since the level's head (`RunsC`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The mirror, roots appended -/

/-- `Runs`, with the roots `nx` read since the level's head appended. -/
def RunsC (s u : MachineState) (ℓ : ℕ) (m : Model.TM Unit) (nx : List (Digest × ℕ × ℕ)) : Prop :=
  ∀ T, TranscriptAt s (s.getReg .x10) T →
    VsoOpeningsAt s (s.getReg .x10) T →
    T.roots = [(digestAt s (s.getReg .x11),
      Model.stackShape (s.getReg .x12).toNat (s.getReg .x13).toNat)] →
    ∃ T' R, (Model.Pcs.verifyStackedOpeningRust (s.getReg .x12).toNat (s.getReg .x13).toNat
        (claimsOf s)).run T = m.run T' ∧
      TranscriptAt u (s.getReg .x10) T' ∧ T'.proof = T.proof ∧
      T'.openingOffset = T.openingOffset + ℓ ∧ T'.roots = R ++ nx ∧ R.length = ℓ + 1 ∧
      (R[ℓ]?).map Prod.fst = some (digestAt u (s.getReg .x11)) ∧
      (ℓ = 0 → R = T.roots) ∧ (0 < ℓ → (R[ℓ]?).map Prod.snd = some (rootShape s ℓ))

theorem Runs.toC {s u : MachineState} {ℓ : ℕ} {m : Model.TM Unit} (h : Runs s u ℓ m) :
    RunsC s u ℓ m [] := fun T hT hO hr ↦ by
  obtain ⟨T', e, hT', p, o, l, d, z, sh⟩ := h T hT hO hr
  exact ⟨T', T'.roots, e, hT', p, o, (List.append_nil _).symm, l, d, z, sh⟩

/-- A step of the mirror that keeps the proof and the opening offset and appends `nx'` to the
roots. -/
theorem RunsC.bind {α : Type} {s u v : MachineState} {ℓ : ℕ} {m : Model.TM α}
    {k : α → Model.TM Unit} {nx nx' : List (Digest × ℕ × ℕ)} (a : α)
    (h : RunsC s u ℓ (m >>= k) nx)
    (hd : digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11))
    (hstep : ∀ T, TranscriptAt u (s.getReg .x10) T → ∃ T', m.run T = some (a, T') ∧
      TranscriptAt v (s.getReg .x10) T' ∧ T'.proof = T.proof ∧
      T'.openingOffset = T.openingOffset ∧ T'.roots = T.roots ++ nx') :
    RunsC s v ℓ (k a) (nx ++ nx') := by
  intro T hT hO hr
  obtain ⟨T₁, R, e₁, hT₁, p₁, o₁, r₁, l₁, d₁, z₁, sh₁⟩ := h T hT hO hr
  obtain ⟨T₂, e₂, hT₂, p₂, o₂, r₂⟩ := hstep T₁ hT₁
  exact ⟨T₂, R, e₁.trans (run_bind_of e₂), hT₂, p₂.trans p₁, by rw [o₂, o₁],
    by rw [r₂, r₁, List.append_assoc], l₁, by rw [hd, d₁], z₁, sh₁⟩

/-- A step of the machine alone. -/
theorem RunsC.same {s u v : MachineState} {ℓ : ℕ} {m : Model.TM Unit}
    {nx : List (Digest × ℕ × ℕ)} (h : RunsC s u ℓ m nx)
    (hd : digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11))
    (hT : ∀ T, TranscriptAt u (s.getReg .x10) T → TranscriptAt v (s.getReg .x10) T) :
    RunsC s v ℓ m nx := by
  intro T₀ hT₀ hO hr
  obtain ⟨T₁, R, e₁, hT₁, p₁, o₁, r₁, l₁, d₁, z₁, sh₁⟩ := h T₀ hT₀ hO hr
  exact ⟨T₁, R, e₁, hT _ hT₁, p₁, o₁, r₁, l₁, by rw [hd, d₁], z₁, sh₁⟩

/-- A frame within `NS` that misses the root keeps the mirror. -/
theorem RunsC.keep {s u v : MachineState} {ℓ : ℕ} {m : Model.TM Unit}
    {nx : List (Digest × ℕ × ℕ)} {n : Word} {X : Word → Prop} (hpre : VsoPre s)
    (h : RunsC s u ℓ m nx) (hinv : InvR s u n) (hX : DFrame u v X) (hXs : ∀ a, X a → NS s a)
    (hr : ∀ y, Within y (s.getReg .x11) 32 → ¬ X y) : RunsC s v ℓ m nx :=
  h.same (digest_keep hX (root_bound hpre) hr) fun _ hT ↦ tr_keep hpre hinv hT hX hXs

/-! ## What the opening writes -/

/-- From the fold rounds' end `t` on: the spills `S - 1032`..`S - 904`, the slots `S - 896`,
`S - 872`, `S - 808`, `S - 792`, `S - 616`..`S - 528`, `S - 464`..`S - 440`, `S - 384`..`S - 352`,
the callees' stacks, `NEXT`, the sponge and offsets, the heap allocated since `t`. -/
def OW (s t u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1032) 128 ∨ Within a (s.getReg .x2 - 896) 8 ∨
    Within a (s.getReg .x2 - 872) 8 ∨ Within a (s.getReg .x2 - 808) 8 ∨
    Within a (s.getReg .x2 - 792) 8 ∨ Within a (s.getReg .x2 - 616) 88 ∨
    Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 384) 32 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ W s a ∨ Fresh t u a

theorem OW.of_heap {s t u v : MachineState} {a : Word} (h : heapNext u ≤ heapNext v)
    (ha : OW s t u a) : OW s t v a := by
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ha)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ha))))))))))
  · simp only [Fresh] at ha
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨ha.1, by omega⟩))))))))))

/-! ## The next root in the frame -/

/-- The digest `d` in the frame's spills, as the level's end reads it back. -/
def NR (u : MachineState) (S : Word) (d : Digest) : Prop :=
  u.getMem (S - 592) &&& 0x00ffffffffffffff = d[0].toBitVec &&& 0x00ffffffffffffff ∧
    u.getMem (S - 944) = d[0].toBitVec >>> 56 ||| d[1].toBitVec <<< 8 ∧
    u.getMem (S - 952) = d[1].toBitVec >>> 56 ||| d[2].toBitVec <<< 8 ∧
    u.getMem (S - 920) = d[2].toBitVec >>> 56 ∧
    u.getMem (S - 936) = d[3].toBitVec

/-! ## The pending claims -/

/-- `n` pending claims from `p`: the intro message and the weight. -/
def pendAt (u : MachineState) (p : Word) (n : ℕ) :
    List (List E × Model.Pcs.GluedWeightRust) :=
  (List.range n).map fun i ↦
    (vecEs u (p + BitVec.ofNat 64 (80 * i)), weightAt u (p + BitVec.ofNat 64 (80 * i) + 24))

/-- `y` is a byte of the pending claims' buffers at `A`. -/
def PBufs (u : MachineState) (A y : Word) : Prop :=
  Within y (vecPtr u A) ((vecCap u A).toNat * 80) ∨ ∃ i < (vecLen u A).toNat,
    Within y (vecPtr u (vecPtr u A + BitVec.ofNat 64 (80 * i)))
      ((vecCap u (vecPtr u A + BitVec.ofNat 64 (80 * i))).toNat * 24) ∨
    InBufs u (vecPtr u A + BitVec.ofNat 64 (80 * i) + 24) y

/-- The pending claims at `A`, every buffer allocated since `t`. -/
structure PendOk (u t : MachineState) (A : Word) (pend : List (List E × Model.Pcs.GluedWeightRust)) :
    Prop where
  vec : VecOk u A 80 8
  elems : pendAt u (vecPtr u A) (vecLen u A).toNat = pend
  intro : ∀ i < (vecLen u A).toNat, VecOk u (vecPtr u A + BitVec.ofNat 64 (80 * i)) 24 8
  ood : ∀ i < (vecLen u A).toNat,
    u.getMem (vecPtr u A + BitVec.ofNat 64 (80 * i) + 24) = 0xffffffffffffffff ∧
    VecOk u (vecPtr u A + BitVec.ofNat 64 (80 * i) + 24 + 8) 24 8
  fresh : ∀ y, PBufs u A y → heapNext t ≤ y.toNat ∧ y.toNat < heapNext u

/-! ## At `0x8000a790` -/

/-- The levels after level `ℓ`'s. -/
abbrev restOf (s : MachineState) (ℓ : ℕ) : List (ℕ × ℕ) :=
  ((cfgOf s).folds.zip (cfgOf s).logInvRates).drop (ℓ + 1)

/-- The roots level `ℓ` reads: the next level's, unless `ℓ` is the last. -/
def nextRoots (s : MachineState) (ℓ : ℕ) (d : Digest) : List (Digest × ℕ × ℕ) :=
  if ℓ = K0 s + 1 then [] else [(d, rootShape s (ℓ + 1))]

/-- At `0x8000a790`, level `ℓ` opened from `t` (`0x8000a304`): the residual `res` (the final
level's) at `ra`/`t6`, the pending claims `pend` at `S - 616`, the next root `d` in the frame. -/
structure Opened (s : MachineState) (x : LCtx) (h t u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q res : List E)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (d : Digest) : Prop where
  fo : Folded s x h t ℓ Wl lf q
  fr : DFrame t u (OW s t u)
  inv : InvR s u (u.getMem nextAddr)
  heap : HeapOk u
  mono : heapNext t ≤ heapNext u
  pc : u.pc = 0x8000a790
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  x9 : u.getReg .x9 = x.FP
  m144 : u.getMem (s.getReg .x2 - 896) = t.getReg .x22
  m232 : u.getMem (s.getReg .x2 - 808) = t.getReg .x23
  m112 : u.getMem (s.getReg .x2 - 928) = BitVec.ofNat 64 (Wl.folds ++ lf).length
  m128 : u.getMem (s.getReg .x2 - 912) = s.getReg .x12
  m168 : u.getMem (s.getReg .x2 - 872) =
    BitVec.ofNat 64 ((s.getReg .x12).toNat - (Wl.folds ++ lf).length)
  m248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8
  rsd : eListAt u (u.getReg .x1) (u.getReg .x31).toNat = res ∧ (u.getReg .x1).toNat % 8 = 0 ∧
    ((u.getReg .x31).toNat = 0 ∨ heapNext t ≤ (u.getReg .x1).toNat ∧
      (u.getReg .x1).toNat + 24 * (u.getReg .x31).toNat ≤ heapNext u)
  pnd : PendOk u t (s.getReg .x2 - 616) pend
  root : NR u (s.getReg .x2) d
  last : ℓ = K0 s + 1 → d = digestAt u (s.getReg .x11)
  value : RunsC s u ℓ (Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ
    (fcOf s ℓ) (rtOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf (res, pend))
    (nextRoots s ℓ d)

/-! ## The level's fold count -/

theorem ladder_sum (s : MachineState) {ℓ : ℕ} (h : ℓ < K0 s + 2) :
    ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum = 6 + 4 * ℓ := by
  induction ℓ with
  | zero => rfl
  | succ i ih =>
    rw [List.take_add_one, List.sum_append, ih (by omega)]
    have hi : i + 1 < (Model.Pcs.ladderFolds (K0 s + 1)).length := by
      simp only [Model.Pcs.ladderFolds, List.length_cons, List.length_replicate]; omega
    rw [List.getElem?_eq_getElem hi]
    simp only [Model.Pcs.ladderFolds, List.getElem_cons_succ, List.getElem_replicate,
      Option.toList_some, List.sum_cons, List.sum_nil]
    omega

/-- The folds through level `ℓ` leave a message of at least two variables. -/
theorem folds_le {s : MachineState} {QP QL : Word} (hc : Cfg s QP QL) {ℓ : ℕ}
    (h : ℓ < K0 s + 2) : ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum + 2 ≤
      (s.getReg .x12).toNat := by
  rw [ladder_sum s h]
  have := hc.logN
  simp only [K0] at h
  omega

end Rv64Verifier.Proofs.Pcs.Vso
