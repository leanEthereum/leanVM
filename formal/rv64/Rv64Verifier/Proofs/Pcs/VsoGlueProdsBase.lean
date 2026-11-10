import Rv64Verifier.Proofs.Pcs.VsoGlueBase

/-!
# `verify_stacked_opening`'s final level: the queries' products, their frame and model

From `QC`'s state `w` (`0x8000be44`) the queries' loop writes `PrW`: the slots `S - 840`, `S - 832`,
`S - 800`, `S - 792`, `S - 464`..`S - 440`, `S - 160`..`S - 104` and the callees' stacks, nothing in
the heap. `PrX` is that frame and the loop's constants at `t`; `prG` is one coordinate of a query's
product, `prProd` the product.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The model -/

/-- One coordinate of a query's product: the product and the basis value. -/
def prG (rs : List K) (acc : E × K) (p : E × ℕ) : E × K :=
  (acc.1 * (1 + p.1 * ofK (1 + acc.2 * (rs.map (·⁻¹)).getD p.2 0)),
    acc.2 * acc.2 + rs.getD p.2 0 * acc.2)

/-- A query's product. -/
def prProd (rs : List K) (xs : List E) (weight : E) (query : BitVec 64) : E :=
  (xs.zipIdx.foldl (prG rs) (weight, BF64.ofBitVec query)).1

/-- The queries' sum, one more. -/
def prSum (rs : List K) (xs : List E) (total : E) (p : E × BitVec 64) : E :=
  total + prProd rs xs p.1 p.2

theorem prFold_eq (rs : List K) (xs : List E) (qs : List (BitVec 64)) (qw : List E) :
    inducedFold rs xs qs qw = (qw.zip qs).foldl (prSum rs xs) 0 := rfl

theorem pr_foldl_take_succ {α β : Type} (f : β → α → β) (b : β) (l : List α) {i : ℕ}
    (hi : i < l.length) : (l.take (i + 1)).foldl f b = f ((l.take i).foldl f b) l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

theorem pr_kListAt_getD (s : MachineState) (a : Word) {n c : ℕ} (hc : c < n) :
    (kListAt s a n).getD c 0 = BF64.ofBitVec (s.getMem (a + BitVec.ofNat 64 (8 * c))) := by
  simp [kListAt, List.getD_eq_getElem?_getD, hc]

/-! ## The frame -/

/-- What the queries' loop writes. -/
def PrW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 840) 16 ∨ Within a (s.getReg .x2 - 800) 16 ∨
    Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 160) 56 ∨
    Within a (s.getReg .x2 - 2464) 1424

theorem PrW.gls {s : MachineState} (hpre : VsoPre s) {a : Word} (h : PrW s a) : GLS s a := by
  have hb := bounds hpre
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inl (by addr_omega [h, hb]))
  · exact Or.inr (Or.inl (by addr_omega [h, hb]))
  · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- What the loop writes once past its entry: the products' slots and the callees' stacks. -/
def PrN (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 160) 56 ∨
    Within a (s.getReg .x2 - 2464) 1424

theorem PrN.w {s : MachineState} {a : Word} (h : PrN s a) : PrW s a := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The entry's slots: the narrow writes miss them. -/
theorem PrN.slot {s : MachineState} (hpre : VsoPre s) {y : Word}
    (hy : y = s.getReg .x2 - 840 ∨ y = s.getReg .x2 - 832 ∨ y = s.getReg .x2 - 800 ∨
      y = s.getReg .x2 - 792) : ∀ i < 8, ¬ PrN s (y + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  intro i hi hw
  rcases hy with rfl | rfl | rfl | rfl <;> rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb]

/-- The words the loop keeps: the heap, and the frame's other slots. -/
def PrK (s : MachineState) (y : Word) : Prop :=
  y.toNat + 8 ≤ heapEnd ∨
    (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 840).toNat ∨
    (s.getReg .x2 - 824).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 800).toNat ∨
    (s.getReg .x2 - 784).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat ∨
    (s.getReg .x2 - 440).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 160).toNat

theorem PrK.miss {s : MachineState} (hpre : VsoPre s) {y : Word} (hy : PrK s y) :
    ∀ i < 8, ¬ PrW s (y + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  intro i hi hw
  simp only [PrK, heapEnd] at hy
  rcases hw with hw | hw | hw | hw | hw <;> rcases hy with hy | hy | hy | hy | hy <;>
    addr_omega [hw, hi, hy, hb, hab]

/-- The loop's constants at `t`, from `w` on: the frame, the heap as at `w`, the count `cnt`, the
roots' pointer, `24 n`, `n + 2` and `s6 = 0`. -/
structure PrX (s v w t : MachineState) (n cnt : ℕ) : Prop where
  gs : GS s v t
  fr : DFrame w t (PrW s)
  nx : heapNext t = heapNext w
  m800 : t.getMem (s.getReg .x2 - 800) = BitVec.ofNat 64 cnt
  m792 : t.getMem (s.getReg .x2 - 792) = w.getReg .x21
  m832 : t.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 (24 * n)
  m840 : t.getMem (s.getReg .x2 - 840) = BitVec.ofNat 64 (n + 2)
  x22 : t.getReg .x22 = 0

section
variable {s v w t : MachineState} {n cnt : ℕ}

theorem PrX.keep (hpre : VsoPre s) (h : PrX s v w t n cnt) {y : Word} (hy : PrK s y) :
    t.getMem y = w.getMem y :=
  h.fr y (hy.miss hpre)

/-- One more step writing the loop's slots. -/
theorem PrX.step (hpre : VsoPre s) (h : PrX s v w t n cnt) {t' : MachineState} {X : Word → Prop}
    (hX : DFrame t t' X) (hXs : ∀ a, X a → PrN s a) (hsp : t'.getReg .x2 = t.getReg .x2)
    (h22 : t'.getReg .x22 = t.getReg .x22) : PrX s v w t' n cnt := by
  have hb := bounds hpre
  obtain ⟨G, nx⟩ := h.gs.stepS hpre hX (fun a ha ↦ (hXs a ha).w.gls hpre) hsp
  have k (y : Word) (hy : y = s.getReg .x2 - 840 ∨ y = s.getReg .x2 - 832 ∨
      y = s.getReg .x2 - 800 ∨ y = s.getReg .x2 - 792) : t'.getMem y = t.getMem y :=
    hX y fun i hi hw ↦ PrN.slot hpre hy i hi (hXs _ hw)
  refine ⟨G, h.fr.trans hX fun a ha ↦ (hXs a ha).w, by rw [← h.nx]; simp only [heapNext, nx],
    ?_, ?_, ?_, ?_, h22.trans h.x22⟩
  · rw [k _ (Or.inr (Or.inr (Or.inl rfl)))]; exact h.m800
  · rw [k _ (Or.inr (Or.inr (Or.inr rfl)))]; exact h.m792
  · rw [k _ (Or.inr (Or.inl rfl))]; exact h.m832
  · rw [k _ (Or.inl rfl)]; exact h.m840

/-- A step writing no memory. -/
theorem PrX.same (hpre : VsoPre s) (h : PrX s v w t n cnt) {t' : MachineState}
    (hm : ∀ a, t'.getMem a = t.getMem a) (hsp : t'.getReg .x2 = t.getReg .x2)
    (h22 : t'.getReg .x22 = t.getReg .x22) : PrX s v w t' n cnt :=
  h.step hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) hsp h22

end

/-! ## The loop's states -/

/-- At `0x8000bea8`, query `i` next, the sum so far `total` in `s7`, `s9`, `s8`. -/
structure PrQ (s v w t : MachineState) (n cnt i : ℕ) (total : E) : Prop
    extends PrX s v w t n cnt where
  pc : t.pc = 0x8000bea8
  ilt : i < cnt
  x8 : t.getReg .x8 = BitVec.ofNat 64 i
  tot : E.ofLimbs (BF64.ofBitVec (t.getReg .x23)) (BF64.ofBitVec (t.getReg .x25))
    (BF64.ofBitVec (t.getReg .x24)) = total

/-- At `0x8000bf00`, coordinate `c` of query `i` next: the product and the basis value `acc` at
`S - 128` and in `s3`; `s1 = 24 (n - c)`, `s2`, `s4`, `s5` the inverse, the challenge and the
root, `s11 = n + 2 - c`. -/
structure PrI (s v w t : MachineState) (n cnt i c : ℕ) (total : E) (acc : E × K) : Prop
    extends PrX s v w t n cnt where
  pc : t.pc = 0x8000bf00
  ilt : i < cnt
  clt : c < n
  x8 : t.getReg .x8 = BitVec.ofNat 64 i
  tot : E.ofLimbs (BF64.ofBitVec (t.getReg .x23)) (BF64.ofBitVec (t.getReg .x25))
    (BF64.ofBitVec (t.getReg .x24)) = total
  x9 : t.getReg .x9 = BitVec.ofNat 64 (24 * (n - c))
  x18 : t.getReg .x18 = w.getMem (s.getReg .x2 - 784) + BitVec.ofNat 64 (8 * c)
  x20 : t.getReg .x20 = w.getMem (s.getReg .x2 - 848) + BitVec.ofNat 64 (24 * c)
  x21 : t.getReg .x21 = w.getReg .x21 + BitVec.ofNat 64 (8 * c)
  x27 : t.getReg .x27 = BitVec.ofNat 64 (n + 2 - c)
  prod : eAt t (s.getReg .x2 - 128) = acc.1
  basis : BF64.ofBitVec (t.getReg .x19) = acc.2

/-- At `0x8000be84`, query `i`'s product `p` at `S - 128`. -/
structure PrE (s v w t : MachineState) (n cnt i : ℕ) (total p : E) : Prop
    extends PrX s v w t n cnt where
  pc : t.pc = 0x8000be84
  ilt : i < cnt
  x8 : t.getReg .x8 = BitVec.ofNat 64 i
  tot : E.ofLimbs (BF64.ofBitVec (t.getReg .x23)) (BF64.ofBitVec (t.getReg .x25))
    (BF64.ofBitVec (t.getReg .x24)) = total
  prod : eAt t (s.getReg .x2 - 128) = p

/-! ## Field facts -/

theorem pr_kOf_xor (a b : K) : BF64.ofBitVec (a.toBitVec ^^^ b.toBitVec) = a + b := rfl

theorem pr_kOf_xor_one (a : K) : BF64.ofBitVec (a.toBitVec ^^^ 1) = 1 + a := by
  rw [add_comm]; rfl

/-- `1 + e`, its first limb flipped. -/
theorem pr_one_add_eAt {t t' : MachineState} {a b : Word} (h0 : t'.getMem b = t.getMem a ^^^ 1)
    (h1 : t'.getMem (b + 8) = t.getMem (a + 8)) (h2 : t'.getMem (b + 16) = t.getMem (a + 16)) :
    eAt t' b = 1 + eAt t a := by
  apply eq_of_limbs
  rw [limbs_eAt, limbs_add, limbs_one, limbs_eAt, h0, h1, h2]
  simp only [Prod.mk.injEq]
  exact ⟨BitVec.xor_comm _ _, (BitVec.zero_xor).symm, (BitVec.zero_xor).symm⟩

/-- The sum's limbs, one product added. -/
theorem pr_ofLimbs_add {a b c : Word} {t : MachineState} {p : Word} :
    E.ofLimbs (BF64.ofBitVec (t.getMem p ^^^ a)) (BF64.ofBitVec (t.getMem (p + 8) ^^^ b))
      (BF64.ofBitVec (t.getMem (p + 16) ^^^ c)) =
      E.ofLimbs (BF64.ofBitVec a) (BF64.ofBitVec b) (BF64.ofBitVec c) + eAt t p := by
  apply eq_of_limbs
  rw [limbs_add, limbs_eAt, limbs_ofLimbs, limbs_ofLimbs]
  simp only [BF64.toBitVec_ofBitVec, Prod.mk.injEq]
  exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩

end Rv64Verifier.Proofs.Pcs.Vso
