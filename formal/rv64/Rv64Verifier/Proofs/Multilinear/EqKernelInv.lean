import Rv64Verifier.Proofs.Multilinear.EqKernelWin
import Rv64Verifier.Proofs.Multilinear.ScalerNew
import Rv64Verifier.Proofs.Multilinear.Frames

/-!
# `verifier::multilinear::eq_kernel`: the invariants

```rust
pub fn eq_kernel(point: &[E]) -> Vec<E> {
    let mut out = vec![ZERO; 1 << point.len()];
    out[0] = ONE;
    for (k, &r) in point.iter().enumerate() {
        let (low, high) = out[..2 << k].split_at_mut(1 << k);
        let scale = Scaler::new(r, low.len());
        for (v, h) in low.iter_mut().zip(high) {
            *h = scale.mul(*v);
            *v += *h;
        }
    }
    out
}
```

compiled at `0x8000cb38` (`Blocks/F51.lean`), with `S` the entry's `sp` and `n` the point's
length: `0x8000cb38` saves `ra`, `s0`..`s11` in a 208-byte frame and calls
`from_elem(a0, &ZERO, 1 << n)`, the `Vec` going straight to the result; `0x8000cb94` keeps its
length at `S - 184` (trapping on `0`, never), `0x8000cba0` writes `out[0] = ONE` (`s0` = the
buffer `P`) and returns at once for `n = 0`; `0x8000cbb4` keeps the point's end at `S - 192` and
the reciprocal of `24` at `S - 200`. The outer loop at `0x8000cc10` (`a3` = `k`, `a1` = `&point[k]`)
traps unless `2 << k` fits and `k < 63` (never), calls `Scaler::new(S - 136, &point[k], 1 << k)`
at `0x8000cc28`, and sets up the inner loop (`0x8000cc54`..`0x8000cc7c`: `s1` = `s2` = `1 << k`
through a division by `24`, `s4` = `&out[1 << k]`, `s6` = the `Scaler`'s tag, `s3`/`s7` = its
table). The inner loop at `0x8000cd04` (`s9` = `j`, `s2` = `&out[j]`) computes `h` at `S - 160`:
by `mul` (`0x8000cc9c`, `Plain`) or by the table (`EqKernelWin.table_mul`); `0x8000ccb0` writes
`out[j + 2^k] = h`, `out[j] += h`. `0x8000cbf8` moves to the next coordinate; `0x8000ce24`
restores and returns.

`mul`'s contract frames doublewords, so the frame here (`Inv.dw`) is of doublewords, as in
`Powers.lean`. From the allocation on, nothing writes the result (`Mid.step`).
-/

namespace Rv64Verifier.Proofs.Multilinear.EqKernel
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F51 Rv64Verifier.Proofs.Multilinear.ScalerFill
  Rv64Verifier.Proofs.Multilinear.EqKernelWin
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Lists -/

theorem eListAt_getD' (s : MachineState) (p : Word) {n i : Nat} (h : i < n) :
    (eListAt s p n).getD i 0 = eAt s (p + BitVec.ofNat 64 (24 * i)) := by
  rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact h), eListAt_getElem]

/-- A slice apart from what a step writes. -/
theorem eListAt_frame {u v : MachineState} {lo P : Word} {n N : Nat}
    (hfr : ∀ a, ¬ Within a lo n → v.getMem a = u.getMem a) (hap : Apart P (24 * N) lo n)
    (hP : P.toNat + 24 * N ≤ 2 ^ 64) : eListAt v P N = eListAt u P N := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i hi _
  rw [eListAt_length] at hi
  rw [eListAt_getElem, eListAt_getElem]
  unfold eAt
  rw [hfr _ (by addr_omega [hi, hap, hP]), hfr (P + BitVec.ofNat 64 (24 * i) + 8)
      (by addr_omega [hi, hap, hP]), hfr (P + BitVec.ofNat 64 (24 * i) + 16)
      (by addr_omega [hi, hap, hP])]

theorem eListAt_same {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a) (P : Word) (N : Nat) :
    eListAt v P N = eListAt u P N := by
  simp only [eListAt, eAt, h]

/-- Two elements written, the rest kept. -/
theorem eListAt_set2 {u v : MachineState} {P : Word} {N i₁ i₂ : Nat} (h1 : i₁ < N) (h2 : i₂ < N)
    (hne : i₁ ≠ i₂) (hP : P.toNat + 24 * N ≤ 2 ^ 64)
    (hfr : ∀ a, ¬ Within a (P + BitVec.ofNat 64 (24 * i₁)) 24 →
      ¬ Within a (P + BitVec.ofNat 64 (24 * i₂)) 24 → v.getMem a = u.getMem a) :
    eListAt v P N = ((eListAt u P N).set i₁ (eAt v (P + BitVec.ofNat 64 (24 * i₁)))).set i₂
      (eAt v (P + BitVec.ofNat 64 (24 * i₂))) := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i hi₁ hi₂
  rw [eListAt_length] at hi₁
  rw [List.getElem_set, List.getElem_set]
  split
  · subst i₂; rw [eListAt_getElem]
  · split
    · subst i₁; rw [eListAt_getElem]
    · rename_i hn2 hn1
      rw [eListAt_getElem, eListAt_getElem]
      unfold eAt
      rw [hfr _ (by addr_omega [hi₁, h1, h2, hn1, hP]) (by addr_omega [hi₁, h1, h2, hn2, hP]),
        hfr (P + BitVec.ofNat 64 (24 * i) + 8) (by addr_omega [hi₁, h1, h2, hn1, hP])
          (by addr_omega [hi₁, h1, h2, hn2, hP]),
        hfr (P + BitVec.ofNat 64 (24 * i) + 16) (by addr_omega [hi₁, h1, h2, hn1, hP])
          (by addr_omega [hi₁, h1, h2, hn2, hP])]

/-- One element written, the rest kept. -/
theorem eListAt_set1 {u v : MachineState} {P : Word} {N i₁ : Nat} (h1 : i₁ < N)
    (hP : P.toNat + 24 * N ≤ 2 ^ 64)
    (hfr : ∀ a, ¬ Within a (P + BitVec.ofNat 64 (24 * i₁)) 24 → v.getMem a = u.getMem a) :
    eListAt v P N = (eListAt u P N).set i₁ (eAt v (P + BitVec.ofNat 64 (24 * i₁))) := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i hi₁ hi₂
  rw [eListAt_length] at hi₁
  rw [List.getElem_set]
  split
  · subst i₁; rw [eListAt_getElem]
  · rename_i hn1
    rw [eListAt_getElem, eListAt_getElem]
    unfold eAt
    rw [hfr _ (by addr_omega [hi₁, h1, hn1, hP]),
      hfr (P + BitVec.ofNat 64 (24 * i) + 8) (by addr_omega [hi₁, h1, hn1, hP]),
      hfr (P + BitVec.ofNat 64 (24 * i) + 16) (by addr_omega [hi₁, h1, hn1, hP])]

/-- The pass for coordinate `k`, as `eq_kernel`'s prefix kernels. -/
theorem pass_eq (pt : List E) {N k : Nat} (hk : k < pt.length) (hN : 2 ^ (k + 1) ≤ N) :
    (List.range (2 ^ k)).foldl (Model.eqKernelStep (pt.getD k 0) (2 ^ k))
        (eqKernel (pt.take k) ++ List.replicate (N - 2 ^ k) 0) =
      eqKernel (pt.take (k + 1)) ++ List.replicate (N - 2 ^ (k + 1)) 0 := by
  have hpow := hN
  rw [pow_succ] at hpow
  have hA : (eqKernel (pt.take k)).length = 2 ^ k := by
    rw [Model.eqKernel_length, List.length_take, Nat.min_eq_left (by omega)]
  have h := Model.eqKernelPass_eq (pt.getD k 0) k (eqKernel (pt.take k)) (N - 2 ^ k) hA
    (by omega)
  rw [Model.eqKernelPass] at h
  rw [h, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.getD_eq_getElem _ _ hk]
  have hk' : eqKernel (pt.take k ++ [pt[k]]) =
      (eqKernel (pt.take k)).map (· * (1 + pt[k])) ++ (eqKernel (pt.take k)).map (· * pt[k]) := by
    simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hk', pow_succ, show N - 2 ^ k - 2 ^ k = N - 2 ^ k * 2 by omega]

/-! ## The frame -/

/-- The length's shift amount, as the machine masks it: `1 << n` allocates `2^(n mod 64)`. -/
def nm (s : MachineState) : Nat := (s.getReg .x12).toNat % 64

theorem nm_lt (s : MachineState) : nm s < 64 := Nat.mod_lt _ (by decide)

theorem nm_le (s : MachineState) : nm s ≤ (s.getReg .x12).toNat := Nat.mod_le _ _

theorem nm_of_lt {s : MachineState} (h : (s.getReg .x12).toNat < 64) :
    nm s = (s.getReg .x12).toNat := Nat.mod_eq_of_lt h

theorem outValid {s : MachineState} (h : EqKernelPre s) : ValidMemRange (s.getReg .x10) 3 := by
  intro i hi
  have ho := h.out
  exact Transcript.Region.valid ho (by addr_omega [ho, hi]) (by addr_omega [ho, hi])
    (by addr_omega [ho, hi])

theorem pointValid {s : MachineState} (h : EqKernelPre s) (hn : 0 < (s.getReg .x12).toNat) :
    ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat) := by
  intro i hi
  have ho := h.point.resolve_left (by omega)
  exact Transcript.Region.valid ho (by addr_omega [ho, hi]) (by addr_omega [ho, hi])
    (by addr_omega [ho, hi])

theorem pointOutside {s : MachineState} (h : EqKernelPre s) (hn : 0 < (s.getReg .x12).toNat) :
    Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat) :=
  h.pointFree.resolve_left (by omega)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25), (96, .x26), (104, .x27)]

theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ 104 := by decide

/-- What the run may have written besides the result, while `NEXT` reached `nx`. -/
@[rv_addr] def LW (s : MachineState) (nx a : Word) : Prop :=
  Within a (stackLo s eqKernelStack) eqKernelStack ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)

@[rv_addr] def PW (s : MachineState) (nx a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ LW s nx a

structure Inv (s u : MachineState) (nx : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 208
  slots : ∀ p ∈ slots, u.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  dw : DwFrame s u (PW s nx)
  next : u.getMem nextAddr = nx
  mono : heapNext s ≤ nx.toNat
  fits : nx.toNat ≤ heapEnd

theorem bounds {s : MachineState} (h : EqKernelPre s) :
    0x78000000 + 1232 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds (outValid h) (by decide)
  simp only [eqKernelStack, mulStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop} (hpre : EqKernelPre s)
    (h : Inv s u nx) (hX : DwFrame u v X) (hsub : ∀ a, X a → PW s nx' a)
    (hslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - 104) 104)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : Inv s v nx' := by
  have hb := bounds hpre
  have mono (a : Word) (ha : PW s nx a) : PW s nx' a := by
    simp only [PW, LW] at ha ⊢
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩))
  refine ⟨hsp.trans h.sp, fun p hp ↦ ?_, ?_, hnx, Nat.le_trans h.mono hle, hend⟩
  · obtain ⟨h1, h2⟩ := slots_ok p hp
    rw [← h.slots p hp]
    exact hX _ (fun hx ↦ hslot _ hx (by addr_omega [hb, h1, h2]))
      (Or.inr fun i hi hx ↦ hslot _ hx (by addr_omega [hb, h1, h2, hi]))
  · intro a ha hb'
    rw [hX a (fun hx ↦ ha (hsub a hx)) (by
        rcases hb' with hb' | hb'
        · exact Or.inl hb'
        · exact Or.inr fun i hi hx ↦ hb' i hi (hsub _ hx))]
    exact h.dw a (fun hx ↦ ha (mono a hx)) (by
      rcases hb' with hb' | hb'
      · exact Or.inl hb'
      · exact Or.inr fun i hi hx ↦ hb' i hi (mono _ hx))

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : EqKernelPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2) : Inv s v nx :=
  h.step hpre (DwFrame.same hm fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    ((hm _).trans h.next) (Nat.le_refl _) h.fits hsp

/-- A doubleword missing what may be written keeps its entry value. -/
theorem Inv.keep {s u : MachineState} {nx : Word} (h : Inv s u nx) {a : Word}
    (ha : ∀ i < 8, ¬ PW s nx (a + BitVec.ofNat 64 i)) : u.getMem a = s.getMem a :=
  h.dw a (by simpa using ha 0 (by decide)) (Or.inr ha)

theorem Inv.rodataOk {s u : MachineState} {nx : Word} (hpre : EqKernelPre s) (h : Inv s u nx) :
    RodataOk u := by
  have hb := bounds hpre
  have hro := hpre.stack.rodata
  have hor := hpre.outRodata
  have hfit := h.fits
  have miss (a : Word) (ha : Within a rodataBase Rv64Verifier.rodataSize) : ¬ PW s nx a := by
    simp only [PW, LW]
    rintro (hw | hw | hw | hw)
    · addr_omega [hw, ha, hor]
    · addr_omega [hw, ha, hro, hb]
    · addr_omega [hw, ha]
    · addr_omega [hw, ha, hfit]
  intro p hp
  have hin := within_of_mem_rodataWords hp
  rw [h.dw p.1 (miss _ (by addr_omega [hin])) (by
    by_cases h8 : p.1.toNat % 8 = 0
    · exact Or.inr fun i hi ↦ miss _ (by addr_omega [hin, hi, h8])
    · exact Or.inl h8)]
  exact hpre.rodata p hp

/-- The point is never written. -/
theorem Inv.point {s u : MachineState} {nx : Word} (hpre : EqKernelPre s) (h : Inv s u nx)
    {i : Nat} (hi : i < (s.getReg .x12).toNat) :
    eAt u (s.getReg .x11 + BitVec.ofNat 64 (24 * i)) =
      eAt s (s.getReg .x11 + BitVec.ofNat 64 (24 * i)) := by
  have hb := bounds hpre
  have he := ValidMemRange.bounds (pointValid hpre (by omega)) (by omega)
  have hef := pointOutside hpre (by omega)
  have hes := hpre.pointStack
  have heo := hpre.pointOut
  have hfit := h.fits
  simp only [Outside] at hef
  have miss (a : Word) (h1 : (s.getReg .x11).toNat + 24 * i ≤ a.toNat)
      (h2 : a.toNat < (s.getReg .x11).toNat + 24 * i + 24) : ¬ PW s nx a := by
    simp only [PW, LW]
    rintro (hw | hw | hw | hw)
    · addr_omega [hw, h1, h2, he, heo, hi]
    · addr_omega [hw, h1, h2, he, hes, hb, hi]
    · addr_omega [hw, h1, h2, he, hef.2, hi]
    · addr_omega [hw, h1, h2, he, hef.1, hfit, hi]
  unfold eAt
  rw [h.keep fun j hj ↦ miss _ (by addr_omega [hj, he, hi]) (by addr_omega [hj, he, hi]),
    h.keep (a := s.getReg .x11 + BitVec.ofNat 64 (24 * i) + 8) fun j hj ↦
      miss _ (by addr_omega [hj, he, hi]) (by addr_omega [hj, he, hi]),
    h.keep (a := s.getReg .x11 + BitVec.ofNat 64 (24 * i) + 16) fun j hj ↦
      miss _ (by addr_omega [hj, he, hi]) (by addr_omega [hj, he, hi])]

/-! ## From the allocation on -/

/-- The point's coordinates. -/
def pt (s : MachineState) : List E := eListAt s (s.getReg .x11) (s.getReg .x12).toNat

theorem DwFrame.keep {u v : MachineState} {X : Word → Prop} (h : DwFrame u v X) {a : Word}
    (ha : ∀ i < 8, ¬ X (a + BitVec.ofNat 64 i)) : v.getMem a = u.getMem a :=
  h a (by simpa using ha 0 (by decide)) (Or.inr ha)

/-- The result's `Vec` (capacity `C`, buffer `P`, length `2^n`), its buffer allocated below
`nx`. -/
structure Res (s u : MachineState) (C P nx : Word) : Prop where
  inv : Inv s u nx
  cap : u.getMem (s.getReg .x10) = C
  ptr : u.getMem (s.getReg .x10 + 8) = P
  len : u.getMem (s.getReg .x10 + 16) = BitVec.ofNat 64 (2 ^ nm s)
  align : P.toNat % 8 = 0
  lo : heapNext s ≤ P.toNat
  room : 2 ^ nm s ≤ C.toNat
  top : P.toNat + 24 * C.toNat ≤ nx.toNat

/-- A step writing `X`, the stack below the saved registers and the heap, keeps the result. -/
theorem Res.step {s u v : MachineState} {C P nx nx' : Word} {X : Word → Prop}
    (hpre : EqKernelPre s) (h : Res s u C P nx) (hX : DwFrame u v X) (hsub : ∀ a, X a → LW s nx' a)
    (hslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - 104) 104)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : Res s v C P nx' := by
  have hb := bounds hpre
  have hof := hpre.outFree
  have hos := hpre.outStack
  simp only [Outside] at hof
  have miss (a : Word) (ha : Within a (s.getReg .x10) 24) : ¬ X a := fun hx ↦ by
    have := hsub a hx
    simp only [LW] at this
    rcases this with hw | hw | hw
    · addr_omega [hw, ha, hos, hb]
    · addr_omega [hw, ha, hof.2]
    · addr_omega [hw, ha, hof.1, hend, hle]
  have w (c : Nat) (hc : c = 0 ∨ c = 8 ∨ c = 16) :
      v.getMem (s.getReg .x10 + BitVec.ofNat 64 c) = u.getMem (s.getReg .x10 + BitVec.ofNat 64 c) :=
    DwFrame.keep hX fun i hi ↦ miss _ (by addr_omega [hc, hi, hb])
  have e0 := w 0 (Or.inl rfl)
  have e1 := w 8 (Or.inr (Or.inl rfl))
  have e2 := w 16 (Or.inr (Or.inr rfl))
  rv_eval [] at e0 e1 e2
  exact ⟨h.inv.step hpre hX (fun a ha ↦ Or.inr (hsub a ha)) hslot hnx hle hend hsp,
    e0.trans h.cap, e1.trans h.ptr, e2.trans h.len, h.align, h.lo, h.room,
    Nat.le_trans h.top hle⟩

/-- The loop's constants: the buffer in `s0`, the table sizes in `s8`, `s10`, `s11`, and at
`S - 200`.. the reciprocal of `24`, the point's end and the length. -/
structure Mid (s u : MachineState) (C P nx : Word) : Prop extends Res s u C P nx where
  x8 : u.getReg .x8 = P
  x24 : u.getReg .x24 = 2112
  x26 : u.getReg .x26 = 704
  x27 : u.getReg .x27 = 1408
  magic : u.getMem (s.getReg .x2 - 200) = 0xaaaaaaaaaaaaaaab
  stop : u.getMem (s.getReg .x2 - 192) =
    s.getReg .x11 + BitVec.ofNat 64 (24 * (s.getReg .x12).toNat)
  nlen : u.getMem (s.getReg .x2 - 184) = BitVec.ofNat 64 (2 ^ nm s)

def midRegs : List Reg := [.x2, .x8, .x24, .x26, .x27]

theorem Mid.step {s u v : MachineState} {C P nx nx' : Word} {X : Word → Prop}
    (hpre : EqKernelPre s) (h : Mid s u C P nx) (hX : DwFrame u v X) (hsub : ∀ a, X a → LW s nx' a)
    (hslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - 104) 104 ∧ ¬ Within a (s.getReg .x2 - 200) 24)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ midRegs, v.getReg r = u.getReg r) : Mid s v C P nx' := by
  have hb := bounds hpre
  have w (c : Nat) (h1 : 184 ≤ c) (h2 : c ≤ 200) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 c) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 c) :=
    DwFrame.keep hX fun i hi hx ↦ (hslot _ hx).2 (by addr_omega [h1, h2, hi, hb])
  exact { toRes := h.toRes.step hpre hX hsub (fun a ha ↦ (hslot a ha).1) hnx hle hend
            (hr _ (by decide))
          x8 := (hr _ (by decide)).trans h.x8
          x24 := (hr _ (by decide)).trans h.x24
          x26 := (hr _ (by decide)).trans h.x26
          x27 := (hr _ (by decide)).trans h.x27
          magic := (w 200 (by decide) (by decide)).trans h.magic
          stop := (w 192 (by decide) (by decide)).trans h.stop
          nlen := (w 184 (by decide) (by decide)).trans h.nlen }

theorem Mid.same {s u v : MachineState} {C P nx : Word} (hpre : EqKernelPre s)
    (h : Mid s u C P nx) (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ midRegs, v.getReg r = u.getReg r) : Mid s v C P nx :=
  h.step hpre (DwFrame.same hm fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    ((hm _).trans h.inv.next) (Nat.le_refl _) h.inv.fits hr

/-- At `0x8000cc10`, the first `k` passes done. -/
structure OInv (s u : MachineState) (C P nx : Word) (k : Nat) : Prop extends Mid s u C P nx where
  pc : u.pc = 0x8000cc10
  lt : k < (s.getReg .x12).toNat
  le : k ≤ nm s
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (24 * k)
  x13 : u.getReg .x13 = BitVec.ofNat 64 k
  buf : eListAt u P (2 ^ nm s) =
    eqKernel ((pt s).take k) ++ List.replicate (2 ^ nm s - 2 ^ k) 0

/-- At `0x8000ce24`, every pass done. -/
structure Exit (s u : MachineState) (C P nx : Word) : Prop extends Res s u C P nx where
  pc : u.pc = 0x8000ce24
  buf : eListAt u P (2 ^ nm s) = eqKernel (pt s)

theorem replicate_set {s : MachineState} {N : Nat} (h : 0 < N) :
    (List.replicate N (0 : E)).set 0 1 = eqKernel ((pt s).take 0) ++ List.replicate (N - 1) 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  simp [List.replicate_succ, eqKernel]

/-! ## The outer loop's head: `Scaler::new` and the inner loop's bounds -/

theorem eListAt_dw {u v : MachineState} {X : Word → Prop} (h : DwFrame u v X) {P : Word} {N : Nat}
    (hP : ∀ a, Within a P (24 * N) → ¬ X a) (hb : P.toNat + 24 * N ≤ 2 ^ 64) :
    eListAt v P N = eListAt u P N := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i hi _
  rw [eListAt_length] at hi
  rw [eListAt_getElem, eListAt_getElem]
  unfold eAt
  rw [DwFrame.keep h fun j hj ↦ hP _ (by addr_omega [hi, hj, hb]),
    DwFrame.keep h (a := P + BitVec.ofNat 64 (24 * i) + 8) fun j hj ↦
      hP _ (by addr_omega [hi, hj, hb]),
    DwFrame.keep h (a := P + BitVec.ofNat 64 (24 * i) + 16) fun j hj ↦
      hP _ (by addr_omega [hi, hj, hb])]

theorem tab_dw {u v : MachineState} {X : Word → Prop} (h : DwFrame u v X) {T : Word}
    (hT : ∀ a, Within a T tabBytes → ¬ X a) (hb : T.toNat + tabBytes ≤ 2 ^ 64) :
    tab v T = tab u T := by
  rw [ScalerNew.tab_eq_map, ScalerNew.tab_eq_map, eListAt_dw h (N := 2112) hT hb]

theorem ofNat_mul_pow {c k : Nat} (hc : 0 < c) (h : c * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 c * BitVec.ofNat 64 (2 ^ k) = BitVec.ofNat 64 (c * 2 ^ k) := by
  have h1 : c < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right c (Nat.two_pow_pos k)) h
  have h2 : 2 ^ k < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hc) h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h]

theorem and63 {k : Nat} (hk : k < 64) : (BitVec.ofNat 64 k &&& 63).toNat % 64 = k := by
  rw [BitVec.toNat_and, show (63 : Word).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  omega

theorem mod64 {k : Nat} (hk : k < 64) : (BitVec.ofNat 64 k).toNat % 64 = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  omega

theorem div24 {m : Nat} (h : 24 * m < 2 ^ 64) :
    rv64_mulhu (BitVec.ofNat 64 (24 * m)) 0xaaaaaaaaaaaaaaab >>> 4 = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Runtime.toNat_mulhu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := m) (by omega), Nat.shiftRight_eq_div_pow]
  simp only [Sym.wordToNatLit]
  omega

/-- The `Scaler` for `r` at `S - 136`, as the inner loop reads it: the tag in `s6`, the table `T`
in `s3`, its length in `s7`. -/
structure Sc (s u : MachineState) (C P T nx : Word) (r : E) : Prop where
  x19 : u.getReg .x19 = T
  plain : u.getReg .x22 ≠ 0 → eAt u (s.getReg .x2 - 128) = r
  table : u.getReg .x22 = 0 → u.getReg .x23 = 2112 ∧ BufP T ∧ P.toNat + 24 * C.toNat ≤ T.toNat ∧
    T.toNat + tabBytes ≤ nx.toNat ∧ tab u T = Model.scaledTable (Model.limbs r)

/-- At `0x8000cd04`, pass `k` at `j`. -/
structure IInv (s u : MachineState) (C P T nx : Word) (k j : Nat) : Prop
    extends Mid s u C P nx where
  pc : u.pc = 0x8000cd04
  lt : k < nm s
  jlt : j < 2 ^ k
  m168 : u.getMem (s.getReg .x2 - 168) = s.getReg .x11 + BitVec.ofNat 64 (24 * k)
  m176 : u.getMem (s.getReg .x2 - 176) = BitVec.ofNat 64 k
  x9 : u.getReg .x9 = BitVec.ofNat 64 (2 ^ k)
  x20 : u.getReg .x20 = P + BitVec.ofNat 64 (24 * 2 ^ k)
  x25 : u.getReg .x25 = BitVec.ofNat 64 j
  sc : Sc s u C P T nx ((pt s).getD k 0)
  buf : eListAt u P (2 ^ nm s) = (List.range j).foldl
    (Model.eqKernelStep ((pt s).getD k 0) (2 ^ k))
    (eqKernel ((pt s).take k) ++ List.replicate (2 ^ nm s - 2 ^ k) 0)

/-- At `0x8000cbf8`, pass `k` done. -/
structure Done (s u : MachineState) (C P nx : Word) (k : Nat) : Prop extends Mid s u C P nx where
  pc : u.pc = 0x8000cbf8
  lt : k < nm s
  m168 : u.getMem (s.getReg .x2 - 168) = s.getReg .x11 + BitVec.ofNat 64 (24 * k)
  m176 : u.getMem (s.getReg .x2 - 176) = BitVec.ofNat 64 k
  buf : eListAt u P (2 ^ nm s) =
    eqKernel ((pt s).take (k + 1)) ++ List.replicate (2 ^ nm s - 2 ^ (k + 1)) 0

/-- The sizes: `24 · 2^n` bytes fit in the heap, so `n < 27`. -/
theorem Res.small {s u : MachineState} {C P nx : Word} (h : Res s u C P nx) :
    P.toNat + 24 * 2 ^ nm s ≤ heapEnd ∧ nm s < 27 := by
  have h1 := h.top
  have h2 := h.room
  have h3 := h.inv.fits
  have hP : P.toNat + 24 * 2 ^ nm s ≤ heapEnd := by omega
  refine ⟨hP, Nat.lt_of_not_le fun h27 ↦ ?_⟩
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h27
  simp only [heapEnd] at hP
  norm_num at this
  omega

end Rv64Verifier.Proofs.Multilinear.EqKernel
