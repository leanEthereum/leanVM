import Rv64Verifier.Proofs.Layout.Contracts
import Rv64Verifier.Proofs.Layout.Grow
import Rv64Verifier.Proofs.Layout.ReprVec
import Rv64Verifier.Blocks.F86

/-!
# `Form::add_scaled`, at `0x800119cc`

```rust
pub fn add_scaled(&mut self, other: &Form, weight: E) {
    for &(monomial, coefficient) in &other.terms {
        match self.terms.iter_mut().find(|(m, _)| *m == monomial) {
            Some((_, c)) => *c += weight * coefficient,
            None => self.terms.push((monomial, weight * coefficient)),
        }
    }
}
```

compiled (`Blocks/F86.lean`), with `sp'` the entry's `sp - 144`: `0x800119cc` saves twelve
registers and the weight's address (`sp' + 8`), and returns at once for an empty `other`;
`0x80011a0c` keeps `other`'s end at `sp'`. The outer loop head `0x80011a78` loads the next term of
`other` (monomial in `s7`..`s9`) and the length; the search (`0x80011a9c` .. `0x80011ae0`) walks
`self`'s terms with `s6`, comparing tags, then `X`'s index or `Xy`'s two. A match (`0x80011b14`)
multiplies into `sp' + 16` and adds it into the matched coefficient (`0x80011b24`); none
(`0x80011aec`) multiplies, grows a full buffer (`0x80011b04`, `grow_one`) and pushes the term
(`0x80011a38`). `0x80011b5c` restores and returns.
-/

namespace Rv64Verifier.Layout.AddScaled
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F86 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

@[rv_addr] def n (s : MachineState) : Nat := (s.getReg .x12).toNat

/-- `other`'s terms. -/
def other (s : MachineState) : List Term := termsOf s (s.getReg .x11) (n s)

/-- `self` after the first `k` terms of `other`. -/
def res (s : MachineState) (k : Nat) : FormRust :=
  ⟨((other s).take k).foldl (fun acc t ↦ addTermRust acc t.1 (eAt s (s.getReg .x13) * t.2))
    (formOf s (s.getReg .x10)).terms⟩

theorem res_zero (s : MachineState) : res s 0 = formOf s (s.getReg .x10) := by simp [res]

theorem res_succ {s : MachineState} {k : Nat} (hk : k < n s) :
    res s (k + 1) = ⟨addTermRust (res s k).terms
      (monoOf s (s.getReg .x11 + BitVec.ofNat 64 (48 * k)))
      (eAt s (s.getReg .x13) * eAt s (s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24))⟩ := by
  have hl : k < (other s).length := by rw [other, termsOf_length]; exact hk
  unfold res
  rw [List.take_succ_eq_append_getElem hl, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, other, termsOf_getElem, termOf]

theorem res_n (s : MachineState) :
    res s (n s) = (formOf s (s.getReg .x10)).addScaled ⟨other s⟩ (eAt s (s.getReg .x13)) := by
  rw [res, List.take_of_length_le (by rw [other, termsOf_length])]
  rfl

/-- A term read through doublewords that agree. -/
theorem termOf_congr {s t : MachineState} {a b : Word}
    (h : ∀ c < 6, t.getMem (a + BitVec.ofNat 64 (8 * c)) = s.getMem (b + BitVec.ofNat 64 (8 * c))) :
    termOf t a = termOf s b ∧ (MonoOk s b → MonoOk t a) := by
  have h0 : t.getMem a = s.getMem b := by simpa using h 0 (by decide)
  have h8 := h 1 (by decide)
  have h16 := h 2 (by decide)
  have h24 := h 3 (by decide)
  have h32 := h 4 (by decide)
  have h40 := h 5 (by decide)
  refine ⟨?_, fun hm ↦ by simp only [MonoOk, h0]; exact hm⟩
  simp only [termOf, monoOf_congr h0 h8 h16, Prod.mk.injEq, true_and]
  refine eAt_congr h24 ?_ ?_
  · rw [BitVec.add_assoc, BitVec.add_assoc]; exact h32
  · rw [BitVec.add_assoc, BitVec.add_assoc]; exact h40

/-- Equal tags in `{0, 1, 2}` and the fields the tag uses: equal monomials; the machine's test. -/
theorem monoOf_eq_iff {s t : MachineState} {a b : Word} (ha : MonoOk s a) (hb : MonoOk t b) :
    monoOf s a = monoOf t b ↔ s.getMem a = t.getMem b ∧
      (s.getMem a = 1 → s.getMem (a + 8) = t.getMem (b + 8)) ∧
      (s.getMem a = 2 → s.getMem (a + 8) = t.getMem (b + 8) ∧
        s.getMem (a + 16) = t.getMem (b + 16)) := by
  simp only [MonoOk] at ha hb
  have h2 : ∀ x : Word, x.toNat ≤ 2 → x = 0 ∨ x = 1 ∨ x = 2 := by
    intro x hx
    rcases (by omega : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2) with h | h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
    · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq h))
  rcases h2 _ ha with h | h | h <;> rcases h2 _ hb with h' | h' | h' <;>
    simp [monoOf, h, h', BitVec.toNat_inj]

/-- `i << 5 + i << 4`, the offset of term `i`. -/
theorem offset48 (i : Word) : i * 32 + i * 16 = BitVec.ofNat 64 (48 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (32 : Word).toNat = 32 from rfl, show (16 : Word).toNat = 16 from rfl]
  omega

/-- What the function may write: `self`'s header and buffer, the stack, `NEXT`, the new heap. -/
@[rv_addr] def W (s u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ formBuf s (s.getReg .x10) a ∨
    Within a (stackLo s addScaledStack) addScaledStack ∨ Within a nextAddr 8 ∨ Fresh s u a

/-- `sp` and the arguments as numbers. -/
theorem bounds {s : MachineState} (hpre : AddScaledPre s) :
    1200 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ 0x78000000 + 1168 ≤ (s.getReg .x2).toNat ∧
      32 ≤ (s.getReg .x10).toNat ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 ∧
      32 ≤ (s.getReg .x13).toNat ∧ (s.getReg .x13).toNat % 8 = 0 ∧
      (s.getReg .x13).toNat + 24 ≤ 0xc0000008 := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hs := ValidMemRange.bounds hpre.self (by decide)
  have hw := ValidMemRange.bounds hpre.weight (by decide)
  simp only [addScaledStack, mulStack, heapEnd, stackLo] at hsb hab
  rw [hsb.2.2.2] at hab
  omega

/-- `other`'s terms are no write's. -/
theorem notW_other {s u : MachineState} (hpre : AddScaledPre s) (hu : HeapOk u) :
    ∀ x, Within x (s.getReg .x11) (48 * n s) → ¬ W s u x := by
  intro x hx hw
  have hb := bounds hpre
  have hso := hpre.selfOther
  have hos := hpre.otherStack
  have hof := hpre.otherFree
  have hhi := hu.hi
  simp only [addScaledStack, mulStack, heapEnd, heapNext] at hos hof hhi
  rcases hw with h | h | h | h | h
  · simp only [n] at hx; addr_omega [hx, h, hso]
  · exact hpre.buf x h (Or.inr (Or.inl hx))
  · simp only [n] at hx; addr_omega [hx, h, hos, hb]
  · simp only [n] at hx; addr_omega [hx, h, hof]
  · simp only [n, Fresh, heapNext] at hx h; addr_omega [hx, h, hof, hhi]

/-- The weight is no write's. -/
theorem notW_weight {s u : MachineState} (hpre : AddScaledPre s) (hu : HeapOk u) :
    ∀ x, Within x (s.getReg .x13) 24 → ¬ W s u x := by
  intro x hx hw
  have hb := bounds hpre
  have hso := hpre.selfWeight
  have hos := hpre.weightStack
  have hof := hpre.weightFree
  have hhi := hu.hi
  simp only [addScaledStack, mulStack, heapEnd, heapNext] at hos hof hhi
  rcases hw with h | h | h | h | h
  · addr_omega [hx, h, hso]
  · exact hpre.buf x h (Or.inr (Or.inr hx))
  · addr_omega [hx, h, hos, hb]
  · addr_omega [hx, h, hof]
  · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hof, hhi]

/-- The top of the frame: the saved registers (at `sp - 104` up) and the weight's address
(`sp - 136`), as the prologue `u0` left them, and `other`'s end (`sp - 144`). -/
@[rv_addr] def Top (s : MachineState) (a : Word) : Prop :=
  a.toNat % 8 = 0 ∧ (Within a (s.getReg .x2 - 144) 8 ∨ Within a (s.getReg .x2 - 136) 8 ∨
    Within a (s.getReg .x2 - 104) 104)

/-- Between the prologue `u0` and `u`, after `k` terms. -/
structure State (s u0 u : MachineState) (k : Nat) : Prop where
  top : ∀ a, a.toNat % 8 = 0 → Within a (s.getReg .x2 - 136) 8 ∨
    Within a (s.getReg .x2 - 104) 104 → u.getMem a = u0.getMem a
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  value : formOf u (s.getReg .x10) = res s k
  ok : FormOk u (s.getReg .x10)
  buf : ∀ x, formBuf u (s.getReg .x10) x → formBuf s (s.getReg .x10) x ∨ Fresh s u x
  frame : DFrame s u (W s u)

/-- At the outer loop head, before term `k`. -/
structure Inv (s u0 u : MachineState) (k : Nat) : Prop extends State s u0 u k where
  pc : u.pc = 0x80011a78
  lt : k < n s
  sp : u.getReg .x2 = s.getReg .x2 - 144
  x9 : u.getReg .x9 = s.getReg .x10
  x18 : u.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (48 * k)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x10)
  x20 : u.getReg .x20 = 1
  x21 : u.getReg .x21 = 2
  endv : u.getMem (s.getReg .x2 - 144) = s.getReg .x11 + BitVec.ofNat 64 (48 * n s)

/-- At the epilogue, every term added. -/
structure Fin (s u0 u : MachineState) : Prop extends State s u0 u (n s) where
  pc : u.pc = 0x80011b5c
  sp : u.getReg .x2 = s.getReg .x2 - 144

/-- A step keeps the state when it writes only where it may and not the top of the frame. -/
theorem State.step {s u0 u v : MachineState} {k k' : Nat} (h : State s u0 u k)
    (hf : DFrame u v (W s v))
    (hkeep : ∀ a, a.toNat % 8 = 0 → Within a (s.getReg .x2 - 136) 8 ∨
      Within a (s.getReg .x2 - 104) 104 → v.getMem a = u.getMem a)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v)
    (hvalue : formOf v (s.getReg .x10) = res s k') (hok : FormOk v (s.getReg .x10))
    (hbuf : ∀ x, formBuf v (s.getReg .x10) x → formBuf u (s.getReg .x10) x ∨ Fresh u v x) :
    State s u0 v k' where
  top a h8 ha := (hkeep a h8 ha).trans (h.top a h8 ha)
  heap := hheap
  mono := Nat.le_trans h.mono hmono
  value := hvalue
  ok := hok
  buf x hx := by
    rcases hbuf x hx with h' | h'
    · rcases h.buf x h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨h''.1, Nat.lt_of_lt_of_le h''.2 hmono⟩
    · exact Or.inr ⟨Nat.le_trans h.mono h'.1, h'.2⟩
  frame := (h.frame.union hf).mono fun a ha ↦ by
    rcases ha with ha | ha
    · rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.1, Nat.lt_of_lt_of_le ha.2 hmono⟩)))
    · exact ha

/-- `self`'s buffer as numbers. -/
theorem bufB {u : MachineState} {a : Word} (hok : FormOk u a) (hu : HeapOk u) :
    (vecPtr u a).toNat % 8 = 0 ∧ (vecLen u a).toNat ≤ (vecCap u a).toNat ∧
      ((vecCap u a).toNat = 0 ∨ (0x20000000 ≤ (vecPtr u a).toNat ∧
        (vecPtr u a).toNat + 48 * (vecCap u a).toNat ≤ 0x78000000)) := by
  have hb := vecBuf_bounds hok.vec (by decide)
  have hl := hok.vec.len
  have hhi := hu.hi
  simp only [heapStart, heapEnd] at hb hhi
  refine ⟨hb.1, hl, ?_⟩
  rcases hb.2 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, by omega⟩

/-- The prologue: the epilogue for an empty `other`, else the loop head. -/
theorem setup {s : MachineState} (hpc : s.pc = 0x800119cc) (hpre : AddScaledPre s) :
    ∃ u0, b800119cc.Holds s u0 ∧ ∃ u, Reaches Image.code s u ∧ (Fin s u0 u ∨ Inv s u0 u 0) := by
  have hb := bounds hpre
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hnx := hpre.stack.next
  have hss := hpre.selfStack
  simp only [addScaledStack, mulStack] at hsb hnx hss
  obtain ⟨u0, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800119cc_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b800119cc_keeps h₁
  have hm₁ := b800119cc_frame h₁ (by addr_omega [hsb])
  have hd₁ : DFrame s u0 (W s u0) := hm₁.dframe.mono fun a ha ↦
    Or.inr (Or.inr (Or.inl (by simp only [addScaledStack, mulStack]; addr_omega [ha, hsb])))
  have hn₁ : u0.getMem nextAddr = s.getMem nextAddr := hm₁ _ (by addr_omega [hnx, hsb])
  have hnext₁ : heapNext u0 = heapNext s := by simp only [heapNext, hn₁]
  have hheap₁ : HeapOk u0 := ⟨hnext₁ ▸ hpre.heap.lo, hnext₁ ▸ hpre.heap.hi⟩
  have hbs := bufB hpre.ok hpre.heap
  have hnotw : ∀ x, (Within x (s.getReg .x10) 24 ∨ formBuf s (s.getReg .x10) x) →
      ¬ Within x (s.getReg .x2 - 136) 136 := by
    intro x hx hw
    rcases hx with hx | hx
    · addr_omega [hx, hw, hss, hsb]
    · simp only [formBuf] at hx
      rcases hbs.2.2 with h0 | h0
      · simp only [Within, h0] at hx; omega
      · addr_omega [hx, hw, h0, hb]
  have hf := formOf_frame hm₁.dframe hpre.ok (fun x hx ↦ hnotw x (Or.inl hx))
    (fun x hx ↦ hnotw x (Or.inr hx)) (by addr_omega [hb]) hpre.heap hnext₁.ge
  have hfb : formBuf u0 (s.getReg .x10) = formBuf s (s.getReg .x10) :=
    formBuf_frame hm₁.dframe (fun x hx ↦ hnotw x (Or.inl hx)) (by addr_omega [hb])
  have st₁ : State s u0 u0 0 := {
    top := fun _ _ _ ↦ rfl
    heap := hheap₁
    mono := hnext₁.ge
    value := by rw [hf.1, res_zero]
    ok := hf.2
    buf := fun x hx ↦ Or.inl (hfb ▸ hx)
    frame := hd₁ }
  refine ⟨u0, h₁, ?_⟩
  by_cases h0 : s.getReg .x12 = 0
  · refine ⟨u0, hr₁, Or.inl { st₁ with
      value := by rw [hf.1, show n s = 0 by simp [n, h0], res_zero]
      pc := b800119cc_pc_taken h₁ h0
      sp := b800119cc_x2 h₁ }⟩
  · obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80011a0c_spec (b800119cc_pc_not_taken h₁ h0) (by
      rv_eval [b800119cc_x2 h₁, k₁ .x10 (by decide)]
      and_intros <;> first
        | valid_access hpre.stack.valid [hsb]
        | valid_access hpre.self [hb])
    have k := b80011a0c_keeps h
    have hm := b80011a0c_frame h (by rw [b800119cc_x2 h₁]; addr_omega [hsb])
    rw [b800119cc_x2 h₁] at hm
    have hsame (a : Word) (ha : ¬ Within a (s.getReg .x2 - 144) 8) : u.getMem a = u0.getMem a :=
      hm a ha
    have hn : heapNext u = heapNext u0 := by
      simp only [heapNext]; rw [hsame _ (by addr_omega [hnx, hsb])]
    have hhd : ∀ x, (Within x (s.getReg .x10) 24 ∨ formBuf u0 (s.getReg .x10) x) →
        ¬ Within x (s.getReg .x2 - 144) 8 := by
      intro x hx hw
      rw [hfb] at hx
      rcases hx with hx | hx
      · addr_omega [hx, hw, hss, hsb]
      · simp only [formBuf] at hx
        rcases hbs.2.2 with h0 | h0
        · simp only [Within, h0] at hx; omega
        · addr_omega [hx, hw, h0, hb]
    have hf' := formOf_frame hm.dframe hf.2 (fun x hx ↦ hhd x (Or.inl hx))
      (fun x hx ↦ hhd x (Or.inr hx)) (by addr_omega [hb]) hheap₁ hn.ge
    have hfb' : formBuf u (s.getReg .x10) = formBuf u0 (s.getReg .x10) :=
      formBuf_frame hm.dframe (fun x hx ↦ hhd x (Or.inl hx)) (by addr_omega [hb])
    have x2 : u.getReg .x2 = s.getReg .x2 - 144 := (k .x2 (by decide)).trans (b800119cc_x2 h₁)
    refine ⟨u, hr₁.trans hr, Or.inr {
      toState := st₁.step (hm.dframe.mono fun a ha ↦ Or.inr (Or.inr (Or.inl (by
          simp only [addScaledStack, mulStack]; addr_omega [ha, hsb]))))
        (fun a _ ha ↦ hsame a (by rcases ha with ha | ha <;> addr_omega [ha, hsb]))
        ⟨hn ▸ hheap₁.lo, hn ▸ hheap₁.hi⟩ hn.ge (by rw [hf'.1, st₁.value]) hf'.2
        (fun x hx ↦ Or.inl (hfb' ▸ hx))
      pc := b80011a0c_pc h
      lt := by simp only [n]; rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h' | h'
               · exact absurd (BitVec.eq_of_toNat_eq h') h0
               · exact h'
      sp := x2
      x9 := by rw [b80011a0c_x9 h, k₁ .x10 (by decide)]
      x18 := by rw [b80011a0c_x18 h, k₁ .x11 (by decide)]; simp
      x19 := by
        rw [b80011a0c_x19 h, k₁ .x10 (by decide)]
        exact (hsame _ (by addr_omega [hb, hss, hsb])).symm
      x20 := b80011a0c_x20 h
      x21 := b80011a0c_x21 h
      endv := by
        have := b80011a0c_m_x2_0 h
        rw [b800119cc_x2 h₁, k₁ .x11 (by decide), k₁ .x12 (by decide), offset48] at this
        exact this }⟩

/-! ## Facts along the loop -/

theorem rodataWords_all : (rodataWords.all fun p ↦ decide (p.1.toNat % 8 = 0 ∧
    0xa0000000 ≤ p.1.toNat ∧ p.1.toNat + 8 ≤ 0xa0000f30)) = true := by
  decide +kernel

theorem rodataWords_aligned :
    ∀ p ∈ rodataWords, p.1.toNat % 8 = 0 ∧ 0xa0000000 ≤ p.1.toNat ∧ p.1.toNat + 8 ≤ 0xa0000f30 :=
  fun p hp ↦ of_decide_eq_true (List.all_eq_true.mp rodataWords_all p hp)

/-- `self`'s buffer lies in the heap, below the stack and `.rodata`. -/
theorem buf_heap {s u0 v : MachineState} {k : Nat} (h : State s u0 v k) {x : Word}
    (hx : formBuf v (s.getReg .x10) x) : 0x20000000 ≤ x.toNat ∧ x.toNat < 0x78000000 := by
  have hb := bufB h.ok h.heap
  simp only [formBuf, Within] at hx
  rcases hb.2.2 with h0 | h0 <;> omega

/-- `.rodata` stays: nothing written is in it, when `self`'s header is not. -/
theorem State.rodata {s u0 v : MachineState} {k : Nat} (hpre : AddScaledPre s)
    (hro : Apart (s.getReg .x10) 24 rodataBase rodataSize) (h : State s u0 v k) : RodataOk v := by
  intro p hp
  obtain ⟨h8, hlo, hhi⟩ := rodataWords_aligned p hp
  have hb := bounds hpre
  have hsr := hpre.stack.rodata
  have hbs := bufB hpre.ok hpre.heap
  have hhv := h.heap.hi
  simp only [addScaledStack, mulStack, heapNext, heapEnd] at hsr hhv
  rw [h.frame.getMem_of (fun x hx hw ↦ ?_) (by omega)]
  · exact hpre.rodata p hp
  rcases hw with hw | hw | hw | hw | hw
  · addr_omega [hx, hw, hro, hlo, hhi]
  · simp only [formBuf] at hw
    rcases hbs.2.2 with h0 | h0
    · simp only [Within, h0] at hw; omega
    · addr_omega [hx, hw, h0, hlo, hhi]
  · addr_omega [hx, hw, hsr, hlo, hhi]
  · addr_omega [hx, hw, hlo, hhi]
  · simp only [Fresh, heapNext] at hw; addr_omega [hx, hw, hhv, hlo, hhi]

/-- `other`'s words and the weight stay what they were at the entry. -/
theorem State.other {s u0 v : MachineState} {k : Nat} (hpre : AddScaledPre s) (h : State s u0 v k)
    {a : Word} (h1 : (s.getReg .x11).toNat ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ (s.getReg .x11).toNat + 48 * n s) : v.getMem a = s.getMem a :=
  h.frame.getMem_of (fun x hx ↦ notW_other hpre h.heap x (by addr_omega [hx, h1, h2]))
    (by have := (s.getReg .x11).isLt; have := ValidMemRange.bounds hpre.other (by
          simp only [n] at h2; omega); simp only [n] at h2 ⊢; omega)

theorem State.weight {s u0 v : MachineState} {k : Nat} (hpre : AddScaledPre s) (h : State s u0 v k) :
    eAt v (s.getReg .x13) = eAt s (s.getReg .x13) := by
  have hb := bounds hpre
  exact eAt_congr' (h.frame.getMem_of (fun x hx ↦ notW_weight hpre h.heap x (by addr_omega [hx, hb]))
      (by addr_omega [hb]))
    (h.frame.getMem_of (fun x hx ↦ notW_weight hpre h.heap x (by addr_omega [hx, hb]))
      (by addr_omega [hb]))
    (h.frame.getMem_of (fun x hx ↦ notW_weight hpre h.heap x (by addr_omega [hx, hb]))
      (by addr_omega [hb]))

/-- `mul` into `sp' + 16` keeps the state and the top of the frame. -/
theorem State.mul {s u0 v v' : MachineState} {k : Nat} (hpre : AddScaledPre s) (h : State s u0 v k)
    (hsp : v.getReg .x2 = s.getReg .x2 - 144) (hout : v.getReg .x10 = s.getReg .x2 - 128)
    (hpost : MulPost v v') :
    State s u0 v' k ∧ (∀ a, Top s a → v'.getMem a = v.getMem a) := by
  have hb := bounds hpre
  have hss := hpre.selfStack
  simp only [addScaledStack, mulStack] at hss
  have hsl : stackLo v mulStack = s.getReg .x2 - 1168 := by
    simp only [stackLo, hsp, mulStack]; rv_eval []
  have hf := dframe_of_two hpost.frame
  rw [hout, hsl] at hf
  have hW : ∀ x, Within x (s.getReg .x2 - 128) 24 ∨ Within x (s.getReg .x2 - 1168) 1024 →
      Within x (stackLo s addScaledStack) addScaledStack := by
    intro x hx
    simp only [addScaledStack, mulStack]
    rcases hx with hx | hx <;> addr_omega [hx, hb]
  have hnot : ∀ x, (Within x (s.getReg .x10) 24 ∨ formBuf v (s.getReg .x10) x) →
      ¬ (Within x (s.getReg .x2 - 128) 24 ∨ Within x (s.getReg .x2 - 1168) 1024) := by
    intro x hx hw
    have := hW x hw
    rcases hx with hx | hx
    · simp only [addScaledStack, mulStack] at this; addr_omega [hx, this, hss]
    · have := buf_heap h hx
      have h' := hW x hw
      simp only [addScaledStack, mulStack] at h'
      addr_omega [h', this, hb]
  have hnx := hpre.stack.next
  simp only [addScaledStack, mulStack] at hnx
  have hn' : v'.getMem nextAddr = v.getMem nextAddr :=
    hf.getMem_of (fun x hx hw ↦ by rcases hw with hw | hw <;> addr_omega [hx, hw, hb, hnx]) (by decide)
  have hn : heapNext v' = heapNext v := by simp only [heapNext, hn']
  have hfo := formOf_frame hf h.ok (fun x hx ↦ hnot x (Or.inl hx)) (fun x hx ↦ hnot x (Or.inr hx))
    (by addr_omega [hb]) h.heap hn.ge
  have hfb := formBuf_frame hf (fun x hx ↦ hnot x (Or.inl hx)) (by addr_omega [hb])
  refine ⟨h.step (hf.mono fun x hx ↦ Or.inr (Or.inr (Or.inl (hW x hx))))
    (fun a h8 ha ↦ hf.getMem_of (fun x hx hw ↦ by rcases ha with ha | ha <;> rcases hw with hw | hw <;>
      addr_omega [hx, hw, ha, hb, h8]) (by rcases ha with ha | ha <;> addr_omega [ha, hb]))
    ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩ hn.ge (by rw [hfo.1, h.value]) hfo.2
    (fun x hx ↦ Or.inl (hfb ▸ hx)), fun a ha ↦ hf.getMem_of (fun x hx hw ↦ by
      simp only [Top] at ha
      obtain ⟨h8, ha⟩ := ha
      rcases ha with ha | ha | ha <;> rcases hw with hw | hw <;> addr_omega [hx, hw, ha, hb, h8])
      (by simp only [Top] at ha; rcases ha.2 with ha | ha | ha <;> addr_omega [ha, hb])⟩

/-- A step that writes nothing keeps the state. -/
theorem State.same {s u0 u v : MachineState} {k : Nat} (hpre : AddScaledPre s) (h : State s u0 u k)
    (hm : ∀ x, v.getMem x = u.getMem x) : State s u0 v k := by
  have hb := bounds hpre
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have hfo := formOf_frame (DFrame.of_same hm fun _ ↦ False) h.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h)
    (by addr_omega [hb]) h.heap hn.ge
  have hfb := formBuf_frame (DFrame.of_same hm fun _ ↦ False) (fun _ _ h ↦ h) (e := s.getReg .x10)
    (by addr_omega [hb])
  exact h.step (DFrame.of_same hm _) (fun a _ _ ↦ hm a) ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩ hn.ge
    (by rw [hfo.1, h.value]) hfo.2 fun x hx ↦ Or.inl (hfb ▸ hx)

theorem termsOf_same {s t : MachineState} (hm : ∀ a, t.getMem a = s.getMem a) (p : Word) (L : Nat) :
    termsOf t p L = termsOf s p L := by
  simp only [termsOf, termOf, monoOf, eAt, hm]

theorem termsOf_succ (s : MachineState) (p : Word) (L : Nat) :
    termsOf s p (L + 1) = termsOf s p L ++ [termOf s (p + BitVec.ofNat 64 (48 * L))] := by
  simp [termsOf, List.range_succ]

/-- Term `j`'s coefficient gains `d`, nothing else of the terms changes. -/
theorem termsOf_modify {u v : MachineState} {P : Word} {L j : Nat} {d : E} (hj : j < L)
    (hPL : P.toNat + 48 * L ≤ 2 ^ 64)
    (hf : DFrame u v (Within · (P + BitVec.ofNat 64 (48 * j) + 24) 24))
    (hc : eAt v (P + BitVec.ofNat 64 (48 * j) + 24) =
      eAt u (P + BitVec.ofNat 64 (48 * j) + 24) + d) :
    termsOf v P L = (termsOf u P L).modify j (fun t ↦ (t.1, t.2 + d)) ∧
      ∀ i < L, MonoOk u (P + BitVec.ofNat 64 (48 * i)) → MonoOk v (P + BitVec.ofNat 64 (48 * i)) := by
  have word (i c : Nat) (hi : i < L) (hc : c + 8 ≤ 48) (hne : i ≠ j ∨ c + 8 ≤ 24) :
      v.getMem (P + BitVec.ofNat 64 (48 * i) + BitVec.ofNat 64 c) =
        u.getMem (P + BitVec.ofNat 64 (48 * i) + BitVec.ofNat 64 c) :=
    hf.getMem_of (fun x hx hw ↦ by
      rcases hne with hne | hne
      · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt <;> addr_omega [hx, hw, hi, hc, hlt, hPL, hj]
      · addr_omega [hx, hw, hi, hc, hne, hPL, hj]) (by addr_omega [hi, hc, hPL])
  refine ⟨List.ext_getElem (by simp [termsOf_length]) fun i h1 h2 ↦ ?_, fun i hi hm ↦ ?_⟩
  · rw [termsOf_length] at h1
    rw [List.getElem_modify, termsOf_getElem, termsOf_getElem]
    by_cases hij : j = i
    · subst hij
      simp only [ite_true, termOf, Prod.mk.injEq]
      refine ⟨monoOf_congr (by simpa using word j 0 h1 (by omega) (Or.inr (by omega)))
        (word j 8 h1 (by omega) (Or.inr (by omega))) (word j 16 h1 (by omega) (Or.inr (by omega))), hc⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hij)]
      exact (termOf_congr fun c hc ↦ word i (8 * c) h1 (by omega) (Or.inl (Ne.symm hij))).1
  · simp only [MonoOk]
    rw [show v.getMem (P + BitVec.ofNat 64 (48 * i)) = u.getMem (P + BitVec.ofNat 64 (48 * i)) by
      simpa using word i 0 hi (by omega) (by by_cases h : i = j <;> omega)]
    exact hm

/-! ## The search -/

/-- The registers the search keeps. -/
def sregs : List Reg := [.x2, .x8, .x9, .x12, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27]

/-- In the search at `0x80011ac8`, before `self`'s term `j`, none before matching `m`. -/
structure SInv (u u₁ w : MachineState) (a : Word) (m : Monomial) (j : Nat) : Prop where
  pc : w.pc = 0x80011ac8
  lt : j < (vecLen u a).toNat
  x22 : w.getReg .x22 = vecPtr u a + BitVec.ofNat 64 (48 * j)
  x10 : w.getReg .x10 = BitVec.ofNat 64 (48 * ((vecLen u a).toNat - j))
  regs : ∀ r ∈ sregs, w.getReg r = u₁.getReg r
  mem : ∀ x, w.getMem x = u.getMem x
  miss : ∀ j' < j, monoOf u (vecPtr u a + BitVec.ofNat 64 (48 * j')) ≠ m

/-- The search is over: a match at `0x80011b14`, or none at `0x80011aec`. -/
def SDone (u u₁ w : MachineState) (a : Word) (m : Monomial) : Prop :=
  (∀ x, w.getMem x = u.getMem x) ∧ (∀ r ∈ sregs, w.getReg r = u₁.getReg r) ∧
    ((w.pc = 0x80011b14 ∧ ∃ j < (vecLen u a).toNat,
      w.getReg .x22 = vecPtr u a + BitVec.ofNat 64 (48 * j) ∧
      monoOf u (vecPtr u a + BitVec.ofNat 64 (48 * j)) = m ∧
      ∀ j' < j, monoOf u (vecPtr u a + BitVec.ofNat 64 (48 * j')) ≠ m) ∨
    (w.pc = 0x80011aec ∧ ∀ j' < (vecLen u a).toNat,
      monoOf u (vecPtr u a + BitVec.ofNat 64 (48 * j')) ≠ m))

/-- Past term `j`, which does not match: the next, or the end. -/
theorem advance {u u₁ b : MachineState} {a : Word} {m : Monomial} {j : Nat}
    (hP : (vecPtr u a).toNat + 48 * (vecLen u a).toNat ≤ 0x78000000) (hpc : b.pc = 0x80011abc) (hj : j < (vecLen u a).toNat)
    (x22 : b.getReg .x22 = vecPtr u a + BitVec.ofNat 64 (48 * j))
    (x10 : b.getReg .x10 = BitVec.ofNat 64 (48 * ((vecLen u a).toNat - j)))
    (regs : ∀ r ∈ sregs, b.getReg r = u₁.getReg r) (mem : ∀ x, b.getMem x = u.getMem x)
    (miss : ∀ j' < j + 1, monoOf u (vecPtr u a + BitVec.ofNat 64 (48 * j')) ≠ m) :
    ∃ w, Reaches Image.code b w ∧ (SDone u u₁ w a m ∨
      (SInv u u₁ w a m (j + 1) ∧ (w.getReg .x10).toNat < (b.getReg .x10).toNat)) := by
  have hL : (vecLen u a).toNat < 2 ^ 58 := by omega
  obtain ⟨w, hr, h⟩ := Sym.BlockSpec.reaches b80011abc_spec hpc trivial
  have k := b80011abc_keeps h
  have hm (x : Word) : w.getMem x = u.getMem x := (b80011abc_mem_same h x).trans (mem x)
  have hregs : ∀ r ∈ sregs, w.getReg r = u₁.getReg r := fun r hr' ↦
    (k r (mem_of_mem hr' _)).trans (regs r hr')
  by_cases hlast : j + 1 = (vecLen u a).toNat
  · refine ⟨w, hr, Or.inl ⟨hm, hregs, Or.inr ⟨b80011abc_pc_taken h (by rw [x10]; addr_omega [hlast, hL]),
      fun j' hj' ↦ miss j' (by omega)⟩⟩⟩
  · refine ⟨w, hr, Or.inr ⟨⟨b80011abc_pc_not_taken h (by rw [x10]; addr_omega [hlast, hL, hj]),
      by omega, by rw [b80011abc_x22 h, x22]; addr_omega [hj, hL, hP], ?_, hregs, hm, miss⟩, ?_⟩⟩
    · rw [b80011abc_x10 h, x10]; addr_omega [hj, hL, hlast]
    · rw [b80011abc_x10 h, x10]; addr_omega [hj, hL, hlast]

/-- One term of `self` compared with `other`'s, whose tag and fields are in `s7`..`s9`. -/
theorem sbody {u u₁ : MachineState} {a q : Word} {m : Monomial}
    (hP : (vecPtr u a).toNat + 48 * (vecLen u a).toNat ≤ 0x78000000)
    (hP0 : 0x20000000 ≤ (vecPtr u a).toNat) (hP8 : (vecPtr u a).toNat % 8 = 0)
    (htags : ∀ i < (vecLen u a).toNat, MonoOk u (vecPtr u a + BitVec.ofNat 64 (48 * i)))
    (hq : MonoOk u q) (hm : m = monoOf u q)
    (x20 : u₁.getReg .x20 = 1) (x21 : u₁.getReg .x21 = 2) (x23 : u₁.getReg .x23 = u.getMem q)
    (x24 : u₁.getReg .x24 = u.getMem (q + 8)) (x25 : u₁.getReg .x25 = u.getMem (q + 16))
    (w : MachineState) (hw : ∃ j, SInv u u₁ w a m j) :
    (∃ v, Reaches Image.code w v ∧ SDone u u₁ v a m) ∨
      (∃ v, Reaches Image.code w v ∧ (∃ j, SInv u u₁ v a m j) ∧
        (v.getReg .x10).toNat < (w.getReg .x10).toNat) := by
  obtain ⟨j, hj⟩ := hw
  have hlt := hj.lt
  obtain ⟨p, hp⟩ : ∃ p, p = vecPtr u a + BitVec.ofNat 64 (48 * j) := ⟨_, rfl⟩
  have hpn : p.toNat = (vecPtr u a).toNat + 48 * j := by rw [hp]; addr_omega [hP, hlt]
  have hPv : ValidMemRange (vecPtr u a) (6 * (vecLen u a).toNat) :=
    validMemRange_of hP8 (Or.inl ⟨by omega, by omega⟩)
  have hx22 : w.getReg .x22 = p := hj.x22.trans hp.symm
  have hr (r : Reg) (hr : r ∈ sregs) : w.getReg r = u₁.getReg r := hj.regs r hr
  have hmono := htags j hlt
  rw [← hp] at hmono
  have heq := monoOf_eq_iff hmono hq
  rw [← hm] at heq
  -- a mismatch: past it
  have past (b : MachineState) (hrb : Reaches Image.code w b) (hpc : b.pc = 0x80011abc)
      (hk : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), b.getReg r = w.getReg r)
      (hb : ∀ x, b.getMem x = w.getMem x) (hne : monoOf u p ≠ m) :
      (∃ v, Reaches Image.code w v ∧ SDone u u₁ v a m) ∨
        (∃ v, Reaches Image.code w v ∧ (∃ j, SInv u u₁ v a m j) ∧
          (v.getReg .x10).toNat < (w.getReg .x10).toNat) := by
    obtain ⟨v, hrv, hv | ⟨hv, hlt'⟩⟩ := advance hP hpc hlt
      (by rw [hk .x22 (by decide), hj.x22]) (by rw [hk .x10 (by decide), hj.x10])
      (fun r hr' ↦ (hk r (mem_of_mem hr' _)).trans (hj.regs r hr')) (fun x ↦ (hb x).trans (hj.mem x))
      (fun j' hj' ↦ by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h' | h'
        · exact hj.miss j' h'
        · rw [h', ← hp]; exact hne)
    · exact Or.inl ⟨v, hrb.trans hrv, hv⟩
    · exact Or.inr ⟨v, hrb.trans hrv, ⟨j + 1, hv⟩, by rwa [hk .x10 (by decide)] at hlt'⟩
  -- a match: found
  have found (b : MachineState) (hrb : Reaches Image.code w b) (hpc : b.pc = 0x80011b14)
      (hk : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), b.getReg r = w.getReg r)
      (hb : ∀ x, b.getMem x = w.getMem x) (heq' : monoOf u p = m) :
      (∃ v, Reaches Image.code w v ∧ SDone u u₁ v a m) :=
    ⟨b, hrb, fun x ↦ (hb x).trans (hj.mem x), fun r hr' ↦ (hk r (mem_of_mem hr' _)).trans (hj.regs r hr'),
      Or.inl ⟨hpc, j, hlt, by rw [hk .x22 (by decide), hj.x22], by rw [← hp]; exact heq', hj.miss⟩⟩
  have mw (x : Word) : w.getMem x = u.getMem x := hj.mem x
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011ac8_spec hj.pc (by
    rv_eval [hx22]; valid_access hPv [hpn, hP, hlt])
  have k₁ := b80011ac8_keeps h₁
  have k₁' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₁.getReg r = w.getReg r :=
    fun r hr' ↦ k₁ r (mem_of_mem hr' _)
  have tagw : w.getMem (w.getReg .x22) = u.getMem p := by rw [hx22, mw]
  have t23 : w.getReg .x23 = u.getMem q := (hr .x23 (by decide)).trans x23
  by_cases htag : u.getMem p = u.getMem q
  swap
  · exact past w₁ hr₁ (b80011ac8_pc_taken h₁ (by rw [tagw, t23]; exact htag)) k₁'
      (b80011ac8_mem_same h₁) fun h' ↦ htag (heq.mp h').1
  obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80011ad0_spec
    (b80011ac8_pc_not_taken h₁ (by rw [tagw, t23]; exact htag)) trivial
  have k₂ := b80011ad0_keeps h₂
  have k₂' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₂.getReg r = w.getReg r :=
    fun r hr' ↦ (k₂ r (mem_of_mem hr' _)).trans (k₁' r hr')
  have m₂ (x : Word) : w₂.getMem x = w.getMem x :=
    (b80011ad0_mem_same h₂ x).trans (b80011ac8_mem_same h₁ x)
  have g22 (b : MachineState) (hk : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), b.getReg r = w.getReg r) :
      b.getReg .x22 = p := (hk .x22 (by decide)).trans hx22
  have g (b : MachineState) (r : Reg) (hk : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), b.getReg r = w.getReg r)
      (hr' : r ∈ sregs := by decide) : b.getReg r = u₁.getReg r :=
    (hk r (mem_of_mem hr' _)).trans (hr r hr')
  by_cases h1 : u.getMem q = 1
  · obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011aa8_spec
      (b80011ad0_pc_taken h₂ (by rw [g w₁ .x23 k₁', g w₁ .x20 k₁', x23, x20, h1])) trivial
    have k₃ := b80011aa8_keeps h₃
    have k₃' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₃.getReg r = w.getReg r :=
      fun r hr' ↦ (k₃ r (mem_of_mem hr' _)).trans (k₂' r hr')
    have a13 : w₃.getReg .x22 + w₃.getReg .x13 = p + 8 := by rw [g22 w₃ k₃', b80011aa8_x13 h₃]
    obtain ⟨w₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011ab0_spec (b80011aa8_pc h₃) (by
      rv_eval [a13]; valid_access hPv [hpn, hP, hlt])
    have k₄ := b80011ab0_keeps h₄
    have k₄' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₄.getReg r = w.getReg r :=
      fun r hr' ↦ (k₄ r (mem_of_mem hr' _)).trans (k₃' r hr')
    have m₄ (x : Word) : w₄.getMem x = w.getMem x :=
      (b80011ab0_mem_same h₄ x).trans ((b80011aa8_mem_same h₃ x).trans (m₂ x))
    have v8 : w₃.getMem (w₃.getReg .x22 + w₃.getReg .x13) = u.getMem (p + 8) := by
      rw [a13, b80011aa8_mem_same h₃, m₂, mw]
    have v11 : w₃.getReg .x11 = u.getMem (q + 8) := by
      rw [b80011aa8_x11 h₃, g w₂ .x24 k₂', x24]
    by_cases e8 : u.getMem (p + 8) = u.getMem (q + 8)
    · exact Or.inl (found w₄ (hr₁.trans (hr₂.trans (hr₃.trans hr₄)))
        (b80011ab0_pc_taken h₄ (by rw [v8, v11]; exact e8)) k₄' m₄
        (heq.mpr ⟨htag, fun _ ↦ e8, fun h2 ↦ absurd (h2 ▸ htag ▸ h1 : (2 : Word) = 1) (by decide)⟩))
    · exact past w₄ (hr₁.trans (hr₂.trans (hr₃.trans hr₄)))
        (b80011ab0_pc_not_taken h₄ (by rw [v8, v11]; exact e8)) k₄' m₄
        fun h' ↦ e8 ((heq.mp h').2.1 (htag.trans h1))
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011ad4_spec
    (b80011ad0_pc_not_taken h₂ (by rw [g w₁ .x23 k₁', g w₁ .x20 k₁', x23, x20]; exact h1)) trivial
  have k₃ := b80011ad4_keeps h₃
  have k₃' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₃.getReg r = w.getReg r :=
    fun r hr' ↦ (k₃ r (mem_of_mem hr' _)).trans (k₂' r hr')
  have m₃ (x : Word) : w₃.getMem x = w.getMem x := (b80011ad4_mem_same h₃ x).trans (m₂ x)
  by_cases h2 : u.getMem q = 2
  swap
  · exact Or.inl (found w₃ (hr₁.trans (hr₂.trans hr₃))
      (b80011ad4_pc_taken h₃ (by rw [g w₂ .x23 k₂', g w₂ .x21 k₂', x23, x21]; exact h2)) k₃' m₃
      (heq.mpr ⟨htag, fun h' ↦ absurd (htag.symm.trans h') h1,
        fun h' ↦ absurd (htag.symm.trans h') h2⟩))
  obtain ⟨w₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011ad8_spec
    (b80011ad4_pc_not_taken h₃ (by rw [g w₂ .x23 k₂', g w₂ .x21 k₂', x23, x21]; exact h2)) (by
      rv_eval [g22 w₃ k₃']; valid_access hPv [hpn, hP, hlt])
  have k₄ := b80011ad8_keeps h₄
  have k₄' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₄.getReg r = w.getReg r :=
    fun r hr' ↦ (k₄ r (mem_of_mem hr' _)).trans (k₃' r hr')
  have m₄ (x : Word) : w₄.getMem x = w.getMem x := (b80011ad8_mem_same h₄ x).trans (m₃ x)
  have v8 : w₃.getMem (w₃.getReg .x22 + 8) = u.getMem (p + 8) := by rw [g22 w₃ k₃', m₃, mw]
  have v24 : w₃.getReg .x24 = u.getMem (q + 8) := by rw [g w₃ .x24 k₃', x24]
  by_cases e8 : u.getMem (p + 8) = u.getMem (q + 8)
  swap
  · exact past w₄ (hr₁.trans (hr₂.trans (hr₃.trans hr₄)))
      (b80011ad8_pc_taken h₄ (by rw [v8, v24]; exact e8)) k₄' m₄
      fun h' ↦ e8 ((heq.mp h').2.2 (htag.trans h2)).1
  obtain ⟨w₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80011ae0_spec
    (b80011ad8_pc_not_taken h₄ (by rw [v8, v24]; exact e8)) trivial
  have k₅ := b80011ae0_keeps h₅
  have k₅' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₅.getReg r = w.getReg r :=
    fun r hr' ↦ (k₅ r (mem_of_mem hr' _)).trans (k₄' r hr')
  have a13 : w₅.getReg .x22 + w₅.getReg .x13 = p + 16 := by rw [g22 w₅ k₅', b80011ae0_x13 h₅]
  obtain ⟨w₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80011ab0_spec (b80011ae0_pc h₅) (by
    rv_eval [a13]; valid_access hPv [hpn, hP, hlt])
  have k₆ := b80011ab0_keeps h₆
  have k₆' : ∀ r ∈ (.x10 :: .x22 :: sregs : List Reg), w₆.getReg r = w.getReg r :=
    fun r hr' ↦ (k₆ r (mem_of_mem hr' _)).trans (k₅' r hr')
  have m₆ (x : Word) : w₆.getMem x = w.getMem x :=
    (b80011ab0_mem_same h₆ x).trans ((b80011ae0_mem_same h₅ x).trans (m₄ x))
  have v16 : w₅.getMem (w₅.getReg .x22 + w₅.getReg .x13) = u.getMem (p + 16) := by
    rw [a13, b80011ae0_mem_same h₅, m₄, mw]
  have v11 : w₅.getReg .x11 = u.getMem (q + 16) := by rw [b80011ae0_x11 h₅, g w₄ .x25 k₄', x25]
  have hrr := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))
  by_cases e16 : u.getMem (p + 16) = u.getMem (q + 16)
  · exact Or.inl (found w₆ hrr (b80011ab0_pc_taken h₆ (by rw [v16, v11]; exact e16)) k₆' m₆
      (heq.mpr ⟨htag, fun h' ↦ absurd (htag.symm.trans h') h1, fun _ ↦ ⟨e8, e16⟩⟩))
  · exact past w₆ hrr (b80011ab0_pc_not_taken h₆ (by rw [v16, v11]; exact e16)) k₆' m₆
      fun h' ↦ e16 ((heq.mp h').2.2 (htag.trans h2)).2

/-- After the search for `other`'s term `k`, at `v` (memory `u`'s): what the two paths need. -/
structure At (s u0 u v : MachineState) (k : Nat) : Prop where
  inv : Inv s u0 u k
  mem : ∀ x, v.getMem x = u.getMem x
  sp : v.getReg .x2 = s.getReg .x2 - 144
  x9 : v.getReg .x9 = s.getReg .x10
  x12 : v.getReg .x12 = s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24
  x18 : v.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (48 * (k + 1))
  x8 : v.getReg .x8 = vecLen u (s.getReg .x10) * 32
  x27 : v.getReg .x27 = vecLen u (s.getReg .x10) * 16
  x26 : v.getReg .x26 = vecLen u (s.getReg .x10)
  x23 : v.getReg .x23 = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (48 * k))
  x24 : v.getReg .x24 = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 8)
  x25 : v.getReg .x25 = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 16)
  x19 : v.getReg .x19 = vecPtr u (s.getReg .x10)
  x20 : v.getReg .x20 = 1
  x21 : v.getReg .x21 = 2

/-- Two ranges with no common byte are apart. -/
theorem apart_of_bytes {a b : Word} {n m : Nat} (h : ∀ x, Within x a n → Within x b m → False) : Apart a n b m := by
  by_contra hc
  simp only [Apart, not_or] at hc
  by_cases hab : a.toNat ≤ b.toNat
  · exact h b ⟨hab, by omega⟩ ⟨Nat.le_refl _, by omega⟩
  · exact h a ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩

/-- `mul(sp' + 16, weight, coefficient)` from `v₁`, at its entry. -/
theorem mulCall (hMul : MulSpec) {s u0 v v₁ : MachineState} (hpre : AddScaledPre s)
    (hro : Apart (s.getReg .x10) 24 rodataBase rodataSize) {k : Nat} (hk : k < n s)
    (st₁ : State s u0 v₁ k) (hr₁ : Reaches Image.code v v₁) (hpc : v₁.pc = 0x80008c48)
    (x2₁ : v₁.getReg .x2 = s.getReg .x2 - 144) (x10₁ : v₁.getReg .x10 = s.getReg .x2 - 128)
    (x11₁ : v₁.getReg .x11 = s.getReg .x13)
    (x12₁ : v₁.getReg .x12 = s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24) :
    ∃ v₂, Reaches Image.code v v₂ ∧ ((v₂.pc = returnAddress v₁ ∧ Preserves v₁ v₂ ∧
      State s u0 v₂ k ∧ (∀ a, Top s a → v₂.getMem a = v₁.getMem a) ∧
      eAt v₂ (s.getReg .x2 - 128) =
        eAt s (s.getReg .x13) * eAt s (s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24) ∧
      ∀ x, (x.toNat + 8 ≤ (s.getReg .x2).toNat - 1168 ∨ (s.getReg .x2).toNat ≤ x.toNat) →
        v₂.getMem x = v₁.getMem x) ∨ Dead Image.code v₂) := by
  have hb := bounds hpre
  have hO := ValidMemRange.bounds hpre.other (by simp only [n] at hk; omega)
  have hws := hpre.weightStack
  have hos := hpre.otherStack
  have hsr := hpre.stack.rodata
  simp only [addScaledStack, mulStack] at hws hos hsr
  simp only [n] at hk hos
  obtain ⟨q, hq⟩ : ∃ q, q = s.getReg .x11 + BitVec.ofNat 64 (48 * k) := ⟨_, rfl⟩
  have hqn : q.toNat = (s.getReg .x11).toNat + 48 * k := by rw [hq]; addr_omega [hO, hk]
  rw [← hq] at x12₁ ⊢
  have hsl : stackLo v₁ mulStack = s.getReg .x2 - 1168 := by
    simp only [stackLo, x2₁, mulStack]; rv_eval []
  have hmul : MulPre v₁ := {
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hb]
    lhs := by rw [x11₁]; exact hpre.weight
    rhs := by rw [x12₁]; valid_sub hpre.other [hqn, hO, hk]
    stack := ⟨by rw [hsl]; valid_sub hpre.stack.valid [hb], by rw [x2₁]; addr_omega [hb]⟩
    outLhs := by rw [x10₁, x11₁]; addr_omega [hws, hb]
    outRhs := by rw [x10₁, x12₁]; addr_omega [hos, hb, hqn, hO, hk]
    outStack := by rw [x10₁, hsl]; addr_omega [hb]
    lhsStack := by rw [x11₁, hsl]; addr_omega [hws, hb]
    rhsStack := by rw [x12₁, hsl]; addr_omega [hos, hb, hqn, hO, hk]
    rodata := st₁.rodata hpre hro
    stackRodata := by rw [hsl]; addr_omega [hsr, hb] }
  obtain ⟨v₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hMul.call hr₁ hpc hmul
  swap
  · exact ⟨v₂, hr₂, Or.inr hdead⟩
  obtain ⟨st₂, top₂⟩ := st₁.mul hpre x2₁ x10₁ hpost₂
  refine ⟨v₂, hr₂, Or.inl ⟨hpc₂, hpres₂, st₂, top₂, ?_, fun x hx ↦ ?_⟩⟩
  · have hv := hpost₂.value
    rw [x10₁, x11₁, x12₁, st₁.weight hpre] at hv
    rw [hv, eAt_congr' (st₁.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk]))
      (st₁.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk]))
      (st₁.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk]))]
  · exact hpost₂.frame x (by rw [x10₁]; addr_omega [hx, hb])
      (by rw [hsl]; simp only [mulStack]; addr_omega [hx, hb])

/-- A match at term `j`: its coefficient gains the product. -/
theorem foundPath (hMul : MulSpec) {s u0 u v : MachineState} (hpre : AddScaledPre s)
    (hro : Apart (s.getReg .x10) 24 rodataBase rodataSize)
    (hw0 : u0.getMem (s.getReg .x2 - 136) = s.getReg .x13) {k j : Nat} (ha : At s u0 u v k)
    (hpc : v.pc = 0x80011b14) (hj : j < (vecLen u (s.getReg .x10)).toNat)
    (x22 : v.getReg .x22 = vecPtr u (s.getReg .x10) + BitVec.ofNat 64 (48 * j))
    (hfind : (res s k).terms.findIdx? (·.1 == monoOf s (s.getReg .x11 + BitVec.ofNat 64 (48 * k))) =
      some j) :
    ∃ w, Reaches Image.code v w ∧ (Inv s u0 w (k + 1) ∨ Fin s u0 w ∨ Dead Image.code w) := by
  have hb := bounds hpre
  have hu := ha.inv
  have hk := hu.lt
  have hO := ValidMemRange.bounds hpre.other (by simp only [n] at hk; omega)
  have hws := hpre.weightStack
  have hos := hpre.otherStack
  have hsr := hpre.stack.rodata
  have hnx := hpre.stack.next
  simp only [addScaledStack, mulStack] at hws hos hsr hnx
  simp only [n] at hk hos
  obtain ⟨q, hq⟩ : ∃ q, q = s.getReg .x11 + BitVec.ofNat 64 (48 * k) := ⟨_, rfl⟩
  have hqn : q.toNat = (s.getReg .x11).toNat + 48 * k := by rw [hq]; addr_omega [hO, hk]
  have hbs := bufB hu.ok hu.heap
  obtain ⟨P, hP⟩ : ∃ P, P = vecPtr u (s.getReg .x10) := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = vecLen u (s.getReg .x10) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = vecCap u (s.getReg .x10) := ⟨_, rfl⟩
  rw [← hP, ← hLd, ← hCd] at hbs
  rw [← hLd] at hj
  rw [← hP] at x22
  have hPL : P.toNat + 48 * C.toNat ≤ 0x78000000 ∧ 0x20000000 ≤ P.toNat := by
    rcases hbs.2.2 with h' | h' <;> omega
  obtain ⟨p, hp⟩ : ∃ p, p = P + BitVec.ofNat 64 (48 * j) := ⟨_, rfl⟩
  have hpn : p.toNat = P.toNat + 48 * j := by rw [hp]; addr_omega [hPL, hj, hbs]
  have hbufv : ValidMemRange P (6 * C.toNat) := validMemRange_of hbs.1 (Or.inl ⟨by omega, by omega⟩)
  have st₀ : State s u0 v k := hu.toState.same hpre ha.mem
  -- `mul(sp' + 16, weight, coefficient)`
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011b14_spec hpc (by
    rv_eval [ha.sp]; valid_access hpre.stack.valid [hb])
  have k₁ := b80011b14_keeps h₁
  have st₁ := st₀.same hpre (b80011b14_mem_same h₁)
  have x2₁ : v₁.getReg .x2 = s.getReg .x2 - 144 := (k₁ .x2 (by decide)).trans ha.sp
  have x10₁ : v₁.getReg .x10 = s.getReg .x2 - 128 := by rw [b80011b14_x10 h₁, ha.sp]; rv_eval []
  have x11₁ : v₁.getReg .x11 = s.getReg .x13 := by
    rw [b80011b14_x11 h₁, ha.sp, show s.getReg .x2 - 144 + 8 = s.getReg .x2 - 136 by rv_eval [],
      ha.mem, hu.top _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hw0]
  have x12₁ : v₁.getReg .x12 = q + 24 := by rw [k₁ .x12 (by decide), ha.x12, ← hq]
  have hsl : stackLo v₁ mulStack = s.getReg .x2 - 1168 := by
    simp only [stackLo, x2₁, mulStack]; rv_eval []
  have hmul : MulPre v₁ := {
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hb]
    lhs := by rw [x11₁]; exact hpre.weight
    rhs := by rw [x12₁]; valid_sub hpre.other [hqn, hO, hk]
    stack := ⟨by rw [hsl]; valid_sub hpre.stack.valid [hb], by rw [x2₁]; addr_omega [hb]⟩
    outLhs := by rw [x10₁, x11₁]; addr_omega [hws, hb]
    outRhs := by rw [x10₁, x12₁]; addr_omega [hos, hb, hqn, hO, hk]
    outStack := by rw [x10₁, hsl]; addr_omega [hb]
    lhsStack := by rw [x11₁, hsl]; addr_omega [hws, hb]
    rhsStack := by rw [x12₁, hsl]; addr_omega [hos, hb, hqn, hO, hk]
    rodata := st₁.rodata hpre hro
    stackRodata := by rw [hsl]; addr_omega [hsr, hb] }
  obtain ⟨v₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hMul.call hr₁ (b80011b14_pc h₁) hmul
  swap
  · exact ⟨v₂, hr₂, Or.inr (Or.inr hdead)⟩
  obtain ⟨st₂, top₂⟩ := st₁.mul hpre x2₁ x10₁ hpost₂
  have hprod : eAt v₂ (s.getReg .x2 - 128) =
      eAt s (s.getReg .x13) * eAt s (q + 24) := by
    have hv := hpost₂.value
    rw [x10₁, x11₁, x12₁, st₁.weight hpre] at hv
    rw [hv, eAt_congr' (st₁.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk]))
      (st₁.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk]))
      (st₁.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk]))]
  -- memory away from the window and the stack: `u`'s
  have hm₂ (x : Word) (hx : x.toNat + 8 ≤ (s.getReg .x2).toNat - 1168 ∨ (s.getReg .x2).toNat ≤ x.toNat) :
      v₂.getMem x = u.getMem x := by
    rw [hpost₂.frame x (by rw [x10₁]; addr_omega [hx, hb]) (by rw [hsl]; simp only [mulStack]; addr_omega [hx, hb]),
      b80011b14_mem_same h₁, ha.mem]
  have hhd (c : Word) (hc : c.toNat ≤ 16) : v₂.getMem (s.getReg .x10 + c) = u.getMem (s.getReg .x10 + c) := by
    have hss := hpre.selfStack
    simp only [addScaledStack, mulStack] at hss
    exact hm₂ _ (by addr_omega [hss, hb, hc])
  have hP₂ : vecPtr v₂ (s.getReg .x10) = P := by rw [hP]; exact hhd 8 (by decide)
  have hL₂ : vecLen v₂ (s.getReg .x10) = L := by rw [hLd]; exact hhd 16 (by decide)
  have hC₂ : vecCap v₂ (s.getReg .x10) = C := by rw [hCd]; simpa [vecCap] using hhd 0 (by decide)
  -- the coefficient gains the product
  have x22₂ : v₂.getReg .x22 = p := by rw [hpres₂.reg .x22, k₁ .x22 (by decide), x22, hp]
  have x2₂ : v₂.getReg .x2 = s.getReg .x2 - 144 := (hpres₂.reg .x2).trans x2₁
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011b24_spec
    (by rw [hpc₂, returnAddress_eq, b80011b14_x1 h₁]; decide) (by
      rv_eval [x22₂, x2₂]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | valid_access hbufv [hpn, hPL, hj, hbs]
        | addr_omega [hb, hpn, hPL, hj, hbs])
  have hm₃ := b80011b24_frame h₃ (by rw [x22₂]; addr_omega [hpn, hPL, hj, hbs])
  rw [x22₂] at hm₃
  have hc₃ : eAt v₃ (p + 24) = eAt v₂ (p + 24) + eAt v₂ (s.getReg .x2 - 128) := by
    have w24 := b80011b24_m_x22_24 h₃
    have w32 := b80011b24_m_x22_32 h₃
    have w40 := b80011b24_m_x22_40 h₃
    rw [x22₂, x2₂] at w24 w32 w40
    rv_eval [] at w24 w32 w40
    apply eAt_eq_of_limbs
    rw [limbs_add, limbs_eAt, limbs_eAt, show p + 24 + 8 = p + 32 by rv_eval [],
      show p + 24 + 16 = p + 40 by rv_eval [], show s.getReg .x2 - 128 + 8 = s.getReg .x2 - 120 by rv_eval [],
      show s.getReg .x2 - 128 + 16 = s.getReg .x2 - 112 by rv_eval [], w24, w32, w40]
    simp only [BitVec.xor_comm]
  -- the terms, the state, and the loop test
  have hLC : L.toNat ≤ C.toNat := hbs.2.1
  obtain ⟨hts, htags⟩ := termsOf_modify (u := v₂) (v := v₃) (P := P) (L := L.toNat) (j := j)
    (d := eAt v₂ (s.getReg .x2 - 128)) hj (by omega) (by rw [← hp]; exact hm₃.dframe)
    (by rw [← hp]; exact hc₃)
  have hsb : ∀ x, Within x (s.getReg .x10) 24 → ¬ formBuf u (s.getReg .x10) x := by
    intro x hx hbx
    have hhi := hu.heap.hi
    have hsf := hpre.selfFree
    simp only [heapEnd, heapNext, Outside] at hhi hsf
    rcases hu.buf x hbx with h' | h'
    · exact hpre.buf x h' (Or.inl hx)
    · simp only [Fresh, heapNext] at h'; addr_omega [hx, h', hhi, hsf]
  have inbuf (x : Word) (hx : Within x (p + 24) 24) : formBuf u (s.getReg .x10) x := by
    simp only [formBuf, ← hP, ← hCd]; addr_omega [hx, hpn, hPL, hj, hLC]
  have hh3 (c : Word) (hc : c.toNat ≤ 16) :
      v₃.getMem (s.getReg .x10 + c) = v₂.getMem (s.getReg .x10 + c) :=
    hm₃ _ fun h' ↦ hsb _ (by addr_omega [hb, hc]) (inbuf _ h')
  have hP₃ : vecPtr v₃ (s.getReg .x10) = P := by rw [← hP₂]; exact hh3 8 (by decide)
  have hL₃ : vecLen v₃ (s.getReg .x10) = L := by rw [← hL₂]; exact hh3 16 (by decide)
  have hC₃ : vecCap v₃ (s.getReg .x10) = C := by rw [← hC₂]; simpa [vecCap] using hh3 0 (by decide)
  have hn₃' : v₃.getMem nextAddr = v₂.getMem nextAddr :=
    hm₃ _ (by addr_omega [hpn, hPL, hj, hbs])
  have hn₃ : heapNext v₃ = heapNext v₂ := by simp only [heapNext, hn₃']
  have hres₂ : (res s k).terms = termsOf v₂ P L.toNat := by
    rw [← st₂.value]; simp only [formOf, hP₂, hL₂]
  have hres : res s (k + 1) = ⟨(termsOf v₂ P L.toNat).modify j
      (fun t ↦ (t.1, t.2 + eAt v₂ (s.getReg .x2 - 128)))⟩ := by
    rw [res_succ (by simp only [n]; exact hk), addTermRust, hfind, ← hres₂, hprod, hq]
  have hbuf₃ : formBuf v₃ (s.getReg .x10) = formBuf v₂ (s.getReg .x10) := by
    funext x; simp only [formBuf, hP₃, hC₃, hP₂, hC₂]
  have hfb₂ : formBuf v₂ (s.getReg .x10) = formBuf u (s.getReg .x10) := by
    funext x; simp only [formBuf, hP₂, hC₂, hP, hCd]
  have st₃ : State s u0 v₃ (k + 1) := st₂.step
    (hm₃.dframe.mono fun x hx ↦ by
      rcases st₂.buf x (hfb₂ ▸ inbuf x hx) with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hn₃] using h')))))
    (fun a h8 ha' ↦ hm₃ a fun h' ↦ by rcases ha' with ha' | ha' <;> addr_omega [ha', h', hb, hpn, hPL, hj, hbs])
    ⟨hn₃ ▸ st₂.heap.lo, hn₃ ▸ st₂.heap.hi⟩ hn₃.ge
    (by rw [hres, formOf, hP₃, hL₃, hts])
    ⟨⟨by
        have h' := st₂.ok.vec.raw
        simp only [RawVecOk, Buf, hP₂, hC₂] at h'
        simp only [RawVecOk, Buf, hP₃, hC₃, hn₃]; exact h',
      by rw [hC₃, hL₃]; exact hLC⟩, fun i hi ↦ by
        rw [hL₃] at hi; rw [hP₃]
        exact htags i hi (by have := st₂.ok.tags i (by rw [hL₂]; exact hi); rwa [hP₂] at this)⟩
    (fun x hx ↦ Or.inl (hbuf₃ ▸ hx))
  have k₃ := b80011b24_keeps h₃
  have x18₃ : v₃.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (48 * (k + 1)) := by
    rw [k₃ .x18 (by decide), hpres₂.reg .x18, k₁ .x18 (by decide), ha.x18]
  have hend : v₂.getMem (v₂.getReg .x2) = s.getReg .x11 + BitVec.ofNat 64 (48 * n s) := by
    rw [x2₂, top₂ _ (by simp only [Top]; exact ⟨by addr_omega [hb], Or.inl (by addr_omega [hb])⟩),
      b80011b14_mem_same h₁, ha.mem, hu.endv]
  have hrr := hr₂.trans hr₃
  simp only [n] at hend
  by_cases hlast : k + 1 = (s.getReg .x12).toNat
  · refine ⟨v₃, hrr, Or.inr (Or.inl { st₃ with
      value := by rw [st₃.value, n, hlast]
      pc := b80011b24_pc_not_taken h₃ (by rw [hend, hpres₂.reg .x18, k₁ .x18 (by decide), ha.x18, hlast])
      sp := by rw [k₃ .x2 (by decide), x2₂] })⟩
  · refine ⟨v₃, hrr, Or.inl { st₃ with
      pc := b80011b24_pc_taken h₃ (by
        rw [hend, hpres₂.reg .x18, k₁ .x18 (by decide), ha.x18]; addr_omega [hO, hk, hlast])
      lt := by simp only [n]; omega
      sp := by rw [k₃ .x2 (by decide), x2₂]
      x9 := by rw [k₃ .x9 (by decide), hpres₂.reg .x9, k₁ .x9 (by decide), ha.x9]
      x18 := x18₃
      x19 := by rw [k₃ .x19 (by decide), hpres₂.reg .x19, k₁ .x19 (by decide), ha.x19, ← hP, hP₃]
      x20 := by rw [k₃ .x20 (by decide), hpres₂.reg .x20, k₁ .x20 (by decide), ha.x20]
      x21 := by rw [k₃ .x21 (by decide), hpres₂.reg .x21, k₁ .x21 (by decide), ha.x21]
      endv := by
        rw [hm₃ _ (by addr_omega [hb, hpn, hPL, hj, hbs]), ← x2₂]
        rw [x2₂] at hend ⊢
        simp only [n]; exact hend }⟩


/-- Room for one more term at `0x80011a38`: the buffer `self` now has (grown if it was full),
starting with the terms it had. -/
structure Ready (s v₂ v₃ : MachineState) (P : Word) (L : Nat) : Prop where
  pc : v₃.pc = 0x80011a38
  regs : ∀ r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    v₃.getReg r = v₂.getReg r
  len : (vecLen v₃ (s.getReg .x10)).toNat = L
  room : L < (vecCap v₃ (s.getReg .x10)).toNat
  p8 : (vecPtr v₃ (s.getReg .x10)).toNat % 8 = 0
  pin : 0x20000000 ≤ (vecPtr v₃ (s.getReg .x10)).toNat ∧
    (vecPtr v₃ (s.getReg .x10)).toNat + 48 * (vecCap v₃ (s.getReg .x10)).toNat ≤ heapNext v₃
  terms : termsOf v₃ (vecPtr v₃ (s.getReg .x10)) L = termsOf v₂ P L
  tags : ∀ i < L, MonoOk v₃ (vecPtr v₃ (s.getReg .x10) + BitVec.ofNat 64 (48 * i))
  buf : ∀ x, formBuf v₃ (s.getReg .x10) x → formBuf v₂ (s.getReg .x10) x ∨ Fresh v₂ v₃ x
  frame : DFrame v₂ v₃ (W s v₃)
  keep : ∀ a, (Top s a ∨ Within a (s.getReg .x2 - 128) 24) → v₃.getMem a = v₂.getMem a
  heap : HeapOk v₃
  mono : heapNext v₂ ≤ heapNext v₃

/-- The capacity check, and `grow_one` when the buffer is full. -/
theorem room (hG : GrowOneFreshSpec 0x80010a94 48 8) {s u0 v₂ : MachineState} {k : Nat}
    (hpre : AddScaledPre s) (st : State s u0 v₂ k) (hpc : v₂.pc = 0x80011afc)
    (x2 : v₂.getReg .x2 = s.getReg .x2 - 144) (x9 : v₂.getReg .x9 = s.getReg .x10)
    (x26 : v₂.getReg .x26 = vecLen v₂ (s.getReg .x10)) :
    ∃ v₃, Reaches Image.code v₂ v₃ ∧ (Ready s v₂ v₃ (vecPtr v₂ (s.getReg .x10))
      (vecLen v₂ (s.getReg .x10)).toNat ∨ Dead Image.code v₃) := by
  have hb := bounds hpre
  have hbs := bufB st.ok st.heap
  have hlo := st.heap.lo
  simp only [heapStart, heapNext] at hlo
  obtain ⟨w, hrw, h⟩ := Sym.BlockSpec.reaches b80011afc_spec hpc (by
    rv_eval [x9]; valid_access hpre.self [hb])
  have k₁ := b80011afc_keeps h
  have hm₁ := b80011afc_mem_same h
  have hcap : v₂.getMem (v₂.getReg .x9) = vecCap v₂ (s.getReg .x10) := by rw [x9]; rfl
  by_cases hfull : vecLen v₂ (s.getReg .x10) = vecCap v₂ (s.getReg .x10)
  swap
  · -- room enough
    have hlt : (vecLen v₂ (s.getReg .x10)).toNat < (vecCap v₂ (s.getReg .x10)).toNat := by
      have := hbs.2.1
      rcases Nat.lt_or_eq_of_le this with h' | h'
      · exact h'
      · exact absurd (BitVec.eq_of_toNat_eq h') hfull
    have hfb : formBuf w (s.getReg .x10) = formBuf v₂ (s.getReg .x10) := by
      funext x; simp only [formBuf, vecPtr, vecCap, hm₁]
    refine ⟨w, hrw, Or.inl {
      pc := b80011afc_pc_taken h (by rw [x26, hcap]; exact hfull)
      regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
      len := by simp only [vecLen, hm₁]
      room := by simp only [vecLen, vecCap, hm₁] at hlt ⊢; exact hlt
      p8 := by simp only [vecPtr, hm₁]; exact hbs.1
      pin := by
        have hh := hbs.2.2
        simp only [vecPtr, vecCap, heapNext, hm₁] at hh ⊢
        rcases hh with h' | h'
        · simp only [vecLen, vecCap] at hlt; omega
        · have := st.ok.vec.raw
          simp only [RawVecOk, Buf, vecPtr, vecCap, heapNext] at this
          rcases this.2 with h'' | h''
          · simp only [vecLen, vecCap] at hlt; rw [Nat.mul_eq_zero] at h''; omega
          · constructor <;> omega
      terms := by rw [show vecPtr w (s.getReg .x10) = vecPtr v₂ (s.getReg .x10) by
          simp only [vecPtr, hm₁], termsOf_same hm₁]
      tags := fun i hi ↦ by
        have := st.ok.tags i hi
        simp only [MonoOk, vecPtr, hm₁] at this ⊢; exact this
      buf := fun x hx ↦ Or.inl (hfb ▸ hx)
      frame := DFrame.of_same hm₁ _
      keep := fun a _ ↦ hm₁ a
      heap := ⟨by simp only [heapNext, hm₁]; exact st.heap.lo, by simp only [heapNext, hm₁]; exact st.heap.hi⟩
      mono := by simp only [heapNext, hm₁]; exact Nat.le_refl _ }⟩
  -- full: grow
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hsf := hpre.selfFree
  simp only [addScaledStack, mulStack, Outside, heapNext, heapEnd] at hss hnx hsf
  obtain ⟨g, hrg, hg⟩ := Sym.BlockSpec.reaches b80011b04_spec
    (b80011afc_pc_not_taken h (by rw [x26, hcap]; exact hfull)) trivial
  have kg := b80011b04_keeps hg
  have hmg (x : Word) : g.getMem x = v₂.getMem x := (b80011b04_mem_same hg x).trans (hm₁ x)
  have hng : heapNext g = heapNext v₂ := by simp only [heapNext, hmg]
  have x2g : g.getReg .x2 = s.getReg .x2 - 144 := by rw [kg .x2 (by decide), k₁ .x2 (by decide), x2]
  have x10g : g.getReg .x10 = s.getReg .x10 := by rw [b80011b04_x10 hg, k₁ .x9 (by decide), x9]
  have hslg : stackLo g growOneStack = s.getReg .x2 - 304 := by
    simp only [stackLo, x2g, growOneStack]; rv_eval []
  have hmono : (s.getMem nextAddr).toNat ≤ (v₂.getMem nextAddr).toNat := st.mono
  have hgpre : GrowOnePre 48 8 g := {
    heap := ⟨hng ▸ st.heap.lo, hng ▸ st.heap.hi⟩
    self := by rw [x10g]; valid_sub hpre.self [hb]
    raw := by
      have := st.ok.vec.raw
      rw [x10g]; simp only [RawVecOk, Buf, vecPtr, vecCap, heapNext, hmg] at this ⊢; exact this
    stack := hpre.stack.inner (k := 144) x2g (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [x10g]; simp only [Outside, heapNext, heapEnd, hmg]
      exact ⟨by omega, by addr_omega [hsf]⟩
    selfStack := by rw [x10g, hslg]; addr_omega [hss, hb] }
  obtain ⟨g', hrg', ⟨hpcg, hpresg, hpost, hfresh⟩ | hdead⟩ := hG.call hrg (b80011b04_pc hg) hgpre
  swap
  · exact ⟨g', hrw.trans hrg', Or.inr hdead⟩
  rw [x10g] at hfresh
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011b10_spec
    (by rw [hpcg, returnAddress_eq, b80011b04_x1 hg]; decide) trivial
  have k₃ := b80011b10_keeps h₃
  have hm₃ (x : Word) : v₃.getMem x = g'.getMem x := b80011b10_mem_same h₃ x
  have hn₃ : heapNext v₃ = heapNext g' := by simp only [heapNext, hm₃]
  have hgf := hpost.frame.dframe
  rw [x10g, hslg] at hgf
  have hhi := hpost.heap.hi
  simp only [heapEnd, heapNext] at hhi
  -- what `grow_one` keeps: everything but `self`'s first 16 bytes, its stack, `NEXT` and new heap
  have gk (a : Word) (hw : a.toNat + 8 ≤ 2 ^ 64)
      (ha : ∀ x, Within x a 8 → ¬ Within x (s.getReg .x10) 16 ∧ ¬ Within x (s.getReg .x2 - 304) 160 ∧
        ¬ Within x nextAddr 8 ∧ (x.toNat < heapNext g ∨ 0x78000000 ≤ x.toNat)) :
      v₃.getMem a = v₂.getMem a := by
    rw [hm₃, hgf.getMem_of (fun x hx hw' ↦ by
      obtain ⟨h1, h2, h3, h4⟩ := ha x hx
      rcases hw' with h' | h' | h' | h'
      · exact h1 h'
      · exact h2 h'
      · exact h3 h'
      · simp only [Fresh, heapNext] at h' h4 hhi; omega) hw, hmg]
  have hC := hpost.cap
  rw [x10g] at hC
  simp only [vecCap, hmg] at hC
  have hraw := hpost.raw
  rw [x10g] at hraw
  simp only [RawVecOk, Buf] at hraw
  have hp8 := hraw.1
  have hpin : 0x20000000 ≤ (vecPtr g' (s.getReg .x10)).toNat ∧
      (vecPtr g' (s.getReg .x10)).toNat + 48 * (vecCap g' (s.getReg .x10)).toNat ≤ heapNext g' := by
    rcases hraw.2 with h' | h'
    · rw [Nat.mul_eq_zero] at h'; simp only [vecCap] at h' ⊢; omega
    · simp only [heapStart] at h'; omega
  have hlen : vecLen v₃ (s.getReg .x10) = vecLen v₂ (s.getReg .x10) := by
    simp only [vecLen]
    exact gk _ (by addr_omega [hb]) fun x hx ↦ ⟨by addr_omega [hx, hb], by addr_omega [hx, hb, hss],
      by addr_omega [hx, hb, hsf], by
        simp only [heapNext, hmg]
        rcases hsf.1 with h' | h'
        · left; addr_omega [hx, h', hmono]
        · right; addr_omega [hx, h', hb]⟩
  have hptr : vecPtr v₃ (s.getReg .x10) = vecPtr g' (s.getReg .x10) := by simp only [vecPtr, hm₃]
  have hcap₃ : vecCap v₃ (s.getReg .x10) = vecCap g' (s.getReg .x10) := by simp only [vecCap, hm₃]
  have hLC : (vecLen v₂ (s.getReg .x10)).toNat = (vecCap v₂ (s.getReg .x10)).toNat := by rw [hfull]
  have hbytes := hpost.bytes
  rw [x10g] at hbytes
  simp only [vecCap, vecPtr, hmg] at hbytes
  have hcopy (i : Nat) (hi : i < (vecLen v₂ (s.getReg .x10)).toNat) :=
    termOf_congr (s := v₂) (t := v₃) (a := vecPtr v₃ (s.getReg .x10) + BitVec.ofNat 64 (48 * i))
      (b := vecPtr v₂ (s.getReg .x10) + BitVec.ofNat 64 (48 * i)) fun c hc ↦ by
        rw [hptr, hm₃, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
        have hb' := getMem_eq_of_bytesAt (k := 48 * i + 8 * c) hbytes hp8 hbs.1 (by omega) (by
          simp only [vecLen, vecCap] at hLC hi; rw [← hLC]; omega)
        simp only [vecPtr] at hb' ⊢
        rw [hb', hmg]
  refine ⟨v₃, hrw.trans (hrg'.trans hr₃), Or.inl {
    pc := b80011b10_pc h₃
    regs := fun r hr ↦ by
      rw [k₃ r (mem_of_mem hr _), hpresg r (mem_of_mem hr calleeSaved), kg r (mem_of_mem hr _),
        k₁ r (mem_of_mem hr _)]
    len := by rw [hlen]
    room := by rw [hcap₃]; simp only [vecCap, vecLen] at hC hLC ⊢; omega
    p8 := by rw [hptr]; exact hp8
    pin := by rw [hptr, hcap₃, hn₃]; exact hpin
    terms := List.map_congr_left fun i hi ↦ (hcopy i (List.mem_range.mp hi)).1
    tags := fun i hi ↦ (hcopy i hi).2 (st.ok.tags i hi)
    buf := fun x hx ↦ Or.inr (by
      simp only [formBuf, hptr, hcap₃] at hx
      simp only [Fresh, hn₃, ← hng]
      simp only [heapNext] at hfresh hpin ⊢
      addr_omega [hx, hfresh, hpin])
    frame := ((DFrame.of_same hmg fun _ ↦ False).union (hgf.union (DFrame.of_same hm₃ fun _ ↦ False))).mono
      fun a ha ↦ by
        rcases ha with ha | (ha | ha | ha | ha) | ha
        · exact ha.elim
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inr (Or.inr (Or.inl (by simp only [addScaledStack, mulStack]; addr_omega [ha, hb])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          simp only [Fresh, hn₃] at ha ⊢
          simp only [heapNext, hmg] at ha ⊢
          omega
        · exact ha.elim
    keep := fun a ha ↦ by
      simp only [Top] at ha
      rcases ha with ⟨h8, ha⟩ | ha
      · exact gk a (by rcases ha with ha | ha | ha <;> addr_omega [ha, hb]) fun x hx ↦ by
          rcases ha with ha | ha | ha <;> exact ⟨by addr_omega [hx, ha, hss, hb, h8],
            by addr_omega [hx, ha, hb, h8], by addr_omega [hx, ha, hb, hnx, h8],
            Or.inr (by addr_omega [hx, ha, hb, h8])⟩
      · exact gk a (by addr_omega [ha, hb]) fun x hx ↦ ⟨by addr_omega [hx, ha, hss, hb],
          by addr_omega [hx, ha, hb], by addr_omega [hx, ha, hb, hnx], Or.inr (by addr_omega [hx, ha, hb])⟩
    heap := ⟨by rw [hn₃]; exact hpost.heap.lo, by rw [hn₃]; exact hpost.heap.hi⟩
    mono := by rw [hn₃, ← hng]; exact hpost.mono }⟩

/-- No match: the product is pushed, the buffer grown when full. -/
theorem pushPath (hMul : MulSpec) (hG : GrowOneFreshSpec 0x80010a94 48 8) {s u0 u v : MachineState}
    (hpre : AddScaledPre s) (hro : Apart (s.getReg .x10) 24 rodataBase rodataSize)
    (hw0 : u0.getMem (s.getReg .x2 - 136) = s.getReg .x13) {k : Nat}
    (ha : At s u0 u v k) (hpc : v.pc = 0x80011aec)
    (hfind : (res s k).terms.findIdx? (·.1 == monoOf s (s.getReg .x11 + BitVec.ofNat 64 (48 * k))) =
      none) :
    ∃ w, Reaches Image.code v w ∧ (Inv s u0 w (k + 1) ∨ Fin s u0 w ∨ Dead Image.code w) := by
  have hb := bounds hpre
  have hu := ha.inv
  have hk := hu.lt
  have hO := ValidMemRange.bounds hpre.other (by simp only [n] at hk; omega)
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hsf := hpre.selfFree
  simp only [addScaledStack, mulStack, Outside, heapNext, heapEnd] at hss hnx hsf
  have st₀ : State s u0 v k := hu.toState.same hpre ha.mem
  -- the product
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011aec_spec hpc (by
    rv_eval [ha.sp]; valid_access hpre.stack.valid [hb])
  have k₁ := b80011aec_keeps h₁
  have st₁ := st₀.same hpre (b80011aec_mem_same h₁)
  obtain ⟨v₂, hr₂, ⟨hpc₂, hpres₂, st₂, top₂, hprod, hm₂⟩ | hdead⟩ := mulCall hMul hpre hro hk st₁ hr₁
    (b80011aec_pc h₁) ((k₁ .x2 (by decide)).trans ha.sp)
    (by rw [b80011aec_x10 h₁, ha.sp]; rv_eval [])
    (by rw [b80011aec_x11 h₁, ha.sp, show s.getReg .x2 - 144 + 8 = s.getReg .x2 - 136 by rv_eval [],
      ha.mem, hu.top _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hw0])
    (by rw [k₁ .x12 (by decide), ha.x12])
  swap
  · exact ⟨v₂, hr₂, Or.inr (Or.inr hdead)⟩
  have hm₂u (x : Word) (hx : x.toNat + 8 ≤ (s.getReg .x2).toNat - 1168 ∨ (s.getReg .x2).toNat ≤ x.toNat) :
      v₂.getMem x = u.getMem x := by rw [hm₂ x hx, b80011aec_mem_same h₁, ha.mem]
  have hhd (c : Word) (hc : c.toNat ≤ 16) : v₂.getMem (s.getReg .x10 + c) = u.getMem (s.getReg .x10 + c) :=
    hm₂u _ (by addr_omega [hss, hb, hc])
  have hL₂ : vecLen v₂ (s.getReg .x10) = vecLen u (s.getReg .x10) := hhd 16 (by decide)
  have x2₂ : v₂.getReg .x2 = s.getReg .x2 - 144 := by rw [hpres₂.reg .x2, k₁ .x2 (by decide), ha.sp]
  have r₂ (r : Reg) (hr : r ∈ calleeSaved) (h' : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23,
      .x24, .x25, .x26, .x27] := by decide) : v₂.getReg r = v.getReg r := by
    rw [hpres₂ r hr, k₁ r (mem_of_mem h' _)]
  -- room for one more term
  obtain ⟨v₃, hr₃, hv₃ | hdead⟩ := room hG hpre st₂ (by rw [hpc₂, returnAddress_eq, b80011aec_x1 h₁]; decide)
    x2₂ (by rw [r₂ .x9 (by decide), ha.x9]) (by rw [r₂ .x26 (by decide), ha.x26, hL₂])
  swap
  · exact ⟨v₃, hr₂.trans hr₃, Or.inr (Or.inr hdead)⟩
  obtain ⟨P', hP'⟩ : ∃ P', P' = vecPtr v₃ (s.getReg .x10) := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = vecLen u (s.getReg .x10) := ⟨_, rfl⟩
  have hlen₃ := hv₃.len
  have hroom := hv₃.room
  have hpin := hv₃.pin
  have hp8 := hv₃.p8
  rw [← hP'] at hpin hp8
  rw [hL₂, ← hLd] at hlen₃ hroom
  have hhi₃ := hv₃.heap.hi
  simp only [heapEnd, heapNext] at hhi₃ hpin
  obtain ⟨slot, hslot⟩ : ∃ slot, slot = P' + BitVec.ofNat 64 (48 * L.toNat) := ⟨_, rfl⟩
  have hsn : slot.toNat = P'.toNat + 48 * L.toNat := by rw [hslot]; addr_omega [hpin, hroom, hhi₃]
  have hcap₃ : (vecCap v₃ (s.getReg .x10)).toNat * 48 = 48 * (vecCap v₃ (s.getReg .x10)).toNat := by ring
  have hslotv : ValidMemRange slot 6 := validMemRange_of (by omega) (Or.inl ⟨by omega, by omega⟩)
  -- the buffer misses `self`'s header
  have hbuf₃ (x : Word) (hx : formBuf v₃ (s.getReg .x10) x) :
      formBuf s (s.getReg .x10) x ∨ Fresh s v₃ x := by
    rcases hv₃.buf x hx with h' | h'
    · rcases st₂.buf x h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨h''.1, Nat.lt_of_lt_of_le h''.2 hv₃.mono⟩
    · exact Or.inr ⟨Nat.le_trans st₂.mono h'.1, h'.2⟩
  have hsb : ∀ x, Within x (s.getReg .x10) 24 → ¬ formBuf v₃ (s.getReg .x10) x := by
    intro x hx hbx
    rcases hbuf₃ x hbx with h' | h'
    · exact hpre.buf x h' (Or.inl hx)
    · simp only [Fresh, heapNext] at h'; addr_omega [hx, h', hhi₃, hsf]
  have inbuf (x : Word) (hx : Within x slot 48) : formBuf v₃ (s.getReg .x10) x := by
    simp only [formBuf, ← hP']; addr_omega [hx, hsn, hroom, hpin]
  have hsa : Apart (s.getReg .x10) 24 slot 48 := apart_of_bytes fun x h1 h2 ↦ hsb x h1 (inbuf x h2)
  -- the push
  have rx (r : Reg) (h' : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]
      := by decide) : v₃.getReg r = v.getReg r := (hv₃.regs r h').trans (r₂ r (mem_of_mem h' calleeSaved) h')
  have hx9 : v₃.getReg .x9 = s.getReg .x10 := (rx .x9).trans ha.x9
  have hx2 : v₃.getReg .x2 = s.getReg .x2 - 144 := (rx .x2).trans ha.sp
  have hsl : v₃.getMem (v₃.getReg .x9 + 8) + (v₃.getReg .x8 + v₃.getReg .x27) = slot := by
    rw [hx9, rx .x8, rx .x27, ha.x8, ha.x27, offset48, hslot, ← hLd, hP']; rfl
  have hsl' : v₃.getMem (s.getReg .x10 + 8) + (v₃.getReg .x8 + v₃.getReg .x27) = slot := by
    rw [← hx9]; exact hsl
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011a38_spec hv₃.pc (by
    rv_eval []
    simp only [hx9, hx2, hsl']
    rv_eval []
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.self [hb]
      | valid_access hslotv [hsn, hpin, hroom]
      | addr_omega [hb, hsn, hpin, hroom, hhi₃, hsa, hss])
  have hs8 : (s.getReg .x10).toNat % 8 = 0 := hb.2.2.2.2.2.1
  have hf₄ : DFrame v₃ v₄ fun x ↦ Within x slot 48 ∨ Within x (s.getReg .x10 + 16) 8 :=
    (h₄.byteFrame (by
      rv_eval [hsl, hsl', hx9]
      and_intros <;> first
        | (intro i hi; first
            | exact Or.inl (by addr_omega [hi, hsn, hpin, hroom, hhi₃])
            | exact Or.inr (by addr_omega [hi, hb]))
        | addr_omega [hsn, hp8, hpin, hroom, hhi₃, hb, hs8])).dframe
  have hw₄ (x : Word) (hw : x.toNat + 8 ≤ 2 ^ 64)
      (h1 : ∀ y, Within y x 8 → ¬ Within y slot 48) (h2 : ∀ y, Within y x 8 → ¬ Within y (s.getReg .x10 + 16) 8) :
      v₄.getMem x = v₃.getMem x :=
    hf₄.getMem_of (fun y hy hw' ↦ by rcases hw' with hw' | hw'; exact h1 y hy hw'; exact h2 y hy hw') hw
  have hP₄ : vecPtr v₄ (s.getReg .x10) = P' := by
    rw [hP']; exact hw₄ _ (by addr_omega [hb]) (fun y hy h' ↦ by addr_omega [hy, h', hsa, hb])
      (fun y hy h' ↦ by addr_omega [hy, h', hb])
  have hC₄ : vecCap v₄ (s.getReg .x10) = vecCap v₃ (s.getReg .x10) :=
    hw₄ _ (by addr_omega [hb]) (fun y hy h' ↦ by addr_omega [hy, h', hsa, hb])
      (fun y hy h' ↦ by addr_omega [hy, h', hb])
  have hlen₄ : vecLen v₄ (s.getReg .x10) = L + 1 := by
    have := b80011a38_m_x9_16 h₄
    rw [hx9, rx .x26, ha.x26, ← hLd] at this
    exact this
  have hlen₄n : (vecLen v₄ (s.getReg .x10)).toNat = L.toNat + 1 := by
    rw [hlen₄]; addr_omega [hroom, hpin, hhi₃]
  have hn₄' : v₄.getMem nextAddr = v₃.getMem nextAddr :=
    hw₄ _ (by decide) (fun y hy h' ↦ by addr_omega [hy, h', hsn, hpin, hroom, hhi₃])
      (fun y hy h' ↦ by addr_omega [hy, h', hb, hsf])
  have hn₄ : heapNext v₄ = heapNext v₃ := by simp only [heapNext, hn₄']
  -- the new term
  have m1 := b80011a38_m1 h₄
  have m2 := b80011a38_m2 h₄
  have m3 := b80011a38_m3 h₄
  have m4 := b80011a38_m4 h₄
  have m5 := b80011a38_m5 h₄
  have m6 := b80011a38_m6 h₄
  rw [hsl] at m1 m2 m3 m4 m5 m6
  rw [rx .x23, ha.x23] at m6
  rw [rx .x24, ha.x24] at m5
  rw [rx .x25, ha.x25] at m4
  rw [hx2] at m1 m2 m3
  rv_eval [] at m1 m2 m3
  have kp (a : Word) (h1 : (s.getReg .x2).toNat - 128 ≤ a.toNat) (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 104) :
      v₃.getMem a = v₂.getMem a := hv₃.keep a (Or.inr (by addr_omega [h1, h2, hb]))
  rw [kp _ (by addr_omega [hb]) (by addr_omega [hb])] at m1 m2 m3
  have hnew : termOf v₄ slot = (monoOf s (s.getReg .x11 + BitVec.ofNat 64 (48 * k)),
      eAt s (s.getReg .x13) * eAt s (s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24)) := by
    rw [termOf, monoOf_congr m6 m5 m4, ← hprod]
    simp only [Prod.mk.injEq, true_and]
    exact eAt_congr m3
      (by rw [show slot + 24 + 8 = slot + 32 by rv_eval [],
        show s.getReg .x2 - 128 + 8 = s.getReg .x2 - 120 by rv_eval []]; exact m2)
      (by rw [show slot + 24 + 16 = slot + 40 by rv_eval [],
        show s.getReg .x2 - 128 + 16 = s.getReg .x2 - 112 by rv_eval []]; exact m1)
  -- the old terms
  have hold (i : Nat) (hi : i < L.toNat) :=
    termOf_frame hf₄ (a := P' + BitVec.ofNat 64 (48 * i)) (fun y hy hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hy, hw, hsn, hi, hpin, hroom, hhi₃]
      · exact hsb y (by addr_omega [hw, hb]) (by simp only [formBuf, ← hP']; addr_omega [hy, hi, hroom, hpin, hhi₃]))
      (by addr_omega [hi, hroom, hpin, hhi₃])
  have hres₂ : (res s k).terms = termsOf v₂ (vecPtr v₂ (s.getReg .x10)) L.toNat := by
    rw [← st₂.value, formOf, hL₂, ← hLd]
  have hts : termsOf v₄ P' (L.toNat + 1) = (res s k).terms ++
      [(monoOf s (s.getReg .x11 + BitVec.ofNat 64 (48 * k)),
        eAt s (s.getReg .x13) * eAt s (s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24))] := by
    rw [termsOf_succ, ← hslot, hnew, hres₂]
    congr 1
    have ht3 := hv₃.terms
    rw [hL₂, ← hLd, ← hP'] at ht3
    rw [← ht3]
    exact List.map_congr_left fun i hi ↦ (hold i (List.mem_range.mp hi)).1
  have hres : res s (k + 1) = ⟨(res s k).terms ++
      [(monoOf s (s.getReg .x11 + BitVec.ofNat 64 (48 * k)),
        eAt s (s.getReg .x13) * eAt s (s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24))]⟩ := by
    rw [res_succ hk, addTermRust, hfind]
  have hfb₄ : formBuf v₄ (s.getReg .x10) = formBuf v₃ (s.getReg .x10) := by
    funext x; simp only [formBuf, hP₄, hC₄, hP']
  have st₄ : State s u0 v₄ (k + 1) := st₂.step
    ((hv₃.frame.union hf₄).mono fun x hx ↦ by
      rcases hx with (hx | hx | hx | hx | hx) | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hn₄] using hx))))
      · rcases hbuf₃ x (inbuf x hx) with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hn₄] using h'))))
      · exact Or.inl (by addr_omega [hx, hb]))
    (fun a h8 ha' ↦ by
      rw [hw₄ a (by rcases ha' with ha' | ha' <;> addr_omega [ha', hb])
        (fun y hy h' ↦ by rcases ha' with ha' | ha' <;> addr_omega [hy, h', ha', hb, hsn, hpin, hroom, hhi₃, h8])
        (fun y hy h' ↦ by rcases ha' with ha' | ha' <;> addr_omega [hy, h', ha', hb, hss, h8])]
      exact hv₃.keep a (Or.inl ⟨h8, Or.inr ha'⟩))
    ⟨hn₄ ▸ hv₃.heap.lo, hn₄ ▸ hv₃.heap.hi⟩ (hn₄ ▸ hv₃.mono)
    (by rw [hres, formOf, hP₄, hlen₄n, hts])
    ⟨⟨by simp only [RawVecOk, Buf, hP₄, hC₄, hn₄]; exact ⟨hp8, Or.inr ⟨by simp only [heapStart]; omega,
        by simp only [heapNext]; omega⟩⟩,
      by rw [hlen₄n, hC₄]; omega⟩, fun i hi ↦ by
        rw [hlen₄n] at hi
        rw [hP₄]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact (hold i hi).2 (by have := hv₃.tags i (by rw [hL₂, ← hLd]; exact hi); rwa [← hP'] at this)
        · subst hi
          simp only [MonoOk, ← hslot]
          rw [m6]
          exact hpre.otherTags k (by simp only [n] at hk; exact hk)⟩
    (fun x hx ↦ by
      rcases hv₃.buf x (hfb₄ ▸ hx) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by rw [hn₄]; exact h'.2⟩)
  have k₄ := b80011a38_keeps h₄
  have x18₄ : v₃.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (48 * (k + 1)) := by rw [rx .x18, ha.x18]
  have hend : v₃.getMem (v₃.getReg .x2) = s.getReg .x11 + BitVec.ofNat 64 (48 * n s) := by
    rw [hx2, hv₃.keep _ (Or.inl ⟨by addr_omega [hb], Or.inl (by addr_omega [hb])⟩),
      top₂ _ ⟨by addr_omega [hb], Or.inl (by addr_omega [hb])⟩, b80011aec_mem_same h₁, ha.mem, hu.endv]
  have hrr := hr₂.trans (hr₃.trans hr₄)
  have hO' := hO
  simp only [n] at hend hk hO'
  by_cases hlast : k + 1 = (s.getReg .x12).toNat
  · refine ⟨v₄, hrr, Or.inr (Or.inl { st₄ with
      value := by rw [st₄.value, n, hlast]
      pc := b80011a38_pc_taken h₄ (by rw [hend, x18₄, hlast])
      sp := by rw [k₄ .x2 (by decide), hx2] })⟩
  · refine ⟨v₄, hrr, Or.inl { st₄ with
      pc := b80011a38_pc_not_taken h₄ (by rw [hend, x18₄]; addr_omega [hO', hk, hlast])
      lt := by simp only [n]; omega
      sp := by rw [k₄ .x2 (by decide), hx2]
      x9 := by rw [k₄ .x9 (by decide), hx9]
      x18 := by rw [k₄ .x18 (by decide), x18₄]
      x19 := by rw [b80011a38_x19 h₄, hx9, hP₄, hP']; rfl
      x20 := by rw [k₄ .x20 (by decide), rx .x20, ha.x20]
      x21 := by rw [k₄ .x21 (by decide), rx .x21, ha.x21]
      endv := by
        rw [hw₄ _ (by addr_omega [hb]) (fun y hy h' ↦ by addr_omega [hy, h', hb, hsn, hpin, hroom, hhi₃])
          (fun y hy h' ↦ by addr_omega [hy, h', hb, hss]), ← hx2]
        rw [hx2] at hend ⊢
        simp only [n]; exact hend }⟩



/-- One term of `other`: the next loop head, the epilogue, or a dead end. -/
theorem step (hMul : MulSpec) (hG : GrowOneFreshSpec 0x80010a94 48 8) {s u0 u : MachineState}
    (hpre : AddScaledPre s) (hro : Apart (s.getReg .x10) 24 rodataBase rodataSize)
    (hw0 : u0.getMem (s.getReg .x2 - 136) = s.getReg .x13) {k : Nat}
    (hu : Inv s u0 u k) :
    ∃ v, Reaches Image.code u v ∧ (Inv s u0 v (k + 1) ∨ Fin s u0 v ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hk := hu.lt
  have hO := ValidMemRange.bounds hpre.other (by simp only [n] at hk; omega)
  simp only [n] at hk
  obtain ⟨q, hq⟩ : ∃ q, q = s.getReg .x11 + BitVec.ofNat 64 (48 * k) := ⟨_, rfl⟩
  have hqn : q.toNat = (s.getReg .x11).toNat + 48 * k := by rw [hq]; addr_omega [hO, hk]
  have hq0 : u.getMem q = s.getMem q := hu.other hpre (by omega) (by simp only [n]; omega)
  have hq8 : u.getMem (q + 8) = s.getMem (q + 8) :=
    hu.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk])
  have hq16 : u.getMem (q + 16) = s.getMem (q + 16) :=
    hu.other hpre (by addr_omega [hqn, hO, hk]) (by simp only [n]; addr_omega [hqn, hO, hk])
  have hbs := bufB hu.ok hu.heap
  -- the next term of `other`, and the length
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011a78_spec hu.pc (by
    rv_eval [hu.x18, hu.x9, ← hq]
    and_intros <;> first
      | valid_access hpre.other [hqn, hO, hk]
      | valid_access hpre.self [hb])
  have k₁ := b80011a78_keeps h₁
  have L₁ : u.getMem (s.getReg .x10 + 16) = vecLen u (s.getReg .x10) := rfl
  have hat (v : MachineState) (hm : ∀ x, v.getMem x = u.getMem x)
      (hr : ∀ r ∈ sregs, v.getReg r = u₁.getReg r) : At s u0 u v k := {
    inv := hu
    mem := hm
    sp := by rw [hr .x2 (by decide), k₁ .x2 (by decide), hu.sp]
    x9 := by rw [hr .x9 (by decide), k₁ .x9 (by decide), hu.x9]
    x12 := by rw [hr .x12 (by decide), b80011a78_x12 h₁, hu.x18]
    x18 := by rw [hr .x18 (by decide), b80011a78_x18 h₁, hu.x18]; addr_omega [hO, hk]
    x8 := by rw [hr .x8 (by decide), b80011a78_x8 h₁, hu.x9]; rfl
    x27 := by rw [hr .x27 (by decide), b80011a78_x27 h₁, hu.x9]; rfl
    x26 := by rw [hr .x26 (by decide), b80011a78_x26 h₁, hu.x9]; rfl
    x23 := by rw [hr .x23 (by decide), b80011a78_x23 h₁, hu.x18, ← hq, hq0]
    x24 := by rw [hr .x24 (by decide), b80011a78_x24 h₁, hu.x18, ← hq, hq8]
    x25 := by rw [hr .x25 (by decide), b80011a78_x25 h₁, hu.x18, ← hq, hq16]
    x19 := by rw [hr .x19 (by decide), k₁ .x19 (by decide), hu.x19]
    x20 := by rw [hr .x20 (by decide), k₁ .x20 (by decide), hu.x20]
    x21 := by rw [hr .x21 (by decide), k₁ .x21 (by decide), hu.x21] }
  have hterms : (res s k).terms = termsOf u (vecPtr u (s.getReg .x10)) (vecLen u (s.getReg .x10)).toNat := by
    rw [← hu.value]; rfl
  have hmq : monoOf u q = monoOf s q := monoOf_congr hq0 hq8 hq16
  by_cases h0 : vecLen u (s.getReg .x10) = 0
  · obtain ⟨w, hrw, hw⟩ := pushPath hMul hG hpre hro hw0 (hat u₁ (b80011a78_mem_same h₁) fun _ _ ↦ rfl)
      (b80011a78_pc_taken h₁ (by rw [hu.x9]; exact h0)) (by
        rw [hterms, h0]; rfl)
    exact ⟨w, hr₁.trans hrw, hw⟩
  have hL : 0 < (vecLen u (s.getReg .x10)).toNat := by
    rcases Nat.eq_zero_or_pos (vecLen u (s.getReg .x10)).toNat with h' | h'
    · exact absurd (BitVec.eq_of_toNat_eq h') h0
    · exact h'
  have hP : (vecPtr u (s.getReg .x10)).toNat + 48 * (vecLen u (s.getReg .x10)).toNat ≤ 0x78000000 ∧
      0x20000000 ≤ (vecPtr u (s.getReg .x10)).toNat := by
    rcases hbs.2.2 with h' | h' <;> omega
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80011a9c_spec
    (b80011a78_pc_not_taken h₁ (by rw [hu.x9]; exact h0)) trivial
  have k₀ := b80011a9c_keeps h₀
  have hs₀ : SInv u u₁ w₀ (s.getReg .x10) (monoOf u q) 0 := {
    pc := b80011a9c_pc h₀
    lt := hL
    x22 := by rw [b80011a9c_x22 h₀, k₁ .x19 (by decide), hu.x19]; simp
    x10 := by
      rw [b80011a9c_x10 h₀, b80011a78_x8 h₁, b80011a78_x27 h₁, hu.x9, offset48, Nat.sub_zero]
      rfl
    regs := fun r hr ↦ k₀ r (mem_of_mem hr _)
    mem := fun x ↦ (b80011a9c_mem_same h₀ x).trans (b80011a78_mem_same h₁ x)
    miss := fun _ h ↦ absurd h (Nat.not_lt_zero _) }
  obtain ⟨v, hrv, hm, hr, hv⟩ := Reaches.loop (fun w ↦ ∃ j, SInv u u₁ w (s.getReg .x10) (monoOf u q) j)
    (fun w ↦ (w.getReg .x10).toNat) (fun w ↦ SDone u u₁ w (s.getReg .x10) (monoOf u q))
    (sbody hP.1 hP.2 hbs.1 (fun i hi ↦ hu.ok.tags i hi) (by
        simp only [MonoOk, hq0]
        have := hpre.otherTags k hk
        rw [← hq] at this; exact this) rfl
      (by rw [k₁ .x20 (by decide), hu.x20]) (by rw [k₁ .x21 (by decide), hu.x21])
      (by rw [b80011a78_x23 h₁, hu.x18, ← hq]) (by rw [b80011a78_x24 h₁, hu.x18, ← hq])
      (by rw [b80011a78_x25 h₁, hu.x18, ← hq])) w₀ ⟨0, hs₀⟩
  have hat' := hat v hm hr
  rcases hv with ⟨hpc, j, hj, x22, heq, hmiss⟩ | ⟨hpc, hmiss⟩
  · obtain ⟨w, hrw, hw⟩ := foundPath hMul hpre hro hw0 hat' hpc hj x22 (by
      rw [hterms, List.findIdx?_eq_some_iff_getElem]
      refine ⟨by rw [termsOf_length]; exact hj, ?_, fun j' hj' ↦ ?_⟩
      · rw [termsOf_getElem, ← hq, ← hmq]; simpa [termOf] using heq
      · rw [termsOf_getElem, ← hq, ← hmq]; simpa [termOf] using hmiss j' hj')
    exact ⟨w, hr₁.trans (hr₀.trans (hrv.trans hrw)), hw⟩
  · obtain ⟨w, hrw, hw⟩ := pushPath hMul hG hpre hro hw0 hat' hpc (by
      rw [hterms, List.findIdx?_eq_none_iff]
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [termsOf_length] at hi
      rw [termsOf_getElem, ← hq, ← hmq]; simpa [termOf] using hmiss i hi)
    exact ⟨w, hr₁.trans (hr₀.trans (hrv.trans hrw)), hw⟩

/-- `other`'s bytes still to go. -/
def meas (s t : MachineState) : Nat := (s.getReg .x11).toNat + 48 * n s - (t.getReg .x18).toNat

/-- The epilogue. -/
theorem exit {s u0 u : MachineState} (hpre : AddScaledPre s) (h₁ : b800119cc.Holds s u0)
    (hu : Fin s u0 u) :
    ∃ v, Reaches Image.code u v ∧ v.pc = returnAddress s ∧ Preserves s v ∧ AddScaledPost s v := by
  have hb := bounds hpre
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b80011b5c_spec hu.pc (by
    rv_eval [hu.sp]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have hm := b80011b5c_mem_same h
  have k := b80011b5c_keeps h
  have top (a : Word) (h1 : (s.getReg .x2).toNat - 104 ≤ a.toNat) (h2 : a.toNat < (s.getReg .x2).toNat)
      (h8 : a.toNat % 8 = 0) :
      u.getMem a = u0.getMem a := hu.top a h8 (Or.inr (by addr_omega [h1, h2, hb]))
  have pc := b80011b5c_pc h
  have r1 := b80011b5c_x1 h
  have r2 := b80011b5c_x2 h
  have r8 := b80011b5c_x8 h
  have r9 := b80011b5c_x9 h
  have r18 := b80011b5c_x18 h
  have r19 := b80011b5c_x19 h
  have r20 := b80011b5c_x20 h
  have r21 := b80011b5c_x21 h
  have r22 := b80011b5c_x22 h
  have r23 := b80011b5c_x23 h
  have r24 := b80011b5c_x24 h
  have r25 := b80011b5c_x25 h
  have r26 := b80011b5c_x26 h
  have r27 := b80011b5c_x27 h
  rw [hu.sp] at pc r1 r2 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  rv_eval [] at pc r1 r2 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n8 h₁] at pc r1
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n16 h₁] at r8
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n24 h₁] at r9
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n32 h₁] at r18
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n40 h₁] at r19
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n48 h₁] at r20
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n56 h₁] at r21
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n64 h₁] at r22
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n72 h₁] at r23
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n80 h₁] at r24
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n88 h₁] at r25
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n96 h₁] at r26
  rw [top _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), b800119cc_m_x2_n104 h₁] at r27
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have hf := formOf_frame (DFrame.of_same hm fun _ ↦ False) hu.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h)
    (by addr_omega [hb]) hu.heap hn.ge
  have hfb : formBuf v (s.getReg .x10) = formBuf u (s.getReg .x10) :=
    formBuf_frame (DFrame.of_same hm fun _ ↦ False) (fun _ _ h ↦ h) (by addr_omega [hb])
  refine ⟨v, hr, pc.trans (returnAddress_eq s).symm, preserves_of r2 r8 r9 r18 r19 fun r hr ↦ ?_,
    ⟨hn ▸ hu.heap.lo, hn ▸ hu.heap.hi⟩, hn ▸ hu.mono, ?_, hf.2, fun x hx ↦ ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r20
    · exact r21
    · exact r22
    · exact r23
    · exact r24
    · exact r25
    · exact r26
    · exact r27
  · rw [hf.1, hu.value, res_n, other]
    rfl
  · rw [hfb] at hx
    rcases hu.buf x hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by simpa only [Fresh, hn] using h')
  · exact (hu.frame.union (DFrame.of_same hm fun _ ↦ False)).mono fun a ha ↦ by
      rcases ha with ha | ha
      · rcases ha with ha | ha | ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hn] using ha))))
      · exact ha.elim

/-- **`Form::add_scaled` meets its contract**, given `mul`'s and `grow_one`'s, when `self`'s header
is apart from `.rodata`: the loop writes the header and `mul` reads `.rodata`. -/
theorem add_scaled_spec (hMul : MulSpec) (hG : GrowOneFreshSpec 0x80010a94 48 8) :
    FunSpec Image.code 0x800119cc
      (fun s ↦ AddScaledPre s ∧ Apart (s.getReg .x10) 24 rodataBase rodataSize) AddScaledPost := by
  intro s hpc ⟨hpre, hro⟩
  obtain ⟨u0, h₁, u, hr, hu⟩ := setup hpc hpre
  obtain ⟨v, hrv, hv⟩ : ∃ v, Reaches Image.code s v ∧ (Fin s u0 v ∨ Dead Image.code v) := by
    rcases hu with hu | hu
    · exact ⟨u, hr, Or.inl hu⟩
    · have hO : (s.getReg .x11).toNat + 48 * n s ≤ 0xc0000008 := by
        have := ValidMemRange.bounds hpre.other (by have := hu.lt; simp only [n] at this ⊢; omega)
        simp only [n]; omega
      obtain ⟨v, huv, hv⟩ := Reaches.loop (fun t ↦ ∃ k, Inv s u0 t k) (meas s)
        (fun t ↦ Fin s u0 t ∨ Dead Image.code t) (fun t ⟨k, ht⟩ ↦ by
          obtain ⟨v, htv, hv | hv | hv⟩ := step hMul hG hpre hro (b800119cc_m_x2_n136 h₁) ht
          · refine Or.inr ⟨v, htv, ⟨k + 1, hv⟩, ?_⟩
            have h1 := hv.lt
            simp only [meas, n, hv.x18, ht.x18]
            simp only [n] at h1 hO
            rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
            omega
          · exact Or.inl ⟨v, htv, Or.inl hv⟩
          · exact Or.inl ⟨v, htv, Or.inr hv⟩) u ⟨0, hu⟩
      exact ⟨v, hr.trans huv, hv⟩
  rcases hv with hv | hd
  · obtain ⟨w, hrw, hpc', hpres, hpost⟩ := exit hpre h₁ hv
    exact ⟨w, hrv.trans hrw, Or.inl ⟨hpc', hpres, hpost⟩⟩
  · exact ⟨v, hrv, Or.inr hd⟩

/-- **`Form::add_scaled` meets its contract.** -/
theorem add_scaled_spec' (hMul : MulSpec) (hG : GrowOneFreshSpec 0x80010a94 48 8) :
    AddScaledSpec :=
  fun s hpc hpre ↦ add_scaled_spec hMul hG s hpc ⟨hpre, hpre.selfRodata⟩

end Rv64Verifier.Layout.AddScaled
