import Rv64Verifier.Proofs.Pcs.Contracts
import Rv64Verifier.Blocks.F66

/-!
# `<RingWeight>::evaluate`

```rust
pub fn evaluate(&self, r_prime: &[E]) -> E {
    ring_weight(&self.point, r_prime, &self.coefficients)
}
fn ring_weight(r: &[E], r_prime: &[E], coefficients: &[E]) -> E {
    assert_eq!(r.len(), r_prime.len());
    let mut total = ZERO;
    let mut frobenius = r.to_vec();
    for &c in coefficients {
        let mut product = c;
        for (value, &challenge) in frobenius.iter_mut().zip(r_prime) {
            product *= ONE + *value + challenge;
            *value = value.square();
        }
        total += product;
    }
    total
}
```

compiled at `0x8000df24` (`Blocks/F66.lean`), with `S` the entry's `sp`, `n` the length of
`r_prime`: `0x8000df24` saves `ra`, `s0`..`s11` in a 176-byte frame and traps (`0x8000e128`)
unless `r.len() = n`; `0x8000df68` zeroes the result's `c1`, `c2` and calls
`try_allocate_in(S - 128, n, 0, 8, 24)`; `0x8000dfa0` traps on `Err`; `0x8000dfa8` takes the buffer
`P` (`s2`) and, for `n > 0`, `0x8000dfb8` copies `r` into it (`memcpy`); `0x8000dfcc` goes to the
end (`0x8000e0e4`, `total = 0`) when there are no coefficients, else `0x8000dfd0` sets the total
(`s4`, `s7`, `s6`) to zero, `s5` walking the coefficients up to `s9`, `s8 = r_prime + 16`,
`s10 = P + 24 n`. The outer loop at `0x8000e01c` puts the coefficient in `product` (`S - 176`)
and starts `s3` at `P`, `s11` at `s8`; the inner loop at `0x8000e040` writes
`1 + value + challenge` to `S - 152` and calls `mul(S - 128, S - 176, S - 152)`, `0x8000e088`
copies the product back and calls `E::square(S - 128, s3)`, `0x8000e0b0` stores the square over
the value and advances; `0x8000dffc` adds `product` to the total. `0x8000e0d8` stores `c1`, `c2`,
`0x8000e0e8` stores `c0`, restores and returns.
-/

namespace Rv64Verifier.Proofs.Pcs.RingEval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F66
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The mirror's loops -/

/-- `r`, `r_prime`, the coefficients. -/
def pt (s : MachineState) : List E := vecEs s (s.getReg .x11)
def rp (s : MachineState) : List E := eListAt s (s.getReg .x12) (s.getReg .x13).toNat
def cs (s : MachineState) : List E := vecEs s (s.getReg .x11 + 24)

/-- `n` and the number of coefficients. -/
@[rv_addr] def nn (s : MachineState) : Nat := (s.getReg .x13).toNat
@[rv_addr] def nc (s : MachineState) : Nat := (s.getMem (s.getReg .x11 + 40)).toNat

/-- The coefficients' buffer `C`. -/
@[rv_addr] def cp (s : MachineState) : Word := s.getMem (s.getReg .x11 + 32)

theorem cs_eq (s : MachineState) : cs s = eListAt s (cp s) (nc s) := by
  have h8 : s.getReg .x11 + 24 + 8 = s.getReg .x11 + 32 := by rv_eval []
  have h16 : s.getReg .x11 + 24 + 16 = s.getReg .x11 + 40 := by rv_eval []
  simp only [cs, vecEs, vecPtr, vecLen, h8, h16, cp, nc]

/-- One coefficient of `ring_weight`'s loop, as `ringWeightRust` folds it. -/
def stepW (rPrime : List E) (acc : E × List E) (c : E) : E × List E :=
  let pass := ringWeightPass rPrime c acc.2
  (acc.1 + pass.1, pass.2)

/-- `(total, frobenius)` after `i` coefficients. -/
def st (s : MachineState) (i : Nat) : E × List E := ((cs s).take i).foldl (stepW (rp s)) (0, pt s)

/-- `product` after `j` values of the pass over `fb` from `c`. -/
def prodJ (rPrime fb : List E) (c : E) (j : Nat) : E :=
  ((fb.zip rPrime).take j).foldl (fun product (value, challenge) ↦
    product * (1 + value + challenge)) c

theorem cs_length (s : MachineState) : (cs s).length = nc s := by
  rw [cs_eq, eListAt_length]

theorem rp_length (s : MachineState) : (rp s).length = nn s := by
  simp [rp, eListAt_length, nn]

theorem stepW_length (rPrime : List E) (acc : E × List E) (c : E)
    (h : acc.2.length = rPrime.length) : (stepW rPrime acc c).2.length = rPrime.length := by
  simp only [stepW]
  rw [ringWeightPass_snd rPrime c acc.2 h, List.length_map, h]

theorem foldl_stepW_length (rPrime : List E) :
    ∀ (l : List E) (acc : E × List E), acc.2.length = rPrime.length →
      (l.foldl (stepW rPrime) acc).2.length = rPrime.length
  | [], _, h => h
  | c :: l, acc, h => foldl_stepW_length rPrime l _ (stepW_length rPrime acc c h)

theorem st_length {s : MachineState} (h : (pt s).length = (rp s).length) (i : Nat) :
    (st s i).2.length = nn s := by
  rw [st, foldl_stepW_length _ _ _ h, rp_length]

theorem st_zero (s : MachineState) : st s 0 = (0, pt s) := rfl

theorem st_succ {s : MachineState} {i : Nat} (hi : i < nc s) :
    st s (i + 1) = stepW (rp s) (st s i) ((cs s)[i]'(by rw [cs_length]; exact hi)) := by
  rw [st, List.take_succ_eq_append_getElem (by rw [cs_length]; exact hi), List.foldl_append]
  rfl

theorem cs_getD (s : MachineState) (i : Nat) (h : i < nc s) :
    (cs s).getD i 0 = eAt s (cp s + BitVec.ofNat 64 (24 * i)) := by
  rw [List.getD_eq_getElem _ _ (by rw [cs_length]; exact h)]
  simp only [cs_eq, eListAt_getElem]

theorem rp_getD (s : MachineState) (j : Nat) (h : j < nn s) :
    (rp s).getD j 0 = eAt s (s.getReg .x12 + BitVec.ofNat 64 (24 * j)) := by
  rw [List.getD_eq_getElem _ _ (by rw [rp_length]; exact h)]
  simp only [rp, eListAt_getElem]

theorem prodJ_zero (rPrime fb : List E) (c : E) : prodJ rPrime fb c 0 = c := rfl

theorem prodJ_succ (rPrime fb : List E) (c : E) (j : Nat) (h1 : j < fb.length)
    (h2 : j < rPrime.length) :
    prodJ rPrime fb c (j + 1) = prodJ rPrime fb c j * (1 + fb.getD j 0 + rPrime.getD j 0) := by
  have hz : j < (fb.zip rPrime).length := by rw [List.length_zip]; omega
  rw [prodJ, List.take_succ_eq_append_getElem hz, List.foldl_append, List.getElem_zip,
    List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  rfl

/-- The pass's product is `prodJ` over all of `fb`. -/
theorem pass_fst (rPrime fb : List E) (c : E) (h : fb.length = rPrime.length) :
    (ringWeightPass rPrime c fb).1 = prodJ rPrime fb c rPrime.length := by
  rw [prodJ, List.take_of_length_le (by rw [List.length_zip]; omega)]
  rfl

/-- `ring_weight` wherever the lengths agree, by `st`. -/
theorem value_eq {s : MachineState} (h : (pt s).length = (rp s).length) :
    (ringWeightAt s (s.getReg .x11)).evaluate (rp s) = some (st s (nc s)).1 := by
  have h' : (ringWeightAt s (s.getReg .x11)).point.length = (rp s).length := h
  rw [RingWeightRust.evaluate, ringWeightRust, ite_eq_left h', st,
    List.take_of_length_le (by rw [cs_length])]
  rfl

/-! ## The frame -/

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25), (96, .x26), (104, .x27)]

/-- What the function writes besides its stack, `NEXT` and the heap: the result. -/
def W (s : MachineState) (a : Word) : Prop := Within a (s.getReg .x10) 24

abbrev Inv (s u : MachineState) (nx : Word) : Prop :=
  PInv s u 176 ringEvalStack slots [] (W s) nx

theorem bounds {s : MachineState} (h : RingEvalPre s) :
    0x78000000 + 1200 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  simp only [ringEvalStack, mulStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem Inv.step' {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : RingEvalPre s) (h : Inv s u nx) (hX : DFrame u v X)
    (hXsub : ∀ a, X a → Wr s ringEvalStack (W s) nx' a)
    (hXslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 104) 104)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : Inv s v nx' :=
  h.step 104 (by decide) (by have := bounds hpre; omega) hX hXsub hXslot hnx hle hend hsp
    (fun _ h ↦ by cases h)

/-- Inputs the function reads are never written. -/
theorem Inv.src {s u : MachineState} {nx : Word} (h : Inv s u nx)
    {a : Word} {n : Nat} (hs : Src s ringEvalStack a n)
    (hw : Apart (s.getReg .x10) 24 a n) : ∀ x, Within x a n → ¬ Wr s ringEvalStack (W s) nx x :=
  hs.miss (fun x hx hW ↦ by simp only [W] at hW; addr_omega [hx, hW, hw]) h.fits

theorem Inv.rodata' {s u : MachineState} {nx : Word} (hpre : RingEvalPre s) (h : Inv s u nx) :
    RodataOk u :=
  h.rodata hpre.rodata (fun a ha hr ↦ by
    have := hpre.out.rodata
    simp only [W] at ha; addr_omega [ha, hr, this]) hpre.stack.rodata

theorem trap : Image.code.fetch 0x8000e128 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- The buffer `P` of `n` elements, from `heapNext s` up to below `nx`. -/
structure BufOk (s : MachineState) (P nx : Word) : Prop where
  align : P.toNat % 8 = 0
  range : nn s = 0 ∨ (heapNext s ≤ P.toNat ∧ P.toNat + 24 * nn s ≤ nx.toNat)

/-- At `0x8000dfcc`: `frobenius` holds `r`. -/
structure Mid (s u : MachineState) (nx P : Word) : Prop where
  inv : Inv s u nx
  pc : u.pc = 0x8000dfcc
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x13
  x18 : u.getReg .x18 = P
  x19 : u.getReg .x19 = s.getReg .x12
  x21 : u.getReg .x21 = s.getMem (s.getReg .x11 + 32)
  x24 : u.getReg .x24 = s.getMem (s.getReg .x11 + 40)
  x25 : u.getReg .x25 = s.getReg .x13 * 8
  x26 : u.getReg .x26 = s.getReg .x13 * 16
  len : s.getMem (s.getReg .x11 + 16) = s.getReg .x13
  o8 : u.getMem (s.getReg .x10 + 8) = 0
  o16 : u.getMem (s.getReg .x10 + 16) = 0
  buf : eListAt u P (nn s) = pt s
  bufOk : BufOk s P nx

/-- The prologue, the length check, the allocation and the copy. -/
theorem setup (hT : TryAllocZeroedSpec) (hC : Runtime.MemcpySpec 0x800126e4) {s : MachineState}
    (hpc : s.pc = 0x8000df24) (hpre : RingEvalPre s) :
    ∃ u, Reaches Image.code s u ∧ (Dead Image.code u ∨ ∃ nx P, Mid s u nx P) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hSW := hpre.self.self.stack
  have hWr := hpre.self.self.region.resolve_left (by decide)
  have hWb := Region.bounds hWr
  have hO := hpre.out.region
  have hOb := Region.bounds hO
  have hOs := hpre.out.stack
  have hOf := hpre.out.free
  simp only [Outside] at hOf
  -- the prologue and the check
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000df24_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hWr (by addr_omega [hWb]) (by addr_omega [hWb]) (by addr_omega [hWb])
      | addr_omega [hWb, hb, hSW])
  by_cases hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13
  swap
  · exact ⟨t₁, hr₁, Or.inl (dead_of_fetch (by rw [b8000df24_pc_taken h₁ hlen]; exact trap))⟩
  have k₁ := b8000df24_keeps h₁
  have hm₁ := b8000df24_frame h₁ (by omega)
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := {
    sp := b8000df24_x2 h₁
    slots := by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000df24_m_x2_n8 h₁, b8000df24_m_x2_n16 h₁, b8000df24_m_x2_n24 h₁,
        b8000df24_m_x2_n32 h₁, b8000df24_m_x2_n40 h₁, b8000df24_m_x2_n48 h₁,
        b8000df24_m_x2_n56 h₁, b8000df24_m_x2_n64 h₁, b8000df24_m_x2_n72 h₁,
        b8000df24_m_x2_n80 h₁, b8000df24_m_x2_n88 h₁, b8000df24_m_x2_n96 h₁,
        b8000df24_m_x2_n104 h₁⟩
    kept := fun _ h ↦ by cases h
    mem := (DFrame.of_memFrame hm₁).mono fun a ha ↦
      Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
    next := hm₁ _ (by addr_omega [hb, hnx8])
    mono := Nat.le_refl _
    fits := hheap.hi }
  -- zero `c1`, `c2`, call `try_allocate_in`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000df68_spec
    (b8000df24_pc_not_taken h₁ hlen) (by
      rv_eval [k₁ .x10 (by decide), k₁ .x11 (by decide)]
      and_intros <;> first
        | exact Region.valid hO (by addr_omega [hOb]) (by addr_omega [hOb]) (by addr_omega [hOb])
        | exact Region.valid hWr (by addr_omega [hWb]) (by addr_omega [hWb]) (by addr_omega [hWb]))
  have k₂ := b8000df68_keeps h₂
  have hm₂ := b8000df68_frame h₂ (by rw [k₁ .x10 (by decide)]; addr_omega [hOb])
  rw [k₁ .x10 (by decide)] at hm₂
  have inv₂ := inv₁.step' hpre (DFrame.of_memFrame hm₂)
    (fun a ha ↦ Or.inl (by simp only [W]; addr_omega [ha, hOb]))
    (fun a ha ↦ by addr_omega [ha, hOb, hOs, hb])
    ((hm₂ _ (by addr_omega [hOf.2, hOb])).trans inv₁.next) (Nat.le_refl _) hheap.hi
    (k₂ .x2 (by decide))
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 176 := inv₂.sp
  have hx10₂ : t₂.getReg .x10 = s.getReg .x2 - 128 := by
    rw [b8000df68_x10 h₂, b8000df24_x2 h₁]; rv_eval []
  have hn₂ : heapNext t₂ = heapNext s := by simp only [heapNext, inv₂.next]
  have hsl : stackLo t₂ tryAllocStack = s.getReg .x2 - 224 := by
    simp only [stackLo, tryAllocStack, hsp₂]; rv_eval []
  have hpre₂ : TryAllocPre .x13 .x14 t₂ := {
    heap := ⟨hn₂ ▸ hheap.lo, hn₂ ▸ hheap.hi⟩
    out := by rw [hx10₂]; valid_sub hst.valid [hb]
    align := by rw [b8000df68_x13 h₂]; decide
    size := by rw [b8000df68_x14 h₂]; decide
    stack := hst.sub 176 hsp₂ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10₂]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₂, hsl]; addr_omega [hb] }
  obtain ⟨t₃, hr₃, ⟨hpc₃, hpres₃, hpost₃, -⟩ | hdead⟩ := hT.call hr₂ (b8000df68_pc h₂) hpre₂
  swap
  · exact ⟨t₃, hr₁.trans hr₃, Or.inl hdead⟩
  have hfr₃ := hpost₃.frame
  rw [hx10₂, hsl] at hfr₃
  have hfit₃ := hpost₃.heap.hi
  have inv₃ : Inv s t₃ (t₃.getMem nextAddr) := inv₂.step' hpre (DFrame.of_byteFrame hfr₃)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨hn₂ ▸ ha.1, ha.2⟩)))
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfit₃])
    rfl (by have := hpost₃.mono; simp only [heapNext] at this hn₂ ⊢; omega) hfit₃
    (hpres₃.reg .x2)
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 176 := inv₃.sp
  -- `Err` traps
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000dfa0_spec
    (by rw [hpc₃, returnAddress_eq, b8000df68_x1 h₂]; decide) (by
      rv_eval [hsp₃]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₃.getMem (s.getReg .x2 - 128)) 0 with htag | htag
  swap
  · refine ⟨t₄, hr₁.trans (hr₃.trans hr₄), Or.inl (dead_of_fetch ?_)⟩
    rw [b8000dfa0_pc_taken h₄ (by rv_eval [hsp₃]; exact htag)]
    exact trap
  have k₄ := b8000dfa0_keeps h₄
  have hm₄ := b8000dfa0_mem_same h₄
  have inv₄ := inv₃.same hm₄ (k₄ .x2 (by decide)) (fun _ h ↦ by cases h)
  obtain ⟨-, hbuf⟩ := hpost₃.ok (by rw [hx10₂]; exact htag)
  rw [hx10₂, b8000df68_x11 h₂, b8000df68_x14 h₂, b8000df68_x13 h₂, k₁ .x13 (by decide)] at hbuf
  rv_eval [] at hbuf
  obtain ⟨P, hP⟩ : ∃ P, P = t₃.getMem (s.getReg .x2 - 112) := ⟨_, rfl⟩
  rw [← hP] at hbuf
  have hBuf : BufOk s P (t₃.getMem nextAddr) := {
    align := hbuf.1
    range := by
      rcases hbuf.2 with h | h
      · exact Or.inl (by simp only [nn]; omega)
      · exact Or.inr ⟨hn₂ ▸ h.1, by simp only [nn, heapNext] at h ⊢; omega⟩ }
  -- the buffer
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 176 := inv₄.sp
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000dfa8_spec
    (b8000dfa0_pc_not_taken h₄ (by rv_eval [hsp₃]; exact htag)) (by
      rv_eval [hsp₄]
      valid_access hst.valid [hb])
  have k₅ := b8000dfa8_keeps h₅
  have inv₅ := inv₄.same (b8000dfa8_mem_same h₅) (k₅ .x2 (by decide)) (fun _ h ↦ by cases h)
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x24]) :
      t₅.getReg r = t₂.getReg r := by
    rw [k₅ r (mem_of_mem hr _), k₄ r (mem_of_mem hr _),
      hpres₃ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have hx9₅ : t₅.getReg .x9 = s.getReg .x13 := by
    rw [hreg .x9 (by decide), b8000df68_x9 h₂, k₁ .x13 (by decide)]
  have hx18₅ : t₅.getReg .x18 = P := by
    rw [b8000dfa8_x18 h₅, hsp₄, hm₄, hP]; rv_eval []
  have hx19₅ : t₅.getReg .x19 = s.getReg .x12 := by
    rw [hreg .x19 (by decide), k₂ .x19 (by decide), b8000df24_x19 h₁]
  have hx8₅ : t₅.getReg .x8 = s.getReg .x10 := by
    rw [hreg .x8 (by decide), b8000df68_x8 h₂, k₁ .x10 (by decide)]
  have hm₁' (a : Word) (h1 : (s.getReg .x11).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x11).toNat + 48) : t₁.getMem a = s.getMem a :=
    hm₁ a (by addr_omega [h1, h2, hWb, hSW, hb])
  have hx21₅ : t₅.getReg .x21 = s.getMem (s.getReg .x11 + 32) := by
    rw [hreg .x21 (by decide), b8000df68_x21 h₂, k₁ .x11 (by decide),
      hm₁' _ (by addr_omega [hWb]) (by addr_omega [hWb])]
  have hx24₅ : t₅.getReg .x24 = s.getMem (s.getReg .x11 + 40) := by
    rw [hreg .x24 (by decide), b8000df68_x24 h₂, k₁ .x11 (by decide),
      hm₁' _ (by addr_omega [hWb]) (by addr_omega [hWb])]
  have hx20₅ : t₅.getReg .x20 = s.getMem (s.getReg .x11 + 8) := by
    rw [hreg .x20 (by decide), b8000df68_x20 h₂, k₁ .x11 (by decide),
      hm₁' _ (by addr_omega [hWb]) (by addr_omega [hWb])]
  have hx9₄ : t₄.getReg .x9 = s.getReg .x13 := by
    rw [k₄ .x9 (by decide), hpres₃.reg .x9, b8000df68_x9 h₂, k₁ .x13 (by decide)]
  have hx25₅ : t₅.getReg .x25 = s.getReg .x13 * 8 := by
    rw [b8000dfa8_x25 h₅, hx9₄]
  have hx26₅ : t₅.getReg .x26 = s.getReg .x13 * 16 := by
    rw [b8000dfa8_x26 h₅, hx9₄]
  -- the result's `c1`, `c2`, zeroed
  have hfit₂ := inv₂.fits
  have hOmiss₃ : ∀ x, Within x (s.getReg .x10) 24 →
      ¬ (Within x (s.getReg .x2 - 128) 24 ∨ Within x (s.getReg .x2 - 224) 48 ∨
        Within x nextAddr 8 ∨ Fresh t₂ t₃ x) := by
    intro x hx hX
    rcases hX with hX | hX | hX | hX
    · addr_omega [hx, hX, hOs, hb]
    · addr_omega [hx, hX, hOs, hb]
    · addr_omega [hx, hX, hOf.2]
    · simp only [Fresh] at hX
      rw [hn₂] at hX
      rcases hOf.1 with h | h
      · addr_omega [hx, hX.1, h]
      · addr_omega [hx, hX.2, h, hfit₃]
  have o8₅ : t₅.getMem (s.getReg .x10 + 8) = 0 := by
    rw [b8000dfa8_mem_same h₅, hm₄, DFrame.word (DFrame.of_byteFrame hfr₃)
      (fun x hx ↦ hOmiss₃ x (by addr_omega [hx, hOb])) (by addr_omega [hOb]),
      ← k₁ .x10 (by decide), b8000df68_m_x10_8 h₂]
  have o16₅ : t₅.getMem (s.getReg .x10 + 16) = 0 := by
    rw [b8000dfa8_mem_same h₅, hm₄, DFrame.word (DFrame.of_byteFrame hfr₃)
      (fun x hx ↦ hOmiss₃ x (by addr_omega [hx, hOb])) (by addr_omega [hOb]),
      ← k₁ .x10 (by decide), b8000df68_m_x10_16 h₂]
  have hpt : pt s = eListAt s (s.getMem (s.getReg .x11 + 8)) (nn s) := by
    simp only [pt, vecEs, vecPtr, vecLen, hlen, nn]
  by_cases h0 : s.getReg .x13 = 0
  · have hn0 : nn s = 0 := by simp only [nn, h0]; rfl
    refine ⟨t₅, hr₁.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr ⟨_, P, {
      inv := inv₅
      pc := b8000dfa8_pc_taken h₅ (by rw [hx9₄]; exact h0)
      x8 := hx8₅
      x9 := hx9₅
      x18 := hx18₅
      x19 := hx19₅
      x21 := hx21₅
      x24 := hx24₅
      x25 := hx25₅
      x26 := hx26₅
      len := hlen
      o8 := o8₅
      o16 := o16₅
      buf := by rw [hpt, hn0]; rfl
      bufOk := hBuf }⟩⟩
  -- copy `r`
  have hn0 : 0 < nn s := by
    rcases Nat.eq_zero_or_pos (nn s) with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simp only [nn] at h; simpa using h)) h0
    · exact h
  have hR := (hpre.rPrime.region.resolve_left (by simp only [nn] at hn0; omega))
  have hRb := Region.bounds hR
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + 24 * nn s ≤ (t₃.getMem nextAddr).toNat :=
    hBuf.range.resolve_left (by omega)
  have hlo := hheap.lo
  have hpsrc := hpre.self.point
  rw [show vecLen s (s.getReg .x11) = s.getReg .x13 from hlen] at hpsrc
  have hpR := hpsrc.region.resolve_left (by simp only [nn] at hn0; omega)
  have hpRb := Region.bounds hpR
  have hpS := hpsrc.stack
  have hpF := hpsrc.free
  simp only [Outside, vecPtr] at hpF hpS hpRb hpR
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000dfb8_spec
    (b8000dfa8_pc_not_taken h₅ (by rw [hx9₄]; exact h0)) trivial
  have k₆ := b8000dfb8_keeps h₆
  have inv₆ := inv₅.same (b8000dfb8_mem_same h₆) (k₆ .x2 (by decide)) (fun _ h ↦ by cases h)
  have hsp₆ : t₆.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 176 := inv₆.sp
  have hd₆ : t₆.getReg .x10 = P := by rw [b8000dfb8_x10 h₆, hx18₅]
  have hs₆ : t₆.getReg .x11 = s.getMem (s.getReg .x11 + 8) := by rw [b8000dfb8_x11 h₆, hx20₅]
  have hn₆ : (t₆.getReg .x12).toNat = 24 * nn s := by
    rw [b8000dfb8_x12 h₆, hx25₅, hx26₅]
    simp only [nn] at hRb ⊢
    addr_omega [hRb]
  have hfit₃' := inv₃.fits
  have hpre₆ : Runtime.MemcpyPre t₆ := {
    dst := by
      rw [hd₆, hn₆]; simp only [Mapped]
      left; simp only [heapStart, heapEnd] at hlo hfit₃' ⊢; omega
    src := by rw [hs₆, hn₆]; exact hpR.1
    apart := by
      rw [hd₆, hs₆, hn₆]
      rcases hpF.1 with h | h
      · addr_omega [h, hPr]
      · addr_omega [h, hPr, hfit₃']
    stack := ⟨by
        simp only [stackLo, hsp₆]
        valid_sub hst.valid [hb],
      by rw [hsp₆]; addr_omega [hb]⟩
    dstStack := by
      rw [hd₆, hn₆]; simp only [stackLo, hsp₆, memcpyStack]
      addr_omega [hPr, hfit₃', hab, hb]
    srcStack := by
      rw [hs₆, hn₆]; simp only [stackLo, hsp₆, memcpyStack]
      addr_omega [hpS, hb] }
  obtain ⟨t₇, hr₇, ⟨hpc₇, hpres₇, hcpy⟩ | hdead⟩ := hC.call hr₆ (b8000dfb8_pc h₆) hpre₆
  swap
  · exact ⟨t₇, hr₁.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₇))), Or.inl hdead⟩
  have hfr₇ := hcpy.frame
  rw [hd₆, hn₆] at hfr₇
  simp only [stackLo, hsp₆, memcpyStack] at hfr₇
  have hmiss₇ (x : Word) (hx : Within x P (24 * nn s) ∨
      Within x (s.getReg .x2 - BitVec.ofNat 64 176 - BitVec.ofNat 64 16) 16) :
      Wr s ringEvalStack (W s) (t₃.getMem nextAddr) x := by
    rcases hx with hx | hx
    · exact Or.inr (Or.inr (Or.inr (by simp only [Within] at hx; omega)))
    · exact Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [hx, hb]))
  have inv₇ := Inv.step' hpre inv₆ (DFrame.of_byteFrame hfr₇) hmiss₇
    (fun a ha ↦ by
      rcases ha with ha | ha
      · addr_omega [ha, hPr, hfit₃', hab, hb]
      · addr_omega [ha, hb])
    (DFrame.word (DFrame.of_byteFrame hfr₇) (fun x hx hX ↦ by
        rcases hX with hX | hX
        · addr_omega [hx, hX, hPr, hfit₃']
        · addr_omega [hx, hX, hnx8, hb]) (by decide) |>.trans inv₆.next)
    (Nat.le_refl _) inv₆.fits (hpres₇.reg .x2)
  have hby := hcpy.bytes
  rw [hd₆, hs₆, hn₆] at hby
  have keep₇ (a : Word) (ha : ∀ x, Within x a 8 → ¬ (Within x P (24 * nn s) ∨
      Within x (s.getReg .x2 - BitVec.ofNat 64 176 - BitVec.ofNat 64 16) 16))
      (hab' : a.toNat + 8 ≤ 2 ^ 64) : t₇.getMem a = t₅.getMem a := by
    rw [DFrame.word (DFrame.of_byteFrame hfr₇) ha hab', b8000dfb8_mem_same h₆]
  have hOmiss₇ (c : Nat) (hc : c = 8 ∨ c = 16) : ∀ x, Within x (s.getReg .x10 + BitVec.ofNat 64 c) 8 →
      ¬ (Within x P (24 * nn s) ∨
        Within x (s.getReg .x2 - BitVec.ofNat 64 176 - BitVec.ofNat 64 16) 16) := by
    intro x hx hX
    rcases hX with hX | hX
    · rcases hOf.1 with h | h
      · addr_omega [hx, hX, h, hPr, hc, hOb]
      · addr_omega [hx, hX, h, hPr, hfit₃', hc, hOb]
    · addr_omega [hx, hX, hOs, hb, hc, hOb]
  have hregs (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x21, .x24, .x25, .x26]) :
      t₇.getReg r = t₅.getReg r := by
    rw [hpres₇ r (by unfold calleeSaved; exact mem_of_mem hr _), k₆ r (mem_of_mem hr _)]
  refine ⟨t₇, hr₁.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₇))), Or.inr ⟨_, P, {
    inv := inv₇
    pc := by rw [hpc₇, returnAddress_eq, b8000dfb8_x1 h₆]; decide
    x8 := (hregs .x8 (by decide)).trans hx8₅
    x9 := (hregs .x9 (by decide)).trans hx9₅
    x18 := (hregs .x18 (by decide)).trans hx18₅
    x19 := (hregs .x19 (by decide)).trans hx19₅
    x21 := (hregs .x21 (by decide)).trans hx21₅
    x24 := (hregs .x24 (by decide)).trans hx24₅
    x25 := (hregs .x25 (by decide)).trans hx25₅
    x26 := (hregs .x26 (by decide)).trans hx26₅
    len := hlen
    o8 := by
      rw [keep₇ _ (by simpa using hOmiss₇ 8 (Or.inl rfl)) (by addr_omega [hOb])]; exact o8₅
    o16 := by
      rw [keep₇ _ (by simpa using hOmiss₇ 16 (Or.inr rfl)) (by addr_omega [hOb])]; exact o16₅
    buf := by
      rw [eListAt_eq_of_bytesAt hby hBuf.align hpRb.2.2, hpt]
      have hop := hpre.outPoint
      rw [show vecLen s (s.getReg .x11) = s.getReg .x13 from hlen] at hop
      exact DFrame.eList inv₆.mem (Inv.src inv₆ hpsrc hop) (Or.inr (by addr_omega [hpRb]))
    bufOk := hBuf }⟩⟩

/-! ## The loops' invariants -/

/-- Registers fixed through the loops. -/
structure Regs (s u : MachineState) (P : Word) : Prop where
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x13
  x18 : u.getReg .x18 = P
  x24 : u.getReg .x24 = s.getReg .x12 + 16
  x25 : u.getReg .x25 = cp s + BitVec.ofNat 64 (24 * nc s)
  x26 : u.getReg .x26 = P + BitVec.ofNat 64 (24 * nn s)

/-- At `0x8000e01c`, before coefficient `i`. -/
structure Outer (s u : MachineState) (nx P : Word) (i : Nat) : Prop extends Regs s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8000e01c
  lt : i < nc s
  x21 : u.getReg .x21 = cp s + BitVec.ofNat 64 (24 * i)
  acc : Model.limbs (st s i).1 = (u.getReg .x20, u.getReg .x23, u.getReg .x22)
  buf : ∀ l < nn s, eAt u (P + BitVec.ofNat 64 (24 * l)) = (st s i).2.getD l 0
  o8 : u.getMem (s.getReg .x10 + 8) = 0
  o16 : u.getMem (s.getReg .x10 + 16) = 0

/-- At `0x8000e040`, value `j` of coefficient `i`'s pass. -/
structure Inner (s u : MachineState) (nx P : Word) (i j : Nat) : Prop extends Regs s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8000e040
  lt : i < nc s
  ltj : j < nn s
  x21 : u.getReg .x21 = cp s + BitVec.ofNat 64 (24 * i)
  x19 : u.getReg .x19 = P + BitVec.ofNat 64 (24 * j)
  x27 : u.getReg .x27 = s.getReg .x12 + BitVec.ofNat 64 (24 * j) + 16
  acc : Model.limbs (st s i).1 = (u.getReg .x20, u.getReg .x23, u.getReg .x22)
  prod : eAt u (s.getReg .x2 - 176) = prodJ (rp s) (st s i).2 ((cs s).getD i 0) j
  buf : ∀ l < nn s, eAt u (P + BitVec.ofNat 64 (24 * l)) =
    if l < j then (st s i).2.getD l 0 * (st s i).2.getD l 0 else (st s i).2.getD l 0
  o8 : u.getMem (s.getReg .x10 + 8) = 0
  o16 : u.getMem (s.getReg .x10 + 16) = 0

/-- At `0x8000dffc`, coefficient `i`'s pass done. -/
structure Done (s u : MachineState) (nx P : Word) (i : Nat) : Prop extends Regs s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8000dffc
  lt : i < nc s
  x21 : u.getReg .x21 = cp s + BitVec.ofNat 64 (24 * i)
  acc : Model.limbs (st s i).1 = (u.getReg .x20, u.getReg .x23, u.getReg .x22)
  prod : eAt u (s.getReg .x2 - 176) = prodJ (rp s) (st s i).2 ((cs s).getD i 0) (nn s)
  buf : ∀ l < nn s, eAt u (P + BitVec.ofNat 64 (24 * l)) = (st s (i + 1)).2.getD l 0
  o8 : u.getMem (s.getReg .x10 + 8) = 0
  o16 : u.getMem (s.getReg .x10 + 16) = 0

/-- At `0x8000e0e8`: the total's `c1`, `c2` stored, `c0` in `s4`. -/
structure Exit (s u : MachineState) (nx : Word) : Prop where
  inv : Inv s u nx
  pc : u.pc = 0x8000e0e8
  x8 : u.getReg .x8 = s.getReg .x10
  x20 : u.getReg .x20 = (Model.limbs (st s (nc s)).1).1
  o8 : u.getMem (s.getReg .x10 + 8) = (Model.limbs (st s (nc s)).1).2.1
  o16 : u.getMem (s.getReg .x10 + 16) = (Model.limbs (st s (nc s)).1).2.2

theorem limbs_zero : Model.limbs (0 : E) = (0, 0, 0) := by
  decide +kernel

/-- The lengths, once the check passed. -/
theorem pt_length {s : MachineState} (h : s.getMem (s.getReg .x11 + 16) = s.getReg .x13) :
    (pt s).length = (rp s).length := by
  simp only [pt, vecEs, vecLen, eListAt_length, rp, h]

/-- The coefficients' bytes, read and never written. -/
theorem coeffs_src {s : MachineState} (hpre : RingEvalPre s) :
    Src s ringEvalStack (cp s) (24 * nc s) ∧ Apart (s.getReg .x10) 24 (cp s) (24 * nc s) := by
  have h8 : s.getReg .x11 + 24 + 8 = s.getReg .x11 + 32 := by rv_eval []
  have h16 : s.getReg .x11 + 24 + 16 = s.getReg .x11 + 40 := by rv_eval []
  have h1 := hpre.self.coeffs
  have h2 := hpre.outCoeffs
  simp only [vecPtr, vecLen, h8, h16] at h1 h2
  exact ⟨h1, h2⟩

theorem cs_region {s : MachineState} (hpre : RingEvalPre s) (h : 0 < nc s) :
    Region (cp s) (24 * nc s) :=
  (coeffs_src hpre).1.region.resolve_left (by omega)

/-! ## From the copy to the loop -/

theorem start {s u : MachineState} {nx P : Word} (hpre : RingEvalPre s) (hm : Mid s u nx P) :
    ∃ v, Reaches Image.code u v ∧ (Exit s v nx ∨ Outer s v nx P 0) := by
  have hb := bounds hpre
  have hk := hm.inv.kept
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000dfcc_spec hm.pc trivial
  have k₁ := b8000dfcc_keeps h₁
  have inv₁ := hm.inv.same (b8000dfcc_mem_same h₁) (k₁ .x2 (by decide)) (fun _ h ↦ by cases h)
  by_cases h0 : s.getMem (s.getReg .x11 + 40) = 0
  · have hnc : nc s = 0 := by simp only [nc, h0]; rfl
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000e0e4_spec
      (b8000dfcc_pc_taken h₁ (by rw [hm.x24]; exact h0)) trivial
    have k₂ := b8000e0e4_keeps h₂
    have hv : Model.limbs (st s (nc s)).1 = (0, 0, 0) := by rw [hnc, st_zero]; exact limbs_zero
    refine ⟨t₂, hr₁.trans hr₂, Or.inl {
      inv := inv₁.same (b8000e0e4_mem_same h₂) (k₂ .x2 (by decide)) (fun _ h ↦ by cases h)
      pc := b8000e0e4_pc h₂
      x8 := by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), hm.x8]
      x20 := by rw [b8000e0e4_x20 h₂, hv]
      o8 := by rw [b8000e0e4_mem_same h₂, b8000dfcc_mem_same h₁, hm.o8, hv]
      o16 := by rw [b8000e0e4_mem_same h₂, b8000dfcc_mem_same h₁, hm.o16, hv] }⟩
  have hnc : 0 < nc s := by
    simp only [nc]
    rcases Nat.eq_zero_or_pos (s.getMem (s.getReg .x11 + 40)).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
    · exact h
  have hC := Region.bounds (cs_region hpre hnc)
  have hnn : nn s = 0 ∨ (s.getReg .x12).toNat + 24 * nn s ≤ 0xc0000000 := by
    rcases hpre.rPrime.region with h | h
    · left; simp only [nn]; omega
    · right; have := Region.bounds h; simp only [nn]; omega
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000dfd0_spec
    (b8000dfcc_pc_not_taken h₁ (by rw [hm.x24]; exact h0)) trivial
  have k₂ := b8000dfd0_keeps h₂
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x21]) : t₂.getReg r = u.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hBuf := hm.bufOk
  refine ⟨t₂, hr₁.trans hr₂, Or.inr {
    x8 := (hreg .x8 (by decide)).trans hm.x8
    x9 := (hreg .x9 (by decide)).trans hm.x9
    x18 := (hreg .x18 (by decide)).trans hm.x18
    x24 := by rw [b8000dfd0_x24 h₂, k₁ .x19 (by decide), hm.x19]
    x25 := by
      rw [b8000dfd0_x25 h₂, k₁ .x21 (by decide), k₁ .x24 (by decide), hm.x21, hm.x24]
      simp only [cp, nc] at hC ⊢
      addr_omega [hC]
    x26 := by
      rw [b8000dfd0_x26 h₂, k₁ .x18 (by decide), k₁ .x26 (by decide), k₁ .x25 (by decide),
        hm.x18, hm.x25, hm.x26]
      by_cases h : nn s = 0
      · simp only [nn] at h ⊢
        have : s.getReg .x13 = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
        rw [this]; simp
      · have hPr := hBuf.range.resolve_left h
        have hfit := hm.inv.fits
        simp only [nn] at hPr ⊢; addr_omega [hPr, hfit]
    inv := inv₁.same (b8000dfd0_mem_same h₂) (k₂ .x2 (by decide)) (fun _ h ↦ by cases h)
    pc := b8000dfd0_pc h₂
    lt := hnc
    x21 := by rw [(hreg .x21 (by decide)), hm.x21]; simp [cp]
    acc := by rw [st_zero, b8000dfd0_x20 h₂, b8000dfd0_x22 h₂, b8000dfd0_x23 h₂]; exact limbs_zero
    buf := fun l hl ↦ by
      have e : eAt t₂ (P + BitVec.ofNat 64 (24 * l)) = eAt u (P + BitVec.ofNat 64 (24 * l)) := by
        simp only [eAt, b8000dfd0_mem_same h₂, b8000dfcc_mem_same h₁]
      rw [e, st_zero]
      have : (eListAt u P (nn s)).getD l 0 = (pt s).getD l 0 := by rw [hm.buf]
      rw [← this, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hl), eListAt_getElem]
    o8 := by rw [b8000dfd0_mem_same h₂, b8000dfcc_mem_same h₁, hm.o8]
    o16 := by rw [b8000dfd0_mem_same h₂, b8000dfcc_mem_same h₁, hm.o16] }⟩

/-! ## The outer loop's head -/

theorem outerHead {s u : MachineState} {nx P : Word} {i : Nat} (hpre : RingEvalPre s)
    (hBuf : BufOk s P nx) (ho : Outer s u nx P i) :
    ∃ v, Reaches Image.code u v ∧ (Inner s v nx P i 0 ∨ (nn s = 0 ∧ Done s v nx P i)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hi := ho.lt
  have hR := cs_region hpre (by omega)
  have hC := Region.bounds hR
  have hsp := ho.inv.sp
  have hx21 := ho.x21
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000e01c_spec ho.pc (by
    rv_eval [hsp, hx21]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hR (by addr_omega [hC, hi]) (by addr_omega [hC, hi])
          (by addr_omega [hC, hi]))
  have k := b8000e01c_keeps h
  have hm := b8000e01c_frame h (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm
  have inv := Inv.step' hpre ho.inv (DFrame.of_memFrame hm)
    (fun a ha ↦ Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb])))
    (fun a ha ↦ by addr_omega [ha, hb])
    ((hm _ (by have := hst.next; simp only [ringEvalStack, mulStack, stackLo] at this; addr_omega [this, hb])).trans
      ho.inv.next) (Nat.le_refl _) ho.inv.fits (k .x2 (by decide))
  -- the coefficient, from `C + 24 i`
  have hcs := coeffs_src hpre
  have hc : eAt t (s.getReg .x2 - 176) = (cs s).getD i 0 := by
    rw [cs_getD s i hi]
    have e : eAt u (cp s + BitVec.ofNat 64 (24 * i)) = eAt s (cp s + BitVec.ofNat 64 (24 * i)) :=
      DFrame.eAt' ho.inv.mem (fun x hx ↦ Inv.src ho.inv hcs.1 hcs.2 x (by
        simp only [cp, nc] at hC hi hx ⊢; addr_omega [hx, hC, hi]))
        (by simp only [cp, nc] at hC hi ⊢; addr_omega [hC, hi])
    rw [← e]
    have m0 := b8000e01c_m_x2_0 h
    have m1 := b8000e01c_m_x2_8 h
    have m2 := b8000e01c_m_x2_16 h
    rw [hsp, hx21] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    unfold eAt
    rv_eval [m0, m1, m2]
  have hmem (a : Word) (h1 : ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 176) 24) :
      t.getMem a = u.getMem a := hm a h1
  have keepE (p : Word) (hp : Apart p 24 (s.getReg .x2 - BitVec.ofNat 64 176) 24)
      (hw : p.toNat + 24 ≤ 2 ^ 64) : eAt t p = eAt u p := hm.eAt hp hw
  have hregs : Regs s t P := {
    x8 := (k .x8 (by decide)).trans ho.x8
    x9 := (k .x9 (by decide)).trans ho.x9
    x18 := (k .x18 (by decide)).trans ho.x18
    x24 := (k .x24 (by decide)).trans ho.x24
    x25 := (k .x25 (by decide)).trans ho.x25
    x26 := (k .x26 (by decide)).trans ho.x26 }
  have hfit := ho.inv.fits
  have o8 : t.getMem (s.getReg .x10 + 8) = 0 := by
    have hO := Region.bounds hpre.out.region
    have hOs := hpre.out.stack
    rw [hmem _ (by addr_omega [hO, hOs, hb])]; exact ho.o8
  have o16 : t.getMem (s.getReg .x10 + 16) = 0 := by
    have hO := Region.bounds hpre.out.region
    have hOs := hpre.out.stack
    rw [hmem _ (by addr_omega [hO, hOs, hb])]; exact ho.o16
  by_cases h0 : s.getReg .x13 = 0
  · have hn0 : nn s = 0 := by simp only [nn, h0]; rfl
    refine ⟨t, hr, Or.inr ⟨hn0, {
      toRegs := hregs
      inv := inv
      pc := b8000e01c_pc_taken h (by rw [ho.x9]; exact h0)
      lt := hi
      x21 := (k .x21 (by decide)).trans hx21
      acc := by rw [k .x20 (by decide), k .x22 (by decide), k .x23 (by decide)]; exact ho.acc
      prod := by rw [hc, hn0]; rfl
      buf := fun l hl ↦ by omega
      o8 := o8
      o16 := o16 }⟩⟩
  · have hBufP := ho.inv.mono
    refine ⟨t, hr, Or.inl {
      toRegs := hregs
      inv := inv
      pc := b8000e01c_pc_not_taken h (by rw [ho.x9]; exact h0)
      lt := hi
      ltj := by
        rcases Nat.eq_zero_or_pos (nn s) with h' | h'
        · exact absurd (BitVec.eq_of_toNat_eq (by simp only [nn] at h'; simpa using h')) h0
        · exact h'
      x21 := (k .x21 (by decide)).trans hx21
      x19 := by rw [b8000e01c_x19 h, ho.x18]; simp
      x27 := by rw [b8000e01c_x27 h, ho.x24]; simp
      acc := by rw [k .x20 (by decide), k .x22 (by decide), k .x23 (by decide)]; exact ho.acc
      prod := by rw [hc]; rfl
      buf := fun l hl ↦ by
        have hPr := hBuf.range.resolve_left (by omega)
        have hab := hst.above
        simp only [Nat.not_lt_zero, ↓reduceIte]
        rw [keepE _ (by addr_omega [hPr, hfit, hab, hb, hl]) (by addr_omega [hPr, hfit, hl])]
        exact ho.buf l hl
      o8 := o8
      o16 := o16 }⟩

end Rv64Verifier.Proofs.Pcs.RingEval
