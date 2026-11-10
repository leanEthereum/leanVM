import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Model.FieldAlg
import Rv64Verifier.Blocks.F33

/-!
# `Scaler::new`: the table fill

`Scaled::new`'s four nested loops as compiled in `Scaler::new` (`Blocks/F33.lean`), each a lemma
taking its loop from head to exit and saying it computes its fold in `Model/FieldAlg.lean`:
`low_loop` (`0x80008b30`, `fillBit`), `bit_loop` (`0x80008b24`, `fillTable`), `table_loop`
(`0x80008b1c`, `fillLimb`) and `limb_loop` (`0x80008b04`, `scaledTable`). The buffer `P` holds
`2112` entries (`tab`); the fill writes nothing else (`Ctx`, relative to the state `t₀` before
it).
-/

namespace Rv64Verifier.Proofs.Multilinear.ScalerFill
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.MultilinearWords
  Rv64Verifier.Model Rv64Verifier.Blocks.F33
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The table's bytes. -/
@[rv_addr] def tabBytes : Nat := 24 * 2112

/-- The buffer: aligned, in the heap. -/
structure BufP (P : Word) : Prop where
  align : P.toNat % 8 = 0
  lo : 0x20 ≤ P.toNat
  hi : P.toNat + tabBytes ≤ heapEnd

/-- The entries of the table at `P`, as limbs. -/
def tab (u : MachineState) (P : Word) : List Limbs :=
  (List.range 2112).map fun i ↦ limbs (eAt u (P + BitVec.ofNat 64 (24 * i)))

theorem tab_length (u : MachineState) (P : Word) : (tab u P).length = 2112 := by simp [tab]

theorem tab_getD (u : MachineState) (P : Word) {i : Nat} (hi : i < 2112) :
    (tab u P).getD i lzero = limbs (eAt u (P + BitVec.ofNat 64 (24 * i))) := by
  simp [tab, List.getD_eq_getElem?_getD, hi]

/-- Writing entry `idx` sets it. -/
theorem tab_set {u v : MachineState} {P : Word} (hP : BufP P) {idx : Nat} (hidx : idx < 2112)
    (hfr : MemFrame u v (P + BitVec.ofNat 64 (24 * idx)) 24) :
    tab v P = (tab u P).set idx (limbs (eAt v (P + BitVec.ofNat 64 (24 * idx)))) := by
  have h1 := hP.hi
  have h2 := hP.lo
  apply List.ext_getElem (by simp [tab_length])
  intro i hi₁ hi₂
  rw [tab_length] at hi₁
  rw [List.getElem_set]
  split
  · subst idx; simp [tab]
  · rename_i hne
    simp only [tab, List.getElem_map, List.getElem_range]
    rw [hfr.eAt (by addr_omega [hi₁, hidx, hne, h1, h2]) (by addr_omega [hi₁, h1, h2])]

/-- What the fill keeps: `sp`, the result's address, `ra`, `s10`, `s11`, and memory outside the
table, unaligned addresses included. -/
structure Ctx (t₀ u : MachineState) (P : Word) : Prop where
  regs : ∀ r ∈ [Reg.x1, .x2, .x8, .x26, .x27], u.getReg r = t₀.getReg r
  mem : MemFrame t₀ u P tabBytes
  una : ∀ a, a.toNat % 8 ≠ 0 → u.getMem a = t₀.getMem a

theorem Ctx.same {t₀ u v : MachineState} {P : Word} (h : Ctx t₀ u P)
    (hm : ∀ a, v.getMem a = u.getMem a) (hr : ∀ r ∈ [Reg.x1, .x2, .x8, .x26, .x27],
      v.getReg r = u.getReg r) : Ctx t₀ v P :=
  ⟨fun r h' ↦ (hr r h').trans (h.regs r h'), fun a ha ↦ (hm a).trans (h.mem a ha),
    fun a ha ↦ (hm a).trans (h.una a ha)⟩

theorem idx_nat {b k : Nat} (hk : k < 2 ^ b) : (1 <<< b ||| k) = 2 ^ b + k := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hk, Nat.one_shiftLeft]

theorem or_idx : ∀ b, b < 6 → ∀ k, k < 2 ^ b →
    (BitVec.ofNat 64 k ||| BitVec.ofNat 64 (2 ^ b)) = BitVec.ofNat 64 (2 ^ b + k) := by decide

theorem heap_valid' {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + 8 ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : Sym.validAccess 8 a = true := by
  rw [Sym.validAccess_eight]
  simp only [heapEnd] at h2
  omega

/-! ## `for low in 0..1 << bit` (`0x80008b30`) -/

/-- The registers the low loop keeps. -/
def lowKeep : List Reg := [.x1, .x2, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
  .x16, .x17, .x18, .x26, .x27, .x28, .x29, .x30, .x31]

structure LowInv (t₀ u₀ u : MachineState) (P : Word) (base b : Nat) (T0 : List Limbs) (k : Nat) :
    Prop where
  ctx : Ctx t₀ u P
  pc : u.pc = 0x80008b30
  keep : ∀ r ∈ lowKeep, u.getReg r = u₀.getReg r
  lt : k < 2 ^ b
  x19 : u.getReg .x19 = P + BitVec.ofNat 64 (24 * (base + k)) + 16
  x20 : u.getReg .x20 = BitVec.ofNat 64 k
  tab : tab u P = (List.range k).foldl
    (fillStep base b (u₀.getReg .x30, u₀.getReg .x29, u₀.getReg .x28)) T0

def lowMeasure (u : MachineState) : Nat := (u.getReg .x18).toNat - (u.getReg .x20).toNat

theorem low_loop {t₀ u₀ : MachineState} {P : Word} (hP : BufP P) {base b : Nat} (hb : b < 6)
    (hbase : base + 2 * 2 ^ b ≤ 2112) {T0 : List Limbs}
    (hx9 : u₀.getReg .x9 = P + BitVec.ofNat 64 (24 * base))
    (hx18 : u₀.getReg .x18 = BitVec.ofNat 64 (2 ^ b)) (h₀ : LowInv t₀ u₀ u₀ P base b T0 0) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x80008b78 ∧ Ctx t₀ v P ∧
      (∀ r ∈ lowKeep, v.getReg r = u₀.getReg r) ∧
      tab v P = fillBit base b (u₀.getReg .x30, u₀.getReg .x29, u₀.getReg .x28) T0 := by
  have h1 := hP.hi
  have h2 := hP.lo
  have h3 := hP.align
  have hpow : 2 ^ b ≤ 32 := by
    have : 2 ^ b ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  obtain ⟨v, hr, hv⟩ := Reaches.loop (code := Image.code) (fun u ↦ ∃ k, LowInv t₀ u₀ u P base b T0 k)
    lowMeasure (fun v ↦ v.pc = 0x80008b78 ∧ Ctx t₀ v P ∧
      (∀ r ∈ lowKeep, v.getReg r = u₀.getReg r) ∧
      tab v P = fillBit base b (u₀.getReg .x30, u₀.getReg .x29, u₀.getReg .x28) T0)
    (fun u ⟨k, hu⟩ ↦ by
      have hk := hu.lt
      have u9 : u.getReg .x9 = P + BitVec.ofNat 64 (24 * base) :=
        (hu.keep .x9 (by decide)).trans hx9
      have u18 : u.getReg .x18 = BitVec.ofNat 64 (2 ^ b) := (hu.keep .x18 (by decide)).trans hx18
      have hor : (u.getReg .x20 ||| u.getReg .x18) = BitVec.ofNat 64 (2 ^ b + k) := by
        rw [hu.x20, u18]; exact or_idx b hb k hk
      obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b80008b30_spec hu.pc (by
        rv_eval [hor, u9, hu.x19]
        and_intros <;> exact heap_valid' (by addr_omega [hk, hbase, hpow, h1, h2])
          (by addr_omega [hk, hbase, hpow, h1, h2]) (by addr_omega [hk, hbase, hpow, h1, h2, h3]))
      have k₁ := b80008b30_keeps h
      have m₀ := h.memAt 0 (by decide)
      have m₁ := h.memAt 1 (by decide)
      have m₂ := h.memAt 2 (by decide)
      rv_eval [hor, u9, hu.x19] at m₀ m₁ m₂
      have hidx : P + BitVec.ofNat 64 (24 * base) +
          (BitVec.ofNat 64 (2 ^ b + k) * 16 + BitVec.ofNat 64 (2 ^ b + k) * 8) =
          P + BitVec.ofNat 64 (24 * (base + (2 ^ b + k))) := by
        addr_omega [hk, hbase, hpow, h1, h2]
      have hsrc : P + BitVec.ofNat 64 (24 * (base + k)) + 16 - 16 =
          P + BitVec.ofNat 64 (24 * (base + k)) := by addr_omega [hk, hbase, hpow, h1, h2]
      rw [hidx] at m₀ m₁ m₂
      have hfr : MemFrame u v (P + BitVec.ofNat 64 (24 * (base + (2 ^ b + k)))) 24 := by
        intro a ha
        refine h.frame a ?_
        rv_eval [hor, u9, hu.x19]
        rw [hidx]
        and_intros <;> intro heq <;> apply ha <;> rw [heq] <;>
          addr_omega [hk, hbase, hpow, h1, h2]
      have hT := tab_set hP (by omega) hfr
      have hnew : limbs (eAt v (P + BitVec.ofNat 64 (24 * (base + (2 ^ b + k))))) =
          ladd ((tab u P).getD (base + k) lzero)
            (u₀.getReg .x30, u₀.getReg .x29, u₀.getReg .x28) := by
        rw [tab_getD u P (by omega), limbs_eAt, limbs_eAt, m₀, m₁, m₂, ladd,
          ← hu.keep .x30 (by decide), ← hu.keep .x29 (by decide), ← hu.keep .x28 (by decide)]
      have hstep : tab v P = (List.range (k + 1)).foldl
          (fillStep base b (u₀.getReg .x30, u₀.getReg .x29, u₀.getReg .x28)) T0 := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hu.tab,
          fillStep, idx_nat hk, hT, hnew]
      have hctx : Ctx t₀ v P := {
        regs := fun r hr' ↦ (k₁ r (Runtime.mem_of_mem hr' _)).trans (hu.ctx.regs r hr')
        mem := fun a ha ↦ (hfr a (by addr_omega [ha, hk, hbase, hpow, h1, h2])).trans
          (hu.ctx.mem a ha)
        una := fun a ha ↦ (h.unaligned (by
          rv_eval [hor, u9, hu.x19]; rw [hidx]
          and_intros <;> addr_omega [hk, hbase, hpow, h1, h2, h3]) a ha).trans (hu.ctx.una a ha) }
      have hkeep (r : Reg) (hr' : r ∈ lowKeep) : v.getReg r = u₀.getReg r :=
        (k₁ r (Runtime.mem_of_mem hr' _)).trans (hu.keep r hr')
      have hx20 : v.getReg .x20 = BitVec.ofNat 64 (k + 1) := by
        rw [b80008b30_x20 h, hu.x20]; addr_omega [hk, hpow]
      by_cases hlast : k + 1 = 2 ^ b
      · refine Or.inl ⟨v, hr, b80008b30_pc_not_taken h (by rw [u18, hu.x20]; addr_omega [hlast, hpow]),
          hctx, hkeep, ?_⟩
        rw [hstep, fillBit, show 1 <<< b = 2 ^ b from Nat.one_shiftLeft b, hlast]
      · refine Or.inr ⟨v, hr, ⟨k + 1, {
          ctx := hctx
          pc := b80008b30_pc_taken h (by rw [u18, hu.x20]; addr_omega [hlast, hk, hpow])
          keep := hkeep
          lt := by omega
          x19 := by rw [b80008b30_x19 h, hu.x19]; addr_omega [hk, hbase, hpow, h1, h2]
          x20 := hx20
          tab := hstep }⟩, ?_⟩
        simp only [lowMeasure]
        rw [hkeep .x18 (by decide), hx18, hx20, hu.x20, u18]
        addr_omega [hk, hpow, hlast]) u₀ ⟨0, h₀⟩
  exact ⟨v, hr, hv⟩

/-! ## `for bit in 0..WINDOW` (`0x80008b24`) -/

theorem sshift63 (x : BitVec 64) : x.sshiftRight 63 = if x.msb then BitVec.allOnes 64 else 0 := by
  have hm : x.msb = x[63] := by simp [BitVec.msb_eq_getLsbD_last]
  by_cases hb : x.msb
  · simp only [hb, ↓reduceIte]
    ext i hi
    rw [BitVec.getElem_sshiftRight, BitVec.getElem_allOnes]
    split
    · have : i = 0 := by omega
      subst this
      rw [← hm]; exact hb
    · exact hb
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    ext i hi
    rw [BitVec.getElem_sshiftRight]
    split
    · have : i = 0 := by omega
      subst this
      simp [← hm, hb]
    · simp [hb]

theorem ushr63 (x : BitVec 64) : x >>> 63 = if x.msb then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide]
  have := x.isLt
  split <;> rename_i h <;> simp at h <;> simp [Nat.shiftRight_eq_div_pow] <;> omega

/-- The compiled `times_x`. -/
theorem timesX_sra (x : BitVec 64) :
    (x.sshiftRight 63 &&& (27 : BitVec 64) ^^^ x * (2 : BitVec 64)) = timesX x := by
  have h2 : x * (2 : BitVec 64) = x <<< 1 := by rw [Sym.shiftLeft_eq_mul]; rfl
  rw [timesX, sshift63, ushr63, h2, BitVec.xor_comm]
  by_cases hb : x.msb
  · simp only [hb, ↓reduceIte]; rfl
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]; rfl

/-- One iteration of `fillTable`'s fold. -/
def bitStep (base : Nat) (st : List Limbs × Limbs) (bit : Nat) : List Limbs × Limbs :=
  (fillBit base bit st.2 st.1, ltimesX st.2)

def bitKeep : List Reg := [.x1, .x2, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14,
  .x15, .x16, .x17, .x26, .x27]

def pwOf (u : MachineState) : Limbs := (u.getReg .x30, u.getReg .x29, u.getReg .x28)

structure BitInv (t₀ u₀ u : MachineState) (P : Word) (base : Nat) (st₀ : List Limbs × Limbs)
    (b : Nat) : Prop where
  ctx : Ctx t₀ u P
  pc : u.pc = 0x80008b24
  keep : ∀ r ∈ bitKeep, u.getReg r = u₀.getReg r
  lt : b < 6
  x31 : u.getReg .x31 = BitVec.ofNat 64 b
  st : (tab u P, pwOf u) = (List.range b).foldl (bitStep base) st₀

def bitMeasure (u : MachineState) : Nat := (u.getReg .x14).toNat - (u.getReg .x31).toNat

theorem bit_loop {t₀ u₀ : MachineState} {P : Word} (hP : BufP P) {base : Nat}
    (hbase : base + 64 ≤ 2112) {st₀ : List Limbs × Limbs}
    (hx9 : u₀.getReg .x9 = P + BitVec.ofNat 64 (24 * base))
    (hx7 : u₀.getReg .x7 = P + BitVec.ofNat 64 (24 * base) + 16)
    (hx12 : u₀.getReg .x12 = 1) (hx14 : u₀.getReg .x14 = 6)
    (h₀ : BitInv t₀ u₀ u₀ P base st₀ 0) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x80008bb0 ∧ Ctx t₀ v P ∧
      (∀ r ∈ bitKeep, v.getReg r = u₀.getReg r) ∧ (tab v P, pwOf v) = fillTable base st₀ := by
  have h1 := hP.hi
  have h2 := hP.lo
  obtain ⟨v, hr, hv⟩ := Reaches.loop (code := Image.code)
    (fun u ↦ ∃ b, BitInv t₀ u₀ u P base st₀ b) bitMeasure
    (fun v ↦ v.pc = 0x80008bb0 ∧ Ctx t₀ v P ∧ (∀ r ∈ bitKeep, v.getReg r = u₀.getReg r) ∧
      (tab v P, pwOf v) = fillTable base st₀)
    (fun u ⟨b, hu⟩ ↦ by
      have hb := hu.lt
      obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008b24_spec hu.pc trivial
      have k₁ := b80008b24_keeps h₁
      have w18 : w.getReg .x18 = BitVec.ofNat 64 (2 ^ b) := by
        rw [h₁.reg .x18 rfl]
        rv_eval [hu.keep .x12 (by decide), hx12, hu.x31]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega),
          Nat.mod_eq_of_lt (a := b) (by omega)]
        exact one_mul _
      have hlow : LowInv t₀ w w P base b (tab w P) 0 := {
        ctx := hu.ctx.same (b80008b24_mem_same h₁) fun r hr' ↦ k₁ r (Runtime.mem_of_mem hr' _)
        pc := b80008b24_pc h₁
        keep := fun _ _ ↦ rfl
        lt := Nat.two_pow_pos b
        x19 := by
          rw [b80008b24_x19 h₁, hu.keep .x7 (by decide), hx7, Nat.add_zero]
        x20 := by rw [b80008b24_x20 h₁]; rfl
        tab := by rw [List.range_zero, List.foldl_nil] }
      have hw9 : w.getReg .x9 = P + BitVec.ofNat 64 (24 * base) := by
        rw [k₁ .x9 (by decide), hu.keep .x9 (by decide), hx9]
      have hpow : 2 * 2 ^ b ≤ 64 := by
        have : 2 ^ b ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp at this; omega
      obtain ⟨v, hr₂, hpc₂, hctx₂, hkeep₂, htab₂⟩ :=
        low_loop hP hb (by omega) hw9 w18 hlow
      have hpw : pwOf w = pwOf u := by
        simp only [pwOf, k₁ .x28 (by decide), k₁ .x29 (by decide), k₁ .x30 (by decide)]
      obtain ⟨v', hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008b78_spec hpc₂ trivial
      have k₃ := b80008b78_keeps h₃
      have v28 := h₃.reg .x28 rfl
      have v29 := h₃.reg .x29 rfl
      have v30 := h₃.reg .x30 rfl
      rv_eval [timesX_sra] at v28 v29 v30
      have hst : (tab v' P, pwOf v') = (List.range (b + 1)).foldl (bitStep base) st₀ := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hu.st, bitStep]
        simp only [Prod.mk.injEq]
        have htv : tab v' P = tab v P := by simp only [tab, eAt, b80008b78_mem_same h₃]
        have htw : tab w P = tab u P := by simp only [tab, eAt, b80008b24_mem_same h₁]
        refine ⟨?_, ?_⟩
        · rw [htv, htab₂, htw, show (w.getReg .x30, w.getReg .x29, w.getReg .x28) = pwOf w from rfl,
            hpw]
        · simp only [pwOf, v28, v29, v30, ltimesX, hkeep₂ .x28 (by decide),
            hkeep₂ .x29 (by decide), hkeep₂ .x30 (by decide), k₁ .x28 (by decide),
            k₁ .x29 (by decide), k₁ .x30 (by decide)]
      have hctx : Ctx t₀ v' P := hctx₂.same (b80008b78_mem_same h₃)
        fun r hr' ↦ k₃ r (Runtime.mem_of_mem hr' _)
      have hkeep (r : Reg) (hr' : r ∈ bitKeep) : v'.getReg r = u₀.getReg r := by
        rw [k₃ r (Runtime.mem_of_mem hr' _), hkeep₂ r (Runtime.mem_of_mem hr' _),
          k₁ r (Runtime.mem_of_mem hr' _), hu.keep r hr']
      have v14 : v.getReg .x14 = 6 := by
        rw [hkeep₂ .x14 (by decide), k₁ .x14 (by decide), hu.keep .x14 (by decide), hx14]
      have v31 : v.getReg .x31 = BitVec.ofNat 64 b := by
        rw [hkeep₂ .x31 (by decide), k₁ .x31 (by decide), hu.x31]
      have hreach := hr₁.trans (hr₂.trans hr₃)
      by_cases hlast : b + 1 = 6
      · refine Or.inl ⟨v', hreach, b80008b78_pc_not_taken h₃ (by rw [v14, v31]; addr_omega [hlast]),
          hctx, hkeep, ?_⟩
        rw [hst, hlast]
        rfl
      · refine Or.inr ⟨v', hreach, ⟨b + 1, {
          ctx := hctx
          pc := b80008b78_pc_taken h₃ (by rw [v14, v31]; addr_omega [hlast, hb])
          keep := hkeep
          lt := by omega
          x31 := by rw [b80008b78_x31 h₃, v31]; addr_omega [hb]
          st := hst }⟩, ?_⟩
        simp only [bitMeasure]
        rw [hkeep .x14 (by decide), hx14, b80008b78_x31 h₃, v31, hu.x31, hu.keep .x14 (by decide),
          hx14]
        addr_omega [hb]) u₀ ⟨0, h₀⟩
  exact ⟨v, hr, hv⟩

/-! ## `for table in limb_tables` (`0x80008b1c`) -/

def tabStep (t : Nat) (st : List Limbs × Limbs) (j : Nat) : List Limbs × Limbs :=
  fillTable ((t * 11 + j) * 64) st

def tabKeep : List Reg := [.x1, .x2, .x5, .x8, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
  .x26, .x27]

structure TabInv (t₀ u₀ u : MachineState) (P : Word) (t : Nat) (st₀ : List Limbs × Limbs)
    (j : Nat) : Prop where
  ctx : Ctx t₀ u P
  pc : u.pc = 0x80008b1c
  keep : ∀ r ∈ tabKeep, u.getReg r = u₀.getReg r
  lt : j < 11
  x6 : u.getReg .x6 = BitVec.ofNat 64 (1536 * j)
  x7 : u.getReg .x7 = P + BitVec.ofNat 64 (24 * ((t * 11 + j) * 64)) + 16
  st : (tab u P, pwOf u) = (List.range j).foldl (tabStep t) st₀

def tabMeasure (u : MachineState) : Nat := (u.getReg .x17).toNat - (u.getReg .x6).toNat

theorem table_loop {t₀ u₀ : MachineState} {P : Word} (hP : BufP P) {t : Nat} (ht : t < 3)
    {st₀ : List Limbs × Limbs}
    (hx10 : u₀.getReg .x10 = P + BitVec.ofNat 64 (24 * (t * 11 * 64)))
    (hx12 : u₀.getReg .x12 = 1) (hx14 : u₀.getReg .x14 = 6) (hx17 : u₀.getReg .x17 = 16896)
    (h₀ : TabInv t₀ u₀ u₀ P t st₀ 0) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x80008bbc ∧ Ctx t₀ v P ∧
      (∀ r ∈ tabKeep, v.getReg r = u₀.getReg r) ∧ (tab v P, pwOf v) = fillLimb t st₀ := by
  have h1 := hP.hi
  have h2 := hP.lo
  obtain ⟨v, hr, hv⟩ := Reaches.loop (code := Image.code)
    (fun u ↦ ∃ j, TabInv t₀ u₀ u P t st₀ j) tabMeasure
    (fun v ↦ v.pc = 0x80008bbc ∧ Ctx t₀ v P ∧ (∀ r ∈ tabKeep, v.getReg r = u₀.getReg r) ∧
      (tab v P, pwOf v) = fillLimb t st₀)
    (fun u ⟨j, hu⟩ ↦ by
      have hj := hu.lt
      obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008b1c_spec hu.pc trivial
      have k₁ := b80008b1c_keeps h₁
      have hw9 : w.getReg .x9 = P + BitVec.ofNat 64 (24 * ((t * 11 + j) * 64)) := by
        rw [b80008b1c_x9 h₁, hu.keep .x10 (by decide), hx10, hu.x6]
        addr_omega [ht, hj, h1, h2]
      have hw7 : w.getReg .x7 = P + BitVec.ofNat 64 (24 * ((t * 11 + j) * 64)) + 16 := by
        rw [k₁ .x7 (by decide), hu.x7]
      have hbit : BitInv t₀ w w P ((t * 11 + j) * 64) (tab w P, pwOf w) 0 := {
        ctx := hu.ctx.same (b80008b1c_mem_same h₁) fun r hr' ↦ k₁ r (Runtime.mem_of_mem hr' _)
        pc := b80008b1c_pc h₁
        keep := fun _ _ ↦ rfl
        lt := by decide
        x31 := by rw [b80008b1c_x31 h₁]; rfl
        st := by rw [List.range_zero, List.foldl_nil] }
      obtain ⟨v, hr₂, hpc₂, hctx₂, hkeep₂, hst₂⟩ := bit_loop hP (by omega) hw9 hw7
        (by rw [k₁ .x12 (by decide), hu.keep .x12 (by decide), hx12])
        (by rw [k₁ .x14 (by decide), hu.keep .x14 (by decide), hx14]) hbit
      have htw : (tab w P, pwOf w) = (tab u P, pwOf u) := by
        simp only [tab, eAt, b80008b1c_mem_same h₁, pwOf, k₁ .x28 (by decide),
          k₁ .x29 (by decide), k₁ .x30 (by decide)]
      obtain ⟨v', hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008bb0_spec hpc₂ trivial
      have k₃ := b80008bb0_keeps h₃
      have hst : (tab v' P, pwOf v') = (List.range (j + 1)).foldl (tabStep t) st₀ := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hu.st, tabStep,
          ← htw, ← hst₂]
        simp only [tab, eAt, b80008bb0_mem_same h₃, pwOf, k₃ .x28 (by decide),
          k₃ .x29 (by decide), k₃ .x30 (by decide)]
      have hctx : Ctx t₀ v' P := hctx₂.same (b80008bb0_mem_same h₃)
        fun r hr' ↦ k₃ r (Runtime.mem_of_mem hr' _)
      have hkeep (r : Reg) (hr' : r ∈ tabKeep) : v'.getReg r = u₀.getReg r := by
        rw [k₃ r (Runtime.mem_of_mem hr' _), hkeep₂ r (Runtime.mem_of_mem hr' _),
          k₁ r (Runtime.mem_of_mem hr' _), hu.keep r hr']
      have v6 : v.getReg .x6 = BitVec.ofNat 64 (1536 * j) := by
        rw [hkeep₂ .x6 (by decide), k₁ .x6 (by decide), hu.x6]
      have v7 : v.getReg .x7 = P + BitVec.ofNat 64 (24 * ((t * 11 + j) * 64)) + 16 := by
        rw [hkeep₂ .x7 (by decide), hw7]
      have v17 : v.getReg .x17 = 16896 := by
        rw [hkeep₂ .x17 (by decide), k₁ .x17 (by decide), hu.keep .x17 (by decide), hx17]
      have hreach := hr₁.trans (hr₂.trans hr₃)
      by_cases hlast : j + 1 = 11
      · refine Or.inl ⟨v', hreach, b80008bb0_pc_not_taken h₃ (by rw [v6, v17]; addr_omega [hlast]),
          hctx, hkeep, ?_⟩
        rw [hst, hlast]
        rfl
      · refine Or.inr ⟨v', hreach, ⟨j + 1, {
          ctx := hctx
          pc := b80008bb0_pc_taken h₃ (by rw [v6, v17]; addr_omega [hlast, hj])
          keep := hkeep
          lt := by omega
          x6 := by rw [b80008bb0_x6 h₃, v6]; addr_omega [hj]
          x7 := by rw [b80008bb0_x7 h₃, v7]; addr_omega [hj, ht, h1, h2]
          st := hst }⟩, ?_⟩
        simp only [tabMeasure]
        rw [hkeep .x17 (by decide), hx17, b80008bb0_x6 h₃, v6, hu.x6, hu.keep .x17 (by decide),
          hx17]
        addr_omega [hj]) u₀ ⟨0, h₀⟩
  exact ⟨v, hr, hv⟩

/-! ## `for limb_tables in tables` (`0x80008b04`) -/

def limbStep (st : List Limbs × Limbs) (t : Nat) : List Limbs × Limbs :=
  ((fillLimb t (st.1, st.2)).1, ltimesY st.2)

def limbKeep : List Reg := [.x1, .x2, .x8, .x12, .x14, .x16, .x17, .x26, .x27]

def monoOf (u : MachineState) : Limbs := (u.getReg .x13, u.getReg .x7, u.getReg .x11)

structure LimbInv (t₀ u₀ u : MachineState) (P : Word) (R : Limbs) (t : Nat) : Prop where
  ctx : Ctx t₀ u P
  pc : u.pc = 0x80008b04
  keep : ∀ r ∈ limbKeep, u.getReg r = u₀.getReg r
  lt : t < 3
  x10 : u.getReg .x10 = P + BitVec.ofNat 64 (24 * (t * 11 * 64))
  x15 : u.getReg .x15 = P + BitVec.ofNat 64 (24 * (t * 11 * 64)) + 16
  st : (tab u P, monoOf u) =
    (List.range t).foldl limbStep (List.replicate ((3 * 11) <<< 6) lzero, R)

def limbMeasure (u : MachineState) : Nat := (u.getReg .x16).toNat - (u.getReg .x10).toNat

theorem limb_loop {t₀ u₀ : MachineState} {P : Word} (hP : BufP P) {R : Limbs}
    (hx12 : u₀.getReg .x12 = 1) (hx14 : u₀.getReg .x14 = 6) (hx17 : u₀.getReg .x17 = 16896)
    (hx16 : u₀.getReg .x16 = P + BitVec.ofNat 64 tabBytes)
    (h₀ : LimbInv t₀ u₀ u₀ P R 0) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x80008bd4 ∧ Ctx t₀ v P ∧
      (∀ r ∈ limbKeep, v.getReg r = u₀.getReg r) ∧ tab v P = scaledTable R := by
  have h1 := hP.hi
  have h2 := hP.lo
  obtain ⟨v, hr, hv⟩ := Reaches.loop (code := Image.code)
    (fun u ↦ ∃ t, LimbInv t₀ u₀ u P R t) limbMeasure
    (fun v ↦ v.pc = 0x80008bd4 ∧ Ctx t₀ v P ∧ (∀ r ∈ limbKeep, v.getReg r = u₀.getReg r) ∧
      tab v P = scaledTable R)
    (fun u ⟨t, hu⟩ ↦ by
      have ht := hu.lt
      obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008b04_spec hu.pc trivial
      have k₁ := b80008b04_keeps h₁
      have htab : TabInv t₀ w w P t (tab w P, pwOf w) 0 := {
        ctx := hu.ctx.same (b80008b04_mem_same h₁) fun r hr' ↦ k₁ r (Runtime.mem_of_mem hr' _)
        pc := b80008b04_pc h₁
        keep := fun _ _ ↦ rfl
        lt := by decide
        x6 := by rw [b80008b04_x6 h₁]; rfl
        x7 := by rw [b80008b04_x7 h₁, hu.x15, Nat.add_zero]
        st := by rw [List.range_zero, List.foldl_nil] }
      obtain ⟨v, hr₂, hpc₂, hctx₂, hkeep₂, hst₂⟩ := table_loop hP ht
        (by rw [k₁ .x10 (by decide), hu.x10])
        (by rw [k₁ .x12 (by decide), hu.keep .x12 (by decide), hx12])
        (by rw [k₁ .x14 (by decide), hu.keep .x14 (by decide), hx14])
        (by rw [k₁ .x17 (by decide), hu.keep .x17 (by decide), hx17]) htab
      have htw : (tab w P, pwOf w) = (tab u P, monoOf u) := by
        simp only [tab, eAt, b80008b04_mem_same h₁, pwOf, monoOf, b80008b04_x28 h₁,
          b80008b04_x29 h₁, b80008b04_x30 h₁]
      obtain ⟨v', hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008bbc_spec hpc₂ trivial
      have k₃ := b80008bbc_keeps h₃
      have hv5 : v.getReg .x5 = u.getReg .x7 := by
        rw [hkeep₂ .x5 (by decide), b80008b04_x5 h₁]
      have hv11 : v.getReg .x11 = u.getReg .x11 := by
        rw [hkeep₂ .x11 (by decide), k₁ .x11 (by decide)]
      have hv13 : v.getReg .x13 = u.getReg .x13 := by
        rw [hkeep₂ .x13 (by decide), k₁ .x13 (by decide)]
      have hst : (tab v' P, monoOf v') =
          (List.range (t + 1)).foldl limbStep (List.replicate ((3 * 11) <<< 6) lzero, R) := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hu.st, limbStep,
          ← htw, ← hst₂]
        simp only [tab, eAt, b80008bbc_mem_same h₃, monoOf, pwOf, ltimesY, b80008bbc_x7 h₃,
          b80008bbc_x11 h₃, b80008bbc_x13 h₃, hv5, hv11, hv13, b80008b04_x28 h₁,
          b80008b04_x29 h₁, b80008b04_x30 h₁, Prod.mk.injEq, true_and]
        exact ⟨BitVec.xor_comm _ _, trivial⟩
      have hctx : Ctx t₀ v' P := hctx₂.same (b80008bbc_mem_same h₃)
        fun r hr' ↦ k₃ r (Runtime.mem_of_mem hr' _)
      have hkeep (r : Reg) (hr' : r ∈ limbKeep) : v'.getReg r = u₀.getReg r := by
        rw [k₃ r (Runtime.mem_of_mem hr' _), hkeep₂ r (Runtime.mem_of_mem hr' _),
          k₁ r (Runtime.mem_of_mem hr' _), hu.keep r hr']
      have v10 : v.getReg .x10 = P + BitVec.ofNat 64 (24 * (t * 11 * 64)) := by
        rw [hkeep₂ .x10 (by decide), k₁ .x10 (by decide), hu.x10]
      have v15 : v.getReg .x15 = P + BitVec.ofNat 64 (24 * (t * 11 * 64)) + 16 := by
        rw [hkeep₂ .x15 (by decide), k₁ .x15 (by decide), hu.x15]
      have v16 : v.getReg .x16 = P + BitVec.ofNat 64 tabBytes := by
        rw [hkeep₂ .x16 (by decide), k₁ .x16 (by decide), hu.keep .x16 (by decide), hx16]
      have v17 : v.getReg .x17 = 16896 := by
        rw [hkeep₂ .x17 (by decide), k₁ .x17 (by decide), hu.keep .x17 (by decide), hx17]
      have hreach := hr₁.trans (hr₂.trans hr₃)
      by_cases hlast : t + 1 = 3
      · refine Or.inl ⟨v', hreach,
          b80008bbc_pc_not_taken h₃ (by rw [v10, v17, v16]; addr_omega [hlast, h1, h2]),
          hctx, hkeep, ?_⟩
        have := congrArg Prod.fst hst
        simp only at this
        rw [this, hlast]
        rfl
      · refine Or.inr ⟨v', hreach, ⟨t + 1, {
          ctx := hctx
          pc := b80008bbc_pc_taken h₃ (by rw [v10, v17, v16]; addr_omega [hlast, ht, h1, h2])
          keep := hkeep
          lt := by omega
          x10 := by rw [b80008bbc_x10 h₃, v10, v17]; addr_omega [ht, h1, h2]
          x15 := by rw [b80008bbc_x15 h₃, v15, v17]; addr_omega [ht, h1, h2]
          st := hst }⟩, ?_⟩
        simp only [limbMeasure]
        rw [hkeep .x16 (by decide), hx16, b80008bbc_x10 h₃, v10, v17, hu.x10,
          hu.keep .x16 (by decide), hx16]
        addr_omega [ht, h1, h2]) u₀ ⟨0, h₀⟩
  exact ⟨v, hr, hv⟩

end Rv64Verifier.Proofs.Multilinear.ScalerFill
