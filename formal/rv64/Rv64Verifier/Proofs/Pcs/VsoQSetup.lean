import Rv64Verifier.Proofs.Pcs.VsoGrind

/-!
# `verify_stacked_opening`'s level loop: the queries' setup

`0x8000a82c` bounds the level by the queries' table (`config.queries[level]`, a panic past it),
`0x8000a83c` takes the depth `d = (message_log + rate) & 63` (a panic on `0`), `0x8000a854` reads the
level's count `cnt` and allocates the `Vec<u64>` of the positions (`try_allocate_in(S - 384, cnt, 0,
8, 8)`, at `S - 464`); with `cnt = 0` it goes on at `0x8000a9d8`, else `0x8000a8a8` sets the mask,
`-d` and `192 / d` up for `sample_queries`' loop at `0x8000a8dc`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- `try_allocate_in(S - 384, a1, _, 8, 8)`: a buffer of `a1` words. -/
theorem callTryAlloc8 (hT : TryAllocZeroedSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800049ac) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 384) (hx13 : t.getReg .x13 = 8)
    (hx14 : t.getReg .x14 = 8) (hheap : HeapOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      (v.getMem (s.getReg .x2 - 384) = 0 → v.getMem (s.getReg .x2 - 376) = t.getReg .x11 ∧
        NewBuf t v (v.getMem (s.getReg .x2 - 368)) ((t.getReg .x11).toNat * 8) 8) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
        Within a nextAddr 8 ∨ Fresh t v a)) := by
  have hst := hpre.stack
  have hb := bounds hpre
  have hsl : stackLo t tryAllocStack = s.getReg .x2 - 1088 := by
    simp only [stackLo, tryAllocStack, hsp]; rv_eval []
  have hnx := hst.next
  have hab := hst.above
  simp only [vso_stack] at hnx hab
  have hpreT : TryAllocPre .x13 .x14 t := {
    heap := hheap
    out := by rw [hx10]; valid_sub hst.valid [hb]
    align := by rw [hx13]; decide
    size := by rw [hx14]; decide
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx, hb]⟩
    outStack := by rw [hx10, hsl]; addr_omega [hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, -⟩ | hdead⟩ := hT.call (Reaches.refl t) hpc hpreT
  · have hok := hpost.ok
    have hfr := DFrame.of_byteFrame hpost.frame
    rw [hx10, hx14, hx13] at hok
    rw [hx10, hsl] at hfr
    refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, fun h0 ↦ ?_, hfr⟩⟩
    obtain ⟨h1, h2⟩ := hok h0
    rw [show s.getReg .x2 - 384 + 8 = s.getReg .x2 - 376 by rv_eval []] at h1
    rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by rv_eval [],
      show (8 : Word).toNat = 8 from rfl] at h2
    exact ⟨h1, h2⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-! ## The setup -/

theorem mask_eq {d : ℕ} (hd : d < 64) :
    (18446744073709551615 : BitVec 64) * BitVec.ofNat 64 (2 ^ d) ^^^ 18446744073709551615 =
      BitVec.ofNat 64 (2 ^ d - 1) := by
  rw [show (18446744073709551615 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not, BitVec.toNat_mul, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have h1 : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hd
  have h2 : 0 < 2 ^ d := Nat.two_pow_pos d
  generalize 2 ^ d = p at h1 h2 ⊢
  rw [Nat.mod_eq_of_lt h1]
  omega

theorem divu_eq {d : ℕ} (h0 : 0 < d) (hd : d < 64) :
    BitVec.signExtend 64 (wordResult WordOp.divu (BitVec.truncate 32 (192 : Word))
      (BitVec.truncate 32 (BitVec.ofNat 64 d))) = BitVec.ofNat 64 (192 / d) := by
  have hb : BitVec.truncate 32 (BitVec.ofNat 64 d) = BitVec.ofNat 32 d := by
    apply BitVec.eq_of_toNat_eq; simp
  have hb0 : BitVec.ofNat 32 d ≠ 0 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  have hq : 192 / d ≤ 192 := Nat.div_le_self _ _
  have hu : (BitVec.truncate 32 (192 : Word) / BitVec.ofNat 32 d).toNat = 192 / d := by
    rw [BitVec.toNat_udiv, show (BitVec.truncate 32 (192 : Word)).toNat = 192 from rfl,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega)]
  rw [hb]
  simp only [wordResult, hb0, ite_false]
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.truncate 32 (192 : Word) / BitVec.ofNat 32 d).msb = false := by
    rw [BitVec.msb_eq_decide, hu]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, hu, hm, BitVec.toNat_ofNat]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero]

theorem and63_small {x : Word} (h : x.toNat < 64) : x &&& 63 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (63 : Word).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem queries_length_of {n r : ℕ} {c : Model.Pcs.WhirConfigRust}
    (h : Model.Pcs.deriveConfigRust n r = some c) : c.queries.length = c.folds.length := by
  unfold Model.Pcs.deriveConfigRust at h
  cases hq : Model.Pcs.whirQueriesRust n r with
  | none => simp [hq] at h
  | some qs =>
    simp only [hq, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hl; cases h; exact hl
    · cases h

/-- What the setup and `sample_queries` write from the grinding's end `w`. -/
def QW (s w u : MachineState) (a : Word) : Prop :=
  W s a ∨ Within a (s.getReg .x2 - 2464) 1424 ∨ Within a (s.getReg .x2 - 464) 24 ∨
    Within a (s.getReg .x2 - 384) 32 ∨ Within a (s.getReg .x2 - 832) 16 ∨ Within a nextAddr 8 ∨
    Fresh w u a

theorem QW.of_heap {s w u v : MachineState} {a : Word} (h : heapNext u ≤ heapNext v)
    (ha : QW s w u a) : QW s w v a := by
  rcases ha with ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.1, by have := ha.2; omega⟩)))))

/-- The positions' `Vec<u64>` at `S - 464`: `r` drawn into a new buffer of `cnt`. -/
structure QVec (s w u : MachineState) (cnt : ℕ) (r : List Word) : Prop where
  cap : vecCap u (s.getReg .x2 - 464) = BitVec.ofNat 64 cnt
  len : vecLen u (s.getReg .x2 - 464) = BitVec.ofNat 64 r.length
  buf : NewBuf w u (vecPtr u (s.getReg .x2 - 464)) (cnt * 8) 8
  elems : u.readWords (vecPtr u (s.getReg .x2 - 464)) r.length = r
  le : r.length ≤ cnt
  hw : heapStart ≤ heapNext w
  hs : heapNext s ≤ heapNext w

/-- At `0x8000a9d8`, the positions `qs` drawn. -/
structure QDone (s w u : MachineState) (d : ℕ) (qs : List Word) : Prop where
  pc : u.pc = 0x8000a9d8
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s u (u.getMem nextAddr)
  fr : DFrame w u (QW s w u)
  mono : heapNext w ≤ heapNext u
  x1 : u.getReg .x1 = vecPtr u (s.getReg .x2 - 464)
  x8 : u.getReg .x8 = BitVec.ofNat 64 d
  x9 : u.getReg .x9 = w.getReg .x9
  x19 : u.getReg .x19 = vecCap u (s.getReg .x2 - 464)
  x20 : u.getReg .x20 = s.getReg .x10
  x26 : u.getReg .x26 = BitVec.ofNat 64 qs.length
  vec : QVec s w u qs.length qs
  /-- The running quadratic's length, in `s7` as at `S - 808`. -/
  x23 : u.getReg .x23 = u.getMem (s.getReg .x2 - 808)

/-- At `0x8000a8dc`, `sample_queries`' loop: `r` of the `cnt` positions drawn, at depth `d`. -/
structure QOuter (s w u : MachineState) (d cnt : ℕ) (r : List Word) : Prop where
  pc : u.pc = 0x8000a8dc
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s u (u.getMem nextAddr)
  fr : DFrame w u (QW s w u)
  mono : heapNext w ≤ heapNext u
  x1 : u.getReg .x1 = vecPtr u (s.getReg .x2 - 464)
  x8 : u.getReg .x8 = BitVec.ofNat 64 d
  x9 : u.getReg .x9 = w.getReg .x9
  x18 : u.getReg .x18 = 0 - BitVec.ofNat 64 d
  x19 : u.getReg .x19 = BitVec.ofNat 64 (2 ^ d - 1)
  x20 : u.getReg .x20 = s.getReg .x10
  x24 : u.getReg .x24 = BitVec.ofNat 64 cnt
  x26 : u.getReg .x26 = BitVec.ofNat 64 r.length
  s832 : u.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 cnt
  s824 : u.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 (192 / d)
  vec : QVec s w u cnt r
  lt : r.length < cnt
  d0 : 0 < d
  d64 : d < 64

theorem qsetup (hT : TryAllocZeroedSpec) {s w : MachineState} {QP QL : Word} {ℓ ml rt : ℕ}
    (hpre : VsoPre s) (hc : Cfg s QP QL)
    (hconf : Model.Pcs.deriveConfigRust (s.getReg .x12).toNat (s.getReg .x13).toNat =
      some (cfgOf s))
    (hinv : InvR s w (w.getMem nextAddr)) (hpc : w.pc = 0x8000a82c)
    (hsp : w.getReg .x2 = s.getReg .x2 - 1040) (hlt : ℓ < K0 s + 2) (hmr : ml + rt < 64)
    (h184 : w.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ)
    (h240 : w.getMem (s.getReg .x2 - 800) = QL)
    (h192 : w.getMem (s.getReg .x2 - 848) = QP)
    (h208 : w.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 (8 * ℓ))
    (h168 : w.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 ml)
    (h216 : w.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 rt)
    (hx20 : w.getReg .x20 = s.getReg .x10)
    (hx23 : w.getReg .x23 = w.getMem (s.getReg .x2 - 808)) :
    ∃ v, Reaches Image.code w v ∧ (Dead Image.code v ∨
      ∃ cnt, (cfgOf s).queries[ℓ]? = some cnt ∧ 0 < ml + rt ∧
        (∀ T, TranscriptAt w (s.getReg .x10) T → TranscriptAt v (s.getReg .x10) T) ∧
        ((cnt = 0 ∧ QDone s w v (ml + rt) []) ∨ QOuter s w v (ml + rt) cnt [])) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hro := hinv.rodata' hpre
  obtain ⟨hQP, hQL⟩ := hc.hQ w hro
  obtain ⟨hq, hQ8, hQlo, hQhi⟩ := Model.Pcs.RodataOk.queries hro hc.rate hc.logN
  simp only [qEntry] at hQP hQL
  rw [hQP] at hq hQ8 hQlo hQhi
  rw [hQL] at hq hQhi
  have hcq : (cfgOf s).queries = Model.Pcs.natsAt w QP QL.toNat := by
    simp only [cfgOf, hq, Option.getD_some]
  have hlen : QL.toNat = K0 s + 2 := by
    have := queries_length_of hconf
    rw [hcq] at this
    simpa [Model.Pcs.natsAt, cfgOf, Model.Pcs.ladderFolds] using this
  have hcnt : (cfgOf s).queries[ℓ]? = some (w.getMem (QP + BitVec.ofNat 64 (8 * ℓ))).toNat := by
    rw [hcq, Model.Pcs.natsAt, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have hl64 : ℓ < 2 ^ 64 := by have := K0_lt s; omega
  have hlt' : ℓ < QL.toNat := by omega
  -- the level against the table's length
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a82c_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have hpc₁ := b8000a82c_pc_taken h₁ (by
    rw [hsp]; rv_eval [h184, h240]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64] at this
    omega)
  have hm₁ := b8000a82c_mem_same h₁
  have k₁ := b8000a82c_keeps h₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₁ .x2 (by decide), hsp]
  -- the depth
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a83c_spec hpc₁ (by
    rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
  have hd : (t₁.getMem (t₁.getReg .x2 + (168 : Word)) + t₁.getMem (t₁.getReg .x2 + (216 : Word))) &&&
      (63 : Word) = BitVec.ofNat 64 (ml + rt) := by
    rw [sp₁, hm₁, hm₁]; rv_eval [h168, h216]
    rw [← BitVec.ofNat_add, and63_small (by rw [BitVec.toNat_ofNat]; omega)]
  by_cases hz : ml + rt = 0
  · have hpc₂ := b8000a83c_pc_not_taken h₂ (by rw [hd, hz]; rfl)
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a850_spec hpc₂ trivial
    exact ⟨t₃, hr₁.trans (hr₂.trans hr₃),
      Or.inl (dead_of_fetch (by rw [b8000a850_pc h₃]; exact trap))⟩
  have hpc₂ := b8000a83c_pc_taken h₂ (by
    rw [hd]; intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact hz this)
  have k₂ := b8000a83c_keeps h₂
  have hm₂ := b8000a83c_mem_same h₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₂ .x2 (by decide), sp₁]
  have x8₂ : t₂.getReg .x8 = BitVec.ofNat 64 (ml + rt) := by rw [b8000a83c_x8 h₂, hd]
  -- the count, and its buffer
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a854_spec (b8000a83c_pc_taken h₂ (by
      rw [hd]; intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hz this)) (by
    rv_eval [sp₂, hm₂, hm₁, h192, h208]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | (rw [Sym.validAccess_eight]; addr_omega [hQhi, hQlo, hQ8, hlt', hlen]))
  have k₃ := b8000a854_keeps h₃
  have hm₃ := b8000a854_mem_same h₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₃ .x2 (by decide), sp₂]
  have x11₃ : t₃.getReg .x11 = w.getMem (QP + BitVec.ofNat 64 (8 * ℓ)) := by
    rw [b8000a854_x11 h₃, sp₂]; simp only [hm₂, hm₁]; rv_eval [h192, h208]
  have hw := hinv.heap hpre.heap
  have hn₃ : heapNext t₃ = heapNext w := by simp only [heapNext, hm₃, hm₂, hm₁]
  have inv₃ : InvR s t₃ (w.getMem nextAddr) :=
    Inv.same' hinv (fun a ↦ by rw [hm₃, hm₂, hm₁]) (by rw [sp₃, hsp])
  obtain ⟨t₄, hr₄, hv₄⟩ := callTryAlloc8 hT hpre (b8000a854_pc h₃) sp₃
    (by rw [b8000a854_x10 h₃, sp₂]; rv_eval []) (b8000a854_x13 h₃) (b8000a854_x14 h₃)
    ⟨by rw [hn₃]; exact hw.lo, by rw [hn₃]; exact hw.hi⟩
  rcases hv₄ with hd₄ | ⟨hpc₄, hpres₄, hheap₄, hmono₄, hok₄, X₄⟩
  · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hd₄⟩
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres₄ .x2 (by decide), sp₃]
  have hfit₄ := hheap₄.hi
  have inv₄ : InvR s t₄ (t₄.getMem nextAddr) := by
    refine Inv.step' hpre inv₃ X₄ (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl
      (by simp only [heapNext] at hmono₄ hn₃; omega) hfit₄ (hpres₄ .x2 (by decide))
    · rcases ha with ha | ha | ha | ha
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by have := inv₃.mono; simp only [heapNext] at *; omega,
          by simp only [heapNext] at ha; exact ha.2⟩))
    · rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx]
      · simp only [Fresh, heapNext] at ha; addr_omega [ha.2, hb, hfit₄]
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000a880_spec
    (by rw [hpc₄, returnAddress_eq, b8000a854_x1 h₃]; decide) (by
      rv_eval [sp₄]; valid_access hst.valid [hb])
  have hm₅ := b8000a880_mem_same h₅
  have k₅ := b8000a880_keeps h₅
  have q656 : t₄.getMem (t₄.getReg .x2 + 656) = t₄.getMem (s.getReg .x2 - 384) := by
    rw [sp₄]; rv_eval []
  by_cases hok : t₄.getMem (s.getReg .x2 - 384) = 0
  swap
  · have hpc₅ := b8000a880_pc_not_taken h₅ (by rw [q656]; exact hok)
    obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000a888_spec hpc₅ trivial
    exact ⟨t₆, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))),
      Or.inl (dead_of_fetch (by rw [b8000a888_pc h₆]; exact trap))⟩
  have hpc₅ := b8000a880_pc_taken h₅ (by rw [q656]; exact hok)
  obtain ⟨hcap₄, hnew₄⟩ := hok₄ hok
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₅ .x2 (by decide), sp₄]
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000a88c_spec hpc₅ (by
      rv_eval [sp₅]; and_intros <;> valid_access hst.valid [hb])
  have k₆ := b8000a88c_keeps h₆
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₆ .x2 (by decide), sp₅]
  have hm₄₅ : ∀ a, t₅.getMem a = t₄.getMem a := hm₅
  have f₆ := DFrame.of_memFrame (b8000a88c_frame h₆ (by rw [sp₅]; addr_omega [hb]))
  rw [sp₅, show s.getReg .x2 - 1040 + 576 = s.getReg .x2 - 464 by rv_eval []] at f₆
  have nx₆ : t₆.getMem nextAddr = t₄.getMem nextAddr := by
    rw [f₆ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx], hm₅]
  have hn₆ : heapNext t₆ = heapNext t₄ := by simp only [heapNext, nx₆]
  set cntW := w.getMem (QP + BitVec.ofNat 64 (8 * ℓ)) with hcntW
  set P := t₄.getMem (s.getReg .x2 - 368) with hP
  have v576 : vecCap t₆ (s.getReg .x2 - 464) = cntW := by
    have := b8000a88c_m_x2_576 h₆; rw [sp₅] at this; rv_eval [hm₅] at this
    simp only [vecCap]; rw [this, hcap₄, x11₃]
  have v584 : vecPtr t₆ (s.getReg .x2 - 464) = P := by
    have := b8000a88c_m_x2_584 h₆; rw [sp₅] at this; rv_eval [hm₅] at this
    simp only [vecPtr]; rw [show s.getReg .x2 - 464 + 8 = s.getReg .x2 - 456 by rv_eval [], this]
  have v592 : vecLen t₆ (s.getReg .x2 - 464) = 0 := by
    have := b8000a88c_m_x2_592 h₆; rw [sp₅] at this; rv_eval [] at this
    simp only [vecLen]; rw [show s.getReg .x2 - 464 + 16 = s.getReg .x2 - 448 by rv_eval [], this]
  have x1₆ : t₆.getReg .x1 = P := by
    rw [b8000a88c_x1 h₆, sp₅]; rv_eval [hm₅]; rfl
  have x24₆ : t₆.getReg .x24 = cntW := by
    rw [k₆ .x24 (by decide), k₅ .x24 (by decide), hpres₄ .x24 (by decide), b8000a854_x24 h₃, sp₂]
    simp only [hm₂, hm₁]; rv_eval [h192, h208]; rfl
  have x8₆ : t₆.getReg .x8 = BitVec.ofNat 64 (ml + rt) := by
    rw [k₆ .x8 (by decide), k₅ .x8 (by decide), hpres₄ .x8 (by decide), k₃ .x8 (by decide), x8₂]
  have x9₆ : t₆.getReg .x9 = w.getReg .x9 := by
    rw [k₆ .x9 (by decide), k₅ .x9 (by decide), hpres₄ .x9 (by decide), k₃ .x9 (by decide),
      k₂ .x9 (by decide), k₁ .x9 (by decide)]
  have x20₆ : t₆.getReg .x20 = s.getReg .x10 := by
    rw [k₆ .x20 (by decide), k₅ .x20 (by decide), hpres₄ .x20 (by decide), k₃ .x20 (by decide),
      k₂ .x20 (by decide), k₁ .x20 (by decide), hx20]
  have hcnt' : (cfgOf s).queries[ℓ]? = some cntW.toNat := hcnt
  have hnew : NewBuf w t₆ P (cntW.toNat * 8) 8 := by
    have h' := hnew₄
    rw [x11₃] at h'
    simp only [NewBuf] at h' ⊢
    rw [hn₆, ← hn₃]
    exact h'
  have X₆ : DFrame w t₆ (QW s w t₆) := by
    have X₄' : DFrame w t₄ (QW s w t₆) := (DFrame.of_same (fun a ↦ by rw [hm₃, hm₂, hm₁]) _).trans
      X₄ fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))
        · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
        · simp only [Fresh] at ha
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))))
          · rw [← hn₃]; exact ha.1
          · rw [hn₆]; exact ha.2
    exact (X₄'.trans (DFrame.of_same hm₅ _) fun _ h ↦ h).trans f₆
      fun a ha ↦ Or.inr (Or.inr (Or.inl ha))
  have inv₆ : InvR s t₆ (t₆.getMem nextAddr) := by
    rw [nx₆]
    refine Inv.step' hpre (Inv.same' inv₄ hm₅ (k₅ .x2 (by decide))) f₆
      (fun a ha ↦ frame_wr hpre (by addr_omega [ha, hb])) (fun a ha ↦ by addr_omega [ha, hb]) nx₆
      (le_refl _) inv₄.fits (k₆ .x2 (by decide))
  have mono₆ : heapNext w ≤ heapNext t₆ := by rw [hn₆, ← hn₃]; exact hmono₄
  have Y₆ : DFrame w t₆ (NS s) := by
    have Y₄ : DFrame w t₄ (NS s) := (DFrame.of_same (fun a ↦ by rw [hm₃, hm₂, hm₁]) _).trans
      X₄ fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inr (Or.inl ha)
        · simp only [Fresh] at ha
          refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
          · have := hinv.mono; simp only [heapNext] at this ha hn₃ ⊢; omega
          · simp only [heapNext] at ha hfit₄ ⊢; omega
    exact (Y₄.trans (DFrame.of_same hm₅ _) fun _ h ↦ h).trans f₆
      fun a ha ↦ Or.inl (by addr_omega [ha, hb])
  have tr₆ : ∀ T, TranscriptAt w (s.getReg .x10) T → TranscriptAt t₆ (s.getReg .x10) T :=
    fun T hT ↦ tr_keep hpre hinv hT Y₆ fun _ h ↦ h
  have hr₁₆ := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))
  have hxx : t₅.getReg .x24 = cntW := by
    rw [k₅ .x24 (by decide), hpres₄ .x24 (by decide), b8000a854_x24 h₃, sp₂]
    simp only [hm₂, hm₁]; rv_eval [h192, h208]; rfl
  have hcntN : cntW = BitVec.ofNat 64 cntW.toNat := by simp
  by_cases h0 : cntW = 0
  · refine ⟨t₆, hr₁₆, Or.inr ⟨_, hcnt', by omega, tr₆, Or.inl ⟨by rw [h0]; rfl, {
      pc := b8000a88c_pc_taken h₆ (by rw [hxx, h0])
      sp := sp₆
      inv := inv₆
      fr := X₆
      mono := mono₆
      x1 := by rw [x1₆, v584]
      x8 := x8₆
      x9 := x9₆
      x19 := by
        rw [v576, b8000a88c_x19 h₆, sp₅]; rv_eval [hm₅]; rw [hcap₄, x11₃]
      x20 := x20₆
      x26 := b8000a88c_x26 h₆
      vec := {
        cap := by rw [v576, h0]; rfl
        len := by rw [v592]; rfl
        buf := by rw [v584]; have := hnew; rw [h0] at this; simpa using this
        elems := rfl
        le := le_refl _
        hw := hw.lo
        hs := by have := hinv.mono; simp only [heapNext] at this ⊢; exact this }
      x23 := by
        have hI := hpre.self
        have hS := Region.bounds hI.ok.self
        have hIs := hI.stack
        rw [stackLo_vso, vso_stack] at hIs
        have hhi6 : heapNext t₆ ≤ heapEnd := by rw [hn₆]; exact hfit₄
        rw [k₆ .x23 (by decide), k₅ .x23 (by decide), hpres₄ .x23 (by decide), k₃ .x23 (by decide),
          k₂ .x23 (by decide), k₁ .x23 (by decide), hx23]
        refine (X₆ _ fun i hi hw ↦ ?_).symm
        rcases hw with hw | hw | hw | hw | hw | hw | hw
        · simp only [W] at hw; addr_omega [hw, hi, hS, hIs, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb, hnx]
        · simp only [Fresh, heapNext, heapEnd] at hw hhi6
          addr_omega [hw.2, hi, hb, hhi6] }⟩⟩⟩
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000a8a8_spec
    (b8000a88c_pc_not_taken h₆ (by rw [hxx]; exact h0)) (by
      rv_eval [sp₆]; and_intros <;> valid_access hst.valid [hb])
  have e19 := h₇.reg_eq .x19 rfl rfl
  have e824 := h₇.mem_eq 1 (by decide) rfl rfl
  rv_eval [] at e19 e824
  have hd64 : (BitVec.ofNat 64 (ml + rt)).toNat = ml + rt := by
    rw [BitVec.toNat_ofNat]; omega
  rw [x8₆, hd64, Nat.mod_eq_of_lt hmr, mask_eq hmr] at e19
  rw [x8₆, divu_eq (by omega) hmr, sp₆] at e824
  rv_eval [] at e824
  have k₇ := b8000a8a8_keeps h₇
  have f₇ := DFrame.of_memFrame (b8000a8a8_frame h₇ (by rw [sp₆]; addr_omega [hb]))
  rw [sp₆, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval []] at f₇
  have hm7 : ∀ y, (s.getReg .x2 - 464).toNat ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2 - 440).toNat →
      t₇.getMem y = t₆.getMem y := fun y h1 h2 ↦ f₇ y fun i hi hw ↦ by addr_omega [hw, hi, h1, h2, hb]
  have nx₇ : t₇.getMem nextAddr = t₆.getMem nextAddr := f₇ _ fun i hi hw ↦ by
    addr_omega [hw, hi, hb, hnx]
  have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, nx₇]
  have vcap : vecCap t₇ (s.getReg .x2 - 464) = vecCap t₆ (s.getReg .x2 - 464) :=
    hm7 _ (by addr_omega [hb]) (by addr_omega [hb])
  have vptr : vecPtr t₇ (s.getReg .x2 - 464) = vecPtr t₆ (s.getReg .x2 - 464) :=
    hm7 _ (by addr_omega [hb]) (by addr_omega [hb])
  have vlen : vecLen t₇ (s.getReg .x2 - 464) = vecLen t₆ (s.getReg .x2 - 464) :=
    hm7 _ (by addr_omega [hb]) (by addr_omega [hb])
  have hcnt0 : 0 < cntW.toNat := by
    rcases Nat.eq_zero_or_pos cntW.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) h0
    · exact h
  refine ⟨t₇, hr₁₆.trans hr₇, Or.inr ⟨_, hcnt', by omega, fun T hT ↦ tr_keep hpre inv₆ (tr₆ T hT) f₇
      (fun a ha ↦ Or.inl (by addr_omega [ha, hb])), Or.inr {
    pc := b8000a8a8_pc h₇
    sp := by rw [k₇ .x2 (by decide), sp₆]
    inv := by
      rw [nx₇]
      exact Inv.step' hpre inv₆ f₇ (fun a ha ↦ frame_wr hpre (by addr_omega [ha, hb]))
        (fun a ha ↦ by addr_omega [ha, hb]) nx₇ (le_refl _) inv₆.fits (k₇ .x2 (by decide))
    fr := (X₆.mono fun a ha ↦ QW.of_heap (by rw [hn₇]) ha).trans f₇
      fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    mono := by rw [hn₇]; exact mono₆
    x1 := by rw [k₇ .x1 (by decide), x1₆, vptr, v584]
    x8 := by rw [k₇ .x8 (by decide), x8₆]
    x9 := by rw [k₇ .x9 (by decide), x9₆]
    x18 := by rw [b8000a8a8_x18 h₇, x8₆]
    x19 := e19
    x20 := by rw [k₇ .x20 (by decide), x20₆]
    x24 := by rw [k₇ .x24 (by decide), x24₆]; exact hcntN
    x26 := by rw [k₇ .x26 (by decide), b8000a88c_x26 h₆]; rfl
    s832 := by
      have := b8000a8a8_m_x2_208 h₇
      rw [sp₆, x24₆] at this; rv_eval [] at this; exact this.trans hcntN
    s824 := e824
    vec := {
      cap := by rw [vcap, v576]; exact hcntN
      len := by rw [vlen, v592]; rfl
      buf := by
        rw [vptr, v584]; simp only [NewBuf] at hnew ⊢; rw [hn₇]; exact hnew
      elems := rfl
      le := Nat.zero_le _
      hw := hw.lo
      hs := by have := hinv.mono; simp only [heapNext] at this ⊢; exact this }
    lt := hcnt0
    d0 := by omega
    d64 := hmr }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
