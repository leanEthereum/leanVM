/-
  Rv64mc.Proof.Walk.MainStream

  `main`'s stream loop (instruction 74, label `0x410`): `k` of the stream's `n` scalars copied from the input,
  two words each, into the `Vec<E>`'s block, until all `n` are, then on to the read of the phases' count (instruction
  93, `InvA`). The scalar `j` is the word pair at `p + 2j` (`scal`).
-/

import Rv64mc.Proof.Walk.MainBase
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Main

namespace Rv64mc.Proof.Walk.Main

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Main (Link tmpl)

/-- The stream's scalar `j`: the limbs at `p + 2j`. -/
def scal (words : List Word) (p j : Nat) : Word × Word := (words.getD (p + 2 * j) 0, words.getD (p + 2 * j + 1) 0)

/-- The stream loop's invariant after `k` scalars: the count `nW` read at `p - 1`, the block `sbuf`. -/
def InvS (env : Env) (words : List Word) (ret top : Word) (regs : Reg → Word) (m M1 : MachineState)
    (p : Nat) (nW sbuf cap : Word) (k : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m M1 R M ∧
    R .x10 = BitVec.ofNat 64 (words.length - (p - 1)) + (nW <<< 1 ^^^ 0xffffffffffffffff#64) ∧
    R .x11 = 0x10000000#64 + BitVec.ofNat 64 (8 * (p + 2 * k)) ∧
    R .x12 = BitVec.ofNat 64 (words.length - (p + 2 * k)) ∧
    R .x13 = sbuf + 8#64 + BitVec.ofNat 64 (16 * k) ∧ R .x14 = 1#64 ∧ R .x15 = BitVec.ofNat 64 (nW.toNat - k) ∧
    R .x18 = nW ∧ R .x19 = cap ∧ R .x20 = sbuf ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    1 ≤ p ∧ p + 2 * k ≤ words.length ∧ k < nW.toNat ∧ nW.toNat < 2 ^ 59 ∧ cap = nW ∧
    (env.next M1).toNat ≤ sbuf.toNat ∧ sbuf.toNat + 16 * nW.toNat ≤ (env.next M).toNat ∧
    EListAt M sbuf ((List.range k).map (scal words p))

/-- At the read of the phases' count (instruction 93), the stream read: `n` scalars from `p`, in the block `sbuf`
    (empty, the dangling `8`, for none), and the reader at `q = p + 2n`. -/
def InvA (env : Env) (words : List Word) (ret top : Word) (regs : Reg → Word) (m M1 : MachineState)
    (p : Nat) (nW sbuf cap : Word) (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m M1 R M ∧
    R .x10 = BitVec.ofNat 64 (words.length - (p + 2 * nW.toNat)) ∧
    R .x11 = 0x10000000#64 + BitVec.ofNat 64 (8 * (p + 2 * nW.toNat)) ∧
    R .x18 = nW ∧ R .x19 = cap ∧ R .x20 = sbuf ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    1 ≤ p ∧ p + 2 * nW.toNat < words.length ∧ nW.toNat < 2 ^ 59 ∧ cap.toNat = nW.toNat ∧
    ((nW.toNat = 0 ∧ sbuf = 8#64) ∨
      ((env.next M1).toNat ≤ sbuf.toNat ∧ sbuf.toNat + 16 * nW.toNat ≤ (env.next M).toNat)) ∧
    EListAt M sbuf ((List.range nW.toNat).map (scal words p))

/-- Two words stored at the end of a list of `E`s extend it. -/
theorem EListAt.snoc {M : MachineState} {a : Word} {es : List (Word × Word)} {e : Word × Word} {v0 v1 : Word}
    (h : EListAt M a es) (hn : a.toNat + 16 * (es.length + 1) < 2 ^ 64) (h0 : v0 = e.1) (h1 : v1 = e.2) :
    EListAt ((M.setMem (a + BitVec.ofNat 64 (16 * es.length)) v0).setMem
      (a + BitVec.ofNat 64 (16 * es.length + 8)) v1) a (es ++ [e]) := by
  obtain ⟨hb, he⟩ := h
  simp only [EListAt, EAt, Layouts.E.byteSize, Layouts.E.c0, Layouts.E.c1] at hb he ⊢
  have ad : ∀ x y, x < 2 ^ 64 → (a + BitVec.ofNat 64 x + BitVec.ofNat 64 y) = a + BitVec.ofNat 64 (x + y) :=
    fun x y _ => add_ofNat a x y
  have tn : ∀ x, a.toNat + x < 2 ^ 64 → (a + BitVec.ofNat 64 x).toNat = a.toNat + x := fun x hx => toNat_add_ofNat hx
  refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun k hk => ?_⟩
  simp only [List.length_append, List.length_singleton] at hk
  rw [ad _ _ (by omega), ad _ _ (by omega)]
  by_cases hkl : k < es.length
  · rw [List.getElem_append_left hkl]
    obtain ⟨e0, e1⟩ := he k hkl
    rw [ad _ _ (by omega)] at e0
    rw [ad _ _ (by omega)] at e1
    have n0 : a + BitVec.ofNat 64 (16 * k + 0) ≠ a + BitVec.ofNat 64 (16 * es.length + 8) := fun q => by
      have := congrArg BitVec.toNat q; rw [tn _ (by omega), tn _ (by omega)] at this; omega
    have n1 : a + BitVec.ofNat 64 (16 * k + 0) ≠ a + BitVec.ofNat 64 (16 * es.length) := fun q => by
      have := congrArg BitVec.toNat q; rw [tn _ (by omega), tn _ (by omega)] at this; omega
    have n2 : a + BitVec.ofNat 64 (16 * k + 8) ≠ a + BitVec.ofNat 64 (16 * es.length + 8) := fun q => by
      have := congrArg BitVec.toNat q; rw [tn _ (by omega), tn _ (by omega)] at this; omega
    have n3 : a + BitVec.ofNat 64 (16 * k + 8) ≠ a + BitVec.ofNat 64 (16 * es.length) := fun q => by
      have := congrArg BitVec.toNat q; rw [tn _ (by omega), tn _ (by omega)] at this; omega
    rw [MachineState.getMem_setMem_ne n0, MachineState.getMem_setMem_ne n1, MachineState.getMem_setMem_ne n2,
      MachineState.getMem_setMem_ne n3]
    exact ⟨e0, e1⟩
  · have hk' : k = es.length := by omega
    subst hk'
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem_cons_zero, Nat.add_zero]
    have n0 : a + BitVec.ofNat 64 (16 * es.length) ≠ a + BitVec.ofNat 64 (16 * es.length + 8) := fun q => by
      have := congrArg BitVec.toNat q; rw [tn _ (by omega), tn _ (by omega)] at this; omega
    rw [MachineState.getMem_setMem_ne n0, MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]
    exact ⟨h0, h1⟩

theorem scal_range_succ (words : List Word) (p k : Nat) :
    (List.range (k + 1)).map (scal words p) = (List.range k).map (scal words p) ++ [scal words p k] := by
  rw [List.range_succ, List.map_append]; rfl

theorem not_xor_shl (a : Nat) (w : Word) (hw : w.toNat < 2 ^ 59) (ha : 2 * w.toNat + 1 ≤ a) (ha' : a < 2 ^ 64) :
    BitVec.ofNat 64 a + (w <<< 1 ^^^ 0xffffffffffffffff#64) = BitVec.ofNat 64 (a - 1 - 2 * w.toNat) := by
  rw [show (0xffffffffffffffff#64 : Word) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt (show a - 1 - 2 * w.toNat < 2 ^ 64 by omega)]
  omega

theorem addr_m8 (s : Word) (x : Nat) : s + 8#64 + BitVec.ofNat 64 x + 18446744073709551608#64 = s + BitVec.ofNat 64 x := by
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 x), ← BitVec.add_assoc, BitVec.add_assoc s,
    show (8#64 : Word) + 18446744073709551608#64 = 0#64 by decide, BitVec.add_zero]

theorem addr_p8 (s : Word) (x : Nat) : s + 8#64 + BitVec.ofNat 64 x = s + BitVec.ofNat 64 (x + 8) := by
  rw [BitVec.add_assoc, BitVec.add_comm 8#64, BitVec.ofNat_add]

/-- The memory after one pass of the stream loop. -/
def stS (M : MachineState) (sbuf : Word) (pos k : Nat) : MachineState :=
  (M.setMem (sbuf + 8#64 + BitVec.ofNat 64 (16 * k) + 18446744073709551608#64)
    (M.getMem (0x10000000#64 + BitVec.ofNat 64 (8 * (pos + 2 * k))))).setMem (sbuf + 8#64 + BitVec.ofNat 64 (16 * k))
    (M.getMem (0x10000000#64 + BitVec.ofNat 64 (8 * (pos + 2 * k)) + 8#64))

theorem lt_of_ne01 {x : Nat} (hx : x < 2 ^ 64) (h1 : ¬BitVec.ofNat 64 x = 1#64) (h0 : ¬BitVec.ofNat 64 x = 0#64) :
    2 ≤ x := by
  rw [ofNat_eq_iff hx (by decide)] at h1 h0
  omega

theorem Base.with_sp {env : Env} {ret top : Word} {regs : Reg → Word} {m M1 : MachineState} {R R' : Reg → Word}
    {M : MachineState} (h : Base env ret top regs m M1 R M) (h2 : R' .x2 = top + 0xfffffffffffffe60#64) :
    Base env ret top regs m M1 R' M := ⟨h2, h.2⟩

/-- **One pass of the stream loop** keeps `Base` and copies the scalar `k`. -/
theorem stepS {env : Env} {words : List Word} {ret top : Word} {regs : Reg → Word} {m M1 : MachineState}
    {pos : Nat} {nW sbuf cap : Word} {k : Nat} {R : Reg → Word} {M : MachineState}
    (fx : Fix env words top m M1) (hlen : words.length ≤ inputCapacity)
    (hinv : InvS env words ret top regs m M1 pos nW sbuf cap k R M)
    (hc1 : ¬BitVec.ofNat 64 (words.length - (pos + 2 * k)) = 1#64)
    (hc2 : ¬BitVec.ofNat 64 (words.length - (pos + 2 * k)) = 0#64) {R' : Reg → Word}
    (hR : R' .x2 = top + 0xfffffffffffffe60#64) :
    Base env ret top regs m M1 R' (stS M sbuf pos k) ∧
      EListAt (stS M sbuf pos k) sbuf ((List.range (k + 1)).map (scal words pos)) ∧
      pos + 2 * (k + 1) ≤ words.length ∧ env.next (stS M sbuf pos k) = env.next M := by
  obtain ⟨hb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1p, hpk, hkn, hn59, -, hs1, hs2, hE⟩ := hinv
  have hcap : inputCapacity = 2 ^ 25 := rfl
  have h2 := lt_of_ne01 (by omega) hc1 hc2
  have hN := hb.2.2.2.2.2.2.2
  have hl := env.layout
  have tk : (sbuf + BitVec.ofNat 64 (16 * k)).toNat = sbuf.toNat + 16 * k := toNat_add_ofNat (by omega)
  have tk8 : (sbuf + BitVec.ofNat 64 (16 * k + 8)).toNat = sbuf.toNat + 16 * k + 8 := toNat_add_ofNat (by omega)
  have v0 := Base.input fx hb (q := pos + 2 * k) (by omega)
  have v1 := Base.input fx hb (q := pos + 2 * k + 1) (by omega)
  have e1 : (0x10000000#64 : Word) + BitVec.ofNat 64 (8 * (pos + 2 * k)) + 8#64 =
      0x10000000#64 + BitVec.ofNat 64 (8 * (pos + 2 * k + 1)) := by
    rw [add_lit _ _ 8 _ rfl, show 8 * (pos + 2 * k) + 8 = 8 * (pos + 2 * k + 1) by omega]
  have hst : stS M sbuf pos k = (M.setMem (sbuf + BitVec.ofNat 64 (16 * k)) words[pos + 2 * k]).setMem
      (sbuf + BitVec.ofNat 64 (16 * k + 8)) words[pos + 2 * k + 1] := by
    rw [stS, addr_m8, addr_p8, v0, e1, v1]
  have hne : sbuf + BitVec.ofNat 64 (16 * k) ≠ env.nextAddr := fun e => by rw [e] at tk; omega
  have hn1 := Tactic.next_setMem (N := M) (v := words[pos + 2 * k]) hne
  have hne' : sbuf + BitVec.ofNat 64 (16 * k + 8) ≠ env.nextAddr := fun e => by rw [e] at tk8; omega
  rw [hst]
  have hb1 := Base.store (a := sbuf + BitVec.ofNat 64 (16 * k)) (v := words[pos + 2 * k]) fx hb hb.1
    (Or.inr ⟨by omega, by omega⟩)
  refine ⟨Base.store (a := sbuf + BitVec.ofNat 64 (16 * k + 8)) (v := words[pos + 2 * k + 1]) fx hb1 hR
    (Or.inr ⟨by omega, by rw [hn1]; omega⟩), ?_, by omega, by
    rw [Tactic.next_setMem hne', hn1]⟩
  rw [scal_range_succ]
  have := EListAt.snoc (e := scal words pos k) (v0 := words[pos + 2 * k]) (v1 := words[pos + 2 * k + 1]) hE
    (by simp only [List.length_map, List.length_range]; omega)
    (by simp only [scal]; rw [List.getD_eq_getElem _ _ (by omega)])
    (by simp only [scal]; rw [List.getD_eq_getElem _ _ (by omega)])
  simpa only [List.length_map, List.length_range] using this

set_option rv_sym.heap true in
/-- **The stream loop**, from its head with `d + 1` scalars to go. -/
theorem loopS (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (hhalt : NoReturn env p L.halt.idx 0)
    (words : List Word) {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {regs : Reg → Word} {m M1 : MachineState} {pos : Nat} {nW sbuf cap : Word}
    (fx : Fix env words top m M1) (hlen : words.length ≤ inputCapacity)
    (hnext : ∀ R M, InvA env words ret top regs m M1 pos nW sbuf cap R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 186, ret, top⟩ :: rest, R, M⟩) :
    ∀ d k R M, k + d + 1 = nW.toNat → InvS env words ret top regs m M1 pos nW sbuf cap k R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 148, ret, top⟩ :: rest, R, M⟩ := by
  have hal := fx.align
  have hcap' : inputCapacity = 2 ^ 25 := rfl
  intro d
  induction d with
  | zero =>
    intro k R M hd hinv
    have hinv0 := hinv
    obtain ⟨hb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1p, hpk, hkn, hn59, hcap, hs1, hs2, hE⟩ := id hinv
    unfold InvS Base at hinv
    rv_intro hinv
    rv_sym hp stop [186] with [hL] using [hhalt]
    · exfalso; apply hc
      rw [sub_lit (k := 1) _ (by decide) (by omega) (by omega), show nW.toNat - k - 1 = 0 by omega]
    · obtain ⟨hb', hE', hpk', hnx'⟩ := stepS fx hlen hinv0 hc_1 hc_2 hb.1
      have h2 := lt_of_ne01 (by omega) hc_1 hc_2
      rw [not_xor_shl _ _ hn59 (by omega) (by omega), ofNat_eq_lit _ (by omega)] at hc
      refine hnext _ _ ⟨Base.with_sp hb' rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h1p,
        by simp only [show (0#64 : Word).toNat = 0 from rfl] at hc; omega, hn59, by rw [hcap],
        Or.inr ⟨hs1, by unfold stS at hnx'; rw [hnx']; exact hs2⟩, by rw [show nW.toNat = k + 1 by omega]; exact hE'⟩
      · rw [Tactic.rf_get_x10, not_xor_shl _ _ hn59 (by omega) (by omega),
          show words.length - (pos - 1) - 1 - 2 * nW.toNat = words.length - (pos + 2 * nW.toNat) by omega]
      · rw [Tactic.rf_get_x11, add_lit _ _ 16 _ rfl, show 8 * (pos + 2 * k) + 16 = 8 * (pos + 2 * nW.toNat) by omega]
    · exact (stepS fx hlen hinv0 hc_1 hc_2 hb.1).1.2.2.1
    · exact (stepS fx hlen hinv0 hc_1 hc_2 hb.1).1.2.2.2.2.2.2.2
  | succ d ih =>
    intro k R M hd hinv
    have hinv0 := hinv
    obtain ⟨hb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1p, hpk, hkn, hn59, hcap, hs1, hs2, hE⟩ := id hinv
    unfold InvS Base at hinv
    rv_intro hinv
    rv_sym hp stop [186] with [hL] using [hhalt]
    · obtain ⟨hb', hE', hpk', hnx'⟩ := stepS fx hlen hinv0 hc_1 hc_2 hb.1
      have h2 := lt_of_ne01 (by omega) hc_1 hc_2
      refine ih (k + 1) _ _ (by omega) ⟨Base.with_sp hb' rfl, rfl, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, h1p, hpk', by omega, hn59, hcap, hs1, by unfold stS at hnx'; rw [hnx']; exact hs2, hE'⟩
      · rw [Tactic.rf_get_x11, add_lit _ _ 16 _ rfl, show 8 * (pos + 2 * k) + 16 = 8 * (pos + 2 * (k + 1)) by omega]
      · rw [Tactic.rf_get_x12, sub_lit (k := 2) _ (by decide) h2 (by omega),
          show words.length - (pos + 2 * k) - 2 = words.length - (pos + 2 * (k + 1)) by omega]
      · rw [Tactic.rf_get_x13, add_lit _ _ 16 _ rfl, show 16 * k + 16 = 16 * (k + 1) by omega]
      · rw [Tactic.rf_get_x15, sub_lit (k := 1) _ (by decide) (by omega) (by omega),
          show nW.toNat - k - 1 = nW.toNat - (k + 1) by omega]
    · exfalso
      rw [sub_lit (k := 1) _ (by decide) (by omega) (by omega), ofNat_eq_lit _ (by omega)] at hc_3
      simp only [show (0#64 : Word).toNat = 0 from rfl] at hc_3; omega
    · exact (stepS fx hlen hinv0 hc_1 hc_2 hb.1).1.2.2.1
    · exact (stepS fx hlen hinv0 hc_1 hc_2 hb.1).1.2.2.2.2.2.2.2

end Rv64mc.Proof.Walk.Main
