module

public import X86.Sphincs.Layer

/-!
# The hypertree and the result

`layers` runs `layer` from the bottom while `r12 < 3` (`layers_ok`): `msg` ends as the three
`layerRoot`s' root with `r12 = 3`, or `r12 = 4` when a layer has none. `result` compares `msg`
with `PK.root` (`result_ok`).
-/

@[expose] public section

namespace X86.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

/-! ## The layers -/

/-- The root after `n` layers from `d`, `none` once a layer has none. -/
def layersAcc (seed : BitVec 128) (idx : Index) (sig : Signature) (d : Digest) : Nat → Option Digest
  | 0 => some d
  | n + 1 => (layersAcc seed idx sig d n).bind fun r ↦
      if h : n < 3 then layerRoot seed idx sig ⟨n, h⟩ r else none

theorem layersAcc_succ (seed : BitVec 128) (idx : Index) (sig : Signature) (d : Digest) {n : Nat}
    (h : n < 3) :
    layersAcc seed idx sig d (n + 1) = (layersAcc seed idx sig d n).bind (layerRoot seed idx sig ⟨n, h⟩) := by
  simp only [layersAcc, dite_yes h]

theorem layersAcc_three (seed : BitVec 128) (idx : Index) (sig : Signature) (d : Digest) :
    layersAcc seed idx sig d 3 =
      ((layerRoot seed idx sig 0 d).bind (layerRoot seed idx sig 1)).bind (layerRoot seed idx sig 2) := by
  rw [layersAcc_succ _ _ _ _ (by decide), layersAcc_succ _ _ _ _ (by decide),
    layersAcc_succ _ _ _ _ (by decide), layersAcc, Option.bind_some]
  rfl

theorem layersAcc_none (seed : BitVec 128) (idx : Index) (sig : Signature) (d : Digest) {n : Nat}
    (h : layersAcc seed idx sig d n = none) : ∀ k, layersAcc seed idx sig d (n + k) = none
  | 0 => h
  | k + 1 => by rw [← Nat.add_assoc, layersAcc, layersAcc_none seed idx sig d h k, Option.bind_none]

/-- The layers loop's state after `n` layers. -/
abbrev LayersInv (base : UInt64) (V₀ : Nat → UInt64) (s₀ : QState) (pk : _root_.Sphincs.PublicKey)
    (sig : Signature) (idx : Index) (d : Digest) (s : QState) : Prop :=
  ∃ n V, Inv base V s ∧ n ≤ 3 ∧ Frame V₀ V ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rbp] s₀ s ∧
    ((∃ r, layersAcc pk.publicSeed idx sig d n = some r ∧ V msg = digestLo r ∧
        V (msg + 1) = digestHi r ∧ s.reg .r12 = n.toUInt64 ∧ s.reg .r11 = (145 * n).toUInt64 ∧
        s.reg .r15 = (idx.val / 2 ^ (8 * n)).toUInt64) ∨
      (layersAcc pk.publicSeed idx sig d 3 = none ∧ s.reg .r12 = (4 : Nat).toUInt64))

theorem layers_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {idx : Index} {d : Digest}
    (hm0 : V msg = digestLo d) (hm1 : V (msg + 1) = digestHi d)
    (hr15 : s.reg .r15 = idx.val.toUInt64) :
    WP layers s (fun s' ↦ ∃ V', Inv base V' s' ∧ Frame V V' ∧
      (layersAcc pk.publicSeed idx sig d 3 = none → s'.reg .r12 = (4 : Nat).toUInt64) ∧
      (∀ r, layersAcc pk.publicSeed idx sig d 3 = some r → V' msg = digestLo r ∧
        V' (msg + 1) = digestHi r ∧ s'.reg .r12 = (3 : Nat).toUInt64) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rbp]
        s s') E := by
  have hidx := idx.isLt
  unfold indexBits at hidx
  unfold layers
  step; step
  have h0 : LayersInv base V s pk sig idx d
      ((s.setReg .r12 (Int64.toUInt64 0)).setReg .r11 (Int64.toUInt64 0)) := by
    refine ⟨0, V, (hI.setReg (by decide) _).setReg (by decide) _, by omega, Frame.refl V, ?_,
      Or.inl ⟨d, rfl, hm0, hm1, ?_, ?_, ?_⟩⟩
    · intro r hr
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h]))]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true]; rfl
    · simp only [QState.setReg_reg, ite_true]; rfl
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, hr15, Nat.mul_zero, Nat.pow_zero,
        Nat.div_one]
  apply WP.blk_cons
  refine WP.mono (wp_loop (LayersInv base V s pk sig idx d) (fun s' ↦ 4 - (s'.reg .r12).toNat)
    h0 ?_) (fun s' h ↦ WP.blk_nil ?_) (fun _ h ↦ h)
  · rintro s1 ⟨n, V1, h1, hn, F1, f1, hr⟩ hc
    rcases hr with ⟨r, hacc, m0, m1, r12, r11, r15⟩ | ⟨-, r12⟩
    · rw [cond_ltu_imm r12 (imm_nat 3) (by omega) (by omega)] at hc
      have hn3 : n < 3 := by simpa using hc
      refine WP.mono (layer_ok (L := ⟨n, hn3⟩) (idx := idx) (d := r) hb h1 (hS.frame F1) m0 m1
        r12 r11 r15) (fun s2 ⟨V2, h2, F2, hnone, hsome, f2⟩ ↦ ?_) (fun _ h ↦ h)
      have hacc' := layersAcc_succ pk.publicSeed idx sig d hn3
      rw [hacc, Option.bind_some] at hacc'
      have f12 : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14,
          .r15, .rbp] s s2 := RegsFrame.trans f1 f2
      cases hroot : layerRoot pk.publicSeed idx sig ⟨n, hn3⟩ r with
      | none =>
        have r12' := hnone hroot
        refine ⟨⟨n + 1, V2, h2, by omega, F1.trans F2, f12, Or.inr ⟨?_, r12'⟩⟩, ?_⟩
        · rw [hroot] at hacc'
          have := layersAcc_none pk.publicSeed idx sig d hacc' (2 - n)
          rwa [show n + 1 + (2 - n) = 3 by omega] at this
        · rw [r12', r12, toNat_toUInt64' (show 4 < 2 ^ 64 by omega),
            toNat_toUInt64' (show n < 2 ^ 64 by omega)]
          omega
      | some r' =>
        obtain ⟨m0', m1', r12', r11', r15'⟩ := hsome r' hroot
        refine ⟨⟨n + 1, V2, h2, by omega, F1.trans F2, f12,
          Or.inl ⟨r', by rw [hacc', hroot], m0', m1', r12', r11', r15'⟩⟩, ?_⟩
        simp only [r12', r12, toNat_toUInt64' (show n + 1 < 2 ^ 64 by omega),
          toNat_toUInt64' (show n < 2 ^ 64 by omega)]
        omega
    · rw [cond_ltu_imm r12 (imm_nat 3) (by omega) (by omega)] at hc
      simp at hc
  · obtain ⟨⟨n, V', h', hn, F', f', hr⟩, hc⟩ := h
    rcases hr with ⟨r, hacc, m0, m1, r12, -, -⟩ | ⟨hnone, r12⟩
    · rw [cond_ltu_imm r12 (imm_nat 3) (by omega) (by omega)] at hc
      have hn3 : n = 3 := by simp at hc; omega
      subst hn3
      refine ⟨V', h', F', fun h ↦ absurd (hacc.symm.trans h) (by simp), fun r' h ↦ ?_, f'⟩
      rw [hacc, Option.some.injEq] at h
      subst h
      exact ⟨m0, m1, r12⟩
    · exact ⟨V', h', F', fun _ ↦ r12, fun r h ↦ absurd (hnone.symm.trans h) (by simp), f'⟩

/-! ## The result -/

theorem digest_eq_iff (a b : BitVec 128) :
    a = b ↔ digestLo a = digestLo b ∧ digestHi a = digestHi b := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    rw [← ofWords_digest a, ← ofWords_digest b, h0, h1]

theorem result_ok (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey} {m : Message}
    {sig : Signature} (hS : Static pk m sig V) {o : Option Digest}
    (hnone : o = none → s.reg .r12 = (4 : Nat).toUInt64)
    (hsome : ∀ r, o = some r → V msg = digestLo r ∧ V (msg + 1) = digestHi r ∧
      s.reg .r12 = (3 : Nat).toUInt64) :
    WP result s (fun s' ↦ s'.mem = s.mem ∧
      s'.reg .rax = (if (match o with | some r => decide (r = pk.root) | none => false) then 1 else 0) ∧
      RegsFrame [.rax, .rcx] s s') E := by
  have hctx : Context.ctxWords = 3200 := rfl
  have hmsg : msg = 1208 := rfl
  have hinp : inp = 128 := rfl
  have hr0 : V (inp + 2) = digestLo pk.root := by
    rw [hS.input 2 (by unfold inputWords; omega), encode_root0]
  have hr1 : V (inp + 3) = digestHi pk.root := by
    rw [hS.input 3 (by unfold inputWords; omega), encode_root1]
  unfold result
  cases o with
  | none =>
    apply WP.ite
    rw [cond_eq_imm (hnone rfl) (imm_nat 3) (by omega) (by omega), decide_eq_false (by omega),
      ite_no Bool.false_ne_true]
    refine WP.ins' ?_
    simp only [QInstr.step]
    refine ⟨rfl, by simp only [QState.setReg_reg, ite_true]; rfl, RegsFrame.setReg (by simp) _⟩
  | some r =>
    obtain ⟨m0, m1, r12⟩ := hsome r rfl
    show WP _ s (fun s' ↦ s'.mem = s.mem ∧
      s'.reg .rax = (if decide (r = pk.root) = true then 1 else 0) ∧ RegsFrame [.rax, .rcx] s s') E
    apply WP.ite
    rw [cond_eq_imm r12 (imm_nat 3) (by omega) (by omega), decide_eq_true rfl, ite_yes rfl]
    refine blk_load_cw hI (by omega) ?_
    refine blk_load_cw (hI.setReg (by decide) _) (by omega) ?_
    rw [m0, hr0]
    apply WP.blk_cons
    apply WP.ite
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
    by_cases h0 : digestLo r = digestLo pk.root
    · rw [h0, beq_self_eq_true, ite_yes rfl]
      refine blk_load_cw ((hI.setReg (by decide) _).setReg (by decide) _) (by omega) ?_
      refine blk_load_cw (((hI.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _)
        (by omega) ?_
      rw [m1, hr1]
      apply WP.blk_cons
      apply WP.ite
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
      by_cases h1 : digestHi r = digestHi pk.root
      · rw [h1, beq_self_eq_true, ite_yes rfl]
        refine WP.ins' ?_
        simp only [QInstr.step]
        refine WP.blk_nil (WP.blk_nil ⟨rfl, ?_, fun r' hr' ↦ ?_⟩)
        · simp only [QState.setReg_reg, ite_true]
          rw [decide_eq_true (p := r = pk.root) ((digest_eq_iff r pk.root).mpr ⟨h0, h1⟩),
            ite_yes rfl]
          rfl
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          simp [QState.setReg_reg, hr'.1, hr'.2]
      · rw [beq_false_of_ne h1, ite_no Bool.false_ne_true]
        refine WP.ins' ?_
        simp only [QInstr.step]
        refine WP.blk_nil (WP.blk_nil ⟨rfl, ?_, fun r' hr' ↦ ?_⟩)
        · simp only [QState.setReg_reg, ite_true]
          rw [decide_eq_false (p := r = pk.root) (fun h ↦ h1 ((digest_eq_iff r pk.root).mp h).2),
            ite_no (by simp)]
          rfl
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          simp [QState.setReg_reg, hr'.1, hr'.2]
    · rw [beq_false_of_ne h0, ite_no Bool.false_ne_true]
      refine WP.ins' ?_
      simp only [QInstr.step]
      refine WP.blk_nil ⟨rfl, ?_, fun r' hr' ↦ ?_⟩
      · simp only [QState.setReg_reg, ite_true]
        rw [decide_eq_false (p := r = pk.root) (fun h ↦ h0 ((digest_eq_iff r pk.root).mp h).1),
          ite_no (by simp)]
        rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp [QState.setReg_reg, hr'.1, hr'.2]

end X86.SphincsVerifier
