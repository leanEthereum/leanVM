module

public import X86.Sphincs.DigestSpec
public import X86.Sphincs.Input

/-!
# The message digest, its index and its FORS leaves

`digestInput`, `digestCalls`, `readIndex` and the 24 `forsLeaf` blocks leave the two digest calls'
lanes at `dgst`, the index `idx` in `r15` and the FORS leaves at `forsLeaves`.
-/

@[expose] public section

namespace X86.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig _root_.Sphincs Keccak

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

theorem imm_toUInt64 (k : Int64) (n : Nat) (h : k = n.toInt64) : k.toUInt64 = n.toUInt64 := by
  rw [h, toInt64_toUInt64]

theorem toNat_shr_and (x : UInt64) {n k : Nat} (hn : n < 64) (hk : k < 64) :
    ((x >>> n.toUInt64) &&& (2 ^ k - 1 : Nat).toUInt64).toNat = x.toNat / 2 ^ n % 2 ^ k := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, toNat_toUInt64 (by omega),
    toNat_toUInt64 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) hk)),
    Nat.mod_eq_of_lt hn, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-! ## The digest calls' input -/

theorem digestInput_ok (hI : Inv base V s) :
    WP digestInput s (fun s' ↦ ∃ V', Inv base V' s' ∧
      (∀ k, ¬(mdBuf ≤ k ∧ k < mdBuf + 10) → V' k = V k) ∧
      (∀ i < 10, V' (mdBuf + i) = V (inp + (i + 8) % 10)) ∧ RegsFrame [.rax] s s') E := by
  unfold digestInput
  have := wp_blk_forall (E := E) (s := s) (xs := (List.range 10).map fun i ↦
      mv (cw (inp + (i + 8) % 10)) (cw (mdBuf + i)))
    (fun n s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬(mdBuf ≤ k ∧ k < mdBuf + n) → V' k = V k) ∧
      (∀ i < n, V' (mdBuf + i) = V (inp + (i + 8) % 10)) ∧ RegsFrame [.rax] s s')
    ⟨V, hI, fun _ _ ↦ rfl, fun i hi ↦ absurd hi (by omega), fun _ _ ↦ rfl⟩ ?_
  · simpa using this
  intro n hn s1 ⟨V1, h1, e1, a1, f1⟩
  simp only [List.length_map, List.length_range] at hn
  simp only [List.getElem_map, List.getElem_range]
  refine WP.mono (mv_ok (j := inp + (n + 8) % 10) (k := mdBuf + n) h1 (by rw [cw_eval, h1.rdi])
    (by unfold inp Context.ctxWords; omega) (by rw [cw_eval]; simp [h1.rdi])
    (by unfold mdBuf Context.ctxWords; omega)) (fun s2 ⟨h2, f2⟩ ↦ ⟨_, h2, fun k hk ↦ ?_,
      fun i hi ↦ ?_, RegsFrame.trans f1 f2⟩) (fun _ h ↦ h)
  · rw [Function.update_of_ne (by omega), e1 k (by omega)]
  · rw [e1 _ (by unfold inp mdBuf; omega)]
    rcases Nat.lt_or_ge i n with hi' | hi'
    · rw [Function.update_of_ne (by omega), a1 i hi']
    · rw [show i = n by omega, Function.update_self]

/-! ## The digest calls -/

theorem mdWords_drop (R seed root : BitVec 128) (m : BitVec 256) {c : Nat} (hc : c < 2) :
    ∀ b ∈ (wordsBytes (mdWords R seed root m c)).drop 84, b = 0 := by
  have h80 : (wordsBytes (mdHead R seed root m)).length = 80 := by
    rw [wordsBytes_length]; simp [mdHead]
  rw [mdWords, wordsBytes_append, List.drop_append, h80, List.drop_of_length_le (by omega),
    List.nil_append]
  interval_cases c <;> (simp [wordsBytes, wordBytes, List.range_succ]; try decide)

theorem mdLane_eq (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256) {c k : Nat}
    (hk : k < 4) :
    mdLane pk R m (4 * c + k) = (keccak256 ((wordsBytes (mdWords R pk.publicSeed pk.root m c)).take 84))[k] := by
  simp only [mdLane, mdLanes, show (4 * c + k) / 4 = c by omega, show (4 * c + k) % 4 = k by omega]

theorem digestCalls_ok (hb : Fits base) (hI : Inv base V s) {R seed root : BitVec 128}
    {m : BitVec 256} (pk : _root_.Sphincs.PublicKey) (hpk : pk.publicSeed = seed ∧ pk.root = root)
    (hmd : words V mdBuf 10 = mdHead R seed root m) :
    WP digestCalls s (fun s' ↦ ∃ V', Inv base V' s' ∧
      (∀ k, scratchWords ≤ k → k ≠ mdBuf + 10 → ¬(dgst ≤ k ∧ k < dgst + 8) → V' k = V k) ∧
      (∀ k < 8, V' (dgst + k) = mdLane pk R m k) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp, .r9] s s') E := by
  obtain ⟨rfl, rfl⟩ := hpk
  unfold digestCalls
  step
  apply WP.blk_cons
  refine WP.mono (WP.loop (fun s' ↦ ∃ c V', Inv base V' s' ∧ s'.reg .rbp = c.toUInt64 ∧ c ≤ 2 ∧
      (∀ k, scratchWords ≤ k → k ≠ mdBuf + 10 → ¬(dgst ≤ k ∧ k < dgst + 8) → V' k = V k) ∧
      (∀ k < 4 * c, V' (dgst + k) = mdLane pk R m k) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp, .r9] s s')
    (fun s' ↦ 2 - (s'.reg .rbp).toNat) ⟨0, V, hI.setReg (by decide) _, by simp; rfl, by omega,
      fun _ _ _ _ ↦ rfl, fun k hk ↦ absurd hk (by omega), RegsFrame.setReg (by simp) _⟩ ?_ ?_)
    (fun s' h ↦ WP.blk_nil h) (fun _ h ↦ h)
  · rintro s1 ⟨c, V1, h1, hc1, hc2, e1, d1, f1⟩ hcond
    rw [cond_ltu_imm (k := 2) (K := 2) hc1 rfl (by omega) (by decide)] at hcond
    have hc : c < 2 := by simpa using hcond
    have hsw : scratchWords = 84 := rfl
    step; step
    simp only [hc1]
    have h1a := h1.setReg (d := .rax) (by decide) (c.toUInt64 <<< (24 : Nat).toUInt64)
    refine blk_store_cw h1a (by unfold mdBuf Context.ctxWords; omega) ?_
    simp only [QState.setReg_reg, ite_true]
    have h2 := h1a.setMem (k := mdBuf + 10) (by unfold mdBuf Context.ctxWords; omega)
      (c.toUInt64 <<< (24 : Nat).toUInt64)
    have hw : words (Function.update V1 (mdBuf + 10) (c.toUInt64 <<< (24 : Nat).toUInt64)) mdBuf
        ((84 + 7) / 8) = mdWords R pk.publicSeed pk.root m c := by
      unfold mdWords
      rw [show (84 + 7) / 8 = 10 + 1 from rfl, words_add, words_one, Function.update_self]
      congr 1
      rw [← hmd]
      apply words_congr
      intro i hi
      rw [Function.update_of_ne (by omega), e1 _ (by unfold mdBuf; omega) (by omega)
        (by unfold mdBuf dgst; omega)]
    apply WP.blk_cons
    refine WP.mono (hashAt_ok hb h2 (buf := mdBuf) (len := 84) (by unfold mdBuf; omega)
      (by unfold mdBuf Context.ctxWords; omega) (by omega) (by omega)
      (hw ▸ mdWords_drop _ _ _ _ hc)) (fun s2 ⟨V2, h2', e2, d2, f2⟩ ↦ ?_) (fun _ h ↦ h)
    rw [hw] at d2
    have hbp : s2.reg .rbp = c.toUInt64 := by
      rw [f2 .rbp (by simp)]; simp [hc1]
    step; step
    simp only [hbp, toUInt64_shl (show 2 < 64 by omega) (show c * 2 ^ 2 < 2 ^ 64 by omega)]
    have h3 := h2'.setReg (d := .r9) (by decide) (c * 2 ^ 2).toUInt64
    apply WP.blk_cons
    refine WP.mono (wp_blk_forall (E := E)
      (xs := (List.range 4).map fun k ↦ mv (cw k) (cwi .r9 (dgst + k)))
      (fun n s' ↦ ∃ V', Inv base V' s' ∧ s'.reg .r9 = (c * 2 ^ 2).toUInt64 ∧
        s'.reg .rbp = c.toUInt64 ∧
        (∀ k, ¬(dgst + 4 * c ≤ k ∧ k < dgst + 4 * c + n) → V' k = V2 k) ∧
        (∀ k < n, V' (dgst + 4 * c + k) = V2 k) ∧
        RegsFrame [.rax] (s2.setReg .r9 (c * 2 ^ 2).toUInt64) s')
      ⟨V2, h3, by simp, by simp [hbp], fun _ _ ↦ rfl, fun k hk ↦ absurd hk (by omega),
        fun _ _ ↦ rfl⟩ ?_) (fun s4 ⟨V4, h4, r4, b4, e4, d4, f4⟩ ↦ ?_) (fun _ h ↦ h)
    · intro n hn s3 ⟨V3, h3', r3, b3, e3, d3, f3⟩
      simp only [List.length_map, List.length_range] at hn
      simp only [List.getElem_map, List.getElem_range]
      have r3' : (s3.setReg .rax (V3 n)).reg .r9 = (c * 2 ^ 2).toUInt64 := by
        simp only [QState.setReg_reg, reduceCtorEq, ite_false]; exact r3
      refine WP.mono (mv_ok (j := n) (k := c * 2 ^ 2 + (dgst + n)) h3' (by rw [cw_eval, h3'.rdi])
        (by unfold Context.ctxWords; omega) (by rw [cwi_eval _ r3']; simp [h3'.rdi])
        (by unfold dgst Context.ctxWords; omega)) (fun s4 ⟨h4, f4⟩ ↦ ⟨_, h4, ?_, ?_, ?_, ?_,
          RegsFrame.trans f3 f4⟩) (fun _ h ↦ h)
      · rw [f4 .r9 (by simp), r3]
      · rw [f4 .rbp (by simp), b3]
      · intro k hk
        rw [Function.update_of_ne (by omega), e3 k (by omega)]
      · intro k hk
        rcases Nat.lt_or_ge k n with hk' | hk'
        · rw [Function.update_of_ne (by omega), d3 k hk']
        · rw [show k = n by omega, show dgst + 4 * c + n = c * 2 ^ 2 + (dgst + n) by omega,
            Function.update_self, e3 n (by unfold dgst; omega)]
    · simp only [List.length_map, List.length_range] at e4 d4
      apply WP.blk_cons
      apply WP.ins'
      simp only [QInstr.step, b4]
      apply WP.blk_nil
      have hbp' : c.toUInt64 + Int64.toUInt64 1 = (c + 1).toUInt64 := by
        rw [show Int64.toUInt64 1 = (1 : Nat).toUInt64 from rfl, toUInt64_add]
      refine ⟨⟨c + 1, V4, h4.setReg (by decide) _, by simp [hbp'], by omega, fun k hk1 hk2 hk3 ↦ ?_,
        fun k hk ↦ ?_, ?_⟩, ?_⟩
      · rw [e4 k (by unfold dgst at *; omega), e2 k hk1, Function.update_of_ne hk2, e1 k hk1 hk2 hk3]
      · rcases Nat.lt_or_ge k (4 * c) with hk' | hk'
        · rw [e4 _ (by omega), e2 _ (by unfold dgst; omega), Function.update_of_ne (by unfold mdBuf dgst; omega),
            d1 k hk']
        · obtain ⟨j, rfl⟩ : ∃ j, k = 4 * c + j := ⟨k - 4 * c, by omega⟩
          rw [show dgst + (4 * c + j) = dgst + 4 * c + j by omega, d4 j (by omega),
            d2 j (by omega), mdLane_eq pk R m (by omega)]
      · intro r hr
        simp only [QState.setReg_reg]
        rw [ite_no (fun h ↦ hr (by simp [h])), f4 r (fun h ↦ hr (by simp_all)),
          QState.setReg_reg, ite_no (fun h ↦ hr (by simp [h])), f2 r (fun h ↦ hr (by simp_all)),
          QState.setMem_reg, QState.setReg_reg, ite_no (fun h ↦ hr (by simp [h])),
          f1 r hr]
      · simp only [QState.setReg_reg, ite_true, hbp', toNat_toUInt64' (show c + 1 < 2 ^ 64 by omega),
          toNat_toUInt64' (show c < 2 ^ 64 by omega)]
        omega
  · rintro s1 ⟨c, V1, h1, hc1, hc2, e1, d1, f1⟩ hcond
    rw [cond_ltu_imm (k := 2) (K := 2) hc1 rfl (by omega) (by decide)] at hcond
    have hc : c = 2 := by simp at hcond; omega
    subst hc
    exact ⟨V1, h1, e1, d1, f1⟩

/-! ## The index and the FORS leaves -/

theorem digestByte_ok (hI : Inv base V s) {d : Reg64} {j : Nat} (hj : j < 64) :
    WP (digestByte d j) s (fun s' ↦ s' = s.setReg d
      ((V (dgst + j / 8)).toNat / 2 ^ (8 * (j % 8)) % 2 ^ 8).toUInt64) E := by
  unfold digestByte
  refine blk_load_cw hI (by unfold dgst Context.ctxWords; omega) ?_
  step; step
  apply WP.blk_nil
  congr 1
  rw [show (0xff : Int64).toUInt64 = (2 ^ 8 - 1 : Nat).toUInt64 from rfl,
    show (V (dgst + j / 8)) = (V (dgst + j / 8)).toNat.toUInt64 by simp,
    toUInt64_shr (by omega) (UInt64.toNat_lt _), toUInt64_and_mask (by omega)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (UInt64.toNat_lt _)),
    toNat_toUInt64' (UInt64.toNat_lt _)]

theorem idx_word {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    ((a.toUInt64 <<< (16 : Nat).toUInt64 + b.toUInt64 <<< (8 : Nat).toUInt64 + c.toUInt64) &&&
        (262143 : Int64).toUInt64) <<< (8 : Nat).toUInt64 + d.toUInt64 =
      ((((a * 256 + b) * 256 + c) % 2 ^ 18) * 256 + d).toUInt64 := by
  rw [toUInt64_shl (a := a) (n := 16) (by omega) (by omega),
    toUInt64_shl (a := b) (n := 8) (by omega) (by omega), toUInt64_add, toUInt64_add,
    show (262143 : Int64).toUInt64 = (2 ^ 18 - 1 : Nat).toUInt64 from rfl,
    toUInt64_and_mask (a := a * 2 ^ 16 + b * 2 ^ 8 + c) (k := 18) (by omega) (by omega),
    toUInt64_shl (a := (a * 2 ^ 16 + b * 2 ^ 8 + c) % 2 ^ 18) (n := 8) (by omega) (by omega),
    toUInt64_add]
  exact congrArg _ (by omega)

theorem leaf_word {a b o : Nat} (ha : a < 256) (hb : b < 256) (ho : o ≤ 6) :
    ((a.toUInt64 <<< (8 : Nat).toUInt64 + b.toUInt64) >>> o.toUInt64 &&& (1023 : Int64).toUInt64) =
      ((a * 256 + b) / 2 ^ o % 1024).toUInt64 := by
  rw [toUInt64_shl (a := a) (n := 8) (by omega) (by omega), toUInt64_add,
    toUInt64_shr (a := a * 2 ^ 8 + b) (n := o) (by omega) (by omega),
    show (1023 : Int64).toUInt64 = (2 ^ 10 - 1 : Nat).toUInt64 from rfl,
    toUInt64_and_mask (a := (a * 2 ^ 8 + b) / 2 ^ o) (k := 10) (by omega)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  rfl

/-- The digest calls' lanes at `dgst`. -/
def LanesAt (V : Nat → UInt64) (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256) :
    Prop := ∀ k < 8, V (dgst + k) = mdLane pk R m k

theorem LanesAt.byte {pk : _root_.Sphincs.PublicKey} {R : BitVec 128} {m : BitVec 256}
    (h : LanesAt V pk R m) {j : Nat} (hj : j < 64) :
    ((V (dgst + j / 8)).toNat / 2 ^ (8 * (j % 8)) % 2 ^ 8) = mdByte pk R m j := by
  rw [h _ (by omega)]; rfl

theorem readIndex_ok (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey} {R : BitVec 128}
    {m : BitVec 256} (hl : LanesAt V pk R m) :
    WP readIndex s (fun s' ↦ s'.mem = s.mem ∧ s'.reg .rdi = s.reg .rdi ∧
      s'.reg .r15 = (((mdByte pk R m 30 * 256 + mdByte pk R m 31) * 256 + mdByte pk R m 32) %
        2 ^ 18 * 256 + mdByte pk R m 33).toUInt64 ∧
      RegsFrame [.rax, .rcx, .r15] s s') E := by
  have b30 := mdByte_lt pk R m 30
  have b31 := mdByte_lt pk R m 31
  have b32 := mdByte_lt pk R m 32
  have b33 := mdByte_lt pk R m 33
  unfold readIndex
  apply WP.blk_cons
  refine WP.mono (digestByte_ok hI (j := 30) (by omega)) (fun s1 h ↦ ?_) (fun _ h ↦ h)
  subst h
  rw [hl.byte (by omega)]
  step
  apply WP.blk_cons
  refine WP.mono (digestByte_ok (by exact hI.frame rfl (by simp)) (j := 31) (by omega))
    (fun s1 h ↦ ?_) (fun _ h ↦ h)
  subst h
  rw [hl.byte (by omega)]
  step; step
  apply WP.blk_cons
  refine WP.mono (digestByte_ok (by exact hI.frame rfl (by simp))
    (j := 32) (by omega)) (fun s1 h ↦ ?_) (fun _ h ↦ h)
  subst h
  rw [hl.byte (by omega)]
  step; step; step
  apply WP.blk_cons
  refine WP.mono (digestByte_ok (by exact hI.frame rfl (by simp))
    (j := 33) (by omega)) (fun s1 h ↦ ?_) (fun _ h ↦ h)
  subst h
  rw [hl.byte (by omega)]
  step; step
  apply WP.blk_nil
  refine ⟨rfl, by simp, ?_, ?_⟩
  · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false]
    exact idx_word b30 b31 b32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

theorem forsLeaf_ok (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey} {R : BitVec 128}
    {m : BitVec 256} (hl : LanesAt V pk R m) {κ : Nat} (hκ : κ < 24) :
    WP (forsLeaf κ) s (fun s' ↦ Inv base (Function.update V (forsLeaves + κ)
      ((mdByte pk R m (10 * κ / 8) * 256 + mdByte pk R m (10 * κ / 8 + 1)) / 2 ^ (6 - 10 * κ % 8) %
        1024).toUInt64) s' ∧ RegsFrame [.rax, .rcx] s s') E := by
  have b0 := mdByte_lt pk R m (10 * κ / 8)
  have b1 := mdByte_lt pk R m (10 * κ / 8 + 1)
  unfold forsLeaf
  apply WP.blk_cons
  refine WP.mono (digestByte_ok hI (j := 10 * κ / 8) (by omega)) (fun s1 h ↦ ?_)
    (fun _ h ↦ h)
  subst h
  rw [hl.byte (by omega)]
  step
  apply WP.blk_cons
  refine WP.mono (digestByte_ok (by exact hI.frame rfl (by simp)) (j := 10 * κ / 8 + 1)
    (by omega)) (fun s1 h ↦ ?_) (fun _ h ↦ h)
  subst h
  rw [hl.byte (by omega)]
  step; step; step
  rw [leaf_word b0 b1 (by omega)]
  refine blk_store_cw (by exact hI.frame rfl (by simp)) (by unfold forsLeaves Context.ctxWords; omega) ?_
  apply WP.blk_nil
  refine ⟨?_, ?_⟩
  · exact (hI.frame (s' := ((s.setReg .rax _).setReg .rcx _).setReg .rax _) rfl (by simp)).setMem
      (by unfold forsLeaves Context.ctxWords; omega) _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

theorem forsLeaves_ok (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey} {R : BitVec 128}
    {m : BitVec 256} (hl : LanesAt V pk R m) :
    WP (blk ((List.range 24).map forsLeaf)) s (fun s' ↦ ∃ V', Inv base V' s' ∧
      (∀ k, ¬(forsLeaves ≤ k ∧ k < forsLeaves + 24) → V' k = V k) ∧
      (∀ κ (hκ : κ < 24), V' (forsLeaves + κ) = (digestForsLeaves (Id.run
        (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R m)) ⟨κ, hκ⟩).val.toUInt64) ∧
      RegsFrame [.rax, .rcx] s s') E := by
  have := wp_blk_forall (E := E) (s := s) (xs := (List.range 24).map forsLeaf)
    (fun n s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬(forsLeaves ≤ k ∧ k < forsLeaves + n) → V' k = V k) ∧
      (∀ κ (hκ : κ < n), V' (forsLeaves + κ) = ((mdByte pk R m (10 * κ / 8) * 256 +
        mdByte pk R m (10 * κ / 8 + 1)) / 2 ^ (6 - 10 * κ % 8) % 1024).toUInt64) ∧
      RegsFrame [.rax, .rcx] s s')
    ⟨V, hI, fun _ _ ↦ rfl, fun κ hκ ↦ absurd hκ (by omega), fun _ _ ↦ rfl⟩ ?_
  · refine WP.mono this (fun s' ⟨V', h, e, d, f⟩ ↦ ⟨V', h, by simpa using e, fun κ hκ ↦ ?_, f⟩)
      (fun _ h ↦ h)
    rw [d κ (by simpa using hκ), digestForsLeaves_val]
  intro n hn s1 ⟨V1, h1, e1, d1, f1⟩
  simp only [List.length_map, List.length_range] at hn
  simp only [List.getElem_map, List.getElem_range]
  have hl1 : LanesAt V1 pk R m := fun k hk ↦ by
    rw [e1 _ (by unfold dgst forsLeaves; omega)]; exact hl k hk
  refine WP.mono (forsLeaf_ok h1 hl1 hn) (fun s2 ⟨h2, f2⟩ ↦ ⟨_, h2, fun k hk ↦ ?_, fun κ hκ ↦ ?_,
    RegsFrame.trans f1 f2⟩) (fun _ h ↦ h)
  · rw [Function.update_of_ne (by omega), e1 k (by omega)]
  · rcases Nat.lt_or_ge κ n with h' | h'
    · rw [Function.update_of_ne (by omega), d1 κ h']
    · rw [show κ = n by omega, Function.update_self]

end X86.SphincsVerifier
