module

public import Native.Sphincs.Tree
public import Native.Sphincs.Digest
public import Native.Sphincs.LayerSpec

/-!
# A layer's key and codeword

The head of `layer`: the key's leaf and tree from `r15` into the address record (`header_ok`),
the encoding hash of `msg` under the layer's counter into scratch words `0, 1` (`encode_ok`), and
the 64 digits of the codeword into `digits`, their sum into `rbp` (`digits_ok`). Blocks split at
any statement (`wp_blk_take_drop`).
-/

@[expose] public section

namespace Native.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {P E : QState → Prop}

/-! ## Splitting a block -/

theorem wp_seq_inv {a b : Stmt} (h : WP (.seq a b) s P E) : WP a s (fun s₁ ↦ WP b s₁ P E) E := by
  obtain ⟨o, hx, ho⟩ := h
  cases hx with
  | seqOk ha hb => exact ⟨_, ha, _, hb, ho⟩
  | seqErr ha => exact ⟨_, ha, ho⟩

theorem wp_blk_cons_inv {x : Stmt} {xs : List Stmt} (h : WP (blk (x :: xs)) s P E) :
    WP x s (fun s₁ ↦ WP (blk xs) s₁ P E) E := by
  cases xs with
  | nil => exact WP.mono h (fun _ h₁ ↦ WP.blk_nil h₁) (fun _ h ↦ h)
  | cons y ys => exact wp_seq_inv h

theorem wp_blk_append : ∀ {xs ys : List Stmt} {s : QState},
    WP (blk xs) s (fun s₁ ↦ WP (blk ys) s₁ P E) E → WP (blk (xs ++ ys)) s P E
  | [], _, _, h => by
    obtain ⟨o, hx, ho⟩ := h
    cases hx
    exact ho
  | _ :: _, _, _, h =>
    WP.blk_cons (WP.mono (wp_blk_cons_inv h) (fun _ h₁ ↦ wp_blk_append h₁) (fun _ h ↦ h))

/-- A block, by its first `n` statements, then the rest. -/
theorem wp_blk_take_drop (n : Nat) {xs : List Stmt}
    (h : WP (blk (xs.take n)) s (fun s₁ ↦ WP (blk (xs.drop n)) s₁ P E) E) : WP (blk xs) s P E := by
  rw [← List.take_append_drop n xs]
  exact wp_blk_append h

/-! ## The key -/

theorem leafOfIndex_val (L : Layer) (idx : Index) :
    (leafOfIndex L idx).val = idx.val / 2 ^ (8 * L.val) % 2 ^ layerHeight L := rfl

theorem treeOfIndex_val (L : Layer) (idx : Index) :
    (treeOfIndex L idx).val = idx.val / 2 ^ (8 * L.val) / 2 ^ layerHeight L := by
  simp only [treeOfIndex, bitsBelowLayer, Nat.pow_add, Nat.div_div_eq_div_mul]

theorem header_regs {L : Layer} {idx : Index} (hr12 : s.reg .r12 = L.val.toUInt64)
    (hr15 : s.reg .r15 = (idx.val / 2 ^ (8 * L.val)).toUInt64) :
    WP (.ite (.cmp .eq .r12 (.imm 2))
        (blk [I (.mov .r10 .r15), I (.andi .r10 1023), I (.mov .r9 .r15), I (.shri .r9 10)])
        (blk [I (.mov .r10 .r15), I (.andi .r10 255), I (.mov .r9 .r15), I (.shri .r9 8)])) s
      (fun s' ↦ s'.mem = s.mem ∧ s'.reg .r10 = (leafOfIndex L idx).val.toUInt64 ∧
        s'.reg .r9 = (treeOfIndex L idx).val.toUInt64 ∧ RegsFrame [.r9, .r10] s s') E := by
  have hL := L.isLt
  have hidx := idx.isLt
  unfold layerCount at hL
  unfold indexBits at hidx
  have hn : idx.val / 2 ^ (8 * L.val) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  apply WP.ite
  rw [cond_eq_imm hr12 (imm_nat 2) (by omega) (by omega)]
  have hf : ∀ r, r ∉ [Reg64.r9, .r10] → ∀ a b : UInt64,
      ((s.setReg .r10 a).setReg .r9 b).reg r = s.reg r := fun r hr a b ↦ by
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), ite_no (fun h ↦ hr (by simp [h]))]
  by_cases h2 : L.val = 2
  · have hh : layerHeight L = 10 := by simp [layerHeight, h2]
    simp only [h2, decide_true, ite_true]
    iterate 4 step
    refine WP.blk_nil ⟨rfl, ?_, ?_, fun r hr ↦ hf r hr _ _⟩
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true, hr15]
      rw [show (1023 : Int64).toUInt64 = (2 ^ 10 - 1 : Nat).toUInt64 from rfl,
        toUInt64_and_mask (by omega) hn, leafOfIndex_val, hh]
    · simp only [QState.setReg_reg, ite_true, hr15]
      rw [toUInt64_shr (by omega) hn, treeOfIndex_val, hh]
  · have hh : layerHeight L = 8 := by simp [layerHeight, h2]
    simp only [h2, decide_false, Bool.false_eq_true, ite_false]
    iterate 4 step
    refine WP.blk_nil ⟨rfl, ?_, ?_, fun r hr ↦ hf r hr _ _⟩
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true, hr15]
      rw [show (255 : Int64).toUInt64 = (2 ^ 8 - 1 : Nat).toUInt64 from rfl,
        toUInt64_and_mask (by omega) hn, leafOfIndex_val, hh]
    · simp only [QState.setReg_reg, ite_true, hr15]
      rw [toUInt64_shr (by omega) hn, treeOfIndex_val, hh]

/-- The key's address record: its layer, tree and leaf, type `WOTS_ENC`. -/
theorem header_ok (hI : Inv base V s) {L : Layer} {idx : Index}
    (hr12 : s.reg .r12 = L.val.toUInt64)
    (hr15 : s.reg .r15 = (idx.val / 2 ^ (8 * L.val)).toUInt64) :
    WP (blk [
      .ite (.cmp .eq .r12 (.imm 2))
        (blk [I (.mov .r10 .r15), I (.andi .r10 1023), I (.mov .r9 .r15), I (.shri .r9 10)])
        (blk [I (.mov .r10 .r15), I (.andi .r10 255), I (.mov .r9 .r15), I (.shri .r9 8)]),
      I (.store (cw adrsRec) .r12), I (.store (cw (adrsRec + 3)) .r9),
      I (.store (cw (adrsRec + 5)) .r10),
      setField 4 7, setField 6 0, setField 7 0]) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧
        (∀ k, (k < adrsRec ∨ adrsRec + 8 ≤ k ∨ k = adrsRec + 1 ∨ k = adrsRec + 2) → V' k = V k) ∧
        V' adrsRec = L.val.toUInt64 ∧ V' (adrsRec + 3) = (treeOfIndex L idx).val.toUInt64 ∧
        V' (adrsRec + 4) = AddressType.wotsEncoding.word.toUInt64 ∧
        V' (adrsRec + 5) = (leafOfIndex L idx).val.toUInt64 ∧
        V' (adrsRec + 6) = (0 : Nat).toUInt64 ∧ V' (adrsRec + 7) = (0 : Nat).toUInt64 ∧
        s'.reg .r10 = (leafOfIndex L idx).val.toUInt64 ∧
        s'.reg .r9 = (treeOfIndex L idx).val.toUInt64 ∧ RegsFrame [.r9, .r10] s s') E := by
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  unfold setField
  apply WP.blk_cons
  refine WP.mono (header_regs hr12 hr15) (fun s1 ⟨m1, r10, r9, f1⟩ ↦ ?_) (fun _ h ↦ h)
  have h1 : Inv base V s1 := hI.frame m1 (f1 .rdi (by simp))
  have r12 : s1.reg .r12 = L.val.toUInt64 := by rw [f1 .r12 (by simp), hr12]
  refine blk_store_cw' h1 (by omega) fun s2 h2 hs2 ↦ ?_
  refine blk_store_cw' h2 (by omega) fun s3 h3 hs3 ↦ ?_
  refine blk_store_cw' h3 (by omega) fun s4 h4 hs4 ↦ ?_
  refine blk_storei_cw' h4 (by omega) fun s5 h5 hs5 ↦ ?_
  refine blk_storei_cw' h5 (by omega) fun s6 h6 hs6 ↦ ?_
  refine blk_storei_cw' h6 (by omega) fun s7 h7 hs7 ↦ ?_
  simp only [hs3, hs2, r10, r9, r12] at h7
  refine WP.blk_nil ⟨_, h7, fun k hk ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self,
      imm_nat]
    rfl
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_self, imm_nat]
  · rw [Function.update_self, imm_nat]
  · rw [hs7, hs6, hs5, hs4, hs3, hs2, r10]
  · rw [hs7, hs6, hs5, hs4, hs3, hs2, r9]
  · intro r hr
    rw [hs7, hs6, hs5, hs4, hs3, hs2, f1 r hr]

/-! ## The encoding hash -/

theorem th_lo (ws : List UInt64) (len : Nat) :
    digestLo (th ws len) = (keccak256 ((wordsBytes ws).take len))[0] := by
  rw [th, digestLo_ofWords]

theorem th_hi (ws : List UInt64) (len : Nat) :
    digestHi (th ws len) = (keccak256 ((wordsBytes ws).take len))[1] := by
  rw [th, digestHi_ofWords]

/-- The bytes past `len` are the payload's past `len - 48`. -/
theorem tweakWords_drop' (V : Nat → UInt64) (buf len : Nat) (h48 : 48 ≤ len) :
    (wordsBytes (tweakWords V buf len)).drop len =
      (wordsBytes (words V (buf + 6) ((len + 7) / 8 - 6))).drop (len - 48) := by
  have h : (wordsBytes ([V buf, V (buf + 1)] ++ adrsWords V)).length = 48 := by
    rw [wordsBytes_length]; simp [adrsWords]
  rw [tweakWords, wordsBytes_append, List.drop_append, h, List.drop_of_length_le (by omega),
    List.nil_append]

theorem encode_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) {L : Layer} {tree : TreeIndex}
    {leaf : TreeLeafIndex} {d : Digest}
    (hA : AdrsAt V L.val tree.val .wotsEncoding leaf.val 0 0)
    (hm0 : V msg = digestLo d) (hm1 : V (msg + 1) = digestHi d)
    (hr11 : s.reg .r11 = (145 * L.val).toUInt64) :
    WP (blk [mv2 msg (smallBuf + 6),
      I (.load .rax (cwi .r11 666)), be32, I (.store (cw (smallBuf + 8)) .rax),
      adrs smallBuf, hashAt smallBuf 68]) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧
        (∀ k, scratchWords ≤ k → (k < smallBuf + 2 ∨ smallBuf + 9 ≤ k) → V' k = V k) ∧
        V' 0 = digestLo (encDigest pk.publicSeed L tree leaf d (sig.layers L).counter) ∧
        V' 1 = digestHi (encDigest pk.publicSeed L tree leaf d (sig.layers L).counter) ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E := by
  have hL := L.isLt
  have htr := tree.isLt
  have hlf := leaf.isLt
  unfold layerCount at hL
  unfold indexBits at htr
  have hlf' : leaf.val < 2 ^ 32 := Nat.lt_of_lt_of_le hlf
    (Nat.pow_le_pow_right (by decide) (by unfold layerHeight topLayer; split <;> decide))
  have hctx : Context.ctxWords = 3200 := rfl
  have har : adrsRec = 1200 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hmsg : msg = 1208 := rfl
  have hsw : scratchWords = 84 := rfl
  apply WP.blk_cons
  refine WP.mono (mv2_ok hI (src := msg) (dst := smallBuf + 6) (by omega) (by omega) (by omega))
    (fun s1 ⟨h1, f1⟩ ↦ ?_) (fun _ h ↦ h)
  rw [show smallBuf + 6 + 1 = smallBuf + 7 from rfl] at h1
  obtain ⟨V1, hV1⟩ : ∃ V1, V1 = Function.update (Function.update V (smallBuf + 6) (V msg))
      (smallBuf + 7) (V (msg + 1)) := ⟨_, rfl⟩
  rw [← hV1] at h1
  have e1 : ∀ k, k ≠ smallBuf + 6 → k ≠ smallBuf + 7 → V1 k = V k := fun k h6 h7 ↦ by
    rw [hV1, Function.update_of_ne h7, Function.update_of_ne h6]
  have r11 : s1.reg .r11 = (145 * L.val).toUInt64 := by rw [f1 .r11 (by simp), hr11]
  refine blk_load_cwi h1 r11 (by omega) ?_
  rw [e1 _ (by omega) (by omega), show 145 * L.val + 666 = inp + (layerOff L.val + 0) by
    unfold inp layerOff; omega, hS.layer L (by omega), layerWord_counter]
  apply WP.blk_cons
  refine WP.mono (be32_ok _) (fun s2 ⟨m2, r2, f2⟩ ↦ ?_) (fun _ h ↦ h)
  have h2 : Inv base V1 s2 := (h1.setReg (by decide) _).frame m2 (f2 .rdi (by simp))
  refine blk_store_cw' h2 (by omega) fun s3 h3 hs3 ↦ ?_
  rw [r2] at h3
  simp only [QState.setReg_reg, ite_true] at h3
  obtain ⟨V3, hV3⟩ : ∃ V3, V3 = Function.update V1 (smallBuf + 8)
      (bs (sig.layers L).counter.toNat.toUInt64) := ⟨_, rfl⟩
  rw [← hV3] at h3
  have e3 : ∀ k, k ≠ smallBuf + 6 → k ≠ smallBuf + 7 → k ≠ smallBuf + 8 → V3 k = V k :=
    fun k h6 h7 h8 ↦ by rw [hV3, Function.update_of_ne h8, e1 k h6 h7]
  have hA3 : AdrsAt V3 L.val tree.val .wotsEncoding leaf.val 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.layer
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.zero1
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.zero2
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.tree
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.type
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.keyPair
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.ch
    · rw [e3 _ (by omega) (by omega) (by omega)]; exact hA.hx
  have hpay : words V3 (smallBuf + 6) 3 =
      [digestLo d, digestHi d, bs (sig.layers L).counter.toNat.toUInt64] := by
    simp only [words, show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil,
      Nat.add_zero, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩
    · rw [hV3, Function.update_of_ne (by omega), hV1, Function.update_of_ne (by omega),
        Function.update_self, hm0]
    · rw [hV3, Function.update_of_ne (by omega), hV1, Function.update_self, hm1]
    · rw [hV3, Function.update_self]
  have hth : th (tweakWords V3 smallBuf 68) 68 =
      encDigest pk.publicSeed L tree leaf d (sig.layers L).counter := by
    rw [encDigest, th_tweakWords hA3 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [e3 _ (by omega) (by omega) (by omega)]; exact hS.small0)
      (by rw [e3 _ (by omega) (by omega) (by omega)]; exact hS.small1) ?_ (by omega)]
    rw [show (68 + 7) / 8 - 6 = 3 from rfl, hpay]
    exact encPayload_take d _
  apply WP.blk_cons
  refine WP.mono (adrs_ok h3 (buf := smallBuf) (by omega) (Or.inr (by omega)))
    (fun s4 ⟨V4, h4, e4, a4, f4⟩ ↦ ?_) (fun _ h ↦ h)
  have hw : words V4 smallBuf ((68 + 7) / 8) = tweakWords V3 smallBuf 68 := by
    unfold tweakWords adrsWords
    rw [show (68 + 7) / 8 = 6 + 3 from rfl, show (68 + 7) / 8 - 6 = 3 from rfl, words_add]
    congr 1
    · simp only [words, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl,
        show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.cons.injEq, and_true]
      exact ⟨e4 _ (by omega), e4 _ (by omega), a4 0 (by omega), a4 1 (by omega), a4 2 (by omega),
        a4 3 (by omega)⟩
    · exact words_congr fun i _ ↦ e4 _ (by omega)
  refine WP.mono (hashAt_ok hb h4 (buf := smallBuf) (len := 68) (by omega) (by omega) (by omega)
    (by omega) ?_) (fun s5 ⟨V5, h5, e5, d5, f5⟩ ↦ ⟨V5, h5, fun k hk hk' ↦ ?_, ?_, ?_, ?_⟩)
    (fun _ h ↦ h)
  · rw [hw, tweakWords_drop' _ _ _ (by omega), show (68 + 7) / 8 - 6 = 3 from rfl, hpay]
    exact encPayload_drop d _
  · rw [e5 k hk, e4 k (by omega), e3 k (by omega) (by omega) (by omega)]
  · rw [d5 0 (by omega), hw, ← hth, th_lo]
  · rw [d5 1 (by omega), hw, ← hth, th_hi]
  · intro r hr
    rw [f5 r hr, f4 r (fun h ↦ hr (by simp_all)), hs3, f2 r (fun h ↦ hr (by simp_all))]
    simp only [QState.setReg_reg]
    rw [ite_no (fun h ↦ hr (by simp [h])), f1 r (fun h ↦ hr (by simp_all))]

/-! ## The digits -/

/-- Digit `j` of the codeword of `D`, `0` past the 64th. -/
def digitOf (D : Digest) (j : Nat) : Nat :=
  if h : j < 64 then (TargetSum.base2bDigits D ⟨j, h⟩).val else 0

theorem digitOf_lt (D : Digest) (j : Nat) : digitOf D j < 4 := by
  unfold digitOf
  split
  · exact (TargetSum.base2bDigits D _).isLt
  · omega

theorem digit_word (x : UInt64) {n : Nat} (hn : n < 64) :
    (x >>> n.toUInt64) &&& (3 : Int64).toUInt64 = (x.toNat / 2 ^ n % 4).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [show (3 : Int64).toUInt64 = (2 ^ 2 - 1 : Nat).toUInt64 from rfl, toNat_shr_and x hn (by omega),
    toNat_toUInt64' (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))]
  rfl

theorem sum_digitOf (D : Digest) :
    ∑ j ∈ Finset.range 64, digitOf D j = TargetSum.sum (TargetSum.base2bDigits D) := by
  rw [TargetSum.sum, ← Fin.sum_univ_eq_sum_range]
  show ∑ i : Fin chainCount, digitOf D i.val = _
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold digitOf
  rw [dite_yes (show i.val < 64 from i.isLt)]

theorem digits_ok (hI : Inv base V s) {D : Digest} (hw0 : V 0 = digestLo D)
    (hw1 : V 1 = digestHi D) :
    WP (blk [I (.movi .rbp 0), blk ((List.range 64).map digit)]) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, ¬(digits ≤ k ∧ k < digits + 64) → V' k = V k) ∧
        (∀ i : ChainIndex, V' (digits + i.val) = (TargetSum.base2bDigits D i).val.toUInt64) ∧
        s'.reg .rbp = (TargetSum.sum (TargetSum.base2bDigits D)).toUInt64 ∧
        RegsFrame [.rax, .rbp] s s') E := by
  have hctx : Context.ctxWords = 3200 := rfl
  have hdg : digits = 1216 := rfl
  step
  apply WP.blk_cons
  refine WP.mono (wp_blk_forall (fun n s' ↦ ∃ V', Inv base V' s' ∧
      (∀ k, ¬(digits ≤ k ∧ k < digits + n) → V' k = V k) ∧
      (∀ j < n, V' (digits + j) = (digitOf D j).toUInt64) ∧
      s'.reg .rbp = (∑ j ∈ Finset.range n, digitOf D j).toUInt64 ∧ RegsFrame [.rax, .rbp] s s')
    ⟨V, hI.setReg (by decide) _, fun _ _ ↦ rfl, fun j hj ↦ absurd hj (by omega),
      by simp only [QState.setReg_reg, ite_true, Finset.range_zero, Finset.sum_empty]; rfl,
      RegsFrame.setReg (by simp) _⟩ ?_) (fun s' h ↦ WP.blk_nil ?_) (fun _ h ↦ h)
  · intro i hi s1 ⟨V1, h1, e1, d1, r1, f1⟩
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    have hsum : ∑ j ∈ Finset.range i, digitOf D j < 2 ^ 64 := by
      have : ∑ j ∈ Finset.range i, digitOf D j ≤ ∑ j ∈ Finset.range i, 3 :=
        Finset.sum_le_sum fun j _ ↦ Nat.le_of_lt_succ (digitOf_lt D j)
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
      omega
    have hsh : (8 * (i / 4) + 6 - 2 * (i % 4)) % 64 < 64 := Nat.mod_lt _ (by omega)
    have hword : V1 (i / 32) = digestWord D (i / 32) := by
      rw [e1 _ (by omega)]
      rcases (by omega : i / 32 = 0 ∨ i / 32 = 1) with h | h <;> rw [h]
      · exact hw0
      · exact hw1
    have hdig : ((digestWord D (i / 32)).toNat / 2 ^ ((8 * (i / 4) + 6 - 2 * (i % 4)) % 64) % 4) =
        digitOf D i := by
      rw [digitOf, dite_yes hi, base2bDigits_val]
    unfold digit
    refine blk_load_cw h1 (by omega) ?_
    step; step
    rw [hword, digit_word _ hsh, hdig]
    refine blk_store_cw' (h1.setReg (by decide) _) (by omega) fun s2 h2 hs2 ↦ ?_
    simp only [QState.setReg_reg, ite_true] at h2
    step
    rw [hs2]
    simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true, r1]
    rw [toUInt64_add, ← Finset.sum_range_succ]
    apply WP.blk_nil
    refine ⟨_, h2.setReg (by decide) _, fun k hk ↦ ?_, fun j hj ↦ ?_, by simp, ?_⟩
    · rw [Function.update_of_ne (by omega), e1 k (by omega)]
    · rcases Nat.lt_or_ge j i with h | h
      · rw [Function.update_of_ne (by omega), d1 j h]
      · rw [show j = i by omega, Function.update_self]
    · intro r hr
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), hs2]
      simp only [QState.setReg_reg]
      rw [ite_no (fun h ↦ hr (by simp [h])), f1 r hr]
  · obtain ⟨V1, h1, e1, d1, r1, f1⟩ := h
    simp only [List.length_map, List.length_range] at e1 d1 r1
    refine ⟨V1, h1, e1, fun i ↦ ?_, by rw [r1, sum_digitOf], f1⟩
    rw [d1 i.val i.isLt, digitOf, dite_yes (show i.val < 64 from i.isLt)]

end Native.SphincsVerifier
