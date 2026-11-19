module

public import NativeVm.Wire.Tables
public import NativeVm.Wire.ModelSpec

/-!
# The leaves' digests

`leafHashes` hashes the leaf at each distinct position (`hashCall`, the leaf's `lw` words as
`8 lw` bytes, `keccak256` of the leaf's `K.toBytes`) and writes the position with its digest into
the level-`0` node table, then the node count (`leafHashes_ok`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Wire
open Native.SphincsVerifier (toUInt64_shl cond_ltu_reg)

theorem leaves_workWords_lt : workWords < 2 ^ 32 := by
  unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; norm_num

theorem leaves_shl {a n : Nat} (hn : n < 64) (h : a < 2 ^ 32) (hn' : n ≤ 8) :
    a.toUInt64 <<< n.toUInt64 = (2 ^ n * a).toUInt64 := by
  rw [toUInt64_shl hn (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos n))
    (by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))), Nat.mul_comm]

theorem leaves_dw (d : Digest) {k : Nat} (hk : k < 4) : dw d k = d[k] := by
  simp [dw, List.getD_eq_getElem?_getD, hk]

/-- The bytes `hashCall` hashes for a leaf of `lw` words. -/
theorem leaves_bytes {W : Nat → UInt64} {b lw : Nat} {l : List K} (hl : l.length = lw)
    (hW : ∀ t < lw, W (b + t) = (l.getD t 0).lane) :
    (wordsBytes (wordsOf W b ((8 * lw + 7) / 8))).take (8 * lw) = l.flatMap K.toBytes := by
  have h8 : (8 * lw + 7) / 8 = lw := by omega
  have hw : wordsOf W b lw = l.map K.lane := by
    apply List.ext_getElem (by simp [wordsOf_length, hl])
    intro t h1 h2
    rw [wordsOf_length] at h1
    simp only [wordsOf, List.getElem_map, List.getElem_range, hW t h1]
    simp [List.getD_eq_getElem?_getD, hl ▸ h1]
  rw [h8, hw, List.take_of_length_le (by rw [length_wordsBytes, List.length_map, hl])]
  simp only [wordsBytes, List.flatMap_map]
  rfl

section Run

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

omit P in
theorem Inv.leavesOf {t t' : QState} (h : Inv e t D W) (hm : t'.mem = t.mem)
    (hr : t'.reg .rdi = t.reg .rdi) : Inv e t' D W :=
  ⟨hr.trans h.rdi, fun a ha ↦ hm ▸ h.out a ha, fun k hk ↦ hm ▸ h.scr k hk,
    fun k hk ↦ hm ▸ h.dec k hk, fun k hk ↦ hm ▸ h.work k hk⟩

/-- `nodeAddr`: `rsi` at the node table's entry `rbp`. -/
theorem leaves_nodeAddr (hI : Inv e s D W) {i : Nat} (hbp : s.reg .rbp = i.toUInt64)
    (hi : i < 2 ^ 32) :
    WP nodeAddr s (fun s' ↦ s'.mem = s.mem ∧ s'.reg .rsi = adr e.wk (wNode + 5 * i) ∧
      RegsFrame [.rax, .rsi] s s') F := by
  unfold nodeAddr
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  step; step; step; step
  apply WP.blk_nil
  refine ⟨rfl, ?_, ?_⟩
  · have h4 : i.toUInt64 <<< (2 : Nat).toUInt64 + i.toUInt64 = (5 * i).toUInt64 := by
      rw [leaves_shl (by norm_num) hi (by norm_num), SphincsVerifier.toUInt64_add]
      congr 1; omega
    simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, hbp, h4]
    rw [eval_ix _ .rsi .rax (a := e.wk) (j := 0) (n := 5 * i) (by simp [adr_zero])
      (by simp) wNode]
    congr 1; omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

/-- **`leafHashes`**: each distinct position with its leaf's digest into the level-`0` node
table, the node count into `wN`. -/
theorem leafHashes_ok (hI : Inv e s D W) {lw : Nat} {ps : List Nat} {leaves : List (List K)}
    (hr12 : s.reg .r12 = lw.toUInt64) (hr10 : s.reg .r10 = ps.length.toUInt64)
    (hlw : lw ≤ wireMaxLeafWords) (hn : ps.length ≤ wireMaxQueries)
    (hps : Tab W wP (ps.map Nat.toUInt64)) (hl : leaves.length = ps.length)
    (hll : ∀ l ∈ leaves, l.length = lw) (hleaf : LeafTab W leaves lw) :
    WP leafHashes s (fun s' ↦ ∃ W', Inv e s' D W' ∧
      NodeTab W' wNode (ps.zip (leaves.map fun l ↦ keccak256 (l.flatMap K.toBytes))) ∧
      W' wN = ps.length.toUInt64 ∧
      Same (fun k ↦ k = wN ∨ (wNode ≤ k ∧ k < wNode + 5 * wireMaxQueries)) W W' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp] s s') F := by
  have hw := leaves_workWords_lt
  have hlw' : lw ≤ 64 := hlw
  have hn' : ps.length ≤ 256 := hn
  have hWQ : wireMaxQueries = 256 := rfl
  have hLW : wLeaf + 64 * 256 = workWords := rfl
  set n := ps.length with hn_def
  set nodes := ps.zip (leaves.map fun l ↦ keccak256 (l.flatMap K.toBytes)) with hnodes
  have hlen : nodes.length = n := by simp [hnodes, hl]; omega
  have hget : ∀ j (hj : j < n), nodes[j]'(hlen ▸ hj) =
      (ps[j], keccak256 ((leaves[j]'(hl ▸ hj)).flatMap K.toBytes)) := fun j hj ↦ by
    simp [hnodes]
  unfold leafHashes
  step
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ ∃ i, i ≤ n ∧ ∃ W', Inv e t D W' ∧
    NodeTab W' wNode (nodes.take i) ∧
    Same (fun k ↦ wNode ≤ k ∧ k < wNode + 5 * wireMaxQueries) W W' ∧ t.reg .rbp = i.toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp] s t
  refine WP.loop Iv (fun t ↦ n - (t.reg .rbp).toNat) ⟨0, by omega, W, hI.setReg (by decide) _,
    fun j hj ↦ absurd hj (by simp), Same.refl _ _, rfl, ?_⟩ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.2.2.2.2.2]
  · intro t ⟨i, hin, W', hIt, hnt, hS, hbp, hft⟩ hcnd
    have h10 : t.reg .r10 = n.toUInt64 := by rw [hft .r10 (by simp), hr10]
    have hi : i < n := by
      rw [cond_ltu_reg hbp h10 (by omega) (by omega)] at hcnd
      simpa using hcnd
    have hW'leaf : ∀ t' < lw, W' (wLeaf + 64 * i + t') = ((leaves[i]'(hl ▸ hi)).getD t' 0).lane :=
      fun t' ht' ↦ by
        rw [hS _ (by unfold wLeaf wSib wSibN wPar at *; omega)]
        exact hleaf i (hl ▸ hi) t' ht'
    have hW'p : W' (wP + i) = (ps[i]).toUInt64 := by
      rw [hS _ (by unfold wNode wFL at *; omega)]
      have := hps i (by simpa using hi)
      rw [List.getElem_map] at this
      exact this
    refine blk_load_ctx P hIt (eval_cw t hIt.rdi cWork) (by decide) P.c10 ?_
    step; step; step; step; step
    have h6 : i.toUInt64 <<< (6 : Nat).toUInt64 = (64 * i).toUInt64 := leaves_shl (by norm_num)
      (by omega) (by norm_num)
    have h3 : lw.toUInt64 <<< (3 : Nat).toUInt64 = (8 * lw).toUInt64 := leaves_shl (by norm_num)
      (by omega) (by norm_num)
    apply WP.blk_cons
    refine WP.mono (hashCall_ok P ((((hIt.setReg (d := .rsi) (by decide) _).setReg (d := .rax)
      (by decide) _).setReg (d := .rsi) (by decide) _).setReg (d := .rbx) (by decide) _)
      (b := wLeaf + 64 * i) (len := 8 * lw)
      ?_ ?_ (by omega) (by omega) ?_)
      (fun t1 ⟨h1, hd1, hf1⟩ ↦ ?_) (fun _ h ↦ h)
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true]
      rw [eval_ix _ .rsi .rax (a := e.wk) (j := 0) (n := 64 * i) (by simp [adr_zero])
        (by simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false]; rw [hbp, h6]) wLeaf]
      congr 1; omega
    · simp only [QState.setReg_reg, ite_true]
      rw [hft .r12 (by simp), hr12, h3]
    · rw [show (8 * lw + 7) / 8 = lw by omega]
      refine ⟨by rw [wordsOf_length]; omega, fun x hx ↦ ?_⟩
      rw [List.drop_of_length_le (by rw [length_wordsBytes, wordsOf_length])] at hx
      simp at hx
    have hdig := leaves_bytes (W := W') (b := wLeaf + 64 * i) (hll _ (List.getElem_mem _))
      hW'leaf
    rw [hdig] at hd1
    have hb1 : t1.reg .rbp = i.toUInt64 := by rw [hf1 .rbp (by simp)]; simp [hbp]
    have hdi1 : t1.reg .rdi = e.x := h1.rdi
    apply WP.blk_cons
    refine WP.mono (leaves_nodeAddr P h1 hb1 (by omega)) (fun t2 ⟨hm2, hsi2, hf2⟩ ↦ ?_)
      (fun _ h ↦ h)
    have h2 : Inv e t2 D W' := h1.leavesOf hm2 (hf2 .rdi (by simp))
    have hb2 : t2.reg .rbp = i.toUInt64 := by rw [hf2 .rbp (by simp), hb1]
    have hk5 : wNode + 5 * i + 5 ≤ workWords := by
      unfold workWords wLeaf wSib wSibN wPar; omega
    have hscr : 4 ≤ scratchWords := by unfold scratchWords; omega
    refine blk_load_ctx P h2 (eval_cw t2 h2.rdi cWork) (by decide) P.c10 ?_
    refine blk_load_work (h2.setReg (by decide) _) (k := wP + i) ?_
      (by unfold wNode wFL at *; omega) ?_
    · rw [eval_ix _ .rcx .rbp (a := e.wk) (j := 0) (n := i) (by simp [adr_zero]) (by simp [hb2]) wP]
      congr 1; omega
    rw [hW'p]
    refine wp_store (a := adr e.wk (wNode + 5 * i)) ?_ ?_ ?_
    · rw [eval_rw']; simp [hsi2]
    · simp [h2.work _ (show wNode + 5 * i < workWords by omega)]
    simp only [QState.setReg_reg, ite_true, QState.setReg_setReg_same]
    have h4 := (h2.setReg (d := .rcx) (by decide) (ps[i]).toUInt64).storeWork P
      (show wNode + 5 * i < workWords by omega) (ps[i]).toUInt64
    apply WP.blk_cons
    refine WP.mono (copy4_work P h4 (src := .rdi) (dst := .rsi) (by decide) (by decide) (i := cScr)
      (j := 1) (J := wNode + 5 * i) (A := e.x)
      (v := fun l ↦ dw (keccak256 ((leaves[i]'(hl ▸ hi)).flatMap K.toBytes)) l)
      (by simp [h2.rdi]) (by simp [hsi2]) (by omega) (fun l hl' ↦ ?_) (fun l hl' l' hl'' ↦ ?_))
      (fun t5 ⟨h5, hf5, _⟩ ↦ ?_) (fun _ h ↦ h)
    · show ((t2.setReg .rcx _).setMem _ _).mem (adr e.x (cScr + l)) = _
      rw [QState.setMem_mem, ite_no (P.scr_ne_work (by omega) (by omega)), QState.setReg_mem, hm2,
        hd1 l hl', leaves_dw _ hl']
    · exact P.scr_ne_work (show l < scratchWords by omega) (by omega)
    step
    apply WP.blk_nil
    have hb5 : t5.reg .rbp = i.toUInt64 := by rw [hf5 .rbp (by simp)]; simp [hb2]
    refine ⟨⟨i + 1, by omega, _, h5.setReg (by decide) _, fun j hj ↦ ?_, fun k hk ↦ ?_, ?_, ?_⟩, ?_⟩
    · have hj' : j < i + 1 := by simp at hj; omega
      simp only [List.getElem_take]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj'' | rfl
      · obtain ⟨ha, hb⟩ := hnt j (by simp; omega)
        simp only [List.getElem_take] at ha hb
        refine ⟨?_, fun k hk ↦ ?_⟩
        · simp only [put4]
          rw [ite_no (by omega), Function.update_of_ne (by omega)]
          exact ha
        · simp only [put4]
          rw [ite_no (by omega), Function.update_of_ne (by omega)]
          exact hb k hk
      · rw [hget j (by omega)]
        refine ⟨?_, fun k hk ↦ ?_⟩
        · simp only [put4]
          rw [ite_no (by omega), Function.update_self]
        · simp only [put4]
          rw [ite_yes (by omega)]
          congr 1; omega
    · simp only [put4]
      rw [ite_no (by omega), Function.update_of_ne (by omega)]
      exact hS k hk
    · simp only [QState.setReg_reg, ite_true, hb5]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl, SphincsVerifier.toUInt64_add]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨ha, hb, hc, hd, hsi, h8, hbp'⟩ := hr
      simp only [QState.setReg_reg, hbp', ite_false]
      rw [hf5 r (by simp [ha]), QState.setMem_reg, QState.setReg_reg, ite_no hc,
        hf2 r (by simp [ha, hsi]), hf1 r (by simp [ha, hb, hc, hd, hsi, h8])]
      simp only [QState.setReg_reg, hb, hsi, ha, ite_false]
      exact hft r (by simp [ha, hb, hc, hd, hsi, h8, hbp'])
    · simp only [QState.setReg_reg, ite_true, hb5, hbp]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl, SphincsVerifier.toUInt64_add,
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hin, W', hIt, hnt, hS, hbp, hft⟩ hcnd
    have h10 : t.reg .r10 = n.toUInt64 := by rw [hft .r10 (by simp), hr10]
    have hi : i = n := by
      rw [cond_ltu_reg hbp h10 (by omega) (by omega)] at hcnd
      simp at hcnd; omega
    subst hi
    rw [List.take_of_length_le (by omega)] at hnt
    refine blk_load_ctx P hIt (eval_cw t hIt.rdi cWork) (by decide) P.c10 ?_
    refine blk_store_work P (hIt.setReg (by decide) _) (k := wN)
      (by rw [eval_rw (a := e.wk) (j := 0) _ _ (by simp [adr_zero])]; rfl) (by decide)
      fun t' h' r' ↦ WP.blk_nil ⟨_, h', fun j hj ↦ ?_, by simp [h10], ?_, ?_⟩
    · obtain ⟨ha, hb⟩ := hnt j hj
      refine ⟨by rw [Function.update_of_ne (by unfold wNode wFL wP wQ wN; omega)]; exact ha,
        fun k hk ↦ ?_⟩
      rw [Function.update_of_ne (by unfold wNode wFL wP wQ wN; omega)]
      exact hb k hk
    · intro k hk
      simp only [not_or] at hk
      rw [Function.update_of_ne hk.1]
      exact hS k hk.2
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [r']
      simp only [QState.setReg_reg, hr.1, ite_false]
      exact hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2])

end Run

end NativeVm.Wire
