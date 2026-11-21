module

public import NativeVm.Wire.Tables
public import NativeVm.Wire.ModelSpec

/-!
# The distinct positions

`sortQ` sorts the queries into the distinct positions by insertion, as the model's `sortD` does
(`sortQ_ok`): each query absent from the positions so far is inserted by `insertQ`, which shifts the
larger positions up one word (`insertQ_ok`). An insertion is `insD` cut where the positions below
the query end (`insD_split`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Wire
open Native.SphincsVerifier (toUInt64_inj cond_ne_imm cond_ltu_reg)

/-! ## The model -/

/-- `insD` puts `x` after the positions below it. -/
theorem insD_split (x : Nat) : ∀ (l : List Nat) (c : Nat), (∀ y ∈ l.take c, y < x) →
    (∀ y ∈ l.drop c, x < y) → insD l x = l.take c ++ x :: l.drop c
  | [], _, _, _ => by simp [insD]
  | a :: l, 0, _, h2 => by
    have : x < a := h2 a (by simp)
    simp [insD, this]
  | a :: l, c + 1, h1, h2 => by
    have ha : a < x := h1 a (by simp)
    rw [insD, ite_no (by omega), ite_no (by omega),
      insD_split x l c (fun y hy ↦ h1 y (by simp [hy])) (fun y hy ↦ h2 y (by simpa using hy))]
    simp

theorem insD_of_mem (x : Nat) : ∀ l : List Nat, l.Pairwise (· < ·) → x ∈ l → insD l x = l
  | [], _, h => by simp at h
  | a :: l, hp, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [insD]
    · have : a < x := List.rel_of_pairwise_cons hp h
      rw [insD, ite_no (by omega), ite_no (by omega), insD_of_mem x l hp.of_cons h]

theorem length_insD (x : Nat) : ∀ l : List Nat, (insD l x).length ≤ l.length + 1
  | [] => by simp [insD]
  | a :: l => by
    unfold insD
    split
    · simp
    · split
      · simp
      · have := length_insD x l
        simp only [List.length_cons]
        omega

theorem length_insD_of_not_mem (x : Nat) : ∀ l : List Nat, x ∉ l → (insD l x).length = l.length + 1
  | [], _ => by simp [insD]
  | a :: l, h => by
    have ha : x ≠ a := fun e ↦ h (by simp [e])
    unfold insD
    split
    · simp
    · rw [List.length_cons, List.length_cons,
        length_insD_of_not_mem x l (fun h' ↦ h (List.mem_cons_of_mem a h'))]

theorem length_foldl_insD (qs : List Nat) :
    ∀ l : List Nat, (qs.foldl insD l).length ≤ l.length + qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    intro l
    have h1 := ih (insD l q)
    have h2 := length_insD q l
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem length_sortD (qs : List Nat) : (sortD qs).length ≤ qs.length := by
  simpa [sortD] using length_foldl_insD qs []

theorem sortD_take_succ (qs : List Nat) {i : Nat} (h : i < qs.length) :
    sortD (qs.take (i + 1)) = insD (sortD (qs.take i)) qs[i] := by
  rw [sortD, sortD, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.foldl_append]
  rfl

theorem pairwise_sortD (qs : List Nat) : (sortD qs).Pairwise (· < ·) :=
  (sortD_aux qs [] List.Pairwise.nil).1

theorem mem_sortD {qs : List Nat} {y : Nat} (h : y ∈ sortD qs) : y ∈ qs := by
  have := ((sortD_aux qs [] List.Pairwise.nil).2 y).1 h
  simpa using this

/-! ## Addresses and conditions -/

theorem sortQ_eval_idx {s : QState} {b i : Reg64} {a : UInt64} {j n : Nat}
    (hb : s.reg b = adr a j) (hi : s.reg i = n.toUInt64) :
    ({ base := b, idx := some (i, .W64) } : Addr).eval s = adr a (j + n) := by
  exact eval_ix s b i hb hi 0

theorem sortQ_eval_idx8 {s : QState} {b i : Reg64} {a : UInt64} {j n : Nat}
    (hb : s.reg b = adr a j) (hi : s.reg i = (n + 1).toUInt64) :
    ({ base := b, idx := some (i, .W64), disp := -8 } : Addr).eval s = adr a (j + n) := by
  have h := eval_ix s b i hb hi 0
  simp only [Addr.eval, hb, hi] at h ⊢
  rw [show (wd 0).toUInt64 = 0 from rfl, UInt64.add_zero, Nat.add_zero, ← Nat.add_assoc,
    ← adr_succ] at h
  rw [h, UInt64.add_assoc, show (8 : UInt64) + (-8 : Int64).toUInt64 = 0 from rfl,
    UInt64.add_zero]

theorem sortQ_cond_eq_reg {s : QState} {r r' : Reg64} {n K : Nat} (hr : s.reg r = n.toUInt64)
    (hk : s.reg r' = K.toUInt64) (hn : n < 2 ^ 64) (hK : K < 2 ^ 64) :
    (Cond.cmp .eq r (.reg r')).eval s = decide (n = K) := by
  simp only [Cond.eval, Rhs.eval, hr, hk]
  by_cases h : n = K
  · subst h; simp
  · simp only [h, decide_false]
    exact beq_false_of_ne fun h' ↦ h (toUInt64_inj hn hK h')

section Run

variable {e : Env} (P : Pre e)
include P
variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

/-- **`insertQ`**: `x`, absent from the ascending positions `l` at `wP`, inserted among them. -/
theorem insertQ_ok (hI : Inv e s D W) {l : List Nat} {x : Nat} (hl : l.Pairwise (· < ·))
    (hx : x ∉ l) (hl32 : ∀ y ∈ l, y < 2 ^ 32) (hx32 : x < 2 ^ 32) (hm : l.length < wireMaxQueries)
    (hrsi : s.reg .rsi = adr e.wk wP) (hrax : s.reg .rax = x.toUInt64)
    (hr10 : s.reg .r10 = l.length.toUInt64) (hT : Tab W wP (l.map Nat.toUInt64)) :
    WP insertQ s (fun s' ↦ ∃ W', Inv e s' D W' ∧ Tab W' wP ((insD l x).map Nat.toUInt64) ∧
      Same (fun k ↦ wP ≤ k ∧ k < wP + wireMaxQueries) W W' ∧
      s'.reg .r10 = (l.length + 1).toUInt64 ∧ RegsFrame [.rbx, .rcx, .rdx, .r10] s s') F := by
  have hw : wP + wireMaxQueries ≤ workWords := by
    unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ wireMaxQueries; norm_num
  have hq : wireMaxQueries = 256 := rfl
  have hT' : ∀ k (h : k < l.length), W (wP + k) = l[k].toUInt64 := fun k h ↦ by
    rw [hT k (by simpa using h), List.getElem_map]
  unfold insertQ
  step; step
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ ∃ c W', c ≤ l.length ∧ Inv e t D W' ∧
    Same (fun k ↦ wP ≤ k ∧ k < wP + wireMaxQueries) W W' ∧
    (∀ k (h : k < l.length), k < c → W' (wP + k) = l[k].toUInt64) ∧
    (∀ k (h : k < l.length), c ≤ k → W' (wP + k + 1) = l[k].toUInt64) ∧
    (∀ k (h : k < l.length), c ≤ k → x < l[k]) ∧
    t.reg .rsi = adr e.wk wP ∧ t.reg .rax = x.toUInt64 ∧ t.reg .r10 = l.length.toUInt64 ∧
    RegsFrame [.rbx, .rcx, .rdx] s t ∧
    ((t.reg .rcx = c.toUInt64 ∧ t.reg .rdx = 0) ∨
      (t.reg .rcx = 0 ∧ t.reg .rdx = c.toUInt64 ∧ ∀ k (h : k < l.length), k < c → l[k] < x))
  have h0 : (0 : Int64).toUInt64 = (0 : Nat).toUInt64 := rfl
  have h1' : (1 : Int64).toUInt64 = (1 : Nat).toUInt64 := rfl
  refine WP.loop Iv (fun t ↦ (t.reg .rcx).toNat) ?_ ?_ ?_
  · refine ⟨l.length, W, le_rfl, (hI.setReg (by decide) _).setReg (by decide) _, Same.refl _ _,
      fun k h _ ↦ hT' k h, fun k h hk ↦ absurd hk (by omega), fun k h hk ↦ absurd hk (by omega),
      by simp [hrsi], by simp [hrax], by simp [hr10], ?_, Or.inl ⟨by simp [hr10], by simp [h0]⟩⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.1, hr.2.2]
  · intro t ⟨c, W', hc, hIt, hS, hlo, hhi, hgt, hsi, hax, h10, hf, hd⟩ hcond
    rcases hd with ⟨hcx, hdx⟩ | ⟨hcx, _, _⟩
    swap
    · rw [cond_ne_imm (n := 0) (by simpa using hcx) h0 (by omega) (by omega)] at hcond
      simp at hcond
    rw [cond_ne_imm hcx h0 (by omega) (by omega)] at hcond
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by simp at hcond; omega⟩
    have hc' : c' < l.length := by omega
    refine blk_load_work hIt (k := wP + c') (sortQ_eval_idx8 hsi hcx) (by omega) ?_
    rw [hlo c' hc' (by omega)]
    apply WP.blk_cons
    apply WP.ite
    rw [cond_ltu_reg (n := x) (K := l[c']) (by simp [hax]) (by simp) (by omega)
      (by have := hl32 _ (List.getElem_mem hc'); omega)]
    by_cases hlt : x < l[c']
    · rw [ite_yes (by simpa using hlt)]
      refine blk_store_work P (hIt.setReg (by decide) _) (k := wP + (c' + 1))
        (sortQ_eval_idx (by simp [hsi]) (by simp [hcx])) (by omega) fun t1 h1 r1 ↦ ?_
      step
      apply WP.blk_nil
      apply WP.blk_nil
      refine ⟨⟨c', _, by omega, h1.setReg (by decide) _, hS.update ⟨by omega, by omega⟩ _,
        fun k h hk ↦ ?_, fun k h hk ↦ ?_, fun k h hk ↦ ?_, by simp [r1, hsi], by simp [r1, hax],
        by simp [r1, h10], ?_, Or.inl ⟨?_, by simp [r1, hdx]⟩⟩, ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact hlo k h (by omega)
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · rw [Nat.add_assoc, Function.update_self]; simp
        · rw [Function.update_of_ne (by omega)]
          exact hhi k h (by omega)
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · exact hlt
        · exact hgt k h (by omega)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, hr.2.1, r1, hf r (by simp [hr.1, hr.2.1, hr.2.2])]
      · simp only [QState.setReg_reg, ite_true, r1, reduceCtorEq, ite_false, hcx]
        rw [h1', Native.SphincsVerifier.toUInt64_sub (by omega), Nat.add_sub_cancel]
      · simp only [QState.setReg_reg, ite_true, r1, reduceCtorEq, ite_false, hcx]
        rw [h1', Native.SphincsVerifier.toUInt64_sub (by omega), Nat.add_sub_cancel,
          toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
        omega
    · rw [ite_no (by simpa using hlt)]
      step; step
      apply WP.blk_nil
      apply WP.blk_nil
      have hle : l[c'] < x := by
        have : l[c'] ≠ x := fun h ↦ hx (h ▸ List.getElem_mem hc')
        omega
      refine ⟨⟨c' + 1, W', hc, (hIt.setReg (by decide) _).setReg (by decide) _ |>.setReg
        (by decide) _, hS, hlo, hhi, hgt, by simp [hsi], by simp [hax], by simp [h10], ?_,
        Or.inr ⟨by simp [h0], by simp [hcx], fun k h hk ↦ ?_⟩⟩, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, hr.2.1, hr.2.2, hf r (by simp [hr.1, hr.2.1, hr.2.2])]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact (List.pairwise_iff_getElem.1 hl k c' h hc' hk).trans hle
        · exact hle
      · simp [hcx, h0]
        omega
  · intro t ⟨c, W', hc, hIt, hS, hlo, hhi, hgt, hsi, hax, h10, hf, hd⟩ hcond
    obtain ⟨hdx, hlt⟩ : t.reg .rdx = c.toUInt64 ∧ ∀ k (h : k < l.length), k < c → l[k] < x := by
      rcases hd with ⟨hcx, hdx⟩ | ⟨_, hdx, hlt⟩
      · rw [cond_ne_imm hcx h0 (by omega) (by omega)] at hcond
        have : c = 0 := by simpa using hcond
        subst this
        exact ⟨by simpa using hdx, fun k _ hk ↦ absurd hk (by omega)⟩
      · exact ⟨hdx, hlt⟩
    have hsplit : insD l x = l.take c ++ x :: l.drop c := by
      refine insD_split x l c (fun y hy ↦ ?_) (fun y hy ↦ ?_)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        simp only [List.length_take] at hk
        rw [List.getElem_take]
        exact hlt k (by omega) (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        simp only [List.length_drop] at hk
        rw [List.getElem_drop]
        exact hgt (c + k) (by omega) (by omega)
    refine blk_store_work P hIt (k := wP + c) (sortQ_eval_idx hsi hdx) (by omega)
      fun t1 h1 r1 ↦ ?_
    step
    apply WP.blk_nil
    rw [hsplit]
    have hmin : min c l.length = c := by omega
    refine ⟨_, h1.setReg (by decide) _, fun i hi ↦ ?_, hS.update ⟨by omega, by omega⟩ _, ?_, ?_⟩
    · simp only [List.length_map, List.length_append, List.length_take, List.length_cons,
        List.length_drop, hmin] at hi
      rw [List.getElem_map, hax]
      rcases lt_trichotomy i c with h | rfl | h
      · rw [Function.update_of_ne (by omega), hlo i (by omega) h,
          List.getElem_append_left (by simp; omega), List.getElem_take]
      · rw [Function.update_self, List.getElem_append_right (by simp)]
        simp [hmin]
      · rw [Function.update_of_ne (by omega), show wP + i = wP + (i - 1) + 1 by omega,
          hhi (i - 1) (by omega) (by omega), List.getElem_append_right (by simp; omega)]
        simp only [List.length_take, hmin, show i - c = (i - 1 - c) + 1 by omega,
          List.getElem_cons_succ, List.getElem_drop]
        congr 2
        omega
    · simp only [QState.setReg_reg, ite_true, r1, h10]
      rw [h1', Native.SphincsVerifier.toUInt64_add]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2, r1, hf r (by simp [hr.1, hr.2.1, hr.2.2.1])]

/-- **`sortQ`**: the distinct positions of the `n` queries at `wQ`, ascending, into `wP`, their
count in `r10`. -/
theorem sortQ_ok (hI : Inv e s D W) {n : Nat} {qs : List Nat} (hr14 : s.reg .r14 = n.toUInt64)
    (hn : n ≤ wireMaxQueries) (hqs : qs.length = n) (hlt : ∀ q ∈ qs, q < 2 ^ 32)
    (hq : Tab W wQ (qs.map Nat.toUInt64)) :
    WP sortQ s (fun s' ↦ ∃ W', Inv e s' D W' ∧ Tab W' wP ((sortD qs).map Nat.toUInt64) ∧
      (sortD qs).length ≤ n ∧ Same (fun k ↦ wP ≤ k ∧ k < wP + wireMaxQueries) W W' ∧
      s'.reg .r10 = (sortD qs).length.toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .rbp] s s') F := by
  have hw : wP + wireMaxQueries ≤ workWords := by
    unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ wireMaxQueries; norm_num
  have hqv : wireMaxQueries = 256 := rfl
  have hwP : wP = wQ + 256 := rfl
  have h0 : (0 : Int64).toUInt64 = (0 : Nat).toUInt64 := rfl
  have h1' : (1 : Int64).toUInt64 = (1 : Nat).toUInt64 := rfl
  have hQ : ∀ i (h : i < qs.length), W (wQ + i) = qs[i].toUInt64 := fun i h ↦ by
    rw [hq i (by simpa using h), List.getElem_map]
  unfold sortQ
  step
  refine blk_load_ctx P (hI.setReg (by decide) _) (eval_cw _ (by simp [hI.rdi]) cWork) (by decide)
    P.c10 ?_
  step; step
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ ∃ i W', i ≤ n ∧ Inv e t D W' ∧
    Same (fun k ↦ wP ≤ k ∧ k < wP + wireMaxQueries) W W' ∧
    Tab W' wP ((sortD (qs.take i)).map Nat.toUInt64) ∧ t.reg .r9 = adr e.wk (wQ + i) ∧
    t.reg .rbp = (n - i).toUInt64 ∧ t.reg .r10 = (sortD (qs.take i)).length.toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .rbp] s t
  refine WP.mono (WP.loop Iv (fun t ↦ (t.reg .rbp).toNat) ?_ ?_ ?_) (fun _ h ↦ WP.blk_nil h)
    (fun _ h ↦ h)
  · refine ⟨0, W, by omega, ((hI.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _,
      Same.refl _ _, fun i h ↦ absurd h (by simp [sortD]), ?_, by simp [hr14], by simp [h0, sortD],
      ?_⟩
    · simp [wd_toUInt64, adr]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]
  · intro t ⟨i, W', hi, hIt, hS, hT, h9, hbp, h10, hf⟩ hcond
    rw [cond_ne_imm hbp h0 (by omega) (by omega)] at hcond
    have hin : i < n := by simp at hcond; omega
    have hiq : i < qs.length := by omega
    have hlen : (sortD (qs.take i)).length ≤ i :=
      (length_sortD _).trans (by simp)
    have hl32 : ∀ y ∈ sortD (qs.take i), y < 2 ^ 32 := fun y hy ↦
      hlt y (List.mem_of_mem_take (mem_sortD hy))
    have hx : W' (wQ + i + 0) = qs[i].toUInt64 := by
      rw [Nat.add_zero, hS _ (by omega), hQ i hiq]
    have tail : ∀ (t3 : QState) (W3 : Nat → UInt64), Inv e t3 D W3 →
        Same (fun k ↦ wP ≤ k ∧ k < wP + wireMaxQueries) W W3 →
        Tab W3 wP ((sortD (qs.take (i + 1))).map Nat.toUInt64) →
        t3.reg .r10 = (sortD (qs.take (i + 1))).length.toUInt64 →
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .rbp] s t3 →
        t3.reg .r9 = adr e.wk (wQ + i) → t3.reg .rbp = (n - i).toUInt64 →
        WP (blk [I (.addi .r9 8), I (.subi .rbp 1)]) t3
          (fun s₁ ↦ Iv s₁ ∧ (s₁.reg .rbp).toNat < (t.reg .rbp).toNat) F := by
      intro t3 W3 hI3 hS3 hT3 h103 hf3 h93 hbp3
      step; step
      apply WP.blk_nil
      refine ⟨⟨i + 1, W3, by omega, (hI3.setReg (by decide) _).setReg (by decide) _, hS3, hT3,
        ?_, ?_, by simp [h103], ?_⟩, ?_⟩
      · simp [h93, show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
      · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, hbp3]
        rw [h1', Native.SphincsVerifier.toUInt64_sub (by omega), Nat.sub_sub]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, hf3 r (by simp [hr.1, hr.2.1, hr.2.2.1,
          hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
          hr.2.2.2.2.2.2.2.2])]
      · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, hbp, hbp3]
        rw [h1', Native.SphincsVerifier.toUInt64_sub (by omega), toNat_toUInt64 (by omega),
          toNat_toUInt64 (by omega)]
        omega
    refine blk_load_work hIt (k := wQ + i + 0) (eval_rw _ _ h9 0) (by omega) ?_
    rw [hx]
    refine blk_load_ctx P (hIt.setReg (by decide) _) (eval_cw _ (by simp [hIt.rdi]) cWork)
      (by decide) P.c10 ?_
    step; step
    apply WP.blk_cons
    have hI3 := ((hIt.setReg (d := .rax) (by decide) qs[i].toUInt64).setReg (d := .rsi) (by decide)
      (e.wk + (wd wP).toUInt64)).setReg (d := .rdx) (by decide) (t.reg .r10)
    refine WP.mono (find_ok (S := 1) (b := wP) (n := (sortD (qs.take i)).length)
      (ks := (sortD (qs.take i)).map Nat.toUInt64) (key := qs[i].toUInt64) hI3 (by decide)
      (by simp [wd_toUInt64, adr]) (by simp [h10]) (by simp) (by simp) (by omega)
      (fun k h ↦ by rw [Nat.one_mul]; exact hT k h)) (fun t2 ⟨hI2, _, hc2, _, _, hf2⟩ ↦ ?_)
      (fun _ h ↦ h)
    have hr10' : t2.reg .r10 = (sortD (qs.take i)).length.toUInt64 := by
      rw [hf2 .r10 (by simp)]; simp [h10]
    have hrsi2 : t2.reg .rsi = adr e.wk wP := by
      rw [hf2 .rsi (by simp)]; simp [wd_toUInt64, adr]
    have hrax2 : t2.reg .rax = qs[i].toUInt64 := by
      rw [hf2 .rax (by simp)]; simp
    have hf2' : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .rbp] s t2 := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hf2 r (by simp [hr])]
      simp [hr, hf r (by simp [hr])]
    have hr92 : t2.reg .r9 = adr e.wk (wQ + i) := by rw [hf2 .r9 (by simp)]; simp [h9]
    have hbp2 : t2.reg .rbp = (n - i).toUInt64 := by rw [hf2 .rbp (by simp)]; simp [hbp]
    have hqi : qs[i] < 2 ^ 32 := hlt _ (List.getElem_mem hiq)
    have hmem : qs[i].toUInt64 ∈ (sortD (qs.take i)).map Nat.toUInt64 ↔
        qs[i] ∈ sortD (qs.take i) := by
      refine ⟨fun h ↦ ?_, fun h ↦ List.mem_map_of_mem h⟩
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
      have := toUInt64_inj (by have := hl32 y hy; omega) (by omega) hyx
      exact this ▸ hy
    have hidx := List.idxOf_le_length (l := (sortD (qs.take i)).map Nat.toUInt64)
      (a := qs[i].toUInt64)
    rw [List.length_map] at hidx
    apply WP.blk_cons
    apply WP.ite
    rw [sortQ_cond_eq_reg hc2 hr10' (by omega) (by omega)]
    by_cases hm : qs[i] ∈ sortD (qs.take i)
    · have hne := List.idxOf_lt_length_iff.2 (hmem.2 hm)
      rw [List.length_map] at hne
      rw [ite_no (by simpa using Nat.ne_of_lt hne)]
      refine WP.skip (tail t2 W' hI2 hS ?_ ?_ hf2' hr92 hbp2)
      · rw [sortD_take_succ qs hiq, insD_of_mem _ _ (pairwise_sortD _) hm]; exact hT
      · rw [sortD_take_succ qs hiq, insD_of_mem _ _ (pairwise_sortD _) hm]; exact hr10'
    · have heq := List.idxOf_eq_length (mt hmem.1 hm)
      rw [List.length_map] at heq
      rw [ite_yes (by simp [heq])]
      refine WP.mono (insertQ_ok P hI2 (pairwise_sortD _) hm hl32 hqi (by omega) hrsi2 hrax2 hr10'
        hT) (fun t3 ⟨W3, hI3, hT3, hS3, h103, hf3⟩ ↦ ?_) (fun _ h ↦ h)
      refine tail t3 W3 hI3 (hS.trans hS3) ?_ ?_ ?_ ?_ ?_
      · rw [sortD_take_succ qs hiq]; exact hT3
      · rw [sortD_take_succ qs hiq, length_insD_of_not_mem _ _ hm]; exact h103
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hf3 r (by simp [hr])]
        exact hf2' r (by simp [hr])
      · rw [hf3 .r9 (by simp)]; exact hr92
      · rw [hf3 .rbp (by simp)]; exact hbp2
  · intro t ⟨i, W', hi, hIt, hS, hT, _, hbp, h10, hf⟩ hcond
    rw [cond_ne_imm hbp h0 (by omega) (by omega)] at hcond
    have hin : i = n := by simp at hcond; omega
    subst hin
    rw [← hqs, List.take_length] at hT h10
    exact ⟨W', hIt, hT, hqs ▸ length_sortD qs, hS, h10, hf⟩

end Run

end NativeVm.Wire
