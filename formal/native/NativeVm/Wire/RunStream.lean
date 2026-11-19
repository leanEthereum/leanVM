module

public import NativeVm.Wire.Tables

/-!
# The stream and the queries

`stream` reads the stream's length and its `2 n` words into the decoded area, as `streamM`
(`stream_ok`); `readQueries` reads a phase's queries into `wQ`, as `rdU32s` (`readQueries_ok`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Protocol.Compile
open Native.SphincsVerifier (toUInt64_add toUInt64_sub toUInt64_shl)

theorem workWords_lt : workWords < 2 ^ 32 := by
  unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; norm_num

theorem dn_ge (L : Nat) : 1 + 2 * (L / 16) + 1 + 8 * phaseWords ≤ decodedWords L := by
  unfold decodedWords phaseBase streamEnd maxStream LeanVM.Protocol.Compile.wireMaxPhases
  omega

/-- The stream words read so far: `D` with word `0` the length and words `1 .. k` read. -/
def streamWords (B : List UInt8) (D : Nat → UInt64) (n k : Nat) (j : Nat) : UInt64 :=
  if j = 0 then n.toUInt64 else if j < 1 + k then leAt B (4 + 8 * (j - 1)) 8 else D j

theorem streamWords_succ (B : List UInt8) (D : Nat → UInt64) (n k : Nat) :
    Function.update (streamWords B D n k) (1 + k) (leAt B (4 + 8 * k) 8) =
      streamWords B D n (k + 1) := by
  funext j
  simp only [Function.update_apply, streamWords]
  by_cases h : j = 1 + k
  · subst h; simp
  · simp only [h, ite_false]
    by_cases h0 : j = 0
    · simp [h0]
    · simp only [h0, ite_false]
      by_cases h1 : j < 1 + k
      · rw [ite_yes h1, ite_yes (by omega)]
      · rw [ite_no h1, ite_no (by omega)]

theorem rdU32s_succ_right (B : List UInt8) (k : Nat) : ∀ {c c1 v : Nat} {qs : List Nat},
    rdU32s B k c = some (qs, c1) → rdU32 B c1 = some (v, c1 + 4) →
      rdU32s B (k + 1) c = some (qs ++ [v], c1 + 4) := by
  induction k with
  | zero =>
    intro c c1 v qs h hv
    simp only [rdU32s, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [rdU32s, hv]
  | succ k ih =>
    intro c c1 v qs h hv
    simp only [rdU32s, Option.bind_eq_bind] at h ⊢
    cases h1 : rdU32 B c with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨a, c2⟩ := p
      simp only [h1, Option.bind_some] at h ⊢
      cases h2 : rdU32s B k c2 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨qs', c3⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih h2 hv
        simp only [rdU32s, Option.bind_eq_bind] at this
        simp [this]

theorem rdU32s_none (B : List UInt8) (k : Nat) : ∀ {c c1 m : Nat} {qs : List Nat},
    rdU32s B k c = some (qs, c1) → rdU32 B c1 = none → rdU32s B (k + m + 1) c = none := by
  induction k with
  | zero =>
    intro c c1 m qs h hv
    simp only [rdU32s, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Nat.zero_add]
    simp [rdU32s, hv]
  | succ k ih =>
    intro c c1 m qs h hv
    rw [show k + 1 + m + 1 = (k + m + 1) + 1 by omega, rdU32s.eq_2]
    rw [rdU32s.eq_2] at h
    simp only [Option.bind_eq_bind] at h ⊢
    cases h1 : rdU32 B c with
    | none => simp
    | some p =>
      obtain ⟨a, c2⟩ := p
      simp only [h1, Option.bind_some] at h ⊢
      cases h2 : rdU32s B k c2 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨qs', c3⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih h2 hv]
        rfl

theorem rdU32s_pos (B : List UInt8) (k : Nat) : ∀ {c c1 : Nat} {qs : List Nat},
    rdU32s B k c = some (qs, c1) → c1 = c + 4 * k ∧ qs.length = k ∧ ∀ q ∈ qs, q < 2 ^ 32 := by
  induction k with
  | zero =>
    intro c c1 qs h
    simp only [rdU32s, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ k ih =>
    intro c c1 qs h
    simp only [rdU32s, Option.bind_eq_bind] at h
    cases h1 : rdU32 B c with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨a, c2⟩ := p
      simp only [h1, Option.bind_some] at h
      cases h2 : rdU32s B k c2 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨qs', c3⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hc2 : c2 = c + 4 := by
          unfold rdU32 at h1; split at h1
          · cases h1; rfl
          · cases h1
        obtain ⟨h3, h4, h5⟩ := ih h2
        refine ⟨by omega, by simp [h4], fun q hq ↦ ?_⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact rdU32_lt h1
        · exact h5 q hq

theorem Tab.snoc {W : Nat → UInt64} {b : Nat} {l : List UInt64} (h : Tab W b l) (v : UInt64) :
    Tab (Function.update W (b + l.length) v) b (l ++ [v]) := by
  intro i hi
  rw [Function.update_apply]
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  by_cases hi' : i < l.length
  · rw [ite_no (by omega), List.getElem_append_left hi']
    exact h i hi'
  · rw [ite_yes (by omega), List.getElem_append_right (by omega)]
    simp [show i - l.length = 0 by omega]

section Run

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

/-- **The stream.** -/
theorem stream_ok (hI : Inv e s D W) (hp : s.reg .r15 = (0 : Nat).toUInt64) :
    WP stream s (fun s' ↦ ∃ str c', streamM e.B 0 = some (str, c') ∧ c' ≤ e.L ∧
      str.length ≤ maxStream e.L ∧ ∃ D', Inv e s' D' W ∧ D' 0 = str.length.toUInt64 ∧
      (∀ i (h : i < str.length), ∀ l < 2, D' (1 + 2 * i + l) = (eWords str[i]).getD l 0) ∧
      Same (fun k ↦ k < 1 + 2 * str.length) D D' ∧ s'.reg .r15 = c'.toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r14, .r15, .rbp] s s')
      (fun s' ↦ streamM e.B 0 = none ∧ Kept e s') := by
  have hL := P.L32
  have hdn : 1 + 2 * (e.L / 16) + 1 + 8 * phaseWords ≤ e.dn := dn_ge e.L
  have hBl := B_length P
  unfold stream
  apply WP.blk_cons
  refine WP.mono (getU32_ok P hI hp (Nat.zero_le _)) (fun s1 ⟨n, hrd, hn32, h1, hb1, hr1, hf1⟩ ↦ ?_)
    (fun s1 ⟨hnone, hk⟩ ↦ ⟨by simp [streamM, hnone], hk⟩)
  have h4 : 4 ≤ e.L := by have := rdU32_le hrd; omega
  step; step; step
  have h16 : (s1.reg .rbx) <<< (4 : Nat).toUInt64 = (n * 2 ^ 4).toUInt64 := by
    rw [hb1, toUInt64_shl (by norm_num) (by omega)]
  apply WP.blk_cons
  refine WP.mono (needR_ok P ((h1.setReg (d := .r14) (by decide) _).setReg (d := .r8) (by decide) _)
    (p := 0 + 4) (n := n * 2 ^ 4) (r := .r8) (by decide) (by simpa using hr1) (by omega)
    (by rw [QState.setReg_reg, ite_yes rfl]; exact h16) (by omega)) (fun s2 ⟨hok, h2, hf2⟩ ↦ ?_)
    (fun s2 ⟨hno, hk⟩ ↦ ⟨?_, hk⟩)
  swap
  · simp only [streamM, hrd, Option.bind_eq_bind, Option.bind_some, rdWords]
    rw [ite_no (by rw [hBl]; omega)]
    rfl
  have hr2 : ∀ r, r ≠ .rax → s2.reg r = ((s1.setReg .r14 (s1.reg .rbx)).setReg
      .r8 (s1.reg .rbx <<< (4 : Nat).toUInt64)).reg r := fun r hr ↦ hf2 r (by simpa using hr)
  refine blk_load_ctx P h2 (eval_cw s2 h2.rdi cDec) (by decide) P.c8 ?_
  refine blk_store_dec P (h2.setReg (by decide) _) (k := 0)
    (by rw [eval_rw (s2.setReg .r9 e.da) .r9 (a := e.da) (j := 0) (by simp [adr_zero]) 0])
    (by omega)
    fun s3 h3 r3 ↦ ?_
  have hn14 : s3.reg .r14 = n.toUInt64 := by
    rw [r3]; simp [hr2 .r14 (by decide), hb1]
  have hD0 : Function.update D 0 ((s2.setReg .r9 e.da).reg .r14) = streamWords e.B D n 0 := by
    funext j
    simp only [Function.update_apply, streamWords]
    by_cases h : j = 0
    · subst h; simp [hr2 .r14 (by decide), hb1]
    · simp [h]
  rw [hD0] at h3
  step; step; step
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ ∃ k, k ≤ 2 * n ∧ Inv e t (streamWords e.B D n k) W ∧
    t.reg .rbp = (2 * n - k).toUInt64 ∧ t.reg .r9 = adr e.da (1 + k) ∧
    t.reg .r15 = (4 + 8 * k).toUInt64 ∧ t.reg .r14 = n.toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r14, .r15, .rbp] s t
  refine WP.mono (WP.loop Iv (fun t ↦ (t.reg .rbp).toNat) ?_ ?_ ?_) (fun _ h ↦ WP.blk_nil h)
    (fun _ h ↦ h)
  · have hfr : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .r8, .r9, .r14, .r15, .rbp] →
        s3.reg r = s.reg r := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [r3]
      simp only [QState.setReg_reg, hr.2.2.2.2.2.1, ite_false]
      rw [hr2 r hr.1]
      simp only [QState.setReg_reg, hr.2.2.2.2.1, hr.2.2.2.2.2.2.1, ite_false]
      exact hf1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1])
    refine ⟨0, by omega, (h3.setReg (by decide) _).setReg (by decide) _, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, hn14]
      rw [show (1 : Nat).toUInt64 = (1 : Nat).toUInt64 from rfl,
        toUInt64_shl (by norm_num) (by omega)]
      congr 1; omega
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r3]
      simp [show (8 : Int64).toUInt64 = 8 from rfl, ← adr_succ, adr_zero]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, r3]
      rw [hr2 .r15 (by decide)]
      simpa using hr1
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, hn14]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, ite_false]
      exact hfr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])
  · intro t ⟨k, hk, hIt, hbp, hr9, hr15, hr14, hft⟩ hc
    have hk2 : k < 2 * n := by
      simp only [Cond.eval, Rhs.eval, hbp, bne_iff_ne, ne_eq] at hc
      by_contra h
      exact hc (by rw [show 2 * n - k = 0 by omega]; rfl)
    apply WP.blk_cons
    refine WP.mono (rdLE_ok P hIt (p := 4 + 8 * k) (n := 8) (by norm_num) le_rfl hr15 (by omega))
      (fun t1 ⟨h1, hb1', hr1', hf1'⟩ ↦ ?_) (fun _ h ↦ h)
    have hr9' : t1.reg .r9 = adr e.da (1 + k) := by rw [hf1' .r9 (by simp), hr9]
    refine blk_store_dec P h1 (k := 1 + k) (by rw [eval_rw t1 .r9 hr9' 0, Nat.add_zero]) (by omega)
      fun t2 h2 r2 ↦ ?_
    rw [hb1', show (leNat e.B (4 + 8 * k) 8).toUInt64 = leAt e.B (4 + 8 * k) 8 from rfl,
      streamWords_succ] at h2
    step; step
    apply WP.blk_nil
    refine ⟨⟨k + 1, by omega, (h2.setReg (by decide) _).setReg (by decide) _, ?_, ?_, ?_, ?_, ?_⟩,
      ?_⟩
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r2]
      rw [hf1' .rbp (by simp), hbp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), Nat.sub_sub]
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r2, hr9']
      rw [show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, r2, hr1']
      congr 1
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, r2]
      rw [hf1' .r14 (by simp), hr14]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, ite_false, r2]
      rw [hf1' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
      exact hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])
    · simp only [QState.setReg_reg, ite_true, r2]
      rw [hf1' .rbp (by simp), hbp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨k, hk, hIt, hbp, _, hr15, _, hft⟩ hc
    have hk2 : k = 2 * n := by
      simp only [Cond.eval, Rhs.eval, hbp] at hc
      have hc' : (2 * n - k).toUInt64 = (0 : Nat).toUInt64 := by
        simpa [bne_eq_false_iff_eq, show (0 : Int64).toUInt64 = 0 from rfl] using hc
      have := congrArg UInt64.toNat hc'
      rw [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at this
      omega
    subst hk2
    let ws : List K := (List.range (2 * n)).map fun i ↦ K.ofLane (leAt e.B (4 + 8 * i) 8)
    have hws : rdWords e.B (2 * n) (0 + 4) = some (ws, 4 + 8 * (2 * n)) := by
      unfold rdWords; rw [ite_yes (by rw [hBl]; omega)]
    refine ⟨(List.range n).map fun i ↦ E.ofLimbs (ws.getD (2 * i) 0) (ws.getD (2 * i + 1) 0),
      4 + 8 * (2 * n), by simp only [streamM, hrd, Option.bind_eq_bind, Option.bind_some, hws],
      by omega,
      by simp only [List.length_map, List.length_range, maxStream]; omega,
      streamWords e.B D n (2 * n), hIt, by simp [streamWords], fun i hi l hl ↦ ?_,
      fun j hj ↦ ?_, hr15, hft⟩
    · simp only [List.length_map, List.length_range] at hi
      simp only [List.getElem_map, List.getElem_range]
      have h0 : ws.getD (2 * i) 0 = K.ofLane (leAt e.B (4 + 8 * (2 * i)) 8) := by
        simp [ws, List.getD_eq_getElem?_getD, show 2 * i < 2 * n by omega]
      have h1 : ws.getD (2 * i + 1) 0 = K.ofLane (leAt e.B (4 + 8 * (2 * i + 1)) 8) := by
        simp [ws, List.getD_eq_getElem?_getD, show 2 * i + 1 < 2 * n by omega]
      rw [h0, h1]
      simp only [streamWords]
      interval_cases l
      · rw [ite_no (by omega), ite_yes (by omega)]
        show _ = (K.ofLane _).lane
        congr 2; omega
      · rw [ite_no (by omega), ite_yes (by omega)]
        show _ = (K.ofLane _).lane
        congr 2; omega
    · simp only [List.length_map, List.length_range] at hj
      simp only [streamWords]
      rw [ite_no (by omega), ite_no (by omega)]

/-- **The queries.** -/
theorem readQueries_ok (hI : Inv e s D W) {n c : Nat} (hr14 : s.reg .r14 = n.toUInt64)
    (hn : n ≤ wireMaxQueries) (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L) :
    WP readQueries s (fun s' ↦ ∃ qs, rdU32s e.B n c = some (qs, c + 4 * n) ∧ ∃ W',
      Inv e s' D W' ∧ Tab W' wQ (qs.map Nat.toUInt64) ∧
      Same (fun k ↦ wQ ≤ k ∧ k < wQ + wireMaxQueries) W W' ∧ s'.reg .r15 = (c + 4 * n).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .r9, .r15, .rbp] s s')
      (fun s' ↦ rdU32s e.B n c = none ∧ Kept e s') := by
  have hL := P.L32
  have hw := workWords_lt
  have hq : wireMaxQueries = 256 := rfl
  unfold readQueries
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  step; step
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ ∃ k qs W', k ≤ n ∧ rdU32s e.B k c = some (qs, c + 4 * k) ∧
    Inv e t D W' ∧ Tab W' wQ (qs.map Nat.toUInt64) ∧
    Same (fun k ↦ wQ ≤ k ∧ k < wQ + wireMaxQueries) W W' ∧ t.reg .rbp = (n - k).toUInt64 ∧
    t.reg .r9 = adr e.wk (wQ + k) ∧ t.reg .r15 = (c + 4 * k).toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .r9, .r15, .rbp] s t
  refine WP.mono (WP.loop Iv (fun t ↦ (t.reg .rbp).toNat) ?_ ?_ ?_) (fun _ h ↦ WP.blk_nil h)
    (fun _ h ↦ h)
  · refine ⟨0, [], W, by omega, rfl, (hI.setReg (d := .r9) (by decide) _).setReg (d := .rbp)
      (by decide) _, fun i hi ↦ by simp at hi, Same.refl _ _, by simp [hr14], ?_, by simp [hp], ?_⟩
    · simp [wd_toUInt64, adr]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2.2.1, hr.2.2.2.2.2.2]
  · intro t ⟨k, qs, W', hk, hrd, hIt, htab, hsame, hbp, hr9, hr15, hft⟩ hc'
    have hkn : k < n := by
      simp only [Cond.eval, Rhs.eval, hbp, bne_iff_ne, ne_eq] at hc'
      by_contra h
      exact hc' (by rw [show n - k = 0 by omega]; rfl)
    obtain ⟨_, hql, hqlt⟩ := rdU32s_pos e.B k hrd
    have hcl : c + 4 * k ≤ e.L := by
      have := rdU32s_le k (B := e.B) (by rw [B_length P]; exact hc) hrd; rwa [B_length P] at this
    apply WP.blk_cons
    refine WP.mono (getU32_ok P hIt hr15 hcl) (fun t1 ⟨v, hv, hv32, h1, hb1, hr1, hf1⟩ ↦ ?_)
      (fun t1 ⟨hno, hk1⟩ ↦ ⟨?_, hk1⟩)
    swap
    · have := rdU32s_none e.B k (m := n - k - 1) hrd hno
      rwa [show k + (n - k - 1) + 1 = n by omega] at this
    have hr9' : t1.reg .r9 = adr e.wk (wQ + k) := by rw [hf1 .r9 (by simp), hr9]
    refine blk_store_work P h1 (k := wQ + k) (by rw [eval_rw t1 .r9 hr9' 0, Nat.add_zero])
      (by unfold workWords wLeaf wSib wSibN wPar wNode wFL wP; omega) fun t2 h2 r2 ↦ ?_
    step; step
    apply WP.blk_nil
    have hqs' := rdU32s_succ_right e.B k hrd hv
    refine ⟨⟨k + 1, qs ++ [v], _, by omega,
      by rw [hqs', show c + 4 * k + 4 = c + 4 * (k + 1) by omega],
      (h2.setReg (by decide) _).setReg (by decide) _, ?_, hsame.update (by omega) _, ?_, ?_, ?_,
      ?_⟩, ?_⟩
    · have := htab.snoc (v.toUInt64)
      rw [List.length_map, hql] at this
      rw [hb1, List.map_append]
      exact this
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r2]
      rw [hf1 .rbp (by simp), hbp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), Nat.sub_sub]
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r2, hr9']
      rw [show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, r2, hr1]
      congr 1
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false, r2]
      rw [hf1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1])]
      exact hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2])
    · simp only [QState.setReg_reg, ite_true, r2]
      rw [hf1 .rbp (by simp), hbp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨k, qs, W', hk, hrd, hIt, htab, hsame, hbp, _, hr15, hft⟩ hc'
    have hk2 : k = n := by
      simp only [Cond.eval, Rhs.eval, hbp] at hc'
      have hc'' : (n - k).toUInt64 = (0 : Nat).toUInt64 := by
        simpa [bne_eq_false_iff_eq, show (0 : Int64).toUInt64 = 0 from rfl] using hc'
      have := congrArg UInt64.toNat hc''
      rw [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at this
      omega
    subst hk2
    exact ⟨qs, hrd, W', hIt, htab, hsame, hr15, hft⟩

end Run

end NativeVm.Wire
