module

public import NativeVm.Wire.Gadgets

/-!
# Tables in the working area

The working area's tables as lists (`Tab`, `NodeTab`, `LeafTab`), and what the shared pieces do to
them: `find` looks up the first entry with a key (`find_ok`), `copy4` and `copyWords` copy words
into the working or the decoded area (`copy4_work`, `copy4_dec`, `copyWords_work`,
`copyWords_dec`), and `hashCall` hashes words of the working area into the scratch's first four
words (`hashCall_ok`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters

/-- The working area's words from `b` are the list `l`. -/
def Tab (W : Nat → UInt64) (b : Nat) (l : List UInt64) : Prop :=
  ∀ i (h : i < l.length), W (b + i) = l[i]

/-- The words of a digest, by index. -/
def dw (d : Digest) (k : Nat) : UInt64 := d.toList.getD k 0

/-- A table of keyed digests from `b`, five words an entry: the key, then the digest's four. -/
def NodeTab (W : Nat → UInt64) (b : Nat) (l : List (Nat × Digest)) : Prop :=
  ∀ i (h : i < l.length), W (b + 5 * i) = l[i].1.toUInt64 ∧ ∀ k < 4, W (b + 5 * i + 1 + k) = dw l[i].2 k

/-- The leaves at `wLeaf`, `wireMaxLeafWords` words reserved each, their first `lw` words. -/
def LeafTab (W : Nat → UInt64) (leaves : List (List K)) (lw : Nat) : Prop :=
  ∀ i (h : i < leaves.length), ∀ t < lw, W (wLeaf + 64 * i + t) = (leaves[i].getD t 0).lane

/-- The opening the model gives the query `q` of a phase of height `h`: its leaf, at its position
among the distinct positions `ps`, and at each level the sibling of the node it is under. -/
def openingOf (ps : List Nat) (leaves : List (List K)) (sibs : List (List (Nat × Digest)))
    (h q : Nat) : LeanVM.Protocol.Compile.Opening :=
  ⟨q, ((ps.zip leaves).lookup q).getD [],
    (List.range h).map fun lv ↦ ((sibs.getD lv []).lookup (q >>> lv)).getD default⟩

/-- `W'` agrees with `W` outside the words `S`. -/
def Same (S : Nat → Prop) (W W' : Nat → UInt64) : Prop := ∀ k, ¬ S k → W' k = W k

theorem Same.refl (S : Nat → Prop) (W : Nat → UInt64) : Same S W W := fun _ _ ↦ rfl

theorem Same.trans {S : Nat → Prop} {W₁ W₂ W₃ : Nat → UInt64} (h₁ : Same S W₁ W₂)
    (h₂ : Same S W₂ W₃) : Same S W₁ W₃ := fun k hk ↦ (h₂ k hk).trans (h₁ k hk)

theorem Same.mono {S S' : Nat → Prop} {W W' : Nat → UInt64} (h : Same S W W')
    (hS : ∀ k, S k → S' k) : Same S' W W' := fun k hk ↦ h k (fun h' ↦ hk (hS k h'))

theorem Same.update {S : Nat → Prop} {W W' : Nat → UInt64} (h : Same S W W') {k : Nat} (hk : S k)
    (v : UInt64) : Same S W (Function.update W' k v) := fun j hj ↦ by
  rw [Function.update_of_ne (fun he ↦ hj (by rw [he]; exact hk))]
  exact h j hj

theorem eval_rw' (s : QState) (r : Reg64) (k : Nat) : (rw r k).eval s = s.reg r + (8 * k).toUInt64 := by
  simp [rw, at_, Addr.eval, wd_toUInt64]

theorem copy4_eq (src dst : Reg64) (i j : Nat) : copy4 src i dst j = blk [
    I (.load .rax (rw src (i + 0))), I (.store (rw dst (j + 0)) .rax),
    I (.load .rax (rw src (i + 1))), I (.store (rw dst (j + 1)) .rax),
    I (.load .rax (rw src (i + 2))), I (.store (rw dst (j + 2)) .rax),
    I (.load .rax (rw src (i + 3))), I (.store (rw dst (j + 3)) .rax)] := rfl

/-- The four words at `A + 8 (i + l)` written to the working area's words `J + l`. -/
def put4 (W : Nat → UInt64) (J : Nat) (v : Nat → UInt64) (k : Nat) : UInt64 :=
  if J ≤ k ∧ k < J + 4 then v (k - J) else W k

theorem put4_eq (W : Nat → UInt64) (J : Nat) (v : Nat → UInt64) :
    Function.update (Function.update (Function.update (Function.update W J (v 0)) (J + 1) (v 1))
      (J + 2) (v 2)) (J + 3) (v 3) = put4 W J v := by
  funext k
  simp only [Function.update_apply, put4]
  by_cases h3 : k = J + 3
  · subst h3; simp
  by_cases h2 : k = J + 2
  · subst h2; simp
  by_cases h1 : k = J + 1
  · subst h1; simp
  by_cases h0 : k = J
  · subst h0; simp
  simp only [h3, h2, h1, h0, ite_false]
  rw [ite_no (by omega)]


theorem idxOf_of_first {ks : List UInt64} {a : UInt64} {i : Nat} (hi : i < ks.length)
    (h : ks[i] = a) (hb : ∀ j (hj : j < i), ks[j] ≠ a) : ks.idxOf a = i := by
  unfold List.idxOf
  rw [List.findIdx_eq hi]
  exact ⟨by simp [h], fun j hj ↦ by simpa using hb j hj⟩

theorem idxOf_of_none {ks : List UInt64} {a : UInt64} (hb : ∀ j (hj : j < ks.length), ks[j] ≠ a) :
    ks.idxOf a = ks.length := by
  apply List.idxOf_eq_length
  intro hm
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
  exact hb j hj rfl

theorem adr_succ (a : UInt64) (k : Nat) : adr a k + 8 = adr a (k + 1) := by
  rw [show (8 : UInt64) = (8 * 1 : Nat).toUInt64 from rfl, adr_add]

section Pieces

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64} {Q F : QState → Prop} {rest : List Stmt}

/-! ## Copying one word -/

/-- A word loaded from anywhere and stored to the working area's word `k`. -/
theorem copyw_work (hI : Inv e s D W) {a1 a2 : Addr} {v : UInt64} {k : Nat}
    (hv : s.mem (a1.eval s) = some v) (hd : a2.eval (s.setReg .rax v) = adr e.wk k)
    (hk : k < workWords)
    (h : ∀ s', Inv e s' D (Function.update W k v) → s'.reg = (s.setReg .rax v).reg →
      (∀ a, a ≠ adr e.wk k → s'.mem a = s.mem a) → WP (blk rest) s' Q F) :
    WP (blk (I (.load .rax a1) :: I (.store a2 .rax) :: rest)) s Q F := by
  refine wp_load rfl hv ?_
  refine wp_store hd ((hI.setReg (d := .rax) (by decide) v).work k hk ▸ rfl) ?_
  refine h _ ?_ rfl fun a ha ↦ ?_
  · have := (hI.setReg (d := .rax) (by decide) v).storeWork P hk ((s.setReg .rax v).reg .rax)
    simpa using this
  · simp [ha]

/-- A word loaded from anywhere and stored to the decoded area's word `k`. -/
theorem copyw_dec (hI : Inv e s D W) {a1 a2 : Addr} {v : UInt64} {k : Nat}
    (hv : s.mem (a1.eval s) = some v) (hd : a2.eval (s.setReg .rax v) = adr e.da k)
    (hk : k < e.dn)
    (h : ∀ s', Inv e s' (Function.update D k v) W → s'.reg = (s.setReg .rax v).reg →
      (∀ a, a ≠ adr e.da k → s'.mem a = s.mem a) → WP (blk rest) s' Q F) :
    WP (blk (I (.load .rax a1) :: I (.store a2 .rax) :: rest)) s Q F := by
  refine wp_load rfl hv ?_
  refine wp_store hd ((hI.setReg (d := .rax) (by decide) v).dec k hk ▸ rfl) ?_
  refine h _ ?_ rfl fun a ha ↦ ?_
  · have := (hI.setReg (d := .rax) (by decide) v).storeDec P hk ((s.setReg .rax v).reg .rax)
    simpa using this
  · simp [ha]

/-- **`copy4` into the working area.** -/
theorem copy4_work (hI : Inv e s D W) {src dst : Reg64} (hsrc : src ≠ .rax) (hdst : dst ≠ .rax)
    {i j J : Nat} {A : UInt64} {v : Nat → UInt64} (hA : s.reg src = A)
    (hd : s.reg dst = adr e.wk J) (hJ : J + j + 4 ≤ workWords)
    (hv : ∀ l < 4, s.mem (A + (8 * (i + l)).toUInt64) = some (v l))
    (hne : ∀ l < 4, ∀ l' < 4, A + (8 * (i + l)).toUInt64 ≠ adr e.wk (J + j + l')) :
    WP (copy4 src i dst j) s (fun s' ↦ Inv e s' D (put4 W (J + j) v) ∧ RegsFrame [.rax] s s' ∧
      ∀ a, (∀ l < 4, a ≠ adr e.wk (J + j + l)) → s'.mem a = s.mem a) F := by
  rw [copy4_eq]
  have hD : ∀ (t : QState) (v' : UInt64) (l : Nat), t.reg dst = adr e.wk J →
      (rw dst (j + l)).eval (t.setReg .rax v') = adr e.wk (J + j + l) := fun t v' l ht ↦ by
    rw [eval_rw', QState.setReg_reg, ite_no hdst, ht, adr_add, Nat.add_assoc]
  have hS : ∀ (t : QState) (l : Nat), t.reg src = A →
      (rw src (i + l)).eval t = A + (8 * (i + l)).toUInt64 := fun t l ht ↦ by rw [eval_rw', ht]
  refine copyw_work P hI (by rw [hS _ _ hA]; exact hv 0 (by omega)) (hD _ _ _ hd)
    (by omega) fun s1 h1 r1 m1 ↦ ?_
  have hs1 : ∀ r, r ≠ .rax → s1.reg r = s.reg r := fun r hr ↦ by rw [r1]; simp [hr]
  refine copyw_work P h1 (by
      rw [hS _ _ (by rw [hs1 _ hsrc, hA]), m1 _ (hne 1 (by omega) 0 (by omega))]
      exact hv 1 (by omega)) (hD _ _ _ (by rw [hs1 _ hdst, hd])) (by omega)
    fun s2 h2 r2 m2 ↦ ?_
  have hs2 : ∀ r, r ≠ .rax → s2.reg r = s.reg r := fun r hr ↦ by rw [r2]; simp [hr, hs1 r hr]
  refine copyw_work P h2 (by
      rw [hS _ _ (by rw [hs2 _ hsrc, hA]), m2 _ (hne 2 (by omega) 1 (by omega)),
        m1 _ (hne 2 (by omega) 0 (by omega))]
      exact hv 2 (by omega)) (hD _ _ _ (by rw [hs2 _ hdst, hd])) (by omega)
    fun s3 h3 r3 m3 ↦ ?_
  have hs3 : ∀ r, r ≠ .rax → s3.reg r = s.reg r := fun r hr ↦ by rw [r3]; simp [hr, hs2 r hr]
  refine copyw_work P h3 (by
      rw [hS _ _ (by rw [hs3 _ hsrc, hA]), m3 _ (hne 3 (by omega) 2 (by omega)),
        m2 _ (hne 3 (by omega) 1 (by omega)), m1 _ (hne 3 (by omega) 0 (by omega))]
      exact hv 3 (by omega)) (hD _ _ _ (by rw [hs3 _ hdst, hd])) (by omega)
    fun s4 h4 r4 m4 ↦ ?_
  have hs4 : ∀ r, r ≠ .rax → s4.reg r = s.reg r := fun r hr ↦ by rw [r4]; simp [hr, hs3 r hr]
  apply WP.blk_nil
  refine ⟨?_, fun r hr ↦ hs4 r (by simpa using hr), fun a ha ↦ ?_⟩
  · rw [← put4_eq]
    simpa using h4
  · rw [m4 _ (ha 3 (by omega)), m3 _ (ha 2 (by omega)), m2 _ (ha 1 (by omega)),
      m1 _ (by simpa using ha 0 (by omega))]

/-- **`copy4` into the decoded area.** -/
theorem copy4_dec (hI : Inv e s D W) {src dst : Reg64} (hsrc : src ≠ .rax) (hdst : dst ≠ .rax)
    {i j J : Nat} {A : UInt64} {v : Nat → UInt64} (hA : s.reg src = A)
    (hd : s.reg dst = adr e.da J) (hJ : J + j + 4 ≤ e.dn)
    (hv : ∀ l < 4, s.mem (A + (8 * (i + l)).toUInt64) = some (v l))
    (hne : ∀ l < 4, ∀ l' < 4, A + (8 * (i + l)).toUInt64 ≠ adr e.da (J + j + l')) :
    WP (copy4 src i dst j) s (fun s' ↦ Inv e s' (put4 D (J + j) v) W ∧ RegsFrame [.rax] s s' ∧
      ∀ a, (∀ l < 4, a ≠ adr e.da (J + j + l)) → s'.mem a = s.mem a) F := by
  rw [copy4_eq]
  have hD : ∀ (t : QState) (v' : UInt64) (l : Nat), t.reg dst = adr e.da J →
      (rw dst (j + l)).eval (t.setReg .rax v') = adr e.da (J + j + l) := fun t v' l ht ↦ by
    rw [eval_rw', QState.setReg_reg, ite_no hdst, ht, adr_add, Nat.add_assoc]
  have hS : ∀ (t : QState) (l : Nat), t.reg src = A →
      (rw src (i + l)).eval t = A + (8 * (i + l)).toUInt64 := fun t l ht ↦ by rw [eval_rw', ht]
  refine copyw_dec P hI (by rw [hS _ _ hA]; exact hv 0 (by omega)) (hD _ _ _ hd)
    (by omega) fun s1 h1 r1 m1 ↦ ?_
  have hs1 : ∀ r, r ≠ .rax → s1.reg r = s.reg r := fun r hr ↦ by rw [r1]; simp [hr]
  refine copyw_dec P h1 (by
      rw [hS _ _ (by rw [hs1 _ hsrc, hA]), m1 _ (hne 1 (by omega) 0 (by omega))]
      exact hv 1 (by omega)) (hD _ _ _ (by rw [hs1 _ hdst, hd])) (by omega)
    fun s2 h2 r2 m2 ↦ ?_
  have hs2 : ∀ r, r ≠ .rax → s2.reg r = s.reg r := fun r hr ↦ by rw [r2]; simp [hr, hs1 r hr]
  refine copyw_dec P h2 (by
      rw [hS _ _ (by rw [hs2 _ hsrc, hA]), m2 _ (hne 2 (by omega) 1 (by omega)),
        m1 _ (hne 2 (by omega) 0 (by omega))]
      exact hv 2 (by omega)) (hD _ _ _ (by rw [hs2 _ hdst, hd])) (by omega)
    fun s3 h3 r3 m3 ↦ ?_
  have hs3 : ∀ r, r ≠ .rax → s3.reg r = s.reg r := fun r hr ↦ by rw [r3]; simp [hr, hs2 r hr]
  refine copyw_dec P h3 (by
      rw [hS _ _ (by rw [hs3 _ hsrc, hA]), m3 _ (hne 3 (by omega) 2 (by omega)),
        m2 _ (hne 3 (by omega) 1 (by omega)), m1 _ (hne 3 (by omega) 0 (by omega))]
      exact hv 3 (by omega)) (hD _ _ _ (by rw [hs3 _ hdst, hd])) (by omega)
    fun s4 h4 r4 m4 ↦ ?_
  have hs4 : ∀ r, r ≠ .rax → s4.reg r = s.reg r := fun r hr ↦ by rw [r4]; simp [hr, hs3 r hr]
  apply WP.blk_nil
  refine ⟨?_, fun r hr ↦ hs4 r (by simpa using hr), fun a ha ↦ ?_⟩
  · rw [← put4_eq]
    simpa using h4
  · rw [m4 _ (ha 3 (by omega)), m3 _ (ha 2 (by omega)), m2 _ (ha 1 (by omega)),
      m1 _ (by simpa using ha 0 (by omega))]

omit P in
/-- **`find S`**: the first of the `n` entries of `S` words at `rsi` whose first word is `rax`; its
index in `rcx` and `rdx` (`n` if none) and its address in `r8`. -/
theorem find_ok (hI : Inv e s D W) {S b n : Nat} {ks : List UInt64} {key : UInt64} (hS : 0 < S)
    (hrsi : s.reg .rsi = adr e.wk b) (hrdx : s.reg .rdx = n.toUInt64) (hrax : s.reg .rax = key)
    (hn : ks.length = n) (hb : b + S * n ≤ workWords)
    (hks : ∀ i (h : i < ks.length), W (b + S * i) = ks[i]) :
    WP (find S) s (fun s' ↦ Inv e s' D W ∧ s'.mem = s.mem ∧
      s'.reg .rcx = (ks.idxOf key).toUInt64 ∧ s'.reg .rdx = (ks.idxOf key).toUInt64 ∧
      s'.reg .r8 = adr e.wk (b + S * ks.idxOf key) ∧ RegsFrame [.rbx, .rcx, .rdx, .r8] s s') F := by
  have hw : workWords < 2 ^ 32 := by unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; norm_num
  have hnw : n ≤ workWords := le_trans (Nat.le_mul_of_pos_left n hS) (by omega)
  unfold find
  step; step
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ Inv e t D W ∧ t.mem = s.mem ∧ RegsFrame [.rbx, .rcx, .rdx, .r8] s t ∧
    t.reg .rax = key ∧ t.reg .rsi = adr e.wk b ∧ ∃ i, i ≤ n ∧ t.reg .rcx = i.toUInt64 ∧
      t.reg .r8 = adr e.wk (b + S * i) ∧ (∀ j (hj : j < ks.length), j < i → ks[j] ≠ key) ∧
      (t.reg .rdx = n.toUInt64 ∨ ∃ h : i < ks.length, ks[i] = key ∧ t.reg .rdx = i.toUInt64)
  refine WP.mono (WP.loop Iv (fun t ↦ (t.reg .rdx).toNat - (t.reg .rcx).toNat) ?_ ?_ ?_)
    (fun _ h ↦ WP.blk_nil h) (fun _ h ↦ h)
  · refine ⟨(hI.setReg (by decide) _).setReg (by decide) _, rfl, ?_, by simp [hrax],
      by simp [hrsi], 0, by omega, by simp; rfl, by simp [hrsi, adr], fun j _ hj ↦ absurd hj (by omega),
      Or.inl (by simp [hrdx])⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.1, hr.2.2.2]
  · intro t ⟨hIt, hmt, hft, hat, hst, i, hin, hci, hri, hbef, hdx⟩ hc
    have hlt : i < n := by
      rcases hdx with hdx | ⟨_, _, hdx⟩
      · simp only [Cond.eval, Rhs.eval, hci, hdx, decide_eq_true_eq] at hc
        rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at hc
        exact hc
      · simp only [Cond.eval, Rhs.eval, hci, hdx, decide_eq_true_eq] at hc
        exact absurd hc (by simp)
    have hdx' : t.reg .rdx = n.toUInt64 := by
      rcases hdx with hdx | ⟨_, _, hdx⟩
      · exact hdx
      · simp only [Cond.eval, Rhs.eval, hci, hdx, decide_eq_true_eq] at hc
        exact absurd hc (by simp)
    have hik : i < ks.length := by omega
    refine blk_load_work hIt (k := b + S * i) (by rw [eval_rw', hri]; simp)
      (by have := Nat.mul_le_mul_left S (show i + 1 ≤ n by omega); rw [Nat.mul_succ] at this; omega) ?_
    apply WP.blk_cons
    apply WP.ite
    have hceq : (Cond.cmp .eq .rbx (.reg .rax)).eval (t.setReg .rbx (W (b + S * i))) =
        decide (ks[i] = key) := by
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hat,
        hks i hik]
      by_cases h : ks[i] = key <;> simp [h]
    rw [hceq]
    by_cases hk : ks[i] = key
    · simp only [hk, decide_true, ite_true]
      apply WP.ins'
      simp only [QInstr.step]
      refine WP.blk_nil ⟨⟨(hIt.setReg (by decide) _).setReg (by decide) _, by simp [hmt], ?_,
        by simp [hat], by simp [hst], i, hin, by simp [hci], by simp [hri], hbef,
        Or.inr ⟨hik, hk, by simp [hci]⟩⟩, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, hr.2.2.1, hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
      · simp [hci, hdx', toNat_toUInt64 (show i < 2 ^ 64 by omega),
          toNat_toUInt64 (show n < 2 ^ 64 by omega)]
        omega
    · simp only [hk, decide_false, Bool.false_eq_true, ite_false]
      step; step
      apply WP.blk_nil
      apply WP.blk_nil
      refine ⟨⟨((hIt.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _, by simp [hmt],
        ?_, by simp [hat], by simp [hst], i + 1, by omega, ?_, ?_, ?_, Or.inl (by simp [hdx'])⟩, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, hr.2.1, hr.2.2.2, hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
      · simp [hci, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl]
      · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hri, wd_toUInt64,
          adr_add]
        congr 1; ring
      · intro j hj hji
        rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
        · exact hbef j hj hji
        · exact hk
      · simp [hci, hdx', toNat_toUInt64 (show i < 2 ^ 64 by omega),
          toNat_toUInt64 (show n < 2 ^ 64 by omega), show (1 : Int64).toUInt64 = (1 : Nat).toUInt64
          from rfl]
        omega
  · intro t ⟨hIt, hmt, hft, hat, hst, i, hin, hci, hri, hbef, hdx⟩ hc
    have hidx : ks.idxOf key = i := by
      rcases hdx with hdx | ⟨hik, hk, hdx⟩
      · simp only [Cond.eval, Rhs.eval, hci, hdx, decide_eq_false_iff_not] at hc
        rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at hc
        have : i = n := by omega
        subst this
        rw [idxOf_of_none fun j hj ↦ hbef j hj (by omega), hn]
      · exact idxOf_of_first hik hk fun j hj ↦ hbef j (by omega) hj
    refine ⟨hIt, hmt, by rw [hidx, hci], ?_, by rw [hidx, hri], hft⟩
    rcases hdx with hdx | ⟨hik, hk, hdx⟩
    · simp only [Cond.eval, Rhs.eval, hci, hdx, decide_eq_false_iff_not] at hc
      rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at hc
      rw [hidx, hdx, show n = i by omega]
    · rw [hidx, hdx]

omit P in
/-- The `n` words of the working area from `b`. -/
def wordsOf (W : Nat → UInt64) (b n : Nat) : List UInt64 := (List.range n).map fun i ↦ W (b + i)

omit P in
theorem wordsOf_length (W : Nat → UInt64) (b n : Nat) : (wordsOf W b n).length = n := by
  simp [wordsOf]

/-- **`hashCall`**: `keccak256` of the `len` bytes the working area's words from `b` hold, in the
scratch's first four words; the areas kept. -/
theorem hashCall_ok (hI : Inv e s D W) {b len : Nat} (hrsi : s.reg .rsi = adr e.wk b)
    (hrbx : s.reg .rbx = len.toUInt64) (hlen : len < 2 ^ 32) (hb : b + (len + 7) / 8 ≤ workWords)
    (hz : HoldsBytes (wordsOf W b ((len + 7) / 8)) len) :
    WP hashCall s (fun s' ↦ Inv e s' D W ∧ (∀ k (hk : k < 4), s'.mem (adr e.x (cScr + k)) =
      some (keccak256 ((wordsBytes (wordsOf W b ((len + 7) / 8))).take len))[k]) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') F := by
  unfold hashCall
  step
  have hrdi : (s.setReg .rdi ((cw cScr).eval s)).reg .rdi = adr e.x cScr := by
    simp [eval_cw s hI.rdi]
  have hscr : ∀ k, scratchAddr (adr e.x cScr) k = adr e.x (cScr + k) := fun k ↦ adr_add _ _ _
  apply WP.blk_cons
  refine WP.mono (hash_spec (ws := wordsOf W b ((len + 7) / 8)) hz (by simpa using hrbx) hlen
    (fun i hi ↦ ?_) (fun k hk ↦ ?_) (fun i hi k hk ↦ ?_)) (fun s1 ⟨hd, hs, hout, hf⟩ ↦ ?_)
    (fun _ h ↦ h)
  · rw [wordsOf_length] at hi
    simp only [QState.setReg_mem, QState.setReg_reg, reduceCtorEq, ite_false, hrsi, adr_add]
    rw [Inv.work hI (b + i) (by omega)]
    simp [wordsOf]
  · rw [hrdi, hscr]
    exact hI.scr k hk
  · rw [wordsOf_length] at hi
    rw [hrdi, hscr]
    simp only [QState.setReg_reg, reduceCtorEq, ite_false, hrsi, adr_add]
    exact (P.scr_ne_work (j := b + i) hk (by omega)).symm
  · rw [hrdi] at hd hs hout
    have hr1 : s1.reg .rdi = adr e.x cScr := by rw [hf .rdi (by simp), hrdi]
    step
    apply WP.blk_nil
    refine ⟨⟨?_, fun a ha ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_⟩, fun k hk ↦ ?_, ?_⟩
    · simp only [QState.setReg_reg, ite_true, Addr.eval, at_, hr1, adr, wd, Int64.toUInt64_neg,
        Int64.toUInt64_ofNat', UInt64.add_zero, cScr]
      simp
    · simp only [QState.setReg_mem]
      rw [hout a fun k hk ↦ by rw [hscr]; exact ha.1 k hk]
      simpa using hI.out a ha
    · simp only [QState.setReg_mem]
      rw [← hscr]; exact hs k hk
    · simp only [QState.setReg_mem]
      rw [hout _ fun j hj ↦ by rw [hscr]; exact (P.scr_ne_dec hj hk).symm]
      simpa using hI.dec k hk
    · simp only [QState.setReg_mem]
      rw [hout _ fun j hj ↦ by rw [hscr]; exact (P.scr_ne_work hj hk).symm]
      simpa using hI.work k hk
    · simp only [QState.setReg_mem]
      rw [← hscr]; exact hd k hk
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases hrd : r = .rdi
      · subst hrd
        simp only [QState.setReg_reg, ite_true, Addr.eval, at_, hr1, adr, wd, Int64.toUInt64_neg,
          Int64.toUInt64_ofNat', UInt64.add_zero, cScr, hI.rdi]
        simp
      · simp only [QState.setReg_reg, hrd, ite_false]
        rw [hf r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
        simp [hrd]

omit P in
/-- `W` with the `i` words from `d` copied from `src`'s words from `a`. -/
def copied (W src : Nat → UInt64) (a d i : Nat) (k : Nat) : UInt64 :=
  if d ≤ k ∧ k < d + i then src (a + (k - d)) else W k

omit P in
theorem copied_succ (W src : Nat → UInt64) (a d i : Nat) :
    Function.update (copied W src a d i) (d + i) (src (a + i)) = copied W src a d (i + 1) := by
  funext k
  simp only [Function.update_apply, copied]
  by_cases h : k = d + i
  · subst h; simp
  · simp only [h, ite_false]
    by_cases h' : d ≤ k ∧ k < d + i
    · rw [ite_yes h', ite_yes (by omega)]
    · rw [ite_no h', ite_no (by omega)]

omit P in
theorem copied_zero (W src : Nat → UInt64) (a d : Nat) : copied W src a d 0 = W := by
  funext k; simp [copied]

/-- **`copyWords` from the working area into the decoded area.** -/
theorem copyWords_dec (hI : Inv e s D W) {a d n : Nat} (hrsi : s.reg .rsi = adr e.wk a)
    (hrbx : s.reg .rbx = adr e.da d) (hrdx : s.reg .rdx = n.toUInt64) (ha : a + n ≤ workWords)
    (hd : d + n ≤ e.dn) :
    WP copyWords s (fun s' ↦ Inv e s' (copied D W a d n) W ∧
      RegsFrame [.rax, .rbx, .rdx, .rsi] s s') F := by
  have hw : workWords < 2 ^ 32 := by unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; norm_num
  let Iv : QState → Prop := fun t ↦ ∃ i, i ≤ n ∧ Inv e t (copied D W a d i) W ∧
    t.reg .rsi = adr e.wk (a + i) ∧ t.reg .rbx = adr e.da (d + i) ∧ t.reg .rdx = (n - i).toUInt64 ∧
    RegsFrame [.rax, .rbx, .rdx, .rsi] s t
  refine WP.mono (WP.loop Iv (fun t ↦ (t.reg .rdx).toNat) ⟨0, by omega, by rwa [copied_zero],
    by simpa using hrsi, by simpa using hrbx, by simpa using hrdx, fun _ _ ↦ rfl⟩ ?_ ?_)
    (fun _ h ↦ h) (fun _ h ↦ h)
  · intro t ⟨i, hin, hIt, hsi, hbx, hdx, hft⟩ hc
    have hlt : i < n := by
      simp only [Cond.eval, Rhs.eval, hdx, bne_iff_ne, ne_eq] at hc
      by_contra h
      exact hc (by rw [show n - i = 0 by omega]; rfl)
    refine copyw_dec P hIt (k := d + i)
      (by rw [eval_rw', hsi, adr_add, Nat.add_zero]; exact hIt.work _ (by omega))
      (by rw [eval_rw']; simp [hbx]) (by omega) fun t1 h1 r1 _ ↦ ?_
    step; step; step
    apply WP.blk_nil
    rw [copied_succ] at h1
    refine ⟨⟨i + 1, by omega, ((h1.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _,
      ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [r1, hsi, show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · simp [r1, hbx, show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · simp only [QState.setReg_reg, ite_true, r1, reduceCtorEq, ite_false, hdx]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), Nat.sub_sub]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, r1, hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
    · simp only [QState.setReg_reg, ite_true, r1, reduceCtorEq, ite_false, hdx]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hin, hIt, _, _, hdx, hft⟩ hc
    simp only [Cond.eval, Rhs.eval, hdx] at hc
    have : n - i = 0 := by
      have hc' : (n - i).toUInt64 = (0 : Nat).toUInt64 := by
        simpa [bne_eq_false_iff_eq, show (0 : Int64).toUInt64 = 0 from rfl] using hc
      have := congrArg UInt64.toNat hc'
      rwa [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at this
    rw [show i = n by omega] at hIt
    exact ⟨hIt, hft⟩

/-- **`copyWords` within the working area**, between words apart. -/
theorem copyWords_work (hI : Inv e s D W) {a d n : Nat} (hrsi : s.reg .rsi = adr e.wk a)
    (hrbx : s.reg .rbx = adr e.wk d) (hrdx : s.reg .rdx = n.toUInt64) (ha : a + n ≤ workWords)
    (hd : d + n ≤ workWords) (hap : a + n ≤ d ∨ d + n ≤ a) :
    WP copyWords s (fun s' ↦ Inv e s' D (copied W W a d n) ∧
      RegsFrame [.rax, .rbx, .rdx, .rsi] s s') F := by
  have hw : workWords < 2 ^ 32 := by unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; norm_num
  let Iv : QState → Prop := fun t ↦ ∃ i, i ≤ n ∧ Inv e t D (copied W W a d i) ∧
    t.reg .rsi = adr e.wk (a + i) ∧ t.reg .rbx = adr e.wk (d + i) ∧ t.reg .rdx = (n - i).toUInt64 ∧
    RegsFrame [.rax, .rbx, .rdx, .rsi] s t
  refine WP.mono (WP.loop Iv (fun t ↦ (t.reg .rdx).toNat) ⟨0, by omega, by rwa [copied_zero],
    by simpa using hrsi, by simpa using hrbx, by simpa using hrdx, fun _ _ ↦ rfl⟩ ?_ ?_)
    (fun _ h ↦ h) (fun _ h ↦ h)
  · intro t ⟨i, hin, hIt, hsi, hbx, hdx, hft⟩ hc
    have hlt : i < n := by
      simp only [Cond.eval, Rhs.eval, hdx, bne_iff_ne, ne_eq] at hc
      by_contra h
      exact hc (by rw [show n - i = 0 by omega]; rfl)
    have hsrc : copied W W a d i (a + i) = W (a + i) := by
      unfold copied; rw [ite_no (by omega)]
    refine copyw_work P hIt (k := d + i)
      (by rw [eval_rw', hsi, adr_add, Nat.add_zero, hIt.work _ (by omega), hsrc])
      (by rw [eval_rw']; simp [hbx]) (by omega) fun t1 h1 r1 _ ↦ ?_
    step; step; step
    apply WP.blk_nil
    rw [copied_succ] at h1
    refine ⟨⟨i + 1, by omega, ((h1.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _,
      ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [r1, hsi, show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · simp [r1, hbx, show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · simp only [QState.setReg_reg, ite_true, r1, reduceCtorEq, ite_false, hdx]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), Nat.sub_sub]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, r1, hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
    · simp only [QState.setReg_reg, ite_true, r1, reduceCtorEq, ite_false, hdx]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_sub (by omega), toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hin, hIt, _, _, hdx, hft⟩ hc
    simp only [Cond.eval, Rhs.eval, hdx] at hc
    have : n - i = 0 := by
      have hc' : (n - i).toUInt64 = (0 : Nat).toUInt64 := by
        simpa [bne_eq_false_iff_eq, show (0 : Int64).toUInt64 = 0 from rfl] using hc
      have := congrArg UInt64.toNat hc'
      rwa [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at this
    rw [show i = n by omega] at hIt
    exact ⟨hIt, hft⟩

end Pieces

end NativeVm.Wire
