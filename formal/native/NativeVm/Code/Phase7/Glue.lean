module

public import NativeVm.Code.Phase7.Push
public import NativeVm.Field.Powers

/-!
# A non-final level's glued claims

`powC`: the query weights `powers λ n` (`λ` at the temporary pair `13`, `n` the queries' count) as
glued claim `g + 1`'s weights (`g` the glued claims' count), the address of their first element at
`cK`. `glueC` then appends glued claim `g` (`λ`, the `α`s' count, `eq oodPoint`) and `g + 1` (`λ²`,
the `α`s' count, `induced μ queries weights`) and adds `λ·oodValue + λ²·batched` to the running
claim (`glueLevel`). `copyWordsC` copies a run of words. The slots' addresses are indexed by
`758 g` (`mul758`, shifts and adds). The proofs track the area's words as a function of their index
(`Tr`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Field (epowers epowers_spec powRegs eval_at int64Zero_toUInt64 toUInt64_succ_sub
  toUInt64_eq_zero ew)
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero wd_add eval_cw wp_load wp_store wp_storei
  wp_reg isSome_setMem ctxWork toUInt64_shl toUInt64_succ toUInt64_add)

/-- Unfold the slots and phase 7's offsets. -/
syntax "gnorm" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| gnorm $[$loc]?) => `(tactic|
    simp only [gslot, sc, cIdx, cN, cLogN, cMu, cDepth, cI, cJ, cK, levO, cFold, cRate, cQ, cNFold,
      cNRate, tmpO, hiO, tabO, layO, whatO, novO, foldO, indO, ptO, xO, ringO, mleO, spO,
      scratch_off, whir_off, basis_off, rounds_off, queries_off, rows_off, mineLo_val, dataEnd_val,
      gluedWords_val, gluedQOff_val, gluedWOff_val, whirGluedOff_val, whirWords_val,
      vecWords_stackCap, wvecWords_queryCap, vecWords_queryCap, roundsWords_val, stackCap_val,
      gluedCap_val, roundCap_val, queryCap_val, vecWords, wvecWords] $[$loc]?)

/-- `omega` on the goal with the offsets unfolded (the context's bounds already numerals); the
unfolding first, as most goals name offsets and a failing `omega` costs as much as a run. -/
macro "gomega" : tactic => `(tactic| first | (gnorm; omega) | omega)

/-! ## Copying words -/

/-- Copy `r15` words from `r13` to `r14`. -/
def copyWordsC : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .rax (at_ .r13 0)), I (.store (at_ .r14 0) .rax),
  I (.addi .r13 8), I (.addi .r14 8), I (.subi .r15 1)])

/-- The registers `copyWordsC` writes. -/
abbrev copyRegs : List Reg64 := [.rax, .r13, .r14, .r15]

/-- **`copyWordsC`**: the `n` words from `wd w a` copied to the `n` words from `wd w b`. -/
theorem copyWordsC_spec {s : QState} {F : QState → Prop} {w : UInt64} {a b n : Nat}
    (h13 : s.reg .r13 = wd w a) (h14 : s.reg .r14 = wd w b) (h15 : s.reg .r15 = n.toUInt64)
    (hab : a + n ≤ b ∨ b + n ≤ a) (ha : a + n < 2 ^ 61) (hb : b + n < 2 ^ 61)
    (hsrc : ∀ k < n, (s.mem (wd w (a + k))).isSome)
    (hdst : ∀ k < n, (s.mem (wd w (b + k))).isSome) :
    WP copyWordsC s (fun s' ↦ (∀ k < n, s'.mem (wd w (b + k)) = s.mem (wd w (a + k))) ∧
      (∀ x, (∀ k < n, x ≠ wd w (b + k)) → s'.mem x = s.mem x) ∧
      (∀ x, (s'.mem x).isSome = (s.mem x).isSome) ∧ RegsFrame copyRegs s s') F := by
  have hne : ∀ i j, i < 2 ^ 61 → j < 2 ^ 61 → i ≠ j → wd w i ≠ wd w j :=
    fun i j hi hj h e ↦ h ((wd_inj hi hj).mp e)
  refine WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r13 = wd w (a + i) ∧ t.reg .r14 = wd w (b + i) ∧
      t.reg .r15 = (n - i).toUInt64 ∧ (∀ k < i, t.mem (wd w (b + k)) = s.mem (wd w (a + k))) ∧
      (∀ x, (∀ k < n, x ≠ wd w (b + k)) → t.mem x = s.mem x) ∧
      (∀ x, (t.mem x).isSome = (s.mem x).isSome) ∧ RegsFrame copyRegs s t)
    (fun t ↦ (t.reg .r15).toNat) ⟨0, Nat.zero_le _, by rw [h13, Nat.add_zero],
      by rw [h14, Nat.add_zero], by rw [h15, Nat.sub_zero], fun _ h ↦ absurd h (Nat.not_lt_zero _),
      fun _ _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩ ?_ ?_
  · intro t ⟨i, hi, t13, t14, t15, hD, hF, hS, hR⟩ hc
    have hne0 : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hin : i < n := by
      by_contra h
      exact hne0 (by rw [t15, show n - i = 0 by omega]; rfl)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsrc i hin)
    have hv' : t.mem (wd w (a + i)) = some v := by
      rw [hF _ fun k hk ↦ hne (a + i) (b + k) (by omega) (by omega) (by omega)]
      exact hv
    refine wp_load (by rw [eval_at, t13, int64Zero_toUInt64, UInt64.add_zero]) hv' ?_
    refine wp_store (x := wd w (b + i)) (by rw [eval_at]; rsimp; rw [t14, UInt64.add_zero])
      (by rw [QState.setReg_mem, hS]; exact hdst i hin) ?_
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl (WP.blk_nil ?_)))
    rsimp
    simp only [QState.setMem_mem]
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, fun k hk ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_, ?_⟩, ?_⟩
    · rw [t13, show (8 : UInt64) = (8 * 1 : Nat).toUInt64 from rfl, wd_add, Nat.add_assoc]
    · rw [t14, show (8 : UInt64) = (8 * 1 : Nat).toUInt64 from rfl, wd_add, Nat.add_assoc]
    · rw [t15, show n - i = (n - (i + 1)) + 1 by omega, toUInt64_succ_sub]
    · show (if _ = _ then _ else _) = _
      by_cases hki : k = i
      · subst hki
        rw [ite_yes rfl, hv]
      · rw [ite_no (hne _ _ (by omega) (by omega) (by omega))]
        exact hD k (by omega)
    · rw [ite_no (hx i hin)]
      exact hF x hx
    · show Option.isSome (if _ = _ then _ else _) = _
      split
      · rename_i e; subst e; rw [hdst i hin]; rfl
      · exact hS x
    · intro r hr
      have : r ≠ .rax ∧ r ≠ .r13 ∧ r ≠ .r14 ∧ r ≠ .r15 := by
        simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact hr
      simp only [QState.setReg_reg, QState.setMem_reg, this.1, this.2.1, this.2.2.1, this.2.2.2,
        ↓reduceIte]
      exact hR r hr
    · rw [t15, show n - i = (n - (i + 1)) + 1 by omega, toUInt64_succ_sub,
        NativeVm.Field.toNat_toUInt64 (by omega), NativeVm.Field.toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hi, _, _, t15, hD, hF, hS, hR⟩ hc
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hin : i = n := by
      have := toUInt64_eq_zero (show n - i < 2 ^ 64 by omega) (by rw [← t15, h0])
      omega
    subst hin
    exact ⟨hD, hF, hS, hR⟩

/-! ## The area's words by index -/

/-- **The area's words as `F`, by index**, the rest kept from `s0` (`FrM`). -/
structure Tr (env : Env) (s0 : QState) (F : Nat → Option UInt64) (s : QState) : Prop where
  fr : FrM env s0 s
  mem : ∀ k < 2 ^ 61, s.mem (wd env.work k) = F k

/-- The area's words exist. -/
def AreaSome (env : Env) (s : QState) : Prop :=
  ∀ k, mineLo ≤ k → k < dataEnd → (s.mem (wd env.work k)).isSome

/-- `F` with the `n` words from `b` copied from the words from `a`. -/
def cp (F : Nat → Option UInt64) (a b n : Nat) : Nat → Option UInt64 :=
  fun k ↦ if b ≤ k ∧ k < b + n then F (a + (k - b)) else F k

theorem upd_ne {F : Nat → Option UInt64} {j k : Nat} {v : Option UInt64} (h : k ≠ j) :
    Function.update F j v k = F k := Function.update_of_ne h _ _

theorem upd_eq {F : Nat → Option UInt64} {j k : Nat} {v : Option UInt64} (h : k = j) :
    Function.update F j v k = v := by subst h; exact Function.update_self ..

theorem cp_in {F : Nat → Option UInt64} {a b n k : Nat} (h : b ≤ k ∧ k < b + n) :
    cp F a b n k = F (a + (k - b)) := ite_yes h _ _

theorem cp_out {F : Nat → Option UInt64} {a b n k : Nat} (h : ¬ (b ≤ k ∧ k < b + n)) :
    cp F a b n k = F k := ite_no h _ _

/-- Look a word up through stores and copies, each index compared by `gomega`. -/
macro "fsimp" : tactic => `(tactic|
  simp (disch := gomega) only [upd_ne, upd_eq, cp_in, cp_out, Nat.add_sub_cancel_left])

namespace Tr

variable {env : Env} {s0 s s' : QState} {F : Nat → Option UInt64}

theorem init (env : Env) (s0 : QState) : Tr env s0 (fun k ↦ s0.mem (wd env.work k)) s0 :=
  ⟨FrM.refl s0, fun _ _ ↦ rfl⟩

theorem setReg (h : Tr env s0 F s) {r : Reg64} (hr : r ≠ .rdi) (v : UInt64) :
    Tr env s0 F (s.setReg r v) :=
  ⟨h.fr.trans (frM_setReg hr v), h.mem⟩

theorem same (h : Tr env s0 F s) (hm : s'.mem = s.mem) (hr : s'.reg .rdi = s.reg .rdi) :
    Tr env s0 F s' :=
  ⟨h.fr.trans ⟨hr, fun a ↦ by rw [hm], fun a _ ↦ by rw [hm]⟩, fun k hk ↦ by
    rw [hm]; exact h.mem k hk⟩

theorem some (h : Tr env s0 F s) (hs : AreaSome env s0) {k : Nat} (h1 : mineLo ≤ k)
    (h2 : k < dataEnd) : (s.mem (wd env.work k)).isSome := by
  rw [h.fr.dom]; exact hs k h1 h2

theorem store (h : Tr env s0 F s) (hs : AreaSome env s0) {j : Nat} (h1 : mineLo ≤ j)
    (h2 : j < dataEnd) (v : UInt64) :
    Tr env s0 (Function.update F j (Option.some v)) (s.setMem (wd env.work j) v) := by
  have hj : j < 2 ^ 61 := by rw [dataEnd_val] at h2; omega
  refine ⟨h.fr.trans (frM_store h1 h2 (h.some hs h1 h2) v), fun k hk ↦ ?_⟩
  rw [setMem_wd _ hj hk]
  by_cases e : k = j
  · rw [ite_yes e, upd_eq e]
  · rw [ite_no e, upd_ne e]; exact h.mem k hk

theorem copy (h : Tr env s0 F s) {a b n : Nat} (hb1 : mineLo ≤ b) (hb2 : b + n ≤ dataEnd)
    (ha : a + n < 2 ^ 61)
    (hc : ∀ k < n, s'.mem (wd env.work (b + k)) = s.mem (wd env.work (a + k)))
    (hf : ∀ x, (∀ k < n, x ≠ wd env.work (b + k)) → s'.mem x = s.mem x)
    (hd : ∀ x, (s'.mem x).isSome = (s.mem x).isSome) (hr : s'.reg .rdi = s.reg .rdi) :
    Tr env s0 (cp F a b n) s' := by
  have hde := dataEnd_eq
  refine ⟨h.fr.trans ⟨hr, hd, fun x hx ↦ hf x fun k hk e ↦
    hx (e ▸ inMine_wd (by omega) (by omega))⟩, fun k hk ↦ ?_⟩
  unfold cp
  split
  · rename_i hk'
    have e := hc (k - b) (by omega)
    rw [Nat.add_sub_cancel' hk'.1] at e
    rw [e, h.mem _ (by omega)]
  · rw [hf _ fun j hj e ↦ ?_]
    · exact h.mem k hk
    · have := (wd_inj hk (by omega)).mp e
      omega

theorem ewat (h : Tr env s0 F s) {k : Nat} {x : EW} (hk : k + 1 < 2 ^ 61)
    (h0 : F k = Option.some x.c0) (h1 : F (k + 1) = Option.some x.c1) :
    EWAt s.mem (wd env.work k) x :=
  ⟨by rw [h.mem k (by omega)]; exact h0, by rw [wd_wd, h.mem _ hk]; exact h1⟩

end Tr

theorem areaSome {env : Env} {inp : Input} {s : QState} (hi : Inputs env inp s.mem) :
    AreaSome env s := fun k _ h2 ↦
  hi.workSome k (by have := workWords_ge inp.bytecode.size; rw [dataEnd_val] at h2; omega)

/-! ## `758 g` -/

/-- `rcx := 758 · rax` (`758 = 3 · 256 - 10`), `rdx` clobbered. -/
def mul758 : List Stmt := [I (.mov .rcx .rax), I (.shli .rcx 1), I (.add .rcx .rax),
  I (.shli .rcx 8), I (.mov .rdx .rax), I (.shli .rdx 2), I (.add .rdx .rax), I (.shli .rdx 1),
  I (.sub .rcx .rdx)]

theorem mul758_val : ∀ g < 16, ((g.toUInt64 <<< (1 : Nat).toUInt64 + g.toUInt64) <<< (8 : Nat).toUInt64) -
    ((g.toUInt64 <<< (2 : Nat).toUInt64 + g.toUInt64) <<< (1 : Nat).toUInt64) =
    (758 * g).toUInt64 := by decide

theorem mul758_wp {s : QState} {P E : QState → Prop} {rest : List Stmt} {g : Nat} (hg : g < 16)
    (hax : s.reg .rax = g.toUInt64)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .rcx = (758 * g).toUInt64 →
      RegsFrame [.rcx, .rdx] s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (mul758 ++ rest)) s P E := by
  unfold mul758
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl
    (wp_reg rfl (wp_reg rfl ?_))))))))
  refine h _ (by rsimp) ?_ (by rf_tac)
  have := mul758_val g hg
  rsimp at this ⊢
  rw [hax]
  exact this

/-! ## The query weights -/

/-- **`epowers`** on the model's words: `powers B n` to the words from `wd w a`. -/
theorem epowers_w {s : QState} {E : QState → Prop} {w : UInt64} {a n : Nat}
    (h14 : s.reg .r14 = wd w a) (h15 : s.reg .r15 = n.toUInt64) (hlen : n < 2 ^ 60)
    (hdom : ∀ k < 2 * n, (s.mem (wd w (a + k))).isSome) :
    WP epowers s (fun s' ↦ EWArr s'.mem (wd w a) (powers ⟨s.reg .r11, s.reg .r12⟩ n) ∧
      (∀ x, (∀ k < 2 * n, x ≠ wd w (a + k)) → s'.mem x = s.mem x) ∧
      RegsFrame powRegs s s') E := by
  have ew_wd : ∀ k, ew (wd w a) k = wd w (a + k) := fun k ↦ wd_add w a k
  refine WP.mono (epowers_spec h14 h15 hlen fun k hk ↦ by rw [ew_wd]; exact hdom k hk)
    (fun _ ⟨h, hm, _, hr⟩ ↦ ⟨?_, fun x hx ↦ hm x fun k hk ↦ by rw [ew_wd]; exact hx k hk, hr⟩)
    fun _ h ↦ h
  rw [EWArr_iff_EArr, NativeVm.Equiv.toList_map_powers]
  exact h

/-- The weights' slot: `powers λ n` (`λ` at the temporary pair `13`, `n` the queries' count) as
glued claim `g + 1`'s weights, the address of the first at `cK`. -/
def powC : Stmt := blk (ldW :: ldw .rax (whirR.off + whirGluedOff) :: (mul758 ++
  [ldw .r15 queriesR.off, I (.store (ix .rcx (gslot 1 + gluedWOff)) .r15),
   I (.lea .r14 (ix .rcx (gslot 1 + gluedWOff + 1))), stw cK .r14,
   ldw .r11 (tmpO + 26), ldw .r12 (tmpO + 26 + 1), epowers]))

theorem powers_size' (b : EW) (n : Nat) : (powers b n).size = n := by
  unfold powers
  suffices ∀ (l : List Nat) (acc : Array EW × EW),
      (l.foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) acc).1.size =
        acc.1.size + l.length by
    rw [this]; simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp; omega

/-- The words `powC` writes. -/
def powWritten (g k : Nat) : Prop :=
  (gslot (g + 1) ≤ k ∧ k < gslot (g + 1) + gluedWords) ∨ k = cK

theorem powC_spec {p : Par} {s : QState} {F : QState → Prop} {sW : WhirStateW} {lam : EW} {n : Nat}
    (hrdi : s.reg .rdi = p.env.ctx) (hi : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hw : WhirAt s.mem (whirR.at p.env.work) sW) (hg : sW.glued.size + 2 ≤ gluedCap)
    (hl : EWAt s.mem (wd p.env.work (tmpO + 26)) lam)
    (hn : NatAt s.mem (wd p.env.work queriesR.off) n) (hnq : n ≤ queryCap) :
    WP powC s (fun s' ↦
      EVec s'.mem (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap (powers lam n) ∧
      s'.mem (wd p.env.work cK) = some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1)) ∧
      FrM p.env s s' ∧ Only p.env (powWritten sW.glued.size) s.mem s'.mem) F := by
  have hde := dataEnd_eq
  have hs0 := areaSome hi
  set g := sW.glued.size with hg_def
  have hg8 : g + 2 ≤ 10 := hg
  have hn230 : n ≤ 230 := hnq
  obtain ⟨-, -, -, hgcnt, -⟩ := hw
  simp only [Region.at, wd_wd] at hgcnt
  obtain ⟨l0, l1⟩ := ewat_wd hl
  have t0 := Tr.init p.env s
  unfold powC ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  have t1 := t0.setReg (r := .rbp) (by decide) p.env.work
  refine ldw_wp (env := p.env) (v := g.toUInt64) (by rsimp)
    (by rw [t1.mem _ (by gomega)]; exact hgcnt.2) ?_
  have t2 := t1.setReg (r := .rax) (by decide) g.toUInt64
  refine mul758_wp (g := g) (by omega) (by rsimp) fun s3 m3 h3 f3 ↦ ?_
  have t3 := t2.same m3 (f3 .rdi (by decide))
  have hW3 : s3.reg .rbp = p.env.work := by rw [f3 .rbp (by decide)]; rsimp
  refine ldw_wp (env := p.env) (v := n.toUInt64) hW3
    (by rw [t3.mem _ (by gomega)]; exact hn.2) ?_
  have t4 := t3.setReg (r := .r15) (by decide) n.toUInt64
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hW3) (by rsimp; exact h3)
    (t4.some hs0 (by gomega) (by gomega)) ?_
  have t5 := t4.store hs0 (j := 758 * g + (gslot 1 + gluedWOff)) (by gomega) (by gomega)
    ((s3.setReg .r15 n.toUInt64).reg .r15)
  refine wp_reg rfl ?_
  set s5 := (s3.setReg .r15 n.toUInt64).setMem (wd p.env.work (758 * g + (gslot 1 + gluedWOff)))
    ((s3.setReg .r15 n.toUInt64).reg .r15) with hs5
  have t6 := t5.setReg (r := .r14) (by decide) ((ix .rcx (gslot 1 + gluedWOff + 1)).eval s5)
  set s6 := s5.setReg .r14 ((ix .rcx (gslot 1 + gluedWOff + 1)).eval s5) with hs6
  have hW6 : s6.reg .rbp = p.env.work := by rw [hs6, hs5]; rsimp; exact hW3
  have h14 : s6.reg .r14 = wd p.env.work (758 * g + (gslot 1 + gluedWOff + 1)) := by
    rw [hs6]; rsimp; exact eval_ix (by rw [hs5]; rsimp; exact hW3) (by rw [hs5]; rsimp; exact h3) _
  refine stw_wp hW6 (t6.some hs0 (by gomega) (by gomega)) ?_
  have t7 := t6.store hs0 (j := cK) (by gomega) (by gomega) (s6.reg .r14)
  refine ldw_wp (env := p.env) (v := lam.c0) (by rsimp; exact hW6)
    (by rw [t7.mem _ (by gomega)]; fsimp; exact l0) ?_
  refine ldw_wp (env := p.env) (v := lam.c1) (by rsimp; exact hW6)
    (by rsimp; rw [t7.mem _ (by gomega)]; fsimp; exact l1) ?_
  set s8 := ((s6.setMem (wd p.env.work cK) (s6.reg .r14)).setReg .r11 lam.c0).setReg .r12 lam.c1
    with hs8
  have t8 : Tr p.env s _ s8 := (t7.setReg (by decide) _).setReg (by decide) _
  have hdom : ∀ k < 2 * n,
      (s8.mem (wd p.env.work (758 * g + (gslot 1 + gluedWOff + 1) + k))).isSome :=
    fun k hk ↦ t8.some hs0 (by gomega) (by gomega)
  refine WP.mono (NativeVm.Transcript.WP.frame (epowers_w (n := n)
    (by rw [hs8]; rsimp; exact h14) (by rw [hs8]; rsimp; rw [hs6, hs5]; rsimp) (by gomega) hdom))
    ?_ fun _ h ↦ h.1
  rintro s' ⟨⟨harr, hfr, hregs⟩, hd, -⟩
  have hreg : (⟨s8.reg .r11, s8.reg .r12⟩ : EW) = lam := by rw [hs8]; rsimp
  rw [hreg] at harr
  have hm : ∀ k < 2 ^ 61, ¬ (758 * g + (gslot 1 + gluedWOff + 1) ≤ k ∧
      k < 758 * g + (gslot 1 + gluedWOff + 1) + 2 * n) →
      s'.mem (wd p.env.work k) = s8.mem (wd p.env.work k) :=
    fun k hk hk' ↦ hfr _ fun j hj e ↦ hk' (by have := (wd_inj hk (by gomega)).mp e; omega)
  have fr8 : FrM p.env s s' := t8.fr.trans ⟨hregs .rdi (by decide), hd, fun x hx ↦ hfr x
    fun j hj e ↦ hx (e ▸ inMine_wd (by gomega) (by gomega))⟩
  refine ⟨⟨by rw [powers_size']; exact hnq, ⟨by rw [powers_size']; exact hn.1, ?_⟩, ?_⟩, ?_, fr8, ?_⟩
  · rw [powers_size', hm _ (by gomega) (by gomega), t8.mem _ (by gomega)]
    fsimp
    rsimp
  · rw [wd_wd, show gslot (g + 1) + gluedWOff + 1 = 758 * g + (gslot 1 + gluedWOff + 1) by gomega]
    exact harr
  · rw [hm _ (by gomega) (by gomega), t8.mem _ (by gomega)]
    fsimp
    rw [h14, show gslot (g + 1) + gluedWOff + 1 = 758 * g + (gslot 1 + gluedWOff + 1) by gomega]
  · intro k h1 h2 hk
    unfold powWritten at hk
    gnorm at hk
    rw [hm _ (by gomega) (by gomega), t8.mem _ (by gomega)]
    fsimp

/-! ## The glued claims -/

/-- `glueC`'s first part: `λ²` to `cI`, then the running claim `claim + λ²·batched`, then
`… + λ·oodValue`. -/
def glueHead : List Stmt := [ldW,
  ldw .r9 (tmpO + 26), ldw .r10 (tmpO + 26 + 1),
  ldw .r11 (tmpO + 26), ldw .r12 (tmpO + 26 + 1), NativeVm.Field.emul,
  stw cI .r9, stw (cI + 1) .r10,
  ldw .r11 (tmpO + 16), ldw .r12 (tmpO + 16 + 1), NativeVm.Field.emul,
  ldw .r11 whirR.off, ldw .r12 (whirR.off + 1), NativeVm.Field.eadd,
  stw whirR.off .r9, stw (whirR.off + 1) .r10,
  ldw .r9 (tmpO + 26), ldw .r10 (tmpO + 26 + 1),
  ldw .r11 (tmpO + 28), ldw .r12 (tmpO + 28 + 1), NativeVm.Field.emul,
  ldw .r11 whirR.off, ldw .r12 (whirR.off + 1), NativeVm.Field.eadd,
  stw whirR.off .r9, stw (whirR.off + 1) .r10]

/-- `glueLevel`: glued claims `g` (`λ`, the `α`s' count, `eq p`) and `g + 1` (`λ²`, the `α`s'
count, `induced μ queries weights`, its weights already in place), the running claim
`claim + λ·oodValue + λ²·batched` (`λ`, `oodValue`, `batched` at the temporary pairs `13`, `14`,
`8`; `μ` at `cMu`, `p` at `spO`, the queries at `queriesR`), `λ²` through `cI`, `cJ`. -/
def glueC : Stmt := blk (glueHead ++
  ldw .rax (whirR.off + whirGluedOff) :: (mul758 ++ [
  ldw .r9 (tmpO + 26), ldw .r10 (tmpO + 26 + 1),
  I (.store (ix .rcx (gslot 0)) .r9), I (.store (ix .rcx (gslot 0 + 1)) .r10),
  ldw .r9 cI, ldw .r10 (cI + 1),
  I (.store (ix .rcx (gslot 1)) .r9), I (.store (ix .rcx (gslot 1 + 1)) .r10),
  ldw .rdx (whirR.off + 2),
  I (.store (ix .rcx (gslot 0 + 2)) .rdx), I (.store (ix .rcx (gslot 1 + 2)) .rdx),
  I (.storei (ix .rcx (gslot 0 + 3)) 0), I (.storei (ix .rcx (gslot 1 + 3)) 1),
  ldw .rdx cMu,
  I (.store (ix .rcx (gslot 0 + 5)) .rdx), I (.store (ix .rcx (gslot 1 + 4)) .rdx),
  leaw .r13 spO, I (.lea .r14 (ix .rcx (gslot 0 + 6))), I (.mov .r15 .rdx), I (.shli .r15 1),
  copyWordsC,
  leaw .r13 queriesR.off, I (.lea .r14 (ix .rcx (gslot 1 + gluedQOff))), ldw .r15 queriesR.off,
  I (.addi .r15 1), copyWordsC,
  ldw .rax (whirR.off + whirGluedOff), I (.addi .rax 2), stw (whirR.off + whirGluedOff) .rax]))

/-- The words `glueC` writes. -/
def glueWritten (g k : Nat) : Prop :=
  (gslot g ≤ k ∧ k < gslot g + 2 * gluedWords) ∨ k = whirR.off ∨ k = whirR.off + 1 ∨
    k = whirR.off + whirGluedOff ∨ k = cI ∨ k = cJ

theorem stixi_wp {s : QState} {P F : QState → Prop} {rest : List Stmt} {W : UInt64} {r : Reg64}
    {i k : Nat} {n : Int64} (hW : s.reg .rbp = W) (hr : s.reg r = i.toUInt64)
    (hk : (s.mem (wd W (i + k))).isSome)
    (h : WP (blk rest) (s.setMem (wd W (i + k)) n.toUInt64) P F) :
    WP (blk (I (.storei (ix r k) n) :: rest)) s P F :=
  wp_storei (eval_ix hW hr k) hk h

theorem Tr.look {env : Env} {s0 s : QState} {F : Nat → Option UInt64} {k : Nat} {v : UInt64}
    (h : Tr env s0 F s) (hk : k < 2 ^ 61) (hv : F k = Option.some v) :
    s.mem (wd env.work k) = Option.some v := by
  rw [h.mem k hk, hv]

/-- `copyWordsC` on the area's words. -/
theorem copy_wp {env : Env} {s0 s : QState} {F : Nat → Option UInt64} {P E : QState → Prop}
    {rest : List Stmt} {a b n : Nat} (ht : Tr env s0 F s) (hs : AreaSome env s0)
    (h13 : s.reg .r13 = wd env.work a) (h14 : s.reg .r14 = wd env.work b)
    (h15 : s.reg .r15 = n.toUInt64) (ha1 : mineLo ≤ a) (ha2 : a + n ≤ dataEnd)
    (hb1 : mineLo ≤ b) (hb2 : b + n ≤ dataEnd) (hab : a + n ≤ b ∨ b + n ≤ a)
    (h : ∀ s', Tr env s0 (cp F a b n) s' → RegsFrame copyRegs s s' → WP (blk rest) s' P E) :
    WP (blk (copyWordsC :: rest)) s P E := by
  have hde := dataEnd_eq
  refine NativeVm.Field.WP.then (copyWordsC_spec h13 h14 h15 hab (by omega) (by omega)
    (fun k hk ↦ ht.some hs (by omega) (by omega)) (fun k hk ↦ ht.some hs (by omega) (by omega)))
    fun s' ⟨c1, c2, c3, c4⟩ ↦ h s' (ht.copy hb1 hb2 (by omega) c1 c2 c3 (c4 .rdi (by decide))) c4

/-- A `Tr` of a state built by register updates and stores from `base`'s state, `hs` the start's
area. -/
macro "tr_tac" base:term:max hs:term:max : tactic => `(tactic|
  repeat' (first | with_reducible apply Tr.setReg | with_reducible apply Tr.store |
    with_reducible exact $base | exact $hs | decide | gomega))

theorem mem_at {m : UInt64 → Option UInt64} {W : UInt64} {a b : Nat} {v : Option UInt64}
    (h : a = b) (hv : m (wd W b) = v) : m (wd W a) = v := h ▸ hv

/-- **`glueC`'s first part**: the words it stores (`λ²` at `cI`, the running claim twice), their
values named. -/
theorem glue_head {p : Par} {s : QState} {P E : QState → Prop} {rest : List Stmt}
    {lam oodValue batched claim : EW}
    (hrdi : s.reg .rdi = p.env.ctx) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hs0 : AreaSome p.env s)
    (hl : EWAt s.mem (wd p.env.work (tmpO + 26)) lam)
    (ho : EWAt s.mem (wd p.env.work (tmpO + 28)) oodValue)
    (hbt : EWAt s.mem (wd p.env.work (tmpO + 16)) batched)
    (hcl : EWAt s.mem (wd p.env.work whirR.off) claim)
    (h : ∀ (s' : QState) (v1 v2 v3 v4 v5 v6 : UInt64),
      Tr p.env s (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (fun k ↦ s.mem (wd p.env.work k)) cI (some v1))
          (cI + 1) (some v2)) whirR.off (some v3)) (whirR.off + 1) (some v4)) whirR.off (some v5))
        (whirR.off + 1) (some v6)) s' →
      s'.reg .rbp = p.env.work → v1 = (lam * lam).c0 → v2 = (lam * lam).c1 →
      v5 = (lam * oodValue + (lam * lam * batched + claim)).c0 →
      v6 = (lam * oodValue + (lam * lam * batched + claim)).c1 → WP (blk rest) s' P E) :
    WP (blk (glueHead ++ rest)) s P E := by
  have hde := dataEnd_eq
  obtain ⟨l0, l1⟩ := ewat_wd hl
  obtain ⟨o0, o1⟩ := ewat_wd ho
  obtain ⟨b0, b1⟩ := ewat_wd hbt
  obtain ⟨c0, c1⟩ := ewat_wd hcl
  have t0 := Tr.init p.env s
  simp only [glueHead, List.cons_append, List.nil_append, ldW]
  refine wp_load (eval_cw hrdi _) hwp ?_
  have t1 := t0.setReg (r := .rbp) (by decide) p.env.work
  have hW1 : (s.setReg .rbp p.env.work).reg .rbp = p.env.work := by rsimp
  -- λ² to `cI`
  refine ldA_wp (x := lam) hW1 (t1.ewat (by gomega) l0 l1) fun s2 m2 x9 x10 f2 ↦ ?_
  have t2 := t1.same m2 (f2 .rdi (by decide))
  have hW2 : s2.reg .rbp = p.env.work := by rw [f2 .rbp (by decide)]; exact hW1
  refine mulM_wp (b := lam) hW2 x9 x10 (t2.ewat (by gomega) l0 l1) fun s3 m3 a9 a10 f3 ↦ ?_
  have t3 := t2.same m3 (f3 .rdi (by decide))
  have hW3 : s3.reg .rbp = p.env.work := by rw [f3 .rbp (by decide)]; exact hW2
  refine stA_wp hW3 (t3.some hs0 (by gomega) (by gomega)) (t3.some hs0 (by gomega) (by gomega)) ?_
  have t4 := (t3.store hs0 (j := cI) (by gomega) (by gomega) (s3.reg .r9)).store hs0
    (j := cI + 1) (by gomega) (by gomega) (s3.reg .r10)
  -- claim := λ²·batched + claim
  refine mulM_wp (b := batched) (by rsimp; exact hW3) (by rsimp; exact a9) (by rsimp; exact a10)
    (t4.ewat (by gomega) (by fsimp; exact b0) (by fsimp; exact b1)) fun s5 m5 b9 b10 f5 ↦ ?_
  have t5 := t4.same m5 (f5 .rdi (by decide))
  have hW5 : s5.reg .rbp = p.env.work := by rw [f5 .rbp (by decide)]; rsimp; exact hW3
  refine addM_wp (b := claim) hW5 b9 b10
    (t5.ewat (by gomega) (by fsimp; exact c0) (by fsimp; exact c1)) fun s6 m6 d9 d10 f6 ↦ ?_
  have t6 := t5.same m6 (f6 .rdi (by decide))
  have hW6 : s6.reg .rbp = p.env.work := by rw [f6 .rbp (by decide)]; exact hW5
  refine stA_wp hW6 (t6.some hs0 (by gomega) (by gomega)) (t6.some hs0 (by gomega) (by gomega)) ?_
  have t7 := (t6.store hs0 (j := whirR.off) (by gomega) (by gomega) (s6.reg .r9)).store hs0
    (j := whirR.off + 1) (by gomega) (by gomega) (s6.reg .r10)
  -- claim := λ·oodValue + claim
  refine ldA_wp (x := lam) (by rsimp; exact hW6)
    (t7.ewat (by gomega) (by fsimp; exact l0) (by fsimp; exact l1)) fun s8 m8 e9 e10 f8 ↦ ?_
  have t8 := t7.same m8 (f8 .rdi (by decide))
  have hW8 : s8.reg .rbp = p.env.work := by rw [f8 .rbp (by decide)]; rsimp; exact hW6
  refine mulM_wp (b := oodValue) hW8 e9 e10
    (t8.ewat (by gomega) (by fsimp; exact o0) (by fsimp; exact o1)) fun s9 m9 g9 g10 f9 ↦ ?_
  have t9 := t8.same m9 (f9 .rdi (by decide))
  have hW9 : s9.reg .rbp = p.env.work := by rw [f9 .rbp (by decide)]; exact hW8
  refine addM_wp (b := lam * lam * batched + claim) hW9 g9 g10
    (t9.ewat (by gomega) (by fsimp; rw [d9]) (by fsimp; rw [d10])) fun s10 m10 h9 h10 f10 ↦ ?_
  have t10 := t9.same m10 (f10 .rdi (by decide))
  have hW10 : s10.reg .rbp = p.env.work := by rw [f10 .rbp (by decide)]; exact hW9
  refine stA_wp hW10 (t10.some hs0 (by gomega) (by gomega))
    (t10.some hs0 (by gomega) (by gomega)) ?_
  exact h _ _ _ _ _ _ _ ((t10.store hs0 (j := whirR.off) (by gomega) (by gomega)
    (s10.reg .r9)).store hs0 (j := whirR.off + 1) (by gomega) (by gomega) (s10.reg .r10))
    (by rsimp; exact hW10) a9 a10 h9 h10

theorem glueC_spec {p : Par} {s : QState} {F : QState → Prop} {sW : WhirStateW}
    {lam oodValue batched : EW} {mu : Nat} {oodPoint : Array EW} {qs : Array UInt64}
    {qw : Array EW}
    (hrdi : s.reg .rdi = p.env.ctx) (hi : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hw : WhirAt s.mem (whirR.at p.env.work) sW) (hg : sW.glued.size + 2 ≤ gluedCap)
    (hl : EWAt s.mem (wd p.env.work (tmpO + 26)) lam)
    (ho : EWAt s.mem (wd p.env.work (tmpO + 28)) oodValue)
    (hbt : EWAt s.mem (wd p.env.work (tmpO + 16)) batched)
    (hmu : NatAt s.mem (wd p.env.work cMu) mu) (hmu30 : mu ≤ 30)
    (hpt : EWArr s.mem (wd p.env.work spO) oodPoint) (hpsz : oodPoint.size = mu)
    (hq : WVec s.mem (wd p.env.work queriesR.off) queryCap qs)
    (hqw : EVec s.mem (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap qw) :
    WP glueC s (fun s' ↦ WhirAt s'.mem (whirR.at p.env.work)
        (glueLevel sW lam mu oodPoint oodValue qs qw batched) ∧ FrM p.env s s' ∧
        Only p.env (glueWritten sW.glued.size) s.mem s'.mem) F := by
  have hde := dataEnd_eq
  have hs0 := areaSome hi
  set g := sW.glued.size with hg_def
  have hg8 : g + 2 ≤ 10 := hg
  have hqs : qs.size ≤ 230 := hq.1
  obtain ⟨hcl, hal, hgsz, hgcnt, hgl⟩ := hw
  have hacnt : NatAt s.mem (wd p.env.work (whirR.off + 2)) sW.alphas.size := by
    have := hal.2.1; simp only [Region.at, wd_wd] at this; exact this
  simp only [Region.at, wd_wd] at hcl hgcnt
  obtain ⟨l0, l1⟩ := ewat_wd hl
  unfold glueC
  refine glue_head hrdi hwp hs0 hl ho hbt hcl fun s10 v1 v2 v3 v4 v5 v6 t11 hW10 a9 a10 h9 h10 ↦ ?_
  -- `rcx := 758 g`
  refine ldw_wp (env := p.env) (v := g.toUInt64) hW10
    (t11.look (by gomega) (by fsimp; exact hgcnt.2)) ?_
  have t12 := t11.setReg (r := .rax) (by decide) g.toUInt64
  refine mul758_wp (g := g) (by omega) (by rsimp) fun sm mm hcx fm ↦ ?_
  have tm := t12.same mm (fm .rdi (by decide))
  have hWm : sm.reg .rbp = p.env.work := by rw [fm .rbp (by decide)]; rsimp; exact hW10
  -- the scalars, the fold starts, the kinds, `μ`
  refine ldw_wp (env := p.env) (v := lam.c0) hWm
    (Tr.look (s0 := s) (by tr_tac tm hs0) (by gomega) (by fsimp; exact l0)) ?_
  refine ldw_wp (env := p.env) (v := lam.c1) (by rsimp; exact hWm)
    (Tr.look (s0 := s) (by tr_tac tm hs0) (by gomega) (by fsimp; exact l1)) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine ldw_wp (env := p.env) (v := (lam * lam).c0) (by rsimp; exact hWm)
    (Tr.look (s0 := s) (by tr_tac tm hs0) (by gomega) (by fsimp; rw [a9])) ?_
  refine ldw_wp (env := p.env) (v := (lam * lam).c1) (by rsimp; exact hWm)
    (Tr.look (s0 := s) (by tr_tac tm hs0) (by gomega) (by fsimp; rw [a10])) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine ldw_wp (env := p.env) (v := sW.alphas.size.toUInt64) (by rsimp; exact hWm)
    (Tr.look (s0 := s) (by tr_tac tm hs0) (by gomega) (by fsimp; exact hacnt.2)) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine stixi_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine stixi_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine ldw_wp (env := p.env) (v := mu.toUInt64) (by rsimp; exact hWm)
    (Tr.look (s0 := s) (by tr_tac tm hs0) (by gomega) (by fsimp; exact hmu.2)) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  refine stix_wp (W := p.env.work) (i := 758 * g) (by rsimp; exact hWm) (by rsimp; exact hcx)
    (Tr.some (by tr_tac tm hs0) hs0 (by gomega) (by gomega)) ?_
  -- `p`
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  refine copy_wp (s0 := s) (a := spO) (b := 758 * g + (gslot 0 + 6)) (n := 2 * mu)
    (by tr_tac tm hs0) hs0
    (by rsimp; exact eval_w (by rsimp; exact hWm) spO)
    (by rsimp; exact eval_ix (by rsimp; exact hWm) (by rsimp; exact hcx) _)
    (by
      have := shl_toUInt64 mu 1 (by omega)
      rsimp at this ⊢
      rw [this, pow_one])
    (by gomega) (by gomega) (by gomega) (by gomega) (by gomega) fun sc1 tc1 rc1 ↦ ?_
  have hWc1 : sc1.reg .rbp = p.env.work := by rw [rc1 .rbp (by decide)]; rsimp; exact hWm
  have hcx1 : sc1.reg .rcx = (758 * g).toUInt64 := by rw [rc1 .rcx (by decide)]; rsimp; exact hcx
  -- the queries
  refine wp_reg rfl (wp_reg rfl ?_)
  refine ldw_wp (env := p.env) (v := qs.size.toUInt64) (by rsimp; exact hWc1)
    (Tr.look (s0 := s) (by tr_tac tc1 hs0) (by gomega) (by fsimp; exact hq.2.1.2)) ?_
  refine wp_reg rfl ?_
  refine copy_wp (s0 := s) (a := queriesR.off) (b := 758 * g + (gslot 1 + gluedQOff))
    (n := qs.size + 1) (by tr_tac tc1 hs0) hs0
    (by rsimp; exact eval_w hWc1 _)
    (by rsimp; exact eval_ix (by rsimp; exact hWc1) (by rsimp; exact hcx1) _)
    (by rsimp; exact toUInt64_succ _)
    (by gomega) (by gomega) (by gomega) (by gomega) (by gomega) fun sc2 tc2 rc2 ↦ ?_
  have hWc2 : sc2.reg .rbp = p.env.work := by rw [rc2 .rbp (by decide)]; rsimp; exact hWc1
  -- the count
  refine ldw_wp (env := p.env) (v := g.toUInt64) hWc2
    (tc2.look (by gomega) (by fsimp; exact hgcnt.2)) ?_
  refine wp_reg rfl ?_
  refine stw_wp (by rsimp; exact hWc2) (Tr.some (by tr_tac tc2 hs0) hs0 (by gomega) (by gomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun sE hsE ↦ ?_
  have tE := ((tc2.setReg (r := .rax) (by decide) g.toUInt64).setReg (r := .rax) (by decide)
    ((sc2.setReg .rax g.toUInt64).reg .rax + Int64.toUInt64 2)).store hs0
    (j := whirR.off + whirGluedOff) (by gomega) (by gomega)
    (((sc2.setReg .rax g.toUInt64).setReg .rax
      ((sc2.setReg .rax g.toUInt64).reg .rax + Int64.toUInt64 2)).reg .rax)
  rw [hsE] at tE
  have hX : lam * oodValue + (lam * lam * batched + sW.claim) =
      sW.claim + lam * oodValue + lam * lam * batched := by
    apply NativeVm.Equiv.EW.toE_injective
    simp only [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul]
    ring
  have hU : ∀ k < 2 ^ 61, ¬ glueWritten g k →
      sE.mem (wd p.env.work k) = s.mem (wd p.env.work k) := by
    intro k hk hn
    unfold glueWritten at hn
    gnorm at hn
    rw [tE.mem k hk]
    fsimp
  have hWt : ∀ j < vecWords queryCap, sE.mem (wd p.env.work (gslot (g + 1) + gluedWOff + j)) =
      s.mem (wd p.env.work (gslot (g + 1) + gluedWOff + j)) := by
    intro j hj
    gnorm at hj
    rw [tE.mem _ (by gomega)]
    fsimp
  have hsz : (glueLevel sW lam mu oodPoint oodValue qs qw batched).glued.size = g + 2 := by
    simp [glueLevel, g]
  refine ⟨⟨?_, ?_, by rw [hsz]; exact hg, ⟨by rw [hsz]; omega, ?_⟩, ?_⟩, tE.fr,
    fun k h1 h2 hk ↦ hU k (by gomega) hk⟩
  · show EWAt sE.mem (wd p.env.work whirR.off) (sW.claim + lam * oodValue + lam * lam * batched)
    rw [← hX]
    refine ⟨?_, ?_⟩
    · rw [tE.mem _ (by gomega)]; fsimp; rw [h9]
    · rw [wd_wd, tE.mem _ (by gomega)]; fsimp; rw [h10]
  · refine hal.congr fun j hj ↦ ?_
    gnorm at hj
    simp only [Region.at, wd_wd]
    exact hU _ (by gomega) (by unfold glueWritten; gnorm; omega)
  · rw [hsz]
    simp only [Region.at, wd_wd]
    rw [tE.mem _ (by gomega)]
    fsimp
    rsimp
    rw [show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toUInt64_add]
  · intro i hi
    have hi' : i < g + 2 := by rw [hsz] at hi; exact hi
    by_cases hig : i < g
    · have e : (glueLevel sW lam mu oodPoint oodValue qs qw batched).glued[i]'hi = sW.glued[i] :=
        Array.getElem_append_left hig
      rw [e]
      refine (hgl i hig).congr fun j hj ↦ ?_
      gnorm at hj
      simp only [Region.at, wd_wd]
      exact hU _ (by gomega) (by unfold glueWritten; gnorm; omega)
    · obtain rfl | rfl : i = g ∨ i = g + 1 := by omega
      · have e : (glueLevel sW lam mu oodPoint oodValue qs qw batched).glued[g]'hi =
            ⟨lam, sW.alphas.size, .eq oodPoint⟩ := by
          simp [glueLevel, g]
        rw [e]
        refine ⟨⟨?_, ?_⟩, ⟨hacnt.1, ?_⟩, ?_, ⟨by rw [hpsz]; exact hmu30, ⟨by rw [hpsz]; exact hmu.1, ?_⟩,
          fun i hi ↦ ⟨?_, ?_⟩⟩⟩
        all_goals simp only [Region.at, wd_wd]
        all_goals rw [tE.mem _ (by gomega)]
        all_goals fsimp
        all_goals try rsimp
        · rw [hpsz]
        · refine mem_at (b := spO + 2 * i) (by gomega) ?_
          have := (hpt i hi).1
          rwa [wd_wd] at this
        · refine mem_at (b := spO + 2 * i + 1) (by gomega) ?_
          have := (hpt i hi).2
          rwa [wd_wd, wd_wd] at this
      · have e : (glueLevel sW lam mu oodPoint oodValue qs qw batched).glued[g + 1]'hi =
            ⟨lam * lam, sW.alphas.size, .induced mu qs qw⟩ := by
          simp [glueLevel, g]
        rw [e]
        refine ⟨⟨?_, ?_⟩, ⟨hacnt.1, ?_⟩, ?_, ⟨hmu.1, ?_⟩, ⟨hq.1, ⟨hq.2.1.1, ?_⟩, fun i hi ↦ ?_⟩, ?_⟩
        rotate_right
        · have eP : wd (wd (Region.at p.env.work whirR) (whirGluedOff + 1 + gluedWords * (g + 1)))
              gluedWOff = wd p.env.work (gslot (g + 1) + gluedWOff) := by
            simp only [Region.at, wd_wd]; exact congrArg (wd p.env.work) (by gomega)
          rw [eP]
          exact hqw.congr fun j hj ↦ by rw [wd_wd]; exact hWt j hj
        all_goals simp only [Region.at, wd_wd]
        all_goals rw [tE.mem _ (by gomega)]
        all_goals fsimp
        all_goals try rsimp
        · refine mem_at (b := queriesR.off) (by gomega) ?_
          exact hq.2.1.2
        · refine mem_at (b := queriesR.off + (1 + i)) (by gomega) ?_
          have := hq.2.2 i hi
          rwa [wd_wd, wd_wd] at this

end NativeVm.Code.P7
