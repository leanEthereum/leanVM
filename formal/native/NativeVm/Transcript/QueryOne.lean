module

public import NativeVm.Transcript.QueryClimb
public import NativeVm.Transcript.SeedBytes

/-!
# One opening

`openOne_spec`: the opening at `r13`, its position at `r10`: its leaf index checked against the
position, its leaf hashed and copied to the rows at `r12` (`copyRow_spec`), its path climbed
(`climbLoop_spec`) and the top checked against the root (`checkRoot_spec`). It ends normally exactly
when the opening checks out (`OpenOk`), writing only the scratch area, the climb's input and the
row's words.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

variable {s : QState} {E : QState → Prop}

theorem wd_shift (b : UInt64) (k j : Nat) : wd (wd b k) j = wd b (k + j) := wd_add b k j

theorem add8_wd (b : UInt64) (k : Nat) : wd b k + 8 = wd b (k + 1) := by rw [← wd_add]; rfl

/-- The row copy: `r15` words from `r9` to `r12`. -/
def copyRowBody : Stmt := blk [
  I (.load .rax (at_ .r9 0)), I (.store (at_ .r12 0) .rax),
  I (.addi .r9 8), I (.addi .r12 8), I (.subi .r15 1)]

/-- **A row copied**: `w` words from `r9` to `r12`. -/
theorem copyRow_spec {O R : UInt64} {b m n w : Nat} {f : Nat → UInt64}
    (hr9 : s.reg .r9 = wd O b) (hr12 : s.reg .r12 = wd R m) (hr15 : s.reg .r15 = w.toUInt64)
    (hfR : Fits R n) (hmn : m + w ≤ n)
    (hv : ∀ t < w, s.mem (wd O (b + t)) = some (f t))
    (hne : ∀ t < w, ∀ t' < w, wd O (b + t) ≠ wd R (m + t'))
    (hd : ∀ t < w, (s.mem (wd R (m + t))).isSome) :
    WP (.loop (.cmp .ne .r15 (.imm 0)) copyRowBody) s (fun s' ↦
      (∀ t < w, s'.mem (wd R (m + t)) = some (f t)) ∧
      Keep (fun a ↦ ∃ t < w, a = wd R (m + t)) s.mem s'.mem ∧
      s'.reg .r9 = wd O (b + w) ∧ s'.reg .r12 = wd R (m + w) ∧
      RegsFrame [.rax, .r9, .r12, .r15] s s') E := by
  have hn : n ≤ 2 ^ 61 := by unfold Fits at hfR; have := R.toNat_lt; omega
  refine WP.loop (fun s' ↦ ∃ j ≤ w, s'.reg .r15 = (w - j).toUInt64 ∧ s'.reg .r9 = wd O (b + j) ∧
      s'.reg .r12 = wd R (m + j) ∧ (∀ t < j, s'.mem (wd R (m + t)) = some (f t)) ∧
      Keep (fun a ↦ ∃ t < j, a = wd R (m + t)) s.mem s'.mem ∧ RegsFrame [.rax, .r9, .r12, .r15] s s')
    (fun s' ↦ (s'.reg .r15).toNat) ⟨0, by omega, by rw [hr15]; rfl, hr9, hr12,
      fun t ht ↦ absurd ht (by omega), fun _ _ ↦ rfl, rf_refl _ _⟩ ?_ ?_
  · rintro s' ⟨j, hj, h15, h9, h12, hw, hk, hr⟩ hc
    have hjw : j < w := by
      rw [cond_ne, rhs_imm, h15, bne_iff_ne, ne_eq] at hc
      by_contra h
      exact hc (by rw [show w - j = 0 by omega]; rfl)
    have hRj : ∀ t, t < j → wd R (m + j) ≠ wd R (m + t) := fun t ht e ↦ by
      rw [wd_inj (by omega) (by omega)] at e; omega
    refine wp_load (x := wd O (b + j)) (by rw [eval_at0, h9]) (by
      rw [hk _ fun ⟨t, ht, e⟩ ↦ hne j hjw t (by omega) e]; exact hv j hjw) ?_
    refine wp_store (x := wd R (m + j)) (by rw [eval_at0]; reg_simp; exact h12) (by
      rw [QState.setReg_mem, hk _ fun ⟨t, ht, e⟩ ↦ hRj t ht e]; exact hd j hjw) ?_
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_done ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)))
    · reg_simp
      rw [h15, sub1_toUInt64 (by omega) (by omega)]
      congr 1
    · reg_simp; rw [h9, add8_wd, Nat.add_assoc]
    · reg_simp; rw [h12, add8_wd, Nat.add_assoc]
    · intro t ht
      simp only [QState.setReg_mem, QState.setMem_mem, QState.setReg_reg, ↓reduceIte]
      split
      · rename_i e
        rw [wd_inj (by omega) (by omega)] at e
        rw [show t = j by omega]
      · rename_i e
        rw [wd_inj (by omega) (by omega)] at e
        exact hw t (by omega)
    · intro a ha
      simp only [QState.setReg_mem, QState.setMem_mem]
      rw [ite_of_not fun e ↦ ha ⟨j, by omega, e⟩]
      exact hk a fun ⟨t, ht, e⟩ ↦ ha ⟨t, by omega, e⟩
    · rf_tac; exact hr
    · reg_simp
      rw [h15, sub1_toUInt64 (by omega) (by omega),
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro s' ⟨j, hj, h15, h9, h12, hw, hk, hr⟩ hc
    have hjw : j = w := by
      rw [cond_ne, rhs_imm, h15, bne_eq_false_iff_eq] at hc
      have := congrArg UInt64.toNat hc
      rw [toNat_toUInt64 (by omega), show (Int64.toUInt64 0).toNat = 0 from rfl] at this
      omega
    subst hjw
    exact ⟨hw, hk, h9, h12, hr⟩

/-! ## The opening -/

/-- The registers `query` writes: all but `rdi`, `rsp` and `rbp`. -/
def queryClobbers : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- What one opening writes: the climb's words and the row's. -/
def OneW (ctx R : UInt64) (m w : Nat) (a : UInt64) : Prop := ClimbW ctx a ∨ ∃ t < w, a = wd R (m + t)

theorem rf_back {l l' : List Reg64} {s₁ s₂ s₃ : QState} (h' : RegsFrame l' s₂ s₃) (hl : l' ⊆ l)
    (h : RegsFrame l s₁ s₂) : RegsFrame l s₁ s₃ := rf_trans h h' (fun _ h ↦ h) hl

theorem add8 (b : UInt64) : b + 8 = wd b 1 := by rw [← add8_wd, wd_zero]

theorem leaf_holds (l : List K) : Keccak.HoldsBytes (l.map K.lane) (8 * l.length) := by
  refine ⟨by simp; omega, fun x hx ↦ ?_⟩
  rw [List.drop_eq_nil_of_le (by rw [wordsBytes_length]; simp)] at hx
  cases hx

theorem leaf_hash (o : Opening) :
    keccak256 ((Keccak.wordsBytes (o.leaf.map K.lane)).take (8 * o.leaf.length)) = openingDigest o := by
  rw [List.take_of_length_le (by rw [wordsBytes_length]; simp), ← flatMap_toBytes]
  rfl

theorem ctx_not_climbW {ctx : UInt64} {k : Nat}
    (hk : k < scratchW ∨ (scratchW + Keccak.scratchWords ≤ k ∧ k < climbW) ∨ qRootW ≤ k)
    (hk' : k < 2 ^ 61) : ¬ ClimbW ctx (wd ctx k) := by
  rintro (h | h)
  · exact not_ctxIn (by lay_omega) hk' (by lay_omega) h
  · exact not_ctxIn (by lay_omega) hk' (by lay_omega) h

/-- **One opening**, at `r13`, its position at `r10`, its row to `r12`. -/
theorem openOne_spec {ctx O R Pa : UInt64} {m n q c height width : Nat} {root : Digest}
    {o : Opening} (hrdi : s.reg .rdi = ctx) (hdom : Dom ctx s.mem) (hfc : Fits ctx ctxEnd)
    (hroot : ∀ k < 4, s.mem (wd ctx (qRootW + k)) = some (root.toList.getD k 0))
    (hh : s.mem (wd ctx (qRootW + 4)) = some height.toUInt64)
    (hw : s.mem (wd ctx (qRootW + 5)) = some width.toUInt64)
    (hh32 : height ≤ wireMaxHeight) (hw64 : width ≤ wireMaxLeafWords)
    (hll : o.leaf.length = width) (hpl : o.path.length = height) (hidx : o.leafIndex < 2 ^ 32)
    (hr13 : s.reg .r13 = O) (hfO : Fits O openingWords) (hdO : Disj O openingWords ctx ctxEnd)
    (hO0 : s.mem (wd O 0) = some o.leafIndex.toUInt64)
    (hleaf : ∀ t < width, s.mem (wd O (1 + t)) = some (o.leaf.getD t 0).lane)
    (hpath : ∀ d < height, ∀ l < 4, s.mem (wd O (1 + wireMaxLeafWords + 4 * d + l)) =
      some ((o.path.getD d default).toList.getD l 0))
    (hr10 : s.reg .r10 = Pa) (hPa : s.mem Pa = some q.toUInt64) (hq : q < 2 ^ 64)
    (hr12 : s.reg .r12 = wd R m) (hmn : m + width ≤ n) (hfR : Fits R n)
    (hdR : Disj R n ctx ctxEnd) (hdOR : Disj O openingWords R n)
    (hRs : ∀ t < width, (s.mem (wd R (m + t))).isSome)
    (hr11 : s.reg .r11 = c.toUInt64) (hc : 0 < c) (hc' : c < 2 ^ 64) :
    WP openOne s (fun s' ↦ OpenOk root q o ∧
        (∀ t < width, s'.mem (wd R (m + t)) = some (o.leaf.getD t 0).lane) ∧
        Keep (OneW ctx R m width) s.mem s'.mem ∧ s'.reg .r10 = Pa + 8 ∧
        s'.reg .r13 = wd O openingWords ∧ s'.reg .r12 = wd R (m + width) ∧
        s'.reg .r11 = (c - 1).toUInt64 ∧ RegsFrame queryClobbers s s')
      (fun s' ↦ ¬ OpenOk root q o ∧ s'.reg .rdi = ctx ∧ Keep (OneW ctx R m width) s.mem s'.mem) := by
  have hoW : openingWords = 193 := openingWords_val
  have hlW : wireMaxLeafWords = 64 := wireMaxLeafWords_val
  have hhW : wireMaxHeight = 32 := wireMaxHeight_val
  have hOc : ∀ i < openingWords, ∀ k < ctxEnd, wd O i ≠ wd ctx k :=
    fun i hi k hk ↦ wd_ne_of_disj hfO hfc hdO hi hk
  have hOR : ∀ i < openingWords, ∀ k < n, wd O i ≠ wd R k :=
    fun i hi k hk ↦ wd_ne_of_disj hfO hfR hdOR hi hk
  have hRc : ∀ i < n, ∀ k < ctxEnd, wd R i ≠ wd ctx k :=
    fun i hi k hk ↦ wd_ne_of_disj hfR hfc hdR hi hk
  have hOW : ∀ i < openingWords, ∀ t < width, ¬ OneW ctx R m width (wd O i) :=
    fun i hi t ht ↦ by
      rintro (h | ⟨t', ht', e⟩)
      · exact not_climbW (fun k hk ↦ hOc i hi k hk) h
      · exact hOR i hi _ (by omega) e
  have hOscr : ∀ i < openingWords, ¬ CtxIn ctx scratchW (scratchW + Keccak.scratchWords) (wd O i) :=
    fun i hi ⟨k, _, hk, e⟩ ↦ hOc i hi k (by lay_omega) e
  have hOrow : ∀ i < openingWords, ¬ ∃ t < width, wd O i = wd R (m + t) :=
    fun i hi ⟨t, ht, e⟩ ↦ hOR i hi _ (by omega) e
  have hCrow : ∀ k < ctxEnd, ¬ ∃ t < width, wd ctx k = wd R (m + t) :=
    fun k hk ⟨t, ht, e⟩ ↦ hRc _ (by omega) k hk e.symm
  have hRscr : ∀ t < width, ¬ CtxIn ctx scratchW (scratchW + Keccak.scratchWords) (wd R (m + t)) :=
    fun t ht ⟨k, _, hk, e⟩ ↦ hRc _ (by omega) k (by lay_omega) e
  unfold openOne
  refine wp_load (x := wd O 0) (by rw [eval_at0, hr13, wd_zero]) hO0 ?_
  refine wp_load (x := Pa) (by rw [eval_at0]; reg_simp; exact hr10) (by reg_simp; exact hPa) ?_
  by_cases hiq : o.leafIndex = q
  swap
  · refine wp_failIf_fail ?_ ⟨fun h ↦ hiq h.1, by reg_simp; exact hrdi, Keep.refl _ _⟩
    rw [cond_ne, rhs_reg]
    reg_simp
    exact bne_iff_ne.mpr fun e ↦ hiq ((toUInt64_inj (by omega) hq).mp e)
  refine wp_failIf (by rw [cond_ne, rhs_reg]; reg_simp; rw [hiq]; exact bne_self_eq_false _) ?_
  refine wp_reg rfl (wp_load (eval_cw (by reg_simp; exact hrdi) _) (by reg_simp; exact hw)
    (wp_reg rfl ?_))
  refine wp_then' (hashAt_spec (ctx := ctx) (ws := o.leaf.map K.lane) (len := 8 * width)
    (by reg_simp; exact hrdi) (by rw [← hll]; exact leaf_holds _)
    (by reg_simp; rw [toUInt64_shl _ _ (by omega), show 2 ^ 3 * width = 8 * width by omega]) (by omega)
    (fun i hi ↦ ?_) (fun k hk ↦ ?_) (fun i hi k hk ↦ ?_)) ?_
  · rw [List.length_map, hll] at hi
    rw [eval_at]
    reg_simp
    rw [hr13, add8, wd_add, List.getElem_map, ← List.getD_eq_getElem _ 0, hleaf i hi]
  · reg_simp
    exact hdom _ (by lay_omega)
  · rw [List.length_map, hll] at hi
    rw [eval_at]
    reg_simp
    rw [hr13, add8, wd_add]
    exact hOc _ (by lay_omega) _ (by lay_omega)
  rintro s₂ ⟨h2, -, k2, r2⟩ hs2
  have e2 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8] → r ≠ .rax → r ≠ .r14 →
      s₂.reg r = s.reg r := fun r hr h1 h2' ↦ by
    rw [r2 r hr]
    simp_all
  refine wp_load (eval_cw (b := ctx) (by rw [e2 _ (by simp) (by simp) (by simp)]; exact hrdi) _)
    (by rw [k2 _ (not_ctxIn (by lay_omega) (by lay_omega) (by lay_omega))]; exact hw) ?_
  refine wp_reg rfl ?_
  refine wp_then' (copyRow_spec (O := O) (b := 1) (f := fun t ↦ (o.leaf.getD t 0).lane) (n := n)
    (by rw [eval_at]; reg_simp; rw [e2 _ (by simp) (by simp) (by simp), hr13, add8])
    (by reg_simp; rw [e2 _ (by simp) (by simp) (by simp), hr12]) (by reg_simp) hfR hmn
    (fun t ht ↦ by reg_simp; rw [k2 _ (hOscr _ (by lay_omega))]; exact hleaf t ht)
    (fun t ht t' ht' ↦ hOR _ (by lay_omega) _ (by omega))
    (fun t ht ↦ by reg_simp; rw [k2 _ (hRscr t ht)]; exact hRs t ht)) ?_
  rintro s₃ ⟨h3, k3, -, g12, r3⟩ hs3
  have e3 : ∀ r, r ∉ [Reg64.rax, .r9, .r12, .r15] → s₃.reg r = s₂.reg r := fun r hr ↦ by
    rw [r3 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [QState.setReg_reg, hr.2.1, hr.2.2.2, ↓reduceIte]
  have e14 : s₂.reg .r14 = q.toUInt64 := by rw [r2 _ (by simp)]; reg_simp
  have hdom3 : Dom ctx s₃.mem := (hdom.of_isSome hs2).of_isSome hs3
  refine wp_load (eval_cw (b := ctx) (by rw [e3 _ (by simp), e2 _ (by simp) (by simp) (by simp)]; exact hrdi) _)
    (by rw [k3 _ (hCrow _ (by lay_omega))]; simp only [QState.setReg_mem]
        rw [k2 _ (not_ctxIn (by lay_omega) (by lay_omega) (by lay_omega))]; exact hh) ?_
  refine wp_reg rfl ?_
  refine wp_then (climbLoop_spec (O := O) (b := 1 + wireMaxLeafWords) (node := openingDigest o)
    (path := o.path) (q := q)
    (by reg_simp; rw [e3 _ (by simp), e2 _ (by simp) (by simp) (by simp)]; exact hrdi) hdom3
    (fun k hk ↦ by
      reg_simp
      rw [k3 _ (hCrow _ (by lay_omega))]; simp only [QState.setReg_mem]
      rw [h2 k hk, ← hll, leaf_hash, getD_toList _ hk])
    (by
      simp only [QState.setReg_reg, ↓reduceIte]
      rw [eval_at]
      reg_simp
      rw [e3 _ (by simp), e2 _ (by simp) (by simp) (by simp), hr13, wdisp_toUInt64]
      rfl)
    (fun d hd l hl ↦ by
      reg_simp
      rw [k3 _ (hOrow _ (by omega))]; simp only [QState.setReg_mem]
      rw [k2 _ (hOscr _ (by omega))]
      exact hpath d (by omega) l hl)
    (fun i hi k hk ↦ by rw [Nat.add_assoc]; exact hOc _ (by omega) k hk)
    (by reg_simp; rw [e3 _ (by simp), e14]) hq (by reg_simp; rw [hpl]) (by omega)) ?_
  rintro s₅ ⟨h5, k5, r5⟩
  have e5 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r14, .r15] →
      s₅.reg r = s₃.reg r := fun r hr ↦ by
    rw [r5 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [QState.setReg_reg, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ↓reduceIte]
  have hrdi5 : s₅.reg .rdi = ctx := by
    rw [e5 _ (by simp), e3 _ (by simp), e2 _ (by simp) (by simp) (by simp)]; exact hrdi
  have K5 : Keep (OneW ctx R m width) s.mem s₅.mem :=
    Keep.trans (Keep.trans k2 k3 (V := OneW ctx R m width) (fun _ h ↦ .inl (.inl h))
      (fun _ h ↦ .inr h)) k5 (fun _ h ↦ h) (fun _ h ↦ .inl h)
  refine wp_then (WP.mono (checkRoot_spec (top := climbK (openingDigest o) q o.path) (root := root)
    hrdi5 h5 (fun k hk ↦ by
      rw [k5 _ (ctx_not_climbW (by lay_omega) (by lay_omega))]; simp only [QState.setReg_mem]
      rw [k3 _ (hCrow _ (by lay_omega))]; simp only [QState.setReg_mem]
      rw [k2 _ (not_ctxIn (by lay_omega) (by lay_omega) (by lay_omega))]
      exact hroot k hk)) (fun _ h ↦ h)
    (fun s₆ ⟨hne, hm, hr⟩ ↦ ⟨fun h ↦ hne h.2, by rw [hr _ (by simp)]; exact hrdi5,
      fun a ha ↦ by rw [hm]; exact K5 a ha⟩)) ?_
  rintro s₆ ⟨htop, hm, r6⟩
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_done ⟨⟨hiq, htop⟩, fun t ht ↦ ?_,
    fun a ha ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩)))
  · reg_simp
    rw [hm, k5 _ (not_climbW fun k hk ↦ hRc _ (by omega) k hk)]
    simp only [QState.setReg_mem]
    exact h3 t ht
  · simp only [QState.setReg_mem]
    rw [hm]
    exact K5 a ha
  · reg_simp
    rw [r6 _ (by simp), e5 _ (by simp), e3 _ (by simp), e2 _ (by simp) (by simp) (by simp), hr10]
  · reg_simp
    rw [r6 _ (by simp), e5 _ (by simp), e3 _ (by simp), e2 _ (by simp) (by simp) (by simp), hr13,
      wdisp_toUInt64]
    rfl
  · reg_simp
    rw [r6 _ (by simp), e5 _ (by simp), g12]
  · reg_simp
    rw [r6 _ (by simp), e5 _ (by simp), e3 _ (by simp), e2 _ (by simp) (by simp) (by simp), hr11,
      sub1_toUInt64 hc hc']
  · unfold queryClobbers
    rf_tac
    refine rf_back r6 (by simp) ?_
    refine rf_back r5 (by simp) ?_
    rf_tac
    refine rf_back r3 (by simp) ?_
    rf_tac
    refine rf_back r2 (by simp) ?_
    rf_tac

end NativeVm.Transcript
