module

public import NativeVm.Code.Data
public import NativeVm.Field.K
public import NativeVm.Equiv.Field

/-!
# Phase 7: the novel basis's evaluation

`novelEvalC`: `(r9, r10) := novelEval cs what` (`NativeVm.Model.novelEval`), the coefficients
`cs` at `r13` (`EWArr`, `r15` of them, at most `64`), the values `what` at `rsi` (`WordArr`, `rdx`
of them), a buffer of `novelBufWords` words at `rbx`.

It runs in two passes over the buffer `B` (kept in `rbp`):

* `novelBasisC` writes `novelBasis`'s fold before its `extract` (`novelStep`): `B[0] := 1`, then
  for each value `v` of `what`, while the basis's size `n` (`r11`) is below the count (`r15`),
  `B[n + i] := B[i] · v` for `i < n` (`novelDouble`) and `n := 2 n`. The size stays a power of two
  at most `64` (`novelPow`), so the basis fits the buffer.
* `novelSum` adds `B[i] · cs[i]` for `i < min n count`, the length of `novelEval`'s `zipWith`.

Each product is `NativeVm.Field.kmul` (`novelKmul`: the model's `kmul` on words).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Transcript

/-! ## Products and the buffer -/

/-- `Field.kmul` computes the model's `kmul` on words. -/
theorem novelKmul (s : QState) {F : QState → Prop} :
    WP Field.kmul s (fun s' ↦ s'.reg .rax = kmul (s.reg .rax) (s.reg .rbx) ∧ s'.mem = s.mem ∧
      RegsFrame Field.kRegs s s') F :=
  WP.mono (Field.kmul_spec s)
    (fun _ ⟨h1, h2, h3⟩ ↦ ⟨Field.ofLane_injective (by rw [h1, Equiv.K_ofLane_kmul]), h2, h3⟩)
    (fun _ h ↦ h)

/-- The words of the basis buffer. -/
def novelBufWords : Nat := 64

/-- The first `m` words at `B` are those of `xs`. -/
def novelBuf (mem : UInt64 → Option UInt64) (B : UInt64) (xs : Array UInt64) (m : Nat) : Prop :=
  ∀ k < m, mem (wd B k) = some (xs.getD k 0)

/-- `mem'` is `mem` outside the buffer at `B`. -/
def novelKeep (mem mem' : UInt64 → Option UInt64) (B : UInt64) : Prop :=
  ∀ a, (∀ k < novelBufWords, a ≠ wd B k) → mem' a = mem a

/-- The buffer's words exist. -/
def novelSome (mem : UInt64 → Option UInt64) (B : UInt64) : Prop :=
  ∀ k < novelBufWords, (mem (wd B k)).isSome

/-- A basis size: a power of two at most `64`. -/
def novelPow (n : Nat) : Prop := n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64

theorem novelBuf_setMem {s : QState} {B : UInt64} {xs : Array UInt64} {m : Nat} {v : UInt64}
    (h : novelBuf s.mem B xs m) (hm : m < 2 ^ 61) (hv : xs.getD m 0 = v) :
    novelBuf (s.setMem (wd B m) v).mem B xs (m + 1) := fun k hk ↦ by
  rw [QState.setMem_mem]
  by_cases e : k = m
  · subst e
    rw [ite_eq_left rfl, hv]
  · rw [ite_eq_right (fun h' ↦ e ((wd_inj (by omega) hm).mp h'))]
    exact h k (by omega)

theorem novelKeep_setMem {mem : UInt64 → Option UInt64} {s : QState} {B : UInt64}
    (h : novelKeep mem s.mem B) {k : Nat} (hk : k < novelBufWords) (v : UInt64) :
    novelKeep mem (s.setMem (wd B k) v).mem B := fun a ha ↦ by
  rw [QState.setMem_mem, ite_eq_right (ha k hk)]
  exact h a ha

theorem novelSome_setMem {s : QState} {B : UInt64} (h : novelSome s.mem B) (a v : UInt64) :
    novelSome (s.setMem a v).mem B := fun k hk ↦ Field.isSome_setMem (h k hk) a v

theorem novel_getD_left {bs ys : Array UInt64} {k : Nat} (h : k < bs.size) :
    (bs ++ ys).getD k 0 = bs.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem novel_getD_right {bs ys : Array UInt64} {k : Nat} :
    (bs ++ ys).getD (bs.size + k) 0 = ys.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right]

theorem novel_getD_map {bs : Array UInt64} {f : UInt64 → UInt64} {k : Nat} (h : k < bs.size) :
    (bs.map f).getD k 0 = f (bs.getD k 0) := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- An address indexed in words from a base. -/
theorem novel_idx {s : QState} {base ix : Reg64} {b : UInt64} {i : Nat} (hb : s.reg base = b)
    (hi : s.reg ix = i.toUInt64) :
    ({ base := base, idx := some (ix, .W64) } : Addr).eval s = wd b i := by
  have := eval_idx64' (s := s) (j := 0) (k := 0) (d := 0) (by rw [hb, wd_zero]) hi (by decide)
  simpa using this

/-! ## The basis -/

/-- One step of `novelBasis`'s fold. -/
def novelStep (count : Nat) (basis : Array UInt64) (value : UInt64) : Array UInt64 :=
  if count ≤ basis.size then basis else basis ++ basis.map (kmul · value)

theorem novelBasis_eq (what : Array UInt64) (count : Nat) :
    novelBasis what count = (what.foldl (novelStep count) #[1]).extract 0 count := (rfl)

/-- The basis after the first `j` values. -/
def novelPre (what : Array UInt64) (count j : Nat) : Array UInt64 :=
  (what.toList.take j).foldl (novelStep count) #[1]

theorem novelPre_succ {what : Array UInt64} {count j : Nat} (hj : j < what.size) :
    novelPre what count (j + 1) = novelStep count (novelPre what count j) what[j] := by
  rw [novelPre, novelPre, List.take_add_one, List.foldl_append, Array.getElem?_toList,
    Array.getElem?_eq_getElem hj]
  rfl

theorem novelPre_size (what : Array UInt64) (count : Nat) :
    novelPre what count what.size = what.foldl (novelStep count) #[1] := by
  rw [novelPre, List.take_of_length_le (by simp), Array.foldl_toList]

/-- The registers `novelDouble` writes. -/
abbrev novelDRegs : List Reg64 := [.rax, .rbx, .rcx, .r8, .r10, .r12]

/-- `B[n + i] := B[i] · r14` for `i` from `r12` (`0`) to `n = r11`, `B` at `rbp`. -/
def novelDouble : Stmt := .loop (.cmp .ltu .r12 (.reg .r11)) (blk [
  I (.load .rax { base := .rbp, idx := some (.r12, .W64) }), I (.mov .rbx .r14), Field.kmul,
  I (.mov .r10 .r12), I (.add .r10 .r11),
  I (.store { base := .rbp, idx := some (.r10, .W64) } .rax), I (.addi .r12 1)])

/-- **`novelDouble` appends the basis times `v`.** -/
theorem novelDouble_spec {t : QState} {F : QState → Prop} {B v : UInt64} {bs : Array UInt64}
    (hbp : t.reg .rbp = B) (h11 : t.reg .r11 = bs.size.toUInt64) (h14 : t.reg .r14 = v)
    (h12 : t.reg .r12 = 0) (hn : 2 * bs.size ≤ novelBufWords) (hb : novelBuf t.mem B bs bs.size)
    (hS : novelSome t.mem B) :
    WP novelDouble t (fun t' ↦ novelBuf t'.mem B (bs ++ bs.map (kmul · v)) (2 * bs.size) ∧
      novelKeep t.mem t'.mem B ∧ novelSome t'.mem B ∧ RegsFrame novelDRegs t t') F := by
  unfold novelDouble novelBufWords at *
  apply WP.loop (fun u ↦ ∃ i ≤ bs.size, u.reg .r12 = i.toUInt64 ∧
      novelBuf u.mem B (bs ++ bs.map (kmul · v)) (bs.size + i) ∧ novelKeep t.mem u.mem B ∧
      novelSome u.mem B ∧ RegsFrame novelDRegs t u)
    (fun u ↦ bs.size - (u.reg .r12).toNat)
  · refine ⟨0, Nat.zero_le _, h12, fun k hk ↦ ?_, fun _ _ ↦ rfl, hS, rf_refl _ _⟩
    rw [novel_getD_left (by omega)]
    exact hb k (by omega)
  · intro u ⟨i, hi, u12, hB, hK, hSu, hf⟩ hc
    have u11 : u.reg .r11 = bs.size.toUInt64 := by rw [hf .r11 (by decide), h11]
    have hlt : i < bs.size := by
      rw [cond_ltu, rhs_reg, u12, u11, decide_eq_true_eq, toUInt64_lt (by omega) (by omega)] at hc
      exact hc
    have ubp : u.reg .rbp = B := by rw [hf .rbp (by decide), hbp]
    have u14 : u.reg .r14 = v := by rw [hf .r14 (by decide), h14]
    refine wp_load (novel_idx ubp u12) (hB i (by omega)) ?_
    fstep
    refine Field.WP.then (novelKmul _) fun u₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1 e2
    have g : ∀ r ∉ Field.kRegs, u₁.reg r = u.reg r := fun r hr ↦ by
      rw [e3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.1, hr.2.1]
    fstep; fstep
    refine wp_store (novel_idx (i := bs.size + i) (by rsimp; rw [g .rbp (by decide), ubp])
      (by rsimp; rw [g .r12 (by decide), g .r11 (by decide), u12, u11, toUInt64_add,
        Nat.add_comm])) (by rsimp; rw [e2]; exact hSu _ (by unfold novelBufWords; omega)) ?_
    fstep
    fdone
    rw [e1, u14]
    refine ⟨⟨i + 1, hlt, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [g .r12 (by decide), u12, toUInt64_succ]
    · rw [← Nat.add_assoc]
      refine novelBuf_setMem (e2 ▸ hB) (by omega) ?_
      rw [novel_getD_right, novel_getD_map hlt, novel_getD_left hlt]
    · exact novelKeep_setMem (e2 ▸ hK) (by unfold novelBufWords; omega) _
    · exact novelSome_setMem (e2 ▸ hSu) _ _
    · intro r hr
      simp only [novelDRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨ha, hb', hc', h8, h10, h12'⟩ := hr
      simp only [QState.setReg_reg, QState.setMem_reg, h10, h12', ↓reduceIte]
      rw [g r (by simp [Field.kRegs, *]), hf r (by simp [novelDRegs, *])]
    · rw [g .r12 (by decide), u12, toUInt64_succ, toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro u ⟨i, hi, u12, hB, hK, hSu, hf⟩ hc
    have u11 : u.reg .r11 = bs.size.toUInt64 := by rw [hf .r11 (by decide), h11]
    have hge : bs.size ≤ i := by
      rw [cond_ltu, rhs_reg, u12, u11, decide_eq_false_iff_not,
        toUInt64_lt (by omega) (by omega)] at hc
      omega
    obtain rfl : i = bs.size := by omega
    exact ⟨by rw [Nat.two_mul]; exact hB, hK, hSu, hf⟩

/-- The registers `novelGrow` writes. -/
abbrev novelGRegs : List Reg64 := [.rax, .rbx, .rcx, .r8, .r10, .r11, .r12]

/-- One step of the fold: double the basis by `r14` while its size `r11` is below `r15`. -/
def novelGrow : Stmt := .ite (.cmp .ltu .r11 (.reg .r15))
  (blk [I (.movi .r12 0), novelDouble, I (.add .r11 .r11)]) .skip

/-- **`novelGrow` is `novelStep`.** -/
theorem novelGrow_spec {t : QState} {F : QState → Prop} {B v : UInt64} {bs : Array UInt64}
    {count : Nat} (hbp : t.reg .rbp = B) (h11 : t.reg .r11 = bs.size.toUInt64)
    (h14 : t.reg .r14 = v) (h15 : t.reg .r15 = count.toUInt64) (hc64 : count ≤ novelBufWords)
    (hp : novelPow bs.size) (hb : novelBuf t.mem B bs bs.size) (hS : novelSome t.mem B) :
    WP novelGrow t (fun t' ↦ t'.reg .r11 = (novelStep count bs v).size.toUInt64 ∧
      novelPow (novelStep count bs v).size ∧
      novelBuf t'.mem B (novelStep count bs v) (novelStep count bs v).size ∧
      novelKeep t.mem t'.mem B ∧ novelSome t'.mem B ∧ RegsFrame novelGRegs t t') F := by
  unfold novelBufWords at hc64
  have hp64 : bs.size ≤ 64 := by unfold novelPow at hp; omega
  unfold novelGrow
  by_cases hlt : bs.size < count
  · have hc : (Cond.cmp .ltu .r11 (.reg .r15)).eval t = true := by
      rw [cond_ltu, rhs_reg, h11, h15, decide_eq_true_eq, toUInt64_lt (by omega) (by omega)]
      exact hlt
    refine wp_ite_true hc ?_
    have hst : novelStep count bs v = bs ++ bs.map (kmul · v) := ite_eq_right (by omega)
    have hsz : (novelStep count bs v).size = 2 * bs.size := by
      rw [hst, Array.size_append, Array.size_map, Nat.two_mul]
    rw [hst] at hsz ⊢
    fstep
    refine Field.WP.then (novelDouble_spec (v := v) (bs := bs) (by rsimp; exact hbp)
      (by rsimp; exact h11)
      (by rsimp; exact h14) (by rsimp) (by unfold novelPow at hp; unfold novelBufWords; omega)
      hb hS) fun u ⟨hB, hK, hSu, hf⟩ ↦ ?_
    have u11 : u.reg .r11 = bs.size.toUInt64 := by rw [hf .r11 (by decide)]; rsimp; exact h11
    fstep
    fdone
    refine ⟨?_, ?_, hsz ▸ hB, hK, hSu, ?_⟩
    · rw [u11, hsz, toUInt64_add, Nat.two_mul]
    · rw [hsz]; unfold novelPow at hp ⊢; omega
    · exact rf_setReg (l := novelGRegs) (r := .r11)
        (rf_trans (l := novelGRegs) (l'' := novelGRegs) (by rf_tac) hf) (by simp) _
  · have hc : (Cond.cmp .ltu .r11 (.reg .r15)).eval t = false := by
      rw [cond_ltu, rhs_reg, h11, h15, decide_eq_false_iff_not,
        toUInt64_lt (by omega) (by omega)]
      exact hlt
    refine wp_ite_false hc ?_
    have hst : novelStep count bs v = bs := ite_eq_left (by omega)
    rw [hst]
    exact WP.skip ⟨h11, hp, hb, fun _ _ ↦ rfl, hS, rf_refl _ _⟩

/-- `novelBasis`'s fold before its `extract` in the buffer at `rbx` (then also `rbp`), its size in
`r11`: the values at `rsi`, `rdx` of them, the count in `r15`. -/
def novelBasisC : Stmt := blk [
  I (.mov .rbp .rbx), I (.storei (at_ .rbp 0) 1), I (.movi .r11 1), I (.movi .r9 0),
  .loop (.cmp .ltu .r9 (.reg .rdx)) (blk [
    I (.load .r14 { base := .rsi, idx := some (.r9, .W64) }), novelGrow, I (.addi .r9 1)])]

/-- **`novelBasisC` writes the basis.** -/
theorem novelBasisC_spec {s : QState} {F : QState → Prop} {what : Array UInt64} {count : Nat}
    {Wp B : UInt64} (hW : WordArr s.mem Wp what) (hsi : s.reg .rsi = Wp)
    (hdx : s.reg .rdx = what.size.toUInt64) (hws : what.size ≤ 64) (hbx : s.reg .rbx = B)
    (h15 : s.reg .r15 = count.toUInt64) (hc64 : count ≤ novelBufWords)
    (hS : novelSome s.mem B) (hfB : Fits B novelBufWords) (hfW : Fits Wp what.size)
    (hBW : Disj B novelBufWords Wp what.size) :
    WP novelBasisC s (fun s' ↦ s'.reg .rbp = B ∧ s'.reg .r15 = count.toUInt64 ∧
      s'.reg .r13 = s.reg .r13 ∧
      s'.reg .r11 = (what.foldl (novelStep count) #[1]).size.toUInt64 ∧
      (what.foldl (novelStep count) #[1]).size ≤ 64 ∧
      novelBuf s'.mem B (what.foldl (novelStep count) #[1])
        (what.foldl (novelStep count) #[1]).size ∧
      novelKeep s.mem s'.mem B) F := by
  unfold novelBasisC
  fstep
  refine wp_storei (x := B) (by simp [eval_at, hbx]; rfl)
    (by rsimp; have := hS 0 (by decide); rwa [wd_zero] at this) ?_
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ j ≤ what.size, u.reg .r9 = j.toUInt64 ∧
      u.reg .rdx = what.size.toUInt64 ∧ u.reg .rsi = Wp ∧ u.reg .rbp = B ∧
      u.reg .r15 = count.toUInt64 ∧ u.reg .r13 = s.reg .r13 ∧
      u.reg .r11 = (novelPre what count j).size.toUInt64 ∧ novelPow (novelPre what count j).size ∧
      novelBuf u.mem B (novelPre what count j) (novelPre what count j).size ∧
      novelKeep s.mem u.mem B ∧ novelSome u.mem B)
    (fun u ↦ what.size - (u.reg .r9).toNat)
  · refine ⟨0, Nat.zero_le _, rfl, by rsimp; exact hdx, by rsimp; exact hsi, by rsimp; exact hbx,
      by rsimp; exact h15, by rsimp, by rsimp; rfl, Or.inl rfl, fun k hk ↦ ?_, fun a ha ↦ ?_,
      fun k hk ↦ ?_⟩
    · obtain rfl : k = 0 := by
        have : (novelPre what count 0).size = 1 := rfl
        omega
      simp only [QState.setReg_mem, QState.setMem_mem, wd_zero, ↓reduceIte]
      rfl
    · simp only [QState.setReg_mem, QState.setMem_mem]
      have := ha 0 (by decide)
      rw [wd_zero] at this
      rw [ite_eq_right this]
    · simp only [QState.setReg_mem]
      exact Field.isSome_setMem (hS k hk) _ _
  · intro u ⟨j, hj, u9, udx, usi, ubp, u15, u13, u11, hp, hB, hK, hSu⟩ hc
    have hlt : j < what.size := by
      rw [cond_ltu, rhs_reg, u9, udx, decide_eq_true_eq, toUInt64_lt (by omega) (by omega)] at hc
      exact hc
    have hwj : u.mem (wd Wp j) = some what[j] := by
      rw [hK _ fun k hk ↦ (wd_ne_of_disj hfB hfW hBW hk hlt).symm]
      exact hW j hlt
    refine wp_load (novel_idx usi u9) hwj ?_
    refine Field.WP.then (novelGrow_spec (v := what[j]) (count := count) (by rsimp; exact ubp)
      (by rsimp; exact u11) (by rsimp) (by rsimp; exact u15) hc64 hp hB hSu)
      fun u₁ ⟨e11, ep, eB, eK, eS, ef⟩ ↦ ?_
    have g : ∀ r ∉ novelGRegs, r ≠ .r14 → u₁.reg r = u.reg r := fun r hr h14 ↦ by
      rw [ef r hr]
      rsimp
      simp [h14]
    fstep
    fdone
    rw [← novelPre_succ hlt] at e11 ep eB
    refine ⟨⟨j + 1, hlt, ?_, ?_, ?_, ?_, ?_, ?_, e11, ep, eB, ?_, eS⟩, ?_⟩
    · rw [g .r9 (by decide) (by decide), u9, toUInt64_succ]
    · rw [g .rdx (by decide) (by decide), udx]
    · rw [g .rsi (by decide) (by decide), usi]
    · rw [g .rbp (by decide) (by decide), ubp]
    · rw [g .r15 (by decide) (by decide), u15]
    · rw [g .r13 (by decide) (by decide), u13]
    · exact fun a ha ↦ (eK a ha).trans (hK a ha)
    · rw [g .r9 (by decide) (by decide), u9, toUInt64_succ, toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro u ⟨j, hj, u9, udx, usi, ubp, u15, u13, u11, hp, hB, hK, hSu⟩ hc
    have hge : what.size ≤ j := by
      rw [cond_ltu, rhs_reg, u9, udx, decide_eq_false_iff_not,
        toUInt64_lt (by omega) (by omega)] at hc
      omega
    obtain rfl : j = what.size := by omega
    rw [novelPre_size] at u11 hp hB
    refine WP.blk_nil ⟨ubp, u15, u13, u11, by unfold novelPow at hp; omega, hB, hK⟩

/-! ## The sum -/

/-- `(r9, r10) += B[i] · C[i]` for `i` from `r12` to `r11`, `B` at `rbp`, `C` at `rsi`. -/
def novelSum : Stmt := .loop (.cmp .ltu .r12 (.reg .r11)) (blk [
  I (.load .rax { base := .rbp, idx := some (.r12, .W64) }), I (.load .rbx (at_ .rsi 0)),
  Field.kmul, I (.xor .r9 .rax),
  I (.load .rax { base := .rbp, idx := some (.r12, .W64) }), I (.load .rbx (at_ .rsi 8)),
  Field.kmul, I (.xor .r10 .rax),
  I (.addi .rsi 16), I (.addi .r12 1)])

/-- The sum of the first `i` elements of `zs`. -/
def novelAcc (zs : Array EW) (i : Nat) : EW := (zs.toList.take i).foldl (· + ·) 0

theorem novelAcc_succ {zs : Array EW} {i : Nat} (hi : i < zs.size) :
    novelAcc zs (i + 1) = novelAcc zs i + zs[i] := by
  rw [novelAcc, novelAcc, List.take_add_one, List.foldl_append, Array.getElem?_toList,
    Array.getElem?_eq_getElem hi]
  rfl

/-- **`novelSum` adds the products.** -/
theorem novelSum_spec {t : QState} {F : QState → Prop} {B C : UInt64} {bs : Array UInt64}
    {cs zs : Array EW} (hzc : zs.size ≤ cs.size) (hz64 : zs.size ≤ 64)
    (hz : ∀ i (h : i < zs.size), zs[i] = EW.scale (bs.getD i 0) cs[i])
    (hbp : t.reg .rbp = B) (hsi : t.reg .rsi = C) (h11 : t.reg .r11 = zs.size.toUInt64)
    (h9 : t.reg .r9 = 0) (h10 : t.reg .r10 = 0) (h12 : t.reg .r12 = 0)
    (hb : novelBuf t.mem B bs zs.size) (hC : EWArr t.mem C cs) :
    WP novelSum t (fun t' ↦ t'.reg .r9 = (sumE zs).c0 ∧ t'.reg .r10 = (sumE zs).c1 ∧
      t'.mem = t.mem) F := by
  unfold novelSum
  apply WP.loop (fun u ↦ ∃ i ≤ zs.size, u.reg .r12 = i.toUInt64 ∧ u.reg .rsi = wd C (2 * i) ∧
      u.reg .r9 = (novelAcc zs i).c0 ∧ u.reg .r10 = (novelAcc zs i).c1 ∧ u.mem = t.mem ∧
      u.reg .rbp = B ∧ u.reg .r11 = zs.size.toUInt64)
    (fun u ↦ zs.size - (u.reg .r12).toNat)
  · exact ⟨0, Nat.zero_le _, h12, by rw [hsi, Nat.mul_zero, wd_zero], h9, h10, rfl, hbp, h11⟩
  · intro u ⟨i, hi, u12, usi, u9, u10, um, ubp, u11⟩ hc
    have hlt : i < zs.size := by
      rw [cond_ltu, rhs_reg, u12, u11, decide_eq_true_eq, toUInt64_lt (by omega) (by omega)] at hc
      exact hc
    have hic : i < cs.size := by omega
    have hbi : u.mem (wd B i) = some (bs.getD i 0) := by rw [um]; exact hb i hlt
    obtain ⟨c0, c1⟩ := hC i hic
    refine wp_load (novel_idx ubp u12) hbi ?_
    refine wp_load (x := wd C (2 * i)) (by simp [eval_at, usi]; rfl)
      (by rsimp; rw [um]; exact c0) ?_
    refine Field.WP.then (novelKmul _) fun u₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1 e2
    have g : ∀ r ∉ Field.kRegs, u₁.reg r = u.reg r := fun r hr ↦ by
      rw [e3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.1, hr.2.1]
    fstep
    refine wp_load (novel_idx (by rsimp; rw [g .rbp (by decide), ubp])
      (by rsimp; rw [g .r12 (by decide), u12])) (by rsimp; rw [e2]; exact hbi) ?_
    refine wp_load (x := wd (wd C (2 * i)) 1)
      (by rw [eval_at]; rsimp; rw [g .rsi (by decide), usi]; rfl)
      (by rsimp; rw [e2, um]; exact c1) ?_
    refine Field.WP.then (novelKmul _) fun u₂ ⟨f1, f2, f3⟩ ↦ ?_
    rsimp at f1 f2
    have g₂ : ∀ r ∉ Field.kRegs, r ≠ .r9 → u₂.reg r = u.reg r := fun r hr h9 ↦ by
      rw [f3 r hr]
      have hr' := hr
      simp only [Field.kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [QState.setReg_reg, hr'.1, hr'.2.1, h9, ↓reduceIte]
      exact g r hr
    have g₉ : u₂.reg .r9 = u₁.reg .r9 ^^^ u₁.reg .rax := by rw [f3 .r9 (by decide)]; rsimp
    fstep; fstep; fstep
    fdone
    have hz' := hz i hlt
    refine ⟨⟨i + 1, hlt, ?_, ?_, ?_, ?_, f2.trans (e2.trans um), ?_, ?_⟩, ?_⟩
    · rw [g₂ .r12 (by decide) (by decide), u12, toUInt64_succ]
    · rw [g₂ .rsi (by decide) (by decide), usi, show 2 * (i + 1) = 2 * i + 2 by omega,
        ← wd_add]
      rfl
    · rw [novelAcc_succ hlt, hz', g₉, e1, g .r9 (by decide), u9]
      rfl
    · rw [novelAcc_succ hlt, hz', g₂ .r10 (by decide) (by decide), f1, u10]
      rfl
    · rw [g₂ .rbp (by decide) (by decide), ubp]
    · rw [g₂ .r11 (by decide) (by decide), u11]
    · rw [g₂ .r12 (by decide) (by decide), u12, toUInt64_succ, toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro u ⟨i, hi, u12, _, u9, u10, um, _, u11⟩ hc
    have hge : zs.size ≤ i := by
      rw [cond_ltu, rhs_reg, u12, u11, decide_eq_false_iff_not,
        toUInt64_lt (by omega) (by omega)] at hc
      omega
    obtain rfl : i = zs.size := by omega
    have hs : novelAcc zs zs.size = sumE zs := by
      rw [novelAcc, List.take_of_length_le (by simp), Array.foldl_toList]
      rfl
    rw [hs] at u9 u10
    exact ⟨u9, u10, um⟩

/-! ## The kernel -/

/-- `(r9, r10) := novelEval cs what`: `cs` at `r13` (`r15` of them), `what` at `rsi` (`rdx` of
them), the basis buffer at `rbx`. -/
def novelEvalC : Stmt := blk [
  novelBasisC, I (.mov .rsi .r13),
  .ite (.cmp .ltu .r15 (.reg .r11)) (I (.mov .r11 .r15)) .skip,
  I (.movi .r9 0), I (.movi .r10 0), I (.movi .r12 0), novelSum]

/-- **`novelEvalC` computes `novelEval`.** -/
theorem novelEvalC_spec {s : QState} {F : QState → Prop} {cs : Array EW} {what : Array UInt64}
    {C Wp B : UInt64}
    (hC : EWArr s.mem C cs) (h13 : s.reg .r13 = C) (h15 : s.reg .r15 = cs.size.toUInt64)
    (hcs : cs.size ≤ 64)
    (hW : WordArr s.mem Wp what) (hsi : s.reg .rsi = Wp) (hdx : s.reg .rdx = what.size.toUInt64)
    (hws : what.size ≤ 64)
    (hbx : s.reg .rbx = B) (hB : ∀ k < novelBufWords, (s.mem (wd B k)).isSome)
    (hfB : Fits B novelBufWords)
    (hfC : Fits C (2 * cs.size)) (hfW : Fits Wp what.size)
    (hBC : Disj B novelBufWords C (2 * cs.size)) (hBW : Disj B novelBufWords Wp what.size) :
    WP novelEvalC s (fun s' ↦ s'.reg .r9 = (novelEval cs what).c0 ∧
      s'.reg .r10 = (novelEval cs what).c1 ∧
      ∀ a, (∀ k < novelBufWords, a ≠ wd B k) → s'.mem a = s.mem a) F := by
  unfold novelEvalC
  refine Field.WP.then (novelBasisC_spec (count := cs.size) hW hsi hdx hws hbx h15 hcs hB hfB hfW
    hBW) fun u ⟨ubp, u15, u13, u11, hsz, hb, hK⟩ ↦ ?_
  set bs := what.foldl (novelStep cs.size) #[1] with hbs
  set zs := Array.zipWith (fun p b ↦ EW.scale b p) cs (bs.extract 0 cs.size) with hzs
  have hzsz : zs.size = min bs.size cs.size := by
    rw [hzs, Array.size_zipWith, Array.size_extract]
    omega
  have hev : novelEval cs what = sumE zs := by
    rw [novelEval, novelBasis_eq]
  have hCu : EWArr u.mem C cs := fun i hi ↦ by
    have hne : ∀ l < 2 * cs.size, u.mem (wd C l) = s.mem (wd C l) := fun l hl ↦
      hK _ fun k hk ↦ (wd_ne_of_disj hfB hfC hBC hk hl).symm
    obtain ⟨c0, c1⟩ := hC i hi
    refine ⟨by rw [hne _ (by omega)]; exact c0, ?_⟩
    rw [wd_wd, hne _ (by omega)]
    rw [wd_wd] at c1
    exact c1
  have hmin : ∀ t : QState, t.reg .rbp = B → t.reg .rsi = C → t.reg .r11 = zs.size.toUInt64 →
      t.mem = u.mem →
      WP (blk [I (.movi .r9 0), I (.movi .r10 0), I (.movi .r12 0), novelSum]) t
        (fun s' ↦ s'.reg .r9 = (novelEval cs what).c0 ∧ s'.reg .r10 = (novelEval cs what).c1 ∧
          ∀ a, (∀ k < novelBufWords, a ≠ wd B k) → s'.mem a = s.mem a) F := by
    intro t tbp tsi t11 tm
    fstep; fstep; fstep
    refine Field.WP.then (novelSum_spec (B := B) (C := C) (bs := bs) (cs := cs) (zs := zs)
      (by omega)
      (by omega) (fun i h ↦ ?_) (by rsimp; exact tbp) (by rsimp; exact tsi)
      (by rsimp; exact t11) (by rsimp) (by rsimp) (by rsimp)
      (fun k hk ↦ by rsimp; rw [tm]; exact hb k (by omega)) (by rsimp; rw [tm]; exact hCu))
      fun v ⟨v9, v10, vm⟩ ↦ ?_
    · simp only [hzs, Array.getElem_zipWith, Array.getElem_extract, Nat.zero_add]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      rfl
    · fdone
      rw [hev]
      refine ⟨v9, v10, fun a ha ↦ ?_⟩
      rw [vm]
      rsimp
      rw [tm]
      exact hK a ha
  fstep
  apply WP.blk_cons
  by_cases hlt : cs.size < bs.size
  · have hc : (Cond.cmp .ltu .r15 (.reg .r11)).eval (u.setReg .rsi (u.reg .r13)) = true := by
      rw [cond_ltu, rhs_reg]
      rsimp
      rw [u15, u11, decide_eq_true_eq, toUInt64_lt (by omega) (by omega)]
      exact hlt
    refine wp_ite_true hc (WP.ins' ?_)
    simp only [QInstr.step]
    refine hmin _ ?_ ?_ ?_ rfl <;> rsimp
    · exact ubp
    · rw [u13, h13]
    · rw [u15, hzsz, Nat.min_eq_right hlt.le]
  · have hc : (Cond.cmp .ltu .r15 (.reg .r11)).eval (u.setReg .rsi (u.reg .r13)) = false := by
      rw [cond_ltu, rhs_reg]
      rsimp
      rw [u15, u11, decide_eq_false_iff_not, toUInt64_lt (by omega) (by omega)]
      exact hlt
    exact wp_ite_false hc (WP.skip (hmin _ (by rsimp; exact ubp) (by rsimp; rw [u13, h13])
      (by rsimp; rw [u11, hzsz, Nat.min_eq_left (by omega)]) rfl))

end NativeVm.Code.P7
