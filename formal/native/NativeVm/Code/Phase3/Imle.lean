module

public import NativeVm.Code.Phase3.Copy

/-!
# Phase 3's slots and `indexMle`

Phase 3's own elements sit in `valsR`, slot `i` at word `sl i` (`sl 0` holds `1`, `sl 1` `g`, ...,
`NativeVm.Code.Phase3.Main` lists them). `imleCode dst`: `indexMle` of the first `r15` coordinates
of the point at `r13`, into word `dst`, through the slots `8 .. 11` (`imle_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field LeanVM.Parameters

/-- Slot `i`'s word. -/
def sl (i : Nat) : Nat := 52880 + 2 * i

theorem valsR_off : valsR.off = 52880 := by decide

/-- The loop's body: coordinate `r` into slot `8`, then `acc · (1 + r·(1 + gp))`, `gp²`. -/
def imleOps : List EOp :=
  [.add (sl 0) (sl 9) (sl 11), .mul (sl 8) (sl 11) (sl 11), .add (sl 0) (sl 11) (sl 11),
    .mul (sl 10) (sl 11) (sl 10), .mul (sl 9) (sl 9) (sl 9)]

/-- `indexMle` of the `r15` coordinates at `r13`, into word `dst`. -/
def imleCode (dst : Nat) : Stmt := blk [
  opSet (sl 10) 1, opSet (sl 9) gen,
  .loop (.test false .r15 (.reg .r15)) (blk ([I (.load .r9 (at_ .r13 0)), I (.load .r10 (at_ .r13 8))] ++
    stA (sl 8) ++ [opsCode imleOps, I (.addi .r13 16), I (.subi .r15 1)])),
  opCopy (sl 10) dst]

/-- The words `imleCode dst` writes: slots `8 .. 11` and `dst`. -/
def imleW (dst k : Nat) : Prop := (sl 8 ≤ k ∧ k < sl 12) ∨ k = dst ∨ k = dst + 1

/-- The fold `indexMle` runs. -/
def imleStep (acc : EW × EW) (r : EW) : EW × EW := (acc.1 * (1 + r * (1 + acc.2)), acc.2 * acc.2)

theorem indexMle_eq (pt : Array EW) : indexMle pt = (pt.foldl imleStep (1, gen)).1 := rfl

variable {s : QState} {E : QState → Prop} {w : UInt64}

theorem imleOps_run (v : Nat → EW) :
    opsRun imleOps v (sl 10) = v (sl 10) * (v (sl 0) + v (sl 8) * (v (sl 0) + v (sl 9))) ∧
    opsRun imleOps v (sl 9) = v (sl 9) * v (sl 9) := by
  simp [opsRun, imleOps, EOp.eval, EOp.dst, sl]

/-- Outside slots `8 .. 11`. -/
def NotW8 (w a' : UInt64) : Prop := ∀ k, sl 8 ≤ k → k < sl 12 → a' ≠ wd w k

theorem notW8_wd {k : Nat} (hk : k < 2 ^ 60) (h : k < sl 8 ∨ sl 12 ≤ k) : NotW8 w (wd w k) :=
  fun k' h1 h2 e ↦ by
    unfold sl at *
    rw [wd_inj (by omega) (by omega)] at e
    omega

/-- A memory changed only at slots `8 .. 11`. -/
def KeepW8 (w : UInt64) (m m' : UInt64 → Option UInt64) : Prop := ∀ a', NotW8 w a' → m' a' = m a'

theorem ewat_keepW8 {m m' : UInt64 → Option UInt64} {k : Nat} {x : EW} (h : KeepW8 w m m')
    (hk : k + 1 < 2 ^ 60) (hk' : k + 1 < sl 8 ∨ sl 12 ≤ k) (hx : EWAt m (wd w k) x) :
    EWAt m' (wd w k) x := by
  refine ⟨(h _ (notW8_wd (by omega) (by omega))).trans hx.1, ?_⟩
  rw [wd_wd, h _ (notW8_wd (by omega) (by omega)), ← wd_wd]
  exact hx.2

/-- One pass: coordinate `j` folded in. -/
theorem imle_body {pt : Array EW} {a n j : Nat} {acc : EW × EW} (hj : j < n) (hn : n ≤ pt.size)
    (h14 : s.reg .r14 = w) (h13 : s.reg .r13 = wd w (a + 2 * j))
    (hx : EWAt s.mem (wd w (a + 2 * j)) pt[j])
    (hone : EWAt s.mem (wd w (sl 0)) 1) (hacc : EWAt s.mem (wd w (sl 10)) acc.1)
    (hgp : EWAt s.mem (wd w (sl 9)) acc.2)
    (hdom : ∀ k, sl 8 ≤ k → k < sl 12 → (s.mem (wd w k)).isSome) :
    WP (blk ([I (.load .r9 (at_ .r13 0)), I (.load .r10 (at_ .r13 8))] ++
      stA (sl 8) ++ [opsCode imleOps, I (.addi .r13 16), I (.subi .r15 1)])) s
      (fun s' ↦ EWAt s'.mem (wd w (sl 10)) (imleStep acc pt[j]).1 ∧
        EWAt s'.mem (wd w (sl 9)) (imleStep acc pt[j]).2 ∧ KeepW8 w s.mem s'.mem ∧
        (∀ a', (s'.mem a').isSome = (s.mem a').isSome) ∧
        s'.reg .r13 = s.reg .r13 + 16 ∧ s'.reg .r15 = s.reg .r15 - 1 ∧
        RegsFrame (opRegs ++ [.r13, .r15]) s s') E := by
  have hd8 := hdom (sl 8) le_rfl (by unfold sl; omega)
  have hd9 := hdom (sl 8 + 1) (by omega) (by unfold sl; omega)
  refine wp_load (by rw [Transcript.eval_at, h13, Field.int64Zero_toUInt64, UInt64.add_zero]) hx.1 ?_
  refine wp_load (by rw [Transcript.eval_at]; rsimp; rw [h13]; rfl) hx.2 ?_
  show WP (blk (stA (sl 8) ++ [opsCode imleOps, I (.addi .r13 16), I (.subi .r15 1)])) _ _ _
  refine stA_spec (by rsimp; exact h14) (by unfold sl; omega) (by rsimp; exact hd8) (by rsimp; exact hd9) ?_
  rsimp
  set m1 := updE s.mem w (sl 8) ⟨pt[j].c0, pt[j].c1⟩ with hm1
  let v : Nat → EW := fun k ↦
    if k = sl 8 then pt[j] else if k = sl 9 then acc.2 else if k = sl 10 then acc.1 else 1
  have hS : Holds m1 w [sl 0, sl 8, sl 9, sl 10] v := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · simp only [v, sl]; simp only [show (52880 + 2 * 0 = 52880 + 2 * 8) = False by decide,
        show (52880 + 2 * 0 = 52880 + 2 * 9) = False by decide,
        show (52880 + 2 * 0 = 52880 + 2 * 10) = False by decide, ↓reduceIte]
      exact updE_ewat_ne (by unfold sl; omega) (by omega) (by unfold sl; omega) hone
    · simp only [v, ↓reduceIte]
      exact updE_ewat (by unfold sl; omega)
    · simp only [v, show (sl 9 = sl 8) = False by decide, ↓reduceIte]
      exact updE_ewat_ne (by unfold sl; omega) (by unfold sl; omega) (by unfold sl; omega) hgp
    · simp only [v, show (sl 10 = sl 8) = False by decide, show (sl 10 = sl 9) = False by decide,
        ↓reduceIte]
      exact updE_ewat_ne (by unfold sl; omega) (by unfold sl; omega) (by unfold sl; omega) hacc
  have hiso1 : ∀ a', (m1 a').isSome = (s.mem a').isSome := updE_isSome hd8 hd9
  refine WP.blk_cons (WP.mono (ops_spec imleOps (lim := 2 ^ 60) (s := ⟨_, m1⟩) (by norm_num)
    (by rsimp; exact h14) hS (by simp [sl]) (by decide) (by simp [imleOps, opsDsts, EOp.dst, sl])
    (fun d hd ↦ ?_)) ?_ fun _ h ↦ h)
  · simp only [imleOps, opsDsts, EOp.dst, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hd
    rw [hiso1, hiso1]
    constructor <;> refine hdom _ ?_ ?_ <;> rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      simp [sl]
  rintro s2 ⟨hH, hk, hsome, hout, hrf⟩
  refine wp_reg rfl (wp_reg rfl (WP.blk_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
  · have := hH (sl 10) (by simp [imleOps, opsDsts, EOp.dst])
    rw [(imleOps_run v).1] at this
    simp only [QState.setReg_mem]
    convert this using 2
    simp [v, imleStep, sl]
  · have := hH (sl 9) (by simp [imleOps, opsDsts, EOp.dst])
    rw [(imleOps_run v).2] at this
    simp only [QState.setReg_mem]
    convert this using 2
    simp [v, imleStep, sl]
  · intro a' ha'
    simp only [QState.setReg_mem]
    have hm1a : m1 a' = s.mem a' := by
      rw [hm1]; unfold updE
      rw [Function.update_of_ne (ha' _ (by unfold sl; omega) (by unfold sl; omega)),
        Function.update_of_ne (ha' _ le_rfl (by unfold sl; omega))]
    by_cases hw : ∃ k < 2 ^ 60, a' = wd w k
    · obtain ⟨k, hk', rfl⟩ := hw
      rw [hk k hk' fun d hd ↦ ?_]
      · exact hm1a
      · simp only [imleOps, opsDsts, EOp.dst, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hd
        constructor
        all_goals
          intro e
          subst e
          rcases hd with rfl | rfl | rfl | rfl | rfl <;> exact ha' _ (by simp [sl]) (by simp [sl]) rfl
    · rw [hout a' fun k hk' e ↦ hw ⟨k, hk', e⟩]
      exact hm1a
  · intro a'
    simp only [QState.setReg_mem]
    rw [hsome a']; exact hiso1 a'
  · rsimp; rw [hrf .r13 (by decide)]
    show ((s.setReg .r9 pt[j].c0).setReg .r10 pt[j].c1).reg .r13 + 16 = _; rsimp
  · rsimp; rw [hrf .r15 (by decide)]
    show ((s.setReg .r9 pt[j].c0).setReg .r10 pt[j].c1).reg .r15 - 1 = _; rsimp
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rsimp
    have h13r : r ≠ .r13 := fun e ↦ by simp [e] at hr
    have h15r : r ≠ .r15 := fun e ↦ by simp [e] at hr
    simp only [h13r, h15r, ↓reduceIte]
    rw [hrf r (fun m ↦ by simp_all)]
    rsimp
    have h9 : r ≠ .r9 := fun e ↦ by simp [e] at hr
    have h10 : r ≠ .r10 := fun e ↦ by simp [e] at hr
    simp [h9, h10]

theorem keepW8_updE {m : UInt64 → Option UInt64} {k : Nat} {x : EW} (hk : sl 8 ≤ k)
    (hk' : k + 1 < sl 12) : KeepW8 w m (updE m w k x) := fun a' ha' ↦ by
  unfold updE
  rw [Function.update_of_ne (ha' _ (by omega) hk'), Function.update_of_ne (ha' _ hk (by omega))]

theorem KeepW8.trans {m₁ m₂ m₃ : UInt64 → Option UInt64} (h₁ : KeepW8 w m₁ m₂)
    (h₂ : KeepW8 w m₂ m₃) : KeepW8 w m₁ m₃ := fun a h ↦ (h₂ a h).trans (h₁ a h)

/-- **`imleCode dst`**: `indexMle` of the first `n` coordinates of `pt` at word `a`, into `dst`;
slots `8 .. 11` and `dst` written. -/
theorem imle_spec {pt : Array EW} {a n dst : Nat} (hn : n ≤ pt.size) (h14 : s.reg .r14 = w)
    (h13 : s.reg .r13 = wd w a) (h15 : s.reg .r15 = n.toUInt64) (hx : EWArr s.mem (wd w a) pt)
    (hone : EWAt s.mem (wd w (sl 0)) 1) (hap : a + 2 * n ≤ sl 8 ∨ sl 12 ≤ a)
    (hlim : a + 2 * n < 2 ^ 60) (hdst : dst + 1 < 2 ^ 60)
    (hdom : ∀ k, sl 8 ≤ k → k < sl 12 → (s.mem (wd w k)).isSome)
    (hdd : (s.mem (wd w dst)).isSome ∧ (s.mem (wd w (dst + 1))).isSome) :
    WP (imleCode dst) s (fun s' ↦ EWAt s'.mem (wd w dst) (indexMle (pt.extract 0 n)) ∧
      (∀ a', NotW8 w a' → a' ≠ wd w dst → a' ≠ wd w (dst + 1) → s'.mem a' = s.mem a') ∧
      (∀ a', (s'.mem a').isSome = (s.mem a').isSome) ∧
      RegsFrame (opRegs ++ [.r13, .r15]) s s') E := by
  unfold imleCode
  have hs10 := hdom (sl 10) (by decide) (by decide)
  have hs10' := hdom (sl 10 + 1) (by decide) (by decide)
  have hs9 := hdom (sl 9) (by decide) (by decide)
  have hs9' := hdom (sl 9 + 1) (by decide) (by decide)
  refine WP.blk_cons (WP.mono (opSet_spec (d := sl 10) (x := 1) h14 (by decide) hs10 hs10') ?_
    fun _ h ↦ h)
  rintro s1 ⟨hm1, hf1⟩
  have hiso1 : ∀ a', (s1.mem a').isSome = (s.mem a').isSome := fun a' ↦ by
    rw [hm1]; exact updE_isSome hs10 hs10' a'
  refine WP.blk_cons (WP.mono (opSet_spec (d := sl 9) (x := gen) ((hf1 .r14 (by decide)).trans h14)
    (by decide) ((hiso1 _).trans hs9) ((hiso1 _).trans hs9')) ?_ fun _ h ↦ h)
  rintro s2 ⟨hm2, hf2⟩
  have hiso2 : ∀ a', (s2.mem a').isSome = (s.mem a').isSome := fun a' ↦ by
    rw [hm2, ← hiso1]; exact updE_isSome ((hiso1 _).trans hs9) ((hiso1 _).trans hs9') a'
  have k2 : KeepW8 w s.mem s2.mem := by
    rw [hm2, hm1]
    exact (keepW8_updE (k := sl 10) (by decide) (by decide)).trans
      (keepW8_updE (k := sl 9) (by decide) (by decide))
  have hf12 : RegsFrame (opRegs ++ [.r13, .r15]) s s2 :=
    Field.RegsFrame.trans (Field.RegsFrame.mono hf1 (by simp)) (Field.RegsFrame.mono hf2 (by simp))
  refine WP.blk_cons (WP.mono (P := fun t ↦ EWAt t.mem (wd w (sl 10)) (indexMle (pt.extract 0 n)) ∧
      t.reg .r14 = w ∧
      KeepW8 w s.mem t.mem ∧ (∀ a', (t.mem a').isSome = (s.mem a').isSome) ∧
      RegsFrame (opRegs ++ [.r13, .r15]) s t) ?_ ?_ fun _ h ↦ h)
  · refine WP.loop (fun t ↦ ∃ j ≤ n, t.reg .r13 = wd w (a + 2 * j) ∧
        t.reg .r15 = (n - j).toUInt64 ∧ t.reg .r14 = w ∧
        EWAt t.mem (wd w (sl 10)) ((pt.extract 0 j).foldl imleStep (1, gen)).1 ∧
        EWAt t.mem (wd w (sl 9)) ((pt.extract 0 j).foldl imleStep (1, gen)).2 ∧
        KeepW8 w s.mem t.mem ∧ (∀ a', (t.mem a').isSome = (s.mem a').isSome) ∧
        RegsFrame (opRegs ++ [.r13, .r15]) s t)
      (fun t ↦ (t.reg .r15).toNat) ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, k2, hiso2, hf12⟩ ?_ ?_
    · rw [(hf2 .r13 (by decide)).trans (hf1 .r13 (by decide))]; simpa using h13
    · rw [(hf2 .r15 (by decide)).trans (hf1 .r15 (by decide))]; simpa using h15
    · rw [(hf2 .r14 (by decide)).trans (hf1 .r14 (by decide))]; exact h14
    · rw [hm2]
      refine updE_ewat_ne (a := sl 9) (k := sl 10) (by decide) (by decide) (by decide) ?_
      rw [hm1, show pt.extract 0 0 = #[] by simp, Array.foldl_empty]
      exact updE_ewat (a := sl 10) (by decide)
    · rw [hm2, show pt.extract 0 0 = #[] by simp, Array.foldl_empty]
      exact updE_ewat (a := sl 9) (by decide)
    · rintro t ⟨j, hj, h13', h15', h14', hacc, hgp, hk, hsome, hf⟩ hc
      have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
      have hjn : j < n := by
        by_contra hh
        exact hne (by rw [h15', show n - j = 0 by omega]; rfl)
      have hxj : EWAt t.mem (wd w (a + 2 * j)) pt[j] := by
        have := hx j (by omega)
        rw [wd_wd] at this
        exact ewat_keepW8 hk (by omega) (by omega) this
      have hone' : EWAt t.mem (wd w (sl 0)) 1 := ewat_keepW8 hk (by decide) (by decide) hone
      refine WP.mono (imle_body (acc := (pt.extract 0 j).foldl imleStep (1, gen)) hjn hn h14' h13' hxj
        hone' hacc hgp (fun k h1 h2 ↦ (hsome _).trans (hdom k h1 h2))) ?_ fun _ h ↦ h
      rintro t' ⟨h10', h9', hk', hsome', h13'', h15'', hf'⟩
      have hfold : (pt.extract 0 (j + 1)).foldl imleStep (1, gen) =
          imleStep ((pt.extract 0 j).foldl imleStep (1, gen)) pt[j] := by
        rw [extract_succ' pt j (by omega), Array.foldl_push]
      refine ⟨⟨j + 1, by omega, ?_, ?_, ?_, by rw [hfold]; exact h10', by rw [hfold]; exact h9',
        hk.trans hk', fun a' ↦ (hsome' a').trans (hsome a'), Field.RegsFrame.trans hf hf'⟩, ?_⟩
      · rw [h13'', h13', show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]; congr 1
      · rw [h15'', h15', show n - j = n - (j + 1) + 1 by omega, Field.toUInt64_succ_sub]
      · rw [hf' .r14 (by decide)]; exact h14'
      · rw [h15'', h15', show n - j = n - (j + 1) + 1 by omega, Field.toUInt64_succ_sub,
          UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
    · rintro t ⟨j, hj, -, h15', h14', hacc, -, hk, hsome, hf⟩ hc
      have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
      have : j = n := by
        by_contra hh
        have := Field.toUInt64_eq_zero (show n - j < 2 ^ 64 by omega) (h15' ▸ h0)
        omega
      subst this
      exact ⟨hacc, h14', hk, hsome, hf⟩
  · rintro t ⟨hacc, h14t, hk, hsome, hf⟩
    refine WP.blk_cons (WP.mono (opCopy_spec h14t hacc (by omega) ((hsome _).trans hdd.1)
      ((hsome _).trans hdd.2)) ?_ fun _ h ↦ h)
    rintro t' ⟨hm, hf'⟩
    refine WP.blk_nil ⟨by rw [hm]; exact updE_ewat (by omega), fun a' ha' h1 h2 ↦ ?_,
      fun a' ↦ ?_, ?_⟩
    · rw [hm]; unfold updE
      rw [Function.update_of_ne h2, Function.update_of_ne h1]
      exact hk a' ha'
    · rw [hm, ← hsome]; exact updE_isSome ((hsome _).trans hdd.1) ((hsome _).trans hdd.2) a'
    · exact Field.RegsFrame.trans hf (Field.RegsFrame.mono hf' (by simp))

end NativeVm.Code.P3
