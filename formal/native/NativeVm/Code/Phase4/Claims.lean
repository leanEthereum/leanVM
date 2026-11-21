module

public import NativeVm.Code.Phase4.Step

/-!
# The tables' column claims

`claimsC_spec`: `claimsC` appends `tableColumnClaims ev` to the column claims at `claimsR`, from
each table's point and evaluations at `evalsR` (`EvalsAt`), table `t`'s evaluations
`widths[t]` long.

`pointCopy_spec` is the copy of a point's words, `claimOne_spec` one claim (`claimOneC`),
`claimTable_spec` a table's (`claimTableC`), `tablesLoop_spec` the six tables'. The model's claims
of the first `t` tables are `claimsPrefix ev t`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

/-- `claimOneC`'s copy of the point's words. -/
abbrev pointCopyC : Stmt := .loop (.test false .rcx (.reg .rcx)) (blk [
    I (.load .rax (wa .r8 0)), I (.store (wa .r9 0) .rax),
    I (.addi .r8 (wdisp 1)), I (.addi .r9 (wdisp 1)), I (.subi .rcx 1)])

/-- **The point's copy**: `N` words from `b` to `d`. -/
theorem pointCopy_spec {s : QState} {E : QState → Prop} {w : UInt64} {b d N : Nat}
    (h8 : s.reg .r8 = wd w b) (h9 : s.reg .r9 = wd w d)
    (hc : s.reg .rcx = N.toUInt64) (hsrc : ∀ q < N, (s.mem (wd w (b + q))).isSome)
    (hdst : ∀ q < N, (s.mem (wd w (d + q))).isSome) (hap : b + N ≤ d ∨ d + N ≤ b)
    (hl : b + N < 2 ^ 61) (hl' : d + N < 2 ^ 61) :
    WP pointCopyC s (fun s' ↦ (∀ q < N, s'.mem (wd w (d + q)) = s.mem (wd w (b + q))) ∧
      Wr w (fun k ↦ d ≤ k ∧ k < d + N) s s' ∧ DomEq s s' ∧
      RegsFrame [.rax, .rcx, .r8, .r9] s s') E := by
  refine WP.loop (fun t ↦ ∃ q ≤ N, t.reg .r8 = wd w (b + q) ∧ t.reg .r9 = wd w (d + q) ∧
      t.reg .rcx = (N - q).toUInt64 ∧ (∀ i < q, t.mem (wd w (d + i)) = s.mem (wd w (b + i))) ∧
      Wr w (fun k ↦ d ≤ k ∧ k < d + N) s t ∧ DomEq s t ∧ RegsFrame [.rax, .rcx, .r8, .r9] s t)
    (fun t ↦ (t.reg .rcx).toNat) ⟨0, Nat.zero_le _, by simpa using h8, by simpa using h9,
      by simpa using hc, fun _ h ↦ absurd h (Nat.not_lt_zero _), Wr.refl _ _ _, DomEq.refl _,
      RegsFrame.refl _ _⟩ ?_ ?_
  · rintro t ⟨q, hq, h8', h9', hc', hcp, hwr, hdom, hrf⟩ hcond
    have hqN : q < N := (test_count hc' (by omega)).mp hcond
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsrc q hqN)
    have hv' : t.mem (wd w (b + q + 0)) = some v := by
      rw [Nat.add_zero, hwr.word (by omega) (fun k hk ↦ ⟨by omega, by omega⟩)]; exact hv
    have hd' : (t.mem (wd w (d + q + 0))).isSome := by
      rw [Nat.add_zero, hdom]; exact hdst q hqN
    refine wp_ldA h8' hv' ?_
    refine wp_stA (by rsimp; exact h9') (by rw [QState.setReg_mem]; exact hd') ?_
    refine wp_addiA (by rsimp; exact h8') ?_
    refine wp_addiA (by rsimp; exact h9') ?_
    fstep
    fdone
    have hrc : t.reg .rcx - 1 = (N - (q + 1)).toUInt64 := by
      rw [hc', show N - q = (N - (q + 1)) + 1 by omega, toUInt64_succ_sub]
    refine ⟨⟨q + 1, by omega, rfl, rfl, hrc, fun i hi ↦ ?_,
      Wr.setReg (Wr.setReg (Wr.setReg (Wr.setMem (Wr.setReg hwr _ _) ⟨by omega, by omega⟩ _) _ _)
        _ _) _ _, hdom.trans (DomEq.setMem (s := t.setReg .rax v) hd' v), ?_⟩, ?_⟩
    · rcases Nat.lt_or_ge i q with h | h
      · rw [mem_setMem_ne _ (by omega) (by omega) (by omega), QState.setReg_mem]
        exact hcp i h
      · obtain rfl : i = q := by omega
        rw [mem_setMem_eq _ (by omega), hv]
    · refine RegsFrame.trans hrf ?_
      rfw
    · rw [hrc, hc', Transcript.toNat_toUInt64 (by omega),
      Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨q, hq, -, -, hc', hcp, hwr, hdom, hrf⟩ hcond
    have h1 : ¬ q < N := fun h ↦ by
      rw [(test_count hc' (by omega)).mpr h] at hcond
      exact absurd hcond (by decide)
    obtain rfl : q = N := by omega
    exact ⟨hcp, hwr, hdom, hrf⟩


/-- The words of an array of elements exist. -/
theorem EWArr.word_isSome {mem : UInt64 → Option UInt64} {w : UInt64} {b : Nat} {xs : Array EW}
    (h : EWArr mem (wd w b) xs) : ∀ q < 2 * xs.size, (mem (wd w (b + q))).isSome := by
  intro q hq
  have := h (q / 2) (by omega)
  rw [EWAt, wd_wd, wd_wd] at this
  rcases Nat.mod_two_eq_zero_or_one q with h2 | h2
  · rw [show b + q = b + 2 * (q / 2) by omega, this.1]; rfl
  · rw [show b + q = b + 2 * (q / 2) + 1 by omega, this.2]; rfl

/-- An array of elements, copied word by word. -/
theorem EWArr.ofCopy {mem mem' : UInt64 → Option UInt64} {w : UInt64} {b d : Nat} {xs : Array EW}
    (h : EWArr mem (wd w b) xs) (hc : ∀ q < 2 * xs.size, mem' (wd w (d + q)) = mem (wd w (b + q))) :
    EWArr mem' (wd w d) xs := by
  intro i hi
  have := h i hi
  rw [EWAt, wd_wd, wd_wd] at this ⊢
  rw [hc _ (by omega), show d + 2 * i + 1 = d + (2 * i + 1) by omega, hc _ (by omega),
    ← Nat.add_assoc]
  exact this

/-- **One claim** (`claimOneC`): the column `r13`, the point at `r14`, the value at `r10`, to `r12`. -/
theorem claimOne_spec {s : QState} {E : QState → Prop} {w : UInt64} {a e v col K c : Nat}
    {pt : Array EW} {x : EW}
    (h12 : s.reg .r12 = wd w a) (h13 : s.reg .r13 = col.toUInt64) (h14 : s.reg .r14 = wd w e)
    (h10 : s.reg .r10 = wd w v) (h11 : s.reg .r11 = (K - c).toUInt64) (hc : c < K)
    (hcol : col < 2 ^ 64) (hpt : EVec s.mem (wd w e) tablePointCap pt) (hx : EWAt s.mem (wd w v) x)
    (hdst : ∀ k < 76, (s.mem (wd w (a + k))).isSome) (he : e + 61 ≤ a) (hv : v + 2 ≤ a)
    (ha : a + 76 < 2 ^ 61) :
    WP claimOneC s (fun s' ↦ ColumnClaimAt s'.mem (wd w a) ⟨col, pt, x⟩ ∧
      Wr w (fun k ↦ a ≤ k ∧ k < a + 76) s s' ∧ DomEq s s' ∧ s'.reg .r10 = wd w (v + 2) ∧
      s'.reg .r11 = (K - (c + 1)).toUInt64 ∧ s'.reg .r12 = wd w (a + 76) ∧
      s'.reg .r13 = (col + 1).toUInt64 ∧
      RegsFrame [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13] s s') E := by
  obtain ⟨hsz, ⟨hszl, hcnt⟩, harr⟩ := hpt
  obtain ⟨hx0, hx1⟩ := hx
  rw [wd_wd] at harr hx1
  unfold tablePointCap at hsz
  unfold claimOneC
  simp only [cV, cW]
  refine wp_stA h12 (hdst 0 (by omega)) ?_
  refine wp_ldA (k := 0) h14 (by rw [mem_setMem_ne _ (by omega) (by omega) (by omega)]; exact hcnt) ?_
  refine wp_stA (k := 1) (by rsimp; exact h12) (by rsimp; rw [mem_setMem_ne _ (by omega) (by omega) (by omega)]; exact hdst 1 (by omega)) ?_
  refine wp_leaA (k := 1) (by rsimp; exact h14) ?_
  refine wp_leaA (k := 2) (by rsimp; exact h12) ?_
  fstep
  have hsh : pt.size.toUInt64 <<< (1 : UInt64) = (2 * pt.size).toUInt64 :=
    toUInt64_shl _ 1 (by omega)
  refine WP.then (pointCopy_spec (w := w) (b := e + 1) (d := a + 2) (N := 2 * pt.size) (by rsimp)
    (by rsimp) (by rsimp; exact hsh) (fun q hq ↦ ?_) (fun q hq ↦ ?_) (by omega) (by omega)
    (by omega)) fun s1 hs1 ↦ ?_
  · simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]
    exact EWArr.word_isSome harr q hq
  · rsimp
    refine isSome_setMem _ _ _ (isSome_setMem _ _ _ ?_)
    rw [Nat.add_assoc]
    exact hdst _ (by omega)
  obtain ⟨hcp, hwr1, hdom1, hrf1⟩ := hs1
  have hk : ∀ j, j < a → s1.mem (wd w j) = s.mem (wd w j) := fun j hj ↦ by
    rw [hwr1.word (by omega) (fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩)]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]
  have hm0 : s1.mem (wd w a) = some col.toUInt64 := by
    rw [hwr1.word (by omega) (fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩)]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne, mem_setMem_eq, h13]
  have hm1 : s1.mem (wd w (a + 1)) = some pt.size.toUInt64 := by
    rw [hwr1.word (by omega) (fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩)]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_eq]
  have hsome : ∀ k < 76, (s1.mem (wd w (a + k))).isSome := fun k hk ↦ by
    rw [hdom1]
    simp only [QState.setReg_mem]
    exact isSome_setMem _ _ _ (isSome_setMem _ _ _ (hdst k hk))
  have hW1 : Wr w (fun k ↦ a ≤ k ∧ k < a + 76) s s1 :=
    Wr.trans (by wr_tac) (hwr1.mono fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩)
  have hD1 : DomEq s s1 := fun b ↦ by
    rw [hdom1]
    simp only [QState.setReg_mem, QState.setMem_mem]
    split_ifs with h1 h2
    · rw [h1, hdst 1 (by omega)]; rfl
    · rw [h2, hdst 0 (by omega)]; rfl
    · rfl
  have hR1 : RegsFrame [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13] s s1 := fun r hr ↦ by
    rw [hrf1 r (fun h ↦ hr (by simp only [List.mem_cons] at h ⊢; tauto))]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rsimp
    simp only [hr, ite_false]
  have r10' : s1.reg .r10 = wd w v := by rw [hrf1 .r10 (by decide)]; rsimp; exact h10
  have r11' : s1.reg .r11 = (K - c).toUInt64 := by rw [hrf1 .r11 (by decide)]; rsimp; exact h11
  have r12' : s1.reg .r12 = wd w a := by rw [hrf1 .r12 (by decide)]; rsimp; exact h12
  have r13' : s1.reg .r13 = col.toUInt64 := by rw [hrf1 .r13 (by decide)]; rsimp; exact h13
  have hpt1 : EWArr s1.mem (wd w (a + 2)) pt := EWArr.ofCopy harr fun q hq ↦ by
    rw [hcp q hq]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]
  clear hcp hwr1 hdom1 hrf1
  refine wp_ldA (k := 0) r10' (by rw [Nat.add_zero, hk v (by omega)]; exact hx0) ?_
  refine wp_stA (k := 74) (by rsimp; exact r12') (by rsimp; exact hsome 74 (by omega)) ?_
  refine wp_ldA (k := 1) (by rsimp; exact r10') (by
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]
    rw [hk _ (by omega)]; exact hx1) ?_
  refine wp_stA (k := 74 + 1) (by rsimp; exact r12') (by
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]; exact hsome 75 (by omega)) ?_
  refine wp_addiA (k := 2) (by rsimp; exact r10') ?_
  refine wp_addiA (k := 76) (by rsimp; exact r12') ?_
  fstep
  fstep
  fdone
  refine ⟨⟨⟨hcol, ?_⟩, ⟨show pt.size ≤ pointCap by rw [pointCap_val]; omega, ⟨hszl, ?_⟩, ?_⟩, ?_⟩, Wr.trans hW1 (by wr_tac),
    hD1.trans fun b ↦ ?_, trivial, ?_, trivial, ?_, RegsFrame.trans hR1 (by rfw)⟩
  · simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]
    exact hm0
  · rw [wd_wd]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]
    exact hm1
  · rw [wd_wd, wd_wd]
    refine EWArr.ofCopy (xs := pt) (b := a + 2) hpt1 fun q (hq : q < 2 * pt.size) ↦ ?_
    rw [show a + 1 + 1 + q = a + 2 + q by omega]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne]
  · rw [show 1 + vecWords pointCap = 74 from cV_val, wd_wd]
    refine ⟨?_, ?_⟩
    · simp (disch := omega) only [QState.setReg_mem, mem_setMem_ne, mem_setMem_eq]
    · rw [wd_wd]
      simp (disch := omega) only [mem_setMem_eq]
  · simp only [QState.setReg_mem, QState.setMem_mem]
    split_ifs with h1 h2
    · rw [h1, show a + (74 + 1) = a + 75 from rfl, hsome 75 (by omega)]; rfl
    · rw [h2, hsome 74 (by omega)]; rfl
    · rfl
  · rw [r11', show K - c = (K - (c + 1)) + 1 by omega, toUInt64_succ_sub]
  · rw [r13', toUInt64_succ]

/-- The claims `D` from word `L` on, claim `j` at `L + 76 j`. -/
def NewClaimsAt (mem : UInt64 → Option UInt64) (w : UInt64) (L : Nat) (D : Array ColumnClaimW) : Prop :=
  ∀ j (h : j < D.size), ColumnClaimAt mem (wd w (L + 76 * j)) D[j]

theorem NewClaimsAt.push {mem : UInt64 → Option UInt64} {w : UInt64} {L : Nat} {D : Array ColumnClaimW}
    {x : ColumnClaimW} (h : NewClaimsAt mem w L D) (hx : ColumnClaimAt mem (wd w (L + 76 * D.size)) x) :
    NewClaimsAt mem w L (D.push x) := by
  intro j hj
  rw [Array.size_push] at hj
  rcases Nat.lt_or_ge j D.size with h' | h'
  · rw [Array.getElem_push_lt h']; exact h j h'
  · obtain rfl : j = D.size := by omega
    rw [Array.getElem_push_eq]; exact hx

theorem NewClaimsAt.congr {mem mem' : UInt64 → Option UInt64} {w : UInt64} {L : Nat}
    {D : Array ColumnClaimW} (h : NewClaimsAt mem w L D)
    (hm : ∀ k, L ≤ k → k < L + 76 * D.size → mem' (wd w k) = mem (wd w k)) : NewClaimsAt mem' w L D :=
  fun j hj ↦ (h j hj).congr fun k hk ↦ by
    have hc : claimWords = 76 := by decide
    rw [hc] at hk
    rw [wd_wd]
    exact hm _ (by omega) (by omega)

/-- A table's claims: its evaluations `vals` on the columns from `base`, at its point `pt`. -/
abbrev tableClaimsOf (base : Nat) (pt vals : Array EW) : Array ColumnClaimW :=
  vals.zipIdx.map fun (value, column) ↦ ⟨base + column, pt, value⟩

theorem tableClaimsOf_getElem {base : Nat} {pt vals : Array EW} {c : Nat} (h : c < (tableClaimsOf base pt vals).size) :
    (tableClaimsOf base pt vals)[c] = ⟨base + c, pt, vals[c]'(by simpa using h)⟩ := by
  simp [Array.getElem_zipIdx]

theorem tableClaimsOf_size (base : Nat) (pt vals : Array EW) : (tableClaimsOf base pt vals).size = vals.size := by
  simp

/-- **One table's claims** (`claimTableC`), its entry of `evalsR` at `r14`. -/
theorem claimTable_spec {s : QState} {E : QState → Prop} {w : UInt64} {e L M T base : Nat}
    {D : Array ColumnClaimW} {pt vals : Array EW}
    (h14 : s.reg .r14 = wd w e) (h15 : s.reg .r15 = (6 - T).toUInt64) (hT : T < 6)
    (h12 : s.reg .r12 = wd w (L + 76 * M)) (h13 : s.reg .r13 = base.toUInt64) (hbase : base < 2 ^ 60)
    (hpt : EVec s.mem (wd w e) tablePointCap pt) (hvals : EVec s.mem (wd w (e + 61)) widthCap vals)
    (hD : NewClaimsAt s.mem w L D) (hM : D.size = M)
    (hdst : ∀ k, L + 76 * M ≤ k → k < L + 76 * (M + vals.size) → (s.mem (wd w k)).isSome)
    (he : e + 246 ≤ L) (hl : L + 76 * (M + vals.size) < 2 ^ 61) :
    WP claimTableC s (fun s' ↦ NewClaimsAt s'.mem w L (D ++ tableClaimsOf base pt vals) ∧
      Wr w (fun k ↦ L + 76 * M ≤ k ∧ k < L + 76 * (M + vals.size)) s s' ∧ DomEq s s' ∧
      s'.reg .r12 = wd w (L + 76 * (M + vals.size)) ∧ s'.reg .r13 = (base + vals.size).toUInt64 ∧
      s'.reg .r14 = wd w (e + 246) ∧ s'.reg .r15 = (6 - (T + 1)).toUInt64 ∧
      RegsFrame [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s') E := by
  obtain ⟨hvsz, ⟨-, hvcnt⟩, hvarr⟩ := hvals
  unfold widthCap at hvsz
  rw [wd_wd] at hvarr
  unfold claimTableC
  simp only [evOff, eS]
  refine wp_ldA (k := 61) h14 hvcnt ?_
  refine wp_leaA (k := 61 + 1) (by rsimp; exact h14) ?_
  have hkeep : ∀ t : QState, Wr w (fun k ↦ L + 76 * M ≤ k ∧ k < L + 76 * (M + vals.size)) s t →
      ∀ j, j < L → t.mem (wd w j) = s.mem (wd w j) := fun t hW j hj ↦
    hW.word (by omega) fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩
  apply WP.blk_cons
  refine WP.loop (fun t ↦ ∃ c ≤ vals.size, t.reg .r10 = wd w (e + 62 + 2 * c) ∧
      t.reg .r11 = (vals.size - c).toUInt64 ∧ t.reg .r12 = wd w (L + 76 * (M + c)) ∧
      t.reg .r13 = (base + c).toUInt64 ∧
      NewClaimsAt t.mem w L (D ++ (tableClaimsOf base pt vals).extract 0 c) ∧
      Wr w (fun k ↦ L + 76 * M ≤ k ∧ k < L + 76 * (M + vals.size)) s t ∧ DomEq s t ∧
      RegsFrame [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13] s t)
    (fun t ↦ (t.reg .r11).toNat) ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, by wr_tac, fun _ ↦ rfl,
      by rfw⟩ ?_ ?_
  · rsimp
  · rsimp; rw [Nat.sub_zero]
  · rsimp; rw [h12, Nat.add_zero]
  · rsimp; rw [h13, Nat.add_zero]
  · simp only [Array.extract_zero, Array.append_empty]; exact hD
  · rintro t ⟨c, hc, h10', h11', h12', h13', hN, hW, hDm, hR⟩ hcond
    have hcs : c < vals.size := (test_count h11' (by omega)).mp hcond
    have hpt' : EVec t.mem (wd w e) tablePointCap pt := hpt.congr fun k hk ↦ by
      rw [wd_wd]
      exact hkeep t hW _ (by unfold vecWords tablePointCap at hk; omega)
    have hx : EWAt t.mem (wd w (e + 62 + 2 * c)) vals[c] := by
      have := hvarr c hcs
      rw [EWAt, wd_wd, wd_wd] at this
      rw [EWAt, wd_wd]
      rw [hkeep t hW _ (by omega), hkeep t hW _ (by omega),
        show e + 62 + 2 * c = e + (61 + 1) + 2 * c by omega]
      exact this
    refine WP.mono (claimOne_spec (a := L + 76 * (M + c)) (col := base + c) (K := vals.size)
      h12' h13' (by rw [hR .r14 (by decide)]; exact h14) h10' h11' hcs (by omega) hpt' hx
      (fun k hk ↦ by rw [hDm]; exact hdst _ (by omega) (by omega)) (by omega) (by omega)
      (by omega)) ?_ (fun _ h ↦ h)
    rintro t' ⟨hcl, hW', hD', r10'', r11'', r12'', r13'', hR'⟩
    have hsz : (D ++ (tableClaimsOf base pt vals).extract 0 c).size = M + c := by
      simp only [Array.size_append, Array.size_extract, tableClaimsOf_size, hM]
      omega
    refine ⟨⟨c + 1, hcs, r10''.trans (congrArg (wd w) (by omega)), r11'', r12''.trans (congrArg (wd w) (by omega)),
      by rw [r13'', Nat.add_assoc], ?_,
      hW.trans (hW'.mono fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩), hDm.trans hD',
      RegsFrame.trans hR hR'⟩, ?_⟩
    · rw [Array.extract_succ_right (by omega) (by rw [tableClaimsOf_size]; exact hcs), Array.append_push]
      refine NewClaimsAt.push (hN.congr fun k hk1 hk2 ↦ ?_) ?_
      · rw [hsz] at hk2
        exact hW'.word (by omega) fun k' ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩
      · rw [hsz, tableClaimsOf_getElem]
        exact hcl
    · rw [r11'', h11', Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨c, hc, h10', h11', h12', h13', hN, hW, hDm, hR⟩ hcond
    have h1 : ¬ c < vals.size := fun h ↦ by
      rw [(test_count h11' (by omega)).mpr h] at hcond
      exact absurd hcond (by decide)
    obtain rfl : c = vals.size := by omega
    rw [Array.extract_eq_self_of_le (by rw [tableClaimsOf_size])] at hN
    refine wp_addiA (k := 246) (by rw [hR .r14 (by decide)]; exact h14) ?_
    fstep
    fdone
    refine ⟨hN, Wr.setReg (Wr.setReg hW _ _) _ _, hDm, h12', h13', trivial, ?_,
      RegsFrame.trans (RegsFrame.mono hR (by decide)) (by rfw)⟩
    rw [hR .r15 (by decide), h15, show 6 - T = (6 - (T + 1)) + 1 by omega, toUInt64_succ_sub]


/-- The first `t` tables' column claims. -/
def claimsPrefix (ev : Array (Array EW × Array EW)) (t : Nat) : Array ColumnClaimW :=
  ((globalColumnBasesW.zip ev).extract 0 t).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩

theorem globalColumnBasesW_eq : globalColumnBasesW = #[5, 18, 31, 38, 52, 66] := by decide

theorem claimsPrefix_six {ev : Array (Array EW × Array EW)} (hev : ev.size = 6) :
    claimsPrefix ev 6 = tableColumnClaims ev := by
  rw [claimsPrefix, Array.extract_eq_self_of_le (by rw [Array.size_zip, hev, globalColumnBasesW_eq]; decide)]
  rfl

theorem claimsPrefix_zero (ev : Array (Array EW × Array EW)) : claimsPrefix ev 0 = #[] := by
  simp [claimsPrefix]

theorem claimsPrefix_succ {ev : Array (Array EW × Array EW)} (hev : ev.size = 6) {t : Nat} (ht : t < 6) :
    claimsPrefix ev (t + 1) = claimsPrefix ev t ++ tableClaimsOf (globalColumnBasesW[t]'(by rw [globalColumnBasesW_eq]; exact ht))
      (ev.getD t (#[], #[])).1 (ev.getD t (#[], #[])).2 := by
  rw [claimsPrefix, Array.extract_succ_right (by omega) (by rw [Array.size_zip, hev, globalColumnBasesW_eq]; exact ht),
    Array.flatMap_push, Array.getElem_zip]
  simp [claimsPrefix, Array.getD_eq_getD_getElem?, hev, ht]

theorem claimsPrefix_size {ev : Array (Array EW × Array EW)} (hev : ev.size = 6)
    (hwid : ∀ t < 6, (ev.getD t (#[], #[])).2.size = widths.getD t 0) :
    ∀ t ≤ 6, (claimsPrefix ev t).size = (widths.take t).sum := by
  intro t ht
  induction t with
  | zero => simp [claimsPrefix_zero]
  | succ t ih =>
    rw [claimsPrefix_succ hev (by omega), Array.size_append, ih (by omega), tableClaimsOf_size, hwid t (by omega)]
    have : ∀ t < 6, (widths.take (t + 1)).sum = (widths.take t).sum + widths.getD t 0 := by decide
    rw [this t (by omega)]

theorem globalColumnBasesW_get {t : Nat} (ht : t < 6) :
    globalColumnBasesW[t]'(by rw [globalColumnBasesW_eq]; exact ht) = 5 + (widths.take t).sum := by
  simp only [globalColumnBasesW_eq]
  interval_cases t <;> rfl

theorem widths_prefix_le {t : Nat} (ht : t ≤ 6) : (widths.take t).sum ≤ 153 := by
  interval_cases t <;> decide

theorem widths_prefix_six : (widths.take 6).sum = 153 := by decide

theorem widths_prefix_succ {t : Nat} (ht : t < 6) :
    (widths.take (t + 1)).sum = (widths.take t).sum + widths.getD t 0 := by
  interval_cases t <;> decide

/-- **The six tables' claims**, from word `L` on. -/
theorem tablesLoop_spec {s0 : QState} {E : QState → Prop} {w : UInt64} {e0 L : Nat}
    {ev : Array (Array EW × Array EW)} (hev : ev.size = 6)
    (hwid : ∀ t < 6, (ev.getD t (#[], #[])).2.size = widths.getD t 0)
    (h15 : s0.reg .r15 = 6) (h14 : s0.reg .r14 = wd w e0) (h12 : s0.reg .r12 = wd w L)
    (h13 : s0.reg .r13 = 5)
    (hE : ∀ t < 6, EVec s0.mem (wd w (e0 + 246 * t)) tablePointCap (ev.getD t (#[], #[])).1 ∧
      EVec s0.mem (wd w (e0 + 246 * t + 61)) widthCap (ev.getD t (#[], #[])).2)
    (hdst : ∀ k, L ≤ k → k < L + 76 * 153 → (s0.mem (wd w k)).isSome)
    (hL : e0 + 246 * 6 ≤ L) (hl : L + 76 * 153 < 2 ^ 61) :
    WP (.loop (.test false .r15 (.reg .r15)) claimTableC) s0 (fun s' ↦
      NewClaimsAt s'.mem w L (tableColumnClaims ev) ∧ Wr w (fun k ↦ L ≤ k ∧ k < L + 76 * 153) s0 s' ∧
      DomEq s0 s' ∧ s'.reg .r13 = (5 + 153).toUInt64 ∧
      RegsFrame [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s0 s') E := by
  have hkeep : ∀ t : QState, Wr w (fun k ↦ L ≤ k ∧ k < L + 76 * 153) s0 t →
      ∀ j, j < L → t.mem (wd w j) = s0.mem (wd w j) := fun t hW j hj ↦
    hW.word (by omega) fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩
  refine WP.loop (fun t ↦ ∃ T ≤ 6, t.reg .r15 = (6 - T).toUInt64 ∧
      t.reg .r14 = wd w (e0 + 246 * T) ∧ t.reg .r12 = wd w (L + 76 * (widths.take T).sum) ∧
      t.reg .r13 = (5 + (widths.take T).sum).toUInt64 ∧ NewClaimsAt t.mem w L (claimsPrefix ev T) ∧
      Wr w (fun k ↦ L ≤ k ∧ k < L + 76 * 153) s0 t ∧ DomEq s0 t ∧
      RegsFrame [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s0 t)
    (fun t ↦ (t.reg .r15).toNat) ⟨0, by omega, by rw [h15]; rfl,
      by rw [h14, Nat.mul_zero, Nat.add_zero], by rw [h12]; simp, by rw [h13]; rfl,
      by rw [claimsPrefix_zero]; intro j hj; simp at hj, Wr.refl _ _ _, DomEq.refl _,
      RegsFrame.refl _ _⟩ ?_ ?_
  · rintro t ⟨T, hT, h15', h14', h12', h13', hN, hW, hD, hR⟩ hcond
    have hT6 : T < 6 := (test_count h15' (by omega)).mp hcond
    have hM := claimsPrefix_size hev hwid T (by omega)
    have hvsz := hwid T hT6
    have hle := widths_prefix_le (t := T + 1) (by omega)
    have hsucc := widths_prefix_succ hT6
    obtain ⟨hp, hv⟩ := hE T hT6
    have hp' : EVec t.mem (wd w (e0 + 246 * T)) tablePointCap (ev.getD T (#[], #[])).1 :=
      hp.congr fun k hk ↦ by
        rw [wd_wd]
        exact hkeep t hW _ (by unfold vecWords tablePointCap at hk; omega)
    have hv' : EVec t.mem (wd w (e0 + 246 * T + 61)) widthCap (ev.getD T (#[], #[])).2 :=
      hv.congr fun k hk ↦ by
        rw [wd_wd]
        exact hkeep t hW _ (by unfold vecWords widthCap at hk; omega)
    refine WP.mono (claimTable_spec (L := L) (M := (widths.take T).sum)
      (base := 5 + (widths.take T).sum) h14' h15' hT6 h12' h13' (by omega) hp' hv' hN hM
      (fun k hk1 hk2 ↦ by rw [hD]; exact hdst k (by omega) (by rw [hvsz] at hk2; omega))
      (by omega) (by rw [hvsz]; omega)) ?_ (fun _ h ↦ h)
    rintro t' ⟨hN', hW', hD', r12', r13', r14', r15', hR'⟩
    refine ⟨⟨T + 1, by omega, r15', r14'.trans (congrArg (wd w) (by omega)),
      r12'.trans (congrArg (wd w) (by rw [hvsz, hsucc])),
      r13'.trans (by rw [hvsz, hsucc, Nat.add_assoc]), ?_,
      hW.trans (hW'.mono fun k ⟨h1, h2⟩ ↦ ⟨by omega, by rw [hvsz] at h2; omega⟩), hD.trans hD',
      RegsFrame.trans hR hR'⟩, ?_⟩
    · rw [claimsPrefix_succ hev hT6, globalColumnBasesW_get hT6]
      exact hN'
    · rw [r15', h15', Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨T, hT, h15', -, -, h13', hN, hW, hD, hR⟩ hcond
    have h1 : ¬ T < 6 := fun h ↦ by
      rw [(test_count h15' (by omega)).mpr h] at hcond
      exact absurd hcond (by decide)
    obtain rfl : T = 6 := by omega
    rw [claimsPrefix_six hev] at hN
    rw [widths_prefix_six] at h13'
    exact ⟨hN, hW, hD, h13', hR⟩

/-- `tableColumnClaims` of evaluations `widths` long: one claim per table column. -/
theorem tableColumnClaims_size {ev : Array (Array EW × Array EW)} (hev : ev.size = 6)
    (hwid : ∀ t < 6, (ev.getD t (#[], #[])).2.size = widths.getD t 0) :
    (tableColumnClaims ev).size = 153 := by
  rw [← claimsPrefix_six hev, claimsPrefix_size hev hwid 6 le_rfl, widths_prefix_six]

/-- The first new claim's address: `n · 608` bytes, by shifts. -/
theorem claimsAddr_val (w : UInt64) (n : Nat) :
    n.toUInt64 <<< 9 + n.toUInt64 <<< 6 + n.toUInt64 <<< 5 + wd w 0 = wd w (76 * n) := by
  rw [show n.toUInt64 <<< 9 = n.toUInt64 <<< (9 : Nat).toUInt64 from rfl,
    show n.toUInt64 <<< 6 = n.toUInt64 <<< (6 : Nat).toUInt64 from rfl,
    show n.toUInt64 <<< 5 = n.toUInt64 <<< (5 : Nat).toUInt64 from rfl,
    toUInt64_shl _ _ (by omega), toUInt64_shl _ _ (by omega), toUInt64_shl _ _ (by omega),
    toUInt64_add, toUInt64_add, wd_zero, wd, UInt64.add_comm]
  congr 2
  omega

theorem claimsCount_val (n : Nat) : n.toUInt64 + (5 + 153 : Nat).toUInt64 - 5 = (n + 153).toUInt64 := by
  rw [toUInt64_add, show n + (5 + 153) = (n + 153) + 5 by omega, ← toUInt64_add]
  exact UInt64.add_sub_cancel _ _

variable {env : Env} {s : QState} {E : QState → Prop}

/-- **The tables' column claims**, appended at `claimsR`. -/
theorem claimsC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    (ev : Array (Array EW × Array EW)) (acc : Array ColumnClaimW)
    (hev : EvalsAt s.mem (wd env.work oE) ev)
    (hwid : ∀ t < 6, (ev.getD t (#[], #[])).2.size = widths.getD t 0)
    (hacc : ClaimsAt s.mem (wd env.work oC) acc) (hsz : acc.size ≤ busClaimCount) :
    WP claimsC s (fun s' ↦ ClaimsAt s'.mem (wd env.work oC) (acc ++ tableColumnClaims ev) ∧
      Wr env.work (fun k ↦ oC ≤ k ∧ k < oC + claimsWords) s s' ∧ RegsFrame arrRegs s s') E := by
  obtain ⟨-, ⟨-, hcnt⟩, hcl⟩ := hacc
  have hn4 : acc.size ≤ 4 := hsz
  have hcnt' := hcnt
  wnorm at hcnt'
  unfold claimsC
  simp only [oC, oE, claimsWords_val]
  wst
  wst
  fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep
  refine wp_leaA (j := 76 * acc.size) (by rsimp; exact claimsAddr_val _ _) ?_
  fstep
  refine wp_leaA (w := env.work) (j := 0) (by rsimp) ?_
  fstep
  refine WP.then (tablesLoop_spec (w := env.work) (e0 := 0 + 14093)
    (L := 76 * acc.size + (15569 + 1)) hev.1 hwid (by rsimp) (by rsimp) (by rsimp) (by rsimp)
    (fun t ht ↦ ?_) (fun k h1 h2 ↦ hws k (by omega) (by omega)) (by omega) (by omega))
    fun s1 hs1 ↦ ?_
  · have := hev.2 t ht
    rw [evalStride_val, evOff_val, wd_wd, wd_wd] at this
    refine ⟨this.1, ?_⟩
    rw [Nat.add_assoc]
    exact this.2
  obtain ⟨hN, hW, -, h13', hR⟩ := hs1
  have hkeep : ∀ j, j < 76 * acc.size + (15569 + 1) → s1.mem (wd env.work j) = s.mem (wd env.work j) :=
    fun j hj ↦ hW.word (by omega) fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩
  have hbp : s1.reg .rbp = wd env.work 0 := by rw [hR .rbp (by decide)]; rsimp
  refine wp_ldA (k := 15569) hbp (by rw [Nat.zero_add, hkeep _ (by omega)]; exact hcnt') ?_
  fstep
  fstep
  refine wp_stA (k := 15569) (by rsimp; exact hbp)
    (by simp only [QState.setReg_mem]; rw [hkeep _ (by omega), hcnt']; rfl) ?_
  fdone
  have htc := tableColumnClaims_size hev.1 hwid
  have hcw : claimWords = 76 := by decide
  refine ⟨⟨by rw [Array.size_append, htc, claimCap_val]; omega,
    ⟨by rw [Array.size_append, htc]; omega, ?_⟩, fun i hi ↦ ?_⟩,
    Wr.setMem (Wr.setReg (Wr.setReg (Wr.setReg (Wr.trans (fun _ _ ↦ rfl)
      (hW.mono fun k ⟨h1, h2⟩ ↦ ⟨by omega, by omega⟩)) _ _) _ _) _ _) ⟨by omega, by omega⟩ _,
    RegsFrame.trans (RegsFrame.trans (by rfw) (RegsFrame.mono hR (by decide))) (by rfw)⟩
  · rw [mem_setMem_eq _ (by omega), h13', claimsCount_val, Array.size_append, htc]
  · rw [Array.size_append] at hi
    rcases Nat.lt_or_ge i acc.size with hi' | hi'
    · rw [Array.getElem_append_left hi']
      refine (hcl i hi').congr fun k hk ↦ ?_
      rw [hcw] at hk
      rw [wd_wd, wd_wd, hcw, mem_setMem_ne _ (by omega) (by omega) (by omega), QState.setReg_mem,
        QState.setReg_mem, QState.setReg_mem, hkeep _ (by omega)]
    · rw [Array.getElem_append_right hi']
      rw [show wd (wd env.work 15569) (1 + claimWords * i) =
        wd env.work (76 * acc.size + (15569 + 1) + 76 * (i - acc.size)) by
          rw [wd_wd, hcw]; congr 1; omega]
      refine (hN (i - acc.size) (by omega)).congr fun k hk ↦ ?_
      rw [hcw] at hk
      rw [wd_wd, mem_setMem_ne _ (by omega) (by omega) (by omega)]
      rfl

end NativeVm.Code.P4
