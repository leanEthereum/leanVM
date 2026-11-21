module

public import NativeVm.Code.Phase3.Pieces

/-!
# The bus's forms emptied, its point and totals

`formsInit`: every one of the `3 · nTables` forms at `busR` empty (`forms0`, the model's
`forms0`); `busTail`: the GKR point (its count from `depthR`) and the three totals into `busR`
after the forms (`busTailR`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters LeanVM.Protocol.Verifier

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

/-- The model's empty forms. -/
def forms0 : Array (Array FormW) := tablesW.map fun _ ↦ #[#[], #[], #[]]

/-- **Every form empty**: a count `0` at each form's first word. -/
def formsInit : Stmt := blk (I (.load .r14 (cw ctxWork)) ::
  (List.range (3 * nTables)).map fun j ↦ I (.storei (at_ .r14 (wdisp (busR.off + formWords * j))) 0))

theorem pc_tablesW_size : tablesW.size = nTables := by simp [tablesW]; rfl

theorem pc_forms0_get {t : Nat} (ht : t < nTables) : forms0.getD t #[] = #[#[], #[], #[]] := by
  simp [Array.getD, forms0, pc_tablesW_size, ht]

/-- Stores of `0` at the forms' first words `l`. -/
theorem pc_zeros {xs : List Stmt} {P : QState → Prop} (l : List Nat) (h14 : s.reg .r14 = env.work)
    (hsome : ∀ j < 3 * nTables, (s.mem (wd env.work (busR.off + formWords * j))).isSome)
    (hl : ∀ j ∈ l, j < 3 * nTables)
    (k : ∀ s', s'.reg = s.reg → (∀ j ∈ l, s'.mem (wd env.work (busR.off + formWords * j)) = some 0) →
      (∀ a, s'.mem a = s.mem a ∨ s'.mem a = some 0) → Wrote env [busR] s s' → WP (blk xs) s' P E) :
    WP (blk (l.map (fun j ↦ I (.storei (at_ .r14 (wdisp (busR.off + formWords * j))) 0)) ++ xs)) s P E := by
  induction l generalizing s with
  | nil => exact k s rfl (by simp) (fun _ ↦ .inl rfl) (Wrote.refl _ _ _)
  | cons j l ih =>
    rw [List.map_cons, List.cons_append]
    have hj := hl j (by simp)
    refine wp_storei (eval_work h14 _) (hsome j hj) ?_
    refine ih (by rsimp; exact h14) (fun j' hj' ↦ by
        have := hsome j' hj'; rw [QState.setMem_mem]; split <;> simp_all)
      (fun j' h ↦ hl j' (by simp [h])) fun s' hr hz ho hw ↦ k s' (by rw [hr]; rfl) ?_ ?_ ?_
    · intro j' hj'
      rcases List.mem_cons.mp hj' with rfl | hj'
      · rcases ho (wd env.work (busR.off + formWords * j')) with h | h
        · rw [h]; simp only [QState.setMem_mem, ↓reduceIte]; rfl
        · exact h
      · exact hz j' hj'
    · intro a
      rcases ho a with h | h
      · rw [h, QState.setMem_mem]
        split
        · right; rfl
        · left; rfl
      · exact .inr h
    · have hb : busR.off + formWords * j < busR.stop := by
        rw [Region.stop, busR_off, busR_size, show formWords = 741 by decide]; unfold nTables at hj
        omega
      exact (wrote_store (s1 := s) (List.mem_singleton_self busR) (by omega) hb rfl rfl
        (hsome j hj) _).trans hw

theorem formsInit_spec (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem) :
    WP formsInit s (fun s' ↦ FormsAt s'.mem (busR.at env.work) forms0 ∧ Wrote env [busR] s s') E := by
  unfold formsInit
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  rw [← List.append_nil (List.map _ (List.range _))]
  refine pc_zeros _ (by rsimp) (fun j hj ↦ hi.ok3_some ok3_busR (by
    rw [busR_size, show formWords = 741 by decide]; unfold nTables at hj; omega))
    (fun j hj ↦ List.mem_range.mp hj) fun s' hr hz ho hw ↦ WP.blk_nil ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [forms0, pc_tablesW_size]
  · intro t ht; rw [pc_forms0_get ht]; rfl
  · intro t ht side hside
    rw [pc_forms0_get ht]
    have hj : 3 * t + side ∈ List.range (3 * nTables) := List.mem_range.mpr (by omega)
    interval_cases side <;>
      exact ⟨by simp, ⟨by simp, by rw [Region.at, wd_wd, formOff, hz _ hj]; rfl⟩, fun i h ↦ by simp at h⟩
  · exact ⟨hw.rdi, hw.mem, hw.dom⟩

/-- The words of `busR` after the forms: the GKR point, the totals. -/
def busTailR : Region := ⟨busR.off + busPointOff, vecWords busPointCap + 2 * nTrees⟩

/-- **The point and the totals** into `busR`. -/
def busTail : Stmt := blk [
  I (.load .r14 (cw ctxWork)),
  I (.load .r15 (at_ .r14 (wdisp depthR.off))),
  I (.store (at_ .r14 (wdisp (busR.off + busPointOff))) .r15),
  I (.mov .r13 .r14), I (.addi .r13 (wdisp pointR.off)), I (.mov .rbx .r14),
  I (.addi .r14 (wdisp (busR.off + busPointOff + 1))), copyE,
  I (.mov .r14 .rbx), I (.mov .r13 .r14), I (.addi .r13 (wdisp totalsR.off)),
  I (.addi .r14 (wdisp (busR.off + busTotalsOff))), I (.movi .r15 3), copyE]

theorem busTail_spec {pt totals : Array EW} (hrdi : s.reg .rdi = env.ctx)
    (hwp : s.mem (wd env.ctx ctxWork) = some env.work) (hi : Inputs env inp s.mem)
    (hdw : NatAt s.mem (depthR.at env.work) pt.size) (hps : pt.size < 64)
    (hp : EWArr s.mem (pointR.at env.work) pt)
    (ht : EWArr s.mem (totalsR.at env.work) totals) (hts : totals.size = 3) :
    WP busTail s (fun s' ↦ EVec s'.mem (wd (busR.at env.work) busPointOff) busPointCap pt ∧
      EWArr s'.mem (wd (busR.at env.work) busTotalsOff) totals ∧ Wrote env [busTailR] s s') E := by
  have hsm : ∀ k, 13960 ≤ k → k < 14093 → (s.mem (wd env.work k)).isSome := fun k h1 h2 ↦
    hi.ok3_some' ok3_busR (by rw [Region.stop, busR_off, busR_size]; omega)
  have hd : s.mem (wd env.work 52879) = some pt.size.toUInt64 := by
    rw [← pc_depthR_off]; exact hdw.2
  have hp' : EWArr s.mem (wd env.work 52704) pt := by rwa [Region.at, pc_pointR_off] at hp
  have ht' : EWArr s.mem (wd env.work 52872) totals := by
    rwa [Region.at, show totalsR.off = 52872 by decide] at ht
  have hTR : busTailR = ⟨13960, 133⟩ := by decide
  have hne : ∀ {a b n : Nat}, a < 2 ^ 61 → b + n < 2 ^ 61 → (a < b ∨ b + n ≤ a) →
      ∀ k < n, wd env.work a ≠ wd env.work (b + k) := fun ha hb h k hk e ↦ by
    rw [wd_inj (by omega) (by omega)] at e; omega
  unfold busTail
  rw [pc_depthR_off, pc_pointR_off, show totalsR.off = 52872 by decide,
    show busR.off + busPointOff = 13960 by decide, show busR.off + busTotalsOff = 14087 by decide]
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine wp_load (eval_work (by rsimp) _) hd ?_
  refine wp_store (eval_work (by rsimp) _) (hsm 13960 le_rfl (by omega)) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  refine WP.blk_cons (WP.mono (copyE_spec (w := env.work) (a := 52704) (b := 13961) (n := pt.size)
    le_rfl ?_ ?_ ?_ ?_ (by right; omega) ⟨by omega, by omega⟩ ?_) ?_ fun _ h ↦ h)
  · rsimp; rfl
  · rsimp; rfl
  · rsimp
  · refine hp'.congr (n := 2 * pt.size) (fun k hk ↦ ?_) le_rfl
    rw [wd_wd]
    simp only [QState.setReg_mem]
    exact setMem_wd_ne _ _ (by omega) (by omega) (by omega)
  · intro k hk
    simp only [QState.setReg_mem, QState.setMem_mem]
    split
    · rfl
    · exact hsm _ (by omega) (by omega)
  rintro s3 ⟨harr, hout, hsome, hf3⟩
  have hbx : s3.reg .rbx = env.work := by rw [hf3 .rbx (by decide)]; rsimp
  have k3 : ∀ j, (j < 13961 ∨ 13961 + 2 * pt.size ≤ j) → j < 2 ^ 60 →
      s3.mem (wd env.work j) = s.mem (wd env.work j) ∨ j = 13960 := fun j h1 h2 ↦ by
    rw [hout _ (hne (by omega) (by omega) h1)]
    simp only [QState.setReg_mem]
    by_cases e : j = 13960
    · exact .inr e
    · exact .inl (setMem_wd_ne _ _ e (by omega) (by omega))
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))))
  refine WP.blk_cons (WP.mono (copyE_spec (w := env.work) (xs := totals) (a := 52872) (b := 14087) (n := 3)
    (by omega) ?_ ?_ ?_ ?_ (by right; omega) ⟨by omega, by omega⟩ ?_) ?_ fun _ h ↦ h)
  · rsimp; rw [hbx]; rfl
  · rsimp; rw [hbx]; rfl
  · rsimp
  · refine ht'.congr (n := 6) (fun k hk ↦ ?_) (by omega)
    rw [wd_wd]
    simp only [QState.setReg_mem]
    rcases k3 (52872 + k) (by omega) (by omega) with h | h
    · exact h
    · omega
  · intro k hk
    simp only [QState.setReg_mem]
    rw [hsome]
    simp only [QState.setReg_mem, QState.setMem_mem]
    split
    · rfl
    · exact hsm _ (by omega) (by omega)
  rintro s4 ⟨harr2, hout2, hsome2, hf4⟩
  have k4 : ∀ j, (j < 14087 ∨ 14093 ≤ j) → j < 2 ^ 60 →
      s4.mem (wd env.work j) = s3.mem (wd env.work j) := fun j h1 h2 ↦ by
    rw [hout2 _ (hne (by omega) (by omega) h1)]; rfl
  rw [Array.extract_size] at harr
  rw [← hts, Array.extract_size] at harr2
  refine WP.blk_nil ⟨⟨show pt.size ≤ 63 by omega, ⟨by omega, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [Region.at, wd_wd, show busR.off + busPointOff = 13960 by decide, k4 _ (by omega) (by omega),
      hout _ (hne (by omega) (by omega) (by omega))]
    simp only [QState.setReg_mem, QState.setMem_mem, ↓reduceIte]
    rsimp
  · rw [Region.at, wd_wd, wd_wd, show busR.off + (busPointOff + 1) = 13961 by decide]
    refine harr.congr (n := 2 * pt.size) (fun k hk ↦ ?_) le_rfl
    rw [wd_wd, k4 _ (by omega) (by omega)]
  · rw [Region.at, wd_wd, show busR.off + busTotalsOff = 14087 by decide]
    exact harr2
  · refine ⟨?_, fun a ha ↦ ?_, fun a ↦ ?_⟩
    · rw [hf4 .rdi (by decide)]; rsimp; rw [hf3 .rdi (by decide)]; rsimp
    · rw [hTR] at ha
      have ha' : ∀ k < 133, a ≠ wd env.work (13960 + k) := fun k hk e ↦
        ha _ (List.mem_singleton_self _) ⟨k, hk, e⟩
      rw [hout2 a fun k hk ↦ by
        have := ha' (127 + k) (by omega); rwa [show 13960 + (127 + k) = 14087 + k by omega] at this]
      simp only [QState.setReg_mem]
      rw [hout a fun k hk ↦ by
        have := ha' (1 + k) (by omega); rwa [show 13960 + (1 + k) = 13961 + k by omega] at this]
      have := ha' 0 (by omega)
      simp only [QState.setReg_mem, QState.setMem_mem, Nat.add_zero] at this ⊢
      simp [this]
    · rw [hsome2 a]
      simp only [QState.setReg_mem]
      rw [hsome a]
      simp only [QState.setReg_mem, QState.setMem_mem]
      split
      · rename_i h; rw [h]; exact (hsm _ le_rfl (by omega)).symm
      · rfl

end NativeVm.Code.P3
