module

public import NativeVm.Code.Phase3.Frame
public import NativeVm.Code.Phase3.Fp

/-!
# A side's total

`accumulateSide`'s total, `tv + dot fsels (ffp.map (β + ·)) + (sumE (fsels ++ tsels) + 1) + pad`
(`accumulateSide_split`), from the side's tree value, framework selectors, fingerprints, table
selectors and padding sum: `totalCode side` (`totalCode_spec`), into word `totW side`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

/-- The words of the side's values. -/
def tvW (side : Nat) : Nat := 52832 + 2 * side
def betaW : Nat := 52702
def fpW (side : Nat) : Nat := 52860 + 6 * side
def fselW (side : Nat) : Nat := 53386 + 512 * side
def tselW (side : Nat) : Nat := 53182 + 512 * side
def padW (side : Nat) : Nat := 54462 + 8 * side
def totW (side : Nat) : Nat := 52872 + 2 * side

theorem offs_eq {side : Nat} (h : side < 3) : treeR.off + 2 * side = tvW side ∧
    (fselR side).off = fselW side ∧ (tselR side).off = tselW side ∧
    (sumR side).off = padW side ∧ totalsR.off + 2 * side = totW side ∧ fpR.off + 6 * side = fpW side := by
  interval_cases side <;> decide

abbrev sU : Nat := sl 14
abbrev sA : Nat := sl 15
abbrev sT : Nat := sl 16
abbrev sSum : Nat := sl 13

/-- The framework selectors' sum: `0 + fs₀ + fs₁ + fs₂`, or `0` on the count side. -/
def ops1 (side : Nat) : List EOp :=
  if side = 2 then [.copy sZero sU]
  else [.add sZero (fselW side) sU, .add sU (fselW side + 2) sU, .add sU (fselW side + 4) sU]

/-- The total, from the table selectors' sum at `sSum`. -/
def ops2 (side : Nat) : List EOp :=
  if side = 2 then
    [.add (tvW side) sZero sT, .add sSum sOne sU, .add sT sU sT, .add sT (padW side) (totW side)]
  else
    [.add betaW (fpW side) sA, .mul (fselW side) sA sA, .add sZero sA sT,
      .add betaW (fpW side + 2) sA, .mul (fselW side + 2) sA sA, .add sT sA sT,
      .add betaW (fpW side + 4) sA, .mul (fselW side + 4) sA sA, .add sT sA sT,
      .add (tvW side) sT sT, .add sSum sOne sU, .add sT sU sT, .add sT (padW side) (totW side)]

/-- The table blocks of a side: `51`, `51`, `45`. -/
def nBlocks (side : Nat) : Nat := if side = 2 then 45 else 51

/-- **A side's total.** -/
def totalCode (side : Nat) : Stmt := blk [
  I (.load .r14 (cw ctxWork)),
  opsCode (ops1 side),
  I (.load .r9 (at_ .r14 (wdisp sU))), I (.load .r10 (at_ .r14 (wdisp (sU + 1)))),
  I (.mov .r13 .r14), I (.addi .r13 (wdisp (tselW side))), I (.movi .r15 (Int64.ofNat (nBlocks side))),
  esum,
  I (.store (at_ .r14 (wdisp sSum)) .r9), I (.store (at_ .r14 (wdisp (sSum + 1))) .r10),
  opsCode (ops2 side)]

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

/-- The regions `totalCode side` writes. -/
abbrev pcR (side : Nat) : List Region := [⟨sSum, 8⟩, ⟨totW side, 2⟩]

theorem pc_R_ok {side : Nat} (h : side < 3) : ∀ r ∈ pcR side, Ok3 r := by
  intro r hr
  simp only [pcR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ok3_sreg (off := 236) (size := 8) (by norm_num)
  · have := ok3_sreg (off := 202 + 2 * side) (size := 2) (by omega)
    simp only [sreg, scratchR_off] at this
    rwa [show 52670 + (202 + 2 * side) = totW side by unfold totW; omega] at this

theorem pc_int64_ofNat (n : Nat) : (Int64.ofNat n).toUInt64 = n.toUInt64 :=
  UInt64.toNat_inj.mp (by simp)

theorem pc_arr3 {xs : Array EW} (h : xs.size = 3) :
    xs = #[xs[0]'(by omega), xs[1]'(by omega), xs[2]'(by omega)] := by
  apply Array.ext
  · simp [h]
  · intro i h1 h2
    rw [h] at h1
    rcases i with _ | _ | _ | i <;> simp
    omega

theorem pc_el {m : UInt64 → Option UInt64} {w : UInt64} {k i : Nat} {xs : Array EW}
    (h : EWArr m (wd w k) xs) (hi : i < xs.size) : EWAt m (wd w (k + 2 * i)) xs[i] := by
  have := h i hi
  rwa [wd_wd] at this

/-- **A straight-line program** writing slots of the regions `ws` only. -/
theorem pc_ops_wrote (l : List EOp) {S : List Nat} {v : Nat → EW} {ws : List Region}
    (hws : ∀ r ∈ ws, Ok3 r) (hi : Inputs env inp s.mem) (h14 : s.reg .r14 = env.work)
    (hS : Holds s.mem env.work S v) (hSe : ∀ k ∈ S, k % 2 = 0 ∧ k + 1 < 2 ^ 60)
    (hval : opsValid l S = true)
    (hde : ∀ d ∈ opsDsts l, d % 2 = 0 ∧ ∃ r ∈ ws, r.off ≤ d ∧ d + 2 ≤ r.stop) :
    WP (opsCode l) s (fun s' ↦ Holds s'.mem env.work (opsDsts l ++ S) (opsRun l v) ∧
      Wrote env ws s s' ∧ RegsFrame opRegs s s') E := by
  have hde' : ∀ d ∈ opsDsts l, d % 2 = 0 ∧ ∃ r ∈ ws, Ok3 r ∧ r.off ≤ d ∧ d + 2 ≤ r.stop :=
    fun d hd ↦ let ⟨h1, r, hr, h2⟩ := hde d hd; ⟨h1, r, hr, hws r hr, h2⟩
  refine WP.mono (ops_spec l (lim := 2 ^ 60) (by norm_num) h14 hS hSe hval
    (fun d hd ↦ ?_) (fun d hd ↦ ?_)) ?_ fun _ h ↦ h
  · obtain ⟨h1, r, -, hr, h2, h3⟩ := hde' d hd
    have hb := hr.bounds
    rw [dataEnd_val] at hb
    unfold Region.stop at hb h3
    exact ⟨h1, by omega⟩
  · obtain ⟨-, r, -, hr, h2, h3⟩ := hde' d hd
    exact ⟨hi.ok3_some' hr (by omega), hi.ok3_some' hr (by omega)⟩
  rintro s' ⟨hH, hk, hsome, hout, hf⟩
  refine ⟨hH, ⟨hf .rdi (by decide), fun a ha ↦ ?_, hsome⟩, hf⟩
  by_cases hw : ∃ k < 2 ^ 60, a = wd env.work k
  · obtain ⟨k, hk', rfl⟩ := hw
    refine hk k hk' fun d hd ↦ ?_
    obtain ⟨-, r, hrm, hr, h2, h3⟩ := hde' d hd
    have hb := hr.bounds
    rw [dataEnd_val] at hb
    unfold Region.stop at hb h3
    constructor
    · intro e
      exact ha r hrm ⟨k - r.off, by omega, by congr 1; omega⟩
    · intro e
      exact ha r hrm ⟨k - r.off, by omega, by congr 1; omega⟩
  · exact hout a fun k hk' e ↦ hw ⟨k, hk', e⟩

/-- The framework selectors' sum into `sU`. -/
theorem pc_ops1_spec {side : Nat} (hside : side < 3) {fsels : Array EW} (hi : Inputs env inp s.mem)
    (h14 : s.reg .r14 = env.work) (hzero : EWAt s.mem (wd env.work sZero) 0)
    (hfs : EWArr s.mem (wd env.work (fselW side)) fsels)
    (hfsz : fsels.size = if side = 2 then 0 else 3) :
    WP (opsCode (ops1 side)) s (fun s' ↦ EWAt s'.mem (wd env.work sU) (sumE fsels) ∧
      Wrote env (pcR side) s s' ∧ RegsFrame opRegs s s') E := by
  obtain h2 | h2 := (by omega : side < 2 ∨ side = 2)
  · have hsz : fsels.size = 3 := by rw [hfsz]; split <;> omega
    have e0 := pc_el hfs (i := 0) (by omega)
    have e1 := pc_el hfs (i := 1) (by omega)
    have e2 := pc_el hfs (i := 2) (by omega)
    rw [pc_arr3 hsz]
    generalize fsels[0] = f0 at e0
    generalize fsels[1] = f1 at e1
    generalize fsels[2] = f2 at e2
    have hs : side = 0 ∨ side = 1 := by omega
    refine WP.mono (pc_ops_wrote (ops1 side) (S := List.map (·.1) [(sZero, (0 : EW)),
      (fselW side, f0), (fselW side + 2, f1), (fselW side + 4, f2)]) (pc_R_ok hside) hi h14
      (holds_vOf _ (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
        (by simpa using ⟨hzero, e0, e1, e2⟩))
      (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
      (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
      (by rcases hs with rfl | rfl <;> decide)) ?_ fun _ h ↦ h
    rintro s' ⟨hH, hw, hf⟩
    refine ⟨?_, hw, hf⟩
    have := hH sU (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
    rcases hs with rfl | rfl <;>
      simpa [opsRun, ops1, EOp.eval, EOp.dst, vOf_cons, sl, fselW, Function.update_apply, sumE,
        ← Array.foldl_toList] using this
  · subst h2
    have hsz : fsels = #[] := Array.eq_empty_of_size_eq_zero (by simpa using hfsz)
    subst hsz
    refine WP.mono (pc_ops_wrote _ (S := List.map (·.1) [(sZero, (0 : EW))]) (pc_R_ok hside) hi h14
      (holds_vOf _ (by decide) (by simpa using hzero)) (by decide) (by decide) (by decide)) ?_
      fun _ h ↦ h
    rintro s' ⟨hH, hw, hf⟩
    refine ⟨?_, hw, hf⟩
    have := hH sU (by decide)
    simpa [opsRun, ops1, EOp.eval, EOp.dst, vOf_cons, sl, Function.update_apply, sumE] using this

/-- The total from the table selectors' sum `S` at `sSum`. -/
theorem pc_ops2_spec {side : Nat} (hside : side < 3) {tv β pad S : EW} {fsels ffp : Array EW}
    (hi : Inputs env inp s.mem) (h14 : s.reg .r14 = env.work)
    (hzero : EWAt s.mem (wd env.work sZero) 0) (hone : EWAt s.mem (wd env.work sOne) 1)
    (htv : EWAt s.mem (wd env.work (tvW side)) tv)
    (hb : side < 2 → EWAt s.mem (wd env.work betaW) β)
    (hfs : EWArr s.mem (wd env.work (fselW side)) fsels)
    (hfsz : fsels.size = if side = 2 then 0 else 3)
    (hfp : EWArr s.mem (wd env.work (fpW side)) ffp) (hfpz : ffp.size = fsels.size)
    (hS : EWAt s.mem (wd env.work sSum) S)
    (hpad : EWAt s.mem (wd env.work (padW side)) pad) :
    WP (opsCode (ops2 side)) s (fun s' ↦ EWAt s'.mem (wd env.work (totW side))
        (tv + dot fsels (ffp.map (β + ·)) + (S + 1) + pad) ∧ Wrote env (pcR side) s s') E := by
  obtain h2 | h2 := (by omega : side < 2 ∨ side = 2)
  · have hsz : fsels.size = 3 := by rw [hfsz]; split <;> omega
    have hpz : ffp.size = 3 := by omega
    have e0 := pc_el hfs (i := 0) (by omega)
    have e1 := pc_el hfs (i := 1) (by omega)
    have e2 := pc_el hfs (i := 2) (by omega)
    have g0 := pc_el hfp (i := 0) (by omega)
    have g1 := pc_el hfp (i := 1) (by omega)
    have g2 := pc_el hfp (i := 2) (by omega)
    have hβ := hb h2
    rw [pc_arr3 hsz, pc_arr3 hpz]
    generalize fsels[0] = f0 at e0
    generalize fsels[1] = f1 at e1
    generalize fsels[2] = f2 at e2
    generalize ffp[0] = p0 at g0
    generalize ffp[1] = p1 at g1
    generalize ffp[2] = p2 at g2
    have hs : side = 0 ∨ side = 1 := by omega
    refine WP.mono (pc_ops_wrote (ops2 side) (S := List.map (·.1) [(betaW, β), (fpW side, p0),
      (fpW side + 2, p1), (fpW side + 4, p2), (fselW side, f0), (fselW side + 2, f1),
      (fselW side + 4, f2), (sZero, (0 : EW)), (tvW side, tv), (sSum, S), (sOne, (1 : EW)),
      (padW side, pad)]) (pc_R_ok hside) hi h14
      (holds_vOf _ (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
        (by simpa using ⟨hβ, g0, g1, g2, e0, e1, e2, hzero, htv, hS, hone, hpad⟩))
      (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
      (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
      (by rcases hs with rfl | rfl <;> decide)) ?_ fun _ h ↦ h
    rintro s' ⟨hH, hw, -⟩
    refine ⟨?_, hw⟩
    have := hH (totW side)
      (by rcases hs with rfl | rfl <;> simp only [List.map_cons, List.map_nil] <;> decide)
    rw [List.map_toArray, List.map_cons, List.map_cons, List.map_cons, List.map_nil, dot3]
    rcases hs with rfl | rfl <;>
      simpa [opsRun, ops2, EOp.eval, EOp.dst, vOf_cons, sl, fselW, fpW, tvW, betaW, padW, totW,
        Function.update_apply] using this
  · subst h2
    have hsz : fsels = #[] := Array.eq_empty_of_size_eq_zero (by simpa using hfsz)
    have hpz : ffp = #[] := Array.eq_empty_of_size_eq_zero (by simpa [hsz] using hfpz)
    subst hsz hpz
    refine WP.mono (pc_ops_wrote _ (S := List.map (·.1) [(sZero, (0 : EW)), (tvW 2, tv), (sSum, S),
      (sOne, (1 : EW)), (padW 2, pad)]) (pc_R_ok hside) hi h14
      (holds_vOf _ (by simp only [List.map_cons, List.map_nil]; decide)
        (by simpa using ⟨hzero, htv, hS, hone, hpad⟩))
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide) (by decide)) ?_ fun _ h ↦ h
    rintro s' ⟨hH, hw, -⟩
    refine ⟨?_, hw⟩
    have := hH (totW 2) (by simp only [List.map_cons, List.map_nil]; decide)
    simpa [opsRun, ops2, EOp.eval, EOp.dst, vOf_cons, sl, tvW, padW, totW, Function.update_apply,
      dot] using this

/-- A word apart from the regions `totalCode side` writes survives. -/
theorem pc_word3 {side : Nat} {s' : QState} (hw : Wrote env (pcR side) s s') {k : Nat}
    (hk : k < 52906 ∨ 52914 ≤ k) (hk2 : k < 52872 + 2 * side ∨ 52874 + 2 * side ≤ k)
    (hk' : k < 2 ^ 61) (hside : side < 3) : s'.mem (wd env.work k) = s.mem (wd env.work k) := by
  refine hw.word (fun r hr ↦ ?_) hk' (fun r hr ↦ ?_)
  all_goals
    simp only [pcR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [Region.stop, totW, sl] <;> omega

theorem pc_ewat {side : Nat} {s' : QState} (hw : Wrote env (pcR side) s s') {k : Nat} {x : EW}
    (h : EWAt s.mem (wd env.work k) x) (hk : k + 2 ≤ 52906 ∨ 52914 ≤ k)
    (hk2 : k + 2 ≤ 52872 + 2 * side ∨ 52874 + 2 * side ≤ k) (hk' : k + 1 < 2 ^ 61)
    (hside : side < 3) : EWAt s'.mem (wd env.work k) x :=
  h.congr fun j hj ↦ by rw [wd_wd]; exact pc_word3 hw (by omega) (by omega) (by omega) hside

theorem pc_ewarr {side : Nat} {s' : QState} (hw : Wrote env (pcR side) s s') {k : Nat}
    {xs : Array EW} (h : EWArr s.mem (wd env.work k) xs) (hk : k + 2 * xs.size ≤ 52906 ∨ 52914 ≤ k)
    (hk2 : k + 2 * xs.size ≤ 52872 + 2 * side ∨ 52874 + 2 * side ≤ k)
    (hk' : k + 2 * xs.size < 2 ^ 61) (hside : side < 3) : EWArr s'.mem (wd env.work k) xs :=
  h.congr (n := 2 * xs.size) (fun j hj ↦ by
    rw [wd_wd]; exact pc_word3 hw (by omega) (by omega) (by omega) hside) le_rfl

/-- **A side's total** (`accumulateSide_split`'s), from its tree value `tv`, framework selectors
`fsels` and fingerprints `ffp` (none on the count side), table selectors `tsels` and padding rows'
sum `pad`. -/
theorem totalCode_spec {side : Nat} (hside : side < 3) (hrdi : s.reg .rdi = env.ctx)
    (hwp : s.mem (wd env.ctx ctxWork) = some env.work) (hi : Inputs env inp s.mem)
    {tv β pad : EW} {fsels ffp tsels : Array EW}
    (hzero : EWAt s.mem (wd env.work sZero) 0) (hone : EWAt s.mem (wd env.work sOne) 1)
    (htv : EWAt s.mem (wd env.work (tvW side)) tv)
    (hb : side < 2 → EWAt s.mem (wd env.work betaW) β)
    (hfs : EWArr s.mem (wd env.work (fselW side)) fsels)
    (hfsz : fsels.size = if side = 2 then 0 else 3)
    (hfp : EWArr s.mem (wd env.work (fpW side)) ffp) (hfpz : ffp.size = fsels.size)
    (hts : EWArr s.mem (wd env.work (tselW side)) tsels) (htsz : tsels.size = nBlocks side)
    (hpad : EWAt s.mem (wd env.work (padW side)) pad) :
    WP (totalCode side) s (fun s' ↦ EWAt s'.mem (wd env.work (totW side))
        (tv + dot fsels (ffp.map (β + ·)) + (sumE (fsels ++ tsels) + 1) + pad) ∧
      Wrote env [⟨sSum, 8⟩, ⟨totW side, 2⟩] s s') E := by
  have hR := pc_R_ok hside
  have hcase : (side = 2 ∧ fsels.size = 0) ∨ (side < 2 ∧ fsels.size = 3) := by
    rw [hfsz]; split <;> omega
  have hnb : nBlocks side ≤ 51 := by unfold nBlocks; split <;> omega
  unfold totalCode
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine WP.blk_cons (WP.mono (pc_ops1_spec (s := s.setReg .r14 env.work) hside hi (by rsimp) hzero
    hfs hfsz) ?_ fun _ h ↦ h)
  rintro s1 ⟨hU, w1, f1⟩
  have h14 : s1.reg .r14 = env.work := by rw [f1 .r14 (by decide)]; rsimp
  have w1' : Wrote env (pcR side) s s1 := ⟨by rw [w1.rdi]; rsimp, w1.mem, w1.dom⟩
  refine wp_load (ew_at h14) hU.1 ?_
  refine wp_load (ew_at (by rsimp; exact h14)) (by rsimp; exact ewat_hi hU) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
  have hts1 : EWArr s1.mem (wd env.work (tselW side)) tsels :=
    pc_ewarr w1' hts (by unfold tselW; omega) (by unfold tselW; omega) (by unfold tselW; omega) hside
  refine WP.blk_cons (WP.mono (esum_spec (w := env.work) (xs := tsels) (a := tselW side)
    (n := nBlocks side) (by omega) (by rsimp; rw [h14]; rfl) (by rsimp; exact pc_int64_ofNat _)
    hts1 (by unfold tselW; omega)) ?_ fun _ h ↦ h)
  rintro s2 ⟨hA, hm2, f2⟩
  have h14' : s2.reg .r14 = env.work := by rw [f2 .r14 (by decide)]; rsimp; exact h14
  have w2 : Wrote env (pcR side) s s2 :=
    ⟨by rw [f2 .rdi (by decide)]; rsimp; exact w1'.rdi,
      fun a ha ↦ by simp only [hm2, QState.setReg_mem]; exact w1'.mem a ha,
      fun a ↦ by simp only [hm2, QState.setReg_mem]; exact w1'.dom a⟩
  have hA' : (⟨s2.reg .r9, s2.reg .r10⟩ : EW) = sumE (fsels ++ tsels) := by
    rw [hA, ← htsz, Array.extract_size]
    rsimp
    simp only [sumE, Array.foldl_append]
  have hs0 := hi.ok3_some' (hR ⟨sSum, 8⟩ (by simp)) (a := sSum) (by simp [Region.stop])
  have hs1 := hi.ok3_some' (hR ⟨sSum, 8⟩ (by simp)) (a := sSum + 1) (by simp [Region.stop])
  show WP (blk (stA sSum ++ [opsCode (ops2 side)])) s2 _ _
  refine stA_spec h14' (by decide) (by rw [w2.dom]; exact hs0) (by rw [w2.dom]; exact hs1) ?_
  have w3 : Wrote env (pcR side) s ⟨s2.reg, updE s2.mem env.work sSum ⟨s2.reg .r9, s2.reg .r10⟩⟩ := by
    refine ⟨w2.rdi, fun a ha ↦ ?_, fun a ↦ ?_⟩
    · have n0 : a ≠ wd env.work sSum := fun e ↦ ha ⟨sSum, 8⟩ (by simp) ⟨0, by decide, by rw [e]; rfl⟩
      have n1 : a ≠ wd env.work (sSum + 1) := fun e ↦
        ha ⟨sSum, 8⟩ (by simp) ⟨1, by decide, by rw [e]⟩
      dsimp only
      simp only [updE, Function.update_apply, n0, n1, ↓reduceIte]
      exact w2.mem a ha
    · dsimp only
      rw [updE_isSome (by rw [w2.dom]; exact hs0) (by rw [w2.dom]; exact hs1), w2.dom]
  have hS3 : EWAt (updE s2.mem env.work sSum ⟨s2.reg .r9, s2.reg .r10⟩) (wd env.work sSum)
      (sumE (fsels ++ tsels)) := hA' ▸ updE_ewat (by decide)
  refine WP.blk_cons (WP.mono (pc_ops2_spec (S := sumE (fsels ++ tsels)) (β := β)
    (s := ⟨s2.reg, updE s2.mem env.work sSum ⟨s2.reg .r9, s2.reg .r10⟩⟩) hside
    (hi.step3 hR w3.step hrdi) h14'
    (pc_ewat w3 hzero (by simp [sl]) (by simp [sl]; omega) (by simp [sl]) hside)
    (pc_ewat w3 hone (by simp [sl]) (by simp [sl]; omega) (by simp [sl]) hside)
    (pc_ewat w3 htv (by unfold tvW; omega) (by unfold tvW; omega) (by unfold tvW; omega) hside)
    (fun h ↦ pc_ewat w3 (hb h) (by unfold betaW; omega) (by unfold betaW; omega)
      (by unfold betaW; omega) hside)
    (pc_ewarr w3 hfs (by unfold fselW; omega) (by unfold fselW; omega) (by unfold fselW; omega) hside)
    hfsz
    (pc_ewarr w3 hfp (by unfold fpW; omega) (by unfold fpW; omega) (by unfold fpW; omega) hside)
    hfpz hS3
    (pc_ewat w3 hpad (by unfold padW; omega) (by unfold padW; omega) (by unfold padW; omega) hside))
    ?_ fun _ h ↦ h)
  rintro s4 ⟨hT, w4⟩
  exact WP.blk_nil ⟨hT, w3.trans w4⟩

end NativeVm.Code.P3
