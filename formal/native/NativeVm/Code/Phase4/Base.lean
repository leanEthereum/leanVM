module

public import NativeVm.Code.Phase4.Code
public import NativeVm.Code.Gadgets
public import NativeVm.Code.Contracts

/-!
# Phase 4's frames

The facts phase 4's proof threads through its blocks:

* `Env4`: where the working area is, apart from the context, the decoded proof and the
  transcript's words (from `Inputs` and `CodeRel`);
* `Fr env ws s s'`: a run from `s` to `s'` keeps `rdi`, which words exist (`DomEq`), and every word
  outside the transcript's (`Foot`) and the regions `ws`; the transcript's gadgets give it for any
  `ws` (`Fr.ofKeeps`), phase 4's blocks for the regions they write;
* `Stab env ws X`: `X` survives such a run, so a block that writes `ws` carries it through;
* `Only env ws s s'`: every word outside `ws` kept, the transcript's included, which keeps
  `CodeRel` (`CodeRel.only`).
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

/-! ## The offsets are the regions' -/

theorem layoutR_off : layoutR.off = oL := by decide
theorem busR_off : busR.off = oB := by decide
theorem evalsR_off : evalsR.off = oE := by decide
theorem claimsR_off : claimsR.off = oC := by decide
theorem scratchR_off : scratchR.off = oS := by decide
theorem busPointOff_val : busR.off + busPointOff = oBP := by decide
theorem busTotalsOff_val : busR.off + busTotalsOff = oBT := by decide
theorem formWords_val : formWords = fW := by decide
theorem evalStride_val : evalStride = eS := by decide
theorem evOff_val : vecWords tablePointCap = evOff := by decide
theorem claimWords_val : claimWords = cW := by decide
theorem cV_val : 1 + vecWords pointCap = cV := by decide
theorem formOff_val (t side : Nat) : busR.off + formOff t side = oB + fW * (3 * t + side) := by
  rw [busR_off, formOff, formWords_val]
theorem evalsWords_val : evalsWords = 1476 := by decide
theorem claimsWords_val : claimsWords = 12161 := by decide
theorem scratchWords_val : scratchWords = 32768 := by decide
theorem tWorkWords_val : Transcript.workWords = 69 := (rfl)

/-! ## Domains -/

/-- `s'` has `s`'s words. -/
def DomEq (s s' : QState) : Prop := ∀ a, (s'.mem a).isSome = (s.mem a).isSome

theorem DomEq.refl (s : QState) : DomEq s s := fun _ ↦ rfl

theorem DomEq.trans {s₁ s₂ s₃ : QState} (h : DomEq s₁ s₂) (h' : DomEq s₂ s₃) : DomEq s₁ s₃ :=
  fun a ↦ (h' a).trans (h a)

/-- A run keeps which words exist. -/
theorem WP.domEq {c : Stmt} {s : QState} {P E : QState → Prop} (h : WP c s P E) :
    WP c s (fun s' ↦ P s' ∧ DomEq s s') (fun s' ↦ E s' ∧ DomEq s s') := by
  obtain ⟨o, hx, ho⟩ := h
  refine ⟨o, hx, ?_⟩
  have hd := Exec.mem_isSome hx
  cases o with
  | ok s' => exact ⟨ho, hd⟩
  | err s' => exact ⟨ho, hd⟩

/-! ## Where the working area is -/

/-- The working area's words up to `dataEnd`: inside the address space, apart from the context's,
the decoded proof's and, from `Transcript.workWords` on, the transcript's. -/
structure Env4 (env : Env) : Prop where
  fit : Fits env.work dataEnd
  notFoot : ∀ k, Transcript.workWords ≤ k → k < dataEnd → ¬ Foot env (wd env.work k)
  ctxNe : ∀ k j, k < dataEnd → j < ctxEnd → wd env.work k ≠ wd env.ctx j
  decNe : ∀ k j, k < dataEnd → j < decodedWords env.L → wd env.work k ≠ wd env.dec j

theorem Env4.of {env : Env} {inp : Input} {mem : UInt64 → Option UInt64} {t : TState} {s : QState}
    (hin : Inputs env inp mem) (hr : CodeRel env t s) : Env4 env := by
  have hd := dataEnd_le inp.bytecode.size
  have hfit : Fits env.work dataEnd := by have := hin.fitWork; unfold Fits at *; omega
  refine ⟨hfit, fun k h1 h2 ↦ hin.not_foot_work h1 (by omega), fun k j hk hj ↦
    (hin.ctx_ne_work hj (by omega)).symm, fun k j hk hj ↦ ?_⟩
  exact (wd_ne_of_disj hr.layout.fitDec hin.fitWork hin.disjDec hj (by omega)).symm

theorem dataEnd_lt : dataEnd < 2 ^ 61 := by rw [dataEnd_val]; decide

/-! ## Regions -/

/-- Regions inside the words phase 4 may write: after the transcript's, before `dataEnd`. -/
def Mine (ws : List Region) : Prop := ∀ r ∈ ws, Transcript.workWords ≤ r.off ∧ r.stop ≤ dataEnd

instance (ws : List Region) : Decidable (Mine ws) := inferInstanceAs (Decidable (∀ r ∈ ws, _))

/-- `r` inside `q`. -/
def _root_.NativeVm.Code.Region.Sub (r q : Region) : Prop := q.off ≤ r.off ∧ r.stop ≤ q.stop

instance (r q : Region) : Decidable (r.Sub q) := inferInstanceAs (Decidable (_ ∧ _))

theorem _root_.NativeVm.Code.Region.Sub.inn {r q : Region} (h : r.Sub q) {w a : UInt64}
    (ha : r.In w a) : q.In w a := by
  obtain ⟨k, hk, rfl⟩ := ha
  refine ⟨r.off - q.off + k, ?_, ?_⟩
  · unfold Region.Sub Region.stop at h; omega
  · congr 1; unfold Region.Sub at h; omega

/-- A word of `r`, its offset in range. -/
theorem _root_.NativeVm.Code.Region.in_wd {r : Region} {w : UInt64} {k : Nat} (h1 : r.off ≤ k)
    (h2 : k < r.stop) :
    r.In w (wd w k) := ⟨k - r.off, by unfold Region.stop at h2; omega, by congr 1; omega⟩

/-- A word of the working area outside `r`. -/
theorem _root_.NativeVm.Code.Region.not_in_wd {r : Region} {env : Env} {k : Nat} (hk : k < dataEnd)
    (hr : r.stop ≤ dataEnd) (h : k < r.off ∨ r.stop ≤ k) : ¬ r.In env.work (wd env.work k) := by
  rintro ⟨j, hj, e⟩
  have hl := dataEnd_lt
  rw [wd_inj (by omega) (by unfold Region.stop at hr; omega)] at e
  unfold Region.stop at h; omega

/-! ## Frames -/

variable {env : Env}

/-- **A frame**: `rdi`, the registers outside `rs` and the words kept, and every word outside the
transcript's and the regions `ws`. -/
structure Fr (env : Env) (ws : List Region) (rs : List Reg64) (s s' : QState) : Prop where
  rdi : s'.reg .rdi = s.reg .rdi
  regs : RegsFrame rs s s'
  dom : DomEq s s'
  mem : ∀ a, ¬ Foot env a → (∀ r ∈ ws, ¬ r.In env.work a) → s'.mem a = s.mem a

/-- `X` survives a frame of `ws` and `rs`. -/
def Stab (env : Env) (ws : List Region) (rs : List Reg64) (X : QState → Prop) : Prop :=
  ∀ s s', X s → Fr env ws rs s s' → X s'

variable {ws ws' : List Region} {rs rs' : List Reg64}

theorem Fr.refl (ws : List Region) (rs : List Reg64) (s : QState) : Fr env ws rs s s :=
  ⟨rfl, fun _ _ ↦ rfl, DomEq.refl s, fun _ _ _ ↦ rfl⟩

theorem Fr.trans {s₁ s₂ s₃ : QState} (h : Fr env ws rs s₁ s₂) (h' : Fr env ws rs s₂ s₃) :
    Fr env ws rs s₁ s₃ :=
  ⟨h'.rdi.trans h.rdi, fun r hr ↦ (h'.regs r hr).trans (h.regs r hr), h.dom.trans h'.dom,
    fun a hf hr ↦ (h'.mem a hf hr).trans (h.mem a hf hr)⟩

/-- A frame of fewer regions, each inside one of the others, and fewer registers. -/
theorem Fr.sub {s s' : QState} (h : Fr env ws rs s s') (hs : ∀ r ∈ ws, ∃ q ∈ ws', r.Sub q)
    (hr : ∀ r ∈ rs, r ∈ rs') : Fr env ws' rs' s s' :=
  ⟨h.rdi, fun r hr' ↦ h.regs r fun hm ↦ hr' (hr r hm), h.dom, fun a hf hr' ↦ h.mem a hf fun r hm hin ↦ by
    obtain ⟨q, hq, hsub⟩ := hs r hm
    exact hr' q hq (hsub.inn hin)⟩

theorem Fr.ofKeeps {s s' : QState} (hk : Keeps clobbers (Foot env) s s') (hd : DomEq s s')
    (hr : ∀ r ∈ clobbers, r ∈ rs) : Fr env ws rs s s' :=
  ⟨hk.rdi, fun r hr' ↦ hk.regs r fun hm ↦ hr' (hr r hm), hd, fun a hf _ ↦ hk.mem a hf⟩

theorem Stab.and {X Y : QState → Prop} (hX : Stab env ws rs X) (hY : Stab env ws rs Y) :
    Stab env ws rs fun s ↦ X s ∧ Y s :=
  fun s s' h hf ↦ ⟨hX s s' h.1 hf, hY s s' h.2 hf⟩

theorem Stab.mono {X : QState → Prop} (h : Stab env ws' rs' X) (hs : ∀ r ∈ ws, ∃ q ∈ ws', r.Sub q)
    (hr : ∀ r ∈ rs, r ∈ rs') : Stab env ws rs X :=
  fun s s' hx hf ↦ h s s' hx (hf.sub hs hr)

theorem Stab.true (ws : List Region) (rs : List Reg64) : Stab env ws rs fun _ ↦ True :=
  fun _ _ _ _ ↦ trivial

/-- A register outside the frame's keeps its value. -/
theorem Stab.reg {r : Reg64} (hr : r ∉ rs) (v : UInt64) : Stab env ws rs fun s ↦ s.reg r = v :=
  fun _ _ h hf ↦ (hf.regs r hr).trans h

/-- **`Kept` from the phase's start survives a frame of regions inside the kept ones.** -/
theorem Stab.kept {ks : List Region} {s0 : QState} (hs : ∀ r ∈ ws, ∃ q ∈ ks, r.Sub q) :
    Stab env ws rs (Kept env ks s0) := fun s s' ⟨hrdi, hm⟩ hf ↦
  ⟨hf.rdi.trans hrdi, fun a hfa hra ↦ by
    rw [(hf.sub (rs' := rs) hs fun _ h ↦ h).mem a hfa hra]
    exact hm a hfa hra⟩

/-- Every word phase 4 may write exists. -/
def WS (env : Env) (s : QState) : Prop :=
  ∀ k, 69 ≤ k → k < 85438 → (s.mem (wd env.work k)).isSome

theorem WS.of {env : Env} {s : QState} (h : ∀ k, Transcript.workWords ≤ k → k < dataEnd →
    (s.mem (wd env.work k)).isSome) : WS env s := fun k h1 h2 ↦
  h k (by rw [tWorkWords_val]; exact h1) (by rw [dataEnd_val]; exact h2)

theorem Stab.wsome (ws : List Region) (rs : List Reg64) : Stab env ws rs (WS env) :=
  fun _ _ h hf k h1 h2 ↦ by rw [hf.dom]; exact h k h1 h2

/-- **A region apart from a frame's is kept.** -/
theorem Fr.same (h4 : Env4 env) {s s' : QState} (hf : Fr env ws rs s s') (hm : Mine ws)
    {q : Region} (hq : Mine [q]) (hap : ∀ r ∈ ws, q.Apart r) :
    Same s.mem s'.mem (q.at env.work) q.size := by
  intro k hk
  have hl := dataEnd_lt
  have hq' := hq q (List.mem_singleton_self _)
  unfold Region.stop at hq'
  rw [Region.at, wd_wd]
  refine hf.mem _ (h4.notFoot _ (by omega) (by omega)) fun r hr ↦ ?_
  have := hm r hr
  have hap' := hap r hr
  unfold Region.Apart Region.stop at hap'
  unfold Region.stop at this
  exact Region.not_in_wd (by omega) (by unfold Region.stop; omega)
    (by unfold Region.stop; omega)

/-- A fact about a region apart from `ws` survives a frame of `ws`. -/
theorem Stab.region (h4 : Env4 env) (hm : Mine ws) {q : Region} (hq : Mine [q])
    (hap : ∀ r ∈ ws, q.Apart r) {P : (UInt64 → Option UInt64) → Prop}
    (hP : ∀ m m', Same m m' (q.at env.work) q.size → P m → P m') :
    Stab env ws rs fun s ↦ P s.mem :=
  fun _ _ h hf ↦ hP _ _ (hf.same h4 hm hq hap) h

/-! ## Writes of phase 4's own code -/

/-- `s'` is `s` but in the regions `ws`, the transcript's words included. -/
def Only (env : Env) (ws : List Region) (s s' : QState) : Prop :=
  ∀ a, (∀ r ∈ ws, ¬ r.In env.work a) → s'.mem a = s.mem a

theorem Only.refl (ws : List Region) (s : QState) : Only env ws s s := fun _ _ ↦ rfl

theorem Only.trans {ws : List Region} {s₁ s₂ s₃ : QState} (h : Only env ws s₁ s₂)
    (h' : Only env ws s₂ s₃) : Only env ws s₁ s₃ := fun a ha ↦ (h' a ha).trans (h a ha)

theorem Only.mono {ws ws' : List Region} {s s' : QState} (h : Only env ws s s')
    (hs : ∀ r ∈ ws, ∃ q ∈ ws', r.Sub q) : Only env ws' s s' := fun a ha ↦
  h a fun r hm hin ↦ by
    obtain ⟨q, hq, hsub⟩ := hs r hm
    exact ha q hq (hsub.inn hin)

theorem Only.setMem {ws : List Region} {s s' : QState} (h : Only env ws s s') {r : Region}
    (hr : r ∈ ws) {k : Nat} (h1 : r.off ≤ k) (h2 : k < r.stop) (v : UInt64) :
    Only env ws s (s'.setMem (wd env.work k) v) := fun a ha ↦ by
  rw [QState.setMem_mem, ite_eq_right]
  · exact h a ha
  · rintro rfl
    exact ha r hr (Region.in_wd h1 h2)

theorem Only.setReg {ws : List Region} {s s' : QState} (h : Only env ws s s') (r : Reg64)
    (v : UInt64) : Only env ws s (s'.setReg r v) := h

theorem Only.fr {s s' : QState} (h : Only env ws s s') (hrdi : s'.reg .rdi = s.reg .rdi)
    (hr : RegsFrame rs s s') (hd : DomEq s s') : Fr env ws rs s s' :=
  ⟨hrdi, hr, hd, fun a _ ha ↦ h a ha⟩

/-- **`CodeRel` survives writes to phase 4's words.** -/
theorem CodeRel.only {t : TState} {ws : List Region} {s s' : QState} (h : CodeRel env t s)
    (h4 : Env4 env) (hm : Mine ws) (ho : Only env ws s s') (hd : DomEq s s')
    (hrdi : s'.reg .rdi = s.reg .rdi) : CodeRel env t s' := by
  obtain ⟨st, hr, hs, hstream, hop⟩ := h
  have hl := dataEnd_lt
  have notMine : ∀ a, (∀ k, Transcript.workWords ≤ k → k < dataEnd → a ≠ wd env.work k) →
      s'.mem a = s.mem a := fun a ha ↦ ho a fun r hr ⟨k, hk, e⟩ ↦ by
    have := hm r hr
    unfold Region.stop at this
    exact ha (r.off + k) (by omega) (by omega) e
  refine ⟨st, hr, hs.congrW (hrdi.trans hs.rdi) hd (fun k hk ↦ notMine _ fun k' h1 h2 e ↦ ?_)
    (fun k hk ↦ notMine _ fun k' h1 h2 e ↦ h4.decNe k' k h2 hk e.symm)
    (fun k hk ↦ notMine _ fun k' h1 h2 e ↦ ?_), hstream, hop⟩
  · refine h4.ctxNe k' k h2 ?_ e.symm
    rw [ctxEnd_val]
    rcases hk with hk | hk
    · rw [scratchW_val] at hk; omega
    · rw [groundW_val] at hk; omega
  · rw [wd_inj (by rw [tWorkWords_val] at hk; omega) (by omega)] at e
    omega

/-! ## Words of the working area -/

theorem mem_setMem_wd {s : QState} {w : UInt64} {j k : Nat} (v : UInt64) (hj : j < 2 ^ 61)
    (hk : k < 2 ^ 61) (h : j ≠ k) : (s.setMem (wd w k) v).mem (wd w j) = s.mem (wd w j) := by
  rw [QState.setMem_mem, ite_eq_right]
  rwa [wd_inj hj hk]

theorem mem_setMem_self {s : QState} {a : UInt64} (v : UInt64) : (s.setMem a v).mem a = some v := by
  rw [QState.setMem_mem, ite_eq_left rfl]

/-- A load of the work area's address from the context. -/
theorem wp_ldW {t : TState} {s : QState} {d : Reg64} {xs : List Stmt} {P E : QState → Prop}
    (h : CodeRel env t s) (k : WP (blk xs) (s.setReg d env.work) P E) :
    WP (blk (I (.load d (cw ctxWork)) :: xs)) s P E :=
  wp_load (eval_cw h.rdi _) h.layout.workPtr k

/-- A load of word `k` of the work area, its address in `r`. -/
theorem wp_ldA {s : QState} {d r : Reg64} {w : UInt64} {j k : Nat} {v : UInt64} {xs : List Stmt}
    {P E : QState → Prop} (hr : s.reg r = wd w j) (hv : s.mem (wd w (j + k)) = some v)
    (h : WP (blk xs) (s.setReg d v) P E) : WP (blk (I (.load d (wa r k)) :: xs)) s P E :=
  wp_load (eval_wd hr k) hv h

/-- A store to word `k` of the work area, its address in `r`. -/
theorem wp_stA {s : QState} {src r : Reg64} {w : UInt64} {j k : Nat} {xs : List Stmt}
    {P E : QState → Prop} (hr : s.reg r = wd w j) (hd : (s.mem (wd w (j + k))).isSome)
    (h : WP (blk xs) (s.setMem (wd w (j + k)) (s.reg src)) P E) :
    WP (blk (I (.store (wa r k) src) :: xs)) s P E :=
  wp_store (eval_wd hr k) hd h

theorem wp_stiA {s : QState} {r : Reg64} {w : UInt64} {j k : Nat} {n : Int64} {xs : List Stmt}
    {P E : QState → Prop} (hr : s.reg r = wd w j) (hd : (s.mem (wd w (j + k))).isSome)
    (h : WP (blk xs) (s.setMem (wd w (j + k)) n.toUInt64) P E) :
    WP (blk (I (.storei (wa r k) n) :: xs)) s P E :=
  wp_storei (eval_wd hr k) hd h

theorem wd_zero' (w : UInt64) : w = wd w 0 := (wd_zero w).symm

/-- The value of an `E` word pair from an `EWAt`. -/
theorem EWAt.lo {mem : UInt64 → Option UInt64} {p : UInt64} {x : EW} (h : EWAt mem p x) :
    mem p = some x.c0 := h.1

theorem EWAt.hi {mem : UInt64 → Option UInt64} {p : UInt64} {x : EW} (h : EWAt mem p x) :
    mem (wd p 1) = some x.c1 := h.2

/-! ## Frames through single instructions -/

theorem Fr.setMem {s s' : QState} (h : Fr env ws rs s s') {r : Region} (hr : r ∈ ws) {k : Nat}
    (h1 : r.off ≤ k) (h2 : k < r.stop) (hd : (s'.mem (wd env.work k)).isSome) (v : UInt64) :
    Fr env ws rs s (s'.setMem (wd env.work k) v) := by
  refine ⟨h.rdi, h.regs, fun a ↦ ?_, fun a hf ha ↦ ?_⟩
  · rw [← h.dom a, QState.setMem_mem]
    split
    · subst a; exact hd.symm
    · rfl
  · rw [QState.setMem_mem, ite_eq_right]
    · exact h.mem a hf ha
    · rintro rfl
      exact ha r hr (Region.in_wd h1 h2)

theorem Fr.setReg {s s' : QState} (h : Fr env ws rs s s') {r : Reg64} (hr : r ∈ rs)
    (hrd : r ≠ .rdi) (v : UInt64) : Fr env ws rs s (s'.setReg r v) :=
  ⟨by rw [QState.setReg_reg, ite_eq_right (Ne.symm hrd)]; exact h.rdi, rf_setReg h.regs hr v,
    h.dom, h.mem⟩

/-- An address `disp` bytes from a word of the working area. -/
theorem eval_atd {s : QState} {r : Reg64} {w : UInt64} {j k : Nat} {d : Int64}
    (hr : s.reg r = wd w j) (hd : d.toUInt64 = (8 * k).toUInt64) : (at_ r d).eval s = wd w (j + k) := by
  rw [Transcript.eval_at, hr, hd, wd_add]

/-! ## The transcript's gadgets with frames -/

/-- `read` as a refinement, `R` kept through the gadget's frame. -/
theorem readScalar_fr {R : QState → Prop}
    (hR : ∀ s s', R s → Keeps clobbers (Foot env) s s' → DomEq s s' → R s') :
    Refines (fun t s ↦ CodeRel env t s ∧ R s) readScalar Model.readScalar
      (fun x t' s' ↦ CodeRel env t' s' ∧ R s' ∧ s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1) R :=
  fun _ s ⟨h, hRs⟩ ↦ WP.mono (WP.domEq (readScalarM_spec h))
    (fun _ ⟨⟨x, t', hr, hc, h9, h10, hk⟩, hd⟩ ↦ ⟨x, t', hr, hc, hR s _ hRs hk hd, h9, h10⟩)
    (fun _ ⟨⟨hr, hk⟩, hd⟩ ↦ ⟨hr, hR s _ hRs hk hd⟩)

/-- `sample` as a refinement, `R` kept through the gadget's frame. -/
theorem sampleChallenge_fr {R : QState → Prop}
    (hR : ∀ s s', R s → Keeps clobbers (Foot env) s s' → DomEq s s' → R s') :
    Refines (fun t s ↦ CodeRel env t s ∧ R s) sampleChallenge Model.sampleChallenge
      (fun x t' s' ↦ CodeRel env t' s' ∧ R s' ∧ s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1) R :=
  fun _ s ⟨h, hRs⟩ ↦ WP.mono (WP.domEq (sampleChallengeM_spec h))
    (fun _ ⟨⟨x, t', hr, hc, h9, h10, hk⟩, hd⟩ ↦ ⟨x, t', hr, hc, hR s _ hRs hk hd, h9, h10⟩)
    (fun _ ⟨h, _⟩ ↦ h.elim)

/-- A `Stab` predicate of a frame with the gadgets' registers survives a gadget. -/
theorem Stab.keeps {X : QState → Prop} (hX : Stab env ws rs X) (hr : ∀ r ∈ clobbers, r ∈ rs) :
    ∀ s s', X s → Keeps clobbers (Foot env) s s' → DomEq s s' → X s' :=
  fun s s' hx hk hd ↦ hX s s' hx (Fr.ofKeeps hk hd hr)

/-! ## What a run's syntax keeps -/

/-- A run keeps which words exist, and every register its statement does not write. -/
theorem WP.frame {c : Stmt} {s : QState} {P E : QState → Prop} (h : WP c s P E) :
    WP c s (fun s' ↦ P s' ∧ DomEq s s' ∧ ∀ r, c.writes r = false → s'.reg r = s.reg r)
      (fun s' ↦ E s' ∧ DomEq s s' ∧ ∀ r, c.writes r = false → s'.reg r = s.reg r) := by
  obtain ⟨o, hx, ho⟩ := h
  refine ⟨o, hx, ?_⟩
  have hd := Exec.mem_isSome hx
  have hr := fun r (h : c.writes r = false) ↦ Exec.reg_frame hx h
  cases o with
  | ok s' => exact ⟨ho, hd, hr⟩
  | err s' => exact ⟨ho, hd, hr⟩

theorem DomEq.setMem {s : QState} {a : UInt64} (h : (s.mem a).isSome) (v : UInt64) :
    DomEq s (s.setMem a v) := fun b ↦ by
  rw [QState.setMem_mem]
  split
  · subst b; exact h.symm
  · rfl

theorem DomEq.setReg (s : QState) (r : Reg64) (v : UInt64) : DomEq s (s.setReg r v) := fun _ ↦ rfl

/-- An address `0` bytes from a word. -/
theorem eval_at0 {s : QState} {r : Reg64} {w : UInt64} {j : Nat} (hr : s.reg r = wd w j) :
    (at_ r 0).eval s = wd w j := by
  rw [Transcript.eval_at, hr, show (0 : Int64).toUInt64 = 0 from rfl, UInt64.add_zero]

/-- An address `8` bytes from a word. -/
theorem eval_at8 {s : QState} {r : Reg64} {w : UInt64} {j : Nat} (hr : s.reg r = wd w j) :
    (at_ r 8).eval s = wd w (j + 1) :=
  eval_atd hr rfl

/-- `16` bytes on. -/
theorem wd_add16 (w : UInt64) (j : Nat) : wd w j + (16 : Int64).toUInt64 = wd w (j + 2) :=
  wd_add w j 2

theorem natSub_toUInt64 {n k : Nat} (h : k < n) :
    (n - k).toUInt64 - (1 : Int64).toUInt64 = (n - (k + 1)).toUInt64 := by
  rw [show n - k = (n - (k + 1)) + 1 by omega]
  exact Field.toUInt64_succ_sub _

/-- A count word's test: nonzero exactly while `k < n`. -/
theorem test_count {s : QState} {r : Reg64} {n k : Nat} (h : s.reg r = (n - k).toUInt64)
    (hn : n < 2 ^ 64) : (Cond.test false r (.reg r)).eval s = true ↔ k < n := by
  simp only [Cond.eval, Rhs.eval, h, UInt64.and_self]
  constructor
  · intro e
    by_contra hk
    rw [show n - k = 0 by omega] at e
    exact absurd e (by decide)
  · intro hk
    have : (n - k).toUInt64 ≠ 0 := fun e ↦ by
      have := Field.toUInt64_eq_zero (by omega) e
      omega
    simpa using this

end NativeVm.Code.P4
