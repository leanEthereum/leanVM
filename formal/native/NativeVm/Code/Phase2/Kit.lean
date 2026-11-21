module

public import NativeVm.Code.Gadgets
public import NativeVm.Code.Contracts

/-!
# A phase's frame, through gadgets and stores

What phases 2 and 5 share. A phase run from `s0` keeps the words outside the transcript's and its
regions `rs` (`Kept`) and which words exist; with a fact `X` of the state, that is `Fr env rs s0 X`.
`X` survives a transcript gadget when it is `Stable` (it reads registers outside `clobbers` and
words outside the transcript's), so each gadget refines its model operation from `Fr` to `Fr`
(`readScalar_fr`, `sampleChallenge_fr`, `grind_fr`, `commit_fr`), its failure keeping `Kept`. A
store into one of `rs`'s regions, or a register write other than `rdi`, keeps `Base`.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {rs : List Region} {s0 s s' : QState} {X : QState → Prop}

/-! ## The frame -/

/-- What a phase run from `s0` keeps: `Kept`, and which words exist. -/
def Base (env : Env) (rs : List Region) (s0 s : QState) : Prop :=
  Kept env rs s0 s ∧ ∀ a, (s.mem a).isSome = (s0.mem a).isSome

/-- `Base`, and the fact `X`. -/
def Fr (env : Env) (rs : List Region) (s0 : QState) (X : QState → Prop) (s : QState) : Prop :=
  Base env rs s0 s ∧ X s

/-- `X` survives a transcript gadget. -/
def Stable (env : Env) (X : QState → Prop) : Prop :=
  ∀ s s', X s → Keeps clobbers (Foot env) s s' → X s'

theorem Base.start (h : s0.reg .rdi = env.ctx) : Base env rs s0 s0 :=
  ⟨⟨h, fun _ _ _ ↦ rfl⟩, fun _ ↦ rfl⟩

theorem Kept.keeps (h : Kept env rs s0 s) (hk : Keeps clobbers (Foot env) s s') :
    Kept env rs s0 s' :=
  ⟨hk.rdi.trans h.1, fun a hf hr ↦ (hk.mem a hf).trans (h.2 a hf hr)⟩

theorem Base.keeps (h : Base env rs s0 s) (hk : Keeps clobbers (Foot env) s s')
    (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome) : Base env rs s0 s' :=
  ⟨h.1.keeps hk, fun a ↦ (hd a).trans (h.2 a)⟩

theorem Base.setReg (h : Base env rs s0 s) {d : Reg64} (hd : d ≠ .rdi) (v : UInt64) :
    Base env rs s0 (s.setReg d v) :=
  ⟨⟨by rw [QState.setReg_reg, ite_of_not (Ne.symm hd)]; exact h.1.1,
    fun a hf hr ↦ by rw [QState.setReg_mem]; exact h.1.2 a hf hr⟩, h.2⟩

/-- A store into word `j` of the region `q` of `rs`, a word that exists. -/
theorem Base.setMem (h : Base env rs s0 s) {q : Region} (hq : q ∈ rs) {j : Nat} (hj : j < q.size)
    {a : UInt64} (ha : a = wd env.work (q.off + j)) (hs : (s.mem a).isSome) (v : UInt64) :
    Base env rs s0 (s.setMem a v) :=
  ⟨⟨by rw [QState.setMem_reg]; exact h.1.1, fun a' hf hr ↦ by
      rw [QState.setMem_mem, ite_of_not (fun e ↦ hr q hq ⟨j, hj, e.trans ha⟩)]
      exact h.1.2 a' hf hr⟩,
    fun a' ↦ (isSome_setMem s v hs a').trans (h.2 a')⟩

/-- A store keeps the words it does not write. -/
theorem same_setMem {p a v : UInt64} {n : Nat} (h : ∀ k < n, wd p k ≠ a) :
    Same s.mem (s.setMem a v).mem p n := fun k hk ↦ by
  rw [QState.setMem_mem, ite_of_not (h k hk)]

/-! ## The regions' words -/

theorem region_lt {q : Region} (hq : q ∈ regions) {j : Nat} (hj : j < q.size) :
    q.off + j < workWords inp.bytecode.size := by
  have := stop_le_of_mem hq inp.bytecode.size
  unfold Region.stop at this
  omega

/-- A word of a region exists. -/
theorem Inputs.region_some (h : Inputs env inp s0.mem) (hb : Base env rs s0 s) {q : Region}
    (hq : q ∈ regions) {j : Nat} (hj : j < q.size) : (s.mem (wd env.work (q.off + j))).isSome := by
  rw [hb.2]
  exact h.workSome _ (region_lt hq hj)

/-- A word of a region is not the transcript's. -/
theorem Inputs.not_foot_region {mem : UInt64 → Option UInt64} (h : Inputs env inp mem) {q : Region}
    (hq : q ∈ regions) {j : Nat} (hj : j < q.size) : ¬ Foot env (wd env.work (q.off + j)) :=
  h.not_foot_work (le_trans (regions_bounds q hq).1 (Nat.le_add_right _ _)) (region_lt hq hj)

/-- A gadget keeps the regions' words. -/
theorem Inputs.keeps_region {mem : UInt64 → Option UInt64} (h : Inputs env inp mem)
    (hk : Keeps clobbers (Foot env) s s') {q : Region} (hq : q ∈ regions) {j : Nat}
    (hj : j < q.size) : s'.mem (wd env.work (q.off + j)) = s.mem (wd env.work (q.off + j)) :=
  hk.mem _ (h.not_foot_region hq hj)

/-- A gadget keeps a region. -/
theorem Inputs.keeps_same {mem : UInt64 → Option UInt64} (h : Inputs env inp mem)
    (hk : Keeps clobbers (Foot env) s s') {q : Region} (hq : q ∈ regions) :
    Same s.mem s'.mem (q.at env.work) q.size := fun j hj ↦ by
  rw [Region.at, wd_wd]
  exact h.keeps_region hk hq hj

theorem _root_.NativeVm.Transcript.Keeps.reg (hk : Keeps clobbers (Foot env) s s') {r : Reg64}
    (hr : r ∉ clobbers) :
    s'.reg r = s.reg r :=
  hk.regs r hr

/-- A region apart from `rs`, from the start. -/
theorem Base.same (h : Base env rs s0 s) (hin : Inputs env inp s0.mem) (hrs : ∀ r ∈ rs, r ∈ regions)
    {q : Region} (hq : q ∈ regions) (hap : ∀ r ∈ rs, q.Apart r) :
    Same s0.mem s.mem (q.at env.work) q.size :=
  h.1.same hin (fun r hr ↦ stop_le_of_mem (hrs r hr) _) hq hap

theorem layoutR_off : layoutR.off = 69 := (rfl)
theorem layoutR_size : layoutR.size = 490 := by decide

/-! ## Addresses -/

theorem eval_work {r : Reg64} {w : UInt64} (h : s.reg r = w) (k : Nat) :
    (at_ r (wdisp k)).eval s = wd w k := by
  rw [eval_at, h, wdisp_toUInt64]
  rfl

theorem toUInt64_sub1 {a : Nat} (h : 1 ≤ a) : a.toUInt64 - 1 = (a - 1).toUInt64 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← toUInt64_add]
  simp

theorem eval_region {r : Reg64} {w : UInt64} {o j : Nat} (h : s.reg r = wd w (o + j)) (k : Nat) :
    (at_ r (wdisp k)).eval s = wd w (o + (j + k)) := by
  rw [eval_work h, wd_wd, Nat.add_assoc]

theorem wd_ne_work {w : UInt64} {a b : Nat} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (h : a ≠ b) :
    wd w a ≠ wd w b := fun e ↦ h ((wd_inj ha hb).mp e)

/-! ## The model's state through the phase's writes -/

theorem CodeRel.of_mem {t : TState} (h : CodeRel env t s) (hm : s'.mem = s.mem)
    (hrdi : s'.reg .rdi = s.reg .rdi) : CodeRel env t s' := by
  obtain ⟨st, h1, h2, h3, h4⟩ := h
  exact ⟨st, h1, h2.of_mem hm hrdi, h3, h4⟩

theorem Base.of_mem (h : Base env rs s0 s) (hm : s'.mem = s.mem)
    (hrdi : s'.reg .rdi = s.reg .rdi) : Base env rs s0 s' :=
  ⟨⟨hrdi.trans h.1.1, fun a hf hr ↦ by rw [hm]; exact h.1.2 a hf hr⟩, fun a ↦ by rw [hm]; exact h.2 a⟩

theorem CodeRel.setReg {t : TState} (h : CodeRel env t s) {r : Reg64} (hr : r ≠ .rdi)
    (v : UInt64) : CodeRel env t (s.setReg r v) := by
  obtain ⟨st, h1, h2, h3, h4⟩ := h
  exact ⟨st, h1, h2.setReg hr v, h3, h4⟩

/-- A store into a region's word keeps the model's state. -/
theorem CodeRel.setMem {t : TState} (h : CodeRel env t s) (hin : Inputs env inp s0.mem)
    {q : Region} (hq : q ∈ regions) {j : Nat} (hj : j < q.size) {a : UInt64}
    (ha : a = wd env.work (q.off + j)) (hs : (s.mem a).isSome) (v : UInt64) :
    CodeRel env t (s.setMem a v) := by
  obtain ⟨st, h1, h2, h3, h4⟩ := h
  subst ha
  have hb := (regions_bounds q hq).1
  have hlt := region_lt (inp := inp) hq hj
  have hww := workWords_lt hin
  refine ⟨st, h1, h2.congrW (by rw [QState.setMem_reg]; exact h2.rdi) (isSome_setMem s v hs)
    (fun k hk ↦ ?_) (fun k hk ↦ ?_) (fun k hk ↦ ?_), h3, h4⟩
  · rw [QState.setMem_mem, ite_of_not (hin.ctx_ne_work (by lay_omega) hlt)]
  · rw [QState.setMem_mem, ite_of_not (wd_ne_of_disj h2.layout.fitDec hin.fitWork hin.disjDec hk hlt)]
  · rw [QState.setMem_mem, ite_of_not (wd_ne_work (by omega) (by omega) (by omega))]

/-! ## Steps that keep the model's state and the frame -/

section Steps

variable {t : TState} {xs : List Stmt} {P E : QState → Prop}

/-- A store into word `j` of the region `q` of `rs`. -/
theorem wp_store_rel {q : Region} (hq : q ∈ rs) (hqr : q ∈ regions) (hin : Inputs env inp s0.mem)
    {j : Nat} (hj : j < q.size) {a : Addr} {r : Reg64} (ha : a.eval s = wd env.work (q.off + j))
    (hc : CodeRel env t s) (hb : Base env rs s0 s)
    (h : CodeRel env t (s.setMem (wd env.work (q.off + j)) (s.reg r)) →
      Base env rs s0 (s.setMem (wd env.work (q.off + j)) (s.reg r)) →
      WP (blk xs) (s.setMem (wd env.work (q.off + j)) (s.reg r)) P E) :
    WP (blk (I (.store a r) :: xs)) s P E := by
  have hs := hin.region_some hb hqr hj
  exact wp_store ha hs (h (hc.setMem hin hqr hj rfl hs _) (hb.setMem hq hj rfl hs _))

/-- A store of a constant into word `j` of the region `q` of `rs`. -/
theorem wp_storei_rel {q : Region} (hq : q ∈ rs) (hqr : q ∈ regions) (hin : Inputs env inp s0.mem)
    {j : Nat} (hj : j < q.size) {a : Addr} {k : Int64} (ha : a.eval s = wd env.work (q.off + j))
    (hc : CodeRel env t s) (hb : Base env rs s0 s)
    (h : CodeRel env t (s.setMem (wd env.work (q.off + j)) k.toUInt64) →
      Base env rs s0 (s.setMem (wd env.work (q.off + j)) k.toUInt64) →
      WP (blk xs) (s.setMem (wd env.work (q.off + j)) k.toUInt64) P E) :
    WP (blk (I (.storei a k) :: xs)) s P E := by
  have hs := hin.region_some hb hqr hj
  exact wp_storei ha hs (h (hc.setMem hin hqr hj rfl hs _) (hb.setMem hq hj rfl hs _))

/-- A register write other than `rdi`. -/
theorem wp_reg_rel {i : QInstr} {d : Reg64} {v : UInt64} (hs : i.step s = some (s.setReg d v))
    (hd : d ≠ .rdi) (hc : CodeRel env t s) (hb : Base env rs s0 s)
    (h : CodeRel env t (s.setReg d v) → Base env rs s0 (s.setReg d v) →
      WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I i :: xs)) s P E :=
  wp_reg hs (h (hc.setReg hd v) (hb.setReg hd v))

/-- A load into a register other than `rdi`. -/
theorem wp_load_rel {d : Reg64} {a : Addr} {x v : UInt64} (ha : a.eval s = x)
    (hv : s.mem x = some v) (hd : d ≠ .rdi) (hc : CodeRel env t s) (hb : Base env rs s0 s)
    (h : CodeRel env t (s.setReg d v) → Base env rs s0 (s.setReg d v) →
      WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d a) :: xs)) s P E :=
  wp_load ha hv (h (hc.setReg hd v) (hb.setReg hd v))

end Steps

/-! ## The gadgets in the frame -/

theorem readScalar_fr (hX : Stable env X) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env rs s0 X s) Transcript.readScalar Model.readScalar
      (fun x t' s' ↦ CodeRel env t' s' ∧ Fr env rs s0 X s' ∧ s'.reg .r9 = x.c0 ∧
        s'.reg .r10 = x.c1)
      (Kept env rs s0) :=
  fun _ _ ⟨h, hf⟩ ↦ WP.mono (Transcript.WP.frame (readScalarM_spec h))
    (fun _ ⟨⟨x, t', hr, hc, h9, h10, hk⟩, hd, _⟩ ↦
      ⟨x, t', hr, hc, ⟨hf.1.keeps hk hd, hX _ _ hf.2 hk⟩, h9, h10⟩)
    (fun _ ⟨⟨hr, hk⟩, _⟩ ↦ ⟨hr, hf.1.1.keeps hk⟩)

theorem sampleChallenge_fr (hX : Stable env X) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env rs s0 X s) Transcript.sampleChallenge
      Model.sampleChallenge
      (fun x t' s' ↦ CodeRel env t' s' ∧ Fr env rs s0 X s' ∧ s'.reg .r9 = x.c0 ∧
        s'.reg .r10 = x.c1)
      (Kept env rs s0) :=
  fun _ _ ⟨h, hf⟩ ↦ WP.mono (Transcript.WP.frame (sampleChallengeM_spec h))
    (fun _ ⟨⟨x, t', hr, hc, h9, h10, hk⟩, hd, _⟩ ↦
      ⟨x, t', hr, hc, ⟨hf.1.keeps hk hd, hX _ _ hf.2 hk⟩, h9, h10⟩)
    (fun _ ⟨h, _⟩ ↦ h.elim)

theorem grind_fr {bits : Nat} (hb0 : bits ≠ 0) (hb : bits < 2 ^ 64) (hX : Stable env X) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env rs s0 X s ∧ s.reg .rsi = bits.toUInt64)
      Transcript.grind (Model.grind bits)
      (fun _ t' s' ↦ CodeRel env t' s' ∧ Fr env rs s0 X s') (Kept env rs s0) :=
  fun _ _ ⟨h, hf, hrsi⟩ ↦ WP.mono (Transcript.WP.frame (grindM_spec h hb0 hb hrsi))
    (fun _ ⟨⟨t', hr, hc, hk⟩, hd, _⟩ ↦ ⟨(), t', hr, hc, hf.1.keeps hk hd, hX _ _ hf.2 hk⟩)
    (fun _ ⟨⟨hr, hk⟩, _⟩ ↦ ⟨hr, hf.1.1.keeps hk⟩)

theorem commit_fr {height width : Nat} (hh : height < 2 ^ 64) (hw : width < 2 ^ 64)
    (hX : Stable env X) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env rs s0 X s ∧ t.roots.size < maxRoots ∧
        s.reg .rsi = height.toUInt64 ∧ s.reg .rbx = width.toUInt64)
      Transcript.commit (Model.readCommitment height width)
      (fun _ t' s' ↦ CodeRel env t' s' ∧ Fr env rs s0 X s') (Kept env rs s0) :=
  fun _ _ ⟨h, hf, hroom, hrsi, hrbx⟩ ↦
    WP.mono (Transcript.WP.frame (readCommitmentM_spec h hroom hh hw hrsi hrbx))
      (fun _ ⟨⟨t', hr, hc, hk⟩, hd, _⟩ ↦ ⟨(), t', hr, hc, hf.1.keeps hk hd, hX _ _ hf.2 hk⟩)
      (fun _ ⟨⟨hr, hk⟩, _⟩ ↦ ⟨hr, hf.1.1.keeps hk⟩)

theorem stable_true : Stable env fun _ ↦ True := fun _ _ _ _ ↦ trivial

/-- **A phase's contract from a refinement** from its start state. -/
theorem runs_of_refines {α : Type} {c : Stmt} {m : VM α} {t : TState} {Out : α → QState → Prop}
    (h : Refines (fun t' s' ↦ t' = t ∧ s' = s0) c m
      (fun x t' s' ↦ CodeRel env t' s' ∧ Out x s' ∧ Kept env rs s0 s') (Kept env rs s0)) :
    Runs env c m t s0 rs Out :=
  h t s0 ⟨rfl, rfl⟩

end NativeVm.Code
