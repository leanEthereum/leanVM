module

public import NativeVm.Code.Phase7.Base
public import NativeVm.Code.Roots

/-!
# Phase 7's WHIR part: the invariant every piece keeps

`Par`: what the WHIR part is about (the environment, the inputs, the state it starts in, the stack's
log-size, the ladder, the basis). `Base p t s`: `s` holds the model's `t` (`CodeRel`), keeps the
frame from the start (`Fr`), and the inputs. The transcript gadgets keep it, with any fact `R` of
the machine state that a gadget's frame keeps (`GOk`): `readScalar_b`, `sample_b`, `grind_b`,
`commit_b`. A piece writing only the area keeps it (`Base.frM`).

The scratch words the pieces share are fixed here (`cIdx`, ... , offsets in the working area).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Fits Disj Env Foot cw wdisp ctxWork ctxEnd Keeps clobbers wd_inj)

/-! ## The scratch words -/

/-- Scratch word `k`, in the working area. -/
abbrev sc (k : Nat) : Nat := scratchR.off + k

theorem scratch_off : scratchR.off = 52670 := by decide
theorem whir_off : whirR.off = 28386 := by decide
theorem basis_off : basisR.off = 28061 := by decide
theorem rounds_off : roundsR.off = 36030 := by decide
theorem queries_off : queriesR.off = 36055 := by decide
theorem rows_off : rowsR.off = 36286 := by decide
theorem ring_off : ringR.off = 27931 := by decide
theorem keccak_off : keccakR.off = 27730 := by decide
theorem claims_off : claimsR.off = 15569 := by decide
theorem ood_off : oodR.off = 559 := by decide
theorem layout_off : layoutR.off = 69 := by decide

/-- The level's index. -/
abbrev cIdx : Nat := sc 0
/-- The ladder's length. -/
abbrev cN : Nat := sc 1
/-- The stack's log-size. -/
abbrev cLogN : Nat := sc 2
/-- The variables left after the level's folds. -/
abbrev cMu : Nat := sc 3
/-- The queries' depth. -/
abbrev cDepth : Nat := sc 4
/-- Loop counters. -/
abbrev cI : Nat := sc 5
abbrev cJ : Nat := sc 6
abbrev cK : Nat := sc 7
/-- The ladder (`LevelsAt`, `levelsWords` words). -/
abbrev levO : Nat := sc 8
/-- The level's fold rounds, rate exponent and queries, the next level's fold and rate exponent. -/
abbrev cFold : Nat := sc 27
abbrev cRate : Nat := sc 28
abbrev cQ : Nat := sc 29
abbrev cNFold : Nat := sc 30
abbrev cNRate : Nat := sc 31
/-- `E` temporaries, two words each (`tmpO + 2 j`, `j < 16`). -/
abbrev tmpO : Nat := sc 32
/-- The high part or the folded polynomial (`≤ 64` elements). -/
abbrev hiO : Nat := sc 64
/-- The subspace table (`≤ 31` entries, two words each). -/
abbrev tabO : Nat := sc 192
/-- The subspace table's layer scratch (`≤ 30` words). -/
abbrev layO : Nat := sc 256
/-- A query's subspace values (`≤ 64` words). -/
abbrev whatO : Nat := sc 320
/-- The novel basis buffer (`64` words). -/
abbrev novO : Nat := sc 384
/-- The fold buffer (`256` words). -/
abbrev foldO : Nat := sc 448
/-- The induced weight's scratch (`256` words). -/
abbrev indO : Nat := sc 704
/-- The final point, the `α`s then the sumcheck's challenges (`≤ 32` elements). -/
abbrev ptO : Nat := sc 960
/-- The basis's point, rotated (`≤ 32` elements). -/
abbrev xO : Nat := sc 1024
/-- The ring weight's buffer (`≤ 128` words). -/
abbrev ringO : Nat := sc 1088
/-- The multilinear evaluation's work area (`≤ 64` words). -/
abbrev mleO : Nat := sc 1216
/-- A stack point (`≤ 64` words). -/
abbrev spO : Nat := sc 1280

/-- Glued claim `g`'s first word in the working area. -/
abbrev gslot (g : Nat) : Nat := whirR.off + whirGluedOff + 1 + gluedWords * g

/-! ## The invariant -/

/-- What the WHIR part is about. -/
structure Par where
  env : Env
  inp : Input
  /-- The state the WHIR part starts in. -/
  s1 : QState
  logN : Nat
  L : List Whir.Level
  basis : BasisW

/-- **The invariant**: the model's state held, the frame from the start kept, the inputs. -/
structure Base (p : Par) (t : TState) (s : QState) : Prop where
  rel : CodeRel p.env t s
  fr : Fr p.env p.s1 s
  inp : Inputs p.env p.inp s.mem

variable {p : Par} {t t' : TState} {s s' : QState}

theorem Base.rdi (h : Base p t s) : s.reg .rdi = p.env.ctx := h.rel.rdi

theorem Base.workPtr (h : Base p t s) : s.mem (wd p.env.ctx ctxWork) = some p.env.work :=
  h.rel.layout.workPtr

/-- A piece writing only the area keeps the invariant. -/
theorem Base.frM (h : Base p t s) (hf : FrM p.env s s') : Base p t s' := by
  refine ⟨codeRel_frM h.rel h.inp hf, h.fr.trans hf.fr, h.inp.kept (rs := whirRegs) ?_ ?_ hf.dom⟩
  · exact kept_of_fr hf.fr h.rdi
  · intro r hr
    exact stop_le_of_mem (by simp only [whirRegs] at hr; simp only [regions]; simp_all) _

/-- A gadget's frame keeps the invariant, the gadget's relation given. -/
theorem Base.keeps {rs : List Reg64} (h : Base p t s) (hr : CodeRel p.env t' s')
    (hk : Keeps rs (Foot p.env) s s') (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome) :
    Base p t' s' := by
  have hf := Fr.of_keeps hk hd
  refine ⟨hr, h.fr.trans hf, h.inp.kept (rs := whirRegs) (kept_of_fr hf h.rdi) ?_ hd⟩
  intro r hr
  exact stop_le_of_mem (by simp only [whirRegs] at hr; simp only [regions]; simp_all) _

/-- **What a gadget keeps of a fact `R`**: every fact of the area's words and of the registers
outside `clobbers` (with `rdi`). -/
def GOk (env : Env) (inp : Input) (R : QState → Prop) : Prop :=
  ∀ s s', R s → Inputs env inp s.mem → Keeps clobbers (Foot env) s s' →
    (∀ a, (s'.mem a).isSome = (s.mem a).isSome) → R s'

/-- A fact of the area's words. -/
def MineOnly (env : Env) (X : (UInt64 → Option UInt64) → Prop) : Prop :=
  ∀ m m', (∀ a, InMine env a → m' a = m a) → X m → X m'

theorem GOk.of_mine {env : Env} {inp : Input} {X : (UInt64 → Option UInt64) → Prop}
    (hX : MineOnly env X) : GOk env inp fun s ↦ X s.mem :=
  fun _ _ hx hi hk _ ↦ hX _ _ (fun _ ha ↦ keeps_mine hi hk ha) hx

theorem GOk.and {env : Env} {inp : Input} {R R' : QState → Prop} (h : GOk env inp R)
    (h' : GOk env inp R') : GOk env inp fun s ↦ R s ∧ R' s :=
  fun s s' hr hi hk hd ↦ ⟨h s s' hr.1 hi hk hd, h' s s' hr.2 hi hk hd⟩

theorem GOk.reg {env : Env} {inp : Input} {r : Reg64} (hr : r ∉ clobbers) (v : UInt64) :
    GOk env inp fun s ↦ s.reg r = v :=
  fun _ _ h _ hk _ ↦ (hk.regs r hr).trans h

theorem GOk.true {env : Env} {inp : Input} : GOk env inp fun _ ↦ True := fun _ _ _ _ _ _ ↦ trivial

/-- The failure exit's invariant: the frame from the start. -/
abbrev Err (p : Par) : QState → Prop := Fr p.env p.s1

/-! ## The gadgets, keeping the invariant -/

variable {R : QState → Prop}

/-- `read`, keeping the invariant and `R`. -/
theorem readScalar_b (hR : GOk p.env p.inp R) :
    Refines (fun t s ↦ Base p t s ∧ R s) Transcript.readScalar Model.readScalar
      (fun x t s ↦ Base p t s ∧ R s ∧ s.reg .r9 = x.c0 ∧ s.reg .r10 = x.c1) (Err p) := by
  intro t s ⟨hb, hRs⟩
  refine WP.mono (NativeVm.Transcript.WP.frame (readScalarM_spec hb.rel)) ?_ ?_
  · rintro s' ⟨⟨x, t', hr, hc, h9, h10, hk⟩, hd, -⟩
    exact ⟨x, t', hr, hb.keeps hc hk hd, hR s s' hRs hb.inp hk hd, h9, h10⟩
  · rintro s' ⟨⟨hr, hk⟩, hd, -⟩
    exact ⟨hr, hb.fr.trans (Fr.of_keeps hk hd)⟩

/-- `sample`, keeping the invariant and `R`. -/
theorem sample_b (hR : GOk p.env p.inp R) :
    Refines (fun t s ↦ Base p t s ∧ R s) Transcript.sampleChallenge Model.sampleChallenge
      (fun x t s ↦ Base p t s ∧ R s ∧ s.reg .r9 = x.c0 ∧ s.reg .r10 = x.c1) (Err p) := by
  intro t s ⟨hb, hRs⟩
  refine WP.mono (NativeVm.Transcript.WP.frame (sampleChallengeM_spec hb.rel)) ?_ ?_
  · rintro s' ⟨⟨x, t', hr, hc, h9, h10, hk⟩, hd, -⟩
    exact ⟨x, t', hr, hb.keeps hc hk hd, hR s s' hRs hb.inp hk hd, h9, h10⟩
  · rintro s' ⟨h, -⟩
    exact h.elim

/-- `grind bits`, `bits ≠ 0` in `rsi`, keeping the invariant and `R`. -/
theorem grind_b {bits : Nat} (hb0 : bits ≠ 0) (hb64 : bits < 2 ^ 64) (hR : GOk p.env p.inp R) :
    Refines (fun t s ↦ Base p t s ∧ R s ∧ s.reg .rsi = bits.toUInt64) Transcript.grind
      (Model.grind bits) (fun _ t s ↦ Base p t s ∧ R s) (Err p) := by
  intro t s ⟨hb, hRs, hsi⟩
  refine WP.mono (NativeVm.Transcript.WP.frame (grindM_spec hb.rel hb0 hb64 hsi)) ?_ ?_
  · rintro s' ⟨⟨t', hr, hc, hk⟩, hd, -⟩
    exact ⟨(), t', hr, hb.keeps hc hk hd, hR s s' hRs hb.inp hk hd⟩
  · rintro s' ⟨⟨hr, hk⟩, hd, -⟩
    exact ⟨hr, hb.fr.trans (Fr.of_keeps hk hd)⟩

/-- `commit height width`, keeping the invariant and `R`, room for a root. -/
theorem commit_b {height width : Nat} (hh : height < 2 ^ 64) (hw : width < 2 ^ 64)
    (hR : GOk p.env p.inp R) :
    Refines (fun t s ↦ Base p t s ∧ R s ∧ t.roots.size < Transcript.maxRoots ∧
        s.reg .rsi = height.toUInt64 ∧ s.reg .rbx = width.toUInt64) Transcript.commit
      (Model.readCommitment height width) (fun _ t s ↦ Base p t s ∧ R s) (Err p) := by
  intro t s ⟨hb, hRs, hroom, hsi, hbx⟩
  refine WP.mono (NativeVm.Transcript.WP.frame (readCommitmentM_spec hb.rel hroom hh hw hsi hbx))
    ?_ ?_
  · rintro s' ⟨⟨t', hr, hc, hk⟩, hd, -⟩
    exact ⟨(), t', hr, hb.keeps hc hk hd, hR s s' hRs hb.inp hk hd⟩
  · rintro s' ⟨⟨hr, hk⟩, hd, -⟩
    exact ⟨hr, hb.fr.trans (Fr.of_keeps hk hd)⟩

/-! ## Facts of the model's state through a step -/

/-- A refinement keeps a fact of the model's state every run of the step keeps. -/
theorem Refines.addT {α : Type} {P : TState → QState → Prop} {c : Stmt} {m : VM α}
    {Q : α → TState → QState → Prop} {E : QState → Prop} (I I' : TState → Prop)
    (hm : ∀ t x t', m.run t = some (x, t') → I t → I' t') (h : Refines P c m Q E) :
    Refines (fun t s ↦ P t s ∧ I t) c m (fun x t s ↦ Q x t s ∧ I' t) E := by
  intro t s ⟨hp, hi⟩
  exact WP.mono (h t s hp) (fun _ ⟨x, t', hr, hq⟩ ↦ ⟨x, t', hr, hq, hm t x t' hr hi⟩)
    fun _ h ↦ h

/-- A refinement of a step that keeps the roots keeps any fact of them. -/
theorem Refines.keepRoots {α : Type} {P : TState → QState → Prop} {c : Stmt} {m : VM α}
    {Q : α → TState → QState → Prop} {E : QState → Prop} (hm : KeepsRoots m)
    (I : Array RootW → Prop) (h : Refines P c m Q E) :
    Refines (fun t s ↦ P t s ∧ I t.roots) c m (fun x t s ↦ Q x t s ∧ I t.roots) E :=
  Refines.addT (fun t ↦ I t.roots) (fun t ↦ I t.roots)
    (fun t x t' hr hi ↦ by rw [hm.keeps t x t' hr]; exact hi) h

/-! ## Pieces writing the area -/

theorem frM_setReg {env : Env} {s : QState} {r : Reg64} (hr : r ≠ .rdi) (v : UInt64) :
    FrM env s (s.setReg r v) :=
  ⟨by rw [QState.setReg_reg, ite_eq_right (Ne.symm hr)], fun _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem frM_store {env : Env} {s : QState} {k : Nat} (h1 : mineLo ≤ k) (h2 : k < dataEnd)
    (hs : (s.mem (wd env.work k)).isSome) (v : UInt64) : FrM env s (s.setMem (wd env.work k) v) :=
  ⟨rfl, fun a ↦ NativeVm.Transcript.isSome_setMem s v hs a, fun a ha ↦ by
    rw [QState.setMem_mem, ite_eq_right (fun e ↦ ha (by rw [e]; exact inMine_wd h1 h2))]⟩

/-! ## Which area words a piece writes -/

/-- **The area's words outside `W` are as in `m0`** (the words a piece writes, by index in the
working area). -/
def Only (env : Env) (W : Nat → Prop) (m0 m : UInt64 → Option UInt64) : Prop :=
  ∀ k, mineLo ≤ k → k < dataEnd → ¬ W k → m (wd env.work k) = m0 (wd env.work k)

namespace Only

variable {env : Env} {W W' : Nat → Prop} {m0 m1 m2 : UInt64 → Option UInt64}

theorem refl (W : Nat → Prop) (m : UInt64 → Option UInt64) : Only env W m m := fun _ _ _ _ ↦ rfl

theorem mono (h : Only env W m0 m1) (hW : ∀ k, W k → W' k) : Only env W' m0 m1 :=
  fun k h1 h2 hk ↦ h k h1 h2 fun hw ↦ hk (hW k hw)

theorem trans (h₁ : Only env W m0 m1) (h₂ : Only env W' m1 m2) :
    Only env (fun k ↦ W k ∨ W' k) m0 m2 :=
  fun k h1 h2 hk ↦ (h₂ k h1 h2 fun h ↦ hk (.inr h)).trans (h₁ k h1 h2 fun h ↦ hk (.inl h))

/-- A run of words outside `W` is as it was. -/
theorem same (h : Only env W m0 m1) {o n : Nat} (hlo : mineLo ≤ o) (hhi : o + n ≤ dataEnd)
    (hW : ∀ j < n, ¬ W (o + j)) : Same m0 m1 (wd env.work o) n := fun j hj ↦ by
  rw [wd_wd]
  exact h (o + j) (by omega) (by omega) (hW j hj)

/-- A piece writing no area word. -/
theorem of_mine (h : ∀ a, InMine env a → m1 a = m0 a) : Only env W m0 m1 :=
  fun k h1 h2 _ ↦ h _ ⟨k, h1, h2, rfl⟩

/-- `Only` through a store to an area word in `W`. -/
theorem store (h : Only env W m0 m1) {k : Nat} (hk : W k) (hk' : k < 2 ^ 61) (v : UInt64) :
    Only env W m0 (Function.update m1 (wd env.work k) (some v)) := fun j h1 h2 hj ↦ by
  rw [Function.update_of_ne]
  · exact h j h1 h2 hj
  · intro e
    rw [dataEnd_val] at h2
    exact hj ((wd_inj (by omega) hk').mp e ▸ hk)

end Only

end NativeVm.Code.P7
