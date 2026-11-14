module

public import LeanVM.Guest.Mode.InvStep

/-!
# The stack after a step

What each step does to the stack (`StackAt`): one in the frame (a fall-through, a forward or table
jump, `stack_move`) moves the top activation's offset; a return (`ret_stack`) pops it, the caller's
walk going on (`Resume`) from what the callee guarantees, a loop's runs rebuilt down its iterations
(`ret_runs`, `Chain.runs`); a loop's tail call (`tail_stack`) adds an iteration; a call
(`call_stack`) pushes the callee's activation, the caller suspended (`resume_of_call`); `main`'s
halting jump ends the run (`halt_of`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

theorem RetHolds.mono {s s' : St} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) {G : Sig}
    (h : RetHolds s G) : RetHolds s' G := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun o ho ↦ hfp ▸ written_mono hle (h1 o ho), fun k hk ↦ (h2 k hk).mono hle hfp,
    fun r hr ↦ (h3 r hr).mono hle hfp, fun q hq ↦ (h4 q hq).mono hle hfp, fun p hp ↦ ?_⟩
  obtain ⟨u, hu, hmu⟩ := h5 p hp
  exact ⟨u, by rw [hfp]; exact hle.get _ _ hu, hmu.mono hle hfp⟩

/-- `main`'s activation is at the bottom, in frame `0`. -/
theorem Below.main_fp {Ks : List Cert} {Km : Cert} {m : Mem} {a : Act} {rest : List Act}
    (h : Below Ks Km m a rest) (hm : a.K.F.main = true) : a.fp = 0 := by
  rcases rest with _ | ⟨b, rest⟩
  · exact h.2.2
  · exact absurd hm (by rw [h.1]; decide)

/-- **A step in the frame**: the top activation at another offset. -/
theorem stack_move {Ks : List Cert} {Km : Cert} {s s' : St} {a : Act} {rest : List Act}
    (ha : ActOk Ks s.mem a) (hfpa : a.fp = s.fp) (hbel : Below Ks Km s.mem a rest)
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) {j : ℕ} (hj : j < a.K.code.length)
    (hpc : s'.pc = a.K.F.entry + j) (hat : AtOff a.K.E a.K.F a.K.code j s') : StackAt Ks Km s' :=
  ⟨a, rest, j, ha.mono hle, hfpa.trans hfp.symm, hj, hpc, hat, hbel.mono hle⟩

/-- A jump the walk knows to stay in the frame does, `main`'s frame being `0`. -/
theorem self_fp {Ks : List Cert} {Km : Cert} {s1 s' : St} {a : Act} {rest : List Act} {A : Abs}
    {f : ℕ} (hbel : Below Ks Km s1.mem a rest) (hfpa : a.fp = s1.fp) (hA : Holds s1 A)
    (hS : SelfF a.K.F A f) (hfp1 : s1.fp < maxCells) (hfp' : s'.fp < maxCells)
    (hv : s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp))) : s'.fp = s1.fp := by
  rcases selfF_fp hA hS hfp1 hfp' hv with h | ⟨hm, h⟩
  · exact h
  · rw [h, ← hfpa, hbel.main_fp hm]

/-- **`main`'s halting jump** goes to the final state. -/
theorem halt_of {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) (hsz : C.ops.size ≤ 2 ^ 30) {s1 s' : St} {a : Act}
    {rest : List Act} {A : Abs} {d f : ℕ} (ha : a.K ∈ Ks) (hbel : Below Ks Km s1.mem a rest)
    (hfpa : a.fp = s1.fp) (hA : Holds s1 A) (hS : SelfF a.K.F A f)
    (hd : A.mono d = some ⟨0, a.K.E.halt, []⟩) (hmain : a.K.F.main = true)
    (hfp1 : s1.fp < maxCells) (hfp' : s'.fp < maxCells) (hpcs : s'.pc < C.ops.size)
    (hvd : s1.mem.get (s1.fp + d) = some (ofK (g ^ s'.pc)))
    (hvf : s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp))) :
    Halted prog { s' with steps := s'.steps + 1 } := by
  have hh : a.K.E.halt = 2 ^ prog.logSize - 1 := ((P.env _ ha).2.2.2.2).trans P.halt
  have hl : 2 ^ prog.logSize ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have hp := mono_pow hA hd hvd
  rw [Nat.mul_zero, Nat.zero_add, hh] at hp
  have hpc' : s'.pc = 2 ^ prog.logSize - 1 := gpow_inj (by omega) (by omega) hp
  have hfp0 : s'.fp = 0 := by
    rw [self_fp hbel hfpa hA hS hfp1 hfp' hvf, ← hfpa, hbel.main_fp hmain]
  exact halted_of hpc' hfp0

/-! ## A return -/

/-- **A return pops the activation**: its header names the caller's return point and frame, where the
caller's walk goes on from what the callee guarantees at its first frame, its loop's runs rebuilt
down its iterations. -/
theorem ret_stack {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) (hsz : C.ops.size ≤ 2 ^ 30) {M : ℕ → E} {s s1 s' : St} {a : Act}
    {rest : List Act} {A : Abs} (ha : ActOk Ks s.mem a) (hfpa : a.fp = s1.fp)
    (hbel : Below Ks Km s.mem a rest) (hnot : a.K ≠ Km) (hle1 : s.mem ≤ s1.mem) (hs1 : Fine M s1)
    (hA : Holds s1 A) (hret : retOk A a.K.F.sig = true) (hf' : Fine M s') (hle' : s1.mem ≤ s'.mem)
    (hpcs : s'.pc < 2 ^ 30) (hvd : s1.mem.get (s1.fp + 0) = some (ofK (g ^ s'.pc)))
    (hvf : s1.mem.get (s1.fp + 1) = some (ofK (g ^ s'.fp))) :
    StackAt Ks Km { s' with steps := s'.steps + 1 } := by
  rcases rest with _ | ⟨b, rest⟩
  · exact absurd hbel.1 hnot
  obtain ⟨-, r, h0, h1, ⟨ro, m0, hr, hro, hm0, hres⟩, hb, hbel'⟩ := hbel
  have hrlt : r < 2 ^ 62 := by have := cert_pc (P.ok b.K hb.mem) hro; omega
  have h0' : s1.mem.get (s1.fp + 0) = some (ofK (g ^ r)) := by rw [← hfpa]; exact hle1.get _ _ h0
  have h1' : s1.mem.get (s1.fp + 1) = some (ofK (g ^ b.fp)) := by rw [← hfpa]; exact hle1.get _ _ h1
  obtain ⟨hpc', hfp'⟩ := ret_regs hrlt hb.fp h0' h1' (by omega) hf'.fp hvd hvf
  have hwf1 := hs1.agree.wf
  have hu1 := hs1.agree.used
  obtain ⟨hR, -, -⟩ := retOk_sound hA hs1.fp hwf1 hu1 hret
  have hT1 : ∀ p ∈ a.K.F.sig.term, LTF s1 p.1 p.2 := fun p hp ↦
    LTF.mono (s := stOf s.mem a.fp) (s' := s1) hle1 hfpa.symm (ha.term p hp)
  obtain ⟨hL, hLP⟩ := ret_runs hA hs1.fp hwf1 hu1 hret hT1 (P.loopRng a.K ha.mem)
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  have hch := ha.chain.mono hle
  obtain ⟨hL0, hLP0⟩ := hch.runs hf'.agree.wf hf'.agree.used
    (fun r hr ↦ RW.mono (s := s1) (s' := stOf s'.mem a.fp) hle' hfpa (hL r hr))
    (fun q hq ↦ PW.mono (s := s1) (s' := stOf s'.mem a.fp) hle' hfpa (hLP q hq))
  have hR0 := hch.ret (RetHolds.mono (s := s1) (s' := stOf s'.mem a.fp) hle' hfpa hR)
  have hT0 := hch.term (ha.term.mono hle)
  have hat := hres s'.mem (Mem.le_trans hm0 hle) hf'.agree.wf hf'.agree.used (hch.fp0 ha.fp) hb.fp
    hR0 hL0 hLP0 hT0
  exact ⟨b, rest, ro, hb.mono hle, hfp'.symm, hro, by rw [show s'.pc = r from hpc', hr],
    AtOff.mono (s := stOf s'.mem b.fp) (Mem.le_refl _) hfp' hat, hbel'.mono hle⟩

/-! ## A tail call -/

/-- **A loop's tail call adds an iteration**: the next frame's entry state holds, its header copied
from this frame's, this frame kept with the walk's state at the call. -/
theorem tail_stack {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) (hsz : C.ops.size ≤ 2 ^ 30) {M : ℕ → E} {s s1 s' : St} {a : Act}
    {rest : List Act} {A : Abs} {d f e : ℕ} {G : Sig} (ha : ActOk Ks s.mem a) (hfpa : a.fp = s1.fp)
    (hbel : Below Ks Km s.mem a rest) (hjt : JtMem E0 s.mem) (hle1 : s.mem ≤ s1.mem)
    (hs1 : Fine M s1) (hA : Holds s1 A) (hfm : A.mono f = some ⟨1, e, []⟩)
    (hdm : A.mono d = some ⟨0, a.K.F.entry, []⟩) (hG : a.K.E.sigs.get a.K.F.entry = some G)
    (htail : tailOk A e G = true) (hloop : loopOk A a.K.F.sig = true) (hf' : Fine M s')
    (hle' : s1.mem ≤ s'.mem) (hpcs : s'.pc < 2 ^ 30)
    (hvd : s1.mem.get (s1.fp + d) = some (ofK (g ^ s'.pc)))
    (hvf : s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp)))
    (hterm : ∀ K' ∈ Ks, s'.pc = K'.F.entry → (∀ o ∈ K'.F.sig.entry, s'.mem.written (s'.fp + o) = true) →
      ∀ p ∈ K'.F.sig.term, LTF { s' with steps := s'.steps + 1 } p.1 p.2) :
    StackAt Ks Km { s' with steps := s'.steps + 1 } := by
  obtain ⟨K', hK', hent', hsig', hmain'⟩ := P.sigs a.K ha.mem _ G hG
  obtain rfl := P.uniq K' hK' a.K ha.mem hent'
  subst hsig'
  have hentlt : a.K.F.entry < 2 ^ 30 := by have := cert_pc (P.ok a.K ha.mem) (P.ne a.K ha.mem); omega
  have hp := mono_pow hA hdm hvd
  rw [Nat.mul_zero, Nat.zero_add] at hp
  have hpc' : s'.pc = a.K.F.entry := gpow_inj (by omega) (by omega) hp
  have hq := mono_pow hA hfm hvf
  rw [Nat.mul_one] at hq
  have hAC : Holds (stOf s'.mem s1.fp) A := Holds.mono (s := s1) (s' := stOf s'.mem s1.fp) hle' rfl hA
  have hmq : MonoVal (stOf s'.mem s1.fp) (.own e) (ofK (g ^ s'.fp)) := by
    have := MonoVal.own (s := stOf s'.mem s1.fp) e
    change MonoVal (stOf s'.mem s1.fp) (.own e) (ofK (g ^ (s1.fp + e))) at this
    rwa [← hq] at this
  have F : Frames (stOf s'.mem s1.fp) (stOf s'.mem s'.fp) (.own e) :=
    ⟨rfl, hmq, hf'.fp, hs1.fp, hf'.agree.wf, hf'.agree.used⟩
  unfold tailOk at htail
  simp only [Bool.and_eq_true, List.all_eq_true] at htail
  obtain ⟨⟨⟨hent, hhd⟩, -⟩, hL⟩ := htail
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  obtain ⟨-, -, e3, e4, -⟩ := P.env a.K ha.mem
  have hW := entryW_sound F hAC (entryW_of_entryOk hent)
  have hTE : TermAt s'.mem s'.fp a.K.F.sig := fun p hp ↦
    LTF.mono (s := { s' with steps := s'.steps + 1 }) (s' := stOf s'.mem s'.fp) (Mem.le_refl _) rfl
      (hterm a.K ha.mem hpc' hW p hp)
  have hEn := entryOk_sound F hAC hent (rw_jt e3 e4 (hjt.mono hle)) hTE
  have hhdr : ∀ o, o < 2 → ∃ u, s'.mem.get (s1.fp + o) = some u ∧ s'.mem.get (s'.fp + o) = some u := by
    intro o ho
    unfold headerOk at hhd
    have hh := List.all_eq_true.mp hhd o (by interval_cases o <;> simp)
    simp only [Bool.and_eq_true] at hh
    obtain ⟨hw, hh⟩ := hh
    split at hh
    · rename_i x y hx hy
      obtain rfl := Mono.beq_eq hh
      obtain ⟨w, hw', hmw⟩ := hvGet_cell F hAC (by omega) hx
      obtain ⟨u, hu', hmu⟩ := hAC.mono_val hy (hAC.written hw)
      exact ⟨u, hu', by rw [← hmw.unique hmu]; exact hw'⟩
    · cases hh
  have hruns : ∀ r ∈ a.K.F.sig.postL ++ a.K.F.sig.postLP.map (·.1),
      trRngUp A (.own e) r = some ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩ := by
    intro r hr
    have := hL r hr
    split at this
    · rename_i r' hr'
      rw [hr', Rng.beq_eq this]
    · cases this
  rcases rest with _ | ⟨b, rest⟩
  · rw [hbel.1, P.mainF] at hmain'
    cases hmain'
  obtain ⟨-, r, h0, h1, hsp, hb, hbel'⟩ := hbel
  obtain ⟨u0, hu0, hu0'⟩ := hhdr 0 (by omega)
  obtain ⟨u1, hu1, hu1'⟩ := hhdr 1 (by omega)
  have e0 : u0 = ofK (g ^ r) := Option.some.inj (hu0.symm.trans (by rw [← hfpa]; exact hle.get _ _ h0))
  have e1 : u1 = ofK (g ^ b.fp) :=
    Option.some.inj (hu1.symm.trans (by rw [← hfpa]; exact hle.get _ _ h1))
  have hit : IterOk s'.mem a.K ⟨s1.fp, A, e⟩ s'.fp :=
    ⟨hAC, hq, hs1.fp, hf'.fp, hloop, hruns, hfpa ▸ ha.term.mono hle, P.tailRet a.K ha.mem _ hG⟩
  refine ⟨⟨a.K, ⟨s1.fp, A, e⟩ :: a.its, s'.fp, a.fp0⟩, b :: rest, 0,
    ⟨ha.mem, ⟨hit, hfpa ▸ ha.chain.mono hle⟩, hTE, hf'.fp⟩, rfl, P.ne a.K ha.mem, by simp [hpc'],
    atOff_zero (holds_stOf.mpr hEn), hmain', r, e0 ▸ hu0', e1 ▸ hu1', hsp.mono hle, hb.mono hle,
    hbel'.mono hle⟩

/-! ## A call -/

/-- **The caller goes on after the call**: its arm's state at the call, the callee's frame named,
give its walk's state after the call once the callee guarantees its facts. -/
theorem resume_of_call {K : Cert} {A : Abs} {sel : Option Base} {mq : Mono} {Gs : List Sig} {j : ℕ}
    {G' : Sig} {sC : St} {fpE ro : ℕ} (hj : Gs[j]? = some G') (hmq : MonoVal sC mq (ofK (g ^ fpE)))
    (hA : Holds sC (atCall (A.assume sel j) mq G')) (hsel : ∀ x, sel = some x → IdxVal sC (.ex x 0) j)
    (hk : ∀ s3, Holds s3 (armsMeet sel ((Gs.zipIdx.map fun p ↦ (p.1, atCall (A.assume sel p.2) mq p.1)).map
      fun p ↦ afterCall p.2 mq p.1)) → AtOff K.E K.F K.code ro s3) :
    Resume K sC.fp ro G' fpE sC.mem := by
  intro m hm hwf hu hfpE hfpC hR hL hLP hT
  have F : Frames (stOf m sC.fp) (stOf m fpE) mq :=
    ⟨rfl, MonoVal.mono (s := sC) (s' := stOf m sC.fp) hm rfl hmq, hfpE, hfpC, hwf, hu⟩
  exact hk _ (ret_resume hj F (Holds.mono (s := sC) (s' := stOf m sC.fp) hm rfl hA)
    (fun x hx ↦ IdxVal.mono (s := sC) (s' := stOf m sC.fp) hm rfl (hsel x hx)) hR hL hLP hT)

/-- **A call pushes the callee's activation**, at its entry, its header naming the caller's return
point and frame, the caller suspended. -/
theorem call_stack {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) (hsz : C.ops.size ≤ 2 ^ 30) {M : ℕ → E} {s s1 s' : St} {a : Act}
    {rest : List Act} {A : Abs} {i d f r : ℕ} {mq : Mono} {G : Sig} {Gs : List Sig}
    (ha : ActOk Ks s.mem a) (hfpa : a.fp = s1.fp) (hbel : Below Ks Km s.mem a rest)
    (hjt : JtMem E0 s.mem) (hle1 : s.mem ≤ s1.mem) (hs1 : Fine M s1) (hA : Holds s1 A)
    (hfm : A.mono f = some mq) (h1 : A.hvGet (mq.shift 1) = some (.m ⟨1, 0, []⟩))
    (h0 : A.hvGet (mq.shift 0) = some (.m ⟨0, r, []⟩)) (hc : calleesOf a.K.E a.K.F A i d = some (G :: Gs))
    (hw : ∀ p ∈ (G :: Gs).zipIdx, entryW (A.assume (selOf A d) p.2) mq p.1 = true)
    (hok : ∀ p ∈ (G :: Gs).zipIdx.map (fun p ↦ (p.1, atCall (A.assume (selOf A d) p.2) mq p.1)),
      entryOk p.2 mq p.1 = true)
    (hr1 : a.K.F.entry + i < r) (hr2 : r < a.K.F.entry + a.K.F.len)
    (hk : ∀ s3, Holds s3 (armsMeet (selOf A d) (((G :: Gs).zipIdx.map fun p ↦
      (p.1, atCall (A.assume (selOf A d) p.2) mq p.1)).map fun p ↦ afterCall p.2 mq p.1)) →
      AtOff a.K.E a.K.F a.K.code (r - a.K.F.entry) s3)
    (hf' : Fine M s') (hle' : s1.mem ≤ s'.mem) (hpcs : s'.pc < 2 ^ 30)
    (hvd : s1.mem.get (s1.fp + d) = some (ofK (g ^ s'.pc)))
    (hvf : s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp)))
    (hterm : ∀ K' ∈ Ks, s'.pc = K'.F.entry → (∀ o ∈ K'.F.sig.entry, s'.mem.written (s'.fp + o) = true) →
      ∀ p ∈ K'.F.sig.term, LTF { s' with steps := s'.steps + 1 } p.1 p.2) :
    StackAt Ks Km { s' with steps := s'.steps + 1 } := by
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  obtain ⟨-, -, e3, e4, -⟩ := P.env a.K ha.mem
  have hT : ∀ G', a.K.E.sigs.get s'.pc = some G' → (∀ o ∈ G'.entry, s'.mem.written (s'.fp + o) = true) →
      ∀ p ∈ G'.term, LTF { s' with steps := s'.steps + 1 } p.1 p.2 := by
    intro G' hG'
    obtain ⟨K', hK', hent, rfl, -⟩ := P.sigs a.K ha.mem _ G' hG'
    exact hterm K' hK' hent.symm
  obtain ⟨Fr, hd1, hd0, j, G', hj, hsig, hsel, hA1, hW, hEn⟩ :=
    call_enter (sE := { s' with steps := s'.steps + 1 }) hA (envOk_of P ha.mem (hjt.mono hle1))
      (envSmall_of P hsz ha.mem) hfm h1 h0 hc hw hok hs1.fp hle' hf'.agree.wf hf'.agree.used hf'.fp
      (show s'.pc < 2 ^ 62 by omega) hvd hvf hT (rw_jt e3 e4 (hjt.mono hle))
  obtain ⟨K', hK', hent, hsig', hmain'⟩ := P.sigs a.K ha.mem _ G' hsig
  subst hsig'
  obtain ⟨-, -, e3', e4', -⟩ := P.env K' hK'
  have hres := resume_of_call (K := a.K) (ro := r - a.K.F.entry) hj Fr.mq hA1 hsel hk
  have hlen := (P.ok a.K ha.mem).len
  refine ⟨⟨K', [], s'.fp, s'.fp⟩, a :: rest, 0, ⟨hK', rfl, fun p hp ↦ ?_, hf'.fp⟩, rfl, P.ne K' hK',
    by simp [hent], ?_, hmain', r, hd0, by rw [hfpa]; exact hd1, ⟨r - a.K.F.entry, s'.mem, by omega,
      by omega, Mem.le_refl _, by rw [hfpa]; exact hres⟩, ha.mono hle, hbel.mono hle⟩
  · exact LTF.mono (s := { s' with steps := s'.steps + 1 }) (s' := stOf s'.mem s'.fp) (Mem.le_refl _) rfl
      (hterm K' hK' hent.symm hW p hp)
  · apply atOff_zero
    rw [← entryAbs_congr (e3.trans e3'.symm) (e4.trans e4'.symm)]
    exact hEn

end

end LeanVM.Guest.Mode
