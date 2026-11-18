module

public import LeanVM.Guest.Mode.InvRule

/-!
# The mode walk's frame interface

`frameSpec_walk`: a certificate whose walk accepts its code and is tied to the executor (`CertOk`),
its loop's runs ranging over its termination facts, meets `FrameSpec` for the frame predicate
`AtOff` (an offset its walk reaches): the entry is the walk's start (`atOff_zero`), a step is
`step_atX`, and a taken jump is one of the walk's `JumpK` cases, sorted into `Out`: a return
(`retOk_sound`, `ret_runs`), a forward or table jump (`jump_to_pc`, in the frame by `selfF_fp`), the
halt, a loop's tail call (`tailOk`'s entry, header and runs, the iteration's `Back` by
`back_of_tail`) and a call (`call_enter`, the caller resumable by `resume_of_call`). `inv_rule`:
`inv_rule_of_specs` with every function on the walk.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- A jump the walk knows to stay in the frame does, `main`'s frame being `0`. -/
theorem self_fp {s1 s' : St} {A : Abs} {F : Fun} {f : ℕ} (hA : Holds s1 A) (hS : SelfF F A f)
    (hm0 : F.main = true → s1.fp = 0) (hfp1 : s1.fp < maxCells) (hfp' : s'.fp < maxCells)
    (hv : s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp))) : s'.fp = s1.fp := by
  rcases selfF_fp hA hS hfp1 hfp' hv with h | ⟨hm, h⟩
  · exact h
  · rw [h, hm0 hm]

/-- **A loop's iteration returns what the next one does**: at a tail call the walk accepts, into the
frame `fp·g^e`, its loop's runs (`loop_step`) and guarantees (`retStay_sound`) at the next frame are
this frame's. -/
theorem back_of_tail {m : Mem} {Kc : Cert} {fp nx e : ℕ} {A : Abs} (hA : Holds (stOf m fp) A)
    (hnext : (g : K) ^ nx = g ^ (fp + e)) (hfp : fp < maxCells) (hnx : nx < maxCells)
    (hloop : loopOk A Kc.F.sig = true)
    (hruns : ∀ r ∈ Kc.F.sig.postL ++ Kc.F.sig.postLP.map (·.1),
      trRngUp A (.own e) r = some ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩)
    (hst : retStay A e Kc.F.sig = true) : Back m Kc.F.sig fp nx := by
  intro m' hle hwf hu ⟨hR, hL, hLP⟩
  have hA' : Holds (stOf m' fp) A := Holds.mono (s := stOf m fp) (s' := stOf m' fp) hle rfl hA
  have F : Frames (stOf m' fp) (stOf m' nx) (.own e) := by
    have hm := MonoVal.own (s := stOf m' fp) e
    change MonoVal (stOf m' fp) (.own e) (ofK (g ^ (fp + e))) at hm
    rw [← hnext] at hm
    exact ⟨rfl, hm, hnx, hfp, hwf, hu⟩
  obtain ⟨hpt, hptP⟩ := loopOk_sound hA' hfp hwf hu hloop
  exact ⟨retStay_sound hA' F hst hR,
    fun r hr ↦ loop_step hA' F (hruns r (List.mem_append_left _ hr)) (hL r hr) (hpt r hr),
    fun q hq ↦ loop_stepP hA' F (hruns q.1 (List.mem_append_right _ (List.mem_map_of_mem hq)))
      (hLP q hq) (hptP q hq)⟩

/-- **The caller goes on after the call**: its arm's state at the call, the callee's frame named,
give its walk's state after the call once the callee guarantees its facts. -/
theorem resume_of_call {K : Cert} {A : Abs} {sel : Option Base} {mq : Mono} {Gs : List Sig} {j : ℕ}
    {G' : Sig} {sC : St} {fpE ro : ℕ} (hj : Gs[j]? = some G') (hmq : MonoVal sC mq (ofK (g ^ fpE)))
    (hA : Holds sC (atCall (A.assume sel j) mq G')) (hsel : ∀ x, sel = some x → IdxVal sC (.ex x 0) j)
    (hk : ∀ s3, Holds s3 (armsMeet sel ((Gs.zipIdx.map fun p ↦ (p.1, atCall (A.assume sel p.2) mq p.1)).map
      fun p ↦ afterCall p.2 mq p.1)) → AtOff K.E K.F K.code ro s3) :
    Resume (AtOff K.E K.F K.code) sC.fp ro G' fpE sC.mem := by
  intro m hm hwf hu hfpE hfpC hR hL hLP hT
  have F : Frames (stOf m sC.fp) (stOf m fpE) mq :=
    ⟨rfl, MonoVal.mono (s := sC) (s' := stOf m sC.fp) hm rfl hmq, hfpE, hfpC, hwf, hu⟩
  exact hk _ (ret_resume hj F (Holds.mono (s := sC) (s' := stOf m sC.fp) hm rfl hA)
    (fun x hx ↦ IdxVal.mono (s := sC) (s' := stOf m sC.fp) hm rfl (hsel x hx)) hR hL hLP hT)

/-- **The mode walk meets the frame interface**, for its frame predicate `AtOff`. -/
theorem frameSpec_walk {C : Ctx} {M : ℕ → E} {K : Cert} (hK : CertOk C K)
    (hrng : ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1), (r.lo, r.hi) ∈ K.F.sig.term) :
    FrameSpec C M K (AtOff K.E K.F K.code) where
  mono hle hfp h := AtOff.mono hle hfp h
  entry h := atOff_zero h
  step := by
    intro s i hi hpc hat hs hsz hhalt hE hES hjt hT hm0 hown hh hres href Inv k
    have hlen : K.F.entry + K.F.len < 2 ^ 62 := by
      have := cert_pc hK (show K.code.length - 1 < K.code.length by omega)
      rw [hK.len]
      omega
    have hhs : (C.hints[s.pc]?).getD [] = (K.F.hints.get i).getD [] := by rw [hpc, hK.hints i hi]
    refine step_atX hK hi hpc hat hs hE
      (fun pre h post hp s1 e hm hin ↦ hh pre h post (hhs.trans hp) s1 e hm hin) hres href
      (fun s1 s' e1 hm hmo e hpc' hfp' hf' hle' hat' ↦ ?_)
      (fun c d f A go A' s1 s' e1 hins hm hmo hA hj hk e hf' hle' hpcs hvd hvf ↦ ?_)
    · have hi' : i + 1 < K.code.length := by
        by_contra hn
        have heq : i + 1 = K.code.length := by omega
        obtain ⟨cur, pend, h0, hh0⟩ := hat'
        rw [heq] at h0
        have hc := preAt_end_cur hK.walk le_rfl h0
        have hp := preAt_end hK.walk le_rfl h0
        subst hc
        subst hp
        rcases hh0 with ⟨A, hA, -⟩ | ⟨G, hG, -⟩
        · exact absurd hA List.not_mem_nil
        · exact absurd hG List.not_mem_nil
      exact k s1 s' (by rw [hhs]; exact e1) hm hmo e hf' hle'
        (.move (i + 1) (hfp'.trans hm.fp.symm) hi' (by rw [hpc', hpc]; omega) hat')
    have hs1 := hm.fine
    have hle1 := hm.le
    have hE1 : EnvOk s1 K.E := EnvOk.mono hle1 hE
    have hm0' : K.F.main = true → s1.fp = 0 := fun h ↦ hm.fp.trans (hm0 h)
    have hpcs' : s'.pc < 2 ^ 30 := by omega
    refine k s1 s' (by rw [hhs]; exact e1) hm (by rw [hins]; exact hmo) (by rw [hins]; exact e) hf' hle' ?_
    cases jumpI_cases hj with
    | ret hd hf hok =>
      subst hd
      subst hf
      have hT1 : ∀ p ∈ K.F.sig.term, LTF s1 p.1 p.2 := fun p hp ↦
        LTF.mono (s := stOf s.mem s.fp) (s' := s1) hle1 hm.fp (hT p hp)
      obtain ⟨hR, -, -⟩ := retOk_sound hA hs1.fp hs1.agree.wf hs1.agree.used hok
      obtain ⟨hL, hLP⟩ := ret_runs hA hs1.fp hs1.agree.wf hs1.agree.used hok hT1 hrng
      exact .ret c (by rw [List.getElem?_eq_getElem hi, hins]) (by omega) hvd hvf (retAll_of hR hL hLP)
    | fwd e' hS hd h1 h2 =>
      obtain ⟨j, hj, hpcj, hjl⟩ := jump_to_pc hA hE1 (.fwd e' hS hd h1 h2) hS (by omega) hlen hvd
      have hfp' := self_fp hA hS hm0' hs1.fp hf'.fp hvf
      exact .move j hfp' (hK.len ▸ hjl) hpcj
        (hk _ rfl _ j hj (Holds.mono (s := s1) (s' := s') hle' hfp' hA))
    | halt hS hd hmain =>
      have hp := mono_pow hA hd hvd
      rw [Nat.mul_zero, Nat.zero_add] at hp
      have hpc' : s'.pc = K.E.halt := gpow_inj (by omega) (by omega) hp
      exact .halt hmain hpc' ((self_fp hA hS hm0' hs1.fp hf'.fp hvf).trans (hm0' hmain))
    | arms ts hS hts =>
      obtain ⟨j, hj, hpcj, hjl⟩ := jump_to_pc hA hE1 (.arms ts hS hts) hS (by omega) hlen hvd
      have hfp' := self_fp hA hS hm0' hs1.fp hf'.fp hvf
      exact .move j hfp' (hK.len ▸ hjl) hpcj
        (hk _ rfl _ j hj (Holds.mono (s := s1) (s' := s') hle' hfp' hA))
    | tail e' G hfm hdm hG htail hloop =>
      obtain rfl := hown G hG
      refine .tail hG fun hTE ↦ ?_
      have hentlt : K.F.entry < 2 ^ 30 := by
        have := cert_pc hK (show 0 < K.code.length by omega)
        omega
      have hp := mono_pow hA hdm hvd
      rw [Nat.mul_zero, Nat.zero_add] at hp
      have hpc' : s'.pc = K.F.entry := gpow_inj (by omega) (by omega) hp
      have hq := mono_pow hA hfm hvf
      rw [Nat.mul_one] at hq
      have hAC : Holds (stOf s'.mem s1.fp) A := Holds.mono (s := s1) (s' := stOf s'.mem s1.fp) hle' rfl hA
      have hmq : MonoVal (stOf s'.mem s1.fp) (.own e') (ofK (g ^ s'.fp)) := by
        have := MonoVal.own (s := stOf s'.mem s1.fp) e'
        change MonoVal (stOf s'.mem s1.fp) (.own e') (ofK (g ^ (s1.fp + e'))) at this
        rwa [← hq] at this
      have F : Frames (stOf s'.mem s1.fp) (stOf s'.mem s'.fp) (.own e') :=
        ⟨rfl, hmq, hf'.fp, hs1.fp, hf'.agree.wf, hf'.agree.used⟩
      unfold tailOk at htail
      simp only [Bool.and_eq_true, List.all_eq_true] at htail
      obtain ⟨⟨⟨⟨hent, hhd⟩, -⟩, hL⟩, hst⟩ := htail
      have hW := entryW_sound F hAC (entryW_of_entryOk hent)
      have hEn := entryOk_sound F hAC hent (hjt _ (Mem.le_trans hle1 hle'))
        (hTE K.F.sig (by rw [hpc']; exact hG) hW)
      have hhdr : ∀ o < 2, ∃ u, s'.mem.get (s1.fp + o) = some u ∧ s'.mem.get (s'.fp + o) = some u := by
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
      have hruns : ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1),
          trRngUp A (.own e') r = some ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩ := by
        intro r hr
        have := hL r hr
        split at this
        · rename_i r' hr'
          rw [hr', Rng.beq_eq this]
        · cases this
      exact ⟨hpc', hW, hhdr, back_of_tail hAC hq hs1.fp hf'.fp hloop hruns hst, holds_stOf.mpr hEn⟩
    | call mq r G Gs _ hfm h1 h0 hc hw hok hr1 hr2 =>
      refine .call fun hTE ↦ ?_
      have hTs : ∀ G', K.E.sigs.get s'.pc = some G' → (∀ o ∈ G'.entry, s'.mem.written (s'.fp + o) = true) →
          ∀ p ∈ G'.term, LTF s' p.1 p.2 := fun G' hG' hw' p hp ↦
        LTF.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hTE G' hG' hw' p hp)
      obtain ⟨Fr, hd1, hd0, j, G', hj, hsig, hsel, hA1, hW, hEn⟩ :=
        call_enter (sE := s') hA hE1 hES hfm h1 h0 hc hw hok hs1.fp hle' hf'.agree.wf hf'.agree.used
          hf'.fp (show s'.pc < 2 ^ 62 by omega) hvd hvf hTs (hjt _ (Mem.le_trans hle1 hle'))
      have hres := resume_of_call (K := K) (ro := r - K.F.entry) hj Fr.mq hA1 hsel
        (fun s3 h ↦ hk _ rfl s3 _ (List.mem_singleton_self _) h)
      have hlen' := hK.len
      exact ⟨G', r - K.F.entry, hsig, by omega,
        by rw [show K.F.entry + (r - K.F.entry) = r by omega]; exact hd0, hd1, hW, hEn, hres⟩

/-- **The invariant rule on the walk**: `inv_rule_of_specs` with every function's frame predicate its
walk's, each certificate tied to the executor and its loop's runs over its termination facts. -/
theorem inv_rule {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    {Ks : List Cert} {Km : Cert} {E0 : Env} {X Pro : St → Prop} (hκ : κ ≤ 28)
    (hC : Ctx.of prog adv = .ok C) (P : ProgOk prog C Ks Km E0)
    (hW : ∀ K ∈ Ks, CertOk C K ∧ ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1), (r.lo, r.hi) ∈ K.F.sig.term)
    (R : Prem prog img n C Ks X)
    (hpro : ∀ s op, X s → Pro s → Fine (refMem img) s → OnRef prog img n s → C.ops[s.pc]? = some op →
      StepOk C (refMem img) (fun s' ↦ Pro s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s) :
    InvRule prog img n C (refMem img) (guestInv prog Ks Km E0 (fun K ↦ AtOff K.E K.F K.code) X Pro) :=
  inv_rule_of_specs hκ hC P (fun K hK ↦ frameSpec_walk (hW K hK).1 (hW K hK).2) R hpro

end

end LeanVM.Guest.Mode
