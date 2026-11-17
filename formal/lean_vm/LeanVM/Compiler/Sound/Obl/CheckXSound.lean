/-
  LeanVM.Compiler.Sound.Obl.CheckXSound

  The analysis with `ext` sites is sound, the callees' `ext` preconditions shown at each site.
-/

module

public import LeanVM.Compiler.Sound.Obl.CheckX
public import LeanVM.Compiler.Sound.Obl.World

/-!
# Soundness with `ext` sites

`XSite X T rd σ s`: what a call, conditional call or dispatch `s` asks of its callees' `ext`
preconditions, `X`, for the callees the table marks `ext` (a conditional call when its condition
holds, a dispatch at its selector's arm). `fnX_obl_of_chk`: a function `chkFnX` accepts has its
obligations under the precondition `UOf T R X`, given its facts and, at each site of `xs`, `XSite`
over the statements before it.
-/

namespace LeanVM.Compiler.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **What a site asks of its callees' `ext` preconditions.** -/
def XSite (X : Reader → String → List E → Prop) (T : Tab) (rd : Reader) (σ : Val) : Stmt → Prop
  | .call f args _ => (T.sig f).ext = true → X rd f (args.map σ)
  | .callIf c f args => σ c ≠ 0 → (T.sig f).ext = true → X rd f (args.map σ)
  | .dispatch x fs args _ => ∀ (j : Nat) (h : j < fs.length), σ x = ofK (addressOfIndex j) →
      (T.sig fs[j]).ext = true → X rd fs[j] (args.map σ)
  | _ => True

variable {R : Nat → Reader → E → Prop} {T : Tab} {X : Reader → String → List E → Prop} {κ : ℕ}
  {L : MemoryImage κ} {σ : Val} {C : CallRel} {ctx : List Hyp}

theorem callOkX_sound (hT : PowsOk T) (hκ : κ ≤ 32) (hc : CtxHolds R L.read σ ctx) {f : String}
    {args : List V} (h : callOkX T ctx f args = true) :
    SigPre R L.read (T.sig f) (args.map σ) := by
  simp only [callOkX, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hm⟩, hxp⟩ := h
  refine ⟨fun p hp' _ => ?_, fun m hm' _ => ?_, fun p hp' _ => ?_⟩
  · obtain ⟨hl, hb⟩ := hp p hp'
    rw [getD_map_lt hl]
    exact bndLe_sound hT hκ hc hb
  · obtain ⟨hl, hb⟩ := hm m hm'
    rw [getD_map_lt hl]
    exact memLe_spec hc hb
  · obtain ⟨hl, hb⟩ := hxp p hp'
    rw [getD_map_lt hl]
    exact xLe_spec hc hb

/-- **An `ext` site the analysis accepts has its obligations**, its callees' `ext` preconditions
given. -/
theorem obl_of_chkX (hT : PowsOk T) (hκ : κ ≤ 32)
    (hpost : ∀ f a r, C f a r →
      SigPost (T.sig f) (a ++ r) ∧ XPost R L.read (T.sig f) (a ++ r)) :
    ∀ (s : Stmt) (N : Prop), CtxHolds R L.read σ ctx → chkX T ctx s = true → XSite X T L.read σ s →
      (CtxHolds R L.read σ (after T ctx s) → Stmt.Holds C L.read σ s True (fun _ => True) → N) →
        Obl C (UOf T R X L.read) L.read σ s N
  | .call f args rets, _, hc, h, hx, hN => by
      simp only [chkX] at h
      refine ⟨⟨callOkX_sound hT hκ hc h, hx⟩, fun hC => hN (fun a ha => ?_) ⟨hC, trivial⟩⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · show SigPost _ _ ∧ XPost _ _ _ _
        rw [List.map_append]
        exact hpost _ _ _ hC
      · exact hc a ha
  | .callIf c f args, _, hc, h, hx, hN => by
      simp only [chkX] at h
      exact fun hk => ⟨fun h0 => ⟨callOkX_sound hT hκ hc h, hx h0⟩,
        fun hC => hN hc ⟨hk, hC, trivial⟩⟩
  | .dispatch x fs args rets, _, hc, h, hx, hN => by
      simp only [chkX, Bool.and_eq_true, List.all_eq_true] at h
      refine ⟨bndLe_sound hT hκ hc h.1, fun j hj hs => ?_, fun hd => hN hc ⟨hd, trivial⟩⟩
      exact ⟨callOkX_sound hT hκ hc (h.2 fs[j] (List.getElem_mem hj)), hx j hj hs⟩
  | .atom _, _, _, h, _, _ => by simp [chkX] at h
  | .ite .., _, _, h, _, _ => by simp [chkX] at h
  | .match_ .., _, _, h, _, _ => by simp [chkX] at h
  | .ret _, _, _, h, _, _ => by simp [chkX] at h

/-- **A block the analysis with `ext` sites accepts has its obligations**, each fact `(i, h)`
holding and each site `i ∈ xs` meeting `XSite` wherever the block's first `i` statements hold. -/
theorem oblTX_of_chk (hT : PowsOk T) (hκ : κ ≤ 32)
    (hpost : ∀ f a r, C f a r →
      SigPost (T.sig f) (a ++ r) ∧ XPost R L.read (T.sig f) (a ++ r)) (w : Want)
    (facts : List (Nat × Hyp)) (xs : List Nat) (body : List Stmt)
    (hf : ∀ p ∈ facts, Stmt.HoldsList C L.read σ (body.take p.1) True (fun _ => True) →
      p.2.Holds R L.read σ)
    (hx : ∀ i ∈ xs, ∀ s ss, body.drop i = s :: ss →
      Stmt.HoldsList C L.read σ (body.take i) True (fun _ => True) → XSite X T L.read σ s) :
    ∀ (ss : List Stmt) (i : Nat) (ctx : List Hyp) (N : Prop), body.drop i = ss →
      Stmt.HoldsList C L.read σ (body.take i) True (fun _ => True) → CtxHolds R L.read σ ctx →
      chkTX T w facts xs i ctx ss = true → N → OblList C (UOf T R X L.read) L.read σ ss N
  | [], _, _, _, _, _, _, _, hN => hN
  | s :: ss, i, ctx, N, hd, hpre, hc, h, hN => by
      simp only [chkTX, Bool.and_eq_true] at h
      have hc' : CtxHolds R L.read σ (factsAt facts i ++ ctx) := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · simp only [factsAt, List.mem_filterMap] at ha
          obtain ⟨p, hp, hq⟩ := ha
          split at hq
          · rename_i he
            obtain rfl := Option.some.inj hq
            rw [beq_iff_eq] at he
            exact hf p hp (he ▸ hpre)
          · exact absurd hq (by simp)
        · exact hc a ha
      have hk : ∀ hc'' : CtxHolds R L.read σ (after T (factsAt facts i ++ ctx) s),
          Stmt.Holds C L.read σ s True (fun _ => True) →
            OblList C (UOf T R X L.read) L.read σ ss N := fun hc'' hs =>
        oblTX_of_chk hT hκ hpost w facts xs body hf hx ss (i + 1) _ N
          (by rw [← List.drop_drop, hd, List.drop_one, List.tail_cons])
          (by
            rw [take_succ_of_drop hd, holdsList_append]
            exact holdsList_mono (fun _ _ _ h => h) _ (fun _ => hs) (fun _ h => h) hpre)
          hc'' h.2 hN
      cases hi : xs.contains i with
      | true =>
        simp only [hi, ↓reduceIte] at h
        exact obl_of_chkX hT hκ hpost s _ hc' h.1
          (hx i (List.contains_iff_mem.mp hi) s ss hd hpre) hk
      | false =>
        simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
        exact obl_of_chk hT hκ (fun f a hx' hp => ⟨hp, fun he => absurd he (by rw [hx']; simp)⟩)
          hpost w s _ _ hc' h.1 hk

/-- **A function the analysis with `ext` sites accepts has its obligations** wherever its
precondition holds, given its facts and its sites' `XSite`. -/
theorem fnX_obl_of_chk (hT : PowsOk T) (hκ : κ ≤ 32)
    (hpost : ∀ f a r, C f a r →
      SigPost (T.sig f) (a ++ r) ∧ XPost R L.read (T.sig f) (a ++ r))
    {facts : List (Nat × Hyp)} {xs : List Nat} {f : Fn} (h : chkFnX T facts xs f = true)
    (hf : ∀ p ∈ facts, Stmt.HoldsList C L.read σ (f.body.take p.1) True (fun _ => True) →
      p.2.Holds R L.read σ)
    (hx : ∀ i ∈ xs, ∀ s ss, f.body.drop i = s :: ss →
      Stmt.HoldsList C L.read σ (f.body.take i) True (fun _ => True) → XSite X T L.read σ s)
    (hpre : SigPre R L.read (T.sig f.name) (f.params.map σ)) :
    OblList C (UOf T R X L.read) L.read σ f.body True :=
  oblTX_of_chk hT hκ hpost _ facts xs f.body hf hx f.body 0 _ True rfl trivial (entry_holds hpre) h
    trivial

end
end LeanVM.Compiler.Obl
