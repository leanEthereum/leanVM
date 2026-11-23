/-
  LeanVM.Guest.CoreMode.Fam.ResExpC

  The exponents a body pins are so on its returning paths (`valExpB_sound`), and the parameters
  whose bounds every call site carries are so at every honest instance (`expCQ_all`).
-/

module

public import LeanVM.Guest.EndExecADyn
public import LeanVM.Guest.CoreMode.Fam.RefAll
public import LeanVM.Guest.CoreMode.Fam.ResExp
public import LeanVM.Guest.CoreMode.Fam.ExpCDefs
public import LeanVM.Guest.CoreMode.Gen.ExpCarry
public import LeanVM.Guest.EndExecCoreFn

/-!
# Exponents a body pins, carried down

`valExpB_sound`: on a returning path whose events hold, a value `valExpB` names is `g^e`, `lo ≤ e < hi`: a constant
of the spine (`spineE_sub`), or a copy of one on the spine of the arm the top-level `match` takes (`walkArms_arm`).
`expCQ_all`: where every function's call sites carry the listed bounds (`carryExpB`) and no listed callee is `main`,
every honest instance of a listed callee has its parameter's word `g^e`, `lo ≤ e < hi` (`insts_all`: the caller's
path returns, its argument is pinned there, and the callee's parameter is that argument's word); at the registry of
every function's carried bounds (`FnReg.expCarry`, its whole-program check `Res.expCarry_all`), `expCarryQ_all`, and
the exponent facts they give (`expOk_of_carry`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

public section

section

variable {rd : Reader} {σ : Val}

theorem constExpS_sound {v : V} {lo hi : ℕ} {sp : List Ev} (hh : ∀ e ∈ sp, e.Holds rd σ)
    (h : CoreMode.constExpS v lo hi sp = true) : ∃ e, lo ≤ e ∧ e < hi ∧ σ v = ofK (addressOfIndex e) := by
  unfold CoreMode.constExpS at h
  obtain ⟨y, hy, hc⟩ := List.any_eq_true.mp h
  rcases y with ⟨a⟩ | _ | _ | _
  all_goals try simp at hc
  cases a
  all_goals try (simp at hc; done)
  rename_i d w
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hd, he⟩ := hc
  have hdv : d = v := by simp only [Res.veq, Bool.and_eq_true, decide_eq_true_eq] at hd; exact hd.2
  subst hdv
  cases hp : Res.powOf1 w with
  | none => rw [hp] at he; simp at he
  | some e =>
    rw [hp] at he
    simp only [Option.any_some, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at he
    have hw : σ d = w := hh _ hy
    exact ⟨e, he.1, he.2, by rw [hw, powOf1_sound hp]⟩

theorem copyExpS_sound {v : V} {lo hi : ℕ} {sp : List Ev} (hh : ∀ e ∈ sp, e.Holds rd σ)
    (h : CoreMode.copyExpS v lo hi sp = true) : ∃ e, lo ≤ e ∧ e < hi ∧ σ v = ofK (addressOfIndex e) := by
  unfold CoreMode.copyExpS at h
  obtain ⟨y, hy, hc⟩ := List.any_eq_true.mp h
  rcases y with ⟨a⟩ | _ | _ | _
  all_goals try simp at hc
  cases a
  all_goals try (simp at hc; done)
  rename_i d s
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hd, hs⟩ := hc
  have hdv : d = v := by simp only [Res.veq, Bool.and_eq_true, decide_eq_true_eq] at hd; exact hd.2
  subst hdv
  have hw : σ d = σ s := hh _ hy
  obtain ⟨e, h1, h2, h3⟩ := constExpS_sound hh hs
  exact ⟨e, h1, h2, hw.trans h3⟩

/-- **A value every arm of a top-level `match` copies from a constant** is that arm's constant, on a returning path
whose events hold. -/
theorem armExpB_sound {v : V} {lo hi : ℕ} : ∀ {ss : List Stmt} {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → (∀ e ∈ es, e.Holds rd σ) → CoreMode.armExpB v lo hi ss = true →
      ∃ e, lo ≤ e ∧ e < hi ∧ σ v = ofK (addressOfIndex e)
  | [], _, _, _, _, hv => by simp [CoreMode.armExpB] at hv
  | s :: ss, es, vs, hw, hh, hv => by
    unfold CoreMode.armExpB at hv
    rw [walk] at hw
    rcases Bool.or_eq_true_iff.mp hv with hv | hv
    · rcases s with _ | _ | ⟨x, _ | ⟨a, as⟩⟩ | _ | _ | _ | _
      all_goals try (simp at hv; done)
      simp only at hv
      rw [List.all_eq_true] at hv
      have hst : walk1 σ (.match_ x (a :: as)) ≠ .stuck := by
        intro h0; rw [h0] at hw; simp [Out.seq] at hw
      simp only [walk1] at hst hw
      obtain ⟨i, hi, -, harm⟩ := walkArms_arm (a :: as) 0 hst
      have hsub := seq_ret_sub hw
      rw [harm] at hst hsub
      have hin : ∀ y ∈ spineE (a :: as)[i], y ∈ es := fun y hy ↦ hsub y (spineE_sub _ hst y hy)
      exact copyExpS_sound (fun e he ↦ hh e (hin e he)) (hv _ (List.getElem_mem hi))
    · rw [Bool.and_eq_true] at hv
      obtain ⟨es1, es2, -, hw2, rfl⟩ := seq_ret_next hv.1 hw
      exact armExpB_sound hw2 (fun e he ↦ hh e (List.mem_append_right _ he)) hv.2

/-- **A value a body pins** (`valExpB`) is `g^e`, `lo ≤ e < hi`, on a returning path whose events hold. -/
theorem valExpB_sound {body : List Stmt} {v : V} {lo hi : ℕ} {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) (h : CoreMode.valExpB body v lo hi = true) :
    ∃ e, lo ≤ e ∧ e < hi ∧ σ v = ofK (addressOfIndex e) := by
  unfold CoreMode.valExpB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · have hst : walk σ body ≠ .stuck := by rw [hw]; simp
    refine constExpS_sound (fun e he ↦ hh e ?_) h
    have := spineE_sub body hst e he
    rwa [hw] at this
  · exact armExpB_sound hw hh h

end

/-- **What a listed callee's honest instance gets**: each listed parameter's word `g^e`, `lo ≤ e < hi`. -/
@[expose] def ExpCQ (L : List (String × ℕ × ℕ × ℕ)) (J : Inst) : Prop :=
  ∀ c ∈ L, ∀ σ bufs kids, J.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → ∀ v,
    fn.params[c.2.1]? = some v → ∃ e, c.2.2.1 ≤ e ∧ e < c.2.2.2 ∧ σ v = ofK (addressOfIndex e)

section

variable {r : Ref}

/-- **`ExpCQ` passes down a call**: the caller's call site carries the bound (`carryExpB`), its argument pinned on its
returning path (`valExpB_sound`), the callee's parameter that argument's word. -/
theorem expCQ_step {L : List (String × ℕ × ℕ × ℕ)} (hall : ∀ fn ∈ coreProgram, CoreMode.carryExpB L fn = true) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (ExpCQ L) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    cc hcc σ bufs kids hJt fn hf v hv
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn', hfn', hpar, -⟩ := hJv
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hfn')
  have hcf : c.f = cc.1 := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have h0 := hall fnI (List.mem_of_find?_eq_some hfI)
  unfold CoreMode.carryExpB at h0
  have hs := Res.calls_sites h0 hw c hc
  simp only [hcf] at hs
  have hs2 := List.all_eq_true.mp hs cc hcc
  simp only [bne_self_eq_false, Bool.false_or] at hs2
  have hpv := congrArg (·[cc.2.1]?) hpar
  simp only [List.getElem?_map, hv, Option.map_some] at hpv
  cases ha : c.args[cc.2.1]? with
  | none => rw [ha] at hpv; cases hpv
  | some a =>
    rw [ha] at hs2 hpv
    obtain ⟨e, h1, h2, h3⟩ := valExpB_sound hw hh hs2
    refine ⟨e, h1, h2, ?_⟩
    simp only [Option.map_some, Option.some.injEq] at hpv
    rw [hpv, h3]

/-- **`ExpCQ` at every honest instance**, every function's call sites carrying the listed bounds and no listed callee
`main`. -/
theorem expCQ_all (hr : r.Ok) {L : List (String × ℕ × ℕ × ℕ)}
    (hall : ∀ fn ∈ coreProgram, CoreMode.carryExpB L fn = true) (hmain : ∀ c ∈ L, c.1 ≠ "main") :
    ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ExpCQ L J := by
  refine insts_all hr (expCQ_step hall) fun J hm ↦ ?_
  intro cc hcc σ bufs kids hJt
  exact absurd (hm _ _ _ _ hJt) (hmain cc hcc)

/-- **The registry's carried bounds at every honest instance.** -/
theorem expCarryQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ExpCQ CoreMode.FnReg.expCarry J :=
  expCQ_all hr Res.expCarry_all (by decide)

end

/-- **A carried bound's exponent fact**: its upper bound. -/
theorem expOk_of_carry {c : String × ℕ × ℕ × ℕ} (hc : c ∈ CoreMode.FnReg.expCarry) : ExpOk (c.1, c.2.1, none, c.2.2.2) := by
  intro r hr J hJ σ bufs kids hJt fn hf v hv
  obtain ⟨e, -, he, hσ⟩ := expCarryQ_all hr J hJ c hc σ bufs kids hJt fn hf v hv
  exact ⟨e, he, by rw [hσ, Value.gen_pow_eq_ofK]⟩

end

end LeanVM.Guest.EndExec
