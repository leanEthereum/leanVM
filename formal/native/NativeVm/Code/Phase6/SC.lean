module

public import NativeVm.Code.Phase6.Round

/-!
# Phase 6's sumchecks against `Model.sumcheck`

`scP_refines`: `scP c co n` refines `sumcheckPlain claim c n`; `scE_refines`: `scE c` refines
`sumcheck claim c (point.map some)` over the point at `ePt`, its challenges written over it. Each
leaves the scratch `g0` with the challenges from `co` (`wrA`), up to the round's temporaries
(`Tmp`), and the final claim at `eSC`.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd wdisp Env)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g g0 : Nat → EW}

/-- The sumcheck's result in the scratch: `g0` with the challenges `pt` from `co`, up to the
temporaries, the final claim `v` at `eSC`. -/
def SCPost (env : Env) (s0 : QState) (g0 : Nat → EW) (co n : Nat) (r : Array EW × EW) (t : TState)
    (s : QState) : Prop :=
  r.1.size = n ∧ ∃ g, St env s0 g t s ∧ (∀ i, ¬ Tmp i → g i = wrA g0 co r.1 i) ∧ g eSC = r.2

/-- The loop's invariant after `k` rounds. -/
def SCInv (env : Env) (s0 : QState) (g0 : Nat → EW) (co : Nat) (eqm : Bool) (np : Nat) (k : Nat)
    (acc : Array EW × EW) (t : TState) (s : QState) : Prop :=
  acc.1.size = k ∧ k ≤ scrN ∧ ∃ g, St env s0 g t s ∧ (∀ i, ¬ Tmp i → g i = wrA g0 co acc.1 i) ∧
    g eRK = EW.ofK k.toUInt64 ∧ g eSC = acc.2 ∧ g ePtN = EW.ofK np.toUInt64 ∧
    s.reg .r15 = k.toUInt64 ∧ (eqm = true → s.reg .r13 = np.toUInt64)

theorem scinv_succ {co k np : Nat} {eqm : Bool} {acc : Array EW × EW} {g : Nat → EW}
    (hsz : acc.1.size = k) (hk : k < scrN) (hag : ∀ i, ¬ Tmp i → g i = wrA g0 co acc.1 i)
    (hpn : g ePtN = EW.ofK np.toUInt64) {acc' : Array EW × EW} {t : TState} {s : QState}
    (h : RPost env s0 g co k np eqm acc.1 acc' t s) :
    SCInv env s0 g0 co eqm np (k + 1) acc' t s := by
  obtain ⟨ch, h1, g', hst, hag', hrk, hsc, hpn', h15, h13⟩ := h
  refine ⟨by rw [h1, Array.size_push, hsz], hk, g', hst, fun i hi ↦ ?_, hrk, hsc, hpn'.trans hpn, h15,
    h13⟩
  rw [hag' i hi, h1, ← wrA_push, hsz]
  by_cases hik : i = co + k
  · subst hik; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hik, Function.update_of_ne hik, hag i hi]

theorem zeroEW : (⟨Int64.toUInt64 0, Int64.toUInt64 0⟩ : EW) = EW.ofK (0 : Nat).toUInt64 := rfl

theorem ltu_imm {s : QState} {k n : Nat} (h15 : s.reg .r15 = k.toUInt64) (hk : k < 2 ^ 63)
    (hn : n < 2 ^ 63) :
    (Cond.cmp .ltu .r15 (.imm (Int64.ofNat n))).eval s = true ↔ k < n := by
  simp only [Cond.eval, h15, Rhs.eval, decide_eq_true_eq]
  rw [show (Int64.ofNat n).toUInt64 = n.toUInt64 from rfl]
  exact toUInt64_lt' (by omega) (by omega)

theorem ltu_reg {s : QState} {k n : Nat} (h15 : s.reg .r15 = k.toUInt64) (h13 : s.reg .r13 = n.toUInt64)
    (hk : k < 2 ^ 63) (hn : n < 2 ^ 63) :
    (Cond.cmp .ltu .r15 (.reg .r13)).eval s = true ↔ k < n := by
  simp only [Cond.eval, h15, Rhs.eval, h13, decide_eq_true_eq]
  exact toUInt64_lt' (by omega) (by omega)

variable (env inp s0)

/-- `scInit`: the round cleared. -/
theorem scInit_spec (hin : Inputs env inp s0.mem) {xs : List Stmt} {P E : QState → Prop}
    (h : St env s0 g t s)
    (k : ∀ s', St env s0 (Function.update g eRK (EW.ofK (0 : Nat).toUInt64)) t s' →
      s'.reg .r15 = (0 : Nat).toUInt64 → WP (blk xs) s' P E) :
    WP (blk (scInit ++ xs)) s P E := by
  obtain ⟨hc, hb, hp, hs⟩ := h
  unfold scInit
  simp only [List.cons_append, List.nil_append]
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  have hp1 : (s.setReg .r15 (Int64.toUInt64 0)).reg .rbp = sb env := by simpa using hp
  have hs1 : Scr (s.setReg .r15 (Int64.toUInt64 0)).mem (sb env) g := hs.congr fun _ _ ↦ rfl
  refine NativeVm.Transcript.wp_storei (eval_el hp1 _) (by rw [(hs1 _ (by p6_omega)).1]; rfl) ?_
  refine NativeVm.Transcript.wp_storei (eval_el (by simpa using hp1) _)
    (by
      simp only [QState.setMem_mem]
      split
      · rfl
      · rw [(hs1 _ (by p6_omega)).2]; rfl) ?_
  have hS := hs1.store (k := eRK) (by p6_omega) ⟨Int64.toUInt64 0, Int64.toUInt64 0⟩
  rw [← mem_setMem, ← mem_setMem] at hS
  rw [zeroEW] at hS
  refine k _ (St.mk' hin ⟨hc, hb, hp, hs⟩ hS (fun a ha ↦ ?_) rfl (by simp)) (by simp; rfl)
  rw [mem_setMem, mem_setMem]
  exact store_out ha (by p6_omega) ⟨Int64.toUInt64 0, Int64.toUInt64 0⟩

theorem sumcheck_list (claim : EW) (c : Nat) (eqs : Array (Option EW)) :
    Model.sumcheck claim c eqs = eqs.toList.foldlM (fun (acc : Array EW × EW) equality ↦ do
      let message ← sumcheckRoundPoly c acc.2 equality
      let challenge ← Model.sampleChallenge
      pure (acc.1.push challenge, polyEval message challenge)) (#[], claim) := by
  rw [Model.sumcheck, Array.foldlM_toList]

/-- **Plain mode**: `scP c co n` refines `sumcheckPlain claim c n`. -/
theorem scP_refines (hin : Inputs env inp s0.mem) {c co n np : Nat} (hc : 2 ≤ c ∧ c ≤ 4)
    (hco : 28 ≤ co) (hn : co + n ≤ scrN) (claim : EW) (g0 : Nat → EW)
    (hsc : g0 eSC = claim) (hnp : g0 ePtN = EW.ofK np.toUInt64) :
    Refines (St env s0 g0) (scP c co n) (sumcheckPlain claim c n) (SCPost env s0 g0 co n)
      (Kept env rs6 s0) := by
  have hN := scrN_lt
  have hagree : ∀ i, ¬ Tmp i → Function.update g0 eRK (EW.ofK (0 : Nat).toUInt64) i =
      wrA g0 co #[] i := fun i hi ↦ by
    rw [wrA_empty, Function.update_of_ne (by unfold Tmp at hi; omega)]
  have hm : sumcheckPlain claim c n = (List.replicate n (none : Option EW)).foldlM
      (fun (acc : Array EW × EW) equality ↦ do
        let message ← sumcheckRoundPoly c acc.2 equality
        let challenge ← Model.sampleChallenge
        pure (acc.1.push challenge, polyEval message challenge)) (#[], claim) := by
    rw [sumcheckPlain, sumcheck_list, Array.toList_replicate]
  rw [hm]
  intro t s h
  unfold scP
  refine scInit_spec env inp s0 hin h fun s1 h1 h15 ↦ ?_
  refine WP.mono (Refines.foldlM (l := List.replicate n (none : Option EW))
    (Inv := SCInv env s0 g0 co false np) (init := ((#[] : Array EW), claim))
    (fun k acc t s ⟨_, hk, g, _, _, _, _, _, h15, _⟩ ↦ by
      rw [List.length_replicate]
      exact ltu_imm h15 (by omega) (by omega)) ?_ t s1
    ⟨rfl, Nat.zero_le _, _, h1, hagree, Function.update_self .., by rw [Function.update_of_ne (by p6_ne), hsc],
      by rw [Function.update_of_ne (by p6_ne), hnp], h15, fun h ↦ absurd h (by decide)⟩)
    (fun s' ⟨r, t', hr, hsz, _, g, hst, hag, _, hsc', _⟩ ↦
      ⟨r, t', hr, by rw [hsz, List.length_replicate], g, hst, hag, hsc'⟩) (fun _ h ↦ h)
  rintro k hk acc t s ⟨hsz, _, g, hst, hag, hrk, hsc', hpn, _, _⟩
  rw [List.length_replicate] at hk
  rw [List.getElem_replicate]
  refine Refines.of_run (fun t ↦ by rw [roundPM_eq hc]) (Refines.mono
    (roundP_refines env inp s0 hin hc hco (by omega) acc.2 acc.1 g hrk hpn hsc')
    (fun _ _ h ↦ h) (fun acc' t' s' h ↦ scinv_succ hsz (by omega) hag hpn h) (fun _ h ↦ h)) t s hst

/-- **Equality mode**: `scE c ePt` refines `sumcheck claim c (point.map some)`, the point at `ePt`,
its challenges written over it. -/
theorem scE_refines (hin : Inputs env inp s0.mem) {c : Nat} (hc : 1 ≤ c ∧ c ≤ 3) (claim : EW)
    (point : Array EW) (hpt : point.size < 32) (g0 : Nat → EW) (hsc : g0 eSC = claim)
    (hnp : g0 ePtN = EW.ofK point.size.toUInt64)
    (hp : ∀ i < point.size, g0 (ePt + i) = point.getD i 0) :
    Refines (St env s0 g0) (scE c ePt) (Model.sumcheck claim c (point.map some))
      (SCPost env s0 g0 ePt point.size) (Kept env rs6 s0) := by
  have hN := scrN_lt
  have hagree : ∀ i, ¬ Tmp i → Function.update g0 eRK (EW.ofK (0 : Nat).toUInt64) i =
      wrA g0 ePt #[] i := fun i hi ↦ by
    rw [wrA_empty, Function.update_of_ne (by unfold Tmp at hi; omega)]
  rw [sumcheck_list, Array.toList_map]
  intro t s h
  unfold scE
  refine scInit_spec env inp s0 hin h fun s1 h1 h15 ↦ ?_
  have hs1 := h1.2.2.2
  refine ld0 (p := sb env) h1.2.2.1 hs1 (by p6_omega) ?_
  rw [Function.update_of_ne (by p6_ne), hnp]
  have h1' := St.mk' (s' := s1.setReg .r13 (EW.ofK point.size.toUInt64).c0)
    (f' := Function.update g0 eRK (EW.ofK (0 : Nat).toUInt64)) hin h1
    (hs1.congr fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by simp) (by simp)
  refine WP.mono (Refines.foldlM (l := point.toList.map some)
    (Inv := SCInv env s0 g0 ePt true point.size) (init := ((#[] : Array EW), claim))
    (fun k acc t s ⟨_, hk, g, _, _, _, _, _, h15, h13⟩ ↦ by
      rw [List.length_map, Array.length_toList]
      exact ltu_reg h15 (h13 rfl) (by omega) (by omega)) ?_ t _
    ⟨rfl, Nat.zero_le _, _, h1', hagree, Function.update_self .., by
      rw [Function.update_of_ne (by p6_ne), hsc], by rw [Function.update_of_ne (by p6_ne), hnp],
      by simp [h15], fun _ ↦ by simp; rfl⟩)
    (fun s' ⟨r, t', hr, hsz, _, g, hst, hag, _, hsc', _⟩ ↦
      ⟨r, t', hr, by rw [hsz, List.length_map, Array.length_toList], g, hst, hag, hsc'⟩)
    (fun _ h ↦ h)
  rintro k hk acc t s ⟨hsz, _, g, hst, hag, hrk, hsc', hpn, _, _⟩
  rw [List.length_map, Array.length_toList] at hk
  rw [List.getElem_map, Array.getElem_toList]
  refine Refines.of_run (fun t ↦ by rw [roundEM_eq hc]) (Refines.mono
    (roundE_refines env inp s0 hin hc (by p6_omega) acc.2 point[k] acc.1 g (by omega) hrk hpn hsc' ?_)
    (fun _ _ h ↦ h) (fun acc' t' s' h ↦ scinv_succ hsz (by p6_omega) hag hpn h) (fun _ h ↦ h)) t s hst
  rw [hag _ (by unfold Tmp; p6_ne), wrA_out (by omega), hp k hk, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hk]
  rfl

end NativeVm.Code.P6
