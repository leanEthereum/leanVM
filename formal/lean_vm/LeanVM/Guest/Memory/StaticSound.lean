/-
  LeanVM.Guest.Memory.StaticSound

  The soundness of the static weight checker: a call site's bound bounds its callee's weight, a
  block's bound its path's callees', and a checked program's every valid tree weighs at most its
  certificate's bound.
-/

module

public import LeanVM.Guest.Memory.Static
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.Value.Tower

/-!
# Soundness of the static checker

`Tree.cost P α ω t`: the weight of `t`, plus, counting words (`α`), the `HeapBuf`s its paths
allocate; without, the weight (`cost_false`). `Bound P α cert ω t args`: what the certificate of
`t`'s function claims of `t` on `args` (`stat`: under its preconditions, `t` costs at most its
bound; `loop`: started at `g^a` with end `g^e`, `a < e`, at most `e - a` times its iteration's
bound). `siteB_sound`: a call site's bound bounds a callee tree satisfying `Bound`.
`blockB_sound`: a block's bound bounds the cost of its path's callees and its `HeapBuf`s. `chk_sound`: if every function of the program passes `chkFn`, every valid tree
satisfies `Bound`, by induction on the instances, a loop helper's iterations one at a time.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Arithmetic -/

theorem Aff.eval_add (a b : Aff) (args : List E) : (a.add b).eval args = a.eval args + b.eval args := by
  simp only [Aff.eval, Aff.add, List.map_append, List.sum_append]
  omega

theorem Aff.eval_scale (n : ℕ) (a : Aff) (args : List E) : (a.scale n).eval args = n * a.eval args := by
  simp only [Aff.eval, Aff.scale, List.map_map, Nat.mul_add]
  congr 1
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_apply]
  ring

theorem Aff.eval_mk_nil (c : ℕ) (args : List E) : (⟨c, []⟩ : Aff).eval args = c := by
  simp [Aff.eval]

theorem Aff.eval_le_of_leB {a b : Aff} (h : a.leB b = true) (args : List E) : a.eval args ≤ b.eval args := by
  simp only [Aff.leB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [Aff.eval, h.2]
  omega

theorem constOk_spec {w : E} {e : ℕ} (h : constOk w e = true) : w = ofK (gpow e) ∧ e < 2 ^ 20 := by
  simp only [constOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨he, h1⟩, h2⟩, h0⟩ := h
  have h0' : w.limb 0 = gpow e := by
    split at h0
    · rename_i h64
      rw [decide_eq_true_eq] at h0
      rw [h0, Parameters.gpow, g_pow_eq_ofBits h64]
    · rw [decide_eq_true_eq] at h0
      rw [h0, Pow.gpowW_eq he]
  refine ⟨E.ext fun i => ?_, he⟩
  rw [limb_ofK]
  fin_cases i
  · simpa using h0'
  · simpa using h1
  · simpa using h2

theorem logG_ofK {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (ofK (gpow e)) = e := logG_spec he

/-- Known constants hold: `σ v = g^e` below the order of `g`. -/
def EnvOk (σ : Val) (ρ : Env) : Prop := ∀ q ∈ ρ, σ q.1 = ofK (gpow q.2) ∧ q.2 < 2 ^ 64 - 1

theorem lookup_mem {ρ : List (V × ℕ)} {v : V} {e : ℕ} : vlookup v ρ = some e → (v, e) ∈ ρ := by
  induction ρ with
  | nil => simp [vlookup]
  | cons q l ih =>
    intro h
    simp only [vlookup] at h
    split_ifs at h with hq
    · cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
      rw [hq.2]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem vidx_get {v : V} : ∀ {ps : List V} {k j : ℕ}, vidx v ps k = some j → k ≤ j ∧ ps[j - k]? = some v
  | [], _, _, h => by simp [vidx] at h
  | p :: ps, k, j, h => by
      simp only [vidx] at h
      split_ifs at h with hq
      · cases h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
        simp [hq.2]
      · obtain ⟨h1, h2⟩ := vidx_get h
        refine ⟨by omega, ?_⟩
        rw [show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
        exact h2

section Cls

variable {σ : Val} {ρ : Env} {ps : List V} {args : List E}

theorem cls_pow (hρ : EnvOk σ ρ) {v : V} {e : ℕ} (h : cls ρ ps v = .pow e) :
    σ v = ofK (gpow e) ∧ e < 2 ^ 64 - 1 := by
  unfold cls at h
  split at h
  · rename_i e' he'
    cases h
    exact hρ _ (lookup_mem he')
  · split at h <;> cases h

theorem cls_param (hp : ps.map σ = args) {v : V} {k : ℕ} (h : cls ρ ps v = .param k) :
    σ v = args.getD k 0 := by
  unfold cls at h
  split at h
  · cases h
  · split at h
    · rename_i k' hk'
      cases h
      have := (vidx_get hk').2
      rw [Nat.sub_zero] at this
      rw [← hp, List.getD_eq_getElem?_getD, List.getElem?_map, this]
      rfl
    · cases h

/-- Bounds on exponents hold. -/
def BndOk (σ : Val) (args : List E) (β : BEnv) : Prop := ∀ q ∈ β, logG (σ q.1) ≤ q.2.eval args

/-- The constants and the bounds hold. -/
def Env2Ok (σ : Val) (args : List E) (ρ : Env × BEnv) : Prop := EnvOk σ ρ.1 ∧ BndOk σ args ρ.2

theorem blookup_mem {β : BEnv} {v : V} {b : Aff} : blookup v β = some b → (v, b) ∈ β := by
  induction β with
  | nil => intro h; cases h
  | cons q l ih =>
      intro h
      simp only [blookup] at h
      split_ifs at h with hq
      · cases h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
        rw [hq.2]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- **`logG` of a product by `g^c`**: at most `c` more (a non-power stays one). -/
theorem logG_mul_le (w : E) (c : ℕ) : logG (w * ofK (gpow c)) ≤ logG w + c := by
  classical
  have hmul : ∀ a b : K, ofK (a * b) = ofK a * ofK b := fun a b => map_mul (algebraMap K E) a b
  have hgp : ∀ a b : ℕ, ofK (gpow a) * ofK (gpow b) = ofK (gpow (a + b)) := by
    intro a b; rw [← hmul, gpow, gpow, gpow, pow_add]
  by_cases hw : ∃ e, w = ofK (gpow e)
  · have hs := Nat.find_spec hw
    have hlw : logG w = Nat.find hw := by rw [logG, dite_eq_left hw]
    rw [hlw]
    generalize Nat.find hw = n at hs
    have hp : ∃ e, w * ofK (gpow c) = ofK (gpow e) := ⟨n + c, by rw [hs, hgp]⟩
    rw [logG, dite_eq_left hp]
    exact Nat.find_min' hp (by rw [hs, hgp])
  · have hn : ¬ ∃ e, w * ofK (gpow c) = ofK (gpow e) := by
      rintro ⟨m, hm⟩
      apply hw
      refine ⟨m + ((2 ^ 64 - 1) * c - c), ?_⟩
      have h1 : ofK (gpow c) * ofK (gpow ((2 ^ 64 - 1) * c - c)) = 1 := by
        rw [hgp, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left c (by norm_num)), gpow, pow_mul,
          g_pow_card_sub_one, one_pow]
        exact map_one (algebraMap K E)
      calc w = w * (ofK (gpow c) * ofK (gpow ((2 ^ 64 - 1) * c - c))) := by rw [h1, mul_one]
        _ = (w * ofK (gpow c)) * ofK (gpow ((2 ^ 64 - 1) * c - c)) := by rw [mul_assoc]
        _ = ofK (gpow (m + ((2 ^ 64 - 1) * c - c))) := by rw [hm, hgp]
    rw [logG, dite_eq_right hn]
    exact Nat.zero_le _

theorem bnd_sound {ρ : Env × BEnv} (hρ : Env2Ok σ args ρ) (hp : ps.map σ = args) {v : V} {b : Aff}
    (h : bnd ρ ps v = some b) : logG (σ v) ≤ b.eval args := by
  unfold bnd at h
  split at h
  · rename_i b' hb'
    cases h
    exact hρ.2 _ (blookup_mem hb')
  · split at h
    · rename_i e he
      cases h
      obtain ⟨hv, heo⟩ := cls_pow hρ.1 he
      rw [hv, logG_ofK heo, Aff.eval_mk_nil]
    · rename_i k hk
      cases h
      rw [cls_param hp hk]
      simp [Aff.eval, argExp]
    · cases h

end Cls

/-! ## Sites -/

section Site

variable {σ : Val} {ρ : Env} {ps : List V} {args : List E} {a : List V}

theorem addAcc_some {x y : Option Acc} {r : Acc} (h : Option.addAcc x y = some r) :
    ∃ rx ry, x = some rx ∧ y = some ry ∧ r = rx.add ry := by
  cases x <;> cases y <;> simp [Option.addAcc] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem maxAcc_some {x y : Option Acc} {r : Acc} (h : Option.maxAcc x y = some r) :
    ∃ rx ry, x = some rx ∧ y = some ry ∧ r = rx.join ry := by
  cases x <;> cases y <;> simp [Option.maxAcc] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem join_eval_left (a b : Acc) (args : List E) : a.1.eval args ≤ (a.join b).1.eval args := by
  simp only [Acc.join, Aff.eval, List.map_append, List.sum_append]
  have := Nat.le_max_left a.1.c b.1.c
  omega

theorem join_eval_right (a b : Acc) (args : List E) : b.1.eval args ≤ (a.join b).1.eval args := by
  simp only [Acc.join, Aff.eval, List.map_append, List.sum_append]
  have := Nat.le_max_right a.1.c b.1.c
  omega

theorem argsPre_append {p q : List (ℕ × ℕ)} {x : List E} :
    ArgsPre (p ++ q) x ↔ ArgsPre p x ∧ ArgsPre q x := by
  simp only [ArgsPre, List.mem_append]
  exact ⟨fun h => ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩,
    fun h r hr => hr.elim (h.1 r) (h.2 r)⟩

theorem termB_sound (hρ : EnvOk σ ρ) (hp : ps.map σ = args) {q : ℕ × ℕ} {r : Acc}
    (h : termB ρ ps a q = some r) : q.2 * argExp (a.map σ) q.1 ≤ r.1.eval args ∧ r.2 = [] := by
  unfold termB at h
  split at h
  · rename_i v hv
    split at h
    · rename_i e he
      cases h
      obtain ⟨h1, h2⟩ := cls_pow hρ he
      simp only [argExp, List.getD_eq_getElem?_getD, List.getElem?_map, hv, Option.map_some,
        Option.getD_some, h1, logG_ofK h2, Aff.eval_mk_nil]
      exact ⟨le_refl _, trivial⟩
    · rename_i k hk
      cases h
      have := cls_param (ρ := ρ) hp hk
      simp only [argExp, List.getD_eq_getElem?_getD, List.getElem?_map, hv, Option.map_some,
        Option.getD_some, this, Aff.eval]
      simp
    · cases h
  · cases h

theorem preB_sound (hρ : EnvOk σ ρ) (hp : ps.map σ = args) {q : ℕ × ℕ} {r : Acc}
    (h : preB ρ ps a q = some r) (hpre : ArgsPre r.2 args) :
    (∃ b, q.2 < b ∧ b < 2 ^ 64 - 1 ∧ (a.map σ).getD q.1 0 = ofK (gpow b)) ∧ r.1.eval args = 0 := by
  unfold preB at h
  split at h
  · rename_i v hv
    have hget : (a.map σ).getD q.1 0 = σ v := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hv]
    split at h
    · rename_i e he
      split at h
      · rename_i hlt
        cases h
        obtain ⟨h1, -⟩ := cls_pow hρ he
        exact ⟨⟨e, hlt.1, hlt.2, by rw [hget, h1]⟩, Aff.eval_mk_nil 0 args⟩
      · cases h
    · rename_i k hk
      cases h
      obtain ⟨b, hb1, hb2, hb3⟩ := hpre _ List.mem_cons_self
      refine ⟨⟨b, hb1, hb2, by rw [hget, cls_param (ρ := ρ) hp hk]; exact hb3⟩, Aff.eval_mk_nil 0 args⟩
    · cases h
  · cases h

theorem sumB_terms (hρ : EnvOk σ ρ) (hp : ps.map σ = args) :
    ∀ (cs : List (ℕ × ℕ)) {r : Acc}, sumB (termB ρ ps a) cs = some r →
      (cs.map fun q => q.2 * argExp (a.map σ) q.1).sum ≤ r.1.eval args ∧ r.2 = []
  | [], r, h => by
      simp only [sumB, Option.some.injEq] at h; subst h
      simp [Aff.eval]
  | q :: cs, r, h => by
      simp only [sumB] at h
      obtain ⟨rx, ry, hx, hy, rfl⟩ := addAcc_some h
      obtain ⟨h1, h2⟩ := termB_sound hρ hp hx
      obtain ⟨h3, h4⟩ := sumB_terms hρ hp cs hy
      simp only [List.map_cons, List.sum_cons, Acc.add, Aff.eval_add, h2, h4, List.append_nil]
      exact ⟨by omega, trivial⟩

theorem sumB_pres (hρ : EnvOk σ ρ) (hp : ps.map σ = args) :
    ∀ (pre : List (ℕ × ℕ)) {r : Acc}, sumB (preB ρ ps a) pre = some r → ArgsPre r.2 args →
      ArgsPre pre (a.map σ) ∧ r.1.eval args = 0
  | [], r, h, _ => by
      simp only [sumB, Option.some.injEq] at h; subst h
      exact ⟨fun _ h => (List.not_mem_nil h).elim, by simp [Aff.eval]⟩
  | q :: pre, r, h, hr => by
      simp only [sumB] at h
      obtain ⟨rx, ry, hx, hy, rfl⟩ := addAcc_some h
      simp only [Acc.add] at hr
      rw [argsPre_append] at hr
      obtain ⟨h1, h2⟩ := preB_sound hρ hp hx hr.1
      obtain ⟨h3, h4⟩ := sumB_pres hρ hp pre hy hr.2
      refine ⟨fun q' hq' => ?_, by simp only [Acc.add, Aff.eval_add, h2, h4]⟩
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact h1
      · exact h3 q' hq'

theorem transB_sound (hρ : EnvOk σ ρ) (hp : ps.map σ = args) {pre : List (ℕ × ℕ)} {b : Aff}
    {r : Acc} (h : transB ρ ps a pre b = some r) (hr : ArgsPre r.2 args) :
    b.eval (a.map σ) ≤ r.1.eval args ∧ ArgsPre pre (a.map σ) := by
  unfold transB at h
  obtain ⟨r0, r12, h0, h12, rfl⟩ := addAcc_some h
  obtain ⟨r1, r2, h1, h2, rfl⟩ := addAcc_some h12
  cases h0
  simp only [Acc.add] at hr ⊢
  rw [argsPre_append, argsPre_append] at hr
  obtain ⟨t1, t2⟩ := sumB_terms hρ hp b.cs h1
  obtain ⟨p1, p2⟩ := sumB_pres hρ hp pre h2 hr.2.2
  refine ⟨?_, p1⟩
  simp only [Aff.eval_add, Aff.eval_mk_nil, p2]
  unfold Aff.eval at t1 ⊢
  omega

mutual
/-- **The cost of a call tree**: its weight and, counting words (`α`), the `HeapBuf`s its paths
allocate. -/
noncomputable def Tree.cost (P : Core.Program) (α : Bool) (ω : String → ℕ) : Tree → ℕ
  | t@(.node f σ _ kids) =>
      ω f + (if α then (allocs σ (t.events P)).sum else 0) + Tree.costKids P α ω kids
  | .phantom f _ => if α then ω f else 0

/-- The cost of a list of call trees. -/
noncomputable def Tree.costKids (P : Core.Program) (α : Bool) (ω : String → ℕ) : List Tree → ℕ
  | [] => 0
  | k :: ks => k.cost P α ω + Tree.costKids P α ω ks
end

mutual
theorem cost_false {P : Core.Program} {ω : String → ℕ} :
    ∀ t : Tree, t.cost P false ω = t.weight ω
  | .node f σ b kids => by
      rw [Tree.cost, Tree.weight, costKids_false kids]
      simp
  | .phantom .. => by rw [Tree.cost, Tree.weight]; rfl

theorem costKids_false {P : Core.Program} {ω : String → ℕ} :
    ∀ ks : List Tree, Tree.costKids P false ω ks = Tree.weightKids ω ks
  | [] => by rw [Tree.costKids, Tree.weightKids]
  | k :: ks => by rw [Tree.costKids, Tree.weightKids, cost_false k, costKids_false ks]
end

/-- A loop's end: its parameter 1, or `g^e`. -/
def endOf (endc : Option ℕ) (args : List E) : E :=
  match endc with
  | some e => ofK (gpow e)
  | none => args.getD 1 0

/-- **What a certificate claims of a tree** of its function on `args`. -/
def Bound (P : Core.Program) (α : Bool) (cert : String → Cert) (ω : String → ℕ) (t : Tree)
    (args : List E) : Prop :=
  match cert t.name with
  | .none => True
  | .stat pre b _ => ArgsPre pre args → t.cost P α ω ≤ b.eval args
  | .loop endc pre b _ => ∀ a0 e, args.getD 0 0 = ofK (gpow a0) → endOf endc args = ofK (gpow e) →
      a0 < e → e < 2 ^ 64 - 1 → ArgsPre pre args → t.cost P α ω ≤ (e - a0) * b.eval args

/-- **A call site's bound bounds its callee**, a tree satisfying its certificate. -/
theorem siteB_sound {P : Core.Program} {α : Bool} {cert : String → Cert} {ω : String → ℕ}
    (hρ : EnvOk σ ρ) (hp : ps.map σ = args)
    {g : String} {r : Acc} (h : siteB cert ρ ps g a = some r) (hr : ArgsPre r.2 args) {t : Tree}
    (hn : t.name = g) (hb : Bound P α cert ω t (a.map σ)) : t.cost P α ω ≤ r.1.eval args := by
  unfold Bound at hb
  rw [hn] at hb
  unfold siteB at h
  cases hc : cert g with
  | none => rw [hc] at h; cases h
  | stat pre b ks =>
      rw [hc] at h hb
      obtain ⟨h1, h2⟩ := transB_sound hρ hp h hr
      exact (hb h2).trans h1
  | loop endc pre b ks =>
      rw [hc] at h hb
      simp only at h hb
      split at h
      · cases h
      · rename_i v0 hv0
        have hget0 : (a.map σ).getD 0 0 = σ v0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, hv0]
        split at h
        · rename_i a0 ha0
          obtain ⟨hs0, -⟩ := cls_pow hρ ha0
          split at h
          · rename_i e he
            split at h
            · rename_i hlt
              obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.mp h
              have hend : endOf endc (a.map σ) = ofK (gpow e) := by
                revert he
                cases endc with
                | some e' => intro he; cases he; rfl
                | none =>
                    intro he
                    simp only at he
                    split at he
                    · rename_i v1 hv1
                      have := (cls_pow hρ he).1
                      simp [endOf, List.getD_eq_getElem?_getD, List.getElem?_map, hv1, this]
                    · cases he
              obtain ⟨t1, t2⟩ := transB_sound hρ hp hR hr
              have := hb a0 e (by rw [hget0, hs0]) hend hlt.1 hlt.2 t2
              rw [Aff.eval_scale]
              exact this.trans (Nat.mul_le_mul_left _ t1)
            · cases h
          · rename_i k hk
            split at h
            · rename_i R hR
              split at h
              · rename_i hcs
                cases h
                have hr' : ArgsPre ((k, a0) :: R.2) args := hr
                obtain ⟨eb, heb1, heb2, heb3⟩ := hr' _ List.mem_cons_self
                simp only at heb1 heb3
                have hR2 : ArgsPre R.2 args := fun q hq => hr' q (List.mem_cons_of_mem _ hq)
                have hend : endOf endc (a.map σ) = ofK (gpow eb) := by
                  revert hk
                  cases endc with
                  | some e' => intro hk; cases hk
                  | none =>
                      intro hk
                      simp only at hk
                      split at hk
                      · rename_i v1 hv1
                        have := cls_param (ρ := ρ) hp hk
                        have h1 : (a.map σ).getD 1 0 = σ v1 := by
                          simp [List.getD_eq_getElem?_getD, List.getElem?_map, hv1]
                        simp only [endOf]
                        rw [h1, this, heb3]
                      · cases hk
                obtain ⟨t1, t2⟩ := transB_sound hρ hp hR hR2
                have := hb a0 eb (by rw [hget0, hs0]) hend heb1 heb2 t2
                have hRc : R.1.eval args = R.1.c := by simp [Aff.eval, hcs]
                rw [hRc] at t1
                have hev : (⟨0, [(k, R.1.c)]⟩ : Aff).eval args = R.1.c * eb := by
                  simp only [Aff.eval, argExp, heb3, logG_ofK heb2, List.map_cons, List.map_nil,
                    List.sum_cons, List.sum_nil]
                  omega
                rw [hev]
                calc t.cost P α ω ≤ (eb - a0) * b.eval (a.map σ) := this
                  _ ≤ (eb - a0) * R.1.c := Nat.mul_le_mul_left _ t1
                  _ ≤ eb * R.1.c := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                  _ = R.1.c * eb := Nat.mul_comm _ _
              · cases h
            · cases h
          · cases h
        · cases h

end Site

/-! ## Blocks -/

section Block

variable {P : Core.Program} {rd : Reader} {σ : Val} {cert : String → Cert} {ω : String → ℕ}
  {α : Bool}

/-- Every event holds. -/
def HoldsAll (rd : Reader) (σ : Val) (es : List Ev) : Prop := ∀ e ∈ es, e.Holds rd σ

/-- The words a path's `HeapBuf`s take, counting words. -/
noncomputable def aw (α : Bool) (σ : Val) (es : List Ev) : ℕ := if α then (allocs σ es).sum else 0

theorem aw_append (es es' : List Ev) : aw α σ (es ++ es') = aw α σ es + aw α σ es' := by
  unfold aw allocs
  split_ifs <;> simp [List.filterMap_append]

theorem aw_nil : aw α σ [] = 0 := by unfold aw allocs; split_ifs <;> rfl

theorem aw_cons_none {e : Ev} (he : e.alloc? σ = none) (es : List Ev) : aw α σ (e :: es) = aw α σ es := by
  unfold aw allocs
  split_ifs <;> simp [he]

variable (P α rd σ cert ω) in
/-- **The callees of a path cost at most `X`, with its `HeapBuf`s**, every callee satisfying its
certificate. -/
def KB (es : List Ev) (X : ℕ) : Prop :=
  ∀ kids, Tree.KidsValid P rd σ (calls es) kids → Tree.BufsOkKids P kids →
    (∀ k ∈ kids, ∀ args' rets', k.Valid P rd args' rets' → k.BufsOk P → Bound P α cert ω k args') →
      Tree.costKids P α ω kids + aw α σ es ≤ X

theorem bufsOkKids_split : ∀ (ks ks' : List Tree),
    Tree.BufsOkKids P (ks ++ ks') → Tree.BufsOkKids P ks ∧ Tree.BufsOkKids P ks'
  | [], _, h => ⟨by rw [Tree.BufsOkKids]; trivial, h⟩
  | k :: ks, ks', h => by
      rw [List.cons_append, Tree.BufsOkKids] at h
      obtain ⟨h1, h2⟩ := bufsOkKids_split ks ks' h.2
      exact ⟨by rw [Tree.BufsOkKids]; exact ⟨h.1, h1⟩, h2⟩

theorem kidsValid_split : ∀ {cs cs' : List Call} {ks : List Tree},
    Tree.KidsValid P rd σ (cs ++ cs') ks →
      ∃ ks₁ ks₂, ks = ks₁ ++ ks₂ ∧ Tree.KidsValid P rd σ cs ks₁ ∧ Tree.KidsValid P rd σ cs' ks₂
  | [], _, ks, h => ⟨[], ks, rfl, by simp [Tree.KidsValid], h⟩
  | c :: cs, cs', [], h => h.elim
  | c :: cs, cs', k :: ks, ⟨hn, hc, h⟩ => by
      obtain ⟨ks₁, ks₂, rfl, h1, h2⟩ := kidsValid_split h
      exact ⟨k :: ks₁, ks₂, rfl, ⟨hn, hc, h1⟩, h2⟩

theorem costKids_append (ks ks' : List Tree) :
    Tree.costKids P α ω (ks ++ ks') = Tree.costKids P α ω ks + Tree.costKids P α ω ks' := by
  induction ks with
  | nil => rw [List.nil_append, Tree.costKids]; omega
  | cons k ks ih => rw [List.cons_append, Tree.costKids, Tree.costKids, ih]; omega

theorem KB_mono {es : List Ev} {X Y : ℕ} (h : KB P rd σ cert ω α es X) (hXY : X ≤ Y) :
    KB P rd σ cert ω α es Y := fun kids hk ho hb => (h kids hk ho hb).trans hXY

theorem KB_nil (X : ℕ) : KB P rd σ cert ω α [] X := fun kids hk _ _ => by
  cases kids with
  | nil => rw [Tree.costKids, aw_nil]; omega
  | cons _ _ => exact hk.elim

theorem KB_append {es es' : List Ev} {X Y : ℕ} (h : KB P rd σ cert ω α es X)
    (h' : KB P rd σ cert ω α es' Y) : KB P rd σ cert ω α (es ++ es') (X + Y) := fun kids hk ho hb => by
  rw [calls_append] at hk
  obtain ⟨ks₁, ks₂, rfl, h1, h2⟩ := kidsValid_split hk
  obtain ⟨ho1, ho2⟩ := bufsOkKids_split ks₁ ks₂ ho
  rw [costKids_append, aw_append]
  have := Nat.add_le_add (h ks₁ h1 ho1 fun k hk' => hb k (List.mem_append_left _ hk'))
    (h' ks₂ h2 ho2 fun k hk' => hb k (List.mem_append_right _ hk'))
  omega

theorem KB_nocall {es : List Ev} (hc : calls es = []) (ha : aw α σ es = 0) (X : ℕ) :
    KB P rd σ cert ω α es X := by
  intro kids hk ho hb
  rw [hc] at hk
  have := KB_nil (P := P) (α := α) (rd := rd) (σ := σ) (cert := cert) (ω := ω) X kids
    (by simpa [calls] using hk) ho hb
  rw [aw_nil] at this
  rw [ha]
  exact this

theorem KB_seq {o k : Out} {X Y : ℕ} (hh : HoldsAll rd σ (o.seq k).evs)
    (h1 : HoldsAll rd σ o.evs → KB P rd σ cert ω α o.evs X)
    (h2 : ∀ es, o = .fall es → HoldsAll rd σ es → HoldsAll rd σ k.evs → KB P rd σ cert ω α k.evs Y) :
    KB P rd σ cert ω α (o.seq k).evs (X + Y) := by
  cases o with
  | fall es =>
      cases k with
      | fall es' =>
          simp only [Out.seq, Out.pre, Out.evs] at hh ⊢
          have ha : HoldsAll rd σ es := fun e he => hh e (List.mem_append_left _ he)
          have hb : HoldsAll rd σ es' := fun e he => hh e (List.mem_append_right _ he)
          exact KB_append (h1 ha) (h2 es rfl ha hb)
      | ret es' vs =>
          simp only [Out.seq, Out.pre, Out.evs] at hh ⊢
          have ha : HoldsAll rd σ es := fun e he => hh e (List.mem_append_left _ he)
          have hb : HoldsAll rd σ es' := fun e he => hh e (List.mem_append_right _ he)
          exact KB_append (h1 ha) (h2 es rfl ha hb)
      | stuck => simp only [Out.seq, Out.pre, Out.evs]; exact KB_nil _
  | ret es vs =>
      simp only [Out.seq, Out.evs] at hh ⊢
      exact KB_mono (h1 hh) (Nat.le_add_right _ _)
  | stuck => simp only [Out.seq, Out.evs]; exact KB_nil _

theorem KB_pre {o : Out} {c : V} {X : ℕ} (hh : HoldsAll rd σ (o.pre [.inK c]).evs)
    (h : HoldsAll rd σ o.evs → KB P rd σ cert ω α o.evs X) : KB P rd σ cert ω α (o.pre [.inK c]).evs X := by
  cases o with
  | fall es =>
      simp only [Out.pre, Out.evs, List.singleton_append] at hh ⊢
      have := h fun e he => hh e (List.mem_cons_of_mem _ he)
      intro kids hk ho hb
      rw [aw_cons_none rfl]
      exact this kids (by simpa [calls, Ev.call?, Out.evs, List.filterMap_cons] using hk) ho hb
  | ret es vs =>
      simp only [Out.pre, Out.evs, List.singleton_append] at hh ⊢
      have := h fun e he => hh e (List.mem_cons_of_mem _ he)
      intro kids hk ho hb
      rw [aw_cons_none rfl]
      exact this kids (by simpa [calls, Ev.call?, Out.evs, List.filterMap_cons] using hk) ho hb
  | stuck => simp only [Out.pre, Out.evs]; exact KB_nil _

theorem pick_cases {x : V} {a r : List V} : ∀ (gs : List String) (j : ℕ),
    pick σ x a r j gs = .stuck ∨ ∃ g ∈ gs, pick σ x a r j gs = .fall [.call g a r]
  | [], _ => Or.inl rfl
  | g :: gs, j => by
      unfold pick
      split_ifs
      · exact Or.inr ⟨g, List.mem_cons_self, rfl⟩
      · rcases pick_cases gs (j + 1) with h | ⟨g', hg', h⟩
        · exact Or.inl h
        · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', h⟩

theorem sumB_mem {α : Type} {f : α → Option Acc} {args : List E} :
    ∀ {l : List α} {R : Acc}, sumB f l = some R → ∀ a ∈ l,
      ∃ Ra, f a = some Ra ∧ Ra.1.eval args ≤ R.1.eval args ∧ (ArgsPre R.2 args → ArgsPre Ra.2 args)
  | [], _, _, _, ha => (List.not_mem_nil ha).elim
  | b :: l, R, h, a, ha => by
      simp only [sumB] at h
      obtain ⟨rx, ry, hx, hy, rfl⟩ := addAcc_some h
      simp only [Acc.add, Aff.eval_add]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨rx, hx, Nat.le_add_right _ _, fun h' => (argsPre_append.mp h').1⟩
      · obtain ⟨Ra, h1, h2, h3⟩ := sumB_mem hy a ha
        exact ⟨Ra, h1, by omega, fun h' => h3 (argsPre_append.mp h').2⟩

theorem maxB_mem {α : Type} {f : α → Option Acc} {args : List E} :
    ∀ {l : List α} {R : Acc}, maxB f l = some R → ∀ a ∈ l,
      ∃ Ra, f a = some Ra ∧ Ra.1.eval args ≤ R.1.eval args ∧ (ArgsPre R.2 args → ArgsPre Ra.2 args)
  | [], _, _, _, ha => (List.not_mem_nil ha).elim
  | b :: l, R, h, a, ha => by
      simp only [maxB] at h
      obtain ⟨rx, ry, hx, hy, rfl⟩ := maxAcc_some h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨rx, hx, join_eval_left _ _ _, fun h' => (argsPre_append.mp h').1⟩
      · obtain ⟨Ra, h1, h2, h3⟩ := maxB_mem hy a ha
        exact ⟨Ra, h1, h2.trans (join_eval_right _ _ _), fun h' => h3 (argsPre_append.mp h').2⟩

/-- A call site's callee: its bound bounds the callee of one frame. -/
theorem KB_site {ρ : Env} {ps : List V} {args : List E} (hρ : EnvOk σ ρ) (hp : ps.map σ = args)
    {g : String} {a r : List V} {t : Bool} {R : Acc} (h : siteB cert ρ ps g a = some R)
    (hr : ArgsPre R.2 args) {es : List Ev} (hc : calls es = [⟨g, a, r, t⟩]) (ha : aw α σ es = 0)
    {Y : ℕ} (hY : t = false → (if α then ω g else 0) ≤ Y) :
    KB P rd σ cert ω α es (R.1.eval args + Y) := by
  intro kids hk ho hb
  rw [hc] at hk
  rw [ha]
  match kids, hk with
  | [k], ⟨hn, hkv, _⟩ =>
      rw [Tree.costKids, Tree.costKids]
      simp only at hn hkv
      simp only [Tree.BufsOkKids] at ho
      by_cases ht : t = true
      · rw [ite_eq_left ht] at hkv
        have := siteB_sound hρ hp h hr hn (hb k List.mem_cons_self _ _ hkv ho.1)
        omega
      · rw [ite_eq_right ht] at hkv
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hkv
        simp only [Tree.name] at hn
        subst hn
        have := hY (by simpa using ht)
        rw [Tree.cost]
        omega

variable {ks : List (V × ℕ)} {ps : List V} {self : String} {args : List E} {wl : String → Option ℕ}

/-- **A phantom's bound bounds its frame**, counting words. -/
theorem phB_sound (hwl : WlOk wl ω) {g : String} {r : Acc} (h : phB wl α g = some r) :
    (if α then ω g else 0) ≤ r.1.eval args := by
  unfold phB at h
  cases α with
  | false => simp
  | true =>
      simp only [↓reduceIte, Option.map_eq_some_iff] at h ⊢
      obtain ⟨n, hn, rfl⟩ := h
      simpa [Aff.eval] using hwl g n hn

/-- **An atom's bound bounds its `HeapBuf`**, and keeps the constants and the bounds true. -/
theorem atomB_sound {ρ ρ' : Env × BEnv} {a : Atom} {r : Acc} (hρ : Env2Ok σ args ρ)
    (hp : ps.map σ = args) (h : atomB α ks ps ρ a = some (r, ρ')) (hh : (Ev.atom a).Holds rd σ) :
    Env2Ok σ args ρ' ∧ r.2 = [] ∧ aw α σ [.atom a] ≤ r.1.eval args := by
  cases a with
  | const v w =>
      simp only [atomB] at h
      have ha : aw α σ [.atom (.const v w)] = 0 := by rw [aw_cons_none rfl, aw_nil]
      rw [ha]
      split at h
      · rename_i e he
        split at h
        · rename_i hok
          cases h
          obtain ⟨hw, he20⟩ := constOk_spec hok
          have hv : σ v = w := hh
          refine ⟨⟨fun q hq => ?_, hρ.2⟩, rfl, Nat.zero_le _⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hv.trans hw, by omega⟩
          · exact hρ.1 q hq
        · cases h; exact ⟨hρ, rfl, Nat.zero_le _⟩
      · cases h; exact ⟨hρ, rfl, Nat.zero_le _⟩
  | mul d x y =>
      simp only [atomB] at h
      have ha : aw α σ [.atom (.mul d x y)] = 0 := by rw [aw_cons_none rfl, aw_nil]
      rw [ha]
      split at h
      · split at h
        · rename_i b c hb hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨⟨hρ.1, fun q hq => ?_⟩, rfl, Nat.zero_le _⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · have hd : σ d = σ x * σ y := hh
            obtain ⟨hy, -⟩ := cls_pow hρ.1 hc
            rw [hd, hy]
            have := bnd_sound hρ hp hb
            simp only [Aff.eval_add, Aff.eval_mk_nil]
            exact (logG_mul_le _ _).trans (by omega)
          · exact hρ.2 q hq
        · cases h
      · cases h; exact ⟨hρ, rfl, Nat.zero_le _⟩
  | hint hn =>
      cases hn with
      | alloc d n =>
          simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hρ, by split_ifs <;> rfl, ?_⟩
          cases α <;> simp [aw, allocs, Ev.alloc?, Acc.zero, Aff.eval]
      | allocDyn d sz =>
          cases α with
          | false =>
              simp only [atomB, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨hρ, rfl, by simp [aw]⟩
          | true =>
              simp only [atomB, ↓reduceIte] at h
              split at h
              · rename_i b hb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨hρ, rfl, ?_⟩
                simpa [aw, allocs, Ev.alloc?] using bnd_sound hρ hp hb
              · cases h
      | _ =>
          simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hρ, rfl, by rw [aw_cons_none rfl, aw_nil]; exact Nat.zero_le _⟩
  | _ =>
      simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hρ, rfl, by rw [aw_cons_none rfl, aw_nil]; exact Nat.zero_le _⟩

mutual
/-- **A block's bound bounds its path's callees.** -/
theorem blockB_sound (hp : ps.map σ = args) (hwl : WlOk wl ω) : ∀ (ss : List Stmt) (ρ : Env × BEnv) (r : Acc),
    Env2Ok σ args ρ →
    blockB cert wl α ks ps self ρ ss = some r → ArgsPre r.2 args → HoldsAll rd σ (walk σ ss).evs →
      KB P rd σ cert ω α (walk σ ss).evs (r.1.eval args)
  | [], _, _, _, _, _, _ => by rw [walk]; exact KB_nil _
  | s :: ss, ρ, r, hρ, h, hr, hh => by
      rw [walk] at hh ⊢
      cases s with
      | atom a =>
          simp only [blockB] at h
          split at h
          · rename_i r1 ρ' hab
            obtain ⟨r2, rr, h2, hrr, rfl⟩ := addAcc_some h
            cases h2
            simp only [Acc.add, argsPre_append] at hr
            simp only [Acc.add, Aff.eval_add]
            refine KB_seq hh (fun h1 => ?_) fun es he h1 h2 => ?_
            · simp only [walk1, Out.evs] at h1 ⊢
              obtain ⟨-, -, hw⟩ := atomB_sound hρ hp hab (h1 _ List.mem_cons_self)
              intro kids hk _ hb
              cases kids with
              | nil => rw [Tree.costKids]; omega
              | cons _ _ => rw [show calls [Ev.atom a] = [] from rfl] at hk; exact hk.elim
            · simp only [walk1, Out.fall.injEq] at he
              subst he
              obtain ⟨hρ', -, -⟩ := atomB_sound hρ hp hab (h1 _ List.mem_cons_self)
              exact blockB_sound hp hwl ss ρ' rr hρ' hrr hr.2 h2
          · cases h
      | ite c z n =>
          simp only [blockB] at h
          obtain ⟨rzn, rr, hzn, hrr, rfl⟩ := addAcc_some h
          obtain ⟨rz, rn, hz, hn, rfl⟩ := maxAcc_some hzn
          simp only [Acc.add, Acc.join, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KB_seq hh (fun h1 => ?_) fun es _ _ h2 => blockB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          rw [walk1] at h1 ⊢
          refine KB_pre h1 fun h1' => ?_
          split_ifs
          · rw [ite_eq_left (by assumption)] at h1'
            exact KB_mono (blockB_sound hp hwl z ρ rz hρ hz hr.1.1 h1') (join_eval_left _ _ _)
          · rw [ite_eq_right (by assumption)] at h1'
            exact KB_mono (blockB_sound hp hwl n ρ rn hρ hn hr.1.2 h1') (join_eval_right _ _ _)
      | match_ x arms =>
          simp only [blockB] at h
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KB_seq hh (fun h1 => ?_) fun es _ _ h2 => blockB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          rw [walk1] at h1 ⊢
          exact armsB_sound hp hwl x arms 0 ρ ra hρ ha hr.1 h1
      | call g a r' =>
          simp only [blockB] at h
          obtain ⟨rs, rr, hs, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KB_seq hh (fun _ => KB_mono (KB_site hρ.1 hp hs hr.1 (t := true) (r := r') ?_ ?_
            (Y := 0) fun h => absurd h (by decide)) (by omega))
            fun es _ _ h2 => blockB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          · simp [walk1, Out.evs, calls, Ev.call?]
          · simp only [walk1, Out.evs]; rw [aw_cons_none rfl, aw_nil]
      | callIf c g a =>
          simp only [blockB] at h
          split at h
          · cases h
          · obtain ⟨rs, rpr, hs, hpr, rfl⟩ := addAcc_some h
            obtain ⟨rph, rr, hph, hrr, rfl⟩ := addAcc_some hpr
            simp only [Acc.add, argsPre_append] at hr
            simp only [Acc.add, Aff.eval_add]
            rw [← Nat.add_assoc]
            refine KB_seq hh (fun _ => ?_) fun es _ _ h2 => blockB_sound hp hwl ss ρ rr hρ hrr hr.2.2 h2
            have hY := phB_sound (args := args) hwl hph
            by_cases h0 : σ c = 0
            · exact KB_site hρ.1 hp hs hr.1 (t := false) (r := []) (by
                simp only [walk1, Out.evs, h0, ↓reduceIte]; rfl)
                (by simp only [walk1, Out.evs, h0, ↓reduceIte]; rw [aw_cons_none rfl, aw_cons_none rfl, aw_nil])
                fun _ => hY
            · exact KB_site hρ.1 hp hs hr.1 (t := true) (r := []) (by
                simp only [walk1, Out.evs, h0, ↓reduceIte]; rfl)
                (by simp only [walk1, Out.evs, h0, ↓reduceIte]; rw [aw_cons_none rfl, aw_cons_none rfl, aw_nil])
                fun h => absurd h (by decide)
      | dispatch x gs a r' =>
          simp only [blockB] at h
          obtain ⟨rs, rr, hs, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KB_seq hh (fun _ => ?_) fun es _ _ h2 => blockB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          rw [walk1]
          rcases pick_cases (σ := σ) (x := x) (a := a) (r := r') gs 0 with hpk | ⟨g, hg, hpk⟩
          · rw [hpk]; exact KB_nil _
          · rw [hpk]
            obtain ⟨Rg, h1, h2, h3⟩ := maxB_mem (args := args) hs g hg
            exact KB_mono (KB_site hρ.1 hp h1 (h3 hr.1) (t := true) (r := r')
              (by simp [Out.evs, calls, Ev.call?]) (by simp only [Out.evs]; rw [aw_cons_none rfl, aw_nil])
              (Y := 0) fun h => absurd h (by decide)) (by omega)
      | ret vs =>
          simp only [walk1, Out.seq, Out.evs]
          exact KB_nil _

/-- `blockB_sound` for the arms of a `match`. -/
theorem armsB_sound (hp : ps.map σ = args) (hwl : WlOk wl ω) (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ)
    (ρ : Env × BEnv) (r : Acc), Env2Ok σ args ρ → armsB cert wl α ks ps self ρ arms = some r → ArgsPre r.2 args →
      HoldsAll rd σ (walkArms σ x j arms).evs → KB P rd σ cert ω α (walkArms σ x j arms).evs (r.1.eval args)
  | [], _, _, _, _, _, _, _ => by rw [walkArms]; exact KB_nil _
  | a :: as, j, ρ, r, hρ, h, hr, hh => by
      simp only [armsB] at h
      obtain ⟨ra, rs, ha, hs, rfl⟩ := maxAcc_some h
      simp only [Acc.join, argsPre_append] at hr
      unfold walkArms at hh ⊢
      split_ifs at hh ⊢
      · exact KB_mono (blockB_sound hp hwl a ρ ra hρ ha hr.1 hh) (join_eval_left _ _ _)
      · exact KB_mono (armsB_sound hp hwl x as (j + 1) ρ rs hρ hs hr.2 hh) (join_eval_right _ _ _)
end

end Block

/-! ## The recursor form -/

section Rec

variable {cert : String → Cert} {wl : String → Option ℕ} {α : Bool} {ks : List (V × ℕ)} {ps : List V}
  {self : String}

theorem Acc.zero_add (r : Acc) : Acc.zero.add r = r := by
  simp [Acc.zero, Acc.add, Aff.add]

theorem addAcc_assoc (a b c : Option Acc) :
    Option.addAcc (Option.addAcc a b) c = Option.addAcc a (Option.addAcc b c) := by
  cases a <;> cases b <;> cases c <;> simp [Option.addAcc, Acc.add, Aff.add, Nat.add_assoc]

theorem addAcc_some_zero (x : Option Acc) : Option.addAcc (some Acc.zero) x = x := by
  cases x <;> simp [Option.addAcc, Acc.zero_add]

theorem blockR_cons (s : Stmt) (ss : List Stmt) (ρ : Env × BEnv) :
    blockR cert wl α ks ps self (s :: ss) ρ = match stmtR cert wl α ks ps self s ρ with
      | none => none
      | some (r, some ρ') => Option.addAcc (some r) (blockR cert wl α ks ps self ss ρ')
      | some (r, none) => some r := rfl

theorem stmtR_ite (c : V) (z n : List Stmt) (ρ : Env × BEnv) :
    stmtR cert wl α ks ps self (.ite c z n) ρ =
      (Option.maxAcc (blockR cert wl α ks ps self z ρ) (blockR cert wl α ks ps self n ρ)).map fun r => (r, some ρ) :=
  rfl

theorem stmtR_match (x : V) (arms : List (List Stmt)) (ρ : Env × BEnv) :
    stmtR cert wl α ks ps self (.match_ x arms) ρ = (armsR cert wl α ks ps self arms ρ).map fun r => (r, some ρ) :=
  rfl

theorem armsR_cons (a : List Stmt) (as : List (List Stmt)) (ρ : Env × BEnv) :
    armsR cert wl α ks ps self (a :: as) ρ = Option.maxAcc (blockR cert wl α ks ps self a ρ) (armsR cert wl α ks ps self as ρ) :=
  rfl

mutual
/-- **The recursor form is `blockB`.** -/
theorem blockR_eq : ∀ (ss : List Stmt) (ρ : Env × BEnv), blockR cert wl α ks ps self ss ρ = blockB cert wl α ks ps self ρ ss
  | [], ρ => by rw [blockB]; rfl
  | s :: ss, ρ => by
      rw [blockR_cons]
      cases s with
      | atom a =>
          simp only [stmtR, blockB]
          cases atomB α ks ps ρ a with
          | none => rfl
          | some q => obtain ⟨r, ρ'⟩ := q; simp only [Option.map_some]; rw [blockR_eq]
      | ite c z n =>
          rw [stmtR_ite, blockR_eq z, blockR_eq n, blockB]
          cases Option.maxAcc (blockB cert wl α ks ps self ρ z) (blockB cert wl α ks ps self ρ n) with
          | none => rfl
          | some r => simp only [Option.map_some]; rw [blockR_eq]
      | match_ x arms =>
          rw [stmtR_match, armsR_eq arms, blockB]
          cases armsB cert wl α ks ps self ρ arms with
          | none => rfl
          | some r => simp only [Option.map_some]; rw [blockR_eq]
      | call g args rets =>
          simp only [stmtR, blockB]
          cases siteB cert ρ.1 ps g args with
          | none => rfl
          | some r => simp only [Option.map_some]; rw [blockR_eq]
      | callIf c g args =>
          simp only [stmtR, blockB]
          split_ifs
          · rfl
          · rw [← addAcc_assoc]
            cases Option.addAcc (siteB cert ρ.1 ps g args) (phB wl α g) with
            | none => rfl
            | some r => simp only [Option.map_some]; rw [blockR_eq]
      | dispatch x gs args rets =>
          simp only [stmtR, blockB]
          cases maxB (fun g => siteB cert ρ.1 ps g args) gs with
          | none => rfl
          | some r => simp only [Option.map_some]; rw [blockR_eq]
      | ret vs => simp only [stmtR, blockB]; rfl

/-- `blockR_eq` for arms. -/
theorem armsR_eq : ∀ (arms : List (List Stmt)) (ρ : Env × BEnv),
    armsR cert wl α ks ps self arms ρ = armsB cert wl α ks ps self ρ arms
  | [], ρ => by rw [armsB]; rfl
  | a :: as, ρ => by
      rw [armsR_cons, blockR_eq a, armsR_eq as, armsB]
end

end Rec

/-! ## Blocks in ranges -/

section Append

variable {cert : String → Cert} {wl : String → Option ℕ} {α : Bool} {ps : List V} {self : String}

/-- No top-level `ret`. -/
def noTopRet (l : List Stmt) : Bool := l.all fun s => match s with
  | .ret _ => false
  | _ => true

theorem blockB_nil (ρ : Env × BEnv) : blockB cert wl α [] ps self ρ [] = some Acc.zero := by rw [blockB]; rfl

theorem atomB_nil_env {ρ ρ' : Env × BEnv} {a : Atom} {r : Acc} (h : atomB α [] ps ρ a = some (r, ρ')) :
    ρ' = ρ := by
  cases a with
  | const v w => simp only [atomB, vlookup, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | mul d x y =>
      simp [atomB, vlookup] at h
      exact h.2.symm
  | hint hn =>
      cases hn with
      | allocDyn d sz =>
          simp only [atomB] at h
          split_ifs at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
            · cases h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
      | _ => simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | _ => simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm

/-- **A block without constants is the sum of its ranges**, the first without `ret`. -/
theorem blockB_append (ρ : Env × BEnv) : ∀ (l1 l2 : List Stmt), noTopRet l1 = true →
    blockB cert wl α [] ps self ρ (l1 ++ l2) =
      Option.addAcc (blockB cert wl α [] ps self ρ l1) (blockB cert wl α [] ps self ρ l2)
  | [], l2, _ => by rw [List.nil_append, blockB_nil, addAcc_some_zero]
  | s :: l1, l2, h => by
      simp only [noTopRet, List.all_cons, Bool.and_eq_true] at h
      have ih := blockB_append ρ l1 l2 h.2
      rw [List.cons_append]
      cases s with
      | atom a =>
          simp only [blockB]
          cases hq : atomB α [] ps ρ a with
          | none => rfl
          | some q =>
              obtain ⟨r, ρ'⟩ := q
              obtain rfl := atomB_nil_env hq
              simp only
              rw [ih, addAcc_assoc]
      | ite c z n => simp only [blockB]; rw [ih, addAcc_assoc]
      | match_ x arms => simp only [blockB]; rw [ih, addAcc_assoc]
      | call g a r => simp only [blockB]; rw [ih, addAcc_assoc]
      | callIf c g a =>
          simp only [blockB]
          split_ifs
          · rfl
          · rw [ih, addAcc_assoc, addAcc_assoc]
      | dispatch x gs a r => simp only [blockB]; rw [ih, addAcc_assoc]
      | ret vs => simp at h

/-- The ranges from `a` and from `a + n`, the first without `ret`. -/
theorem blockB_drop (ρ : Env × BEnv) (l : List Stmt) (a n : ℕ) (h : noTopRet ((l.drop a).take n) = true) :
    blockB cert wl α [] ps self ρ (l.drop a) =
      Option.addAcc (blockB cert wl α [] ps self ρ ((l.drop a).take n)) (blockB cert wl α [] ps self ρ (l.drop (a + n))) := by
  rw [← blockB_append ρ _ _ h, ← List.drop_drop, List.take_append_drop]

theorem blockB_drop' (ρ : Env × BEnv) (l : List Stmt) (a n b : ℕ) (h : noTopRet ((l.drop a).take n) = true)
    (hb : a + n = b) : blockB cert wl α [] ps self ρ (l.drop a) =
      Option.addAcc (blockB cert wl α [] ps self ρ ((l.drop a).take n)) (blockB cert wl α [] ps self ρ (l.drop b)) := by
  subst hb; exact blockB_drop ρ l a n h

end Append

/-! ## Lookups -/

section Look

variable {look cert : String → Cert} {wl : String → Option ℕ} {α : Bool} {ks : List (V × ℕ)} {ps : List V}
  {self : String}

theorem siteB_mono (hl : LookOk look cert) {ρ : Env} {g : String} {a : List V} {r : Acc}
    (h : siteB look ρ ps g a = some r) : siteB cert ρ ps g a = some r := by
  have hg : look g ≠ .none := by
    intro h0
    unfold siteB at h
    rw [h0] at h
    cases h
  unfold siteB at h ⊢
  rw [← hl g hg]
  exact h

theorem maxB_site_mono (hl : LookOk look cert) {ρ : Env} {a : List V} :
    ∀ {gs : List String} {r : Acc}, maxB (fun g => siteB look ρ ps g a) gs = some r →
      maxB (fun g => siteB cert ρ ps g a) gs = some r
  | [], _, h => h
  | g :: gs, r, h => by
      simp only [maxB] at h ⊢
      obtain ⟨rx, ry, hx, hy, rfl⟩ := maxAcc_some h
      rw [siteB_mono hl hx, maxB_site_mono hl hy]
      rfl

mutual
/-- **A block checked by a lookup is checked by `cert`.** -/
theorem blockB_mono (hl : LookOk look cert) : ∀ (ss : List Stmt) (ρ : Env × BEnv) {r : Acc},
    blockB look wl α ks ps self ρ ss = some r → blockB cert wl α ks ps self ρ ss = some r
  | [], _, _, h => by rw [blockB] at h ⊢; exact h
  | s :: ss, ρ, r, h => by
      cases s with
      | atom a =>
          simp only [blockB] at h ⊢
          split at h
          · rename_i r1 ρ' hab
            obtain ⟨r2, rr, h2, hrr, rfl⟩ := addAcc_some h
            cases h2
            rw [blockB_mono hl ss ρ' hrr]
            rfl
          · cases h
      | ite c z n =>
          simp only [blockB] at h ⊢
          obtain ⟨rzn, rr, hzn, hrr, rfl⟩ := addAcc_some h
          obtain ⟨rz, rn, hz, hn, rfl⟩ := maxAcc_some hzn
          rw [blockB_mono hl z ρ hz, blockB_mono hl n ρ hn, blockB_mono hl ss ρ hrr]
          rfl
      | match_ x arms =>
          simp only [blockB] at h ⊢
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          rw [armsB_mono hl arms ρ ha, blockB_mono hl ss ρ hrr]
          rfl
      | call g a rets =>
          simp only [blockB] at h ⊢
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          rw [siteB_mono hl ha, blockB_mono hl ss ρ hrr]
          rfl
      | callIf c g a =>
          simp only [blockB] at h ⊢
          split at h
          · cases h
          · rw [ite_eq_right (by assumption)]
            obtain ⟨ra, rpr, ha, hpr, rfl⟩ := addAcc_some h
            obtain ⟨rph, rr, hph, hrr, rfl⟩ := addAcc_some hpr
            rw [siteB_mono hl ha, hph, blockB_mono hl ss ρ hrr]
            rfl
      | dispatch x gs a rets =>
          simp only [blockB] at h ⊢
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          rw [maxB_site_mono hl ha, blockB_mono hl ss ρ hrr]
          rfl
      | ret vs => simp only [blockB] at h ⊢; exact h

/-- `blockB_mono` for arms. -/
theorem armsB_mono (hl : LookOk look cert) : ∀ (arms : List (List Stmt)) (ρ : Env × BEnv) {r : Acc},
    armsB look wl α ks ps self ρ arms = some r → armsB cert wl α ks ps self ρ arms = some r
  | [], _, _, h => by rw [armsB] at h ⊢; exact h
  | a :: as, ρ, r, h => by
      simp only [armsB] at h ⊢
      obtain ⟨ra, rr, ha, hrr, rfl⟩ := maxAcc_some h
      rw [blockB_mono hl a ρ ha, armsB_mono hl as ρ hrr]
      rfl
end

end Look

/-! ## Loop helpers -/

section Loop

variable {σ : Val}

theorem Out.seq_assoc : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_append : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_append l l', Out.seq_assoc]

theorem pick_noRet {x : V} {a r : List V} (gs : List String) (j : ℕ) :
    (∃ es, pick σ x a r j gs = .fall es) ∨ pick σ x a r j gs = .stuck := by
  rcases pick_cases (σ := σ) (x := x) (a := a) (r := r) gs j with h | ⟨g, -, h⟩
  · exact Or.inr h
  · exact Or.inl ⟨_, h⟩

theorem pre_noRet {o : Out} {es : List Ev} (h : (∃ es', o = .fall es') ∨ o = .stuck) :
    (∃ es', o.pre es = .fall es') ∨ o.pre es = .stuck := by
  rcases h with ⟨es', rfl⟩ | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

theorem seq_noRet {o k : Out} (h : (∃ es, o = .fall es) ∨ o = .stuck)
    (h' : (∃ es, k = .fall es) ∨ k = .stuck) : (∃ es, o.seq k = .fall es) ∨ o.seq k = .stuck := by
  rcases h with ⟨es, rfl⟩ | rfl
  · exact pre_noRet h'
  · exact Or.inr rfl

mutual
/-- A block without `ret` falls through or is stuck. -/
theorem walk1_noRet : ∀ (s : Stmt), Stmt.noRet s = true →
    (∃ es, walk1 σ s = .fall es) ∨ walk1 σ s = .stuck
  | .atom _, _ => Or.inl ⟨_, rfl⟩
  | .ite c z n, h => by
      simp only [Stmt.noRet, Bool.and_eq_true] at h
      rw [walk1]
      split_ifs
      · exact pre_noRet (walk_noRet z h.1)
      · exact pre_noRet (walk_noRet n h.2)
  | .match_ x arms, h => by
      rw [walk1]
      exact walkArms_noRet x arms 0 h
  | .call .., _ => Or.inl ⟨_, rfl⟩
  | .callIf .., _ => Or.inl ⟨_, rfl⟩
  | .dispatch x gs a r, _ => by rw [walk1]; exact pick_noRet gs 0
  | .ret _, h => by simp [Stmt.noRet] at h

theorem walk_noRet : ∀ (ss : List Stmt), Stmt.noRetListS ss = true →
    (∃ es, walk σ ss = .fall es) ∨ walk σ ss = .stuck
  | [], _ => Or.inl ⟨[], rfl⟩
  | s :: ss, h => by
      simp only [Stmt.noRetListS, Bool.and_eq_true] at h
      rw [walk]
      exact seq_noRet (walk1_noRet s h.1) (walk_noRet ss h.2)

theorem walkArms_noRet (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.noRetArms arms = true →
    (∃ es, walkArms σ x j arms = .fall es) ∨ walkArms σ x j arms = .stuck
  | [], _, _ => Or.inr rfl
  | a :: as, j, h => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_noRet a h.1
      · exact walkArms_noRet x as (j + 1) h.2
end

/-- **A top-level atom of a block without `ret` is on its path.** -/
theorem atom_on_path {a : Atom} : ∀ {l : List Stmt} {es : List Ev}, Stmt.noRetListS l = true →
    walk σ l = .fall es → Stmt.atom a ∈ l → Ev.atom a ∈ es
  | [], _, _, _, hm => (List.not_mem_nil hm).elim
  | s :: l, es, hn, hw, hm => by
      simp only [Stmt.noRetListS, Bool.and_eq_true] at hn
      rw [walk] at hw
      rcases walk1_noRet (σ := σ) s hn.1 with ⟨es1, h1⟩ | h1
      · rw [h1] at hw
        rcases walk_noRet (σ := σ) l hn.2 with ⟨es2, h2⟩ | h2
        · rw [h2] at hw
          simp only [Out.seq, Out.pre, Out.fall.injEq] at hw
          subst hw
          rcases List.mem_cons.mp hm with rfl | hm
          · simp only [walk1, Out.fall.injEq] at h1
            subst h1
            exact List.mem_append_left _ List.mem_cons_self
          · exact List.mem_append_right _ (atom_on_path hn.2 h2 hm)
        · rw [h2] at hw; simp [Out.seq, Out.pre] at hw
      · rw [h1] at hw; simp [Out.seq] at hw

theorem defAtom_mem {d : V} {a : Atom} : ∀ {l : List Stmt}, defAtom d l = some a → Stmt.atom a ∈ l
  | [], h => by simp [defAtom] at h
  | .atom b :: l, h => by
      simp only [defAtom] at h
      split_ifs at h
      · cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (defAtom_mem h)
  | .ite .. :: l, h => List.mem_cons_of_mem _ (defAtom_mem (by simpa [defAtom] using h))
  | .match_ .. :: l, h => List.mem_cons_of_mem _ (defAtom_mem (by simpa [defAtom] using h))
  | .call .. :: l, h => List.mem_cons_of_mem _ (defAtom_mem (by simpa [defAtom] using h))
  | .callIf .. :: l, h => List.mem_cons_of_mem _ (defAtom_mem (by simpa [defAtom] using h))
  | .dispatch .. :: l, h => List.mem_cons_of_mem _ (defAtom_mem (by simpa [defAtom] using h))
  | .ret .. :: l, h => List.mem_cons_of_mem _ (defAtom_mem (by simpa [defAtom] using h))

theorem defAtom_mul {d x y z : V} : ∀ {l : List Stmt}, defAtom d l = some (.mul x y z) → x = d
  | [], h => by simp [defAtom] at h
  | .atom b :: l, h => by
      simp only [defAtom] at h
      split_ifs at h with hb
      · cases h; simpa using hb
      · exact defAtom_mul h
  | .ite .. :: l, h => defAtom_mul (by simpa [defAtom] using h)
  | .match_ .. :: l, h => defAtom_mul (by simpa [defAtom] using h)
  | .call .. :: l, h => defAtom_mul (by simpa [defAtom] using h)
  | .callIf .. :: l, h => defAtom_mul (by simpa [defAtom] using h)
  | .dispatch .. :: l, h => defAtom_mul (by simpa [defAtom] using h)
  | .ret .. :: l, h => defAtom_mul (by simpa [defAtom] using h)

theorem defAtom_add {d x y z : V} : ∀ {l : List Stmt}, defAtom d l = some (.add x y z) → x = d
  | [], h => by simp [defAtom] at h
  | .atom b :: l, h => by
      simp only [defAtom] at h
      split_ifs at h with hb
      · cases h; simpa using hb
      · exact defAtom_add h
  | .ite .. :: l, h => defAtom_add (by simpa [defAtom] using h)
  | .match_ .. :: l, h => defAtom_add (by simpa [defAtom] using h)
  | .call .. :: l, h => defAtom_add (by simpa [defAtom] using h)
  | .callIf .. :: l, h => defAtom_add (by simpa [defAtom] using h)
  | .dispatch .. :: l, h => defAtom_add (by simpa [defAtom] using h)
  | .ret .. :: l, h => defAtom_add (by simpa [defAtom] using h)

theorem defAtom_const {d x : V} {w : E} : ∀ {l : List Stmt}, defAtom d l = some (.const x w) → x = d
  | [], h => by simp [defAtom] at h
  | .atom b :: l, h => by
      simp only [defAtom] at h
      split_ifs at h with hb
      · cases h; simpa using hb
      · exact defAtom_const h
  | .ite .. :: l, h => defAtom_const (by simpa [defAtom] using h)
  | .match_ .. :: l, h => defAtom_const (by simpa [defAtom] using h)
  | .call .. :: l, h => defAtom_const (by simpa [defAtom] using h)
  | .callIf .. :: l, h => defAtom_const (by simpa [defAtom] using h)
  | .dispatch .. :: l, h => defAtom_const (by simpa [defAtom] using h)
  | .ret .. :: l, h => defAtom_const (by simpa [defAtom] using h)

theorem ofK_mulS (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem gpow_succ' (a : ℕ) : gpow a * gpow 1 = gpow (a + 1) := by
  simp [Parameters.gpow, pow_add]

variable {rd : Reader} {pre : List Stmt} {es : List Ev}

/-- A defining atom of a block without `ret`, on its path, holds. -/
theorem defAtom_holds (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es)
    (hh : HoldsAll rd σ es) {d : V} {a : Atom} (h : defAtom d pre = some a) : a.Holds rd σ :=
  hh _ (atom_on_path hn hw (defAtom_mem h))

theorem isG_val (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es) (hh : HoldsAll rd σ es)
    {z : V} (h : (match defAtom z pre with
      | some (.const _ w) => constOk w 1
      | _ => false) = true) : σ z = ofK (gpow 1) := by
  split at h
  · rename_i x w hd
    have := defAtom_holds hn hw hh hd
    rw [← defAtom_const hd]
    exact this.trans (constOk_spec h).1
  · cases h

theorem isStep_val (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es)
    (hh : HoldsAll rd σ es) {p d : V} (h : isStep pre p d = true) : σ d = σ p * ofK (gpow 1) := by
  unfold isStep at h
  split at h
  · rename_i x y z hd
    have hm : σ x = σ y * σ z := defAtom_holds hn hw hh hd
    rw [← defAtom_mul hd, hm]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hz⟩ | ⟨rfl, hz⟩
    · rw [isG_val hn hw hh hz]
    · rw [isG_val hn hw hh hz, mul_comm]
  · cases h

theorem isEnd_val (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es)
    (hh : HoldsAll rd σ es) {p1 : Option V} {endc : Option ℕ} {y : V} (h : isEnd pre p1 endc y = true) :
    (endc = none → p1 = some y) ∧ ∀ e, endc = some e → σ y = ofK (gpow e) := by
  unfold isEnd at h
  cases endc with
  | none => exact ⟨fun _ => (by simpa using h), fun _ he => (by cases he)⟩
  | some e =>
      refine ⟨fun he => (by cases he), fun e' he => ?_⟩
      cases he
      simp only at h
      split at h
      · rename_i x w hd
        have := defAtom_holds hn hw hh hd
        rw [← defAtom_const hd]
        exact this.trans (constOk_spec h).1
      · cases h

/-- **A loop helper's shape.** -/
theorem loopShape_spec {fn : Fn} {endc : Option ℕ} (h : loopShape fn endc = some pre) :
    ∃ c i' p0 prest, fn.params = p0 :: prest ∧
      fn.body = pre ++ [.callIf c fn.name (i' :: prest), .ret []] ∧ Stmt.noRetListS pre = true ∧
      isStep pre p0 i' = true ∧ ∃ x y, defAtom c pre = some (.add c x y) ∧
        ((isStep pre p0 x = true ∧ isEnd pre prest.head? endc y = true) ∨
          (isStep pre p0 y = true ∧ isEnd pre prest.head? endc x = true)) := by
  unfold loopShape at h
  split at h
  · rename_i c g i' rest rpre p0 prest hrev hps
    simp only at h
    split_ifs at h with hc
    cases h
    obtain ⟨hg, hrest, hnr, hst, hgd⟩ := hc
    subst hg hrest
    refine ⟨c, i', p0, _, hps, ?_, hnr, hst, ?_⟩
    · have := congrArg List.reverse hrev
      rw [List.reverse_reverse] at this
      rw [this]
      simp
    · split at hgd
      · rename_i c' x y hd
        obtain rfl := defAtom_add hd
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hgd
        exact ⟨x, y, hd, hgd⟩
      · cases hgd
  · cases h

end Loop

/-! ## The main induction -/

section Main

variable {P : Core.Program} {α : Bool} {cert : String → Cert} {ω : String → ℕ} {rd : Reader}

theorem fn_name_of_find {f : String} {fn : Fn} (h : P.find? f = some fn) : fn.name = f := by
  simpa using List.find?_some h

theorem countKids_le : ∀ {ks : List Tree} {k : Tree}, k ∈ ks → k.count ≤ Tree.countKids ks
  | [], _, h => (List.not_mem_nil h).elim
  | k' :: ks, k, h => by
      rw [Tree.countKids]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := countKids_le h; omega

theorem count_pos : ∀ t : Tree, 1 ≤ t.count
  | .node .. => by rw [Tree.count]; omega
  | .phantom .. => by rw [Tree.count]

theorem getD_tail {a : E} {l l' : List E} (h : a :: l = l') {k : ℕ} (hk : k ≠ 0) (b : E) :
    (b :: l).getD k 0 = l'.getD k 0 := by
  subst h
  cases k with
  | zero => exact absurd rfl hk
  | succ k => simp

/-- **Soundness of the static checker**: if every function of the program passes, every valid
tree satisfies its certificate. -/
theorem chk_sound {X : String → Prop} (hchk : CheckedExcept P α cert ω X)
    (hX : ∀ f, X f → ∀ (t : Tree) (args rets : List E), t.name = f → t.Valid P rd args rets →
      t.BufsOk P → Bound P α cert ω t args) :
    ∀ (n : ℕ) (t : Tree) (args rets : List E), t.count ≤ n → t.Valid P rd args rets → t.BufsOk P →
      Bound P α cert ω t args
  | 0, t, _, _, hc, _, _ => by have := count_pos t; omega
  | _ + 1, .phantom .., _, _, _, hv, _ => hv.elim
  | n + 1, .node f σ bufs kids, args, rets, hc, hv, hbo => by
      by_cases hXf : X f
      · exact hX f hXf _ args rets rfl hv hbo
      have hbk : Tree.BufsOkKids P kids := by simp only [Tree.BufsOk] at hbo; exact hbo.2
      obtain ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ := hv
      have hcost : (Tree.node f σ bufs kids).cost P α ω = ω f + aw α σ es + Tree.costKids P α ω kids := by
        rw [Tree.cost]
        simp only [Tree.events, Tree.name, Tree.val, hf, hw, aw]
      have hname := fn_name_of_find hf
      obtain ⟨look, wl, hlook, hwl, hc'⟩ := hchk fn (List.mem_of_find?_eq_some hf) (by rw [hname]; exact hXf)
      have hIH : ∀ k ∈ kids, ∀ args' rets', k.Valid P rd args' rets' → k.BufsOk P →
          Bound P α cert ω k args' :=
        fun k hk' a' r' hv' hb' => chk_sound hchk hX n k a' r' (by
          have := countKids_le hk'; rw [Tree.count] at hc; omega) hv' hb'
      unfold Bound
      simp only [Tree.name]
      unfold chkFn at hc'
      rw [hname] at hc'
      cases hcf : cert f with
      | none => trivial
      | stat pre b ks =>
          rw [hcf] at hc'
          simp only at hc'
          split at hc'
          · rename_i r hb
            simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc'
            intro hpre
            have hpr : ArgsPre r.2 args := fun q hq => hpre q (hc'.2 q hq)
            rw [blockR_eq] at hb
            replace hb := blockB_mono hlook _ _ hb
            have hkb := blockB_sound (rd := rd) (ω := ω) hp hwl fn.body ([], []) r
              ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
              hb hpr (by rw [hw]; exact hes) kids (by rw [hw]; exact hk) hbk hIH
            rw [hw] at hkb
            simp only [Out.evs] at hkb
            rw [hcost]
            have := Aff.eval_le_of_leB hc'.1 args
            simp only [Aff.eval] at this hkb ⊢
            omega
          · cases hc'
      | loop endc pre b ks =>
          rw [hcf] at hc'
          simp only at hc'
          split at hc'
          · rename_i pre' hsh
            split at hc'
            · rename_i r hb
              simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc'
              obtain ⟨⟨⟨hle, hpre⟩, hbc⟩, hpc⟩ := hc'
              obtain ⟨c, i', p0, prest, hps, hbody, hnr, hst, x, y, hadd, hxy⟩ := loopShape_spec hsh
              rw [blockR_eq] at hb
              replace hb := blockB_mono hlook _ _ hb
              rw [hname] at hbody
              rw [hbody, walk_append] at hw
              rcases walk_noRet (σ := σ) pre' hnr with ⟨es1, hw1⟩ | hw1
              · rw [hw1] at hw
                have hwt : walk σ [.callIf c f (i' :: prest), .ret []] =
                    .ret [.inK c, if σ c = 0 then .skip f (i' :: prest) else .call f (i' :: prest) []] [] := by
                  simp [walk, walk1, Out.seq, Out.pre]
                rw [hwt] at hw
                simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
                obtain ⟨rfl, rfl⟩ := hw
                have hes1 : HoldsAll rd σ es1 := fun e he => hes e (List.mem_append_left _ he)
                rw [calls_append] at hk
                obtain ⟨ks1, ks2, rfl, hk1, hk2⟩ := kidsValid_split hk
                obtain ⟨hbk1, hbk2⟩ := bufsOkKids_split ks1 ks2 hbk
                intro a0 e h0 hend hae hord hpre0
                have hkb := blockB_sound (rd := rd) (ω := ω) hp hwl pre' ([], []) r
                  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩ hb (fun q hq => hpre0 q (hpre q hq))
                  (by rw [hw1]; exact hes1) ks1 (by rw [hw1]; exact hk1) hbk1
                  (fun k hk' => hIH k (List.mem_append_left _ hk'))
                have hle' := Aff.eval_le_of_leB hle args
                simp only [Aff.eval] at hle' hkb
                have hcalls : calls [Ev.inK c, if σ c = 0 then .skip f (i' :: prest)
                    else .call f (i' :: prest) []] = [⟨f, i' :: prest, [], !decide (σ c = 0)⟩] := by
                  by_cases h0c : σ c = 0 <;> simp only [h0c, ↓reduceIte, decide_true, decide_false,
                    Bool.not_true, Bool.not_false] <;> rfl
                rw [hcalls] at hk2
                have hargs : args = σ p0 :: prest.map σ := by rw [← hp, hps, List.map_cons]
                have hp0 : σ p0 = ofK (gpow a0) := by rw [← h0, hargs]; rfl
                have hi' : σ i' = ofK (gpow (a0 + 1)) := by
                  rw [isStep_val hnr hw1 hes1 hst, hp0, ← ofK_mulS, gpow_succ']
                have hM : 1 ≤ e - a0 := by omega
                match ks2, hk2 with
                | [tk], ⟨htn, htv, _⟩ =>
                  have htail : aw α σ [Ev.inK c, if σ c = 0 then .skip f (i' :: prest)
                      else .call f (i' :: prest) []] = 0 := by
                    unfold aw allocs; split_ifs <;> rfl
                  rw [hw1] at hkb
                  simp only [Out.evs] at hkb
                  rw [hcost, aw_append, htail, costKids_append, Tree.costKids, Tree.costKids]
                  by_cases h0c : σ c = 0
                  · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
                    obtain ⟨⟨g', σ', rfl⟩, -⟩ := htv
                    simp only [Tree.name] at htn
                    subst htn
                    simp only [Tree.cost, Aff.eval] at hkb hle' ⊢
                    have : b.eval args ≤ (e - a0) * b.eval args := Nat.le_mul_of_pos_left _ hM
                    simp only [Aff.eval] at this
                    omega
                  · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
                    have hb' := hIH tk (List.mem_append_right _ List.mem_cons_self) _ _ htv
                      (by simp only [Tree.BufsOkKids] at hbk2; exact hbk2.1)
                    unfold Bound at hb'
                    rw [htn, hcf] at hb'
                    simp only at hb'
                    have hargs'' : (i' :: prest).map σ = σ i' :: prest.map σ := rfl
                    have hget : ∀ k, k ≠ 0 → ((i' :: prest).map σ).getD k 0 = args.getD k 0 := by
                      intro k hk0
                      rw [hargs'', hargs]
                      cases k with
                      | zero => exact absurd rfl hk0
                      | succ k => simp
                    have hendeq : endOf endc ((i' :: prest).map σ) = endOf endc args := by
                      cases endc with
                      | some _ => rfl
                      | none => exact hget 1 (by omega)
                    have hyv : ∀ {z : V}, isEnd pre' prest.head? endc z = true → σ z = ofK (gpow e) := by
                      intro z hz
                      obtain ⟨h1, h2⟩ := isEnd_val hnr hw1 hes1 hz
                      cases endc with
                      | some e' => rw [h2 e' rfl]; exact hend
                      | none =>
                          have := h1 rfl
                          cases prest with
                          | nil => cases this
                          | cons y' ys =>
                              simp only [List.head?_cons, Option.some.injEq] at this
                              subst this
                              rw [← hend]
                              simp [endOf, hargs]
                    have hcv : σ c = σ x + σ y := defAtom_holds hnr hw1 hes1 hadd
                    have hne : a0 + 1 ≠ e := by
                      intro hae'
                      apply h0c
                      rw [hcv, e_add_eq_zero_iff]
                      rcases hxy with ⟨hsx, hey⟩ | ⟨hsy, hex⟩
                      · rw [isStep_val hnr hw1 hes1 hsx, hp0, ← ofK_mulS, gpow_succ', hyv hey, hae']
                      · rw [isStep_val hnr hw1 hes1 hsy, hp0, ← ofK_mulS, gpow_succ', hyv hex, hae']
                    have hpre'' : ArgsPre pre ((i' :: prest).map σ) := by
                      intro q hq
                      rw [hget q.1 (hpc q hq)]
                      exact hpre0 q hq
                    have hbev : b.eval ((i' :: prest).map σ) = b.eval args := by
                      unfold Aff.eval
                      congr 1
                      congr 1
                      refine List.map_congr_left fun q hq => ?_
                      unfold argExp
                      rw [hget q.1 (hbc q hq)]
                    have htk := hb' (a0 + 1) e (by rw [hargs'']; simpa using hi') (by rw [hendeq]; exact hend)
                      (by omega) hord hpre''
                    rw [hbev] at htk
                    have he1 : e - a0 = (e - (a0 + 1)) + 1 := by omega
                    rw [he1, Nat.add_mul, Nat.one_mul]
                    simp only [Aff.eval] at htk ⊢
                    omega
              · rw [hw1] at hw; simp [Out.seq] at hw
            · cases hc'
          · cases hc'

/-- **A checked bound**: every valid tree of a function with a `stat` certificate costs at most
its bound, under its preconditions, the functions of `X` satisfying theirs by hypothesis. -/
theorem cost_le_of_stat {X : String → Prop} (hchk : CheckedExcept P α cert ω X)
    (hX : ∀ f, X f → ∀ (t : Tree) (args rets : List E), t.name = f → t.Valid P rd args rets →
      t.BufsOk P → Bound P α cert ω t args) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : cert f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid P rd args rets) (hb : t.BufsOk P)
    (hpre : ArgsPre pre args) : t.cost P α ω ≤ b.eval args := by
  have := chk_sound hchk hX t.count t args rets le_rfl hv hb
  unfold Bound at this
  rw [hn, hcf] at this
  exact this hpre

/-- **A checked loop**: a valid tree of a loop helper started at `g^a`, its end `g^e`, `a < e`,
costs at most `e - a` times its iteration's bound. -/
theorem cost_le_of_loop {X : String → Prop} (hchk : CheckedExcept P α cert ω X)
    (hX : ∀ f, X f → ∀ (t : Tree) (args rets : List E), t.name = f → t.Valid P rd args rets →
      t.BufsOk P → Bound P α cert ω t args) {f : String}
    {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.cost P α ω ≤ (e - a) * b.eval args := by
  have := chk_sound hchk hX t.count t args rets le_rfl hv hb
  unfold Bound at this
  rw [hn, hcf] at this
  exact this a e ha he hae heo hpre

theorem noHand : ∀ f, (fun _ => False) f → ∀ (t : Tree) (args rets : List E), t.name = f →
    t.Valid P rd args rets → t.BufsOk P → Bound P α cert ω t args :=
  fun _ h => h.elim

/-- `cost_le_of_stat` for the weight. -/
theorem weight_le_of_stat (hchk : Checked P false cert ω) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : cert f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid P rd args rets) (hb : t.BufsOk P)
    (hpre : ArgsPre pre args) : t.weight ω ≤ b.eval args := by
  rw [← cost_false (P := P)]; exact cost_le_of_stat hchk noHand hcf hn hv hb hpre

/-- **A constant checked bound** is a `WeightLe`. -/
theorem weightLe_of_stat (hchk : Checked P false cert ω) {f : String} {B : ℕ}
    {ks : List (V × ℕ)} (hcf : cert f = .stat [] ⟨B, []⟩ ks) : WeightLe P ω f fun _ => B :=
  fun _ _ _ _ hn hv hb => by
    have := weight_le_of_stat hchk hcf hn hv hb (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

/-- `cost_le_of_loop` for the weight. -/
theorem weight_le_of_loop (hchk : Checked P false cert ω) {f : String}
    {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.weight ω ≤ (e - a) * b.eval args := by
  rw [← cost_false (P := P)]; exact cost_le_of_loop hchk noHand hcf hn hv hb ha he hae heo hpre

end Main

end
end LeanVM.Guest.Memory
