/-
  LeanVM.Guest.Memory.StaticSound

  The soundness of the static weight checker: a call site's bound bounds its callee's weight, a
  block's bound its path's callees', and a checked program's every valid tree weighs at most its
  certificate's bound.
-/

module

public import LeanVM.Guest.Memory.Static
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Value.Tower

/-!
# Soundness of the static checker

`Bound cert ω t args`: what the certificate of `t`'s function claims of `t` on `args` (`stat`:
under its preconditions, `t` weighs at most its bound; `loop`: started at `g^a` with end `g^e`,
`a < e`, at most `e - a` times its iteration's bound). `siteB_sound`: a call site's bound bounds a
callee tree satisfying `Bound`. `blockB_sound`: a block's bound bounds the weight of its path's
callees. `chk_sound`: if every function of the program passes `chkFn`, every valid tree
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
  obtain ⟨⟨⟨he, h0⟩, h1⟩, h2⟩ := h
  refine ⟨E.ext fun i => ?_, he⟩
  rw [limb_ofK]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; rw [h0, Pow.gpowW_eq he]
  · simpa using h1
  · simpa using h2

theorem logG_ofK {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (ofK (gpow e)) = e := logG_spec he

/-- Known constants hold: `σ v = g^e` below the order of `g`. -/
def EnvOk (σ : Val) (ρ : Env) : Prop := ∀ q ∈ ρ, σ q.1 = ofK (gpow q.2) ∧ q.2 < 2 ^ 64 - 1

theorem lookup_mem {ρ : Env} {v : V} {e : ℕ} (h : ρ.lookup v = some e) : (v, e) ∈ ρ := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  exact List.mem_append_right _ List.mem_cons_self

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
      obtain ⟨hk, hv, -⟩ := List.idxOf?_eq_some_iff.mp hk'
      rw [← hp, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
      simp [hv]
    · cases h

end Cls

/-! ## Sites -/

section Site

variable {σ : Val} {ρ : Env} {ps : List V} {args : List E} {a : List V}

theorem addAcc_some {x y : Option Acc} {r : Acc} (h : Option.addAcc x y = some r) :
    ∃ rx ry, x = some rx ∧ y = some ry ∧ r = rx.add ry := by
  cases x <;> cases y <;> simp [Option.addAcc] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

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

/-- A loop's end: its parameter 1, or `g^e`. -/
def endOf (endc : Option ℕ) (args : List E) : E :=
  match endc with
  | some e => ofK (gpow e)
  | none => args.getD 1 0

/-- **What a certificate claims of a tree** of its function on `args`. -/
def Bound (cert : String → Cert) (ω : String → ℕ) (t : Tree) (args : List E) : Prop :=
  match cert t.name with
  | .none => True
  | .stat pre b _ => ArgsPre pre args → t.weight ω ≤ b.eval args
  | .loop endc pre b _ => ∀ a0 e, args.getD 0 0 = ofK (gpow a0) → endOf endc args = ofK (gpow e) →
      a0 < e → e < 2 ^ 64 - 1 → ArgsPre pre args → t.weight ω ≤ (e - a0) * b.eval args

/-- **A call site's bound bounds its callee**, a tree satisfying its certificate. -/
theorem siteB_sound {cert : String → Cert} {ω : String → ℕ} (hρ : EnvOk σ ρ) (hp : ps.map σ = args)
    {g : String} {r : Acc} (h : siteB cert ρ ps g a = some r) (hr : ArgsPre r.2 args) {t : Tree}
    (hn : t.name = g) (hb : Bound cert ω t (a.map σ)) : t.weight ω ≤ r.1.eval args := by
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
                calc t.weight ω ≤ (eb - a0) * b.eval (a.map σ) := this
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

/-- Every event holds. -/
def HoldsAll (rd : Reader) (σ : Val) (es : List Ev) : Prop := ∀ e ∈ es, e.Holds rd σ

variable (P rd σ cert ω) in
/-- **The callees of a path weigh at most `X`**, every callee satisfying its certificate. -/
def KB (es : List Ev) (X : ℕ) : Prop :=
  ∀ kids, Tree.KidsValid P rd σ (calls es) kids →
    (∀ k ∈ kids, ∀ args' rets', k.Valid P rd args' rets' → Bound cert ω k args') →
      Tree.weightKids ω kids ≤ X

theorem calls_append (es es' : List Ev) : calls (es ++ es') = calls es ++ calls es' :=
  List.filterMap_append

theorem kidsValid_split : ∀ {cs cs' : List Call} {ks : List Tree},
    Tree.KidsValid P rd σ (cs ++ cs') ks →
      ∃ ks₁ ks₂, ks = ks₁ ++ ks₂ ∧ Tree.KidsValid P rd σ cs ks₁ ∧ Tree.KidsValid P rd σ cs' ks₂
  | [], _, ks, h => ⟨[], ks, rfl, by simp [Tree.KidsValid], h⟩
  | c :: cs, cs', [], h => h.elim
  | c :: cs, cs', k :: ks, ⟨hn, hc, h⟩ => by
      obtain ⟨ks₁, ks₂, rfl, h1, h2⟩ := kidsValid_split h
      exact ⟨k :: ks₁, ks₂, rfl, ⟨hn, hc, h1⟩, h2⟩

theorem weightKids_append (ks ks' : List Tree) :
    Tree.weightKids ω (ks ++ ks') = Tree.weightKids ω ks + Tree.weightKids ω ks' := by
  induction ks with
  | nil => rw [List.nil_append, Tree.weightKids]; omega
  | cons k ks ih => rw [List.cons_append, Tree.weightKids, Tree.weightKids, ih]; omega

theorem KB_mono {es : List Ev} {X Y : ℕ} (h : KB P rd σ cert ω es X) (hXY : X ≤ Y) :
    KB P rd σ cert ω es Y := fun kids hk hb => (h kids hk hb).trans hXY

theorem KB_nil (X : ℕ) : KB P rd σ cert ω [] X := fun kids hk _ => by
  cases kids with
  | nil => rw [Tree.weightKids]; omega
  | cons _ _ => exact hk.elim

theorem KB_append {es es' : List Ev} {X Y : ℕ} (h : KB P rd σ cert ω es X)
    (h' : KB P rd σ cert ω es' Y) : KB P rd σ cert ω (es ++ es') (X + Y) := fun kids hk hb => by
  rw [calls_append] at hk
  obtain ⟨ks₁, ks₂, rfl, h1, h2⟩ := kidsValid_split hk
  rw [weightKids_append]
  exact Nat.add_le_add (h ks₁ h1 fun k hk' => hb k (List.mem_append_left _ hk'))
    (h' ks₂ h2 fun k hk' => hb k (List.mem_append_right _ hk'))

theorem KB_nocall {es : List Ev} (hc : calls es = []) (X : ℕ) : KB P rd σ cert ω es X := by
  intro kids hk hb
  rw [hc] at hk
  exact KB_nil X kids (by simpa [calls] using hk) hb

theorem KB_seq {o k : Out} {X Y : ℕ} (hh : HoldsAll rd σ (o.seq k).evs)
    (h1 : HoldsAll rd σ o.evs → KB P rd σ cert ω o.evs X)
    (h2 : ∀ es, o = .fall es → HoldsAll rd σ es → HoldsAll rd σ k.evs → KB P rd σ cert ω k.evs Y) :
    KB P rd σ cert ω (o.seq k).evs (X + Y) := by
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
    (h : HoldsAll rd σ o.evs → KB P rd σ cert ω o.evs X) : KB P rd σ cert ω (o.pre [.inK c]).evs X := by
  cases o with
  | fall es =>
      simp only [Out.pre, Out.evs, List.singleton_append] at hh ⊢
      have := h fun e he => hh e (List.mem_cons_of_mem _ he)
      intro kids hk hb
      exact this kids (by simpa [calls, Ev.call?, Out.evs, List.filterMap_cons] using hk) hb
  | ret es vs =>
      simp only [Out.pre, Out.evs, List.singleton_append] at hh ⊢
      have := h fun e he => hh e (List.mem_cons_of_mem _ he)
      intro kids hk hb
      exact this kids (by simpa [calls, Ev.call?, Out.evs, List.filterMap_cons] using hk) hb
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

/-- A call site's callee: its bound bounds the callee of one frame. -/
theorem KB_site {ρ : Env} {ps : List V} {args : List E} (hρ : EnvOk σ ρ) (hp : ps.map σ = args)
    {g : String} {a r : List V} {t : Bool} {R : Acc} (h : siteB cert ρ ps g a = some R)
    (hr : ArgsPre R.2 args) {es : List Ev} (hc : calls es = [⟨g, a, r, t⟩]) :
    KB P rd σ cert ω es (R.1.eval args) := by
  intro kids hk hb
  rw [hc] at hk
  match kids, hk with
  | [k], ⟨hn, hkv, _⟩ =>
      rw [Tree.weightKids, Tree.weightKids]
      simp only at hn hkv
      by_cases ht : t = true
      · rw [ite_eq_left ht] at hkv
        have := siteB_sound hρ hp h hr hn (hb k List.mem_cons_self _ _ hkv)
        omega
      · rw [ite_eq_right ht] at hkv
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hkv
        simp [Tree.weight]

variable {ks : List (V × ℕ)} {ps : List V} {self : String} {args : List E}

mutual
/-- **A block's bound bounds its path's callees.** -/
theorem blockB_sound (hp : ps.map σ = args) : ∀ (ss : List Stmt) (ρ : Env) (r : Acc), EnvOk σ ρ →
    blockB cert ks ps self ρ ss = some r → ArgsPre r.2 args → HoldsAll rd σ (walk σ ss).evs →
      KB P rd σ cert ω (walk σ ss).evs (r.1.eval args)
  | [], _, _, _, _, _, _ => by rw [walk]; exact KB_nil _
  | s :: ss, ρ, r, hρ, h, hr, hh => by
      rw [walk] at hh ⊢
      cases s with
      | atom a =>
          have hc1 : KB P rd σ cert ω (walk1 σ (.atom a)).evs 0 :=
            KB_nocall (by simp [walk1, Out.evs, calls, Ev.call?]) 0
          refine KB_mono (KB_seq hh (fun _ => hc1) fun es he h1 h2 => ?_) (by omega : 0 + r.1.eval args ≤ _)
          simp only [walk1, Out.fall.injEq] at he
          subst he
          cases a with
          | const v w =>
              simp only [blockB] at h
              split at h
              · rename_i e he
                split at h
                · rename_i hok
                  obtain ⟨hw, he20⟩ := constOk_spec hok
                  have hv : σ v = w := h1 _ List.mem_cons_self
                  refine blockB_sound hp ss _ r (fun q hq => ?_) h hr h2
                  rcases List.mem_cons.mp hq with rfl | hq
                  · exact ⟨hv.trans hw, by omega⟩
                  · exact hρ q hq
                · exact blockB_sound hp ss ρ r hρ h hr h2
              · exact blockB_sound hp ss ρ r hρ h hr h2
          | _ => simp only [blockB] at h; exact blockB_sound hp ss ρ r hρ h hr h2
      | ite c z n =>
          simp only [blockB] at h
          obtain ⟨rz, rnr, hz, hnr, rfl⟩ := addAcc_some h
          obtain ⟨rn, rr, hn, hrr, rfl⟩ := addAcc_some hnr
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          rw [← Nat.add_assoc]
          refine KB_seq hh (fun h1 => ?_) fun es _ _ h2 => blockB_sound hp ss ρ rr hρ hrr hr.2.2 h2
          rw [walk1] at h1 ⊢
          refine KB_pre h1 fun h1' => ?_
          split_ifs
          · rw [ite_eq_left (by assumption)] at h1'
            exact KB_mono (blockB_sound hp z ρ rz hρ hz hr.1 h1') (Nat.le_add_right _ _)
          · rw [ite_eq_right (by assumption)] at h1'
            exact KB_mono (blockB_sound hp n ρ rn hρ hn hr.2.1 h1') (Nat.le_add_left _ _)
      | match_ x arms =>
          simp only [blockB] at h
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KB_seq hh (fun h1 => ?_) fun es _ _ h2 => blockB_sound hp ss ρ rr hρ hrr hr.2 h2
          rw [walk1] at h1 ⊢
          exact armsB_sound hp x arms 0 ρ ra hρ ha hr.1 h1
      | call g a r' =>
          simp only [blockB] at h
          obtain ⟨rs, rr, hs, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KB_seq hh (fun _ => KB_site hρ hp hs hr.1 (t := true) (r := r') ?_)
            fun es _ _ h2 => blockB_sound hp ss ρ rr hρ hrr hr.2 h2
          simp [walk1, Out.evs, calls, Ev.call?]
      | callIf c g a =>
          simp only [blockB] at h
          split at h
          · cases h
          · obtain ⟨rs, rr, hs, hrr, rfl⟩ := addAcc_some h
            simp only [Acc.add, argsPre_append] at hr
            simp only [Acc.add, Aff.eval_add]
            refine KB_seq hh (fun _ => ?_) fun es _ _ h2 => blockB_sound hp ss ρ rr hρ hrr hr.2 h2
            by_cases h0 : σ c = 0
            · exact KB_site hρ hp hs hr.1 (t := false) (r := []) (by
                simp only [walk1, Out.evs, h0, ↓reduceIte]; rfl)
            · exact KB_site hρ hp hs hr.1 (t := true) (r := []) (by
                simp only [walk1, Out.evs, h0, ↓reduceIte]; rfl)
      | dispatch x gs a r' =>
          simp only [blockB] at h
          obtain ⟨rs, rr, hs, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KB_seq hh (fun _ => ?_) fun es _ _ h2 => blockB_sound hp ss ρ rr hρ hrr hr.2 h2
          rw [walk1]
          rcases pick_cases (σ := σ) (x := x) (a := a) (r := r') gs 0 with hpk | ⟨g, hg, hpk⟩
          · rw [hpk]; exact KB_nil _
          · rw [hpk]
            obtain ⟨Rg, h1, h2, h3⟩ := sumB_mem (args := args) hs g hg
            exact KB_mono (KB_site hρ hp h1 (h3 hr.1) (t := true) (r := r')
              (by simp [Out.evs, calls, Ev.call?])) h2
      | ret vs =>
          simp only [walk1, Out.seq, Out.evs]
          exact KB_nil _

/-- `blockB_sound` for the arms of a `match`. -/
theorem armsB_sound (hp : ps.map σ = args) (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) (ρ : Env)
    (r : Acc), EnvOk σ ρ → armsB cert ks ps self ρ arms = some r → ArgsPre r.2 args →
      HoldsAll rd σ (walkArms σ x j arms).evs → KB P rd σ cert ω (walkArms σ x j arms).evs (r.1.eval args)
  | [], _, _, _, _, _, _, _ => by rw [walkArms]; exact KB_nil _
  | a :: as, j, ρ, r, hρ, h, hr, hh => by
      simp only [armsB] at h
      obtain ⟨ra, rs, ha, hs, rfl⟩ := addAcc_some h
      simp only [Acc.add, argsPre_append] at hr
      simp only [Acc.add, Aff.eval_add]
      unfold walkArms at hh ⊢
      split_ifs at hh ⊢
      · exact KB_mono (blockB_sound hp a ρ ra hρ ha hr.1 hh) (Nat.le_add_right _ _)
      · exact KB_mono (armsB_sound hp x as (j + 1) ρ rs hρ hs hr.2 hh) (Nat.le_add_left _ _)
end

end Block

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

theorem walk_noRet : ∀ (ss : List Stmt), Stmt.noRetList ss = true →
    (∃ es, walk σ ss = .fall es) ∨ walk σ ss = .stuck
  | [], _ => Or.inl ⟨[], rfl⟩
  | s :: ss, h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at h
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
theorem atom_on_path {a : Atom} : ∀ {l : List Stmt} {es : List Ev}, Stmt.noRetList l = true →
    walk σ l = .fall es → Stmt.atom a ∈ l → Ev.atom a ∈ es
  | [], _, _, _, hm => (List.not_mem_nil hm).elim
  | s :: l, es, hn, hw, hm => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at hn
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

theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem gpow_succ' (a : ℕ) : gpow a * gpow 1 = gpow (a + 1) := by
  simp [Parameters.gpow, pow_add]

variable {rd : Reader} {pre : List Stmt} {es : List Ev}

/-- A defining atom of a block without `ret`, on its path, holds. -/
theorem defAtom_holds (hn : Stmt.noRetList pre = true) (hw : walk σ pre = .fall es)
    (hh : HoldsAll rd σ es) {d : V} {a : Atom} (h : defAtom d pre = some a) : a.Holds rd σ :=
  hh _ (atom_on_path hn hw (defAtom_mem h))

theorem isG_val (hn : Stmt.noRetList pre = true) (hw : walk σ pre = .fall es) (hh : HoldsAll rd σ es)
    {z : V} (h : (match defAtom z pre with
      | some (.const _ w) => constOk w 1
      | _ => false) = true) : σ z = ofK (gpow 1) := by
  split at h
  · rename_i x w hd
    have := defAtom_holds hn hw hh hd
    rw [← defAtom_const hd]
    exact this.trans (constOk_spec h).1
  · cases h

theorem isStep_val (hn : Stmt.noRetList pre = true) (hw : walk σ pre = .fall es)
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

theorem isEnd_val (hn : Stmt.noRetList pre = true) (hw : walk σ pre = .fall es)
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
      fn.body = pre ++ [.callIf c fn.name (i' :: prest), .ret []] ∧ Stmt.noRetList pre = true ∧
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

variable {P : Core.Program} {cert : String → Cert} {ω : String → ℕ} {rd : Reader}

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
theorem chk_sound (hchk : ∀ fn ∈ P, chkFn cert ω fn = true) :
    ∀ (n : ℕ) (t : Tree) (args rets : List E), t.count ≤ n → t.Valid P rd args rets →
      Bound cert ω t args
  | 0, t, _, _, hc, _ => by have := count_pos t; omega
  | _ + 1, .phantom .., _, _, _, hv => hv.elim
  | n + 1, .node f σ bufs kids, args, rets, hc, hv => by
      obtain ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ := hv
      have hname := fn_name_of_find hf
      have hc' := hchk fn (List.mem_of_find?_eq_some hf)
      have hIH : ∀ k ∈ kids, ∀ args' rets', k.Valid P rd args' rets' → Bound cert ω k args' :=
        fun k hk' a' r' hv' => chk_sound hchk n k a' r' (by
          have := countKids_le hk'; rw [Tree.count] at hc; omega) hv'
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
            have hkb := blockB_sound (rd := rd) (ω := ω) hp fn.body [] r (fun _ h => (List.not_mem_nil h).elim)
              hb hpr (by rw [hw]; exact hes) kids (by rw [hw]; exact hk) hIH
            rw [Tree.weight]
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
                intro a0 e h0 hend hae hord hpre0
                have hkb := blockB_sound (rd := rd) (ω := ω) hp pre' [] r
                  (fun _ h => (List.not_mem_nil h).elim) hb (fun q hq => hpre0 q (hpre q hq))
                  (by rw [hw1]; exact hes1) ks1 (by rw [hw1]; exact hk1)
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
                  rw [isStep_val hnr hw1 hes1 hst, hp0, ← ofK_mul, gpow_succ']
                have hM : 1 ≤ e - a0 := by omega
                match ks2, hk2 with
                | [tk], ⟨htn, htv, _⟩ =>
                  rw [Tree.weight, weightKids_append, Tree.weightKids, Tree.weightKids]
                  by_cases h0c : σ c = 0
                  · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
                    obtain ⟨⟨g', σ', rfl⟩, -⟩ := htv
                    simp only [Tree.weight, Aff.eval] at hkb hle' ⊢
                    have : b.eval args ≤ (e - a0) * b.eval args := Nat.le_mul_of_pos_left _ hM
                    simp only [Aff.eval] at this
                    omega
                  · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
                    have hb' := hIH tk (List.mem_append_right _ List.mem_cons_self) _ _ htv
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
                      · rw [isStep_val hnr hw1 hes1 hsx, hp0, ← ofK_mul, gpow_succ', hyv hey, hae']
                      · rw [isStep_val hnr hw1 hes1 hsy, hp0, ← ofK_mul, gpow_succ', hyv hex, hae']
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

/-- **A checked bound**: every valid tree of a function with a `stat` certificate weighs at most
its bound, under its preconditions. -/
theorem weight_le_of_stat (hchk : ∀ fn ∈ P, chkFn cert ω fn = true) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : cert f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid P rd args rets)
    (hpre : ArgsPre pre args) : t.weight ω ≤ b.eval args := by
  have := chk_sound hchk t.count t args rets le_rfl hv
  unfold Bound at this
  rw [hn, hcf] at this
  exact this hpre

/-- **A constant checked bound** is a `WeightLe`. -/
theorem weightLe_of_stat (hchk : ∀ fn ∈ P, chkFn cert ω fn = true) {f : String} {B : ℕ}
    {ks : List (V × ℕ)} (hcf : cert f = .stat [] ⟨B, []⟩ ks) : WeightLe P ω f fun _ => B :=
  fun _ _ _ _ hn hv => by
    have := weight_le_of_stat hchk hcf hn hv (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

/-- **A checked loop**: a valid tree of a loop helper started at `g^a`, its end `g^e`, `a < e`,
weighs at most `e - a` times its iteration's bound. -/
theorem weight_le_of_loop (hchk : ∀ fn ∈ P, chkFn cert ω fn = true) {f : String}
    {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid P rd args rets) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.weight ω ≤ (e - a) * b.eval args := by
  have := chk_sound hchk t.count t args rets le_rfl hv
  unfold Bound at this
  rw [hn, hcf] at this
  exact this a e ha he hae heo hpre

end Main

end
end LeanVM.Guest.Memory
