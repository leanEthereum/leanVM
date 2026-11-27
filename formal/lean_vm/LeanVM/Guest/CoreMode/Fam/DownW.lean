/-
  LeanVM.Guest.CoreMode.Fam.DownW

  The facts carried to callees, every family's check of one function in one walk of its body: the carried and nonzero
  facts (`Res.carryG`, `Res.carryNzG`), the exponent bounds (`CoreMode.carryExpB`) and the callers' checks
  (`Res.callersG`, `Res.callersM`, `Res.callersB`).
-/

module

public import LeanVM.Guest.CoreMode.Fam.CarryWit
public import LeanVM.Guest.CoreMode.Fam.ExpCWit
public import LeanVM.Guest.CoreMode.Fam.CallersWit

/-!
# The facts carried to callees, in one walk

Each family's witnessed check (`carryGW`, `carryNzW`, `CoreMode.carryExpW`, `callersGW`, `callersMW`, `callersBW`)
walks the whole body, and the walk, not the checks, is most of their cost. `downW` walks it once (`allB`): at an atom
the carried facts' heap witness and the nonzero facts' allocation, at a call site every family's check of the site,
the callee's code computed once (`siteD`). `allB_sites` and `allB_block` read a family's `sitesB` or `blockAll` off
the walk, `allB_ctx` the nonzero facts' `allB`, and `downW_*` each family's check.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (spine blockAll armsAll)
open LeanVM.Guest.Exec (natSeq natSeq_eq)

@[expose] public section

/-- The lists and tables the families read. -/
structure DownT where
  carried : NTab (ℕ × Kd)
  cnz : NTab ℕ
  up : NTab ℕ
  own : NTab ℕ
  exp : NTab (ℕ × ℕ × ℕ)
  term : List (String × String)
  gl : List (String × List String)
  mono : List (String × String)
  any : Link

/-- A function's witnesses: the sub-spines of the carried facts (over `Bridge.spine`), of the nonzero facts and of the
exponent bounds (over `Memory.spineE`). -/
structure DownB where
  g : ℕ
  nz : ℕ
  exp : ℕ

/-- **Every family's check of a call site**, `c` the callee's code, `k` the caller's. -/
noncomputable def siteD (D : DownT) (fn : Fn) (spA : List Atom) (kv : List V) (spN spX : List Ev) (k : ℕ) (f : String)
    (args : List V) (c : ℕ) : Bool :=
  ((D.carried.at c).all fun e ↦ match args[e.1]? with
    | some a => pinW fn spA e.2 a
    | none => false) &&
  ((D.cnz.at c).all fun i ↦ match args[i]? with
    | some a => nzOf kv spN nzDepth a
    | none => false) &&
  ((D.exp.at c).all fun e ↦ match args[e.1]? with
    | some a => CoreMode.constExpS a e.2.1 e.2.2 spX || CoreMode.armExpB a e.2.1 e.2.2 fn.body
    | none => false) &&
  ((NTab.ofNamed encS D.term).at c).all (fun d ↦ Nat.beq d k || (fn.name == f && fn.loop)) &&
  ((NTab.ofNamed (fun cs : List String ↦ cs.map encS) D.gl).at c).all
    (fun cs ↦ cs.contains k || (fn.name == f && fn.loop)) &&
  ((NTab.ofNamed encS D.mono).at c).all (fun d ↦ Nat.beq d k || (fn.name == f && fn.loop)) &&
  (((NTab.ofNamed (fun _ ↦ ()) D.any.fams).at c).isEmpty || Nat.beq k (encS D.any.oName) ||
    (fn.name == f && fn.loop))

/-- A dynamic allocation's size nonzero in `K`. -/
noncomputable def nzAtom (kv : List V) (sp : List Ev) : Atom → Bool
  | .hint (.allocDyn _ s) => nzOf kv sp nzDepth s
  | _ => true

/-- **Every family's check of a statement**: an atom's (a heap witness, a dynamic allocation's size), a call site's
(`siteD`, the callee's code evaluated first). -/
noncomputable def stmtD (D : DownT) (fn : Fn) (spA : List Atom) (kv : List V) (spN spX : List Ev) (k : ℕ) :
    Stmt → Bool
  | .atom a => witAtomC fn spA a && nzAtom kv spN a
  | .call f args _ => natSeq (encS f) (siteD D fn spA kv spN spX k f args)
  | .callIf _ f args => natSeq (encS f) (siteD D fn spA kv spN spX k f args)
  | .dispatch _ fs args _ => fs.all fun f ↦ natSeq (encS f) (siteD D fn spA kv spN spX k f args)
  | _ => true

/-- **The facts carried to callees, every family's check of one function**, its witnesses `w`. -/
noncomputable def downW (D : DownT) (fn : Fn) (w : DownB) : Bool :=
  natSeq (encS fn.name) fun k ↦
    allB (fun _ s ↦ stmtD D fn (pickB w.g (spine fn.body)) (kvNzW D.cnz D.own fn) (pickB w.nz (spineE fn.body))
      (pickB w.exp (spineE fn.body)) k s) fn.body (spineE fn.body) &&
    (D.up.at k).all (upChkW fn (pickB w.nz (spineE fn.body))) &&
    (D.own.at k).all fun v ↦ ownChkW fn (pickB w.nz (spineE fn.body)) (V.n v)

end

/-! ## The walk gives each family's -/

/-- A call site's check `p`, `true` at any other statement. -/
@[expose] public def siteOk (p : String → List V → List V → Bool) : Stmt → Bool
  | .call f args rets => p f args rets
  | .callIf _ f args => p f args []
  | .dispatch _ fs args rets => fs.all fun f ↦ p f args rets
  | _ => true

public section

section

variable {q : Stmt → Bool} {p : String → List V → List V → Bool}

mutual
theorem allS_sites (h : ∀ s, q s = true → siteOk p s = true) :
    ∀ (s : Stmt) (ctx : List Ev), allS (fun _ s ↦ q s) s ctx = true → sitesS p s = true
  | .atom _, _, _ => rfl
  | .ite c z n, ctx, hs => by
    replace hs : (q (.ite c z n) && allB (fun _ s ↦ q s) z (ctx ++ spineE z) &&
      allB (fun _ s ↦ q s) n (ctx ++ spineE n)) = true := hs
    show (sitesB p z && sitesB p n) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨allB_sites h z _ hs.1.2, allB_sites h n _ hs.2⟩
  | .match_ x arms, ctx, hs => by
    replace hs : (q (.match_ x arms) && allA (fun _ s ↦ q s) arms ctx) = true := hs
    simp only [Bool.and_eq_true] at hs
    exact allA_sites h arms ctx hs.2
  | .call f a r, _, hs => h (.call f a r) hs
  | .callIf c f a, _, hs => h (.callIf c f a) hs
  | .dispatch x fs a r, _, hs => h (.dispatch x fs a r) hs
  | .ret _, _, _ => rfl

theorem allB_sites (h : ∀ s, q s = true → siteOk p s = true) :
    ∀ (ss : List Stmt) (ctx : List Ev), allB (fun _ s ↦ q s) ss ctx = true → sitesB p ss = true
  | [], _, _ => rfl
  | s :: ss, ctx, hs => by
    replace hs : (allS (fun _ s ↦ q s) s ctx && allB (fun _ s ↦ q s) ss ctx) = true := hs
    show (sitesS p s && sitesB p ss) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨allS_sites h s ctx hs.1, allB_sites h ss ctx hs.2⟩

theorem allA_sites (h : ∀ s, q s = true → siteOk p s = true) :
    ∀ (as : List (List Stmt)) (ctx : List Ev), allA (fun _ s ↦ q s) as ctx = true → sitesA p as = true
  | [], _, _ => rfl
  | b :: as, ctx, hs => by
    replace hs : (allB (fun _ s ↦ q s) b (ctx ++ spineE b) && allA (fun _ s ↦ q s) as ctx) = true := hs
    show (sitesB p b && sitesA p as) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨allB_sites h b _ hs.1, allA_sites h as ctx hs.2⟩
end

end

section

variable {q : Stmt → Bool} {p : Atom → Bool}

mutual
theorem allS_block (h : ∀ a, q (.atom a) = true → p a = true) :
    ∀ (s : Stmt) (ctx : List Ev), allS (fun _ s ↦ q s) s ctx = true → blockAll p [s] = true
  | .atom a, _, hs => by
    show (p a && true) = true
    rw [Bool.and_true]
    exact h a hs
  | .ite c z n, ctx, hs => by
    replace hs : (q (.ite c z n) && allB (fun _ s ↦ q s) z (ctx ++ spineE z) &&
      allB (fun _ s ↦ q s) n (ctx ++ spineE n)) = true := hs
    show ((blockAll p z && blockAll p n) && true) = true
    simp only [Bool.and_true, Bool.and_eq_true] at hs ⊢
    exact ⟨allB_block h z _ hs.1.2, allB_block h n _ hs.2⟩
  | .match_ x arms, ctx, hs => by
    replace hs : (q (.match_ x arms) && allA (fun _ s ↦ q s) arms ctx) = true := hs
    show (armsAll p arms && true) = true
    simp only [Bool.and_true, Bool.and_eq_true] at hs ⊢
    exact allA_block h arms ctx hs.2
  | .call .., _, _ => rfl
  | .callIf .., _, _ => rfl
  | .dispatch .., _, _ => rfl
  | .ret _, _, _ => rfl

theorem allB_block (h : ∀ a, q (.atom a) = true → p a = true) :
    ∀ (ss : List Stmt) (ctx : List Ev), allB (fun _ s ↦ q s) ss ctx = true → blockAll p ss = true
  | [], _, _ => rfl
  | s :: ss, ctx, hs => by
    replace hs : (allS (fun _ s ↦ q s) s ctx && allB (fun _ s ↦ q s) ss ctx) = true := hs
    rw [blockAll_cons, Bool.and_eq_true]
    simp only [Bool.and_eq_true] at hs
    exact ⟨allS_block h s ctx hs.1, allB_block h ss ctx hs.2⟩

theorem allA_block (h : ∀ a, q (.atom a) = true → p a = true) :
    ∀ (as : List (List Stmt)) (ctx : List Ev), allA (fun _ s ↦ q s) as ctx = true → armsAll p as = true
  | [], _, _ => rfl
  | b :: as, ctx, hs => by
    replace hs : (allB (fun _ s ↦ q s) b (ctx ++ spineE b) && allA (fun _ s ↦ q s) as ctx) = true := hs
    show (blockAll p b && armsAll p as) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨allB_block h b _ hs.1, allA_block h as ctx hs.2⟩
end

end

/-! ## Each family from the walk -/

section

variable {D : DownT} {fn : Fn} {w : DownB}

/-- The walk's parts. -/
private theorem downW_parts (h : downW D fn w = true) :
    allB (fun _ s ↦ stmtD D fn (pickB w.g (spine fn.body)) (kvNzW D.cnz D.own fn) (pickB w.nz (spineE fn.body))
      (pickB w.exp (spineE fn.body)) (encS fn.name) s) fn.body (spineE fn.body) = true ∧
    (D.up.at (encS fn.name)).all (upChkW fn (pickB w.nz (spineE fn.body))) = true ∧
    ((D.own.at (encS fn.name)).all fun v ↦ ownChkW fn (pickB w.nz (spineE fn.body)) (V.n v)) = true := by
  unfold downW at h
  rw [natSeq_eq] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A family's site check from every family's, at each kind of site. -/
private theorem site_of {spA : List Atom} {kv : List V} {spN spX : List Ev} {k : ℕ}
    {p : String → List V → List V → Bool}
    (hp : ∀ f args rets, siteD D fn spA kv spN spX k f args (encS f) = true → p f args rets = true) :
    ∀ s, stmtD D fn spA kv spN spX k s = true → siteOk p s = true
  | .call f args rets, h => hp f args rets (by rw [stmtD, natSeq_eq] at h; exact h)
  | .callIf _ f args, h => hp f args [] (by rw [stmtD, natSeq_eq] at h; exact h)
  | .dispatch _ fs args rets, h => by
    rw [stmtD] at h
    exact all_imp (fun f hf ↦ hp f args rets (by rw [natSeq_eq] at hf; exact hf)) h
  | .atom _, _ => rfl
  | .ite .., _ => rfl
  | .match_ .., _ => rfl
  | .ret _, _ => rfl

private theorem siteD_parts {spA : List Atom} {kv : List V} {spN spX : List Ev} {k : ℕ} {f : String}
    {args : List V} {c : ℕ} (h : siteD D fn spA kv spN spX k f args c = true) :
    ((D.carried.at c).all fun e ↦ match args[e.1]? with
      | some a => pinW fn spA e.2 a
      | none => false) = true ∧
    ((D.cnz.at c).all fun i ↦ match args[i]? with
      | some a => nzOf kv spN nzDepth a
      | none => false) = true ∧
    ((D.exp.at c).all fun e ↦ match args[e.1]? with
      | some a => CoreMode.constExpS a e.2.1 e.2.2 spX || CoreMode.armExpB a e.2.1 e.2.2 fn.body
      | none => false) = true ∧
    (((NTab.ofNamed encS D.term).at c).all fun d ↦ Nat.beq d k || (fn.name == f && fn.loop)) = true ∧
    (((NTab.ofNamed (fun cs : List String ↦ cs.map encS) D.gl).at c).all
      fun cs ↦ cs.contains k || (fn.name == f && fn.loop)) = true ∧
    (((NTab.ofNamed encS D.mono).at c).all fun d ↦ Nat.beq d k || (fn.name == f && fn.loop)) = true ∧
    (((NTab.ofNamed (fun _ ↦ ()) D.any.fams).at c).isEmpty || Nat.beq k (encS D.any.oName) ||
      (fn.name == f && fn.loop)) = true := by
  unfold siteD at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem downW_carryG (hT : tabOk carried D.carried id = true) (h : downW D fn w = true) : carryG fn = true := by
  obtain ⟨hw, -, -⟩ := downW_parts h
  have hc : carryGW D.carried fn w.g = true := by
    unfold carryGW
    simp only [Bool.and_eq_true]
    refine ⟨allB_sites (fun s hs ↦ ?_) fn.body _ hw, allB_block (fun a ha ↦ ?_) fn.body _ hw⟩
    · refine site_of (p := siteCW D.carried fn (pickB w.g (spine fn.body))) (fun f args rets hd ↦ ?_) s hs
      exact (siteD_parts hd).1
    · rw [stmtD, Bool.and_eq_true] at ha
      exact ha.1
  exact carryG_of_wit hT hc

theorem downW_carryNz (hT : tabOk carriedNz D.cnz id = true) (hU : tabOk nzUp D.up id = true)
    (hO : tabOk ownNz D.own id = true) (h : downW D fn w = true) : carryNzG fn = true := by
  obtain ⟨hw, h2, h3⟩ := downW_parts h
  refine carryNzG_of_wit hT hU hO (b := w.nz) ?_
  unfold carryNzW
  simp only [Bool.and_eq_true]
  refine ⟨⟨allB_ctx (ctx0 := spineE fn.body) (fun ctx s _ hs ↦ ?_) fn.body _ (fun _ h ↦ h) hw, h2⟩, h3⟩
  cases s with
  | atom a =>
    rw [stmtD, Bool.and_eq_true] at hs
    have h2 := hs.2
    cases a with
    | hint hh =>
      cases hh with
      | allocDyn _ s => exact h2
      | _ => rfl
    | _ => rfl
  | call f args _ =>
    rw [stmtD, natSeq_eq] at hs
    exact (siteD_parts hs).2.1
  | callIf _ f args =>
    rw [stmtD, natSeq_eq] at hs
    exact (siteD_parts hs).2.1
  | dispatch _ fs args _ =>
    rw [stmtD] at hs
    exact all_imp (fun f hf ↦ by rw [natSeq_eq] at hf; exact (siteD_parts hf).2.1) hs
  | _ => rfl

theorem downW_carryExp {L : List (String × ℕ × ℕ × ℕ)} (hT : tabOk L D.exp id = true) (h : downW D fn w = true) :
    CoreMode.carryExpB L fn = true := by
  obtain ⟨hw, -, -⟩ := downW_parts h
  refine CoreMode.carryExpB_of_wit hT (b := w.exp) ?_
  unfold CoreMode.carryExpW
  refine allB_sites (fun s hs ↦ ?_) fn.body _ hw
  exact site_of (fun f args rets hd ↦ (siteD_parts hd).2.2.1) s hs

theorem downW_term {R : List (String × String)} (hR : D.term = R) (h : downW D fn w = true) : callersG R fn = true := by
  subst hR
  obtain ⟨hw, -, -⟩ := downW_parts h
  refine callersG_of_wit ?_
  unfold callersGW
  rw [natSeq_eq]
  refine allB_sites (fun s hs ↦ ?_) fn.body _ hw
  exact site_of (fun f args rets hd ↦ (siteD_parts hd).2.2.2.1) s hs

theorem downW_gl {R : List (String × List String)} (hR : D.gl = R) (h : downW D fn w = true) : callersM R fn = true := by
  subst hR
  obtain ⟨hw, -, -⟩ := downW_parts h
  refine callersM_of_wit ?_
  unfold callersMW
  rw [natSeq_eq]
  refine allB_sites (fun s hs ↦ ?_) fn.body _ hw
  exact site_of (fun f args rets hd ↦ (siteD_parts hd).2.2.2.2.1) s hs

theorem downW_mono {R : List (String × String)} (hR : D.mono = R) (h : downW D fn w = true) : callersG R fn = true := by
  subst hR
  obtain ⟨hw, -, -⟩ := downW_parts h
  refine callersG_of_wit ?_
  unfold callersGW
  rw [natSeq_eq]
  refine allB_sites (fun s hs ↦ ?_) fn.body _ hw
  exact site_of (fun f args rets hd ↦ (siteD_parts hd).2.2.2.2.2.1) s hs

theorem downW_any {L : Link} (hL : D.any = L) (h : downW D fn w = true) : callersB L fn = true := by
  subst hL
  obtain ⟨hw, -, -⟩ := downW_parts h
  refine callersB_of_wit ?_
  unfold callersBW
  rw [natSeq_eq]
  refine allB_sites (fun s hs ↦ ?_) fn.body _ hw
  exact site_of (fun f args rets hd ↦ (siteD_parts hd).2.2.2.2.2.2) s hs

end

end

end LeanVM.Guest.Res
