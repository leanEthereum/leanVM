/-
  LeanVM.Guest.EndExecADyn

  Every dynamic `HeapBuf`'s size is a power of `g`, at every honest instance (`DynPow`): the
  nonzero facts' check (`Res.carryNzG`) carried down the honest tree.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.EndExecAReady
public import LeanVM.Guest.Memory.Scope

/-!
# Dynamic sizes are powers of `g`

`g` generates `K^×` (`orderOf_g`), so a value of `K` is a power of `g` exactly when it is nonzero
(`exists_gpow`); `NZ x`: `x` in `K` and nonzero.

* `nzOf_sound`: a value the check pins (`Res.nzOf`) is `NZ`, given its listed values, the events of
  its context holding on a memory whose addresses are nonzero, and its context's calls' listed words
  (`Res.nzUp`).
* `up_valid`: on a valid tree, each listed word of a node is `NZ` (`UpOk`), by its own body's check
  (`Res.upChk`) and its callees', by induction on the tree.
* `carryNzQ_all`: at every honest instance, its carried parameters (`Res.carriedNz`) are `NZ`
  (`CarryNzQ`), by `Res.insts_down`: a call site passes them (`Res.siteNz`), in the context of its
  statement on the path (`Memory.allB_body`), with the caller's carried values and loop counter.
* `dynPow_guest : DynPow`: a dynamic allocation on an honest instance's path has its size pinned.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (veq kvNz pinIn kIn upAt pinNz nzOf nzDepth siteNz nzStmt retNz upChk carryNzG
  carriedNz nzUp carryNz_all)

@[expose] public section

/-- `x` nonzero in `K`. -/
def NZ (x : E) : Prop := IsInK x ∧ x ≠ 0

/-- **The listed words of a node** (`Res.nzUp`), among its arguments then its returns, are `NZ`. -/
def UpOk (f : String) (args rets : List E) : Prop :=
  ∀ c ∈ nzUp, c.1 = f → ∀ w, (args ++ rets)[c.2]? = some w → NZ w

/-- **The carried parameters of an instance** (`Res.carriedNz`) are `NZ`. -/
def CarryNzQ (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ carriedNz,
    c.1 = f → ∀ v, fn.params[c.2]? = some v → NZ (σ v)

end

public section

/-! ## Powers of `g` -/

/-- **Every nonzero element of `K` is a power of `g`**, which generates `K^×`. -/
theorem exists_gpow {x : K} (hx : x ≠ 0) : ∃ n, x = addressOfIndex n := by
  let f : Fin (2 ^ 64 - 1) → Kˣ := fun i ↦ Units.mk0 (addressOfIndex i) (gpow_ne_zero i)
  have hf : Function.Injective f := fun i j h ↦
    Fin.ext (gpow_injOn i.2 j.2 (congrArg Units.val h))
  have hc : Nat.card Kˣ ≤ Nat.card (Fin (2 ^ 64 - 1)) := by
    rw [Nat.card_units, BF64.nat_card_bf64, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨i, hi⟩ := (hf.bijective_of_nat_card_le hc).2 (Units.mk0 x hx)
  exact ⟨i, (congrArg Units.val hi).symm⟩

theorem ofK_ne_zero' {a : K} (h : a ≠ 0) : ofK a ≠ 0 := fun h0 ↦
  h (ofK_injective (h0.trans (map_zero (algebraMap K E)).symm))

theorem limb_zero : (0 : E).limb 0 = 0 := by
  rw [show (0 : E) = ofK 0 from (map_zero (algebraMap K E)).symm, limb_ofK]
  rfl

theorem limb0_ne_zero {x : E} (h : x ≠ 0) (hk : IsInK x) : x.limb 0 ≠ 0 := by
  intro h0
  apply h
  rw [Core.eq_ofK_limb hk, h0]
  exact map_zero (algebraMap K E)

/-- An `NZ` word is a power of `g`. -/
theorem NZ.pow {x : E} (h : NZ x) : ∃ n, x = ofK (addressOfIndex n) := by
  obtain ⟨n, hn⟩ := exists_gpow (limb0_ne_zero h.2 h.1)
  exact ⟨n, by rw [Core.eq_ofK_limb h.1, hn]⟩

theorem nz_gpow (n : ℕ) : NZ (ofK (addressOfIndex n)) :=
  ⟨B2C.isInK_ofK _, ofK_ne_zero' (gpow_ne_zero n)⟩

theorem NZ.mul {a b : E} (ha : NZ a) (hb : NZ b) : NZ (a * b) :=
  ⟨isInK_mul ha.1 hb.1, mul_ne_zero ha.2 hb.2⟩

/-- A factor of an `NZ` product by a nonzero value of `K` is `NZ`. -/
theorem NZ.of_mul {a b : E} (hd : NZ (a * b)) (ha : IsInK a) : NZ b := by
  have ha0 : a ≠ 0 := fun h ↦ hd.2 (by rw [h, zero_mul])
  have hb0 : b ≠ 0 := fun h ↦ hd.2 (by rw [h, mul_zero])
  refine ⟨?_, hb0⟩
  obtain ⟨x, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨y, hy⟩ := (isInK_iff _).mp hd.1
  have hx : x ≠ 0 := fun h ↦ ha0 (by rw [h]; exact map_zero (algebraMap K E))
  have : b = ofK (x⁻¹ * y) := by
    rw [ofK_mul, ← hy, show ofK x⁻¹ = (ofK x)⁻¹ from map_inv₀ (algebraMap K E) x, inv_mul_cancel_left₀ ha0]
  rw [this]
  exact B2C.isInK_ofK _

/-! ## The checks' soundness -/

theorem veq_eq {a b : V} (h : veq a b = true) : a = b := by
  simp only [veq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- A loaded address is nonzero, on a memory whose addresses are. -/
theorem load_nz {rd : Reader} (hrd : ∀ a w, rd a = some w → a ≠ 0) {p d : E} {off : ℕ}
    (h : LoadHolds rd p off d) : NZ p := by
  refine ⟨h.1, fun h0 ↦ hrd _ _ h.2 ?_⟩
  rw [h0, limb_zero, zero_mul]

section

variable {rd : Reader} {σ : Val}

theorem pinIn_sound {v : V} {e : Ev} (hh : e.Holds rd σ) (hp : pinIn v e = true) : IsInK (σ v) := by
  rcases e with a | _ | _ | _
  all_goals try (simp [pinIn] at hp; done)
  cases a
  all_goals try (simp [pinIn] at hp; done)
  all_goals simp only [pinIn, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  all_goals simp only [Ev.Holds, Atom.Holds] at hh
  case const d w =>
    rw [veq_eq hp.1] at hh
    rw [hh]; exact hp.2
  case load d p off => rw [← veq_eq hp]; exact hh.1
  case rangeCheck x y t1 t2 k =>
    rcases hp with hp | hp <;> rw [← veq_eq hp]
    · exact hh.1.1
    · exact hh.2.2.1
  case assertInK a b =>
    rcases hp with hp | hp <;> rw [← veq_eq hp]
    · exact hh.1
    · exact hh.2
  case frameAddr p run => rw [← veq_eq hp]; exact hh.1
  case touch t p => rw [← veq_eq hp]; exact hh.1

/-- **`kIn` puts its value in `K`.** -/
theorem kIn_sound {kv : List V} {sp : List Ev} (hkv : ∀ u ∈ kv, IsInK (σ u)) (hh : ∀ e ∈ sp, e.Holds rd σ) :
    ∀ n v, kIn kv sp n v = true → IsInK (σ v)
  | 0, v, h => by
    simp only [kIn, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨u, hu, he⟩ | ⟨e, he, hp⟩
    · rw [← veq_eq he]; exact hkv u hu
    · exact pinIn_sound (hh e he) hp
  | n + 1, v, h => by
    simp only [kIn, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with (⟨u, hu, he⟩ | ⟨e, he, hp⟩) | ⟨e, he, hm⟩
    · rw [← veq_eq he]; exact hkv u hu
    · exact pinIn_sound (hh e he) hp
    · cases e with
      | atom a =>
        cases a <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at hm
        rename_i d x y
        obtain ⟨⟨hd, hx⟩, hy⟩ := hm
        have := hh _ he
        simp only [Ev.Holds, Atom.Holds] at this
        rw [← veq_eq hd, this]
        exact isInK_mul (kIn_sound hkv hh n x hx) (kIn_sound hkv hh n y hy)
      | _ => simp at hm

/-- The listed words of a context's calls are `NZ`. -/
def UpCtx (σ : Val) (sp : List Ev) : Prop :=
  ∀ g args rets, Ev.call g args rets ∈ sp → UpOk g (args.map σ) (rets.map σ)

theorem pinNz_sound (hrd : ∀ a w, rd a = some w → a ≠ 0) {sp : List Ev} (hup : UpCtx σ sp) {v : V} {e : Ev}
    (he : e ∈ sp) (hh : e.Holds rd σ) (hp : pinNz v e = true) : NZ (σ v) := by
  rcases e with a | _ | ⟨g, args, rets⟩ | _
  all_goals try (simp [pinNz] at hp; done)
  · cases a
    all_goals try (simp [pinNz] at hp; done)
    all_goals simp only [pinNz, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hp
    all_goals simp only [Ev.Holds, Atom.Holds] at hh
    case const d w =>
      obtain ⟨⟨hd, h1⟩, h0⟩ := hp
      rw [veq_eq hd] at hh
      rw [hh]
      exact ⟨h1, fun h ↦ h0 (by rw [h, limb_zero])⟩
    case load d p off => rw [← veq_eq hp]; exact load_nz hrd hh
    case rangeCheck x y t1 t2 k =>
      rcases hp with hp | hp <;> rw [← veq_eq hp]
      · exact load_nz hrd hh.1
      · exact load_nz hrd hh.2.2
    case touch t p => rw [← veq_eq hp]; exact load_nz hrd hh
  · simp only [pinNz, upAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨c, hc, hw, hg⟩ := hp
    split at hw
    · rename_i w hwv
      have hv := veq_eq hw
      subst hv
      exact hup g args rets he c hc hg (σ w) (by rw [← List.map_append, List.getElem?_map, hwv]; rfl)
    · cases hw

/-- **`nzOf` puts its value nonzero in `K`**, given its listed values, its context's events holding on
a memory whose addresses are nonzero, and its context's calls' listed words. -/
theorem nzOf_sound (hrd : ∀ a w, rd a = some w → a ≠ 0) {kv : List V} {sp : List Ev}
    (hkv : ∀ u ∈ kv, NZ (σ u)) (hh : ∀ e ∈ sp, e.Holds rd σ) (hup : UpCtx σ sp) :
    ∀ n v, nzOf kv sp n v = true → NZ (σ v)
  | 0, v, h => by
    simp only [nzOf, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨u, hu, he⟩ | ⟨e, he, hp⟩
    · rw [← veq_eq he]; exact hkv u hu
    · exact pinNz_sound hrd hup he (hh e he) hp
  | n + 1, v, h => by
    have hk := kIn_sound (rd := rd) (σ := σ) (fun u hu ↦ (hkv u hu).1) hh
    simp only [nzOf, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with (⟨u, hu, he⟩ | ⟨e, he, hp⟩) | ⟨e, he, hm⟩
    · rw [← veq_eq he]; exact hkv u hu
    · exact pinNz_sound hrd hup he (hh e he) hp
    · cases e with
      | atom a =>
        have hhe := hh _ he
        cases a <;> simp only [Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hm <;>
          simp only [Ev.Holds, Atom.Holds] at hhe
        · rename_i d x y
          rcases hm with (⟨⟨hd, hx⟩, hy⟩ | ⟨⟨hd, hx⟩, hy⟩) | ⟨⟨hd, hx⟩, hy⟩
          · rw [← veq_eq hd, hhe]
            exact (nzOf_sound hrd hkv hh hup n x hx).mul (nzOf_sound hrd hkv hh hup n y hy)
          · rw [← veq_eq hd]
            have := nzOf_sound hrd hkv hh hup n d hy
            rw [hhe] at this
            exact this.of_mul (hk _ x hx)
          · rw [← veq_eq hd]
            have := nzOf_sound hrd hkv hh hup n d hy
            rw [hhe, mul_comm] at this
            exact this.of_mul (hk _ y hx)
        · rename_i d s
          rcases hm with ⟨hd, hs⟩ | ⟨hd, hs⟩
          · rw [← veq_eq hd, hhe]; exact nzOf_sound hrd hkv hh hup n s hs
          · rw [← veq_eq hd, ← hhe]; exact nzOf_sound hrd hkv hh hup n d hs
      | _ => simp at hm

end

/-! ## The listed words of a valid tree -/

theorem call_mem_calls {es : List Ev} {g : String} {args rets : List V} (h : Ev.call g args rets ∈ es) :
    (⟨g, args, rets, true⟩ : Call) ∈ calls es := mem_calls_of_call h

theorem carryNzG_of {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) : carryNzG fn = true :=
  carryNz_all fn (List.mem_of_find?_eq_some hf)

section

variable {rd : Reader}

mutual
/-- **The listed words of a valid node are `NZ`.** -/
theorem up_valid (hrd : ∀ a w, rd a = some w → a ≠ 0) :
    ∀ (t : Tree) {args rets : List E}, t.Valid coreProgram rd args rets → UpOk t.name args rets
  | .node f σ _ kids, args, rets, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ => by
    have hname : fn.name = f := fn_name_of_find hf
    have hG := carryNzG_of hf
    simp only [carryNzG, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hG
    have hupc : ∀ ctx : List Ev, (∀ x ∈ ctx, x ∈ es) → UpCtx σ ctx := fun ctx hctx g a r hg ↦
      Tree.KidsValid.up hrd σ kids (calls es) hk _ (call_mem_calls (hctx _ hg)) rfl
    have hsp : ∀ x ∈ spineE fn.body, x ∈ es := by
      have := spineE_sub (σ := σ) fn.body (by rw [hw]; simp)
      rwa [hw] at this
    intro c hc hcf w hwc
    have hu := (hG.2 c hc).resolve_left (by rw [hname, hcf]; exact not_not.mpr rfl)
    have hlen : args.length = fn.params.length := by rw [← hp, List.length_map]
    unfold upChk at hu
    split at hu
    · rename_i p hpi
      have hlt : c.2 < fn.params.length := (List.getElem?_eq_some_iff.mp hpi).1
      rw [List.getElem?_append_left (by omega), ← hp, List.getElem?_map, hpi, Option.map_some,
        Option.some.injEq] at hwc
      subst hwc
      exact nzOf_sound hrd (by simp) (fun e he ↦ hes e (hsp e he)) (hupc _ hsp) _ _ hu
    · rename_i hpi
      have hge : fn.params.length ≤ c.2 := by
        by_contra h
        rw [List.getElem?_eq_none_iff] at hpi
        omega
      obtain ⟨ctx, hret, hctx⟩ := allB_body_ret (σ := σ) hu hw
      rw [List.getElem?_append_right (by omega), ← hr, hlen, List.getElem?_map] at hwc
      simp only [retNz] at hret
      split at hret
      · rename_i v hv
        rw [hv, Option.map_some, Option.some.injEq] at hwc
        subst hwc
        exact nzOf_sound hrd (by simp) (fun e he ↦ hes e (hctx e he)) (hupc _ hctx) _ _ hret
      · cases hret
  | .phantom .., _, _, h => h.elim

/-- `up_valid` for the callees: each call entered has its listed words `NZ`. -/
theorem Tree.KidsValid.up (hrd : ∀ a w, rd a = some w → a ≠ 0) : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValid coreProgram rd σ cs ks → ∀ c ∈ cs, c.taken = true → UpOk c.f (c.args.map σ) (c.rets.map σ)
  | _, [], [], _, _, hc, _ => (List.not_mem_nil hc).elim
  | σ, k :: ks, c :: cs, ⟨hn, hk, hks⟩, c', hc', ht => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [ite_eq_left ht] at hk
        rw [← hn]
        exact up_valid hrd k hk
      · exact Tree.KidsValid.up hrd σ ks cs hks c' hc' ht
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
end

end

/-! ## At the honest instances -/

section

variable {r : Ref}

theorem ref_rd (hr : r.Ok) : ∀ a w, r.img.read a = some w → a ≠ 0 := fun a w h ↦ by
  obtain ⟨i, -, rfl⟩ := read_pow h (logMemorySize_le_28 (e := r.exec) hr.size)
  exact gpow_ne_zero i

/-- The values `kvNz` lists of an honest instance are `NZ`, given its carried parameters. -/
theorem kvNz_sound (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hQ : CarryNzQ I) : ∀ u ∈ kvNz fn, NZ (σ u) := by
  have hname : fn.name = f := fn_name_of_find hf
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · obtain ⟨c, hc, hcu⟩ := List.mem_filterMap.mp hu
    split_ifs at hcu with hb
    exact hQ f σ bufs kids hIt fn hf c hc (by rw [← hname]; exact beq_iff_eq.mp hb) u hcu
  · split_ifs at hu with hl
    · obtain ⟨p0, prest, e', hps, hσ⟩ := inst_ctr hr hI hIt hf hl
      rw [hps] at hu
      simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hu
      rw [hu, hσ]
      exact nz_gpow e'
    · simp at hu

/-- **The carried parameters pass down a call.** -/
theorem carryNzQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) CarryNzQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph hQI
    f σ bufs kids hJt fn hfn cc hcc hcf v hv
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn', hfn', hpar, -⟩ := hJv
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hfn')
  have hcf' : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the call's event and the statement emitting it
  obtain ⟨e, he, hec⟩ := List.mem_filterMap.mp hc
  have hev : e = .call c.f c.args c.rets := by
    rcases e with _ | _ | ⟨g, a, r'⟩ | ⟨g, a⟩ <;> simp only [Ev.call?, reduceCtorEq] at hec
    · obtain rfl := Option.some.inj hec; rfl
    · obtain rfl := Option.some.inj hec; cases hct
  subst hev
  have hG := carryNzG_of hfI
  simp only [carryNzG, Bool.and_eq_true] at hG
  obtain ⟨ctx, s, hs, hem, hctx⟩ := allB_body hG.1 hw _ he
  have hrd := ref_rd hr
  obtain ⟨args', rets', hvI⟩ := inst_valid' hr hI hIt
  obtain ⟨fnI', hfI', -, es', vs', hw', -, -, hkI⟩ := hvI
  obtain rfl : fnI = fnI' := Option.some.inj (hfI.symm.trans hfI')
  rw [hw] at hw'
  obtain ⟨rfl, rfl⟩ := Out.ret.inj hw'
  have hpin : ∀ a, nzOf (kvNz fnI) ctx nzDepth a = true → NZ (σI a) := fun a ha ↦
    nzOf_sound hrd (kvNz_sound hr hI hIt hfI hQI) (fun x hx ↦ hh x (hctx x hx))
      (fun g a' r' hg ↦ Tree.KidsValid.up hrd σI kidsI (calls es) hkI _ (call_mem_calls (hctx _ hg)) rfl) _ a ha
  have hsite : siteNz (kvNz fnI) ctx c.f c.args = true := by
    rcases s with a | _ | _ | ⟨g, a', r'⟩ | ⟨b, g, a'⟩ | ⟨x, gs, a', r'⟩ | _
    all_goals try (simp [Emits] at hem; done)
    · simp only [Emits, Ev.call.injEq] at hem
      obtain ⟨rfl, rfl, rfl⟩ := hem; exact hs
    · simp only [Emits, reduceCtorEq, Ev.call.injEq, false_or] at hem
      obtain ⟨rfl, rfl, -⟩ := hem; exact hs
    · simp only [Emits, Ev.call.injEq] at hem
      obtain ⟨g, hg, rfl, rfl, -⟩ := hem
      exact List.all_eq_true.mp hs _ hg
  have hs' := List.all_eq_true.mp hsite cc hcc
  rw [hcf', ← hcf] at hs'
  simp only [bne_self_eq_false, Bool.false_or] at hs'
  have hpv : (fn.params.map σ)[cc.2]? = some (σ v) := by simp [hv]
  rw [hpar] at hpv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hpv
  obtain ⟨a, ha, hav⟩ := hpv
  rw [ha] at hs'
  rw [← hav]
  exact hpin a hs'

/-- **The carried parameters at every honest instance.** -/
theorem carryNzQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, CarryNzQ J := by
  refine insts_all hr (carryNzQ_step hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt fn _ c hc hcf
  have hn := hm _ _ _ _ hJt
  subst hn
  have : ∀ c ∈ carriedNz, c.1 ≠ "main" := by decide
  exact absurd hcf (this c hc)

end

/-- **Every dynamic `HeapBuf`'s size is a power of `g`**, at every honest instance. -/
theorem dynPow_guest : DynPow := by
  intro r hr I hI f σ bufs kids hIt d s hev
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv
  rw [hIt, events_node hf hw] at hev
  have hG := carryNzG_of hf
  simp only [carryNzG, Bool.and_eq_true] at hG
  obtain ⟨ctx, st, hs, hem, hctx⟩ := allB_body hG.1 hw _ hev
  have hs' : nzOf (kvNz fn) ctx nzDepth s = true := by
    rcases st with a | _ | _ | _ | _ | _ | _
    all_goals try (simp [Emits] at hem; done)
    simp only [Emits, Ev.atom.injEq] at hem
    subst hem
    exact hs
  have hrd := ref_rd hr
  have hnz := nzOf_sound hrd (kvNz_sound hr hI hIt hf (carryNzQ_all hr I hI)) (fun x hx ↦ hh x (hctx x hx))
    (fun g a' r' hg ↦ Tree.KidsValid.up hrd σ kids (calls es) hk _ (call_mem_calls (hctx _ hg)) rfl) _ _ hs'
  obtain ⟨n, hn⟩ := hnz.pow
  classical
  have hex : ∃ e, I.t.val s = ofK (addressOfIndex e) := ⟨n, by rw [hIt]; exact hn⟩
  unfold logG
  split
  · rename_i h; exact Nat.find_spec h
  · contradiction

end

end LeanVM.Guest.EndExec
