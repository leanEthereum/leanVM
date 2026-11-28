/-
  LeanVM.Guest.EndExecW

  Facts carried down b2c's aligned honest tree at listed parameters (`Res.carried`): the heap
  witness pointers no spine pins in `K`, written from offset `0`.
-/

module

public import LeanVM.Guest.EndExecInstA
public import LeanVM.Guest.CoreMode.Fam.ProgOkG
public import LeanVM.Guest.CoreMode.Fam.LoopTreeA
public import LeanVM.Guest.CoreMode.Gen.CarryOk
public import LeanVM.Guest.B1.Bits.Log2
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.Bridge.Pair
public import LeanVM.Guest.B2C.ShareSound

/-!
# Facts carried at listed parameters, aligned

The bus era's `EndExecW` on b2c's aligned tree (`instsR al D r`, a reference run of the honest tree,
`RefH`). `CarryQ r J`: at an instance `J` of a callee listed in `Res.carried`, each listed parameter
holds its fact (`KH`): in `K`, or the base of the exponent tables, their window section included, on
the reference memory.

`carryQ_allA`: at every honest instance, by `insts_allA`. A caller passes the facts on at every call
site (`Res.carry_all`, the check `Res.carryG`): an argument in `K` (`Res.kOf`) is one of the caller's
carried values, its loop counter (a power of `g`, `Res.instsA_ctr`), pinned by an atom of its spine on
the path (an allocation by the placement, `HonestAtA.nodeAt`; a load, touch, range check or frame
address holding on the reference), or a product of such; the tables' base is one of the caller's
carried values or the return of a call of `exponent_tables` on the path (`exponent_tables_holds`).
`main` is listed nowhere.

`witPtrK_carry`: a heap witness pointer its spine does not pin is in `K` by the carried values
(`carryG`'s `witAtomC`), and its hint writes from offset `0` at least one word.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (Kd carried cvars pinK kOf scanCall pin siteC witAtomC carryG carry_all)

@[expose] public section

/-- A carried fact of a value, on the reference memory. -/
def KH (r : Ref) : Kd → E → Prop
  | .inK, x => IsInK x
  | .tab, x => B1.ExpTables r.img.read x ∧ B1.ExpWinTab r.img.read x

/-- **The carried facts at an instance.** -/
def CarryQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ carried,
    c.1 = f → ∀ v, fn.params[c.2.1]? = some v → KH r c.2.2 (σ v)

end

public section

/-! ## The checks' soundness -/

theorem isInK_mulW {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a * b) := by
  obtain ⟨x, rfl⟩ := (isInK_iff a).mp ha
  obtain ⟨y, rfl⟩ := (isInK_iff b).mp hb
  rw [← ofK_mul]
  exact B2C.isInK_ofK _

/-- **`kOf` puts its value in `K`**, given its listed values and the atoms pinning in `K`. -/
theorem kOf_sound {kv : List V} {sp : List Atom} {σ : Val} {rd : Reader}
    (hkv : ∀ u ∈ kv, IsInK (σ u)) (hpin : ∀ a ∈ sp, ∀ v, pinK v a = true → IsInK (σ v))
    (hh : ∀ a ∈ sp, a.Holds rd σ) : ∀ n v, kOf kv sp n v = true → IsInK (σ v)
  | 0, v, h => by
    simp only [kOf, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] at h
    rcases h with h | ⟨a, ha, hp⟩
    · exact hkv v h
    · exact hpin a ha v hp
  | n + 1, v, h => by
    simp only [kOf, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] at h
    rcases h with (h | ⟨a, ha, hp⟩) | ⟨a, ha, hm⟩
    · exact hkv v h
    · exact hpin a ha v hp
    · cases a with
      | mul d x y =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        obtain ⟨⟨rfl, hx⟩, hy⟩ := hm
        have := hh _ ha
        simp only [Atom.Holds] at this
        rw [this]
        exact isInK_mulW (kOf_sound hkv hpin hh n x hx) (kOf_sound hkv hpin hh n y hy)
      | _ => simp at hm

/-- **A top-level call is on every returning path.** -/
theorem scanCall_soundW {σ : Val} {p : String → List V → List V → Bool} :
    ∀ {ss : List Stmt} {es : List Ev} {vs : List V}, scanCall p ss = true → walk σ ss = .ret es vs →
      ∃ f args rets, p f args rets = true ∧ Ev.call f args rets ∈ es
  | [], _, _, h, _ => by simp [scanCall] at h
  | s :: ss, es, vs, h, hw => by
    simp only [scanCall, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hn, h⟩
    · cases s with
      | call f args rets =>
        rw [walk] at hw
        simp only [walk1, Out.seq] at hw
        cases h2 : walk σ ss with
        | fall _ => rw [h2] at hw; simp [Out.pre] at hw
        | ret es2 vs2 =>
          rw [h2] at hw
          simp only [Out.pre, Out.ret.injEq] at hw
          exact ⟨f, args, rets, h, by rw [← hw.1]; exact List.mem_cons_self⟩
        | stuck => rw [h2] at hw; simp [Out.pre] at hw
      | _ => simp at h
    · obtain ⟨es1, es2, -, h2, rfl⟩ := Res.walk_cons_noRet hn hw
      obtain ⟨f, args, rets, hp, he⟩ := scanCall_soundW h h2
      exact ⟨f, args, rets, hp, List.mem_append_right _ he⟩

theorem cvars_mem {fn : Fn} {kd : Kd} {u : V} (h : u ∈ cvars fn kd) :
    (∃ c ∈ carried, c.1 = fn.name ∧ c.2.2 = kd ∧ fn.params[c.2.1]? = some u) ∨
      (kd = .inK ∧ fn.loop = true ∧ u ∈ fn.params.take 1) := by
  unfold cvars at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨c, hc, hu⟩ := List.mem_filterMap.mp h
    split_ifs at hu with hb
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact Or.inl ⟨c, hc, hb.1, hb.2, hu⟩
  · split_ifs at h with hb
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact Or.inr ⟨hb.1, hb.2, h⟩
    · simp at h

/-! ## At the honest instances -/

section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **A loop helper's counter at an honest instance is a power of `g`.** -/
theorem inst_ctrW (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hn : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hl : fn.loop = true) :
    ∃ p0 prest e', fn.params = p0 :: prest ∧ σ p0 = ofK (addressOfIndex e') := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  have hroot : Res.CtrOk coreProgram B2C.fs ((D r).T.total B2C.fs + 1) (D r).T := by
    intro f' σ' _ _ fn' hT' hg hl'
    have := (progOk_guest.loop f' fn' hg hl').1
    have hn' := hR.name
    rw [hT'] at hn'
    simp only [Tree.name] at hn'
    subst hn'
    exact absurd this (by decide)
  have hfs : ∀ g, 1 ≤ B2C.fs g := fun g ↦ le_trans (by norm_num) (B2C.two_le_fs g)
  obtain ⟨p0, prest, e1, hps, hσ0, -⟩ := Res.instsA_ctr hfs progOk_guest (D r).T _ r.hdr hH.valid le_rfl hroot I hI
    f σ bufs kids fn hn hf hl
  exact ⟨p0, prest, e1, hps, hσ0⟩

/-- **An atom on an honest instance's path pins in `K`.** -/
theorem pinK_soundA (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node f σ bufs kids)
    {es : List Ev} (hev : I.t.events coreProgram = es) (hh : ∀ e ∈ es, e.Holds r.img.read σ)
    {a : Atom} (ha : Ev.atom a ∈ es) {v : V} (hp : pinK v a = true) : IsInK (σ v) := by
  have hhold : a.Holds r.img.read σ := hh _ ha
  cases a with
  | hint h =>
    have hal : Bridge.allocOf (.hint h) = some v := by
      cases h <;> simp_all [pinK, Bridge.allocOf]
    obtain ⟨rd, hH, -⟩ := hR.honest
    have h1 := (hH.nodeAt hI hIt).1
    have h2 : σ v ∈ (allocDsts (I.t.events coreProgram)).map σ :=
      List.mem_map.mpr ⟨v, by rw [hev]; exact Bridge.allocDsts_of_mem ha hal, rfl⟩
    rw [h1] at h2
    obtain ⟨b, -, hb⟩ := List.mem_map.mp h2
    rw [← hb]
    exact B2C.isInK_ofK _
  | load d p off =>
    simp only [pinK, decide_eq_true_eq] at hp
    subst hp
    exact hhold.1
  | touch t p =>
    simp only [pinK, decide_eq_true_eq] at hp
    subst hp
    exact hhold.1
  | rangeCheck x y t1 t2 k =>
    simp only [pinK, Bool.or_eq_true, decide_eq_true_eq] at hp
    rcases hp with rfl | rfl
    · exact hhold.1.1
    · exact hhold.2.2.1
  | frameAddr p run =>
    simp only [pinK, decide_eq_true_eq] at hp
    subst hp
    exact hhold.1
  | _ => simp [pinK] at hp

/-- **A pinned value holds its fact** at an honest instance with its carried facts. -/
theorem pin_soundA (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds r.img.read σ) (hQ : CarryQ r I) {kd : Kd} {a : V} (hp : pin fn kd a = true) :
    KH r kd (σ a) := by
  have hname : fn.name = f := find_name' hf
  have hev : I.t.events coreProgram = es := by rw [hIt]; exact events_node hf hw
  have hcar : ∀ kd u, (∃ c ∈ carried, c.1 = fn.name ∧ c.2.2 = kd ∧ fn.params[c.2.1]? = some u) →
      KH r kd (σ u) := fun kd u ⟨c, hc, h1, h2, h3⟩ ↦ by
    rw [← h2]; exact hQ f σ bufs kids hIt fn hf c hc (by rw [h1, hname]) u h3
  cases kd with
  | inK =>
    refine kOf_sound (rd := r.img.read) (fun u hu ↦ ?_) (fun b hb v hv ↦ ?_) (fun b hb ↦ ?_) _ _ hp
    · rcases cvars_mem hu with h | ⟨-, hl, hu'⟩
      · exact hcar .inK u h
      · obtain ⟨p0, prest, e', hps, hσ⟩ := inst_ctrW hR hI hIt hf hl
        rw [hps] at hu'
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hu'
        rw [hu', hσ]
        exact B2C.isInK_ofK _
    · exact pinK_soundA hR hI hIt hev hh (Bridge.spine_on_path _ hw b hb) hv
    · exact hh _ (Bridge.spine_on_path _ hw b hb)
  | tab =>
    simp only [pin, Bool.or_eq_true, List.contains_iff_mem] at hp
    rcases hp with hu | hs
    · rcases cvars_mem hu with h | ⟨h, -⟩
      · exact hcar .tab a h
      · cases h
    · obtain ⟨g, args, rets, hp, he⟩ := scanCall_soundW hs hw
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
      obtain ⟨args', rets', hv⟩ := inst_validA hR hI hIt
      obtain ⟨fn', hf', -, es', vs', hw', -, -, hk⟩ := hv
      obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
      rw [hw] at hw'
      obtain ⟨rfl, -⟩ := Out.ret.inj hw'
      have hrel := Tree.KidsValid.rel σ kids (calls es) hk _ (mem_calls_of_call he) rfl
      exact (B1.exponent_tables_holds _ _ _).mp hrel

/-- **The carried facts pass down a call.** -/
theorem carryQ_stepA (hR : RefH (layB al) (D r) r) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) (CarryQ r) := by
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
  have hG := carry_all fnI (List.mem_of_find?_eq_some hfI)
  simp only [carryG, Bool.and_eq_true] at hG
  have hs : siteC fnI c.f c.args c.rets = true := Res.calls_sites hG.1 hw c hc
  have hs' := List.all_eq_true.mp hs cc hcc
  rw [hcf', ← hcf] at hs'
  simp only [bne_self_eq_false, Bool.false_or] at hs'
  have hpv : (fn.params.map σ)[cc.2.1]? = some (σ v) := by simp [hv]
  rw [hpar] at hpv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hpv
  obtain ⟨a, ha, hav⟩ := hpv
  rw [ha] at hs'
  rw [← hav]
  exact pin_soundA hR hI hIt hfI hw hh hQI hs'

/-- **The carried facts at every honest instance.** -/
theorem carryQ_allA (hR : RefH (layB al) (D r) r) : ∀ J ∈ instsR al D r, CarryQ r J := by
  refine insts_allA hR (carryQ_stepA hR) fun J hm ↦ ?_
  intro f σ bufs kids hJt fn _ c hc hcf
  have hn := hm _ _ _ _ hJt
  subst hn
  have : ∀ c ∈ carried, c.1 ≠ "main" := by decide
  exact absurd hcf (this c hc)

/-! ## The heap witness pointers -/

/-- **The heap witness pointers the spine does not pin** are in `K`, written from offset `0`, at least
one word. -/
theorem witPtrK_carry (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node f σ bufs kids) {fn : Fn}
    (hfn : coreProgram.find? f = some fn) {S : String} {p : V} {off len : ℕ}
    (hatom : Ev.atom (.hint (.witness S (.heap p off len))) ∈ I.t.events coreProgram)
    (hpk : Bridge.ptrOk (Bridge.spine fn.body) p = false) : IsInK (σ p) ∧ off = 0 ∧ 0 < len := by
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI hIt
  obtain ⟨fn', hf', -, es, vs, hw, -, hh, -⟩ := hv
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hf')
  have hev : I.t.events coreProgram = es := by rw [hIt]; exact events_node hfn hw
  rw [hev] at hatom
  have hG := carry_all fn (List.mem_of_find?_eq_some hfn)
  simp only [carryG, Bool.and_eq_true] at hG
  have hA := Bridge.blockAll_sound _ fn.body hG.2 _ (B2C.walk_atoms fn.body (by rw [hw]; exact hatom))
  simp only [witAtomC, hpk, Bool.false_or, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hA
  obtain ⟨⟨hk, rfl⟩, hlen⟩ := hA
  exact ⟨pin_soundA hR hI hIt hfn hw hh (carryQ_allA hR I hI) (kd := .inK) (a := p) hk, rfl, hlen⟩

end

end

end LeanVM.Guest.EndExec
