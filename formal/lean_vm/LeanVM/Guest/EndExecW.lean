/-
  LeanVM.Guest.EndExecW

  Facts carried down the honest tree at listed parameters (`Res.carried`): the heap witness
  pointers no spine pins, powers below `maxCells` (`WitPtrRes`).
-/

module

public import LeanVM.Guest.EndExecYPtr
public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.Gen.CarryOk
public import LeanVM.Guest.B1.Bits.Log2
public import LeanVM.Guest.B1.Bits.Tables

/-!
# Facts carried at listed parameters

`CarryQ r J`: at an instance `J` of a callee listed in `Res.carried`, each listed parameter holds
its fact (`KH`): in `K`, or the base of the exponent tables, their window section included, on the
reference memory.

`carryQ_all`: at every honest instance, by `Res.insts_down`. A caller passes the facts on at every
call site (`Res.carry_all`, the check `Res.carryG`): an argument in `K` (`Res.kOf`) is one of the
caller's carried values, its loop counter (a power of `g`, `Res.insts_ctr`), pinned by an atom of
its spine on the path (an allocation by the placement, `Inst.nodeAt`; a load, touch, range check or
frame address holding on the reference), or a product of such; the tables' base is one of the
caller's carried values or the return of a call of `exponent_tables` on the path
(`exponent_tables_holds`). `main` is listed nowhere.

`witPtrRes_guest : WitPtrRes`: a heap witness pointer its spine does not pin is in `K` by the
carried values (`carryG`), and its hint writes the memory from offset `0`, so the pointer is a
power below `maxCells`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (Kd carried cvars pinK kOf scanCall pin siteC witAtomC carryG carry_all)
open LeanVM.Protocol.Verifier (gen)

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
        exact LeanVM.Guest.B1.isInK_mul (kOf_sound hkv hpin hh n x hx) (kOf_sound hkv hpin hh n y hy)
      | _ => simp at hm

/-- **A top-level call is on every returning path.** -/
theorem scanCall_sound {σ : Val} {p : String → List V → List V → Bool} :
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
      obtain ⟨f, args, rets, hp, he⟩ := scanCall_sound h h2
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

variable {r : Ref}

theorem inst_valid' (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    ∃ args rets, (Memory.Tree.node f σ bufs kids).Valid coreProgram r.img.read args rets := by
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  rcases insts_good r.T _ r.hdr hv I hI with ⟨args, rets, hval⟩ | ⟨_, _, hph⟩
  · rw [ht] at hval; exact ⟨args, rets, hval⟩
  · rw [ht] at hph; cases hph

/-- A loop helper's counter at an honest instance is a power of `g`. -/
theorem inst_ctr (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hn : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hl : fn.loop = true) :
    ∃ p0 prest e', fn.params = p0 :: prest ∧ σ p0 = ofK (addressOfIndex e') := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  have hroot : Res.CtrOk coreProgram B2C.fs (r.T.total B2C.fs + 1) r.T := by
    intro f' σ' _ _ fn' hT' hg hl'
    have := (progOk_guest.loop f' fn' hg hl').1
    have hn' := hr.name
    rw [hT'] at hn'
    simp only [Tree.name] at hn'
    subst hn'
    exact absurd this (by decide)
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨p0, prest, e1, hps, hσ0, -⟩ := Res.insts_ctr hfs progOk_guest r.T _ r.hdr hH.valid le_rfl hroot I hI
    f σ bufs kids fn hn hf hl
  exact ⟨p0, prest, e1, hps, hσ0⟩

/-- **An atom on an honest instance's path pins in `K`.** -/
theorem pinK_sound (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node f σ bufs kids)
    {es : List Ev} (hev : I.t.events coreProgram = es) (hh : ∀ e ∈ es, e.Holds r.img.read σ)
    {a : Atom} (ha : Ev.atom a ∈ es) {v : V} (hp : pinK v a = true) : IsInK (σ v) := by
  have hhold : a.Holds r.img.read σ := hh _ ha
  cases a with
  | hint h =>
    have hal : Bridge.allocOf (.hint h) = some v := by
      cases h <;> simp_all [pinK, Bridge.allocOf]
    obtain ⟨t, ν, hv, -, hpl, -, -, -, hTt⟩ := hr.tree
    have hTp : r.T.Placed coreProgram B2C.fs B2C.cert (0, r.T.block B2C.fs coreProgram.loop) := by
      rw [hTt, block_retemp]
      exact placed_retemp coreProgram_fresh t _ hv hpl
    have hI' : I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
    have h1 := (Inst.nodeAt (insts_placedAt r.T _ r.hdr hTp I hI') (insts_placed r.T _ r.hdr (by omega) I hI') hIt).1
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
theorem pin_sound (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds r.img.read σ) (hQ : CarryQ r I) {kd : Kd} {a : V} (hp : pin fn kd a = true) :
    KH r kd (σ a) := by
  have hname : fn.name = f := fn_name_of_find hf
  have hev : I.t.events coreProgram = es := by rw [hIt]; exact events_node hf hw
  have hcar : ∀ kd u, u ∈ cvars fn kd → (∃ c ∈ carried, c.1 = fn.name ∧ c.2.2 = kd ∧ fn.params[c.2.1]? = some u) →
      KH r kd (σ u) := fun kd u _ ⟨c, hc, h1, h2, h3⟩ ↦ by
    rw [← h2]; exact hQ f σ bufs kids hIt fn hf c hc (by rw [h1, hname]) u h3
  cases kd with
  | inK =>
    refine kOf_sound (rd := r.img.read) (fun u hu ↦ ?_) (fun b hb v hv ↦ ?_) (fun b hb ↦ ?_) _ _ hp
    · rcases cvars_mem hu with h | ⟨-, hl, hu'⟩
      · exact hcar .inK u hu h
      · obtain ⟨p0, prest, e', hps, hσ⟩ := inst_ctr hr hI hIt hf hl
        rw [hps] at hu'
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hu'
        rw [hu', hσ]
        exact B2C.isInK_ofK _
    · exact pinK_sound hr hI hIt hev hh (Bridge.spine_on_path _ hw b hb) hv
    · exact hh _ (Bridge.spine_on_path _ hw b hb)
  | tab =>
    simp only [pin, Bool.or_eq_true, List.contains_iff_mem] at hp
    rcases hp with hu | hs
    · rcases cvars_mem hu with h | ⟨h, -⟩
      · exact hcar .tab a hu h
      · cases h
    · obtain ⟨g, args, rets, hp, he⟩ := scanCall_sound hs hw
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
      obtain ⟨args', rets', hv⟩ := inst_valid' hr hI hIt
      obtain ⟨fn', hf', -, es', vs', hw', -, -, hk⟩ := hv
      obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
      rw [hw] at hw'
      obtain ⟨rfl, -⟩ := Out.ret.inj hw'
      have hrel := Tree.KidsValid.rel σ kids (calls es) hk _ (mem_calls_of_call he) rfl
      exact (B1.exponent_tables_holds _ _ _).mp hrel

/-- **The carried facts pass down a call.** -/
theorem carryQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (CarryQ r) := by
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
  exact pin_sound hr hI hIt hfI hw hh hQI hs'

/-- **The carried facts at every honest instance.** -/
theorem carryQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, CarryQ r J := by
  refine insts_all hr (carryQ_step hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt fn _ c hc hcf
  have hn := hm _ _ _ _ hJt
  subst hn
  have : ∀ c ∈ carried, c.1 ≠ "main" := by decide
  exact absurd hcf (this c hc)

end

/-! ## The heap witness pointers -/

/-- **The heap witness pointers the spine does not pin** are powers below `maxCells`. -/
theorem witPtrRes_guest : WitPtrRes := by
  intro r hr I hI f σ bufs kids hIt fn hfn S p off len hatom hpk
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hv' := hv
  obtain ⟨fn', hf', -, es, vs, hw, -, hh, -⟩ := hv'
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hf')
  have hev : I.t.events coreProgram = es := by rw [hIt]; exact events_node hfn hw
  rw [hev] at hatom
  have hG := carry_all fn (List.mem_of_find?_eq_some hfn)
  simp only [carryG, Bool.and_eq_true] at hG
  have hA := Bridge.blockAll_sound _ fn.body hG.2 _ (B2C.walk_atoms fn.body (by rw [hw]; exact hatom))
  simp only [witAtomC, hpk, Bool.false_or, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hA
  obtain ⟨⟨hk, rfl⟩, hlen⟩ := hA
  -- in `K`, by the carried values
  have hK : IsInK (σ p) := by
    have := pin_sound hr hI hIt hfn hw hh (carryQ_all hr I hI) (kd := .inK) (a := p) hk
    exact this
  -- a word of the memory, by the hint's first
  obtain ⟨len', rfl⟩ : ∃ len', len = len' + 1 := ⟨len - 1, by omega⟩
  have hA' : (σ p).limb 0 * addressOfIndex (0 + 0) ∈ hintWords coreProgram B2C.fs B2C.H r.hdr r.T := by
    refine List.mem_flatMap.mpr ⟨I, hI, ?_⟩
    simp only [Inst.hintAddrs, hIt]
    refine List.mem_flatMap.mpr ⟨.atom (.hint (.witness S (.heap p 0 (len' + 1)))), by rw [← hIt, hev]; exact hatom, ?_⟩
    simp only [Ev.hintAddrs]
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), rfl⟩
  obtain ⟨w, -, hrd⟩ := hr.hintWords _ hA'
  rw [show addressOfIndex (0 + 0) = 1 by simp [addressOfIndex], mul_one] at hrd
  obtain ⟨b, hb, he⟩ := read_pow hrd hκ
  exact ⟨b, hb, by rw [Core.eq_ofK_limb hK, he]⟩

end

end LeanVM.Guest.EndExec
