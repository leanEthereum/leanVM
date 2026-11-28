module

public import NativeRustcVmX64.Ring.Seq
public import NativeRustcVmX64.Basic
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# Functions with stack arguments as sequences of blocks and calls (x86-64)

`NativeRustcVmX64.Ring`'s templates (`Ring.Seq`) for a function reading `A` bytes of stack
arguments above its return address: region `0` of a block's environment (`envA`) is the frame, the
return address and the arguments, the `F + 8 + A` bytes from `stackBelow m0 F` (`LayA`: the
arguments mapped and not wrapping, the arrays apart from them too). Writes into region `0` stay
below its offset `F` (`writeOk`), so the arguments and the return address are kept. The steps
`startA`, `jumpStepA`, `callStepA`, `exitStepA`, `mulStepA` are `Ring.Seq`'s in this
environment.
-/

namespace NativeRustcVmX64.Whir.Rows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Ring

@[expose] public section

/-- The environment of `m`: region `0` the `F` bytes below the entry `m0`'s RSP, its return
address and the `A` bytes of arguments above, then the arrays `rs`. -/
abbrev envA (m0 m : MachineData) (F A : Nat) (rs : List (BitVec 64 × Nat))
    (vals : Nat → BitVec 64) (ret : BitVec 64) : Env :=
  Env.ofMachine m ((stackBelow m0 F, F + 8 + A) :: rs) vals ret

/-- The layout: `Ring.Lay`, and the `A` bytes of arguments above the return address mapped, not
wrapping, apart from the arrays. -/
structure LayA (m0 : MachineData) (F A N : Nat) (rs : List (BitVec 64 × Nat)) : Prop where
  ok : StackOk m0 N
  le : F ≤ N
  f8 : 8 ≤ F
  top : (rspOf m0).toNat + 8 + A ≤ 2 ^ 64
  args : Mapped m0.dmem (rspOf m0 + 8#64) A
  arr : AllOf (fun e : BitVec 64 × Nat ↦
    Mapped m0.dmem e.1 e.2 ∧ NoWrap e.1 e.2 ∧ Apart e.1 e.2 (stackBelow m0 N) (N + 8 + A)) rs
  disj : rs.Pairwise fun e e' ↦ Apart e.1 e.2 e'.1 e'.2

/-- **Between blocks** (`Ring.Bnd` in `envA`). -/
structure BndA [Labels] (m0 : MachineData) (F A N : Nat) (rs : List (BitVec 64 × Nat))
    (wr : Nat → Bool) (T : SState) (vals : Nat → BitVec 64) (m : MachineData) : Prop where
  mt : ∀ ret, Match (envA m0 m F A rs vals ret) T m
  same : SameOutside m0.dmem m.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q)
  kept : Kept m0.dmem m.dmem

end

public section

variable {m0 : MachineData} {F A N : Nat} {rs : List (BitVec 64 × Nat)} {wr : Nat → Bool}

theorem regions_envA {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64} {T : SState}
    (hT : T.regions = (F + 8 + A) :: rs.map Prod.snd) :
    ∀ (r n : Nat), T.regions[r]? = some n →
      ∃ b, (envA m0 m F A rs vals ret).regions[r]? = some (b, n) := by
  intro r n h
  rw [hT] at h
  cases r with
  | zero =>
    cases h
    exact ⟨_, rfl⟩
  | succ r =>
    simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    exact ⟨e.1, by simp [he]⟩

theorem LayA.geo (h : LayA m0 F A N rs) : Geo m0 F N := ⟨h.ok, h.le, h.f8⟩

/-- The layout without the arguments. -/
theorem LayA.lay (h : LayA m0 F A N rs) : Lay m0 F N rs := by
  refine ⟨h.ok, h.le, h.f8, ?_, h.disj⟩
  have harr := h.arr
  clear h
  induction rs with
  | nil => trivial
  | cons e rs ih =>
    refine ⟨⟨harr.1.1, harr.1.2.1, ?_⟩, ih harr.2⟩
    have := harr.1.2.2
    unfold Apart at this ⊢
    omega

/-- Region `0`'s byte `i` as a number. -/
theorem LayA.addr (h : LayA m0 F A N rs) {i : Nat} (hi : i < F + 8 + A) :
    (stackBelow m0 F + BitVec.ofNat 64 i).toNat = (rspOf m0).toNat - F + i := by
  have g := h.geo
  have := h.top
  have := g.sp
  have := g.le
  rw [toNat_add_ofNat _ _ (by rw [g.base]; omega), g.base]

theorem LayA.noWrap0 (h : LayA m0 F A N rs) : NoWrap (stackBelow m0 F) (F + 8 + A) := by
  have g := h.geo
  have := h.top
  have := g.sp
  have := g.le
  unfold NoWrap
  rw [g.base]
  omega

/-- Argument byte `j`: region `0`'s byte `F + 8 + j`. -/
theorem frame_arg (F j : Nat) :
    stackBelow m0 F + BitVec.ofNat 64 (F + 8 + j) = rspOf m0 + 8#64 + BitVec.ofNat 64 j := by
  rw [Nat.add_assoc, frame_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem LayA.mapped0 (h : LayA m0 F A N rs) : Mapped m0.dmem (stackBelow m0 F) (F + 8 + A) := by
  intro i hi
  by_cases hi' : i < F + 8
  · exact h.geo.okF.2.2 i hi'
  · obtain ⟨j, rfl⟩ : ∃ j, i = F + 8 + j := ⟨i - (F + 8), by omega⟩
    rw [frame_arg]
    exact h.args j (by omega)

theorem LayA.frame_apart (h : LayA m0 F A N rs) {e : BitVec 64 × Nat} (he : e ∈ rs) :
    Apart (stackBelow m0 F) (F + 8 + A) e.1 e.2 := by
  have ha := (mem_of_allOf h.arr he).2.2
  have g := h.geo
  have hb := g.base
  have hN := g.below
  have := g.sp
  have := g.le
  unfold Apart at ha ⊢
  omega

theorem LayA.wf (h : LayA m0 F A N rs) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {vals : Nat → BitVec 64} {ret : BitVec 64} : (envA m0 m F A rs vals ret).WF := by
  refine Env.wf_of ⟨⟨fun i hi ↦ hk _ (h.mapped0 i hi), h.noWrap0⟩, ?_⟩ ?_
  · show AllOf _ rs
    have harr := h.arr
    clear h
    induction rs with
    | nil => trivial
    | cons e rs ih =>
      exact ⟨⟨fun i hi ↦ hk _ (harr.1.1 i hi), harr.1.2.1⟩, ih harr.2⟩
  · show List.Pairwise _ ((stackBelow m0 F, F + 8 + A) :: rs)
    exact List.Pairwise.cons (fun e he ↦ h.frame_apart he) h.disj

/-- The bytes of the frame, the arguments and the arrays are outside the stack below the frame's
base. -/
theorem LayA.region_not_stack (h : LayA m0 F A N rs) {S : Nat} (hS : F + S ≤ N)
    {m : MachineData} (hrsp : rspOf m = stackBelow m0 F) {vals : Nat → BitVec 64}
    {ret : BitVec 64} {r : Nat} {b : BitVec 64} {sz j : Nat}
    (hb : (envA m0 m F A rs vals ret).regions[r]? = some (b, sz)) (hj : j < sz) :
    ¬InRange (stackBelow m S) S (b + BitVec.ofNat 64 j) := by
  intro hp
  have g := h.geo
  have hs := g.sp
  have hbase := g.base
  have hmb : (stackBelow m S).toNat = (rspOf m0).toNat - F - S := by
    rw [stackBelow_toNat' (by rw [hrsp, hbase]; omega), hrsp, hbase]
  rw [Sym.inRange_iff (by rw [hmb]; have := g.top; omega), hmb] at hp
  cases r with
  | zero =>
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [h.addr hj] at hp
    omega
  | succ r =>
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ] at hb
    obtain ⟨hm, hnw, hap⟩ := mem_of_allOf h.arr (List.mem_of_getElem? hb)
    simp only at hm hnw hap
    rw [toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)] at hp
    unfold Apart at hap
    rw [g.below] at hap
    omega

/-- A block's writes are in the stack or the writable arrays. -/
theorem LayA.written (h : LayA m0 F A N rs) {m : MachineData} {vals : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState}
    (hw : S.mem.all (writeOk F ((F + 8 + A) :: rs.map Prod.snd) wr) = true) {q : BitVec 64}
    (hq : Written (envA m0 m F A rs vals ret) S q) :
    InRange (stackBelow m0 N) N q ∨ outsOf rs wr q := by
  obtain ⟨w, hwm, b, sz, hb, h1, h2⟩ := hq
  have hok := List.all_eq_true.mp hw w hwm
  simp only [writeOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at hok
  have g := h.geo
  rcases hok with ⟨hr, hn⟩ | ⟨⟨hr, hwr⟩, hle⟩
  · left
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [inRange_N g]
    have := g.base
    have := g.sp
    have := g.le
    omega
  · right
    obtain ⟨i, hi⟩ : ∃ i, w.r = i + 1 := ⟨w.r - 1, by omega⟩
    rw [hi] at hb hwr hle
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ] at hb
    have hnw : NoWrap b sz := (mem_of_allOf h.arr (List.mem_of_getElem? hb)).2.1
    have hsz : ((F + 8 + A) :: rs.map Prod.snd).getD (i + 1) 0 = sz := by
      simp [List.getD_eq_getElem?_getD, hb]
    exact ⟨i, (b, sz), hwr, hb, by
      rw [Sym.inRange_iff hnw]
      omega⟩

/-- An argument word of the entry, through region `0`. -/
theorem load_arg [Labels] {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64} (j : Nat) :
    (envA m0 m F A rs vals ret).load 0 (F + 8 + j) 8 =
      (NativeRustcVm.wordOf m.dmem (rspOf m0 + 8#64 + BitVec.ofNat 64 j)).toBitVec := by
  rw [load_eq_wordOf]
  show (NativeRustcVm.wordOf m.dmem (stackBelow m0 F + _)).toBitVec = _
  rw [frame_arg]

theorem writeOk_mono {sizes : List Nat} {wr' : Nat → Bool} (hsub : ∀ r, wr' r = true → wr r = true)
    {ws : List Write} (h : ws.all (writeOk F sizes wr') = true) : ws.all (writeOk F sizes wr) = true := by
  rw [List.all_eq_true] at h ⊢
  intro w hw
  have := h w hw
  simp only [writeOk, Bool.or_eq_true, Bool.and_eq_true] at this ⊢
  rcases this with h0 | ⟨⟨h1, h2⟩, h3⟩
  · exact .inl h0
  · exact .inr ⟨⟨h1, hsub _ h2⟩, h3⟩

theorem outsOf_mono {wr' : Nat → Bool} (hsub : ∀ r, wr' r = true → wr r = true) {q : BitVec 64}
    (h : outsOf rs wr' q) : outsOf rs wr q := by
  obtain ⟨i, e, hi, he, hin⟩ := h
  exact ⟨i, e, hsub _ hi, he, hin⟩

theorem BndA.mono [Labels] {wr' : Nat → Bool} (hsub : ∀ r, wr' r = true → wr r = true)
    {T : SState} {vals : Nat → BitVec 64} {m : MachineData} (h : BndA m0 F A N rs wr' T vals m) :
    BndA m0 F A N rs wr T vals m :=
  ⟨h.mt, fun q hq ↦ h.same q fun h' ↦ hq (h'.imp id (outsOf_mono hsub)), h.kept⟩

/-- **Bytes kept** by a change in the stack and the writable arrays `wr'`: `n` bytes at `a`, apart
from the stack and from each writable array. -/
theorem LayA.keep (h : LayA m0 F A N rs) {wr' : Nat → Bool} {d d' : DataMem}
    (hs : SameOutside d d' (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q))
    {a : BitVec 64} {n : Nat} (hnw : NoWrap a n) (hst : Apart a n (stackBelow m0 N) N)
    (hout : ∀ i e, wr' (i + 1) = true → rs[i]? = some e → Apart a n e.1 e.2) :
    ∀ j < n, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j) := by
  intro j hj
  have g := h.geo
  unfold NoWrap at hnw
  have hq : (a + BitVec.ofNat 64 j).toNat = a.toNat + j := toNat_add_ofNat _ _ (by omega)
  refine hs _ fun hin ↦ hin.elim (fun h1 ↦ ?_) fun ⟨i, e, hi, he, h2⟩ ↦ ?_
  · rw [inRange_N g, hq] at h1
    unfold Apart at hst
    rw [g.below] at hst
    have := g.sp
    omega
  · have hap := hout i e hi he
    have hnw' : NoWrap e.1 e.2 := (mem_of_allOf h.arr (List.mem_of_getElem? he)).2.1
    rw [Sym.inRange_iff hnw', hq] at h2
    unfold Apart at hap
    omega

/-- Two arrays of the layout are apart. -/
theorem LayA.apart (h : LayA m0 F A N rs) {i i' : Nat} {e e' : BitVec 64 × Nat} (hne : i ≠ i')
    (he : rs[i]? = some e) (he' : rs[i']? = some e') : Apart e.1 e.2 e'.1 e'.2 := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp he'
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact List.pairwise_iff_getElem.mp h.disj i i' hi hi' hlt
  · have := List.pairwise_iff_getElem.mp h.disj i' i hi' hi hlt
    unfold Apart at this ⊢
    omega

/-- **An array kept** by a change in the stack and the writable arrays `wr'`, not it. -/
theorem LayA.keepArr (h : LayA m0 F A N rs) {wr' : Nat → Bool} {d d' : DataMem}
    (hs : SameOutside d d' (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q))
    {i : Nat} {e : BitVec 64 × Nat} (he : rs[i]? = some e) (hw : wr' (i + 1) = false) :
    ∀ j < e.2, d'.get? (e.1 + BitVec.ofNat 64 j) = d.get? (e.1 + BitVec.ofNat 64 j) := by
  obtain ⟨-, hnw, hap⟩ := mem_of_allOf h.arr (List.mem_of_getElem? he)
  refine h.keep hs hnw (by unfold Apart at hap ⊢; omega) fun i' e' hi' he' ↦
    h.apart (fun hii ↦ ?_) he he'
  subst hii
  rw [hw] at hi'
  cases hi'

/-- **A byte of another region** is not in the array `rs[i]`. -/
theorem LayA.notIn (h : LayA m0 F A N rs) {i : Nat} {e : BitVec 64 × Nat} (he : rs[i]? = some e)
    {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64} {r : Nat} {b : BitVec 64}
    {sz j : Nat} (hb : (envA m0 m F A rs vals ret).regions[r]? = some (b, sz)) (hj : j < sz)
    (hr : r ≠ i + 1) : ¬InRange e.1 e.2 (b + BitVec.ofNat 64 j) := by
  have hnw : NoWrap e.1 e.2 := (mem_of_allOf h.arr (List.mem_of_getElem? he)).2.1
  rw [Sym.inRange_iff hnw]
  cases r with
  | zero =>
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hap := h.frame_apart (List.mem_of_getElem? he)
    rw [h.addr hj]
    have := h.noWrap0
    unfold Apart at hap
    unfold NoWrap at this
    have g := h.geo
    rw [g.base] at hap this
    omega
  | succ r =>
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ] at hb
    have hap := h.apart (i := r) (i' := i) (by omega) hb he
    have hnw' : NoWrap b sz := (mem_of_allOf h.arr (List.mem_of_getElem? hb)).2.1
    unfold NoWrap at hnw'
    rw [toNat_add_ofNat _ _ (by omega)]
    unfold Apart at hap
    simp only at hap
    omega

/-- Writes of a template all outside region `i + 1`: none of its bytes. -/
theorem LayA.notW (h : LayA m0 F A N rs) {i : Nat} {e : BitVec 64 × Nat} (he : rs[i]? = some e)
    {T : SState} (hT : T.mem.all (fun w ↦ w.r != i + 1) = true) :
    ∀ (mc : MachineData) (vals : Nat → BitVec 64) ret r b sz j v t,
      (envA m0 mc F A rs vals ret).regions[r]? = some (b, sz) → j < sz →
      findWrite r j T.mem = some (v, t) → ¬InRange e.1 e.2 (b + BitVec.ofNat 64 j) := by
  intro mc vals ret r b sz j v t hb hj hf
  obtain ⟨w, hwm, hwr, -⟩ := findWrite_spec hf
  have := List.all_eq_true.mp hT w hwm
  rw [hwr, bne_iff_ne] at this
  exact h.notIn he hb hj this

theorem mem_of_lookup {β : Type} {x : Sym} {b : β} :
    ∀ {l : List (Sym × β)}, l.lookup x = some b → (x, b) ∈ l
  | [], h => by cases h
  | (y, c) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hxy
      cases h
      rw [beq_iff_eq.mp hxy]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- A template's aliases, from each of them. -/
theorem aliasesOk_of [Labels] {T : SState} {env : Env}
    (h : ∀ x r o, (x, r, o) ∈ T.aliases → x.eval env = env.base r + BitVec.ofInt 64 o) :
    AliasesOk T env := fun x r o hl ↦ h x r o (mem_of_lookup hl)

/-- **The stack arguments** of the entry, in a state between blocks. -/
theorem LayA.args_same (h : LayA m0 F A N rs) {d : DataMem}
    (hs : SameOutside m0.dmem d (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q))
    (hA : 0 < A) : ∀ j < A, d.get? (rspOf m0 + 8#64 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + 8#64 + BitVec.ofNat 64 j) := by
  have g := h.geo
  have ht := h.top
  have hS := g.sp
  have hb := g.below
  have h8 : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl]
    omega
  refine h.keep hs (by unfold NoWrap; omega) (by unfold Apart; omega) fun i e _ he ↦ ?_
  have hap := (mem_of_allOf h.arr (List.mem_of_getElem? he)).2.2
  unfold Apart at hap ⊢
  omega

/-- **A stack argument loaded** through region `0`, in a state between blocks. -/
theorem LayA.loadArg [Labels] (h : LayA m0 F A N rs) {m : MachineData}
    (hs : SameOutside m0.dmem m.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q))
    {vals : Nat → BitVec 64} {ret : BitVec 64} {i : Nat} (hi : 8 * i + 8 ≤ A) :
    (envA m0 m F A rs vals ret).load 0 (F + 8 + 8 * i) 8 = stackArg m0 i := by
  rw [load_arg]
  unfold stackArg
  rw [show rspOf m0 + BitVec.ofNat 64 (8 + 8 * i) = rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
  rw [NativeRustcVm.addr_add_add]
  exact h.args_same hs (by omega) _ (by omega)

variable [Host]

/-- **The start**: the entry state, with the template's known registers' values. -/
theorem startA {sizes : List Nat} {known : List (Reg64 × Sym)} {al : List (Sym × Nat × Int)}
    {vals : Nat → BitVec 64} (hsz : sizes = (F + 8 + A) :: rs.map Prod.snd)
    (hknown : ∀ ret, AllOf (fun p ↦ m0.regs.get64 p.1 = p.2.eval (envA m0 m0 F A rs vals ret))
      known)
    (hal : ∀ ret, AliasesOk (tpl sizes known [] [] al) (envA m0 m0 F A rs vals ret)) :
    BndA m0 F A N rs wr (tpl sizes known [] [] al) vals m0 :=
  ⟨fun ret ↦ match_tpl (hknown := rfl) rfl rfl (fun r v hv ↦ by
      rw [tpl_reg] at hv
      cases hv
      cases hl : known.lookup r with
      | none => rfl
      | some u =>
        exact lookup_of_allOf (P := fun r v ↦
          m0.regs.get64 r = v.eval (envA m0 m0 F A rs vals ret)) (fun _ _ ↦ Reg64.eq_of_beq)
          (hknown ret) hl)
      rfl (regions_envA hsz) rfl (fun _ _ h ↦ by cases h) (hal ret)
      (fun _ _ _ _ _ _ _ _ h ↦ by cases h),
    fun _ _ ↦ rfl, fun _ h ↦ h⟩

/-- **A block without a call**, to the template `T'` with no known bytes. -/
theorem jumpStepA (h : LayA m0 F A N rs) {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : BndA m0 F A N rs wr T vals m) {ds : List Directive} {k : Nat}
    {x : Exit} (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', x))
    (hx : ∀ l, x ≠ .call l)
    (wr' : Nat → Bool) (hsub : ∀ r, wr' r = true → wr r = true)
    (hwr' : S'.mem.all (writeOk F ((F + 8 + A) :: rs.map Prod.snd) wr') = true)
    {L LW : List (Nat × Sym)} (hL : rlinks false S' T' = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW, p.2.eval (envA m0 m F A rs vals ret) = vals' p.1)
    (hsz : T'.regions = (F + 8 + A) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envA m0 m' F A rs vals' ret))
    (hbd : ∀ (m' : MachineData) ret, ∀ x n, (x, n) ∈ T'.bounds →
      (x.eval (envA m0 m' F A rs vals' ret)).toNat < n)
    {R : MachineState → Prop}
    (cont : ∀ st, PcOk (envA m0 m F A rs vals 0) x (Host.addrOf (k + ds.length)) st →
      BndA m0 F A N rs wr T' vals' st.data → Match (envA m0 m F A rs vals 0) S' st.data →
      SameOutside m.dmem st.data.dmem
        (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q) →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwr := writeOk_mono hsub hwr'
  have hwf := h.wf hB.kept (vals := vals) (ret := 0)
  refine exec_then hk hrun hwf (fun l hl ↦ absurd hl (hx l)) (hB.mt 0) fun st hm hpc ↦
    cont st hpc ⟨fun ret ↦ ?_, ?_, fun p hp ↦ hm.kept hwf p (hB.kept p hp)⟩ hm
      fun q hq ↦ hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr' hW)
  · refine match_tpl (hknown := hknown) rfl rfl (reg_link_jump hL hm (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun p hp ↦ hvals 0 p (List.mem_append_left _ hp))) hfl (regions_envA hsz) hlab
      (hbd st.data ret) (hal st.data ret) ?_
    intro r b sz j v t hb hj hf
    obtain ⟨w, hwm, hwr', h1, h2, hv, ht⟩ := findWrite_spec hf
    obtain ⟨p, hpL, hpw⟩ := wlinks_spec hLW w hwm
    obtain ⟨hwv, hall⟩ := wlink_spec hpw
    have hf' := hall t (by omega)
    rw [hwr', show w.off + t = j by omega] at hf'
    have hb0 : (envA m0 m F A rs vals 0).regions[r]? = some (b, sz) := hb
    rw [hm.mem r b sz hb0 j hj, memByte, hf', ← hv, hwv]
    simp only [Sym.eval]
    exact congrArg (fun x ↦ some (byteOf x t)) (hvals 0 p (List.mem_append_right _ hpL))
  · intro q hq
    rw [hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr hW)]
    exact hB.same q hq

/-- **A block ending in a call**, the callee's contract, to the template `T'` with no known
bytes; RAX and RDX the callee's result `cf` of the registers at the call. -/
theorem callStepA (h : LayA m0 F A N rs) {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : BndA m0 F A N rs wr T vals m) {ds : List Directive} {k : Nat}
    {l : Label} (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', .call l))
    (wr' : Nat → Bool) (hsub : ∀ r, wr' r = true → wr r = true)
    (hwr' : S'.mem.all (writeOk F ((F + 8 + A) :: rs.map Prod.snd) wr') = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0))
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {S : Nat} (hS : F + S ≤ N)
    (hP : ∀ mc, Match (envA m0 m F A rs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc →
      Kept m0.dmem mc.dmem → StackOk mc S → P mc)
    {W : BitVec 64 → Prop}
    (hQ : ∀ mc m', Match (envA m0 m F A rs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc →
      Q mc m' →
      SameOutside mc.dmem m'.dmem (fun q ↦ InRange (stackBelow mc S) S q ∨ W q) ∧ Saved mc m')
    (hWo : ∀ q, W q → outsOf rs wr' q)
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW, p.2.eval (envA m0 m F A rs vals ret) = vals' p.1)
    (hrax : ∀ i, T'.reg .rax = some (.var i) → ∀ mc m' : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envA m0 m F A rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      Q mc m' → reg m' .rax = vals' i)
    (hrdx : ∀ i, T'.reg .rdx = some (.var i) → ∀ mc m' : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envA m0 m F A rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      Q mc m' → reg m' .rdx = vals' i)
    (hWT : ∀ (mc : MachineData) ret r b sz j v t,
      (envA m0 mc F A rs vals' ret).regions[r]? = some (b, sz) → j < sz →
      findWrite r j T'.mem = some (v, t) → ¬W (b + BitVec.ofNat 64 j))
    (hsz : T'.regions = (F + 8 + A) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envA m0 m' F A rs vals' ret))
    (hbd : ∀ (m' : MachineData) ret, ∀ x n, (x, n) ∈ T'.bounds →
      (x.eval (envA m0 m' F A rs vals' ret)).toNat < n)
    {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + ds.length) → BndA m0 F A N rs wr T' vals' st.data →
      (∃ mc, Match (envA m0 m F A rs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc ∧
        SameOutside m.dmem mc.dmem
          (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q) ∧ Q mc st.data) →
      SameOutside m.dmem st.data.dmem
        (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q) →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwr := writeOk_mono hsub hwr'
  have hWo' : ∀ q, W q → outsOf rs wr q := fun q hq ↦ by
    obtain ⟨i, e, hi, he, hin⟩ := hWo q hq
    exact ⟨i, e, hsub _ hi, he, hin⟩
  let ra := (Host.addrOf (k + ds.length)).toBitVec
  have hwf := h.wf hB.kept (vals := vals) (ret := ra)
  refine exec_then hk hrun hwf (fun _ _ ↦ rfl) (hB.mt ra) fun st hm hpc ↦ ?_
  have hkept : Kept m0.dmem st.data.dmem := fun p hp ↦ hm.kept hwf p (hB.kept p hp)
  have hrsp : rspOf st.data = stackBelow m0 F := by
    show st.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    show stackBelow m0 F + BitVec.ofInt 64 0 = _
    simp
  have hsame : SameOutside m0.dmem st.data.dmem
      (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) := fun q hq ↦ by
    rw [hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr hW)]
    exact hB.same q hq
  have hloc : SameOutside m.dmem st.data.dmem
      (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q) := fun q hq ↦
    hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr' hW)
  refine call_then (env := envA m0 m F A rs vals ra) hpc hspec
    (hP st.data hm hkept (h.lay.stackOk hkept hrsp hS))
    fun st' hpc' hrsp2 hqc ↦ cont st' hpc' ⟨fun ret ↦ ?_, ?_,
      fun p hp ↦ (hQ _ _ hm hqc).2.2 p (hkept p hp)⟩ ⟨st.data, hm, hloc, hqc⟩ ?_
  · obtain ⟨hso, hsv⟩ := hQ _ _ hm hqc
    have hR : ∀ r v, S'.reg r = some v → reg st.data r = v.eval (envA m0 m F A rs vals ra) :=
      fun r v hv ↦ hm.regs r v hv
    refine match_tpl (hknown := hknown) rfl rfl ?_ hfl (regions_envA hsz) hlab (hbd st'.data ret)
      (hal st'.data ret) ?_
    · intro r v hv
      obtain ⟨a, ha, haL⟩ := rlinks_spec hL hv
      rcases regLink_spec ha with ⟨-, rfl, rfl, -⟩ | ⟨hnr, hr | ⟨i, rfl, -, hr⟩ |
          ⟨i, s, rfl, hcs, hs, rfl⟩ | ⟨hpl, hcs, hs⟩⟩
      · show reg st'.data .rsp = _
        rw [show reg st'.data .rsp = rspOf st'.data from rfl, hrsp2, hrsp]
        show _ = stackBelow m0 F + BitVec.ofInt 64 8
        rfl
      · subst hr
        rfl
      · rcases hr with rfl | rfl
        · exact hrax i hv st.data st'.data hR hqc
        · exact hrdx i hv st.data st'.data hR hqc
      · have hcs' : calleeSaved r = true := hcs.resolve_left (by decide)
        rw [hsv.1 r hcs', hm.regs r s hs, hvals ra (i, s)
          (List.mem_append_left _ (haL _ List.mem_cons_self))]
        rfl
      · have hcs' : calleeSaved r = true := hcs.resolve_left (by decide)
        rw [hsv.1 r hcs', hm.regs r v hs]
        rcases hpl with ⟨x, o, rfl⟩ | ⟨n, rfl⟩ | ⟨l, rfl⟩ <;> rfl
    · intro r b sz j v t hb hj hf
      obtain ⟨w, hwm, hwr', h1, h2, hv, ht⟩ := findWrite_spec hf
      obtain ⟨p, hpL, hpw⟩ := wlinks_spec hLW w hwm
      obtain ⟨hwv, hall⟩ := wlink_spec hpw
      have hf' := hall t (by omega)
      rw [hwr', show w.off + t = j by omega] at hf'
      have hb0 : (envA m0 m F A rs vals ra).regions[r]? = some (b, sz) := hb
      have hnot : ¬(InRange (stackBelow st.data S) S (b + BitVec.ofNat 64 j) ∨
          W (b + BitVec.ofNat 64 j)) := fun hin ↦ hin.elim
        (fun h1 ↦ h.region_not_stack (vals := vals) (ret := ra) hS hrsp hb0 hj h1)
        (fun h2 ↦ hWT st'.data ret r b sz j v t hb hj hf h2)
      rw [hso _ hnot, hm.mem r b sz hb0 j hj, memByte, hf', ← hv, hwv]
      simp only [Sym.eval]
      exact congrArg (fun x ↦ some (byteOf x t)) (hvals ra p (List.mem_append_right _ hpL))
  · intro q hq
    rw [(hQ _ _ hm hqc).1 q fun hin ↦ hq (hin.elim (fun h' ↦ .inl (h.lay.stack_in hS hrsp h'))
      fun h' ↦ .inr (hWo' q h'))]
    exact hsame q hq
  · intro q hq
    rw [(hQ _ _ hm hqc).1 q fun hin ↦ hq (hin.elim (fun h' ↦ .inl (h.lay.stack_in hS hrsp h'))
      fun h' ↦ .inr (hWo q h'))]
    exact hloc q hq

/-- **The last block**, ending in `ret`: back at the entry's return address, RSP 8 above the
entry's, the callee-saved registers the entry's. -/
theorem exitStepA (h : LayA m0 F A N rs) {T S' : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : BndA m0 F A N rs wr T vals m) {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', .ret (.load 0 F 8)))
    (wr' : Nat → Bool) (hsub : ∀ r, wr' r = true → wr r = true)
    (hwr' : S'.mem.all (writeOk F ((F + 8 + A) :: rs.map Prod.snd) wr') = true)
    (hsp : S'.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int)))
    (hcs : ∀ r, calleeSaved r = true →
      ∃ v, S'.reg r = some v ∧ v.eval (envA m0 m F A rs vals 0) = m0.regs.get64 r)
    {R : MachineState → Prop}
    (cont : ∀ st, Match (envA m0 m F A rs vals 0) S' st.data → st.pc = retOf m0 →
      rspOf st.data = rspOf m0 + 8#64 →
      SameOutside m0.dmem st.data.dmem
        (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) →
      Saved m0 st.data →
      SameOutside m.dmem st.data.dmem
        (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q) →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwr := writeOk_mono hsub hwr'
  have hwf := h.wf hB.kept (vals := vals) (ret := 0)
  have g := h.geo
  refine exec_then hk hrun hwf nofun (hB.mt 0) fun st hm hpc ↦ ?_
  have hsame : SameOutside m0.dmem st.data.dmem
      (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) := fun q hq ↦ by
    rw [hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr hW)]
    exact hB.same q hq
  refine cont st hm ?_ ?_ hsame ⟨fun r hr ↦ ?_, fun p hp ↦ hm.kept hwf p (hB.kept p hp)⟩
    fun q hq ↦ hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr' hW)
  · simp only [PcOk] at hpc
    rw [hpc]
    exact load_ret (m := m) (vars := vals) (ret := 0) g.okF (h.lay.ret_same hB.same)
  · show st.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact frame_rsp F 8
  · obtain ⟨v, hv, he⟩ := hcs r hr
    rw [hm.regs r v hv, he]

/-- **A block ending in a call of `EW::mul`**, to a template with no known bytes. -/
theorem mulStepA (h : LayA m0 F A N rs)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hS : F + ewMulStack ≤ N) {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : BndA m0 F A N rs wr T vals m) {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (wr' : Nat → Bool) (hsub : ∀ r, wr' r = true → wr r = true)
    (hwr : S'.mem.all (writeOk F ((F + 8 + A) :: rs.map Prod.snd) wr') = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0))
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW, p.2.eval (envA m0 m F A rs vals ret) = vals' p.1)
    (hrax : ∀ i, T'.reg .rax = some (.var i) → ∀ mc : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envA m0 m F A rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      (mulRes mc).1 = vals' i)
    (hrdx : ∀ i, T'.reg .rdx = some (.var i) → ∀ mc : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envA m0 m F A rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      (mulRes mc).2 = vals' i)
    (hsz : T'.regions = (F + 8 + A) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envA m0 m' F A rs vals' ret))
    (hbd : T'.bounds = [])
    {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + ds.length) → BndA m0 F A N rs wr T' vals' st.data →
      SameOutside m.dmem st.data.dmem
        (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr' q) →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ :=
  callStepA (hknown := hknown) h hB hk hrun wr' hsub hwr hsp hmul hS
    (fun _ _ _ h ↦ h) (W := fun _ ↦ False)
    (fun _ _ _ hq ↦ ⟨fun p hp ↦ hq.2.2.1 p fun h ↦ hp (.inl h), hq.2.2.2⟩) (fun _ h ↦ h.elim)
    hL hLW hvals (fun i hi mc m' hR hq ↦ hq.1.trans (hrax i hi mc hR))
    (fun i hi mc m' hR hq ↦ hq.2.1.trans (hrdx i hi mc hR))
    (fun _ _ _ _ _ _ _ _ _ _ _ h ↦ h) hsz hfl hlab hal
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx) fun st hpc hB' _ hso ↦ cont st hpc hB' hso

end

end NativeRustcVmX64.Whir.Rows
