module

public import NativeRustcVmX64.Ring.Seq

/-!
# Blocks and calls of a function with stack arguments (x86-64)

`NativeRustcVmX64.Ring.Seq` with region `0` reaching past the return address: the `Z` bytes from
`F` below the entry's RSP (the frame, the return address and the stack arguments above it,
`envZ`). A function's proof runs block after block, each from a literal template `T` (`BndZ`:
`Match` for every return address, memory the entry's but in the stack and the writable arrays);
the blocks write only the frame's first `F` bytes (`writeOk F`), so the return address and the
stack arguments stay the entry's.

- `startZ`: the entry state.
- `jumpZ`: a block without a call, run from a state `S` the machine matches.
- `callZ`: a block ending in a call at RSP the frame's offset `oc`, then the callee's contract;
  the callee's outputs `W` may depend on the state at the call.
  Both wrappers require the destination template's known-byte list to be empty.
- `exitZ`: the last block, ending in `ret`.
-/

namespace NativeRustcVmX64.KeccakGkr.SeqZ

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Ring

@[expose] public section

/-- The environment of `m`: region `0` the `Z` bytes from `F` below the entry's RSP, then the
arrays `rs`. -/
abbrev envZ (m0 m : MachineData) (F Z : Nat) (rs : List (BitVec 64 × Nat))
    (vals : Nat → BitVec 64) (ret : BitVec 64) : Env :=
  Env.ofMachine m ((stackBelow m0 F, Z) :: rs) vals ret

/-- The layout: `N` bytes of stack below the entry's RSP, the frame its top `F`, region `0` its
`Z` bytes from the frame's base mapped (the return address and the stack arguments past `F`), the
arrays mapped, not wrapping, apart from the stack and region `0` and from each other. -/
structure LayZ (m0 : MachineData) (F Z N : Nat) (rs : List (BitVec 64 × Nat)) : Prop where
  ok : StackOk m0 N
  le : F ≤ N
  f8 : 8 ≤ F
  fz : F + 8 ≤ Z
  map : Mapped m0.dmem (stackBelow m0 F) Z
  nw : NoWrap (stackBelow m0 F) Z
  arr : AllOf (fun e : BitVec 64 × Nat ↦
    Mapped m0.dmem e.1 e.2 ∧ NoWrap e.1 e.2 ∧ Apart e.1 e.2 (stackBelow m0 N) (N - F + Z)) rs
  disj : rs.Pairwise fun e e' ↦ Apart e.1 e.2 e'.1 e'.2

/-- **Between blocks**: the template describes the machine state, whose memory is the entry's but
in the stack and the writable arrays. -/
structure BndZ [Labels] (m0 : MachineData) (F Z N : Nat) (rs : List (BitVec 64 × Nat))
    (wr : Nat → Bool) (T : SState) (vals : Nat → BitVec 64) (m : MachineData) : Prop where
  mt : ∀ ret, Match (envZ m0 m F Z rs vals ret) T m
  same : SameOutside m0.dmem m.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q)
  kept : Kept m0.dmem m.dmem

/-- The registers but RSP. -/
def noRsp : List Reg64 := allRegs.filter (· != .rsp)

end

public section

theorem mem_noRsp {r : Reg64} (h : r ≠ .rsp) : r ∈ noRsp :=
  List.mem_filter.mpr ⟨mem_allRegs r, by cases r <;> first | exact absurd rfl h | rfl⟩

/-- The frame's base plus `oc` is the base of a frame `oc` bytes smaller. -/
theorem stackBelow_add {m : MachineData} {F oc : Nat} (h : oc ≤ F) :
    stackBelow m F + BitVec.ofInt 64 (oc : Int) = stackBelow m (F - oc) := by
  rw [BitVec.ofInt_natCast]
  unfold stackBelow
  bv_omega

variable {m0 : MachineData} {F Z N : Nat} {rs : List (BitVec 64 × Nat)} {wr : Nat → Bool}

theorem LayZ.geo (h : LayZ m0 F Z N rs) : Geo m0 F N := ⟨h.ok, h.le, h.f8⟩

theorem LayZ.base (h : LayZ m0 F Z N rs) : (stackBelow m0 F).toNat = (rspOf m0).toNat - F :=
  h.geo.base

/-- An address of region `0` as a number. -/
theorem LayZ.addr (h : LayZ m0 F Z N rs) {j : Nat} (hj : j < Z) :
    (stackBelow m0 F + BitVec.ofNat 64 j).toNat = (rspOf m0).toNat - F + j := by
  have := h.nw
  unfold NoWrap at this
  rw [toNat_add_ofNat _ _ (by omega), h.base]

theorem regions_envZ {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64} {T : SState}
    (hT : T.regions = Z :: rs.map Prod.snd) :
    ∀ (r n : Nat), T.regions[r]? = some n →
      ∃ b, (envZ m0 m F Z rs vals ret).regions[r]? = some (b, n) := by
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

theorem LayZ.frame_apart (h : LayZ m0 F Z N rs) {e : BitVec 64 × Nat} (he : e ∈ rs) :
    Apart (stackBelow m0 F) Z e.1 e.2 := by
  have ha := (mem_of_allOf h.arr he).2.2
  have g := h.geo
  have hb := g.base
  have hN := g.below
  have := g.sp
  have := g.le
  unfold Apart at ha ⊢
  omega

theorem LayZ.wf (h : LayZ m0 F Z N rs) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {vals : Nat → BitVec 64} {ret : BitVec 64} : (envZ m0 m F Z rs vals ret).WF := by
  refine Env.wf_of ⟨⟨fun i hi ↦ hk _ (h.map i hi), h.nw⟩, ?_⟩ ?_
  · show AllOf _ rs
    have harr := h.arr
    clear h
    induction rs with
    | nil => trivial
    | cons e rs ih =>
      exact ⟨⟨fun i hi ↦ hk _ (harr.1.1 i hi), harr.1.2.1⟩, ih harr.2⟩
  · show List.Pairwise _ ((stackBelow m0 F, Z) :: rs)
    exact List.Pairwise.cons (fun e he ↦ h.frame_apart he) h.disj

/-- A read-only source region, including separation from incoming stack arguments. -/
theorem LayZ.withGot [Labels] (h : LayZ m0 F Z N rs) {l : Label}
    (hg : GotAt m0 N rs [l])
    (hspan : Apart (gotAddr l) 8 (stackBelow m0 N) (N - F + Z)) :
    LayZ m0 F Z N (rs ++ [(gotAddr l, 8)]) := by
  refine ⟨h.ok, h.le, h.f8, h.fz, h.map, h.nw, ?_, ?_⟩
  · have hall : ∀ a ∈ rs ++ [(gotAddr l, 8)],
        Mapped m0.dmem a.1 a.2 ∧ NoWrap a.1 a.2 ∧
          Apart a.1 a.2 (stackBelow m0 N) (N - F + Z) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact mem_of_allOf h.arr ha
      · simp only [List.mem_singleton] at ha
        subst a
        exact ⟨hg.mapped (by simp), (hg.1 l (by simp)).2.1, hspan⟩
    generalize rs ++ [(gotAddr l, 8)] = xs at hall ⊢
    induction xs with
    | nil => trivial
    | cons a xs ih =>
      exact ⟨hall a (by simp), ih (fun b hb ↦ hall b (by simp [hb]))⟩
  · rw [List.pairwise_append]
    refine ⟨h.disj, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact ((hg.1 l (by simp)).2.2.2 a ha).symm

/-- The layout of the frame below RSP at the frame's offset `oc` (a callee's view). -/
theorem LayZ.lay (h : LayZ m0 F Z N rs) {oc : Nat} (hoc : oc + 8 ≤ F) : Lay m0 (F - oc) N rs := by
  refine ⟨h.ok, by have := h.le; omega, by omega, ?_, h.disj⟩
  have harr := h.arr
  have hfz := h.fz
  have hle := h.le
  clear h
  induction rs with
  | nil => trivial
  | cons e rs ih =>
    refine ⟨⟨harr.1.1, harr.1.2.1, ?_⟩, ih harr.2⟩
    have := harr.1.2.2
    unfold Apart at this ⊢
    omega

/-- A block's writes are in the stack or the writable arrays. -/
theorem LayZ.written (h : LayZ m0 F Z N rs) {m : MachineData} {vals : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState}
    (hw : S.mem.all (writeOk F (Z :: rs.map Prod.snd) wr) = true) {q : BitVec 64}
    (hq : Written (envZ m0 m F Z rs vals ret) S q) :
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
    have hsz : (Z :: rs.map Prod.snd).getD (i + 1) 0 = sz := by
      simp [List.getD_eq_getElem?_getD, hb]
    exact ⟨i, (b, sz), hwr, hb, by
      rw [NativeRustcX64.Sym.inRange_iff hnw]
      omega⟩

/-- Region `0` from the frame's offset `oc` is not in the stack below RSP there. -/
theorem LayZ.not_callee (h : LayZ m0 F Z N rs) {oc S : Nat} (hoc : oc + 8 ≤ F) (hS : F - oc + S ≤ N)
    {mc : MachineData} (hrsp : rspOf mc = stackBelow m0 (F - oc)) {j : Nat} (hj : oc ≤ j)
    (hjZ : j < Z) : ¬InRange (stackBelow mc S) S (stackBelow m0 F + BitVec.ofNat 64 j) := by
  intro hp
  have g := h.geo
  have hs := g.sp
  have hbase := g.base
  have := g.le
  have hb' : (stackBelow m0 (F - oc)).toNat = (rspOf m0).toNat - (F - oc) :=
    stackBelow_toNat' (by omega)
  have hmb : (stackBelow mc S).toNat = (rspOf m0).toNat - (F - oc) - S := by
    rw [stackBelow_toNat' (by rw [hrsp, hb']; omega), hrsp, hb']
  rw [NativeRustcX64.Sym.inRange_iff (by rw [hmb]; have := g.top; omega), hmb, h.addr hjZ] at hp
  omega

/-- **A template with more facts**: aliases, bounds that hold. -/
theorem match_with [Labels] {env : Env} {T : SState} {m : MachineData} (hm : Match env T m)
    {bd : List (Sym × Nat)} {al : List (Sym × Nat × Int)}
    (hbd : ∀ x n, (x, n) ∈ bd → (x.eval env).toNat < n)
    (hal : ∀ x r o, al.lookup x = some (r, o) → x.eval env = env.base r + BitVec.ofInt 64 o) :
    Match env { T with bounds := bd, aliases := al } m :=
  { hm with bounds := hbd, aliases := hal }

theorem BndZ.weaken [Labels] {T : SState} {vals : Nat → BitVec 64} {m : MachineData}
    (hB : BndZ m0 F Z N rs wr T vals m) {wr' : Nat → Bool} (hw : ∀ i, wr i = true → wr' i = true) :
    BndZ m0 F Z N rs wr' T vals m :=
  ⟨hB.mt, fun q hq ↦ hB.same q fun h ↦ hq (h.imp id fun ⟨i, e, h1, h2, h3⟩ ↦ ⟨i, e, hw _ h1, h2, h3⟩),
    hB.kept⟩

variable [Host]

/-- **The start**: the entry state, with the template's known registers' values. -/
theorem startZ {sizes : List Nat} {known : List (Reg64 × Sym)} {vals : Nat → BitVec 64}
    (hsz : sizes = Z :: rs.map Prod.snd)
    (hknown : ∀ ret, AllOf (fun p ↦ m0.regs.get64 p.1 = p.2.eval (envZ m0 m0 F Z rs vals ret))
      known) :
    BndZ m0 F Z N rs wr (tpl sizes known []) vals m0 :=
  ⟨fun ret ↦ match_tpl rfl rfl (fun r v hv ↦ by
      rw [tpl_reg] at hv
      cases hv
      cases hl : known.lookup r with
      | none => rfl
      | some u =>
        exact lookup_of_allOf (P := fun r v ↦
          m0.regs.get64 r = v.eval (envZ m0 m0 F Z rs vals ret)) (fun _ _ ↦ Reg64.eq_of_beq)
          (hknown ret) hl)
      rfl (regions_envZ hsz) rfl (fun _ _ h ↦ by cases h) (fun _ _ _ h ↦ by cases h)
      (fun _ _ _ _ _ _ _ _ h ↦ by cases h),
    fun _ _ ↦ rfl, fun _ h ↦ h⟩

/-- **A block without a call**, from a state `S` the machine matches, to the template `T'`. -/
theorem jumpZ (h : LayZ m0 F Z N rs) {T S T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : BndZ m0 F Z N rs wr T vals m) {ds : List Directive} {k : Nat}
    {x : Exit} (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds S = some (S', x))
    (hm : Match (envZ m0 m F Z rs vals 0) S m) (hx : ∀ l, x ≠ .call l)
    (hwr : S'.mem.all (writeOk F (Z :: rs.map Prod.snd) wr) = true)
    {L LW : List (Nat × Sym)} (hL : rlinks false S' T' = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ p ∈ L ++ LW, p.2.eval (envZ m0 m F Z rs vals 0) = vals' p.1)
    (hok : tplOk T' = true)
    (hsz : T'.regions = Z :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envZ m0 m' F Z rs vals' ret))
    (hbd : ∀ (m' : MachineData) ret, ∀ x n, (x, n) ∈ T'.bounds →
      (x.eval (envZ m0 m' F Z rs vals' ret)).toNat < n)
    {R : MachineState → Prop}
    (cont : ∀ st, PcOk (envZ m0 m F Z rs vals 0) x (Host.addrOf (k + ds.length)) st →
      BndZ m0 F Z N rs wr T' vals' st.data → Match (envZ m0 m F Z rs vals 0) S' st.data →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwf := h.wf hB.kept (vals := vals) (ret := 0)
  refine exec_then hk hrun hwf (fun l hl ↦ absurd hl (hx l)) hm fun st hm' hpc ↦
    cont st hpc ⟨fun ret ↦ match_links (hknown := hknown) hm' hok hL hLW (fun _ ↦ rfl) rfl rfl rfl hvals hfl
      (regions_envZ hsz) hlab (hbd st.data ret) (hal st.data ret), ?_,
      fun p hp ↦ hm'.kept hwf p (hB.kept p hp)⟩ hm'
  intro q hq
  rw [hm'.get?_mem0 hwf fun hW ↦ hq (h.written hwr hW)]
  exact hB.same q hq

/-- **A block ending in a call, and the call** at RSP the frame's offset `oc` (the body's at
`oc + 8` after it), from a state `S` the machine matches; the callee's outputs `W mc` (of the
state `mc` at the call) in the stack or the writable arrays, not in the template's writes. The
continuation also gets the state at the call, the callee's postcondition and the block's changes. -/
theorem callZ (h : LayZ m0 F Z N rs) {T S T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : BndZ m0 F Z N rs wr T vals m) {ds : List Directive} {k : Nat}
    {srcRs : List (BitVec 64 × Nat)}
    {l : Label} (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds S = some (S', .call l))
    (hm : Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S m)
    {oc : Nat} (hoc : oc + 8 ≤ F) (hsp : S'.reg .rsp = some (.ptr 0 (oc : Int)))
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {Sk : Nat} (hS : F - oc + Sk ≤ N)
    (hP : ∀ mc, Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc →
      Kept m0.dmem mc.dmem → StackOk mc Sk →
      SameOutside m0.dmem mc.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) →
      rspOf mc = stackBelow m0 (F - oc) → P mc)
    {W : MachineData → BitVec 64 → Prop}
    (hQ : ∀ mc m', Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc →
      Q mc m' →
      SameOutside mc.dmem m'.dmem (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ W mc q) ∧
        Saved mc m')
    (hWo : ∀ mc, Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc →
      ∀ q, W mc q → InRange (stackBelow m0 N) N q ∨ outsOf rs wr q)
    (hok : tplOk T' = true) (hrspT : T'.reg .rsp = some (.ptr 0 ((oc + 8 : Nat) : Int)))
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' T' noRsp = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ p ∈ L ++ LW,
      p.2.eval (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) = vals' p.1)
    (hrax : ∀ i, T'.reg .rax = some (.var i) → ∀ mc m' : MachineData,
      Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc → Q mc m' →
      reg m' .rax = vals' i)
    (hrdx : ∀ i, T'.reg .rdx = some (.var i) → ∀ mc m' : MachineData,
      Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc → Q mc m' →
      reg m' .rdx = vals' i)
    (hWT : ∀ mc, Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc →
      ∀ j v t, j < Z → findWrite 0 j T'.mem = some (v, t) →
        oc ≤ j ∧ ¬W mc (stackBelow m0 F + BitVec.ofNat 64 j))
    (hsz : T'.regions = Z :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envZ m0 m' F Z rs vals' ret))
    (hbd : ∀ (m' : MachineData) ret, ∀ x n, (x, n) ∈ T'.bounds →
      (x.eval (envZ m0 m' F Z rs vals' ret)).toNat < n)
    {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + ds.length) → BndZ m0 F Z N rs wr T' vals' st.data →
      (∃ mc, Match (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc ∧
        rspOf mc = stackBelow m0 (F - oc) ∧ Q mc st.data ∧
        SameOutside m.dmem mc.dmem
          (Written (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec) S')) →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl)
    (hwfS : (envZ m0 m F Z srcRs vals (Host.addrOf (k + ds.length)).toBitVec).WF := by
      exact h.wf hB.kept)
    (hwrites : ∀ {q}, Written (envZ m0 m F Z srcRs vals
        (Host.addrOf (k + ds.length)).toBitVec) S' q →
      InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  let ra := (Host.addrOf (k + ds.length)).toBitVec
  have h' : Lay m0 (F - oc) N rs := h.lay hoc
  have hwf := hwfS
  refine exec_then hk hrun hwf (fun _ _ ↦ rfl) hm fun st hm' hpc ↦ ?_
  have hkept : Kept m0.dmem st.data.dmem := fun p hp ↦ hm'.kept hwf p (hB.kept p hp)
  have hrsp : rspOf st.data = stackBelow m0 (F - oc) := by
    show st.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact stackBelow_add (by omega)
  have hsame : SameOutside m0.dmem st.data.dmem
      (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) := fun q hq ↦ by
    rw [hm'.get?_mem0 hwf fun hW ↦ hq (hwrites hW)]
    exact hB.same q hq
  simp only [tplOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hokr, hokw⟩ := hok
  refine call_then (env := envZ m0 m F Z srcRs vals ra) hpc hspec
    (hP st.data hm' hkept (h'.stackOk hkept hrsp hS) hsame hrsp) fun st' hpc' hrsp2 hqc ↦
      cont st' hpc' ⟨fun ret ↦ ?_, ?_, fun p hp ↦ (hQ _ _ hm' hqc).2.2 p (hkept p hp)⟩
        ⟨st.data, hm', hrsp, hqc, fun q hq ↦ hm'.get?_mem0 hwf hq⟩
  · obtain ⟨hso, hsv⟩ := hQ _ _ hm' hqc
    have hR : ∀ r v, S'.reg r = some v → reg st.data r = v.eval (envZ m0 m F Z srcRs vals ra) :=
      fun r v hv ↦ hm'.regs r v hv
    refine match_tpl (hknown := hknown) rfl rfl ?_ hfl (regions_envZ hsz) hlab (hbd st'.data ret)
      (hal st'.data ret) ?_
    · intro r v hv
      by_cases hr : r = .rsp
      · subst hr
        rw [hrspT] at hv
        cases hv
        show rspOf st'.data = _
        rw [hrsp2, hrsp]
        show _ = stackBelow m0 F + BitVec.ofInt 64 ((oc + 8 : Nat) : Int)
        rw [← stackBelow_add (by omega), BitVec.ofInt_natCast, BitVec.ofInt_natCast,
          BitVec.add_assoc, BitVec.ofNat_add]
      obtain ⟨a, ha, haL⟩ := rlinksOf_spec hL r (mem_noRsp hr) v hv
      have hk' := hokr r (mem_allRegs r)
      rw [hv] at hk'
      rcases regLink_spec ha with ⟨-, hr', -, -⟩ | ⟨hnr, hr' | ⟨i, rfl, -, hr'⟩ |
          ⟨i, s, rfl, hcs, hs, rfl⟩ | ⟨hpl, hcs, hs⟩⟩
      · exact absurd hr' hr
      · subst hr'
        rfl
      · rcases hr' with rfl | rfl
        · exact hrax i hv st.data st'.data hm' hqc
        · exact hrdx i hv st.data st'.data hm' hqc
      · have hcs' : calleeSaved r = true := hcs.resolve_left (by decide)
        rw [hsv.1 r hcs', hm'.regs r s hs, hvals (i, s)
          (List.mem_append_left _ (haL _ List.mem_cons_self))]
        rfl
      · have hcs' : calleeSaved r = true := hcs.resolve_left (by decide)
        rw [hsv.1 r hcs', hm'.regs r v hs]
        rcases hpl with ⟨x, o, rfl⟩ | ⟨n, rfl⟩ | ⟨l, rfl⟩
        · cases x with
          | zero => rfl
          | succ x => simp at hk'
        · rfl
        · rfl
    · intro r b sz j v t hb hj hf
      obtain ⟨w, hwm, hwr', h1, h2, hv, ht⟩ := findWrite_spec hf
      obtain ⟨p, hpL, hpw⟩ := wlinks_spec hLW w hwm
      obtain ⟨hwv, hall⟩ := wlink_spec hpw
      have hw0 := hokw w hwm
      simp only [beq_iff_eq] at hw0
      have hr0 : r = 0 := hwr' ▸ hw0.1
      subst hr0
      have hb' : b = stackBelow m0 F ∧ Z = sz := by
        simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hb
        exact ⟨hb.1.symm, hb.2⟩
      obtain ⟨rfl, rfl⟩ := hb'
      have hf' := hall t (by omega)
      rw [hwr', show w.off + t = j by omega] at hf'
      have hb0 : (envZ m0 m F Z srcRs vals ra).regions[0]? = some (stackBelow m0 F, Z) := rfl
      obtain ⟨hjo, hjW⟩ := hWT st.data hm' j v t hj hf
      have hnot : ¬(InRange (stackBelow st.data Sk) Sk (stackBelow m0 F + BitVec.ofNat 64 j) ∨
          W st.data (stackBelow m0 F + BitVec.ofNat 64 j)) := fun hin ↦ hin.elim
        (fun h1 ↦ h.not_callee hoc hS hrsp hjo hj h1) (fun h2 ↦ hjW h2)
      rw [hso _ hnot, hm'.mem 0 _ _ hb0 j hj, memByte, hf', ← hv, hwv]
      simp only [Sym.eval]
      exact congrArg (fun x ↦ some (byteOf x t)) (hvals p (List.mem_append_right _ hpL))
  · intro q hq
    rw [(hQ _ _ hm' hqc).1 q fun hin ↦ hq (hin.elim (fun h'' ↦ .inl (h'.stack_in hS hrsp h''))
      fun h'' ↦ hWo st.data hm' q h'')]
    exact hsame q hq

/-- **The last block**, ending in `ret`: back at the entry's return address, RSP 8 above the
entry's, the callee-saved registers the entry's. -/
theorem exitZ (h : LayZ m0 F Z N rs) {T S S' : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : BndZ m0 F Z N rs wr T vals m) {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds S = some (S', .ret (.load 0 F 8)))
    (hm : Match (envZ m0 m F Z rs vals 0) S m)
    (hwr : S'.mem.all (writeOk F (Z :: rs.map Prod.snd) wr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int)))
    (hcs : ∀ r, calleeSaved r = true →
      ∃ v, S'.reg r = some v ∧ v.eval (envZ m0 m F Z rs vals 0) = m0.regs.get64 r)
    {R : MachineState → Prop}
    (cont : ∀ st, Match (envZ m0 m F Z rs vals 0) S' st.data → st.pc = retOf m0 →
      rspOf st.data = rspOf m0 + 8#64 →
      SameOutside m0.dmem st.data.dmem
        (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) →
      Saved m0 st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwf := h.wf hB.kept (vals := vals) (ret := 0)
  have g := h.geo
  refine exec_then hk hrun hwf nofun hm fun st hm' hpc ↦ ?_
  have hsame : SameOutside m0.dmem st.data.dmem
      (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) := fun q hq ↦ by
    rw [hm'.get?_mem0 hwf fun hW ↦ hq (h.written hwr hW)]
    exact hB.same q hq
  refine cont st hm' ?_ ?_ hsame ⟨fun r hr ↦ ?_, fun p hp ↦ hm'.kept hwf p (hB.kept p hp)⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    have e : (Sym.load 0 F 8).eval (envZ m0 m F Z rs vals 0) =
        (frameEnv m0 m F vals 0).load 0 F 8 := rfl
    rw [e]
    exact load_ret g.okF ((h.lay (oc := 0) (by have := h.f8; omega)).ret_same hB.same)
  · show st.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact frame_rsp F 8
  · obtain ⟨v, hv, he⟩ := hcs r hr
    rw [hm'.regs r v hv, he]

end

end NativeRustcVmX64.KeccakGkr.SeqZ
