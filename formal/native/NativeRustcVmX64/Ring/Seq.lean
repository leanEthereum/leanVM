module

public import NativeRustcVmX64.Field.Call
public import NativeRustcVmX64.Got
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names

/-!
# Functions as sequences of blocks and calls (x86-64)

A function keeps its frame in the `F` bytes below the entry `m0`'s RSP (its call slot at offset
`0`, its spills and its pushes above), uses `N` bytes of stack with its callees', and reads or
writes arrays `rs` apart from that stack (`Lay`). Its proof runs block after block, each from a
literal symbolic state, a *template* `T`, in the environment `envS` of the machine state where the
block starts: region `0` the frame and the return address, region `i + 1` the array `rs[i]`, and
variables `vals` naming the values the template holds (a register or a spill `.var i`). Between
blocks the machine state is what the template says (`Bnd`): `Match` for every return address, and
memory changed only in the stack and the writable arrays (`outsOf`).

- `callStep`: a block ending in a call, then the callee's contract: the next template `T'` takes
  its registers and words from the block's result (`rlinks`, `wlinks`: which symbolic value each
  of `T'`'s variables is), RAX and RDX from the callee's result (`cf`).
- `jumpStep`: a block ending in a fall-through or a branch.
- `exitStep`: the last block, ending in `ret`: back at the entry's return address with the
  callee-saved registers restored.
- `match_tpl`, `start`: a template's `Match` from its registers' and writes' values.
-/

namespace NativeRustcVmX64.Ring

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field

@[expose] public section

/-- The environment of `m`: region `0` the `F` bytes below the entry `m0`'s RSP and its return
address, then the arrays `rs`. -/
abbrev envS (m0 m : MachineData) (F : Nat) (rs : List (BitVec 64 × Nat))
    (vals : Nat → BitVec 64) (ret : BitVec 64) : Env :=
  Env.ofMachine m ((stackBelow m0 F, F + 8) :: rs) vals ret

/-- The layout: `N` bytes of stack below the entry's RSP, the frame its top `F` (at least its call
slot), the arrays mapped, not wrapping, apart from the stack and the return address and from each
other. -/
structure Lay (m0 : MachineData) (F N : Nat) (rs : List (BitVec 64 × Nat)) : Prop where
  ok : StackOk m0 N
  le : F ≤ N
  f8 : 8 ≤ F
  arr : AllOf (fun e : BitVec 64 × Nat ↦
    Mapped m0.dmem e.1 e.2 ∧ NoWrap e.1 e.2 ∧ Apart e.1 e.2 (stackBelow m0 N) (N + 8)) rs
  disj : rs.Pairwise fun e e' ↦ Apart e.1 e.2 e'.1 e'.2

/-- The bytes of the writable arrays (`wr` of their region's index, `i + 1` for `rs[i]`). -/
def outsOf (rs : List (BitVec 64 × Nat)) (wr : Nat → Bool) (q : BitVec 64) : Prop :=
  ∃ i e, wr (i + 1) = true ∧ rs[i]? = some e ∧ InRange e.1 e.2 q

/-- **Between blocks**: the template describes the machine state, whose memory is the entry's but
in the stack and the writable arrays. -/
structure Bnd [Labels] (m0 : MachineData) (F N : Nat) (rs : List (BitVec 64 × Nat)) (wr : Nat → Bool)
    (T : SState) (vals : Nat → BitVec 64) (m : MachineData) : Prop where
  mt : ∀ ret, Match (envS m0 m F rs vals ret) T m
  same : SameOutside m0.dmem m.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q)
  kept : Kept m0.dmem m.dmem

/-- A template: the regions' sizes, the known registers, the writes. -/
def tpl (sizes : List Nat) (known : List (Reg64 × Sym)) (ws : List Write)
    (bounds : List (Sym × Nat) := []) (aliases : List (Sym × Nat × Int) := []) : SState :=
  { init sizes known [] bounds aliases with mem := ws }

/-- The template's aliases hold in the environment. -/
def AliasesOk [Labels] (T : SState) (env : Env) : Prop :=
  ∀ x r o, T.aliases.lookup x = some (r, o) → x.eval env = env.base r + BitVec.ofInt 64 o

/-- A block's write is in the frame below the return address or in a writable array (`sizes` the
regions' sizes). -/
def writeOk (F : Nat) (sizes : List Nat) (wr : Nat → Bool) (w : Write) : Bool :=
  (w.r == 0 && decide (w.off + w.n ≤ F)) ||
    (w.r != 0 && wr w.r && decide (w.off + w.n ≤ sizes.getD w.r 0))

/-- What the template's register `r` holding `v` asks of the block's result `S'` (in a call step,
`call`): an atom `r` nothing; RAX and RDX in a call step the callee's result; a variable the
block's value (a callee-saved register's, in a call step); a pointer or a literal the same; RSP in
a call step the frame's offset `8`, from `0` at the call. -/
def regLink (call : Bool) (S' : SState) (r : Reg64) (v : Sym) : Option (List (Nat × Sym)) :=
  if call = true ∧ r = .rsp then
    if v = .ptr 0 8 ∧ S'.reg .rsp = some (.ptr 0 0) then some [] else none
  else
    match v with
    | .reg r' => if r' = r then some [] else none
    | .var i =>
      if call = true ∧ (r = .rax ∨ r = .rdx) then some []
      else if call = false ∨ calleeSaved r = true then (S'.reg r).map fun s ↦ [(i, s)] else none
    | .ptr _ _ | .lit _ | .label _ =>
      if (call = false ∨ calleeSaved r = true) ∧ S'.reg r = some v then some [] else none
    | _ => none

/-- The variables the template's registers take from the block's result. -/
def rlinksOf (call : Bool) (S' T' : SState) : List Reg64 → Option (List (Nat × Sym))
  | [] => some []
  | r :: rs =>
    match T'.reg r with
    | none => rlinksOf call S' T' rs
    | some v =>
      match regLink call S' r v, rlinksOf call S' T' rs with
      | some a, some b => some (a ++ b)
      | _, _ => none

/-- The variables the template's registers take from the block's result. -/
def rlinks (call : Bool) (S' T' : SState) : Option (List (Nat × Sym)) :=
  rlinksOf call S' T' allRegs

/-- The variable a template's write takes from the block's result: the symbolic value whose bytes
the block leaves there. -/
def wlink (S' : SState) (w : Write) : Option (Nat × Sym) :=
  match w.v, findWrite w.r w.off S'.mem with
  | .var i, some (s, 0) =>
    if (List.range w.n).all fun t ↦ findWrite w.r (w.off + t) S'.mem == some (s, t) then
      some (i, s)
    else none
  | _, _ => none

/-- The variables the template's writes take from the block's result. -/
def wlinks (S' : SState) : List Write → Option (List (Nat × Sym))
  | [] => some []
  | w :: ws =>
    match wlink S' w, wlinks S' ws with
    | some a, some b => some (a :: b)
    | _, _ => none

/-- A template whose registers are atoms, variables or region-0 pointers or literals, whose writes
are in region 0 and variables, so that its meaning does not depend on the other regions. -/
def tplOk (T : SState) : Bool :=
  allRegs.all (fun r ↦ match T.reg r with
    | some (.reg r') => r' == r
    | some (.var _) => true
    | some (.ptr 0 _) => true
    | some (.lit _) | some (.label _) => true
    | _ => false) &&
  T.mem.all fun w ↦ w.r == 0 && match w.v with
    | .var _ => true
    | _ => false

/-- The template's flags: their atoms. -/
def atomFlags : SFlags := ⟨some .flagCF, some .flagZF, some .flagSF, some .flagOF⟩

/-- `EW::sq_iter`'s result of the registers at its call. -/
def sqRes (mc : MachineData) : BitVec 64 × BitVec 64 :=
  let e := NativeVm.Model.EW.sqIter (reg mc .rdi).toNat ⟨.ofBitVec (reg mc .rsi), .ofBitVec (reg mc .rdx)⟩
  (e.c0.toBitVec, e.c1.toBitVec)

/-- `EW::mul`'s result of the registers at its call. -/
def mulRes (mc : MachineData) : BitVec 64 × BitVec 64 :=
  let e := NativeVm.Model.EW.mul ⟨.ofBitVec (reg mc .rdi), .ofBitVec (reg mc .rsi)⟩
    ⟨.ofBitVec (reg mc .rdx), .ofBitVec (reg mc .rcx)⟩
  (e.c0.toBitVec, e.c1.toBitVec)

end

public section

/-! ## Lists -/

theorem findWrite_spec {r j : Nat} {v : Sym} {t : Nat} :
    ∀ {ws : List Write}, findWrite r j ws = some (v, t) →
      ∃ w ∈ ws, w.r = r ∧ w.off ≤ j ∧ j < w.off + w.n ∧ w.v = v ∧ t = j - w.off
  | [], h => by cases h
  | w :: ws, h => by
    rw [findWrite_cons] at h
    by_cases hw : w.r = r ∧ w.off ≤ j ∧ j < w.off + w.n
    · rw [ite_pos hw] at h
      cases h
      exact ⟨w, List.mem_cons_self, hw.1, hw.2.1, hw.2.2, rfl, rfl⟩
    · rw [ite_neg hw] at h
      obtain ⟨w', hw', h'⟩ := findWrite_spec h
      exact ⟨w', List.mem_cons_of_mem _ hw', h'⟩

theorem rlinksOf_spec {call : Bool} {S' T' : SState} :
    ∀ {l : List Reg64} {L : List (Nat × Sym)}, rlinksOf call S' T' l = some L →
      ∀ r ∈ l, ∀ v, T'.reg r = some v → ∃ a, regLink call S' r v = some a ∧ ∀ p ∈ a, p ∈ L
  | [], _, _, _, hr, _, _ => by cases hr
  | r' :: l, L, h, r, hr, v, hv => by
    simp only [rlinksOf] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [hv] at h
      simp only at h
      split at h
      · rename_i a b ha hb
        cases h
        exact ⟨a, ha, fun p hp ↦ List.mem_append_left _ hp⟩
      · cases h
    · cases hT : T'.reg r' with
      | none =>
        rw [hT] at h
        exact rlinksOf_spec h r hr v hv
      | some u =>
        rw [hT] at h
        simp only at h
        split at h
        · rename_i a b ha hb
          cases h
          obtain ⟨c, hc, hcL⟩ := rlinksOf_spec hb r hr v hv
          exact ⟨c, hc, fun p hp ↦ List.mem_append_right _ (hcL p hp)⟩
        · cases h

theorem rlinks_spec {call : Bool} {S' T' : SState} {L : List (Nat × Sym)}
    (h : rlinks call S' T' = some L) {r : Reg64} {v : Sym} (hv : T'.reg r = some v) :
    ∃ a, regLink call S' r v = some a ∧ ∀ p ∈ a, p ∈ L :=
  rlinksOf_spec h r (mem_allRegs r) v hv

theorem wlink_spec {S' : SState} {w : Write} {p : Nat × Sym} (h : wlink S' w = some p) :
    w.v = .var p.1 ∧ ∀ t < w.n, findWrite w.r (w.off + t) S'.mem = some (p.2, t) := by
  unfold wlink at h
  split at h
  · rename_i i s hv hf
    split at h
    · rename_i hall
      cases h
      refine ⟨hv, fun t ht ↦ ?_⟩
      have := List.all_eq_true.mp hall t (List.mem_range.mpr ht)
      exact beq_iff_eq.mp this
    · cases h
  · cases h

theorem wlinks_spec {S' : SState} :
    ∀ {ws : List Write} {L : List (Nat × Sym)}, wlinks S' ws = some L →
      ∀ w ∈ ws, ∃ p ∈ L, wlink S' w = some p
  | [], _, _, w, hw => by cases hw
  | w' :: ws, L, h, w, hw => by
    simp only [wlinks] at h
    split at h
    · rename_i a b ha hb
      cases h
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨a, List.mem_cons_self, ha⟩
      · obtain ⟨p, hp, hpw⟩ := wlinks_spec hb w hw
        exact ⟨p, List.mem_cons_of_mem _ hp, hpw⟩
    · cases h

theorem tpl_reg (sizes : List Nat) (known : List (Reg64 × Sym)) (ws : List Write)
    (bounds : List (Sym × Nat)) (aliases : List (Sym × Nat × Int)) (r : Reg64) :
    (tpl sizes known ws bounds aliases).reg r = some ((known.lookup r).getD (.reg r)) := by
  unfold tpl SState.reg init
  simp only
  rw [allRegs_map_getElem?]
  rfl

/-! ## Words -/

theorem ofBytes_eq_leNat : ∀ bs : List UInt8, Nat.ofBytes bs = NativeRustcVm.leNat bs
  | [] => rfl
  | b :: bs => by
    show Nat.ofBytes bs * 256 + b.toNat = b.toNat + 256 * NativeRustcVm.leNat bs
    rw [ofBytes_eq_leNat bs]
    omega

/-- **An environment's load of eight bytes** is the word `wordOf` reads there. -/
theorem load_eq_wordOf (env : Env) (r off : Nat) :
    env.load r off 8 =
      (NativeRustcVm.wordOf env.mem0 (env.base r + BitVec.ofNat 64 off)).toBitVec := by
  unfold Env.load NativeRustcVm.wordOf NativeRustcVm.bytesFrom
  rw [ofBytes_natCast, BitVec.ofInt_natCast, ofBytes_eq_leNat]
  show BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  congr 2
  apply List.map_congr_left
  intro i _
  rw [addr_add]

/-- `EW::mul`'s result, from the arguments' values at the call. -/
theorem mulRes_of [Labels] {env : Env} {S' : SState} {mc : MachineData}
    (hR : ∀ r v, S'.reg r = some v → reg mc r = v.eval env) {a0 a1 b0 b1 : Sym}
    (h0 : S'.reg .rdi = some a0) (h1 : S'.reg .rsi = some a1) (h2 : S'.reg .rdx = some b0)
    (h3 : S'.reg .rcx = some b1) {x y : NativeVm.Model.EW} (hx0 : a0.eval env = x.c0.toBitVec)
    (hx1 : a1.eval env = x.c1.toBitVec) (hy0 : b0.eval env = y.c0.toBitVec)
    (hy1 : b1.eval env = y.c1.toBitVec) :
    mulRes mc = ((NativeVm.Model.EW.mul x y).c0.toBitVec, (NativeVm.Model.EW.mul x y).c1.toBitVec) := by
  unfold mulRes
  rw [hR _ _ h0, hR _ _ h1, hR _ _ h2, hR _ _ h3, hx0, hx1, hy0, hy1]

/-! ## Templates -/

/-- **A template's `Match`** from its registers' and writes' values. -/
theorem match_tpl [Labels] {env : Env} {T : SState} {m : MachineData}
    (hmem0 : env.mem0 = m.dmem) (hfl : env.flags = m.status)
    (hregs : ∀ r v, T.reg r = some v → m.regs.get64 r = v.eval env)
    (hflags : T.flags = atomFlags)
    (hregions : ∀ (r n : Nat), T.regions[r]? = some n → ∃ b, env.regions[r]? = some (b, n))
    (hlabels : T.labels = []) (hbounds : ∀ x n, (x, n) ∈ T.bounds → (x.eval env).toNat < n)
    (haliases : AliasesOk T env)
    (hw : ∀ r b sz j v t, env.regions[r]? = some (b, sz) → j < sz →
      findWrite r j T.mem = some (v, t) →
      m.dmem.get? (b + BitVec.ofNat 64 j) = some (byteOf (v.eval env) t))
    (hknown : T.known = [] := by rfl) :
    Match env T m where
  regs := hregs
  flags := by
    rw [hflags]
    refine ⟨fun b h ↦ ?_, fun b h ↦ ?_, fun b h ↦ ?_, fun b h ↦ ?_⟩ <;> cases h <;>
      rw [← hfl] <;> rfl
  regions := hregions
  mem r b n hb i hi := by
    unfold memByte
    cases hf : findWrite r i T.mem with
    | none => rw [hmem0]
    | some vt =>
      obtain ⟨v, t⟩ := vt
      exact hw r b n i v t hb hi hf
  labels l r h := by rw [hlabels] at h; cases h
  bounds := hbounds
  aliases := haliases
  outside a _ := by rw [hmem0]
  known := by rw [hknown]; intro w hw; cases hw

variable {m0 : MachineData} {F N : Nat} {rs : List (BitVec 64 × Nat)} {wr : Nat → Bool}

theorem regions_envS {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64} {T : SState}
    (hT : T.regions = (F + 8) :: rs.map Prod.snd) :
    ∀ (r n : Nat), T.regions[r]? = some n →
      ∃ b, (envS m0 m F rs vals ret).regions[r]? = some (b, n) := by
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

/-! ## The layout -/

theorem Lay.geo (h : Lay m0 F N rs) : Geo m0 F N := ⟨h.ok, h.le, h.f8⟩

theorem Lay.frame_apart (h : Lay m0 F N rs) {e : BitVec 64 × Nat} (he : e ∈ rs) :
    Apart (stackBelow m0 F) (F + 8) e.1 e.2 := by
  have ha := (mem_of_allOf h.arr he).2.2
  have g := h.geo
  have hb := g.base
  have hN := g.below
  have := g.sp
  have := g.le
  unfold Apart at ha ⊢
  omega

theorem Lay.wf (h : Lay m0 F N rs) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {vals : Nat → BitVec 64} {ret : BitVec 64} : (envS m0 m F rs vals ret).WF := by
  have g := h.geo
  refine Env.wf_of ⟨⟨fun i hi ↦ hk _ (g.okF.2.2 i hi), frame_noWrap g.okF⟩, ?_⟩ ?_
  · show AllOf _ rs
    have harr := h.arr
    clear h g
    induction rs with
    | nil => trivial
    | cons e rs ih =>
      exact ⟨⟨fun i hi ↦ hk _ (harr.1.1 i hi), harr.1.2.1⟩, ih harr.2⟩
  · show List.Pairwise _ ((stackBelow m0 F, F + 8) :: rs)
    exact List.Pairwise.cons (fun e he ↦ h.frame_apart he) h.disj

/-- A read-only GOT region extends a layout without adding a writable area. -/
theorem Lay.withGot [Labels] {l : Label} (h : Lay m0 F N rs)
    (hg : GotAt m0 N rs [l]) : Lay m0 F N (rs ++ [(gotAddr l, 8)]) := by
  refine ⟨h.ok, h.le, h.f8, ?_, ?_⟩
  · have hall : ∀ a ∈ rs ++ [(gotAddr l, 8)],
        Mapped m0.dmem a.1 a.2 ∧ NoWrap a.1 a.2 ∧
          Apart a.1 a.2 (stackBelow m0 N) (N + 8) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact mem_of_allOf h.arr ha
      · simp only [List.mem_singleton] at ha
        subst a
        exact ⟨hg.mapped (by simp), (hg.1 l (by simp)).2.1,
          (hg.1 l (by simp)).2.2.1⟩
    generalize rs ++ [(gotAddr l, 8)] = xs at hall ⊢
    induction xs with
    | nil => trivial
    | cons a xs ih =>
      exact ⟨hall a (by simp), ih (fun b hb => hall b (by simp [hb]))⟩
  · rw [List.pairwise_append]
    refine ⟨h.disj, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact ((hg.1 l (by simp)).2.2.2 a ha).symm

/-- An address of the stack below the frame's base is in the `N` bytes of stack. -/
theorem Lay.stack_in (h : Lay m0 F N rs) {p : BitVec 64} {S : Nat} (hS : F + S ≤ N)
    {m : MachineData} (hrsp : rspOf m = stackBelow m0 F)
    (hp : InRange (stackBelow m S) S p) : InRange (stackBelow m0 N) N p := by
  have g := h.geo
  have hs := g.sp
  have hb := g.base
  have hmb : (stackBelow m S).toNat = (rspOf m0).toNat - F - S := by
    rw [stackBelow_toNat' (by rw [hrsp, hb]; omega), hrsp, hb]
  rw [NativeRustcX64.Sym.inRange_iff (by rw [hmb]; have := g.top; omega), hmb] at hp
  rw [inRange_N g]
  omega

/-- The bytes of the frame and of the arrays are outside the stack below the frame's base. -/
theorem Lay.region_not_stack (h : Lay m0 F N rs) {S : Nat} (hS : F + S ≤ N) {m : MachineData}
    (hrsp : rspOf m = stackBelow m0 F) {vals : Nat → BitVec 64} {ret : BitVec 64} {r : Nat}
    {b : BitVec 64} {sz j : Nat} (hb : (envS m0 m F rs vals ret).regions[r]? = some (b, sz))
    (hj : j < sz) : ¬InRange (stackBelow m S) S (b + BitVec.ofNat 64 j) := by
  intro hp
  have g := h.geo
  have hs := g.sp
  have hbase := g.base
  have hmb : (stackBelow m S).toNat = (rspOf m0).toNat - F - S := by
    rw [stackBelow_toNat' (by rw [hrsp, hbase]; omega), hrsp, hbase]
  rw [NativeRustcX64.Sym.inRange_iff (by rw [hmb]; have := g.top; omega), hmb] at hp
  cases r with
  | zero =>
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [g.addr (by omega)] at hp
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
theorem Lay.written (h : Lay m0 F N rs) {m : MachineData} {vals : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hw : S.mem.all (writeOk F ((F + 8) :: rs.map Prod.snd) wr) = true) {q : BitVec 64}
    (hq : Written (envS m0 m F rs vals ret) S q) :
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
    have hsz : ((F + 8) :: rs.map Prod.snd).getD (i + 1) 0 = sz := by
      simp [List.getD_eq_getElem?_getD, hb]
    exact ⟨i, (b, sz), hwr, hb, by
      rw [NativeRustcX64.Sym.inRange_iff hnw]
      omega⟩

/-- The return address is neither in the stack below RSP nor in an array. -/
theorem Lay.ret_same (h : Lay m0 F N rs) {m : MachineData}
    (hs : SameOutside m0.dmem m.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q)) :
    ∀ j < 8, m.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) := by
  intro j hj
  have g := h.geo
  have ht := g.top
  have hsN := g.sp
  have hq : (rspOf m0 + BitVec.ofNat 64 j).toNat = (rspOf m0).toNat + j :=
    toNat_add_ofNat _ _ (by omega)
  refine hs _ fun hin ↦ hin.elim (fun h1 ↦ ?_) fun ⟨i, e, _, he, h2⟩ ↦ ?_
  · rw [inRange_N g, hq] at h1
    omega
  · obtain ⟨-, hnw, hap⟩ := mem_of_allOf h.arr (List.mem_of_getElem? he)
    rw [NativeRustcX64.Sym.inRange_iff hnw, hq] at h2
    unfold Apart at hap
    rw [g.below] at hap
    omega

/-- The stack a callee using `S` bytes sees, at the frame's base. -/
theorem Lay.stackOk (h : Lay m0 F N rs) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    (hrsp : rspOf m = stackBelow m0 F) {S : Nat} (hS : F + S ≤ N) : StackOk m S := by
  have g := h.geo
  have hs := g.sp
  have ht := g.top
  have hbase := g.base
  have hsp : (rspOf m).toNat = (rspOf m0).toNat - F := by rw [hrsp, hbase]
  have hmb : (stackBelow m S).toNat = (rspOf m0).toNat - F - S := by
    rw [stackBelow_toNat' (by omega), hsp]
  refine ⟨by omega, by omega, fun i hi ↦ hk _ (g.mapped ?_ ?_)⟩ <;>
    rw [show rspOf m - BitVec.ofNat 64 S = stackBelow m S from rfl,
      toNat_add_ofNat _ _ (by omega), hmb] <;> omega

theorem regLink_spec {call : Bool} {S' : SState} {r : Reg64} {v : Sym} {a : List (Nat × Sym)}
    (h : regLink call S' r v = some a) :
    (call = true ∧ r = .rsp ∧ v = .ptr 0 8 ∧ S'.reg .rsp = some (.ptr 0 0)) ∨
    (¬(call = true ∧ r = .rsp) ∧
      (v = .reg r ∨ (∃ i, v = .var i ∧ call = true ∧ (r = .rax ∨ r = .rdx)) ∨
      (∃ i s, v = .var i ∧ (call = false ∨ calleeSaved r = true) ∧ S'.reg r = some s ∧
        a = [(i, s)]) ∨
      ((∃ x o, v = .ptr x o) ∨ (∃ n, v = .lit n) ∨ (∃ l, v = .label l)) ∧
        (call = false ∨ calleeSaved r = true) ∧ S'.reg r = some v)) := by
  unfold regLink at h
  by_cases hc : call = true ∧ r = .rsp
  · rw [ite_pos hc] at h
    by_cases hv : v = .ptr 0 8 ∧ S'.reg .rsp = some (.ptr 0 0)
    · exact .inl ⟨hc.1, hc.2, hv.1, hv.2⟩
    · rw [ite_neg hv] at h
      cases h
  · rw [ite_neg hc] at h
    refine .inr ⟨hc, ?_⟩
    split at h
    · rename_i r'
      by_cases he : r' = r
      · exact .inl (by rw [he])
      · rw [ite_neg he] at h
        cases h
    · rename_i i
      by_cases h1 : call = true ∧ (r = .rax ∨ r = .rdx)
      · exact .inr (.inl ⟨i, rfl, h1⟩)
      · rw [ite_neg h1] at h
        by_cases h2 : call = false ∨ calleeSaved r = true
        · rw [ite_pos h2] at h
          obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .inr (.inr (.inl ⟨i, s, rfl, h2, hs, rfl⟩))
        · rw [ite_neg h2] at h
          cases h
    · rename_i x o
      by_cases h1 : (call = false ∨ calleeSaved r = true) ∧ S'.reg r = some (.ptr x o)
      · exact .inr (.inr (.inr ⟨.inl ⟨x, o, rfl⟩, h1.1, h1.2⟩))
      · rw [ite_neg h1] at h
        cases h
    · rename_i n
      by_cases h1 : (call = false ∨ calleeSaved r = true) ∧ S'.reg r = some (.lit n)
      · exact .inr (.inr (.inr ⟨.inr (.inl ⟨n, rfl⟩), h1.1, h1.2⟩))
      · rw [ite_neg h1] at h
        cases h
    · rename_i l
      by_cases h1 : (call = false ∨ calleeSaved r = true) ∧ S'.reg r = some (.label l)
      · exact .inr (.inr (.inr ⟨.inr (.inr ⟨l, rfl⟩), h1.1, h1.2⟩))
      · rw [ite_neg h1] at h
        cases h
    · cases h

/-- A register of the template from the block's result, in a step without a call. -/
theorem reg_link_jump [Labels] {env env' : Env} {S' T' : SState} {m : MachineData}
    {L : List (Nat × Sym)} (hL : rlinks false S' T' = some L) (hm : Match env S' m)
    (hbase : ∀ r, env'.base r = env.base r) (hregs : ∀ r, env'.regs r = m.regs.get64 r)
    (hvals : ∀ p ∈ L, p.2.eval env = env'.vars p.1) :
    ∀ r v, T'.reg r = some v → m.regs.get64 r = v.eval env' := by
  intro r v hv
  obtain ⟨a, ha, haL⟩ := rlinks_spec hL hv
  rcases regLink_spec ha with ⟨hc, -⟩ | ⟨-, hr | ⟨i, -, hc, -⟩ | ⟨i, s, rfl, -, hs, rfl⟩ |
      ⟨hpl, -, hs⟩⟩
  · cases hc
  · subst hr
    exact (hregs r).symm
  · cases hc
  · rw [hm.regs r s hs, hvals (i, s) (haL _ List.mem_cons_self)]
    rfl
  · rw [hm.regs r v hs]
    rcases hpl with ⟨x, o, rfl⟩ | ⟨n, rfl⟩ | ⟨l, rfl⟩
    · simp only [Sym.eval, hbase]
    · rfl
    · rfl

/-- **A template in another environment**: the machine state a block's result `S'` describes in
`env`, the template `T'` (`tplOk`, linked to `S'` by `L`, `LW`) describes in any `env'` of the same
machine state whose region `0` is `env`'s, whose variables are the links' values. -/
theorem match_links [Labels] {env env' : Env} {S' T' : SState} {m : MachineData}
    (hm : Match env S' m) (hok : tplOk T' = true) {L LW : List (Nat × Sym)}
    (hL : rlinks false S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hregs : ∀ r, env'.regs r = m.regs.get64 r) (hmem : env'.mem0 = m.dmem)
    (hfl : env'.flags = m.status) (h0 : env'.regions[0]? = env.regions[0]?)
    (hvals : ∀ p ∈ L ++ LW, p.2.eval env = env'.vars p.1)
    (hflags : T'.flags = atomFlags)
    (hregions : ∀ (r n : Nat), T'.regions[r]? = some n → ∃ b, env'.regions[r]? = some (b, n))
    (hlab : T'.labels = []) (hbd : ∀ x n, (x, n) ∈ T'.bounds → (x.eval env').toNat < n)
    (hal : AliasesOk T' env') (hknown : T'.known = [] := by rfl) : Match env' T' m := by
  simp only [tplOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hokr, hokw⟩ := hok
  have hb0 : ∀ o, (Sym.ptr 0 o).eval env' = (Sym.ptr 0 o).eval env := by
    intro o
    simp only [Sym.eval, Env.base, h0]
  refine match_tpl (hknown := hknown) hmem hfl ?_ hflags hregions hlab hbd hal ?_
  · intro r v hv
    obtain ⟨a, ha, haL⟩ := rlinks_spec hL hv
    have hk := hokr r (mem_allRegs r)
    rw [hv] at hk
    rcases regLink_spec ha with ⟨hc, -⟩ | ⟨-, hr | ⟨i, -, hc, -⟩ | ⟨i, s, rfl, -, hs, rfl⟩ |
        ⟨hpl, -, hs⟩⟩
    · cases hc
    · subst hr
      exact (hregs r).symm
    · cases hc
    · rw [hm.regs r s hs, hvals (i, s) (List.mem_append_left _ (haL _ List.mem_cons_self))]
      rfl
    · rw [hm.regs r v hs]
      rcases hpl with ⟨x, o, rfl⟩ | ⟨n, rfl⟩ | ⟨l, rfl⟩
      · cases x with
        | zero => exact (hb0 o).symm
        | succ x => simp at hk
      · rfl
      · rfl
  · intro r b sz j v t hb hj hf
    obtain ⟨w, hwm, hwr, h1, h2, hv, ht⟩ := findWrite_spec hf
    obtain ⟨p, hpL, hpw⟩ := wlinks_spec hLW w hwm
    obtain ⟨hwv, hall⟩ := wlink_spec hpw
    have hw0 := hokw w hwm
    simp only [beq_iff_eq] at hw0
    have hr0 : r = 0 := hwr ▸ hw0.1
    subst hr0
    have hf' := hall t (by omega)
    rw [hwr, show w.off + t = j by omega] at hf'
    have hbe : env.regions[0]? = some (b, sz) := h0 ▸ hb
    rw [hm.mem 0 b sz hbe j hj, memByte, hf', ← hv, hwv]
    simp only [Sym.eval]
    exact congrArg (fun x ↦ some (byteOf x t)) (hvals p (List.mem_append_right _ hpL))

/-- Change only the symbolic layout between blocks, retaining the original write footprint. -/
theorem Bnd.relayout [Labels] {m : MachineData} {T T' : SState}
    {vals vals' : Nat → BitVec 64} {rs' : List (BitVec 64 × Nat)} {wr' : Nat → Bool}
    (hB : Bnd m0 F N rs wr T vals m)
    (hok : tplOk T' = true) {L LW : List (Nat × Sym)}
    (hL : rlinks false T T' = some L) (hLW : wlinks T T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m F rs vals ret) = vals' p.1)
    (hflags : T'.flags = atomFlags)
    (hsizes : T'.regions = (F + 8) :: rs'.map Prod.snd)
    (hlab : T'.labels = [])
    (hbd : ∀ ret, ∀ x n, (x, n) ∈ T'.bounds →
      (x.eval (envS m0 m F rs' vals' ret)).toNat < n)
    (hal : ∀ ret, AliasesOk T' (envS m0 m F rs' vals' ret))
    (houts : ∀ q, outsOf rs wr q → outsOf rs' wr' q)
    (hknown : T'.known = [] := by rfl) :
    Bnd m0 F N rs' wr' T' vals' m :=
  ⟨fun ret => match_links (hB.mt ret) hok hL hLW (fun _ => rfl) rfl rfl rfl
      (hvals ret) hflags (regions_envS hsizes) hlab (hbd ret) (hal ret) hknown,
    fun q hq => hB.same q (fun h => hq (h.elim Or.inl (fun h => Or.inr (houts q h)))),
    hB.kept⟩

/-- Seed a slot's bytes in a template after proving them from the loader and frame. -/
theorem Bnd.withKnownBytes [Labels] {m : MachineData} {T : SState}
    {vals : Nat → BitVec 64} {r off n : Nat} {v : Sym}
    (hB : Bnd m0 F N rs wr T vals m)
    (hb : ∀ ret, ∀ i < n,
      (envS m0 m F rs vals ret).mem0.get?
        ((envS m0 m F rs vals ret).base r + BitVec.ofNat 64 (off + i)) =
        some (byteOf (v.eval (envS m0 m F rs vals ret)) i)) :
    Bnd m0 F N rs wr (T.withKnownBytes r off n v) vals m :=
  ⟨fun ret => (hB.mt ret).withKnownBytes (hb ret), hB.same, hB.kept⟩

variable [Host]

/-! ## Steps -/

/-- **The start**: the entry state, with the template's known registers' values. -/
theorem start {sizes : List Nat} {known : List (Reg64 × Sym)}
    {vals : Nat → BitVec 64} (hsz : sizes = (F + 8) :: rs.map Prod.snd)
    (hknown : ∀ ret, AllOf (fun p ↦ m0.regs.get64 p.1 = p.2.eval (envS m0 m0 F rs vals ret)) known) :
    Bnd m0 F N rs wr (tpl sizes known []) vals m0 :=
  ⟨fun ret ↦ match_tpl rfl rfl (fun r v hv ↦ by
      rw [tpl_reg] at hv
      cases hv
      cases hl : known.lookup r with
      | none => rfl
      | some u =>
        exact lookup_of_allOf (P := fun r v ↦
          m0.regs.get64 r = v.eval (envS m0 m0 F rs vals ret)) (fun _ _ ↦ Reg64.eq_of_beq)
          (hknown ret) hl)
      rfl (regions_envS hsz) rfl (fun _ _ h ↦ by cases h) (fun _ _ _ h ↦ by cases h)
      (fun _ _ _ _ _ _ _ _ h ↦ by cases h),
    fun _ _ ↦ rfl, fun _ h ↦ h⟩

/-- **A block without a call**, to the template `T'`. -/
theorem jumpStep (h : Lay m0 F N rs) {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 F N rs wr T vals m) {ds : List Directive} {k : Nat} {x : Exit}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', x))
    (hx : ∀ l, x ≠ .call l) (hwr : S'.mem.all (writeOk F ((F + 8) :: rs.map Prod.snd) wr) = true)
    {L LW : List (Nat × Sym)} (hL : rlinks false S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW, p.2.eval (envS m0 m F rs vals ret) = vals' p.1)
    (hsz : T'.regions = (F + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' F rs vals' ret))
    (hbd : ∀ (m' : MachineData) ret, ∀ x n, (x, n) ∈ T'.bounds →
      (x.eval (envS m0 m' F rs vals' ret)).toNat < n)
    {R : MachineState → Prop}
    (cont : ∀ st, PcOk (envS m0 m F rs vals 0) x (Host.addrOf (k + ds.length)) st →
      Bnd m0 F N rs wr T' vals' st.data → Match (envS m0 m F rs vals 0) S' st.data →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwf := h.wf hB.kept (vals := vals) (ret := 0)
  refine exec_then hk hrun hwf (fun l hl ↦ absurd hl (hx l)) (hB.mt 0) fun st hm hpc ↦
    cont st hpc ⟨fun ret ↦ ?_, ?_, fun p hp ↦ hm.kept hwf p (hB.kept p hp)⟩ hm
  · refine match_tpl (hknown := hknown) rfl rfl (reg_link_jump hL hm (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun p hp ↦ hvals 0 p (List.mem_append_left _ hp))) hfl (regions_envS hsz) hlab
      (hbd st.data ret) (hal st.data ret) ?_
    intro r b sz j v t hb hj hf
    obtain ⟨w, hwm, hwr', h1, h2, hv, ht⟩ := findWrite_spec hf
    obtain ⟨p, hpL, hpw⟩ := wlinks_spec hLW w hwm
    obtain ⟨hwv, hall⟩ := wlink_spec hpw
    have hf' := hall t (by omega)
    rw [hwr', show w.off + t = j by omega] at hf'
    have hb0 : (envS m0 m F rs vals 0).regions[r]? = some (b, sz) := hb
    rw [hm.mem r b sz hb0 j hj, memByte, hf', ← hv, hwv]
    simp only [Sym.eval]
    exact congrArg (fun x ↦ some (byteOf x t)) (hvals 0 p (List.mem_append_right _ hpL))
  · intro q hq
    rw [hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr hW)]
    exact hB.same q hq

/-- **A block ending in a call**, the callee's contract, to the template `T'`; RAX and RDX what
the callee's postcondition says of them (`hrax`, `hrdx`); its outputs `W` in the stack or the
writable arrays, not in the template's writes. The continuation also gets the state at the call
and the callee's postcondition. -/
theorem callStep (h : Lay m0 F N rs) {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 F N rs wr T vals m) {ds : List Directive} {k : Nat} {l : Label}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', .call l))
    (hwr : S'.mem.all (writeOk F ((F + 8) :: rs.map Prod.snd) wr) = true) (hsp : S'.reg .rsp = some (.ptr 0 0))
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {S : Nat} (hS : F + S ≤ N)
    (hP : ∀ mc, Match (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc →
      Kept m0.dmem mc.dmem → StackOk mc S → P mc)
    {W : BitVec 64 → Prop}
    (hQ : ∀ m m', Q m m' → SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m S) S q ∨ W q) ∧
      Saved m m')
    (hWo : ∀ q, W q → InRange (stackBelow m0 N) N q ∨ outsOf rs wr q)
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW, p.2.eval (envS m0 m F rs vals ret) = vals' p.1)
    (hrax : ∀ i, T'.reg .rax = some (.var i) → ∀ mc m' : MachineData,
      Match (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc → Q mc m' →
      reg m' .rax = vals' i)
    (hrdx : ∀ i, T'.reg .rdx = some (.var i) → ∀ mc m' : MachineData,
      Match (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc → Q mc m' →
      reg m' .rdx = vals' i)
    (hWT : ∀ (mc : MachineData) ret r b sz j v t,
      (envS m0 mc F rs vals' ret).regions[r]? = some (b, sz) → j < sz →
      findWrite r j T'.mem = some (v, t) → ¬W (b + BitVec.ofNat 64 j))
    (hsz : T'.regions = (F + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' F rs vals' ret))
    (hbd : ∀ (m' : MachineData) ret, ∀ x n, (x, n) ∈ T'.bounds →
      (x.eval (envS m0 m' F rs vals' ret)).toNat < n)
    {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + ds.length) → Bnd m0 F N rs wr T' vals' st.data →
      (∃ mc, Match (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec) S' mc ∧
        rspOf mc = stackBelow m0 F ∧ Q mc st.data) →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  let ra := (Host.addrOf (k + ds.length)).toBitVec
  have hwf := h.wf hB.kept (vals := vals) (ret := ra)
  have g := h.geo
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
  refine call_then (env := envS m0 m F rs vals ra) hpc hspec (hP st.data hm hkept (h.stackOk hkept hrsp hS))
    fun st' hpc' hrsp2 hqc ↦ cont st' hpc' ⟨fun ret ↦ ?_, ?_, fun p hp ↦ (hQ _ _ hqc).2.2 p (hkept p hp)⟩
      ⟨st.data, hm, hrsp, hqc⟩
  · obtain ⟨hso, hsv⟩ := hQ _ _ hqc
    refine match_tpl (hknown := hknown) rfl rfl ?_ hfl (regions_envS hsz) hlab (hbd st'.data ret) (hal st'.data ret) ?_
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
        · exact hrax i hv st.data st'.data hm hqc
        · exact hrdx i hv st.data st'.data hm hqc
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
      have hb0 : (envS m0 m F rs vals ra).regions[r]? = some (b, sz) := hb
      have hnot : ¬(InRange (stackBelow st.data S) S (b + BitVec.ofNat 64 j) ∨
          W (b + BitVec.ofNat 64 j)) := fun hin ↦ hin.elim
        (fun h1 ↦ h.region_not_stack (vals := vals) (ret := ra) hS hrsp hb0 hj h1)
        (fun h2 ↦ hWT st'.data ret r b sz j v t hb hj hf h2)
      rw [hso _ hnot, hm.mem r b sz hb0 j hj, memByte, hf', ← hv, hwv]
      simp only [Sym.eval]
      exact congrArg (fun x ↦ some (byteOf x t)) (hvals ra p (List.mem_append_right _ hpL))
  · intro q hq
    rw [(hQ _ _ hqc).1 q fun hin ↦ hq (hin.elim (fun h' ↦ .inl (h.stack_in hS hrsp h'))
      fun h' ↦ hWo q h')]
    exact hsame q hq

/-- **The last block**, ending in `ret`: back at the entry's return address, RSP 8 above the
entry's, the callee-saved registers the entry's. -/
theorem exitStep (h : Lay m0 F N rs) {T S' : SState} {vals : Nat → BitVec 64} {m : MachineData}
    (hB : Bnd m0 F N rs wr T vals m) {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', .ret (.load 0 F 8)))
    (hwr : S'.mem.all (writeOk F ((F + 8) :: rs.map Prod.snd) wr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int)))
    (hcs : ∀ r, calleeSaved r = true →
      ∃ v, S'.reg r = some v ∧ v.eval (envS m0 m F rs vals 0) = m0.regs.get64 r)
    {R : MachineState → Prop}
    (cont : ∀ st, Match (envS m0 m F rs vals 0) S' st.data → st.pc = retOf m0 →
      rspOf st.data = rspOf m0 + 8#64 →
      SameOutside m0.dmem st.data.dmem (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) →
      Saved m0 st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwf := h.wf hB.kept (vals := vals) (ret := 0)
  have g := h.geo
  refine exec_then hk hrun hwf nofun (hB.mt 0) fun st hm hpc ↦ ?_
  have hsame : SameOutside m0.dmem st.data.dmem
      (fun q ↦ InRange (stackBelow m0 N) N q ∨ outsOf rs wr q) := fun q hq ↦ by
    rw [hm.get?_mem0 hwf fun hW ↦ hq (h.written hwr hW)]
    exact hB.same q hq
  refine cont st hm ?_ ?_ hsame ⟨fun r hr ↦ ?_, fun p hp ↦ hm.kept hwf p (hB.kept p hp)⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact load_ret (m := m) (vars := vals) (ret := 0) g.okF (h.ret_same hB.same)
  · show st.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact frame_rsp F 8
  · obtain ⟨v, hv, he⟩ := hcs r hr
    rw [hm.regs r v hv, he]

/-- **A block ending in a call of `EW::sq_iter`.** -/
theorem sqStep (h : Lay m0 F N rs) (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hS : F + ewSqIterStack ≤ N) {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 F N rs wr T vals m) {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWSqIter.entryLabel))
    (hwr : S'.mem.all (writeOk F ((F + 8) :: rs.map Prod.snd) wr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0))
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW, p.2.eval (envS m0 m F rs vals ret) = vals' p.1)
    (hrax : ∀ i, T'.reg .rax = some (.var i) → ∀ mc : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      (sqRes mc).1 = vals' i)
    (hrdx : ∀ i, T'.reg .rdx = some (.var i) → ∀ mc : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      (sqRes mc).2 = vals' i)
    (hsz : T'.regions = (F + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' F rs vals' ret))
    (hbd : T'.bounds = [])
    {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + ds.length) → Bnd m0 F N rs wr T' vals' st.data →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ :=
  callStep (hknown := hknown) h hB hk hrun hwr hsp hsq hS (fun _ _ _ h ↦ h) (W := fun _ ↦ False)
    (fun _ _ hq ↦ ⟨fun p hp ↦ hq.2.2.1 p fun h ↦ hp (.inl h), hq.2.2.2⟩) (fun _ h ↦ h.elim)
    hL hLW hvals
    (fun i hi mc m' hm hq ↦ hq.1.trans (hrax i hi mc fun r v h ↦ hm.regs r v h))
    (fun i hi mc m' hm hq ↦ hq.2.1.trans (hrdx i hi mc fun r v h ↦ hm.regs r v h))
    (fun _ _ _ _ _ _ _ _ _ _ _ h ↦ h) hsz hfl hlab hal
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx) fun st h1 h2 _ ↦ cont st h1 h2

/-- **A block ending in a call of `EW::mul`.** -/
theorem mulStep (h : Lay m0 F N rs) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hS : F + ewMulStack ≤ N) {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 F N rs wr T vals m) {ds : List Directive} {k : Nat}
    (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hwr : S'.mem.all (writeOk F ((F + 8) :: rs.map Prod.snd) wr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0))
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW, p.2.eval (envS m0 m F rs vals ret) = vals' p.1)
    (hrax : ∀ i, T'.reg .rax = some (.var i) → ∀ mc : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      (mulRes mc).1 = vals' i)
    (hrdx : ∀ i, T'.reg .rdx = some (.var i) → ∀ mc : MachineData, (∀ r v, S'.reg r = some v →
      reg mc r = v.eval (envS m0 m F rs vals (Host.addrOf (k + ds.length)).toBitVec)) →
      (mulRes mc).2 = vals' i)
    (hsz : T'.regions = (F + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' F rs vals' ret)) (hbd : T'.bounds = [])
    {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + ds.length) → Bnd m0 F N rs wr T' vals' st.data →
      Eventually (step1 Host.exe) R st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ :=
  callStep (hknown := hknown) h hB hk hrun hwr hsp hmul hS (fun _ _ _ h ↦ h) (W := fun _ ↦ False)
    (fun _ _ hq ↦ ⟨fun p hp ↦ hq.2.2.1 p fun h ↦ hp (.inl h), hq.2.2.2⟩) (fun _ h ↦ h.elim)
    hL hLW hvals
    (fun i hi mc m' hm hq ↦ hq.1.trans (hrax i hi mc fun r v h ↦ hm.regs r v h))
    (fun i hi mc m' hm hq ↦ hq.2.1.trans (hrdx i hi mc fun r v h ↦ hm.regs r v h))
    (fun _ _ _ _ _ _ _ _ _ _ _ h ↦ h) hsz hfl hlab hal
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx) fun st h1 h2 _ ↦ cont st h1 h2

end

end NativeRustcVmX64.Ring
