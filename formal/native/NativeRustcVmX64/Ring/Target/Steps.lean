module

public import NativeRustcVmX64.Ring.Target.Basic
public import NativeRustcVmX64.Ring.Stack

/-!
# `ring_target`: a block and its call, with an invariant (x86-64)

`At`: before the block at `off`, the template `T` with the values `vals` in the layout `rs`, and an
invariant `I` of the machine state. `cstep`: a block ending in a call whose callee changes only its
stack, the invariant kept (`hI`). The images' copy at the frame's offset `1280` is kept by a block
writing below it and a callee below the frame (`cAt_call`). A callee's results (`sq_res`, `mul_res`,
`poly_res`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget

@[expose] public section

variable [Host]

/-- Before the block at `off`. -/
def At (m0 : MachineData) (k off : Nat) (rs : List (BitVec 64 × Nat)) (T : SState)
    (vals : Nat → BitVec 64) (I : MachineData → Prop) (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + off) ∧ Bnd m0 2352 NT rs noWr T vals st.data ∧ I st.data

/-- The images' copy, `64` elements at the frame's offset `1280`. -/
def CAt (m0 : MachineData) (d : MachineData) : Prop :=
  NativeRustcVm.EWsAt d.dmem (stackBelow m0 2352 + BitVec.ofNat 64 1280) (imgs m0).toList

/-- A block's writes miss the frame's bytes from `lo` to `hi`. -/
def missOk (lo hi : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r == 0 && (decide (w.off + w.n ≤ lo) || decide (hi ≤ w.off))

end

public section

variable {m0 : MachineData}

theorem imgs_size : (imgs m0).size = 64 := by
  simp [imgs, sl, arr, coeffCount]

/-- A byte of the frame between `lo` and `hi` no write covers. -/
theorem not_written_mid [Labels] {rs : List (BitVec 64 × Nat)} {m : MachineData}
    {vals : Nat → BitVec 64} {ret : BitVec 64} (g : NativeRustcVmX64.Field.Geo m0 2352 NT)
    {S : SState} {lo hi : Nat} (hS : missOk lo hi S = true) {j : Nat} (h1 : lo ≤ j) (h2 : j < hi)
    (hhi : hi ≤ 2360) :
    ¬Written (envS m0 m 2352 rs vals ret) S (stackBelow m0 2352 + BitVec.ofNat 64 j) := by
  rintro ⟨w, hw, b, sz, hb, hw1, hw2⟩
  simp only [missOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    decide_eq_true_eq] at hS
  obtain ⟨hr, hok⟩ := hS w hw
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [g.addr (by omega)] at hw1 hw2
  rw [g.base] at hw1 hw2
  omega

/-- **The copy kept** through a block writing below it and a callee below the frame. -/
theorem cAt_call [Labels] {rs : List (BitVec 64 × Nat)} {m mc m' : MachineData}
    {vals : Nat → BitVec 64} {ret : BitVec 64} (g : NativeRustcVmX64.Field.Geo m0 2352 NT)
    {S : SState} (hwf : (envS m0 m 2352 rs vals ret).WF) (hS : missOk 1280 2304 S = true)
    (hm : Match (envS m0 m 2352 rs vals ret) S mc) (hC : CAt m0 m) {n : Nat}
    (hsp : rspOf mc = stackBelow m0 2352) (hn : 2352 + n ≤ NT)
    (hq : SameOutside mc.dmem m'.dmem (InRange (stackBelow mc n) n)) : CAt m0 m' := by
  refine NativeRustcVm.BytesAt.of_sameOutside hC (R := fun q ↦ ?_) ?_ ?_
  · exact InRange (stackBelow mc n) n q ∨ Written (envS m0 m 2352 rs vals ret) S q
  · intro q hq'
    rw [hq q fun h ↦ hq' (.inl h)]
    exact hm.get?_mem0 hwf fun h ↦ hq' (.inr h)
  · intro i hi hR
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, imgs_size] at hi
    rw [NativeRustcVm.addr_add] at hR
    rcases hR with hR | hR
    · exact not_callee g.ok hsp hn (j := 1280 + i) (by omega) hR
    · exact not_written_mid g hS (j := 1280 + i) (by omega) (by omega) (by omega) hR

/-- **Frame bytes kept** through a block writing outside them. -/
theorem bytes_block [Labels] {rs : List (BitVec 64 × Nat)} {m mc : MachineData}
    {vals : Nat → BitVec 64} {ret : BitVec 64} (g : NativeRustcVmX64.Field.Geo m0 2352 NT)
    {S : SState} (hwf : (envS m0 m 2352 rs vals ret).WF) {lo hi : Nat}
    (hS : missOk lo hi S = true) (hhi : hi ≤ 2360)
    (hm : Match (envS m0 m 2352 rs vals ret) S mc) {a : Nat} {bs : List UInt8}
    (hb : NativeRustcVm.BytesAt m.dmem (stackBelow m0 2352 + BitVec.ofNat 64 a) bs)
    (hlo : lo ≤ a) (hlen : a + bs.length ≤ hi) :
    NativeRustcVm.BytesAt mc.dmem (stackBelow m0 2352 + BitVec.ofNat 64 a) bs :=
  NativeRustcVm.BytesAt.of_sameOutside hb (R := Written (envS m0 m 2352 rs vals ret) S)
    (fun q hq ↦ hm.get?_mem0 hwf hq) fun i hi hR ↦ by
      rw [NativeRustcVm.addr_add] at hR
      exact not_written_mid g hS (j := a + i) (by omega) (by omega) hhi hR

/-- **Frame bytes kept** by a callee below the frame. -/
theorem bytes_callee {mc m' : MachineData} (g : NativeRustcVmX64.Field.Geo m0 2352 NT) {lo : Nat}
    {bs : List UInt8}
    (hb : NativeRustcVm.BytesAt mc.dmem (stackBelow m0 2352 + BitVec.ofNat 64 lo) bs)
    (hlen : lo + bs.length ≤ 2360) {n : Nat} (hsp : rspOf mc = stackBelow m0 2352)
    (hn : 2352 + n ≤ NT) (hq : SameOutside mc.dmem m'.dmem (InRange (stackBelow mc n) n)) :
    NativeRustcVm.BytesAt m'.dmem (stackBelow m0 2352 + BitVec.ofNat 64 lo) bs :=
  NativeRustcVm.BytesAt.of_sameOutside hb hq fun i hi hR ↦ by
    rw [NativeRustcVm.addr_add] at hR
    exact not_callee g.ok hsp hn (j := lo + i) (by omega) hR

/-! ## A callee's results -/

section
variable [Labels] {env : Env} {S' : SState} {mc m' : MachineData}

theorem regv (hm : Match env S' mc) {r : Reg64} {a : Sym} (h : S'.reg r = some a) {v : BitVec 64}
    (hv : a.eval env = v) : reg mc r = v := (hm.regs r a h).trans hv

omit [Labels] in
theorem ew_eta (x : EW) : (⟨.ofBitVec (c0 x), .ofBitVec (c1 x)⟩ : EW) = x := rfl

/-- `EW::sq_iter`'s result. -/
theorem sq_res (hm : Match env S' mc) (hq : EWSqIterPost mc m') {n : Nat} (hn : n < 2 ^ 64)
    (h0 : S'.reg .rdi = some (.lit n)) {a b : Sym} (h1 : S'.reg .rsi = some a)
    (h2 : S'.reg .rdx = some b) {x y : EW} (ha : a.eval env = c0 x) (hb : b.eval env = c1 x)
    (hy : EW.sqIter n x = y) : reg m' .rax = c0 y ∧ reg m' .rdx = c1 y := by
  have e0 : (reg mc .rdi).toNat = n := by
    rw [regv hm h0 rfl]
    show (BitVec.ofNat 64 n).toNat = n
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  rw [hq.1, hq.2.1, e0, regv hm h1 ha, regv hm h2 hb, ew_eta, hy]
  exact ⟨rfl, rfl⟩

/-- `EW::mul`'s result. -/
theorem mul_res (hm : Match env S' mc) (hq : EWMulPost mc m') {a b c d : Sym}
    (h0 : S'.reg .rdi = some a) (h1 : S'.reg .rsi = some b) (h2 : S'.reg .rdx = some c)
    (h3 : S'.reg .rcx = some d) {x y z : EW} (ha : a.eval env = c0 x) (hb : b.eval env = c1 x)
    (hc : c.eval env = c0 y) (hd : d.eval env = c1 y) (hz : x * y = z) :
    reg m' .rax = c0 z ∧ reg m' .rdx = c1 z := by
  rw [hq.1, hq.2.1, regv hm h0 ha, regv hm h1 hb, regv hm h2 hc, regv hm h3 hd, ew_eta, ew_eta,
    ← hz]
  exact ⟨rfl, rfl⟩

/-- `poly_eval`'s result, over a slice of known elements. -/
theorem poly_res (hm : Match env S' mc) (hq : PolyEvalPost mc m') {xs : Array EW}
    (hs : slice mc (reg mc .rdi) (reg mc .rsi) = xs) {c d : Sym}
    (h2 : S'.reg .rdx = some c) (h3 : S'.reg .rcx = some d) {y z : EW}
    (hc : c.eval env = c0 y) (hd : d.eval env = c1 y) (hz : polyEval xs y = z) :
    reg m' .rax = c0 z ∧ reg m' .rdx = c1 z := by
  have h := hq.1
  rw [hs, regv hm h2 hc, regv hm h3 hd, ewArg, ew_eta, hz] at h
  unfold ewRet ewArg at h
  rw [← h]
  exact ⟨rfl, rfl⟩

end

/-! ## A step -/

variable [Host] {k : Nat}

/-- **A block and its call**, the callee changing only its stack, the invariant kept. -/
theorem cstep (hp : Placed code k) {rs : List (BitVec 64 × Nat)} (h : Lay m0 2352 NT rs)
    {ds : List Directive} {off off' : Nat} (hds : ds.IsInfixAt code off) (hne : ds ≠ [])
    (hoff : off + ds.length = off') {T T' S' : SState} {vals vals' : Nat → BitVec 64} {l : Label}
    (hrun : exec ds T = some (S', .call l))
    (hwr : S'.mem.all (writeOk 2352 ((2352 + 8) :: rs.map Prod.snd) noWr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0))
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {S : Nat} (hS : 2352 + S ≤ NT)
    {I : MachineData → Prop}
    (hP : ∀ m mc, Bnd m0 2352 NT rs noWr T vals m → I m →
      Match (envS m0 m 2352 rs vals (Host.addrOf (k + off + ds.length)).toBitVec) S' mc →
      Kept m0.dmem mc.dmem → StackOk mc S → P mc)
    (hQ : ∀ m m', Q m m' → SameOutside m.dmem m'.dmem (InRange (stackBelow m S) S) ∧ Saved m m')
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ m, Bnd m0 2352 NT rs noWr T vals m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 2352 rs vals ret) = vals' p.1)
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hres : ∀ m, Bnd m0 2352 NT rs noWr T vals m → I m → ∀ mc m',
      Match (envS m0 m 2352 rs vals (Host.addrOf (k + off + ds.length)).toBitVec) S' mc →
      Q mc m' → reg m' .rax = vals' 6 ∧ reg m' .rdx = vals' 7)
    (hI : ∀ m mc m', Bnd m0 2352 NT rs noWr T vals m → I m →
      Match (envS m0 m 2352 rs vals (Host.addrOf (k + off + ds.length)).toBitVec) S' mc →
      rspOf mc = stackBelow m0 2352 → Q mc m' → I m')
    (hsz : T'.regions = (2352 + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 2352 rs vals' ret))
    (hbd : T'.bounds = []) {st : MachineState}
    (hA : At m0 k off rs T vals I st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k off' rs T' vals' I) st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB, hId⟩ := hA
  simp only at hpc hB hId
  subst hpc
  refine callStep (hknown := hknown) h hB (hds.trans hp.1 hne) hrun hwr hsp hspec hS
    (fun mc hm hk hso ↦ hP d mc hB hId hm hk hso)
    (W := fun _ ↦ False)
    (fun m m' hq ↦ ⟨fun q hq' ↦ (hQ m m' hq).1 q fun h ↦ hq' (.inl h), (hQ m m' hq).2⟩)
    (fun _ h ↦ h.elim) hL hLW (hvals d hB)
    (fun i hi mc m' hm hq ↦ by
      rw [hrax] at hi; cases hi
      exact (hres d hB hId mc m' hm hq).1)
    (fun i hi mc m' hm hq ↦ by
      rw [hrdx] at hi; cases hi
      exact (hres d hB hId mc m' hm hq).2)
    (fun _ _ _ _ _ _ _ _ _ _ _ h ↦ h) hsz hfl hlab hal
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx)
    fun st hpc' hB' ⟨mc, hm, hsp', hq⟩ ↦ .done _ ⟨by rw [hpc', Nat.add_assoc, hoff], hB',
      hI d mc st.data hB hId hm hsp' hq⟩

end

end NativeRustcVmX64.Ring.Target
