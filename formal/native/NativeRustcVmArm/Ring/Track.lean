module

public import NativeRustcVmArm.Ring.Frame

/-!
# Tracking values through straight-line code

A state description `D : List (Sym × Nat)`: each location `s` (a register, a word of a region, a
literal) holds the value `V n` of a table `V : Nat → UInt64` (`Holds rs V D m`, the locations
evaluated in the environment of `m` with the regions `rs`). After a block from `m` (a `Match` in
that environment), a location's content is a symbolic value of the block's start (`content`, by
the literal result); where that is a location `D` describes with index `n`, the location holds
`V n` (`trackOk`, `Holds.after`). A call keeps the callee-saved registers and the regions'
words (`callSafe`, `Holds.call`); `trackStep` runs a block ending in a call within a frame
(`Fr`), checked by `decide`.
-/

namespace NativeRustcVmArm.Ring

open NativeRustcArm NativeRustcArm.Sym

@[expose] public section

/-- A location's content after a block, as a symbolic value of the block's start: a register's,
a literal, a word of region `r` (of size `sz.getD r 0`) no write touched or one write stored. -/
def content (sz : List Nat) (S : SState) : Sym → Option Sym
  | .reg r => S.reg r
  | .lit c => some (.lit c)
  | .load r off 8 =>
    if off + 8 ≤ sz.getD r 0 then
      if (List.range 8).all (fun i ↦ findWrite r (off + i) S.mem == none) then some (.load r off 8)
      else match findWrite r off S.mem with
        | some (v, _) =>
          if (List.range 8).all (fun i ↦ findWrite r (off + i) S.mem == some (v, i)) then some v
          else none
        | none => none
    else none
  | _ => none

/-- Every location of `D'` holds, after the block, a location `D` describes with its index. -/
def trackOk (sz : List Nat) (S : SState) (D D' : List (Sym × Nat)) : Bool :=
  D'.all fun p ↦ match content sz S p.1 with
    | some c => D.contains (c, p.2)
    | none => false

/-- A location a call keeps: a callee-saved register, a literal, a word of a region. -/
def callSafe (sz : List Nat) : Sym → Bool
  | .reg r => calleeSaved r
  | .lit _ => true
  | .load r off 8 => decide (off + 8 ≤ sz.getD r 0)
  | _ => false

section
variable [Labels]

/-- A location's value in `m`, the regions `rs`. -/
def tval (rs : List (BitVec 64 × Nat)) (m : MachineData) (s : Sym) : UInt64 :=
  UInt64.ofBitVec (s.eval (Env.ofMachine m rs))

/-- **The description holds**: each location of `D` holds its value. -/
def Holds (rs : List (BitVec 64 × Nat)) (V : Nat → UInt64) (D : List (Sym × Nat))
    (m : MachineData) : Prop :=
  ∀ p ∈ D, tval rs m p.1 = V p.2

end

end

public section

theorem getD_sz {rs : List (BitVec 64 × Nat)} {sz : List Nat} (hsz : rs.map Prod.snd = sz)
    {r n : Nat} (h : n ≤ sz.getD r 0) (hn : 0 < n) :
    ∃ b, rs[r]? = some (b, sz.getD r 0) := by
  subst hsz
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at h ⊢
  cases hr : rs[r]? with
  | none => rw [hr] at h; simp at h; omega
  | some e => exact ⟨e.1, by simp⟩

theorem Holds.mono [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64}
    {D D' : List (Sym × Nat)} {m : MachineData} (h : Holds rs V D m) (hs : ∀ p ∈ D', p ∈ D) :
    Holds rs V D' m := fun p hp ↦ h p (hs p hp)

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {sz : List Nat}

/-- **A location's value after a block** is its content's at the block's start. -/
theorem content_eval (hsz : rs.map Prod.snd = sz) {m m' : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m rs) S m') {s c : Sym} (h : content sz S s = some c) :
    tval rs m' s = UInt64.ofBitVec (c.eval (Env.ofMachine m rs)) := by
  unfold tval
  congr 1
  match s, h with
  | .reg r, h => exact hm.regs r c h
  | .lit _, h => simp only [content, Option.some.injEq] at h; subst h; rfl
  | .load r off 8, h =>
    simp only [content] at h
    split at h
    case isFalse => cases h
    case isTrue hle =>
    obtain ⟨b, hb⟩ := getD_sz hsz hle (by omega)
    have hbm : (Env.ofMachine m rs).regions[r]? = some (b, sz.getD r 0) := hb
    have hbm' : (Env.ofMachine m' rs).base r = b := Env.base_ofMachine m' rs _ hb
    split at h
    case isTrue hall =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hall
      simp only [Sym.eval, Env.load]
      rw [hbm', Env.base_ofMachine m rs _ hb]
      congr 2
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [show (Env.ofMachine m' rs).mem0 = m'.dmem from rfl, hm.mem r b _ hbm (off + i) (by omega)]
      unfold memByte
      rw [hall i hi]
    case isFalse =>
      split at h
      case h_2 => cases h
      case h_1 v t _ =>
      split at h
      case isFalse => cases h
      case isTrue hall =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hall
      simp only [Sym.eval, Env.load]
      rw [hbm']
      have hbytes : ((List.range 8).map fun i ↦
          ((Env.ofMachine m' rs).mem0.get? (b + BitVec.ofNat 64 (off + i))).getD 0) =
          (List.range 8).map fun i ↦ byteOf (v.eval (Env.ofMachine m rs)) (0 + i) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [show (Env.ofMachine m' rs).mem0 = m'.dmem from rfl,
          hm.mem r b _ hbm (off + i) (by omega)]
        unfold memByte
        rw [hall i hi, Nat.zero_add]
        rfl
      rw [hbytes, ofBytes_byteOf, BitVec.ofInt_natCast]
      apply BitVec.eq_of_toNat_eq
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
      have := (v.eval (Env.ofMachine m rs)).isLt
      omega

/-- **The description after a block.** -/
theorem Holds.after (hsz : rs.map Prod.snd = sz) {V : Nat → UInt64} {D D' : List (Sym × Nat)}
    {m m' : MachineData} {S : SState} (h : Holds rs V D m)
    (hm : Match (Env.ofMachine m rs) S m') (ht : trackOk sz S D D' = true) : Holds rs V D' m' := by
  intro p hp
  simp only [trackOk, List.all_eq_true] at ht
  have := ht p hp
  split at this
  case h_2 => cases this
  case h_1 c hc =>
  rw [content_eval hsz hm hc]
  exact h (c, p.2) (List.contains_iff_mem.mp this)

/-- **The description across a call** that keeps the callee-saved registers and the regions'
bytes. -/
theorem Holds.call (hsz : rs.map Prod.snd = sz) {V : Nat → UInt64} {D : List (Sym × Nat)}
    {m m2 : MachineData} (h : Holds rs V D m) (hsafe : D.all (fun p ↦ callSafe sz p.1) = true)
    (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = m.regs.getXReg r)
    (hmem : ∀ (r : Nat) (b : BitVec 64) (n : Nat), rs[r]? = some (b, n) → ∀ i < n,
      m2.dmem.get? (b + BitVec.ofNat 64 i) = m.dmem.get? (b + BitVec.ofNat 64 i)) :
    Holds rs V D m2 := by
  intro p hp
  rw [← h p hp]
  simp only [List.all_eq_true] at hsafe
  have hs := hsafe p hp
  unfold tval
  congr 1
  match p.1, hs with
  | .reg r, hs =>
    simp only [callSafe] at hs
    show (m2.regs.getXReg r).toBitVec = (m.regs.getXReg r).toBitVec
    rw [hcs r hs]
  | .lit _, _ => rfl
  | .load r off 8, hs =>
    simp only [callSafe, decide_eq_true_eq] at hs
    obtain ⟨b, hb⟩ := getD_sz hsz hs (by omega)
    simp only [Sym.eval, Env.load]
    rw [Env.base_ofMachine m2 rs _ hb, Env.base_ofMachine m rs _ hb]
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    show (m2.dmem.get? _).getD 0 = (m.dmem.get? _).getD 0
    rw [hmem r b _ hb (off + i) (by omega)]

end

variable [Host] {rs : List (BitVec 64 × Nat)} {sz : List Nat}

/-- **A block ending in a call**, within a frame: the description `D'` after the call. The
callee changes only its `N'` bytes of stack below the frame; the regions other than the frame
(region 0) are apart from the whole stack. -/
theorem trackStep {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
    {outs : BitVec 64 → Prop} (hsz : rs.map Prod.snd = sz) {V : Nat → UInt64}
    {D D' : List (Sym × Nat)} {S0 S' : SState} {ds : List Directive} {i : Nat} {l : Label}
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop} {N' : Nat}
    {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S0 = some (S', .call l))
    (hfr : Fr m0 F N slots keep outs m) (hm : Match (Env.ofMachine m rs) S0 m)
    (hwf : (Env.ofMachine m rs).WF) (h0 : rs[0]? = some (base m0 F, F)) (hFN : F ≤ N)
    (hN : N ≤ m0.regs.SP.toNat) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hsp : S'.sp = S0.sp)
    (hkeep : ∀ r ∈ keep, (∃ v, S0.reg r = some v ∧ S'.reg r = some v) ∧ calleeSaved r = true)
    (hW : ∀ w ∈ S'.mem, WriteOk (Env.ofMachine m rs) F slots outs w)
    (hfro : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hap : ∀ (r : Nat) (b : BitVec 64) (n : Nat), rs[r]? = some (b, n) → r ≠ 0 →
      Apart b n (stackBelow m0 N) N)
    (hH : Holds rs V D m) (htr : trackOk sz S' D D' = true)
    (hsafe : D'.all (fun p ↦ callSafe sz p.1) = true) (hle : F + N' ≤ N)
    (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ a b, Q a b → SameOutside a.dmem b.dmem
      (fun q ↦ InRange (stackBelow a N') N' q ∨ False) ∧ Saved a b)
    (hP : ∀ st : MachineData, Match (Env.ofMachine m rs) S' st →
      Fr m0 F N slots keep outs st → P st)
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m rs) S' st → Q st m2 →
      Fr m0 F N slots keep outs m2 → Holds rs V D' m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : Fr m0 F N slots keep outs st.data :=
    hfr.ofBlockW hm hm1 hwf rfl hsp (fun r hr ↦ (hkeep r hr).1) h0 hFN hN hsl hW
  have hH1 : Holds rs V D' st.data := hH.after hsz hm1 htr
  refine Fr.leaf hfr1 hN hle (fun r hr ↦ (hkeep r hr).2) hsl hfro hspec
    (fun a b hq ↦ ⟨NativeRustcVm.SameOutside.mono (hQ a b hq).1 fun q h ↦ h.elim .inl
      False.elim, (hQ a b hq).2⟩) hpc (hP st.data hm1 hfr1) fun m2 hfr2 hq hcs ↦
    cont st.data m2 hm1 hq hfr2 ?_
  have hs := (hQ _ _ hq).1
  refine hH1.call hsz hsafe hcs fun r b n hb j hj ↦ hs _ ?_
  have hsb := stackBelow_eq hfr1.sp (N' := N') (by omega)
  have hb' := base_toNat (m0 := m0) (F := F + N') (by omega)
  have hnw : NoWrap (base m0 (F + N')) N' := by
    unfold NoWrap; rw [hb']; have := m0.regs.SP.toNat_lt; omega
  have hnwr : NoWrap b n := hwf.noWrap r b n hb
  rintro (hq' | hq')
  · rw [hsb, inRange_iff hnw, hb', NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnwr; omega)] at hq'
    by_cases hr0 : r = 0
    · subst hr0
      rw [h0] at hb
      cases hb
      rw [base_toNat (by omega)] at hq'
      omega
    · have := hap r b n hb hr0
      have hsN : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
      unfold Apart at this
      omega
  · exact hq'

end

end NativeRustcVmArm.Ring
