module

public import NativeRustcVmArm.Bus.Common
public import NativeRustcVm.Layout.Forms

/-!
# More of the bus's frame lemmas

- `Fr.ofPrologueW`: a prologue that also writes an output region.
- `writeOk_two`: the writes of a two-region environment, region 1 the output.
- `Fr.rodataAt`: the read-only data at its labels in the frame, for a callee.
- `terms_ok`: a form's terms in `TERMS` as `FormBuf::add_scaled` reads them.
- `mov_reg`, `ofBlock_keep`: registers through a block.
-/

namespace NativeRustcVmArm.Bus

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring

public section

/-- **After a prologue that also writes outputs**: as `Fr.ofPrologue`, its writes in the frame or
in a region of the outputs (`WriteOk` with no slots to avoid). -/
theorem Fr.ofPrologueW [Labels] {m0 m : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState}
    (hN : N ≤ m0.regs.SP.toNat) (hFN : F ≤ N)
    (hm : Match (Env.ofMachine m0 ((base m0 F, F) :: rs) vars) S m)
    (hwf : (Env.ofMachine m0 ((base m0 F, F) :: rs) vars).WF)
    (hsp : S.sp = .ptr 0 0) (hok : slotsOk S slots = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hW : ∀ w ∈ S.mem, WriteOk (Env.ofMachine m0 ((base m0 F, F) :: rs) vars) F [] outs w)
    (hkeep : ∀ r ∈ keep, S.reg r = some (.reg r)) :
    Fr m0 F N slots keep outs m where
  sp := by rw [hm.sp, hsp]; simp [Sym.eval]
  keep r hr := UInt64.toBitVec_inj.mp (hm.regs r _ (hkeep r hr))
  slots p hp := by
    have hw := hm.bytesAt_write (r := 0) (o := p.1) (n := 8) (b := base m0 F) (sz := F) rfl
      (hsl p hp) (v := .reg p.2) fun i hi ↦ slotsOk_iff hok p hp i hi
    rw [wordBytes_reg] at hw
    exact hw
  same q hq := by
    refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq ?_
    rcases hW w hw with ⟨hr, hle, -⟩ | ⟨-, hout⟩
    · left
      rw [hr] at hb
      cases hb
      rw [Sym.inRange_iff (base_noWrap hN), base_toNat hN]
      rw [base_toNat (by omega)] at h1 h2
      omega
    · right
      obtain ⟨hle, hall⟩ := hout b sz hb
      have := Env.addr_in hwf hb (a := q) (by omega)
      rw [this]
      exact hall _ (by omega)
  kept := hm.kept hwf

/-- The writes of a block in a two-region environment, region 1 the output. -/
theorem writeOk_two {m : MachineData} {vars : Nat → BitVec 64} {F : Nat} {b0 b1 : BitVec 64}
    {n1 : Nat} (hnw : NoWrap b1 n1) {w : Write}
    (h : (w.r = 0 ∧ w.off + w.n ≤ F) ∨ (w.r = 1 ∧ w.off + w.n ≤ n1)) :
    WriteOk (Env.ofMachine m [(b0, F), (b1, n1)] vars) F [] (InRange b1 n1) w := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact .inl ⟨h0, h1, by simp⟩
  · refine .inr ⟨by omega, fun b sz hb ↦ ?_⟩
    change [(b0, F), (b1, n1)][w.r]? = some (b, sz) at hb
    rw [h0] at hb
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨h1, fun i hi ↦ NativeRustcVm.inRange_add hi (by unfold NoWrap at hnw; omega)⟩

/-- **The read-only data in the frame**, for a callee using `N'` bytes of stack: the outputs are
apart from it. -/
theorem Fr.rodataAt [Labels] {m0 m : MachineData} {F N N' : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs m)
    (hR : RodataAt m0 N) (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N)
    (hout : ∀ t : NativeRustcVm.Data.Item, ∀ i < t.bytes.length,
      ¬outs (NativeRustcVmArm.rodataAddr t + BitVec.ofNat 64 i)) :
    RodataAt m N' := fun t ↦ by
  have hnw := base_noWrap (m0 := m0) (F := N) hN
  refine ⟨(hR.bytesAt t).of_sameOutside h.same fun i hi hq ↦ hq.elim (fun hs ↦ ?_)
    (hout t i hi), hR.noWrap t, ?_⟩
  · exact (hR.apart t).not_inRange_add (hR.noWrap t) hnw hi hs
  · rw [stackBelow_eq h.sp (by omega)]
    refine (hR.apart t).mono_right ?_ ?_
    · show (base m0 N).toNat ≤ _
      rw [base_toNat hN, base_toNat (by omega)]; omega
    · show _ ≤ (base m0 N).toNat + N
      rw [base_toNat hN, base_toNat (by omega)]; omega

/-- An output apart from the read-only data is not one of its bytes. -/
theorem rodataApart_out [Labels] {a : BitVec 64} {n : Nat} {d : Mem 64} {sb : BitVec 64} {N : Nat}
    (hA : RodataApart a n)
    (hR : NativeRustcVm.RodataAt d NativeRustcVmArm.rodataAddr sb N) (ha : NoWrap a n)
    (t : NativeRustcVm.Data.Item) (i : Nat) (hi : i < t.bytes.length) :
    ¬InRange a n (NativeRustcVmArm.rodataAddr t + BitVec.ofNat 64 i) :=
  (hA t).symm.not_inRange_add (hR.noWrap t) ha hi

/-- **A form's terms in `TERMS`**: readable, apart from the stack and from what is apart from the
read-only data. -/
theorem terms_ok [Labels] {m : MachineData} {N : Nat} (hR : RodataAt m N) {a : BitVec 64}
    {n k : Nat} (hn : 0 < n) (hk : k + n ≤ NativeRustcVm.Data.terms.length)
    (ha : a = NativeRustcVmArm.rodataAddr .terms + BitVec.ofNat 64 (NativeRustcVm.Layout.termBytes * k))
    {b : BitVec 64} {nb : Nat} (hb : RodataApart b nb) :
    Readable m a (NativeRustcVm.Layout.termBytes * n) ∧
      OffStack m a (NativeRustcVm.Layout.termBytes * n) N ∧
      Apart b nb a (NativeRustcVm.Layout.termBytes * n) := by
  have hT := hR.bytesAt .terms
  have hTn := hR.noWrap .terms
  have hTa := hR.apart .terms
  have hTb := hb .terms
  have hlen : (NativeRustcVm.Data.Item.terms).bytes.length =
      NativeRustcVm.Layout.termBytes * NativeRustcVm.Data.terms.length := by
    show (NativeRustcVm.Data.terms.flatMap NativeRustcVm.Data.Term.bytes).length = _
    exact NativeRustcVm.length_flatMap_const NativeRustcVm.Layout.length_term_bytes _
  have hmap := hT.mapped
  rw [hlen] at hTn hTa hTb hmap
  have h40 : NativeRustcVm.Layout.termBytes = 40 := rfl
  rw [h40] at ha hTn hTa hTb hmap ⊢
  rw [NativeRustcVm.Layout.terms_length] at hTn hTa hTb hmap hk
  unfold NativeRustcVm.NoWrap at hTn
  have hat : a.toNat = (NativeRustcVmArm.rodataAddr .terms).toNat + 40 * k := by
    rw [ha, NativeRustcVm.toNat_add_ofNat (by omega)]
  refine ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_, ?_⟩
  · rw [ha, NativeRustcVm.addr_add_add]; exact hmap _ (by omega)
  · unfold NoWrap; rw [hat]; omega
  · unfold OffStack
    exact hTa.mono (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)
  · exact hTb.mono_right (by omega) (by omega)

/-- A register a block moved from another. -/
theorem mov_reg [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r r' : XReg} (hm : Match (Env.ofMachine m rs) S m') (h : S.reg r = some (.reg r')) :
    m'.regs.getXReg r = m.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- The kept registers through a block that leaves them alone. -/
theorem ofBlock_keep {S S' : SState} {keep : List XReg}
    (h : keep.all (fun r ↦ S.reg r == some (.reg r) && S'.reg r == some (.reg r)) = true) :
    ∀ r ∈ keep, ∃ v, S.reg r = some v ∧ S'.reg r = some v := fun r hr ↦ by
  have := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨_, this.1, this.2⟩

/-- A change nowhere is no change. -/
theorem dmem_eq_of_same {d d' : Mem 64} (h : SameOutside d d' fun _ ↦ False) : d' = d :=
  Std.ExtHashMap.ext_getElem? fun a ↦ by
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    exact h a id

theorem beq_toNat (a b : BitVec 64) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases h : a = b
  · simp [h]
  · have : a.toNat ≠ b.toNat := fun h' ↦ h (BitVec.eq_of_toNat_eq h')
    simp [h, this]

theorem ult_toNat (a b : BitVec 64) : a.ult b = decide (a.toNat < b.toNat) := rfl

/-- An `if` on a `Bool`, whatever its decidability instance, is `cond`. -/
theorem ite_bool {α : Sort _} {c : Bool} {inst : Decidable (c = true)} (a b : α) :
    @ite α (c = true) inst a b = cond c a b := by
  cases inst with
  | isTrue h => exact (Bool.cond_pos h).symm
  | isFalse h => exact (Bool.cond_neg (Bool.eq_false_iff.mpr h)).symm

/-- A conditional branch's target, by the condition's value. -/
theorem pc_of_cond [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) :
    (c.eval env = true → st.pc = Labels.label l) ∧ (c.eval env = false → st.pc = next) := by
  simp only [PcOk] at h
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩ <;> rw [h] <;> simp [hc]

/-- The registers `L` two states of one environment give the same symbolic values. -/
theorem KeepRegs.of_block' [Labels] {L : List XReg} {env : Env} {S S' : SState}
    {m m' : MachineData} (hm : Match env S m) (hm' : Match env S' m')
    (h : L.all (fun r ↦ (S.reg r).isSome && S'.reg r == S.reg r) = true) : KeepRegs L m m' :=
  fun r hr ↦ by
    have := List.all_eq_true.mp h r hr
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at this
    obtain ⟨⟨v, hv⟩, he⟩ := this
    exact Match.reg_eq hm hm' hv (he.trans hv)

theorem add_zero' (a : BitVec 64) : a + BitVec.ofNat 64 0 = a := by simp

/-- **A call writing `W`** (in the stack or the outputs, not the slots): the frame kept. -/
theorem Fr.callW [Host] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} {W : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs st.data)
    (hkeep : ∀ r ∈ keep, calleeSaved r = true) (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem W ∧ Saved st.data m')
    (hW : ∀ q, W q → InRange (base m0 N) N q ∨ outs q)
    (hsl : ∀ p ∈ slots, ∀ i < 8, ¬W (base m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i))
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (cont : ∀ m2, Fr m0 F N slots keep outs m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hq⟩ ↦ by
    simp only at hpc' hq
    rw [hpc', hpc.2]
    obtain ⟨hs, hS⟩ := hQ _ hq
    exact cont m2 (h.step hS.2.1 (fun r hr ↦ hS.1 r (hkeep r hr)) hS.2.2 hs hW hsl) hq hS.1

/-- A local of the frame is in the stack. -/
theorem inRange_local {m0 : MachineData} {F N o n : Nat} (hN : N ≤ m0.regs.SP.toNat)
    (hFN : F ≤ N) (hon : o + n ≤ F) {q : BitVec 64}
    (h : InRange (base m0 F + BitVec.ofNat 64 o) n q) : InRange (base m0 N) N q := by
  have hb := base_toNat (m0 := m0) (F := F) (by omega)
  have hlt := m0.regs.SP.toNat_lt
  have ha : (base m0 F + BitVec.ofNat 64 o).toNat = (base m0 F).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hnw : NoWrap (base m0 F + BitVec.ofNat 64 o) n := by unfold NoWrap; rw [ha]; omega
  rw [Sym.inRange_iff hnw, ha] at h
  rw [Sym.inRange_iff (base_noWrap hN), base_toNat hN]
  omega

/-- A callee's stack below the frame is in the stack. -/
theorem inRange_callee {m0 m : MachineData} {F N N' : Nat} (hN : N ≤ m0.regs.SP.toNat)
    (hsp : m.regs.SP.toBitVec = base m0 F) (hle : F + N' ≤ N) {q : BitVec 64}
    (h : InRange (stackBelow m N') N' q) : InRange (base m0 N) N q := by
  rw [stackBelow_eq hsp (by omega)] at h
  have hnw : NoWrap (base m0 (F + N')) N' := by
    unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
  rw [Sym.inRange_iff hnw, base_toNat (by omega)] at h
  rw [Sym.inRange_iff (base_noWrap hN), base_toNat hN]
  omega

/-- A slot of the frame is not in a callee's stack. -/
theorem slot_not_callee {m0 m : MachineData} {F N' p i : Nat}
    (hN : F + N' ≤ m0.regs.SP.toNat) (hsp : m.regs.SP.toBitVec = base m0 F) (hp : p + i < F) :
    ¬InRange (stackBelow m N') N' (base m0 F + BitVec.ofNat 64 p + BitVec.ofNat 64 i) := by
  rw [stackBelow_eq hsp hN, NativeRustcVm.addr_add_add]
  have hnw : NoWrap (base m0 (F + N')) N' := by
    unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
  have hb := base_toNat (m0 := m0) (F := F) (by omega)
  have hlt := m0.regs.SP.toNat_lt
  rw [Sym.inRange_iff hnw, base_toNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- A slot of the frame is not in a local before it. -/
theorem slot_not_local {m0 : MachineData} {F o n p i : Nat} (hF : F ≤ m0.regs.SP.toNat)
    (hp : o + n ≤ p) (hpi : p + i < F) :
    ¬InRange (base m0 F + BitVec.ofNat 64 o) n (base m0 F + BitVec.ofNat 64 p + BitVec.ofNat 64 i) := by
  have hb := base_toNat (m0 := m0) (F := F) hF
  have hlt := m0.regs.SP.toNat_lt
  have ha : (base m0 F + BitVec.ofNat 64 o).toNat = (base m0 F).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hnw : NoWrap (base m0 F + BitVec.ofNat 64 o) n := by unfold NoWrap; rw [ha]; omega
  rw [NativeRustcVm.addr_add_add, Sym.inRange_iff hnw, ha, NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- **A word of a slot store**: slot `k` (at `o + s k` of region `r`) is the stored value where the
index is `k`, else the old word. -/
theorem slot_word [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz)
    {x V : Sym} {k : Nat}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem =
      some (.ite (.cmp .eq .W64 x (.lit k)) V (.load r o 8), i)) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o)
      (if x.eval env = BitVec.ofNat 64 k then UInt64.ofBitVec (V.eval env)
        else UInt64.ofBitVec (env.load r o 8)) := by
  have h := Bus.wordAt_write hm hb hle hw
  simp only [Sym.eval, SBool.eval, CmpOp.apply, Sym.low_W64] at h
  by_cases hx : x.eval env = BitVec.ofNat 64 k
  · simp only [hx, beq_self_eq_true, ↓reduceIte] at h ⊢
    exact h
  · have : (x.eval env == BitVec.ofNat 64 k) = false := by simpa using hx
    simp only [this, hx, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact h

/-- A two-region environment of mapped, apart regions is well formed. -/
theorem wf_two {m : MachineData} {a1 a2 : BitVec 64} {n1 n2 : Nat}
    (hm1 : NativeRustcVm.Mapped m.dmem a1 n1) (hn1 : NoWrap a1 n1)
    (hm2 : NativeRustcVm.Mapped m.dmem a2 n2) (hn2 : NoWrap a2 n2) (hap : Apart a1 n1 a2 n2)
    (vars : Nat → BitVec 64 := fun _ ↦ 0) :
    (Env.ofMachine m [(a1, n1), (a2, n2)] vars).WF :=
  Env.wf_of ⟨⟨hm1, hn1⟩, ⟨hm2, hn2⟩, trivial⟩
    (List.Pairwise.cons (by simp only [List.mem_singleton, forall_eq]; exact hap)
      (List.pairwise_singleton _ _))

/-- A block whose writes are in `[lo, hi)` of region `r` changes nothing else. -/
theorem same_of_writes_in [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz lo hi : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hnw : b.toNat + sz ≤ 2 ^ 64) (hlh : lo < hi)
    (hhi : hi ≤ sz)
    (h : (S.mem.all fun w ↦ w.r == r && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) = true) :
    SameOutside env.mem0 m.dmem (InRange (b + BitVec.ofNat 64 lo) (hi - lo)) := by
  intro q hq
  refine hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ hq ?_
  have := List.all_eq_true.mp h w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨⟨hr, hlo⟩, hhi'⟩ := this
  rw [hr, hb] at hb'
  cases hb'
  have hlb : (b + BitVec.ofNat 64 lo).toNat = b.toNat + lo :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [hlb]; omega), hlb]
  omega

/-- The writes of a block in a two-region environment: in the frame avoiding the slots, or in
region 1, inside the outputs. -/
theorem writeOk_two' {m : MachineData} {vars : Nat → BitVec 64} {F : Nat}
    {slots : List (Nat × XReg)} {outs : BitVec 64 → Prop} {b0 b1 : BitVec 64} {n1 : Nat}
    (hout : ∀ i < n1, outs (b1 + BitVec.ofNat 64 i)) {w : Write}
    (h : (w.r = 0 ∧ w.off + w.n ≤ F ∧ ∀ p ∈ slots, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off) ∨
      (w.r = 1 ∧ w.off + w.n ≤ n1)) :
    WriteOk (Env.ofMachine m [(b0, F), (b1, n1)] vars) F slots outs w := by
  rcases h with h | ⟨h0, h1⟩
  · exact .inl h
  · refine .inr ⟨by omega, fun b sz hb ↦ ?_⟩
    change [(b0, F), (b1, n1)][w.r]? = some (b, sz) at hb
    rw [h0] at hb
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨h1, hout⟩

/-- A word outside the bytes a change touched is kept. -/
theorem wordAt_keep_out {d d' : Mem 64} {b : BitVec 64} {sz lo hi o : Nat} {w : UInt64}
    (hnw : b.toNat + sz ≤ 2 ^ 64) (hs : SameOutside d d' (InRange (b + BitVec.ofNat 64 lo) (hi - lo)))
    (hlh : lo < hi) (hhi : hi ≤ sz) (ho : o + 8 ≤ sz) (hd : o + 8 ≤ lo ∨ hi ≤ o)
    (h : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) w) :
    NativeRustcVm.WordAt d' (b + BitVec.ofNat 64 o) w :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi' hin ↦ by
    rw [NativeRustcVm.length_wordBytes] at hi'
    have hlb : (b + BitVec.ofNat 64 lo).toNat = b.toNat + lo :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    rw [NativeRustcVm.addr_add_add, Sym.inRange_iff (by rw [hlb]; omega), hlb,
      NativeRustcVm.toNat_add_ofNat (by omega)] at hin
    omega

/-- A word moved: where `d'` at `b` holds what `d` holds at `a`, for `n` bytes. -/
theorem wordAt_transfer {d d' : Mem 64} {a b : BitVec 64} {n o : Nat} {w : UInt64}
    (htr : ∀ i < n, ∀ x, d.get? (a + BitVec.ofNat 64 i) = some x →
      d'.get? (b + BitVec.ofNat 64 i) = some x)
    (ho : o + 8 ≤ n) (h : NativeRustcVm.WordAt d (a + BitVec.ofNat 64 o) w) :
    NativeRustcVm.WordAt d' (b + BitVec.ofNat 64 o) w := fun i hi ↦ by
  rw [NativeRustcVm.length_wordBytes] at hi
  rw [NativeRustcVm.addr_add_add]
  exact htr (o + i) (by omega) _ (by rw [← NativeRustcVm.addr_add_add]; exact h i (by
    rw [NativeRustcVm.length_wordBytes]; exact hi))

section
variable [Labels] (m : MachineData) (rs : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64)

theorem eval_eq_lit (r : XReg) {n : Nat} (hn : n < 2 ^ 64) :
    (SBool.cmp .eq .W64 (.reg r) (.lit n)).eval (Env.ofMachine m rs vars) =
      decide ((m.regs.getXReg r).toNat = n) := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64, Env.ofMachine_regs, beq_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, UInt64.toNat_toBitVec]

theorem eval_ult_lit (r : XReg) {n : Nat} (hn : n < 2 ^ 64) :
    (SBool.cmp .ult .W64 (.reg r) (.lit n)).eval (Env.ofMachine m rs vars) =
      decide ((m.regs.getXReg r).toNat < n) := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64, Env.ofMachine_regs, ult_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, UInt64.toNat_toBitVec]

theorem eval_eq_reg (r r' : XReg) :
    (SBool.cmp .eq .W64 (.reg r) (.reg r')).eval (Env.ofMachine m rs vars) =
      decide ((m.regs.getXReg r).toNat = (m.regs.getXReg r').toNat) := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64, Env.ofMachine_regs, beq_toNat,
    UInt64.toNat_toBitVec]

theorem eval_ult_reg (r r' : XReg) :
    (SBool.cmp .ult .W64 (.reg r) (.reg r')).eval (Env.ofMachine m rs vars) =
      decide ((m.regs.getXReg r).toNat < (m.regs.getXReg r').toNat) := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64, Env.ofMachine_regs, ult_toNat,
    UInt64.toNat_toBitVec]

end

theorem toNat_take'' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `lsl #3` as rustc writes it (`ubfm #61, #60`). -/
theorem lsl3 (x : BitVec 64) : (UnOp.apply (.ubfm 61 60) .W64 x).toNat = 8 * x.toNat % 2 ^ 64 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  simp [evalUBFM, toNat_take'', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- A shift left by `k`. -/
theorem shl_toNat (x : BitVec 64) (k : Nat) :
    (UnOp.apply (.shift .LSL k) .W64 x).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  simp [UnOp.apply, Sym.ext_W64, Sym.low_W64, shiftW, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem memExt3 (v : BitVec 64) :
    (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 v).toNat = v.toNat * 8 % 2 ^ 64 := by
  simp only [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned, BitVec.toNat_ofInt,
    Int.shiftLeft_eq]
  omega

end

end NativeRustcVmArm.Bus
