module

public import NativeRustcVmX64.Whir.LanesOf.Exec
public import NativeRustcVmX64.Whir.MathFrame

/-!
# `lanes_of`'s states (x86-64)

The row's words at the entry (`rowW`), the lanes the model asks for (`revL` at level `0`, `pairL`
later; `lanes_rev`, `lanes_pair`), the lanes written so far (`Lanes`), what every state of the body
keeps (`Body`: the frame with RBX in its slot, `Transcript.Frame`; memory changed only in the lanes
and that slot), and the steps every path takes: a block from the entry's environment (`chain_fr`,
`chain_same`), a block writing lanes (`same_lanes`), the return (`done`).
-/

namespace NativeRustcVmX64.Whir.LanesOf

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.LanesOf
open NativeRustcVm (Region wordOf ewOf)
open NativeRustcVmX64.Transcript (frameEnv)

@[expose] public section

/-- The row. -/
abbrev rowOf (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The lanes. -/
abbrev outOf (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The row's word count. -/
abbrev lenOf (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The pairs' count. -/
abbrev nOf (m0 : MachineData) : Nat := lenOf m0 / 2
/-- The row's word `i` at the entry. -/
def rowW (m0 : MachineData) (i : Nat) : UInt64 :=
  wordOf m0.dmem (rowOf m0 + BitVec.ofNat 64 (8 * i))
/-- Level `0`'s lane `j`: the row's words reversed. -/
def revL (m0 : MachineData) (j : Nat) : EW := EW.ofK (rowW m0 (lenOf m0 - 1 - j))
/-- A later level's lane `j`: the row's pair `j`. -/
def pairL (m0 : MachineData) (j : Nat) : EW := ⟨rowW m0 (2 * j), rowW m0 (2 * j + 1)⟩
/-- The model's lanes. -/
def lanesM (m0 : MachineData) : Array EW :=
  lanesOf (reg m0 .rdi).toNat (wordSlice m0 (rowOf m0) (lenOf m0))
/-- The output. -/
def outs (m0 : MachineData) : List Region := [⟨outOf m0, lanesBytes⟩]

/-- The lanes `f` below `c` written. -/
def Lanes (m0 : MachineData) (f : Nat → EW) (c : Nat) (st : MachineData) : Prop :=
  ∀ j < c, NativeRustcVm.EWAt st.dmem (outOf m0 + BitVec.ofNat 64 (16 * j)) (f j)

/-- **A state of the body**: the frame, RBX in its slot and RSP there; memory changed only in the
lanes and the slot; the lanes `f` below `c` written. -/
structure Body (m0 : MachineData) (f : Nat → EW) (c : Nat) (st : MachineData) : Prop where
  fr : Transcript.Frame m0 8 slots 0 st
  same : ChangesIn m0 st lanesOfStack (outs m0)
  lanes : Lanes m0 f c st

/-- `lanes_of`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ LanesOfPost m0 st.data

end

public section

theorem lanesBytes_eq : lanesBytes = 1024 := rfl
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 8 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide


/-! ## The model -/

/-- **Level `0`'s lanes**: the row reversed. -/
theorem lanes_rev {m0 : MachineData} (h0 : (reg m0 .rdi).toNat = 0) :
    (lanesM m0).size = lenOf m0 ∧
      ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = revL m0 j := by
  have hs : (lanesM m0).size = lenOf m0 := by
    simp [lanesM, lanesOf, h0, wordSlice]
  refine ⟨hs, fun j h ↦ ?_⟩
  rw [hs] at h
  simp [lanesM, lanesOf, h0, wordSlice, revL, rowW, NativeRustcVm.wordsOf]

/-- **A later level's lanes**: the row's pairs. -/
theorem lanes_pair {m0 : MachineData} (h0 : (reg m0 .rdi).toNat ≠ 0) :
    (lanesM m0).size = nOf m0 ∧
      ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = pairL m0 j := by
  have hs : (lanesM m0).size = nOf m0 := by
    simp [lanesM, lanesOf, h0, wordSlice, extRow, nOf]
  refine ⟨hs, fun j h ↦ ?_⟩
  rw [hs] at h
  have h1 : 2 * j + 1 < lenOf m0 := by unfold nOf at h; omega
  simp [lanesM, lanesOf, h0, wordSlice, extRow, pairL, rowW, NativeRustcVm.wordsOf,
    Array.getD_eq_getD_getElem?, h1, show 2 * j < lenOf m0 by omega]

/-! ## Memory -/

section
variable {m0 st st' : MachineData}

theorem pre_stack (hpre : LanesOfPre m0) : StackOk m0 8 := hpre.1

/-- The row and the lanes: readable, apart from the stack and from each other. -/
theorem pre_row (hpre : LanesOfPre m0) : WhirIn m0 (rowOf m0) (8 * lenOf m0) 8 := hpre.2.1
theorem pre_out (hpre : LanesOfPre m0) : WhirIn m0 (outOf m0) 1024 8 := hpre.2.2.1
theorem pre_apart (hpre : LanesOfPre m0) : Apart (outOf m0) 1024 (rowOf m0) (8 * lenOf m0) :=
  hpre.2.2.2

/-- **The row's words** in a body: apart from the lanes and the stack. -/
theorem row_word (hpre : LanesOfPre m0) (hc : ChangesIn m0 st lanesOfStack (outs m0)) {i : Nat}
    (hi : i < lenOf m0) : wordOf st.dmem (rowOf m0 + BitVec.ofNat 64 (8 * i)) = rowW m0 i := by
  have hr := pre_row hpre
  have ho := pre_out hpre
  refine NativeRustcVm.wordOf_congr fun b hb ↦ ?_
  rw [addr_add]
  refine hc _ fun h ↦ h.elim (fun ⟨r, hr', hp⟩ ↦ ?_) (fun h ↦ ?_)
  · simp only [outs, List.mem_singleton] at hr'
    subst hr'
    exact Arrays.not_inRange_of_apart (Arrays.apart_symm (pre_apart hpre)) hr.1.2 ho.1.2
      (by omega) hp
  · exact Arrays.not_inRange_of_apart (Arrays.apart_mono hr.2 (by decide : 8 ≤ 8 + 8)) hr.1.2
      (NativeRustcVm.NoWrap.mono (stack_noWrap (pre_stack hpre)) (by omega)) (by omega) h

theorem Lanes.of_dmem {f : Nat → EW} {c : Nat} (h : Lanes m0 f c st) (hd : st'.dmem = st.dmem) :
    Lanes m0 f c st' := by
  unfold Lanes; rw [hd]; exact h

theorem lanes_zero (f : Nat → EW) : Lanes m0 f 0 st := fun _ h ↦ absurd h (by omega)

/-- **Lanes written** from `c`, `w` of them: the earlier ones kept. -/
theorem Lanes.extend {f : Nat → EW} {c w : Nat} (h : Lanes m0 f c st)
    (hnw : NativeRustcVm.NoWrap (outOf m0) 1024) (hcw : c + w ≤ 64)
    (hs : SameOutside st.dmem st'.dmem (InRange (outOf m0 + BitVec.ofNat 64 (16 * c)) (16 * w)))
    (hn : ∀ t < w,
      NativeRustcVm.EWAt st'.dmem (outOf m0 + BitVec.ofNat 64 (16 * (c + t))) (f (c + t))) :
    Lanes m0 f (c + w) st' := by
  intro j hj
  by_cases hjc : j < c
  · intro b hb
    have hb16 : b < 16 := by rwa [NativeRustcVm.length_ewBytes] at hb
    rw [hs _ fun hin ↦ ?_]
    · exact h j hjc b hb
    · unfold NativeRustcVm.NoWrap at hnw
      rw [addr_add, Sym.inRange_iff (NativeRustcVm.NoWrap.sub hnw (by omega)),
        toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hin
      omega
  · have := hn (j - c) (by omega)
    rwa [show c + (j - c) = j by omega] at this

/-- **A lane a block wrote**: its two words, at offsets `o` and `o + 8` of region `r`. -/
theorem ewAt_write [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 16 ≤ sz) {v0 v1 : Sym}
    (hw0 : ∀ i < 8, findWrite r (o + i) S.mem = some (v0, i))
    (hw1 : ∀ i < 8, findWrite r (o + 8 + i) S.mem = some (v1, i)) :
    NativeRustcVm.EWAt m.dmem (b + BitVec.ofNat 64 o)
      ⟨UInt64.ofBitVec (v0.eval env), UInt64.ofBitVec (v1.eval env)⟩ := by
  rw [NativeRustcVm.ewAt_iff]
  refine ⟨Transcript.wordAt_write hm hb (by omega) hw0, ?_⟩
  rw [addr_add]
  exact Transcript.wordAt_write hm hb (by omega) hw1

/-- A row word an environment loads: region `r` the row from word `o`. -/
theorem load_row (hpre : LanesOfPre m0) (hc : ChangesIn m0 st lanesOfStack (outs m0)) {env : Env}
    (hd : env.mem0 = st.dmem) {r o t : Nat} (hb : env.base r = rowOf m0 + BitVec.ofNat 64 (8 * o))
    (ht : o + t < lenOf m0) :
    UInt64.ofBitVec (env.load r (8 * t) 8) = rowW m0 (o + t) := by
  rw [Arrays.load8_eq, hd, hb, addr_add, show 8 * o + 8 * t = 8 * (o + t) by omega,
    row_word hpre hc ht]

/-! ## Environments -/

/-- The frame's region: mapped, not wrapping. -/
theorem frame_ok8 (hpre : LanesOfPre m0) (hk : Kept m0.dmem st.dmem) :
    NativeRustcVm.Mapped st.dmem (stackBelow m0 8) (8 + 8) ∧
      NativeRustcVm.NoWrap (stackBelow m0 8) (8 + 8) :=
  ⟨fun i hi ↦ hk _ ((pre_stack hpre).2.2 i hi), Transcript.frame_noWrap (pre_stack hpre) le_rfl⟩

/-- **A loop turn's environment**: the frame, `n` bytes of the row from byte `o`, `n'` bytes of
the lanes from byte `c`. -/
theorem wf3 (hpre : LanesOfPre m0) (hk : Kept m0.dmem st.dmem) {o n c n' : Nat}
    (hrow : o + n ≤ 8 * lenOf m0) (hout : c + n' ≤ 1024) (hn : 0 < n) (hn' : 0 < n')
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 st 8 [(rowOf m0 + BitVec.ofNat 64 o, n), (outOf m0 + BitVec.ofNat 64 c, n')]
      vars ret).WF := by
  have hr := pre_row hpre
  have ho := pre_out hpre
  have hap := pre_apart hpre
  have hS := pre_stack hpre
  have hr' := Readable.keep (Readable.sub hr.1 hrow) hk
  have ho' := Readable.keep (Readable.sub ho.1 hout) hk
  have h1 : (rowOf m0).toNat + 8 * lenOf m0 ≤ 2 ^ 64 := hr.1.2
  have h2 : (outOf m0).toNat + 1024 ≤ 2 ^ 64 := ho.1.2
  have hrs : Apart (rowOf m0) (8 * lenOf m0) (stackBelow m0 8) (8 + 8) := hr.2
  have hos : Apart (outOf m0) 1024 (stackBelow m0 8) (8 + 8) := ho.2
  unfold Apart at hap hrs hos
  have e1 : (rowOf m0 + BitVec.ofNat 64 o).toNat = (rowOf m0).toNat + o :=
    toNat_add_ofNat _ _ (by omega)
  have e2 : (outOf m0 + BitVec.ofNat 64 c).toNat = (outOf m0).toNat + c :=
    toNat_add_ofNat _ _ (by omega)
  refine Transcript.frame_wf (frame_ok8 hpre hk) (Transcript.rest2_ok ⟨hr'.1, hr'.2⟩ ⟨ho'.1, ho'.2⟩
    fun _ h ↦ h) (Transcript.pairwise3 ?_ ?_ ?_)
  · show NativeRustcVm.Apart (stackBelow m0 8) (8 + 8) (rowOf m0 + BitVec.ofNat 64 o) n
    unfold NativeRustcVm.Apart; rw [e1]; omega
  · show NativeRustcVm.Apart (stackBelow m0 8) (8 + 8) (outOf m0 + BitVec.ofNat 64 c) n'
    unfold NativeRustcVm.Apart; rw [e2]; omega
  · show NativeRustcVm.Apart (rowOf m0 + BitVec.ofNat 64 o) n (outOf m0 + BitVec.ofNat 64 c) n'
    unfold NativeRustcVm.Apart; rw [e1, e2]; omega

/-- The frame's environment alone. -/
theorem wf1 (hpre : LanesOfPre m0) (hk : Kept m0.dmem st.dmem) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : (frameEnv m0 st 8 [] vars ret).WF :=
  Transcript.frame_wf (frame_ok8 hpre hk) (fun _ h ↦ absurd h List.not_mem_nil)
    (List.pairwise_singleton _ _)

/-! ## Changes -/

/-- **A block writing only RBX's slot** (region 0 below `8`), from the entry. -/
theorem chain_same [Labels] {S : SState} (hpre : LanesOfPre m0)
    (hm : Match (frameEnv m0 m0 8 []) S st) (hw : writesBelow S 0 8 = true) :
    ChangesIn m0 st lanesOfStack (outs m0) := by
  have hwf := wf1 (st := m0) (vars := fun _ ↦ 0) (ret := 0) hpre fun _ h ↦ h
  have hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by
    intro w hw'
    simp only [writesBelow, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hw
    exact hw w hw'
  have := Transcript.sameOutside_low hwf hm (r := 0) rfl (by omega) hS
  exact fun p hp ↦ this p fun h ↦ hp (.inr h)

/-- **A block writing only lanes**: region `2` from byte `c` of the lanes, below `len`. -/
theorem same_lanes [Labels] {S : SState} {rest0 : BitVec 64 × Nat} {c n' len : Nat}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hpre : LanesOfPre m0)
    (hc : ChangesIn m0 st lanesOfStack (outs m0))
    (hwf : (frameEnv m0 st 8 [rest0, (outOf m0 + BitVec.ofNat 64 c, n')] vars ret).WF)
    (hm : Match (frameEnv m0 st 8 [rest0, (outOf m0 + BitVec.ofNat 64 c, n')] vars ret) S st')
    (hw : writesBelow S 2 len = true) (hlen : len ≤ n') (hcl : c + len ≤ 1024) :
    ChangesIn m0 st' lanesOfStack (outs m0) ∧
      SameOutside st.dmem st'.dmem (InRange (outOf m0 + BitVec.ofNat 64 c) len) := by
  have hS : ∀ w ∈ S.mem, w.r = 2 ∧ w.off + w.n ≤ len := by
    intro w hw'
    simp only [writesBelow, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hw
    exact hw w hw'
  have hso := Transcript.sameOutside_low hwf hm (r := 2) rfl hlen hS
  refine ⟨fun p hp ↦ ?_, hso⟩
  rw [hso p fun h ↦ hp (.inl ⟨_, List.mem_singleton_self _, ?_⟩)]
  · exact hc p hp
  · exact NativeRustcVm.InRange.of_sub h (pre_out hpre).1.2 (by rw [lanesBytes_eq]; omega)

end

/-! ## The end -/

section
variable {m0 st : MachineData}

/-- **The postcondition with lanes**: the model's `n ≤ 64` lanes written, RAX `1`, RDX `n`. -/
theorem post_some {f : Nat → EW} {n : Nat} (hc : ChangesIn m0 st lanesOfStack (outs m0))
    (hs : Saved m0 st) (hl : Lanes m0 f n st) (hsz : (lanesM m0).size = n)
    (hf : ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = f j) (hn : n ≤ 64)
    (hax : reg st .rax = 1#64) (hdx : (reg st .rdx).toNat = n) : LanesOfPost m0 st := by
  refine ⟨?_, hc, hs⟩
  have hc : (lanesM m0).size ≤ laneCap := by rw [hsz]; exact hn
  show if (lanesM m0).size ≤ laneCap then _ else _
  simp only [hc, ↓reduceIte]
  refine ⟨hax, hdx.trans hsz.symm, ?_⟩
  show NativeRustcVm.EWsAt st.dmem (outOf m0) (lanesM m0).toList
  refine NativeRustcVm.ewsAt_iff.mpr fun i hi ↦ ?_
  have hi' : i < (lanesM m0).size := by simpa using hi
  rw [Array.getElem_toList, hf i hi']
  exact hl i (by omega)

/-- **The postcondition without**: more than 64 lanes, RAX `0`. -/
theorem post_none (hc : ChangesIn m0 st lanesOfStack (outs m0)) (hs : Saved m0 st)
    (hsz : 64 < (lanesM m0).size) (hax : reg st .rax = 0#64) : LanesOfPost m0 st := by
  refine ⟨?_, hc, hs⟩
  have hc : ¬(lanesM m0).size ≤ laneCap := by unfold laneCap; omega
  show if (lanesM m0).size ≤ laneCap then _ else _
  simp only [hc, ↓reduceIte]
  exact hax

end

/-! ## Values -/

theorem bv_eq_toNat {x y : BitVec 64} (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv_beq_ofNat (x : BitVec 64) {n : Nat} (h : n < 2 ^ 64) :
    (x == BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  rw [bv_beq_toNat, toNat_ofNat_lt h]

theorem ult_lit (x : BitVec 64) {n : Nat} (h : n < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 n) = decide (x.toNat < n) := ult_ofNat h

theorem toNat_shr1 (x : BitVec 64) : (BinOp.apply .shr .W64 x (BitVec.ofNat 64 1)).toNat = x.toNat / 2 := by
  show (x >>> 1).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `b7`'s R8: `8 len - 8`, the last word's byte offset. -/
theorem r8_eq (x : BitVec 64) (h : x.toNat < 65) (h0 : 0 < x.toNat) :
    x * BitVec.ofNat 64 8 + BitVec.ofNat 64 18446744073709551608 =
      BitVec.ofNat 64 (8 * (x.toNat - 1)) := by
  have hx : x * BitVec.ofNat 64 8 =
      BitVec.ofNat 64 (8 * (x.toNat - 1)) + BitVec.ofNat 64 8 := by
    conv_lhs =>
      rw [← show BitVec.ofNat 64 x.toNat = x by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    omega
  rw [hx, BitVec.add_assoc,
    show BitVec.ofNat 64 8 + BitVec.ofNat 64 18446744073709551608 = 0#64 by decide,
    BitVec.add_zero]

theorem shl4_ofNat (e : Nat) :
    BinOp.apply .shl .W64 (BitVec.ofNat 64 e) (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * e) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  have : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := rfl
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show e % 2 ^ 64 * 2 ^ 4 % 2 ^ 64 = 16 * e % 2 ^ 64
  omega

/-! ## Loops -/

section
variable [Host]

/-- **A loop's turns**: from turn `i` at `pc` until `Q`. -/
theorem run_loop {L : Nat → MachineData → Prop} {Q : MachineState → Prop} {pc : Int64}
    (B : Nat) (hB : ∀ i st, L i st → i < B)
    (ht : ∀ i st, L i st →
      Eventually (step1 Host.exe) (fun s ↦ Q s ∨ (L (i + 1) s.data ∧ s.pc = pc)) ⟨st, pc⟩)
    {i : Nat} {st : MachineData} (h0 : L i st) : Eventually (step1 Host.exe) Q ⟨st, pc⟩ :=
  Sym.loop (tr := step1 Host.exe) (Q := Q)
    (fun n s ↦ ∃ i, n = B - i ∧ s.pc = pc ∧ L i s.data)
    (fun n s ⟨i, hn, hpc, hL⟩ ↦ by
      obtain ⟨d, pc'⟩ := s
      simp only at hpc
      subst hpc
      have := hB i d hL
      refine (ht i d hL).mono fun s' h ↦ ?_
      rcases h with h | ⟨hL', hpc'⟩
      · exact .inl h
      · exact .inr ⟨B - (i + 1), by omega, i + 1, rfl, hpc', hL'⟩)
    (n := B - i) ⟨i, rfl, rfl, h0⟩

/-- Continue from a state at `pc`. -/
theorem at_pc {P : MachineData → Prop} {R : MachineState → Prop} {pc : Int64}
    (h : ∀ st, P st → Eventually (step1 Host.exe) R ⟨st, pc⟩) {s : MachineState}
    (hs : P s.data ∧ s.pc = pc) : Eventually (step1 Host.exe) R s := by
  obtain ⟨d, pc'⟩ := s
  obtain ⟨hP, hpc⟩ := hs
  simp only at hpc
  subst hpc
  exact h d hP

variable {k : Nat}

theorem inf (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- **A return from the entry's environment**: a chain of blocks writing only RBX's slot, ending
in `EpiOk` without slots (RBX loaded from its write). -/
theorem chain_ret {m0 : MachineData} (hpre : LanesOfPre m0) {S : SState} {st : MachineState}
    {nx : Int64} (hm : Match (frameEnv m0 m0 8 []) S st.data)
    (hpc : PcOk (frameEnv m0 m0 8 []) (.ret (.load 0 8 8)) nx st)
    (he : NativeRustcVmX64.Transcript.EpiOk 8 [] S = true) (hw : writesBelow S 0 8 = true) :
    st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
      ChangesIn m0 st.data lanesOfStack (outs m0) ∧ Saved m0 st.data := by
  have hwf := wf1 (st := m0) (vars := fun _ ↦ 0) (ret := 0) hpre fun _ h ↦ h
  obtain ⟨hs, hrsp⟩ := Transcript.Frame.epilogue Transcript.Frame.entry hwf hm he
  refine ⟨?_, hrsp, chain_same hpre hm hw, hs⟩
  simp only [PcOk] at hpc
  rw [hpc]
  exact Transcript.Frame.load_ret Transcript.Frame.entry (pre_stack hpre) le_rfl

/-- **The return from the frame** (`b10`): from a body with the `n` lanes the model asks for,
RAX `1`, RDX `n`. -/
theorem done (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0) {f : Nat → EW}
    {n : Nat} {st : MachineData} (hb : Body m0 f n st) (hsz : (lanesM m0).size = n)
    (hf : ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = f j) (hn : n ≤ 64)
    (hax : reg st .rax = 1#64) (hdx : (reg st .rdx).toNat = n) :
    Eventually (step1 Host.exe) (Post m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b10Offset)⟩ := by
  have hwf := wf1 (st := st) (vars := fun _ ↦ 0) (ret := 0) hpre hb.fr.kept
  have hm : Match (frameEnv m0 st 8 [] (fun _ ↦ 0) 0) midS0 st :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_then (inf hp b10_in_code (by simp [b10])) run_b10 hwf (by intro l h; cases h) hm
    fun st' hm' hpc ↦ .done _ ?_
  obtain ⟨he, hmem⟩ := after_eq run_b10 ▸ epi_b10
  obtain ⟨hs, hrsp⟩ := Transcript.Frame.epilogue hb.fr hwf hm' he
  have hd : st'.data.dmem = st.dmem := hm'.dmem_eq hwf hmem
  refine ⟨?_, hrsp, post_some (fun p hp ↦ by rw [hd]; exact hb.same p hp) hs
    (hb.lanes.of_dmem hd) hsz hf hn ?_ ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact Transcript.Frame.load_ret hb.fr (pre_stack hpre) le_rfl
  · exact (hm'.regs .rax _ rfl).trans hax
  · exact (congrArg BitVec.toNat (hm'.regs .rdx _ rfl)).trans hdx

end

end

end NativeRustcVmX64.Whir.LanesOf
