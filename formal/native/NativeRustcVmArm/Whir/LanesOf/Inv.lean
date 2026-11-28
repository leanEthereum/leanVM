module

public import NativeRustcVmArm.Whir.LanesOf.Exec

/-!
# `lanes_of`'s states

The row's words at the entry (`rowW`), the lanes the model asks for (`revL` at level `0`, `pairL`
later; `lanes_rev`, `lanes_pair`), the lanes written so far (`Lanes`), what every state keeps
(`Body`: no frame, `Fr`), and the loops' heads:
- `index ≠ 0`, `n = len / 2` pairs: `CpLoop j` (`b17`, `2j` lanes copied two at a time),
  `CpTail e` (`b20`, the scalar tail from lane `e`), `Cp1Loop i` (`b21`, `i` lanes copied);
- `index = 0`: `RvLoop j` (`b9`, `4j` lanes reversed four at a time), `RvTail e` (`b11`, the scalar
  tail from lane `e`), `Rv1Loop i` (`b12`, `i` lanes reversed);
- `Done f n` (`b14`): the `n` lanes `f` written, X0 `1`, X2 `n`.
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (Region wordOf ewOf)

@[expose] public section

/-- The row. -/
def rowOf (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The lanes. -/
def outOf (m0 : MachineData) : BitVec 64 := m0.regs.X3.toBitVec
/-- The row's word count. -/
def lenOf (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- The pairs' count. -/
def nOf (m0 : MachineData) : Nat := lenOf m0 / 2
/-- The reversal's four-lane turns. -/
def qOf (m0 : MachineData) : Nat := lenOf m0 / 4
/-- The row's word `i` at the entry. -/
def rowW (m0 : MachineData) (i : Nat) : UInt64 :=
  wordOf m0.dmem (rowOf m0 + BitVec.ofNat 64 (8 * i))
/-- Level `0`'s lane `j`: the row's words reversed. -/
def revL (m0 : MachineData) (j : Nat) : EW := EW.ofK (rowW m0 (lenOf m0 - 1 - j))
/-- A later level's lane `j`: the row's pair `j`. -/
def pairL (m0 : MachineData) (j : Nat) : EW := ⟨rowW m0 (2 * j), rowW m0 (2 * j + 1)⟩
/-- The model's lanes. -/
def lanesM (m0 : MachineData) : Array EW :=
  lanesOf m0.regs.X0.toNat (wordSlice m0 (rowOf m0) (lenOf m0))
/-- The output. -/
def outs (m0 : MachineData) : List Region := [⟨outOf m0, lanesBytes⟩]

/-- A state of the body: no frame. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 0 lanesOfStack [] (outs m0) st

/-- The lanes `f` below `c` written. -/
def Lanes (m0 : MachineData) (f : Nat → EW) (c : Nat) (st : MachineData) : Prop :=
  ∀ j < c, NativeRustcVm.EWAt st.dmem (outOf m0 + BitVec.ofNat 64 (16 * j)) (f j)

/-- What every state keeps. -/
structure Body (m0 : MachineData) (f : Nat → EW) (c : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  lanes : Lanes m0 f c st
  x1 : st.regs.X1 = m0.regs.X1
  x3 : st.regs.X3 = m0.regs.X3
  x30 : st.regs.X30 = m0.regs.X30

/-- `b17`'s head after `j` turns. -/
structure CpLoop (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  body : Body m0 (pairL m0) (2 * j) st
  x2 : st.regs.X2.toNat = nOf m0
  x8 : st.regs.X8.toNat = 2 * (nOf m0 / 2)
  x11 : st.regs.X11.toNat = 2 * (nOf m0 / 2) - 2 * j
  x9 : st.regs.X9.toBitVec = outOf m0 + BitVec.ofNat 64 (32 * j + 16)
  x10 : st.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (32 * j + 16)
  hj : j < nOf m0 / 2
  hn : lenOf m0 < 130

/-- `b20`: the scalar tail from lane `e`. -/
structure CpTail (m0 : MachineData) (e : Nat) (st : MachineData) : Prop where
  body : Body m0 (pairL m0) e st
  x2 : st.regs.X2.toNat = nOf m0
  x8 : st.regs.X8.toNat = e
  he : e < nOf m0
  hn : lenOf m0 < 130

/-- `b21`'s head, `i` lanes copied. -/
structure Cp1Loop (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 (pairL m0) i st
  x0 : st.regs.X0 = 1
  x2 : st.regs.X2.toNat = nOf m0
  x8 : st.regs.X8.toNat = nOf m0 - i
  x9 : st.regs.X9.toBitVec = rowOf m0 + BitVec.ofNat 64 (16 * i + 8)
  x10 : st.regs.X10.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * i + 8)
  hi : i < nOf m0
  hn : lenOf m0 < 130

/-- `b9`'s head after `j` turns. -/
structure RvLoop (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  body : Body m0 (revL m0) (4 * j) st
  x2 : st.regs.X2.toNat = lenOf m0
  x11 : st.regs.X11.toNat = lenOf m0
  x12 : st.regs.X12.toNat = 4 * qOf m0
  x15 : st.regs.X15.toNat = 4 * qOf m0 - 4 * j
  x14 : st.regs.X14.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * lenOf m0 - 16 - 32 * j)
  x13 : st.regs.X13.toBitVec = outOf m0 + BitVec.ofNat 64 (64 * j + 32)
  x8 : st.regs.X8.toBitVec = outOf m0 + BitVec.ofNat 64 (64 * qOf m0)
  x10 : st.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - 4 * qOf m0))
  x9 : st.regs.X9.toNat = 16 * lenOf m0
  hj : j < qOf m0
  hn : lenOf m0 < 65

/-- `b11`: the scalar tail from lane `e`. -/
structure RvTail (m0 : MachineData) (e : Nat) (st : MachineData) : Prop where
  body : Body m0 (revL m0) e st
  x2 : st.regs.X2.toNat = lenOf m0
  x8 : st.regs.X8.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * e)
  x10 : st.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - e))
  x9 : st.regs.X9.toNat = 16 * lenOf m0
  he : e < lenOf m0
  hn : lenOf m0 < 65

/-- `b12`'s head, `i` lanes reversed. -/
structure Rv1Loop (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 (revL m0) i st
  x0 : st.regs.X0 = 1
  x2 : st.regs.X2.toNat = lenOf m0
  x8 : st.regs.X8.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * i)
  x9 : st.regs.X9.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * lenOf m0)
  x10 : st.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - 1 - i))
  x11 : st.regs.X11.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - 1 - i))
  hi : i < lenOf m0
  hn : lenOf m0 < 65

/-- `b14`: the `n` lanes `f` written. -/
structure Done (m0 : MachineData) (f : Nat → EW) (n : Nat) (st : MachineData) : Prop where
  body : Body m0 f n st
  x0 : st.regs.X0 = 1
  x2 : st.regs.X2.toNat = n

end

public section

theorem pre_parts {m0 : MachineData} (hpre : LanesOfPre m0) :
    WhirIn m0 (rowOf m0) (8 * lenOf m0) 0 ∧ WhirIn m0 (outOf m0) lanesBytes 0 ∧
      NativeRustcVm.Apart (outOf m0) lanesBytes (rowOf m0) (8 * lenOf m0) :=
  hpre

theorem lanesBytes_eq : lanesBytes = 1024 := rfl

/-! ## The model -/

/-- **Level `0`'s lanes**: the row reversed. -/
theorem lanes_rev {m0 : MachineData} (h0 : m0.regs.X0.toNat = 0) :
    (lanesM m0).size = lenOf m0 ∧
      ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = revL m0 j := by
  have hs : (lanesM m0).size = lenOf m0 := by
    simp [lanesM, lanesOf, h0, wordSlice]
  refine ⟨hs, fun j h ↦ ?_⟩
  rw [hs] at h
  simp [lanesM, lanesOf, h0, wordSlice, revL, rowW, NativeRustcVm.wordsOf]

/-- **A later level's lanes**: the row's pairs. -/
theorem lanes_pair {m0 : MachineData} (h0 : m0.regs.X0.toNat ≠ 0) :
    (lanesM m0).size = nOf m0 ∧
      ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = pairL m0 j := by
  have hs : (lanesM m0).size = nOf m0 := by
    simp [lanesM, lanesOf, h0, wordSlice, extRow, nOf]
  refine ⟨hs, fun j h ↦ ?_⟩
  rw [hs] at h
  have h1 : 2 * j + 1 < lenOf m0 := by unfold nOf at h; omega
  simp [lanesM, lanesOf, h0, wordSlice, extRow, pairL, rowW, NativeRustcVm.wordsOf,
    Array.getD_eq_getD_getElem?, h1, show 2 * j < lenOf m0 by omega]

/-! ## Frames and memory -/

section
variable {m0 st st' : MachineData}

theorem fr_entry : Fr m0 m0 := Frame.of_saved ⟨fun _ _ ↦ rfl, rfl, fun _ h ↦ h⟩ rfl

theorem Fr.saved (h : Fr m0 st) : Saved m0 st := by
  refine ⟨fun r hr ↦ h.regs r hr (by simp), ?_, h.kept⟩
  apply UInt64.toBitVec_inj.mp
  rw [h.sp]
  simp

/-- **The row's words** in a body: apart from the lanes. -/
theorem row_word (hpre : LanesOfPre m0) (hfr : Fr m0 st) {i : Nat} (hi : i < lenOf m0) :
    wordOf st.dmem (rowOf m0 + BitVec.ofNat 64 (8 * i)) = rowW m0 i := by
  obtain ⟨hrin, hoin, hap⟩ := pre_parts hpre
  refine NativeRustcVm.wordOf_congr fun b hb ↦ ?_
  rw [addr_add]
  refine hfr.get?_eq fun h ↦ h.elim (fun ⟨r, hr, hp⟩ ↦ ?_) (fun h ↦ ?_)
  · simp only [outs, List.mem_singleton] at hr
    subst hr
    exact not_inRange_of_apart hap.symm hrin.1.2 hoin.1.2 (by omega) hp
  · unfold InRange at h
    simp [lanesOfStack] at h

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
        toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)] at hin
      omega
  · have := hn (j - c) (by omega)
    rwa [show c + (j - c) = j by omega] at this

/-- **A lane a block wrote**: its two words, at offsets `o` and `o + 8` of region `r`. -/
theorem Match.ewAt_write [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 16 ≤ sz) {v0 v1 : Sym}
    (hw0 : ∀ i < 8, findWrite r (o + i) S.mem = some (v0, i))
    (hw1 : ∀ i < 8, findWrite r (o + 8 + i) S.mem = some (v1, i)) :
    NativeRustcVm.EWAt m.dmem (b + BitVec.ofNat 64 o)
      ⟨UInt64.ofBitVec (v0.eval env), UInt64.ofBitVec (v1.eval env)⟩ := by
  rw [NativeRustcVm.ewAt_iff]
  refine ⟨Match.wordAt_write hm hb (by omega) hw0, ?_⟩
  rw [addr_add]
  exact Match.wordAt_write hm hb (by omega) hw1

/-- A row word an environment loads: region `0` the row from word `o`. -/
theorem load_row (hpre : LanesOfPre m0) (hfr : Fr m0 st) {o t : Nat}
    {rest : List (BitVec 64 × Nat)} {n : Nat} (ht : o + t < lenOf m0) :
    (Env.ofMachine st ((rowOf m0 + BitVec.ofNat 64 (8 * o), n) :: rest)).load 0 (8 * t) 8 =
      (rowW m0 (o + t)).toBitVec := by
  rw [load8_eq]
  show (wordOf st.dmem (rowOf m0 + BitVec.ofNat 64 (8 * o) + BitVec.ofNat 64 (8 * t))).toBitVec = _
  rw [addr_add, show 8 * o + 8 * t = 8 * (o + t) by omega, row_word hpre hfr ht]

/-- A row word a block loaded: `load 0 off 8`, `off` the word `t`'s. -/
theorem load_eval [Labels] (hpre : LanesOfPre m0) (hfr : Fr m0 st) {o t off : Nat}
    {rest : List (BitVec 64 × Nat)} {n : Nat} (hoff : off = 8 * t) (ht : o + t < lenOf m0) :
    UInt64.ofBitVec ((Sym.load 0 off 8).eval
      (Env.ofMachine st ((rowOf m0 + BitVec.ofNat 64 (8 * o), n) :: rest))) = rowW m0 (o + t) := by
  subst hoff
  show UInt64.ofBitVec ((Env.ofMachine st _).load 0 (8 * t) 8) = _
  rw [load_row hpre hfr ht]

/-- **A loop body's environment**: the row's `n` bytes from word `o`, the lanes' `n'` from lane
`c`. -/
theorem wf_two (hpre : LanesOfPre m0) (hfr : Fr m0 st) {o n c n' : Nat}
    (hrow : 8 * o + n ≤ 8 * lenOf m0) (hout : 16 * c + n' ≤ 1024) (hn : 0 < n) (hn' : 0 < n') :
    (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * o), n),
      (outOf m0 + BitVec.ofNat 64 (16 * c), n')]).WF := by
  obtain ⟨hrin, hoin, hap⟩ := pre_parts hpre
  have hr := hfr.readable (Readable.sub hrin.1 hrow)
  have ho := hfr.readable (Readable.sub hoin.1 hout)
  refine Env.wf_of ⟨⟨hr.1, hr.2⟩, ⟨ho.1, ho.2⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  have h1 : (rowOf m0).toNat + 8 * lenOf m0 ≤ 2 ^ 64 := hrin.1.2
  have h2 : (outOf m0).toNat + 1024 ≤ 2 ^ 64 := hoin.1.2
  have hap' : (outOf m0).toNat + 1024 ≤ (rowOf m0).toNat ∨
      (rowOf m0).toNat + 8 * lenOf m0 ≤ (outOf m0).toNat := hap
  show Apart _ _ _ _
  unfold Apart
  rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
  omega

/-- A block writing lanes keeps a body: its writes in region `1`, the lanes from lane `c`. -/
theorem Fr.of_lanes [Labels] {env : Env} {S₀ S₁ : SState} (hpre : LanesOfPre m0) (hb : Fr m0 st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ (freeRegs []) = true) {c n len : Nat}
    (hr : env.regions[1]? = some (outOf m0 + BitVec.ofNat 64 (16 * c), n)) (hlen : len ≤ n)
    (hall : ∀ w ∈ S₁.mem, w.r = 1 ∧ w.off + w.n ≤ len) (hc : 16 * c + len ≤ 1024) :
    Fr m0 st' :=
  hb.of_block hm₀ hm hwf hd hk hr hlen hall
    (fun p h ↦ .inl ⟨_, List.mem_singleton_self _,
      NativeRustcVm.InRange.of_sub h (pre_parts hpre).2.1.1.2 (by rw [lanesBytes_eq]; omega)⟩)
    (fun _ hq ↦ absurd hq List.not_mem_nil)

/-- A register-only block keeps a body. -/
theorem Fr.of_regsS [Labels] {S₁ : SState} (hb : Fr m0 st)
    (hm : Match (Env.ofMachine st []) S₁ st') (hk : keepsRegs regsS S₁ (freeRegs []) = true)
    (hmem : S₁.mem = []) : Fr m0 st' :=
  hb.of_regs (match_nil st) hm (Env.wf_nil _) rfl hk hmem

/-- A register a block kept. -/
theorem reg_kept [Labels] {regions : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine st regions) S st') {r : XReg} (h : S.reg r = some (.reg r)) :
    st'.regs.getXReg r = st.regs.getXReg r :=
  UInt64.toBitVec_inj.mp ((hm.regs r _ h).trans rfl)

/-- A register-only block keeps a body's lanes and registers. -/
theorem Body.of_regsS [Labels] {f : Nat → EW} {c : Nat} {S₁ : SState} (hb : Body m0 f c st)
    (hm : Match (Env.ofMachine st []) S₁ st') (hk : keepsRegs regsS S₁ (freeRegs []) = true)
    (hmem : S₁.mem = []) (h1 : S₁.reg .X1 = some (.reg .X1)) (h3 : S₁.reg .X3 = some (.reg .X3))
    (h30 : S₁.reg .X30 = some (.reg .X30)) : Body m0 f c st' where
  fr := hb.fr.of_regsS hm hk hmem
  lanes := hb.lanes.of_dmem (hm.dmem_eq (Env.wf_nil _) hmem)
  x1 := (reg_kept hm h1).trans hb.x1
  x3 := (reg_kept hm h3).trans hb.x3
  x30 := (reg_kept hm h30).trans hb.x30

end

/-! ## The end -/

/-- **The postcondition with lanes**: the model's `n ≤ 64` lanes written, X0 `1`, X1 `n`. -/
theorem post_some {m0 st : MachineData} {f : Nat → EW} {n : Nat} (hfr : Fr m0 st)
    (hl : Lanes m0 f n st) (hsz : (lanesM m0).size = n)
    (hf : ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = f j) (hn : n ≤ 64)
    (hx0 : st.regs.X0 = 1) (hx1 : st.regs.X1.toNat = n) : LanesOfPost m0 st := by
  refine ⟨?_, hfr.same, hfr.saved⟩
  have hc : (lanesM m0).size ≤ laneCap := by rw [hsz]; exact hn
  show if (lanesM m0).size ≤ laneCap then _ else _
  simp only [hc, ↓reduceIte]
  refine ⟨hx0, hx1.trans hsz.symm, ?_⟩
  show NativeRustcVm.EWsAt st.dmem (outOf m0) (lanesM m0).toList
  refine NativeRustcVm.ewsAt_iff.mpr fun i hi ↦ ?_
  have hi' : i < (lanesM m0).size := by simpa using hi
  rw [Array.getElem_toList, hf i hi']
  exact hl i (by omega)

/-- **The postcondition without**: more than 64 lanes, X0 `0`. -/
theorem post_none {m0 st : MachineData} (hfr : Fr m0 st) (hsz : 64 < (lanesM m0).size)
    (hx0 : st.regs.X0 = 0) : LanesOfPost m0 st := by
  refine ⟨?_, hfr.same, hfr.saved⟩
  have hc : ¬(lanesM m0).size ≤ laneCap := by unfold laneCap; omega
  show if (lanesM m0).size ≤ laneCap then _ else _
  simp only [hc, ↓reduceIte]
  exact hx0

/-! ## Words -/

theorem bv_eq_toNat {x : BitVec 64} {v : UInt64} (h : x.toNat = v.toNat) : x = v.toBitVec :=
  BitVec.eq_of_toNat_eq (by simpa using h)

theorem ofInt_pos (c : Nat) : BitVec.ofInt 64 (c : Int) = BitVec.ofNat 64 c := rfl

/-- A pointer's negative offset. -/
theorem add_ofInt_neg (a : BitVec 64) {n c : Nat} {z : Int} (hz : z = -(c : Int)) (h : c ≤ n) :
    a + BitVec.ofNat 64 n + BitVec.ofInt 64 z = a + BitVec.ofNat 64 (n - c) := by
  subst hz
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem sub_ofNat (a : BitVec 64) {n c : Nat} (h : c ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 c = a + BitVec.ofNat 64 (n - c) := by
  have e : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - c) + BitVec.ofNat 64 c := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h]
  rw [e, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem ofNat_sub_ofNat {n c : Nat} (h : c ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 c = BitVec.ofNat 64 (n - c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem shl_apply (x : BitVec 64) (n : Nat) :
    UnOp.apply (.shift .LSL n) .W64 x = BitVec.ofNat 64 (2 ^ n * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64, shiftW]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

/-- Level `0`'s lane `c`: the row's word `o + u`, `0`. -/
theorem revL_of [Labels] {env : Env} {m0 : MachineData} {o u c : Nat}
    (h : o + u = lenOf m0 - 1 - c) :
    (⟨rowW m0 (o + u), UInt64.ofBitVec ((Sym.lit 0).eval env)⟩ : EW) = revL m0 c := by
  rw [h]; rfl

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `lsl #3` as rustc writes it (`ubfm #61, #60`). -/
theorem lsl3 (x : BitVec 64) : UnOp.apply (.ubfm 61 60) .W64 x = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `lsl #4` as rustc writes it (`ubfm #60, #59`). -/
theorem lsl4 (x : BitVec 64) : UnOp.apply (.ubfm 60 59) .W64 x = BitVec.ofNat 64 (16 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `lsr #1`. -/
theorem lsr1 (x : BitVec 64) : UnOp.apply (.ubfm 1 63) .W64 x = BitVec.ofNat 64 (x.toNat / 2) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- `lsr #3`. -/
theorem lsr3 (x : BitVec 64) : UnOp.apply (.ubfm 3 63) .W64 x = BitVec.ofNat 64 (x.toNat / 8) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- `lsr #4`. -/
theorem lsr4 (x : BitVec 64) : UnOp.apply (.ubfm 4 63) .W64 x = BitVec.ofNat 64 (x.toNat / 16) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- `and #0x1ffffffffffffffc` of a small count: its multiple of `4`. -/
theorem and_mask4 (x : BitVec 64) (h : x.toNat < 65) :
    (x &&& BitVec.ofNat 64 2305843009213693948).toNat = 4 * (x.toNat / 4) := by
  have key : ∀ L < 65,
      (BitVec.ofNat 64 L &&& BitVec.ofNat 64 2305843009213693948).toNat = 4 * (L / 4) := by
    decide
  simpa using key x.toNat h

/-- `and #0x7e` of a small count: its multiple of `2`. -/
theorem and_mask2 (x : BitVec 64) (h : x.toNat < 65) :
    (x &&& BitVec.ofNat 64 126).toNat = 2 * (x.toNat / 2) := by
  have key : ∀ L < 65, (BitVec.ofNat 64 L &&& BitVec.ofNat 64 126).toNat = 2 * (L / 2) := by
    decide
  simpa using key x.toNat h

/-- `orr #8, x, lsl #4` of a small count. -/
theorem orr_lsl4 (x : BitVec 64) (h : x.toNat < 65) :
    (BitVec.ofNat 64 8 ||| x <<< 4).toNat = 16 * x.toNat + 8 := by
  have key : ∀ L < 65, (BitVec.ofNat 64 8 ||| BitVec.ofNat 64 L <<< 4).toNat = 16 * L + 8 := by
    decide
  simpa using key x.toNat h

end

/-! ## Loops -/

public section
variable [Host]

/-- **A loop's turns**: from turn `0` at `pc` until `Q`. -/
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

end

end NativeRustcVmArm.Whir.LanesOf
