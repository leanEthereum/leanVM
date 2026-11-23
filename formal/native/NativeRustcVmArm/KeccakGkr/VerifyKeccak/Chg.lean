module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.First

/-!
# Changes as numbers

From the entry `m0`: the output regions by index (`ob`, `osz`: the `TState`, the scratch, the
column claims, `KeccakOutW`), a set of bytes a step may change (`WS`: the stack below the frame,
frame ranges `L`, ranges `O` of the outputs), changes within it (`Chg`, composing by `Chg.trans`),
and what they keep: frame bytes (`Chg.frame`), output bytes (`Chg.out`), the `TState`
(`Chg.ts`), the column claims (`Chg.cls`). A callee's footprint into `WS`: `ws_stk`, `ws_loc`,
`ws_ob`; a block's writes: `Chg.block`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.Layout (Same)

@[expose] public section

/-- Output region `i`'s base. -/
def ob (m0 : MachineData) : Nat → BitVec 64
  | 0 => tA m0
  | 1 => scA m0
  | 2 => clA m0
  | _ => oA m0

/-- Output region `i`'s size. -/
def osz : Nat → Nat
  | 0 => 760
  | 1 => 205824
  | 2 => 97288
  | _ => 1608

/-- The bytes a step may change: the stack below the frame, the frame's ranges `L` (offsets),
the outputs' ranges `O` (region, from, to). -/
def WS (m0 : MachineData) (L : List (Nat × Nat)) (O : List (Nat × Nat × Nat))
    (q : BitVec 64) : Prop :=
  (m0.regs.SP.toNat - 7008 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360) ∨
    (∃ p ∈ L, m0.regs.SP.toNat - 3360 + p.1 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + p.2) ∨
    (∃ o ∈ O, (ob m0 o.1).toNat + o.2.1 ≤ q.toNat ∧ q.toNat < (ob m0 o.1).toNat + o.2.2)

/-- **Changes within `WS m0 L O`.** -/
def Chg (m0 : MachineData) (L : List (Nat × Nat)) (O : List (Nat × Nat × Nat))
    (d d' : Mem 64) : Prop :=
  SameOutside d d' (WS m0 L O)

/-- The frame ranges are below the slots. -/
def okL (L : List (Nat × Nat)) : Bool := L.all fun p ↦ decide (p.2 ≤ 3264)

/-- The output ranges are within their regions. -/
def okO (O : List (Nat × Nat × Nat)) : Bool := O.all fun o ↦ decide (o.1 < 4 ∧ o.2.2 ≤ osz o.1)

end

public section

variable {m0 : MachineData}

theorem Chg.refl (L : List (Nat × Nat)) (O : List (Nat × Nat × Nat)) (d : Mem 64) :
    Chg m0 L O d d := fun _ _ ↦ rfl

theorem Chg.trans {L L' : List (Nat × Nat)} {O O' : List (Nat × Nat × Nat)} {d1 d2 d3 : Mem 64}
    (h : Chg m0 L O d1 d2) (h' : Chg m0 L' O' d2 d3) : Chg m0 (L ++ L') (O ++ O') d1 d3 := by
  intro q hq
  have mono : ∀ {L1 O1}, (∀ p ∈ L1, p ∈ L ++ L') → (∀ o ∈ O1, o ∈ O ++ O') →
      ¬WS m0 (L ++ L') (O ++ O') q → ¬WS m0 L1 O1 q := by
    intro L1 O1 hL hO hn hw
    apply hn
    rcases hw with h1 | ⟨p, hp, h1⟩ | ⟨o, ho, h1⟩
    · exact .inl h1
    · exact .inr (.inl ⟨p, hL p hp, h1⟩)
    · exact .inr (.inr ⟨o, hO o ho, h1⟩)
  rw [h' q (mono (fun p hp ↦ List.mem_append_right _ hp) (fun o ho ↦ List.mem_append_right _ ho)
    hq), h q (mono (fun p hp ↦ List.mem_append_left _ hp)
      (fun o ho ↦ List.mem_append_left _ ho) hq)]

theorem Chg.mono {L L' : List (Nat × Nat)} {O O' : List (Nat × Nat × Nat)} {d d' : Mem 64}
    (h : Chg m0 L O d d') (hL : ∀ p ∈ L, p ∈ L') (hO : ∀ o ∈ O, o ∈ O') : Chg m0 L' O' d d' := by
  intro q hq
  refine h q fun hw ↦ hq ?_
  rcases hw with h1 | ⟨p, hp, h1⟩ | ⟨o, ho, h1⟩
  · exact .inl h1
  · exact .inr (.inl ⟨p, hL p hp, h1⟩)
  · exact .inr (.inr ⟨o, hO o ho, h1⟩)

section
variable [Labels] {a : DecArea} {inst : Array EW}

/-- An output region: no wrap, apart from the stack. -/
theorem ob_ok (hn : Nums a inst m0) {i : Nat} (hi : i < 4) :
    (ob m0 i).toNat + osz i ≤ 2 ^ 64 ∧
      ((ob m0 i).toNat + osz i ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ (ob m0 i).toNat) := by
  match i, hi with
  | 0, _ => exact ⟨hn.tW, hn.tS⟩
  | 1, _ => exact ⟨hn.sW, hn.sS⟩
  | 2, _ => exact ⟨hn.cW, hn.cS⟩
  | 3, _ => exact ⟨hn.oW, hn.oS⟩

/-- Two output regions are apart. -/
theorem ob_apart (hn : Nums a inst m0) {i j : Nat} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    (ob m0 i).toNat + osz i ≤ (ob m0 j).toNat ∨ (ob m0 j).toNat + osz j ≤ (ob m0 i).toNat := by
  have h4 : ∀ x, x < 4 → x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  have := hn.txs; have := hn.txc; have := hn.txo; have := hn.sxc; have := hn.sxo; have := hn.cxo
  rcases h4 i hi with rfl | rfl | rfl | rfl <;> rcases h4 j hj with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hij | (simp only [ob, osz]; omega)

/-- An output region is apart from the decoded area. -/
theorem ob_words (hn : Nums a inst m0) {i : Nat} (hi : i < 4) :
    (ob m0 i).toNat + osz i ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (ob m0 i).toNat := by
  match i, hi with
  | 0, _ => exact hn.t_w
  | 1, _ => exact hn.s_w
  | 2, _ => exact hn.c_w
  | 3, _ => exact hn.o_w

omit [Labels] in
theorem okO_mem {O : List (Nat × Nat × Nat)} (h : okO O = true) {o : Nat × Nat × Nat}
    (ho : o ∈ O) : o.1 < 4 ∧ o.2.2 ≤ osz o.1 := by
  simp only [okO, List.all_eq_true, decide_eq_true_eq] at h
  exact h o ho

/-- **Frame bytes** a change misses. -/
theorem Chg.frame (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hO : okO O = true) {o n : Nat} (ho : o + n ≤ 3360)
    (hL : L.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true) :
    Same d d' (loc m0 o) n := by
  have := hn.hN
  have := m0.regs.SP.toNat_lt
  refine same_num hc (by rw [loc_toNat hn.hN (by omega)]; omega) fun q hq ↦ ?_
  rw [loc_toNat hn.hN (by omega)]
  rcases hq with h1 | ⟨p, hp, h1⟩ | ⟨e, he, h1⟩
  · omega
  · simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hL
    have := hL p hp
    omega
  · obtain ⟨hi, hle⟩ := okO_mem hO he
    have := ob_ok hn hi
    omega

/-- **Output bytes** a change misses. -/
theorem Chg.out (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hLok : okL L = true) (hO : okO O = true) {i o n : Nat}
    (hi : i < 4) (hn0 : 0 < n) (hon : o + n ≤ osz i)
    (hOi : O.all (fun e ↦ decide (e.1 ≠ i) || decide (e.2.2 ≤ o) || decide (o + n ≤ e.2.1)) =
      true) :
    Same d d' (ob m0 i + BitVec.ofNat 64 o) n := by
  have hi' := ob_ok hn hi
  have := hn.hN
  refine same_num hc (by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega) fun q hq ↦ ?_
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  rcases hq with h1 | ⟨p, hp, h1⟩ | ⟨e, he, h1⟩
  · omega
  · simp only [okL, List.all_eq_true, decide_eq_true_eq] at hLok
    have := hLok p hp
    omega
  · obtain ⟨hei, hle⟩ := okO_mem hO he
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hOi
    by_cases hne : e.1 = i
    · rw [hne] at h1
      rcases hOi e he with (hne' | h2) | h2
      · exact absurd hne hne'
      · omega
      · omega
    · have := ob_apart hn hei hi hne
      omega

/-- Output bytes at the region's base. -/
theorem Chg.out0 (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hLok : okL L = true) (hO : okO O = true) {i n : Nat}
    (hi : i < 4) (hn0 : 0 < n) (hon : n ≤ osz i)
    (hOi : O.all (fun e ↦ decide (e.1 ≠ i) || decide (e.2.2 ≤ 0) || decide (n ≤ e.2.1)) = true) :
    Same d d' (ob m0 i) n := by
  have := hc.out hn hLok hO hi (o := 0) (n := n) hn0 (by omega) (by simpa using hOi)
  rwa [NativeRustcVm.addr_add_zero] at this

/-- **The `TState`** stays where a change misses it. -/
theorem Chg.ts (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hk : Kept d d') (hLok : okL L = true)
    (hO : okO O = true) (hOt : O.all (fun e ↦ decide (e.1 ≠ 0)) = true) {s' : TState}
    (h : TStateAt d (tA m0) a s') : TStateAt d' (tA m0) a s' := by
  have := hn.hN; have := hn.tS; have := hn.wS
  refine ts_keep hn h hk hc fun q hq ↦ ?_
  rcases hq with h1 | ⟨p, hp, h1⟩ | ⟨e, he, h1⟩
  · constructor <;> omega
  · simp only [okL, List.all_eq_true, decide_eq_true_eq] at hLok
    have := hLok p hp
    constructor <;> omega
  · obtain ⟨hei, hle⟩ := okO_mem hO he
    simp only [List.all_eq_true, decide_eq_true_eq] at hOt
    have h0 : (ob m0 e.1).toNat + osz e.1 ≤ (tA m0).toNat ∨
        (tA m0).toNat + 760 ≤ (ob m0 e.1).toNat := ob_apart hn hei (j := 0) (by decide) (hOt e he)
    have h2 := ob_words hn hei
    constructor <;> omega

/-- **The column claims** stay where a change misses them. -/
theorem Chg.cls (hn : Nums a inst m0) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)}
    {d d' : Mem 64} (hc : Chg m0 L O d d') (hLok : okL L = true) (hO : okO O = true)
    (hOc : O.all (fun e ↦ decide (e.1 ≠ 2)) = true) {cs : Array ColumnClaimW}
    (h : NativeRustcVm.Layout.ClaimsWAt d (clA m0) cs) :
    NativeRustcVm.Layout.ClaimsWAt d' (clA m0) cs :=
  NativeRustcVm.Tables.ClaimsWAt.of_same h (hc.out0 hn hLok hO (i := 2) (by decide)
      (by decide) le_rfl (by
    simp only [List.all_eq_true, decide_eq_true_eq] at hOc
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact fun e he ↦ .inl (.inl (hOc e he))))

/-! ## Footprints into `WS` -/

theorem ws_stk (hn : Nums a inst m0) {st : MachineData} (hfr : VFr m0 st) {N' : Nat}
    (hN' : N' ≤ 3648) {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {q : BitVec 64}
    (h : InRange (stackBelow st N') N' q) : WS m0 L O q := by
  have := stk_nat hn hfr hN' h
  exact .inl ⟨by omega, this.2⟩

theorem ws_loc (hn : Nums a inst m0) {o n : Nat} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (hp : (o, o + n) ∈ L) (ho : o + n ≤ 3360) {q : BitVec 64}
    (h : NativeRustcVm.InRange (loc m0 o) n q) : WS m0 L O q := by
  have := loc_nat hn ho h
  refine .inr (.inl ⟨_, hp, ?_, ?_⟩) <;> simp only <;> omega

theorem ws_ob (hn : Nums a inst m0) {i o n : Nat} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (hp : (i, o, o + n) ∈ O) (hi : i < 4) (hn0 : 0 < n)
    (ho : o + n ≤ osz i) {q : BitVec 64} (h : NativeRustcVm.InRange
        (ob m0 i + BitVec.ofNat 64 o) n q) :
    WS m0 L O q := by
  have := ob_ok hn hi
  have e : (ob m0 i + BitVec.ofNat 64 o).toNat = (ob m0 i).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have h1 := inR_nat (by rw [e]; omega) h
  rw [e] at h1
  exact .inr (.inr ⟨_, hp, by simp only; omega, by simp only; omega⟩)

theorem ws_ob0 (hn : Nums a inst m0) {i n : Nat} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (hp : (i, 0, n) ∈ O) (hi : i < 4) (hn0 : 0 < n)
    (ho : n ≤ osz i) {q : BitVec 64} (h : NativeRustcVm.InRange (ob m0 i) n q) : WS m0 L O q :=
  ws_ob hn (o := 0) (n := n) (by simpa using hp) hi hn0 (by omega)
    (by rwa [NativeRustcVm.addr_add_zero])

/-- **A block's writes** in the frame's ranges `L`. -/
theorem Chg.block (hn : Nums a inst m0) {rs : List (BitVec 64 × Nat)} {m st : MachineData}
    {S : SState} (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S st)
    (hwf : (Env.ofMachine m ((fb m0, 3360) :: rs)).WF) {L : List (Nat × Nat)}
    (hw : S.mem.all (fun w ↦ w.r == 0 &&
      L.any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true) :
    Chg m0 L [] m.dmem st.dmem :=
  NativeRustcVm.SameOutside.mono (written_in hn hm hwf hw) fun _ h ↦ .inr (.inl h)

end

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
