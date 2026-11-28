module

public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify.Bytes
public import NativeRustcArm.XmssVerify.Calls

/-!
# `xmss_verify`: what its layer blocks store

For a block run with the frame as region 0 (and an index `var 0` for a path pointer): the bytes
of an `n`-byte store (`frameWriteN`), bytes copied from the frame (`copiedFrom`,
`bytesAt_copied`), a path step's two children stored in the order bit `z` of the key index says
(`childrenAt`), consecutive pieces (`BytesAt.append_ad`). The symbolic state of a loop's head
(`initL`, `match_initL`), and a block testing `wots_leaf`'s tag (`tagBlock`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc

@[expose] public section

/-- Where a byte of region 0 a block stored was loaded from in region 0, if it was. -/
def copiedFrom (j : Nat) (ws : List Write) : Option Nat :=
  match findWrite 0 j ws with
  | some (.load 0 off k, u) => if u < k ∧ k ≤ 8 then some (off + u) else none
  | _ => none

/-- A loop head's symbolic state: the frame as region 0 (SP its base), the `known` registers,
the index `var 0` below `241`. -/
def initL (known : List (XReg × Sym)) : SState :=
  init [(5872, true)] (.ptr 0 0) known (bounds := [(.var 0, 241)])

end

public section

variable [Labels] {m₀ m m' : MachineData}

omit [Labels] in
theorem BytesAt.append_ad {d : DataMem} {o : Nat} {xs ys : List UInt8}
    (h₁ : BytesAt d (ad m₀ o) xs) (h₂ : BytesAt d (ad m₀ (o + xs.length)) ys) :
    BytesAt d (ad m₀ o) (xs ++ ys) :=
  h₁.append (by rw [ad_add]; exact h₂)

/-- **An `n`-byte store** to the frame: the value's low `n` bytes. -/
theorem frameWriteN {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S m') {o n : Nat}
    (ho : o + n ≤ 5872) {v : Sym} (hw : ∀ t < n, findWrite 0 (o + t) S.mem = some (v, t)) :
    BytesAt m'.dmem (ad m₀ (fb + o))
      ((List.range n).map (byteOf (v.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)))) := by
  have := hm.bytesAt_write (r := 0) (b := ad m₀ fb) (sz := 5872) rfl ho hw
  rwa [ad_add] at this

/-- **Bytes copied within the frame**. -/
theorem bytesAt_copied {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S m') {o s : Nat}
    {bs : List UInt8} (ho : o + bs.length ≤ 5872)
    (hc : ∀ i < bs.length, copiedFrom (o + i) S.mem = some (s + i))
    (h : BytesAt m.dmem (ad m₀ (fb + s)) bs) : BytesAt m'.dmem (ad m₀ (fb + o)) bs := by
  intro i hi
  have hci := hc i hi
  unfold copiedFrom at hci
  split at hci
  · rename_i off k u hf
    split at hci
    · rename_i hu
      simp only [Option.some.injEq] at hci
      have := hm.get?_load (r := 0) (b := ad m₀ fb) (sz := 5872) rfl (j := o + i) (by omega) hf
        hu.1 hu.2
      rw [show ad m₀ (fb + o) + BitVec.ofNat 64 i = ad m₀ fb + BitVec.ofNat 64 (o + i) by
        rw [ad_add, ad_add, Nat.add_assoc], this]
      simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, Env.ofMachine_mem0]
      rw [hci, show ad m₀ fb + BitVec.ofNat 64 (s + i) = ad m₀ (fb + s) + BitVec.ofNat 64 i by
        rw [ad_add, ad_add, Nat.add_assoc], h i hi]
      rfl
    · cases hci
  · cases hci

omit [Labels] in
/-- **A 64-bit load from the frame**: the bytes there. -/
theorem regBytes_frame {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {o : Nat}
    {bs : List UInt8} (hl : bs.length = 8) (h : BytesAt m.dmem (ad m₀ (fb + o)) bs) :
    regBytes ((Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars).load 0 o 8) = bs :=
  regBytes_load hl (by
    simp only [Env.ofMachine_mem0, Env.base_ofMachine_eq, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, ad_add]
    exact h)

/-- **A path step's children**, in the order the condition says: the stores of `cur`'s and the
sibling's 8-byte halves at `5016`. -/
theorem childrenAt {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S m') {c : SBool}
    {a0 a1 b0 b1 : Sym}
    (h0 : ∀ t < 8, findWrite 0 (5016 + t) S.mem = some (.ite c a0 b0, t))
    (h1 : ∀ t < 8, findWrite 0 (5024 + t) S.mem = some (.ite c a1 b1, t))
    (h2 : ∀ t < 8, findWrite 0 (5032 + t) S.mem = some (.ite c b0 a0, t))
    (h3 : ∀ t < 8, findWrite 0 (5040 + t) S.mem = some (.ite c b1 a1, t)) {cur sib : List UInt8}
    (hcur : regBytes (a0.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)) ++
      regBytes (a1.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)) = cur)
    (hsib : regBytes (b0.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)) ++
      regBytes (b1.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)) = sib) :
    BytesAt m'.dmem (ad m₀ (fb + 5016))
      (if c.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) = true then cur ++ sib
        else sib ++ cur) := by
  have w0 := frameWrite hm (o := 5016) (by omega) h0
  have w1 := frameWrite hm (o := 5024) (by omega) h1
  have w2 := frameWrite hm (o := 5032) (by omega) h2
  have w3 := frameWrite hm (o := 5040) (by omega) h3
  subst hcur hsib
  have l := length_regBytes
  by_cases hc : c.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) = true <;>
    simp only [Sym.eval, hc, ite_true, ite_false, Bool.false_eq_true] at w0 w1 w2 w3 ⊢ <;>
    simp only [List.append_assoc] <;>
    refine BytesAt.append_ad w0 (BytesAt.append_ad (by simp only [l]; exact w1)
      (BytesAt.append_ad (by simp only [l]; exact w2) (by simp only [l]; exact w3)))

/-- **A node's address**: the stores of its low field (4 bytes), its high field (2 bytes and 1),
the type `3` and 8 zero bytes at `5392`. -/
theorem addrAt {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S m') {vlo vhi vb2 : Sym}
    (h1 : ∀ t < 4, findWrite 0 (5392 + t) S.mem = some (vlo, t))
    (h2 : ∀ t < 2, findWrite 0 (5396 + t) S.mem = some (vhi, t))
    (h3 : ∀ t < 1, findWrite 0 (5398 + t) S.mem = some (vb2, t))
    (h4 : ∀ t < 1, findWrite 0 (5399 + t) S.mem = some (.lit 3, t))
    (h5 : ∀ t < 8, findWrite 0 (5400 + t) S.mem = some (.lit 0, t)) {lo : Nat} {hi : UInt32}
    (hlo : (vlo.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)).toNat = lo)
    (hhi : [UInt8.ofNat (vhi.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)).toNat,
      UInt8.ofNat ((vhi.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)).toNat / 256),
      UInt8.ofNat (vb2.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars)).toNat] =
      (u32Bytes hi).take 3) :
    BytesAt m'.dmem (ad m₀ (fb + 5392)) (Xmss.address (Xmss.tweak 3 hi lo.toUInt32)) := by
  have p1 := frameWriteN hm (o := 5392) (by omega) h1
  have p2 := frameWriteN hm (o := 5396) (by omega) h2
  have p3 := frameWriteN hm (o := 5398) (by omega) h3
  have p4 := frameWriteN hm (o := 5399) (by omega) h4
  have p5 := frameWriteN hm (o := 5400) (by omega) h5
  rw [u32Bytes_byteOf _ hlo] at p1
  have e23 : (List.range 2).map (byteOf (vhi.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars))) ++
      (List.range 1).map (byteOf (vb2.eval (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars))) =
      (u32Bytes hi).take 3 := by
    rw [← hhi]
    simp [List.range_succ, byteOf]
  have e4 : (List.range 1).map (byteOf ((Sym.lit 3).eval
      (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars))) = [(3 : UInt8) ||| (0 : UInt8) <<< 5] := by
    show (List.range 1).map (byteOf (BitVec.ofNat 64 3)) = _
    decide
  have e5 : (List.range 8).map (byteOf ((Sym.lit 0).eval
      (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars))) = List.replicate 8 0 := by
    show (List.range 8).map (byteOf (BitVec.ofNat 64 0)) = _
    decide
  rw [e4] at p4
  rw [e5] at p5
  have p23 := BytesAt.append_ad p2 (by rw [List.length_map, List.length_range]; exact p3)
  rw [e23] at p23
  unfold Xmss.address Xmss.tweak
  exact BytesAt.append_ad (BytesAt.append_ad (BytesAt.append_ad p1 (by
      rw [NativeRustc.length_u32Bytes]; exact p23))
    (by simp only [List.length_append, NativeRustc.length_u32Bytes, List.length_take]; exact p4))
    (by simp only [List.length_append, NativeRustc.length_u32Bytes, List.length_take,
      List.length_cons, List.length_nil]; exact p5)

/-- A register a block set to a literal. -/
theorem toNat_lit {env : Env} {r : XReg} {n : Nat}
    (h : (m.regs.getXReg r).toBitVec = (Sym.lit n).eval env) (hn : n < 2 ^ 64) :
    (m.regs.getXReg r).toNat = n := by
  have h' : (m.regs.getXReg r).toBitVec = BitVec.ofNat 64 n := h
  rw [toNat_X, h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

end

/-! ## A loop head, a tag test -/

public section

variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

/-- A loop head's environment is well formed. -/
theorem match_initL (P : Pre w m₀) (C : Common m₀ m) {known : List (XReg × Sym)} {z : Nat}
    (hz : 16 * z < 241)
    (hk : AllOf (fun p => (m.regs.getXReg p.1).toBitVec =
      p.2.eval (Env.ofMachine m [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z))) known) :
    Match (Env.ofMachine m [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) (initL known) m := by
  unfold initL
  apply match_ofMachine
  · exact And.intro rfl (And.intro (fun _ => frame16 P) trivial)
  · rw [C.sp]
    simp [Sym.eval]
  · exact hk
  · exact trivial
  · refine ⟨?_, trivial⟩
    simp only [Sym.eval, Env.ofMachine]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hz
  · exact trivial

/-- The path pointer `frame + o + var 0` at turn `z`. -/
theorem eval_pathPtr (o z : Nat) :
    (Sym.bin .add .W64 (.ptr 0 o) (.var 0)).eval
      (Env.ofMachine m [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)) =
      ad m₀ (fb + o + 16 * z) := by
  have h : (Env.ofMachine m [(ad m₀ fb, 5872)] fun _ => BitVec.ofNat 64 (16 * z)).vars 0 =
      BitVec.ofNat 64 (16 * z) := rfl
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.base_ofMachine_eq,
    List.getElem?_cons_zero, Option.map_some, Option.getD_some, BitVec.ofInt_natCast, h, ad_add]

end

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **A block testing `wots_leaf`'s tag** (`ldrb w8, [x21, #16]`, `cbz w8, .LXmssVerify_9`): to
the rejection if it is `0`, else on. -/
theorem tagBlock (P : Pre w m₀) {ds : List Directive} {j : Nat} {known : List (XReg × Sym)}
    {S' : SState} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds (stF0 known) = some (S', .cond (.cmp .eq .W32 (.load 0 5408 1) (.lit 0))
      NativeRustcArm.Xmss.XmssVerify.label_9))
    (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.reg .X29))
    (h29₀ : (stF0 known).reg .X29 = some (.reg .X29)) {st : MachineState}
    (hpc : st.pc = Host.addrOf j) (C : Common m₀ st.data)
    (hknown : AllOf (fun p => (st.data.regs.getXReg p.1).toBitVec =
      p.2.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)])) known)
    {tag : UInt8} {rest : List UInt8} (htag : BytesAt st.data.dmem (ad m₀ (fb + 5408)) (tag :: rest))
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState,
      st'.pc = (if tag = 0 then Labels.label NativeRustcArm.Xmss.XmssVerify.label_9 else Host.addrOf (j + ds.length)) →
      Common m₀ st'.data → st'.data.dmem = st.data.dmem →
      (∀ r v, S'.reg r = some v →
        (st'.data.regs.getXReg r).toBitVec = v.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)])) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := frame_wf P C
  have hm := match_stF0 P C hknown
  refine exec_at hk hx hwf hpc hm fun st' hm' hpc' => ?_
  have hd := hm'.dmem_eq hwf hmem
  have C' := Common.block P C hwf hm hm' (by rw [hsp]; rfl) h29₀ h29 (by simp [writesIn, hmem])
    (fun x _ _ => by rw [hmem]; rfl)
  refine cont st' ?_ C' hd fun r v h => hm'.regs r v h
  have hl : (Env.ofMachine st.data [(ad m₀ fb, 5872)]).load 0 5408 1 =
      BitVec.ofInt 64 (Int.ofBytes [tag]) :=
    Env.load_of_bytesAt rfl (by
      simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, Env.ofMachine_mem0, ad_add]
      exact htag.left (xs := [tag]))
  have hc : (SBool.cmp .eq .W32 (.load 0 5408 1) (.lit 0)).eval
      (Env.ofMachine st.data [(ad m₀ fb, 5872)]) = decide (tag = 0) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, hl, low_W32]
    have ht := tag.toNat_lt
    rw [ofBytes_eq_leNat]
    by_cases h0 : tag = 0
    · subst h0
      decide
    · have : tag.toNat ≠ 0 := fun h => h0 (UInt8.toNat_inj.mp h)
      simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp [NativeRustc.leNat] at this
      omega
  simp only [PcOk, hc] at hpc'
  by_cases h0 : tag = 0 <;> simp only [h0, decide_true, decide_false, ite_true, ite_false,
    Bool.false_eq_true] at hpc' ⊢ <;> exact hpc'

end

end NativeRustcArm.Xmss.XmssVerify
