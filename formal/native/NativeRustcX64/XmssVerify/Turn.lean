module

public import NativeRustcX64.XmssVerify.Node
public import NativeRustcX64.XmssVerify.Bytes

/-!
# `xmss_verify`: what its path loops' blocks store (x86-64)

A path turn's blocks run with the frame below the layers (region 0, `3356` bytes),
the turn's node of the path (region 1, `16` bytes), and the memset GOT slot (region 2)
(`nodeR`, `node_wf`). The bytes of a store to the frame (`frameWrite`), a path step's two children stored in the order the bit test
says (`childrenAt`), a node's address (`addrAt`), and the values the blocks compute
(`add1_eval`, `trunc_toNat`, `shr16_toNat`, `hiBytes_bottom`, `hiBytes_top`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

public section

variable [Labels] {w : Nat → UInt64} {m₀ m m' : MachineData}

/-- A path turn's regions: the frame below the layers, the path node at the frame offset
`o`, and the memset GOT slot. -/
abbrev nodeR (m₀ : MachineData) (o : Nat) : List (BitVec 64 × Nat) :=
  [(ad m₀ fr, 3356), (ad m₀ (fr + o), 16), (gotAddr "memset", 8)]

theorem node_wf (P : Pre w m₀) (hk : Kept m₀.dmem m.dmem) {o : Nat} (ho : 3356 ≤ o)
    (ho' : o + 16 ≤ 5816) {vs : Nat → BitVec 64} {ret : BitVec 64} :
    (Env.ofMachine m (nodeR m₀ o) vs ret).WF :=
  Env.wf_of ⟨⟨(P.mapped.sub (i := fr) (k := 3356) (by fro)).kept hk, P.ad_nw (by fro)⟩,
      ⟨(P.mapped.sub (i := fr + o) (k := 16) (by fro)).kept hk, P.ad_nw (by fro)⟩,
      ⟨(P.got.mapped (by simp)).kept hk, (P.got.1 "memset" (by simp)).2.1⟩, trivial⟩
    (pairwise3 (P.apart_ad (s := 3356) (s' := 16) (by omega) (by fro) (by fro)
      (by decide) (by decide))
      (got_apart P (by simp) (by fro) (by dsimp; decide)).symm
      (got_apart P (by simp) (by fro) (by dsimp; decide)).symm)

theorem match_stN (P : Pre w m₀)
    (hs : SameOutside m₀.dmem m.dmem (InRange (lo m₀) 9248))
    {o : Nat} {ret : BitVec 64} {known : List (Reg64 × Sym)}
    (hk : AllOf (fun p => reg m p.1 =
      p.2.eval (Env.ofMachine m (nodeR m₀ o) (fun _ => 0) ret))
      ((.rsp, .ptr 0 24) :: known)) :
    Match (Env.ofMachine m (nodeR m₀ o) (fun _ => 0) ret) (stN known) m := by
  apply Match.withKnownBytes
  · exact match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ hk trivial trivial
      ⟨by simp [Sym.eval, Env.base, nodeR, gotAddr], trivial⟩
  · intro i hi
    simpa [Sym.eval, Env.base, nodeR] using got_byte P hs (by simp : "memset" ∈ _) hi

/-- **An `n`-byte store** to the frame. -/
theorem frameWrite {N : Nat} {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) S m')
    {o n : Nat} (ho : o + n ≤ N) {v : Sym} (hw : ∀ t < n, findWrite 0 (o + t) S.mem = some (v, t)) :
    BytesAt m'.dmem (ad m₀ (fr + o))
      ((List.range n).map (byteOf (v.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)))) := by
  have := hm.bytesAt_write (r := 0) (b := ad m₀ fr) (sz := N) rfl ho hw
  rwa [ad_add] at this

omit [Labels] in
theorem BytesAt.append_ad {d : DataMem} {o : Nat} {xs ys : List UInt8}
    (h₁ : BytesAt d (ad m₀ o) xs) (h₂ : BytesAt d (ad m₀ (o + xs.length)) ys) :
    BytesAt d (ad m₀ o) (xs ++ ys) :=
  h₁.append (by rw [ad_add]; exact h₂)

omit [Labels] in
theorem bytes_take {d : DataMem} {o : Nat} {bs : List UInt8} (h : BytesAt d (ad m₀ o) bs)
    (n : Nat) : BytesAt d (ad m₀ o) (bs.take n) := fun i hi => by
  rw [List.length_take] at hi
  rw [h i (by omega), List.getElem_take]

omit [Labels] in
theorem bytes_drop {d : DataMem} {o : Nat} {bs : List UInt8} (h : BytesAt d (ad m₀ o) bs)
    (n : Nat) : BytesAt d (ad m₀ (o + n)) (bs.drop n) := fun i hi => by
  rw [List.length_drop] at hi
  rw [← ad_add, addr_add_addr, h (n + i) (by omega), List.getElem_drop]

omit [Labels] in
/-- A 16-byte value's halves. -/
theorem halves {d : DataMem} {o : Nat} {bs : List UInt8} (h : BytesAt d (ad m₀ o) bs) :
    BytesAt d (ad m₀ o) (bs.take 8) ∧ BytesAt d (ad m₀ (o + 8)) ((bs.drop 8).take 8) :=
  ⟨bytes_take h 8, bytes_take (bytes_drop h 8) 8⟩

omit [Labels] in
/-- **A 64-bit load from the frame**: the bytes there. -/
theorem regBytes_frame {N : Nat} {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {o : Nat} {bs : List UInt8} (hl : bs.length = 8)
    (h : BytesAt m.dmem (ad m₀ (fr + o)) bs) :
    regBytes ((Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret).load 0 o 8) = bs :=
  regBytes_load hl (by
    show BytesAt m.dmem (ad m₀ fr + BitVec.ofNat 64 o) bs
    rw [ad_add]
    exact h)

/-- **A 64-bit load from a path turn's node**: the bytes there. -/
theorem regBytes_node {O : Nat} {vs : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    {bs : List UInt8} (hl : bs.length = 8) (h : BytesAt m.dmem (ad m₀ (fr + O + o)) bs) :
    regBytes ((Env.ofMachine m (nodeR m₀ O) vs ret).load 1 o 8) = bs :=
  regBytes_load hl (by
    show BytesAt m.dmem (ad m₀ (fr + O) + BitVec.ofNat 64 o) bs
    rw [ad_add]
    exact h)

theorem eval_ptr1 {O : Nat} {vs : Nat → BitVec 64} {ret : BitVec 64} (q : Nat) :
    (Sym.ptr 1 q).eval (Env.ofMachine m (nodeR m₀ O) vs ret) = ad m₀ (fr + O + q) := by
  show ad m₀ (fr + O) + BitVec.ofInt 64 (q : Int) = _
  rw [BitVec.ofInt_natCast, ad_add]

/-- **A hash's first 16 bytes** copied from `184` to `592` by two 8-byte loads and stores. -/
theorem copy16 {N : Nat} {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) S m')
    (hN : 608 ≤ N) (h0 : ∀ t < 8, findWrite 0 (592 + t) S.mem = some (.load 0 184 8, t))
    (h1 : ∀ t < 8, findWrite 0 (600 + t) S.mem = some (.load 0 192 8, t)) {X : List UInt8}
    (hX : X.length = 32) (hb : BytesAt m.dmem (ad m₀ (fr + 184)) X) :
    BytesAt m'.dmem (ad m₀ (fr + 592)) (X.take 16) := by
  have w0 := frameWrite hm (o := 592) (by omega) h0
  have w1 := frameWrite hm (o := 600) (by omega) h1
  have hh := halves hb
  have l0 : (X.take 8).length = 8 := by simp [hX]
  have l1 : ((X.drop 8).take 8).length = 8 := by simp [hX]
  have r0 := regBytes_frame (N := N) (rest := rest) (vs := vs) (ret := ret) l0 hh.1
  have r1 := regBytes_frame (N := N) (rest := rest) (vs := vs) (ret := ret) (o := 192) l1
    (by rw [show fr + 192 = fr + 184 + 8 by omega]; exact hh.2)
  change BytesAt _ _ (regBytes (Env.load _ 0 184 8)) at w0
  change BytesAt _ _ (regBytes (Env.load _ 0 192 8)) at w1
  rw [r0] at w0
  rw [r1] at w1
  rw [show (16 : Nat) = 8 + 8 from rfl, List.take_add]
  exact BytesAt.append_ad w0 (by rw [l0, show fr + 592 + 8 = fr + 600 by omega]; exact w1)

/-- **A path step's children**, in the order the condition says: the stores of `cur`'s and the
sibling's 8-byte halves at `88`. -/
theorem childrenAt {N : Nat} {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) S m') (hN : 120 ≤ N) {c : SBool}
    {a0 a1 b0 b1 : Sym}
    (h0 : ∀ t < 8, findWrite 0 (88 + t) S.mem = some (.ite c a0 b0, t))
    (h1 : ∀ t < 8, findWrite 0 (96 + t) S.mem = some (.ite c a1 b1, t))
    (h2 : ∀ t < 8, findWrite 0 (104 + t) S.mem = some (.ite c b0 a0, t))
    (h3 : ∀ t < 8, findWrite 0 (112 + t) S.mem = some (.ite c b1 a1, t)) {cur sib : List UInt8}
    (hcur : regBytes (a0.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)) ++
      regBytes (a1.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)) = cur)
    (hsib : regBytes (b0.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)) ++
      regBytes (b1.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)) = sib) :
    BytesAt m'.dmem (ad m₀ (fr + 88))
      (if c.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) = true then cur ++ sib
        else sib ++ cur) := by
  have w0 := frameWrite hm (o := 88) (by omega) h0
  have w1 := frameWrite hm (o := 96) (by omega) h1
  have w2 := frameWrite hm (o := 104) (by omega) h2
  have w3 := frameWrite hm (o := 112) (by omega) h3
  subst hcur hsib
  have l := length_regBytes
  by_cases hc : c.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) = true <;>
    simp only [Sym.eval, hc, ite_true, ite_false, Bool.false_eq_true] at w0 w1 w2 w3 ⊢ <;>
    simp only [List.append_assoc] <;>
    refine BytesAt.append_ad w0 (BytesAt.append_ad (by simp only [l]; exact w1)
      (BytesAt.append_ad (by simp only [l]; exact w2) (by simp only [l]; exact w3)))

/-- **A node's address**: the stores of its low field (4 bytes), its high field (2 bytes and 1),
the type `3` and 8 zero bytes at `24`. -/
theorem addrAt {N : Nat} {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) S m') (hN : 40 ≤ N)
    {vlo vhi vb2 : Sym}
    (h1 : ∀ t < 4, findWrite 0 (24 + t) S.mem = some (vlo, t))
    (h2 : ∀ t < 2, findWrite 0 (28 + t) S.mem = some (vhi, t))
    (h3 : ∀ t < 1, findWrite 0 (30 + t) S.mem = some (vb2, t))
    (h4 : ∀ t < 1, findWrite 0 (31 + t) S.mem = some (.lit 3, t))
    (h5 : ∀ t < 8, findWrite 0 (32 + t) S.mem = some (.lit 0, t)) {lo : Nat} {hi : UInt32}
    (hlo : (vlo.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)).toNat = lo)
    (hhi : [UInt8.ofNat (vhi.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)).toNat,
      UInt8.ofNat ((vhi.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)).toNat / 256),
      UInt8.ofNat (vb2.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret)).toNat] =
      (u32Bytes hi).take 3) :
    BytesAt m'.dmem (ad m₀ (fr + 24)) (address (tweak 3 hi lo.toUInt32)) := by
  have p1 := frameWrite hm (o := 24) (by omega) h1
  have p2 := frameWrite hm (o := 28) (by omega) h2
  have p3 := frameWrite hm (o := 30) (by omega) h3
  have p4 := frameWrite hm (o := 31) (by omega) h4
  have p5 := frameWrite hm (o := 32) (by omega) h5
  rw [u32Bytes_byteOf _ hlo] at p1
  have e23 : (List.range 2).map (byteOf (vhi.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret))) ++
      (List.range 1).map (byteOf (vb2.eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret))) =
      (u32Bytes hi).take 3 := by
    rw [← hhi]
    simp [List.range_succ, byteOf]
  have e4 : (List.range 1).map (byteOf ((Sym.lit 3).eval
      (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret))) = [(3 : UInt8) ||| (0 : UInt8) <<< 5] := by
    show (List.range 1).map (byteOf (BitVec.ofNat 64 3)) = _
    decide
  have e5 : (List.range 8).map (byteOf ((Sym.lit 0).eval
      (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret))) = List.replicate 8 0 := by
    show (List.range 8).map (byteOf (BitVec.ofNat 64 0)) = _
    decide
  rw [e4] at p4
  rw [e5] at p5
  have p23 := BytesAt.append_ad p2 (by rw [List.length_map, List.length_range]; exact p3)
  rw [e23] at p23
  unfold address tweak
  exact BytesAt.append_ad (BytesAt.append_ad (BytesAt.append_ad p1 (by
      rw [length_u32Bytes]; exact p23))
    (by simp only [List.length_append, length_u32Bytes, List.length_take]; exact p4))
    (by simp only [List.length_append, length_u32Bytes, List.length_take,
      List.length_cons, List.length_nil]; exact p5)

end

/-! ## Values -/

public section

variable [Labels] {env : Env}

theorem add1_eval {s : Sym} {z : Nat} (h : s.eval env = BitVec.ofNat 64 z) :
    (Sym.bin .add .W64 s (.lit 1)).eval env = BitVec.ofNat 64 (z + 1) := by
  simp only [Sym.eval, BinOp.apply, h]
  show ((BitVec.ofNat 64 z).setWidth 64 + (BitVec.ofNat 64 1).setWidth 64).setWidth 64 = _
  simp only [BitVec.setWidth_eq, BitVec.ofNat_add_ofNat]

omit [Labels] in
theorem trunc_toNat (wd : Width) (x : BitVec 64) :
    (UnOp.apply .trunc wd x).toNat = x.toNat % 2 ^ wd.bits := by
  have : x.toNat % 2 ^ wd.bits < 2 ^ 64 := by
    have := x.isLt
    have := Nat.mod_le x.toNat (2 ^ wd.bits)
    omega
  show ((x.setWidth wd.bits).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt this

omit [Labels] in
theorem shr16_toNat (x : BitVec 64) :
    (BinOp.apply .shr .W32 x (BitVec.ofNat 64 16)).toNat = x.toNat % 2 ^ 32 / 2 ^ 16 := by
  show (((x.setWidth 32).ushiftRight (shiftCount .W32 (BitVec.ofNat 64 16))).setWidth 64).toNat =
    _
  rw [show shiftCount .W32 (BitVec.ofNat 64 16) = 16 from rfl, BitVec.toNat_setWidth,
    show (BitVec.setWidth 32 x).ushiftRight 16 = BitVec.setWidth 32 x >>> 16 from rfl,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

omit [Labels] in
theorem or_toNat (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 32) :
    (BinOp.apply .or .W32 x (BitVec.ofNat 64 c)).toNat = (x.toNat % 2 ^ 32 ||| c) := by
  have h1 : x.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have h2 : (x.toNat % 2 ^ 32 ||| c) < 2 ^ 32 := Nat.or_lt_two_pow h1 hc
  show ((x.setWidth 32 ||| (BitVec.ofNat 64 c).setWidth 32).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt hc]
  exact Nat.mod_eq_of_lt (by omega)

omit [Labels] in
/-- The address's `hi` bytes of a bottom node at level `z + 1`. -/
theorem hiBytes_bottom : ∀ z < 16,
    [UInt8.ofNat ((z + 1) % 2 ^ 16), UInt8.ofNat ((z + 1) % 2 ^ 16 / 256),
      UInt8.ofNat ((z + 1) % 2 ^ 32 / 2 ^ 16 % 2 ^ 8)] =
      (u32Bytes (layerHi 0 (z + 1).toUInt32)).take 3 := by
  decide +kernel

omit [Labels] in
/-- The address's `hi` bytes of a top node at level `z + 1`. -/
theorem hiBytes_top : ∀ z < 16,
    [UInt8.ofNat ((z + 1) % 2 ^ 16), UInt8.ofNat ((z + 1) % 2 ^ 16 / 256),
      UInt8.ofNat (((z + 1) % 2 ^ 32 ||| 8388608) % 2 ^ 32 / 2 ^ 16 % 2 ^ 8)] =
      (u32Bytes (layerHi 1 (z + 1).toUInt32)).take 3 := by
  decide +kernel

end

end NativeRustcX64.Xmss.XmssVerify
