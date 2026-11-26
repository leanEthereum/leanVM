module

public import NativeRustcX64.Code.Sphincs.SphincsVerify.Names

public import NativeRustcX64.SphincsVerify.Calls
public import NativeRustcX64.SphincsVerify.Epilogue
public import NativeRustcX64.SphincsVerify.Bswap
public import NativeRustcX64.SphincsVerify.Tree.Model
public import NativeRustcX64.SphincsVerify.Tree.Exec

/-!
# The tree region's glue (x86-64)

Bytes in the frame: lists' parts (`bytesAt_cat`, `bytesAt_sub`, `bytesAt_zero`), a block's
writes (`write_eval`), loads of known bytes (`bytes_load`, `load_word`, `load_lo`, `load_hi`),
16-byte values by their words (`write_pair`), a hasher's parts (`hbytes_parts`,
`hbytes_of_parts`). What every state of the region keeps (`Keep`: the inputs and the layer loop's
spills the region reads; `Base`: with the layer, the frame and RBP hasher B), through a block
(`Base.of_match`, by `keepW`) and a call above the spills (`Base.of_call`). The blocks' places
(`hb<k>`) and labels (`lbl_<n>`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

/-! ## Lists of bytes -/

theorem addr_add' (b : BitVec 64) (o i : Nat) :
    b + BitVec.ofNat 64 o + BitVec.ofNat 64 i = b + BitVec.ofNat 64 (o + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_append_left {d : DataMem} {a : BitVec 64} {p q : List UInt8}
    (h : BytesAt d a (p ++ q)) : BytesAt d a p := fun i hi ↦ by
  rw [h i (by simp; omega), List.getElem_append_left hi]

theorem bytesAt_append_right {d : DataMem} {a : BitVec 64} {p q : List UInt8}
    (h : BytesAt d a (p ++ q)) : BytesAt d (a + BitVec.ofNat 64 p.length) q := fun i hi ↦ by
  rw [addr_add', h (p.length + i) (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem bytesAt_append {d : DataMem} {a : BitVec 64} {p q : List UInt8}
    (hp : BytesAt d a p) (hq : BytesAt d (a + BitVec.ofNat 64 p.length) q) :
    BytesAt d a (p ++ q) := fun i hi ↦ by
  by_cases h : i < p.length
  · rw [hp i h, List.getElem_append_left h]
  · have := hq (i - p.length) (by simp at hi; omega)
    rw [addr_add', show p.length + (i - p.length) = i by omega] at this
    rw [this, List.getElem_append_right (by omega)]

theorem rep_sub {n i k : Nat} {a : UInt8} (h : i + k ≤ n) :
    ((List.replicate n a).drop i).take k = List.replicate k a := by
  rw [List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]

section
variable {r : Run}

/-- Two adjacent byte ranges of the frame. -/
theorem bytesAt_cat {d : DataMem} {o n : Nat} {p q : List UInt8} (hn : p.length = n)
    (hp : BytesAt d (r.off o) p) (hq : BytesAt d (r.off (o + n)) q) : BytesAt d (r.off o) (p ++ q) :=
  bytesAt_append hp (by rw [hn, Run.off_add]; exact hq)

/-- Bytes inside known bytes. -/
theorem bytesAt_sub {d : DataMem} {o : Nat} {bs : List UInt8} (h : BytesAt d (r.off o) bs)
    (i n : Nat) : BytesAt d (r.off (o + i)) ((bs.drop i).take n) := fun j hj ↦ by
  simp only [List.length_take, List.length_drop] at hj
  rw [Run.off_add, Nat.add_assoc, ← Run.off_add, h (i + j) (by omega)]
  simp [List.getElem_take, List.getElem_drop]

/-- Zeros inside zeros. -/
theorem bytesAt_zero {d : DataMem} {o n : Nat} (h : BytesAt d (r.off o) (List.replicate n 0))
    {i k : Nat} (hik : i + k ≤ n) : BytesAt d (r.off (o + i)) (List.replicate k 0) := by
  have := bytesAt_sub h i k
  rwa [rep_sub hik] at this

/-- **The parts of a hasher's bytes** with a zero state, `T` buffered, `buf_len` `n`. -/
theorem hbytes_parts {d : DataMem} {o : Nat} {T : List UInt8} {n : Nat}
    (h : BytesAt d (r.off o) (List.replicate 200 0 ++ (T ++ (List.replicate (136 - T.length) 0 ++
      wordBytes n.toUInt64)))) (hT : T.length ≤ 136) :
    BytesAt d (r.off o) (List.replicate 200 0) ∧ BytesAt d (r.off (o + 200)) T ∧
      BytesAt d (r.off (o + 200 + T.length)) (List.replicate (136 - T.length) 0) ∧
      BytesAt d (r.off (o + 336)) (wordBytes n.toUInt64) := by
  have h1 := bytesAt_append_right h
  have h2 := bytesAt_append_right h1
  have h3 := bytesAt_append_right h2
  simp only [List.length_replicate, Run.off_add] at h1 h2 h3
  refine ⟨bytesAt_append_left h, bytesAt_append_left h1, bytesAt_append_left h2, ?_⟩
  rwa [show o + 200 + T.length + (136 - T.length) = o + 336 by omega] at h3

/-- **A hasher's bytes from its parts.** -/
theorem hbytes_of_parts {d : DataMem} {o : Nat} {T : List UInt8} {n : Nat} (hT : T.length ≤ 136)
    (h0 : BytesAt d (r.off o) (List.replicate 200 0)) (h1 : BytesAt d (r.off (o + 200)) T)
    (h2 : BytesAt d (r.off (o + 200 + T.length)) (List.replicate (136 - T.length) 0))
    (h3 : BytesAt d (r.off (o + 336)) (wordBytes n.toUInt64)) :
    BytesAt d (r.off o) (List.replicate 200 0 ++ (T ++ (List.replicate (136 - T.length) 0 ++
      wordBytes n.toUInt64))) := by
  refine bytesAt_cat (List.length_replicate ..) h0 (bytesAt_cat rfl h1 (bytesAt_cat
    (List.length_replicate ..) h2 ?_))
  rwa [show o + 200 + T.length + (136 - T.length) = o + 336 by omega]

end

/-- The bytes of a hasher whose state is zero and whose buffer holds `T`, `buf_len` `n`. -/
@[expose] def hbytes (T : List UInt8) (n : Nat) : List UInt8 :=
  List.replicate 200 0 ++ (T ++ (List.replicate (136 - T.length) 0 ++ wordBytes n.toUInt64))

theorem length_hbytes {T : List UInt8} (hT : T.length ≤ 136) (n : Nat) :
    (hbytes T n).length = 344 := by
  simp only [hbytes, List.length_append, List.length_replicate, length_wordBytes]
  omega

/-! ## The executor's frame -/

section
variable {r : Run} [Labels]

theorem regs0 (m : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (r.env m vars ret).regions[0]? = some (r.base, frameRegion) := rfl

/-- A region pointer of the frame's environment is the frame's byte. -/
theorem eval_ptr {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (r.env m vars ret) = r.off o := by
  show r.base + BitVec.ofInt 64 (o : Int) = r.base + BitVec.ofNat 64 o
  simp

/-- **A write of `n` bytes** whose value evaluates to `w`. -/
theorem write_eval {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m vars ret) S m') {o n : Nat} {v : Sym} {w : BitVec 64}
    (hle : o + n ≤ frameRegion)
    (hw : ∀ i < n, findWrite 0 (o + i) S.mem = some (v, i)) (hv : v.eval (r.env m vars ret) = w)
    {bs : List UInt8} (hbs : (List.range n).map (byteOf w) = bs) : BytesAt m'.dmem (r.off o) bs :=
  hbs ▸ hv ▸ hm.bytesAt_write (regs0 m vars ret) hle hw

/-- The bytes of a load of known bytes. -/
theorem bytes_load {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {o n : Nat}
    {bs : List UInt8} (h : BytesAt m.dmem (r.off o) bs) (hl : bs.length = n) (hn : n ≤ 8) :
    (List.range n).map (byteOf ((r.env m vars ret).load 0 o n)) = bs := by
  subst hl
  apply List.ext_getElem (by simp)
  intro t h1 h2
  rw [List.getElem_map, List.getElem_range, byteOf_load h2 hn]
  show (m.dmem.get? (r.base + BitVec.ofNat 64 (o + t))).getD 0 = _
  rw [show r.base + BitVec.ofNat 64 (o + t) = r.off o + BitVec.ofNat 64 t by
    rw [Run.off_add]; rfl, h t h2]
  rfl

/-- A load of a word's bytes is the word. -/
theorem load_word {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    {v : UInt64} (h : r.WordAt m o v) : (r.env m vars ret).load 0 o 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (bs := wordBytes v) (length_wordBytes v)
    (by show BytesAt m.dmem (r.base + BitVec.ofNat 64 o) _; exact h)]
  exact ofInt_ofBytes_wordBytes v

/-- A word of known bytes, as loaded. -/
theorem load_sub {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    {bs : List UInt8} (h : BytesAt m.dmem (r.off o) bs) {i : Nat} {v : UInt64}
    (hv : (bs.drop i).take 8 = wordBytes v) : (r.env m vars ret).load 0 (o + i) 8 = v.toBitVec := by
  apply load_word
  show BytesAt m.dmem (r.off (o + i)) (wordBytes v)
  rw [← hv]
  exact bytesAt_sub h i 8

/-- A 16-byte value's low 8 bytes, as loaded. -/
theorem load_lo {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    {v : List UInt8} (h : BytesAt m.dmem (r.off o) v) (hl : v.length = 16) :
    (List.range 8).map (byteOf ((r.env m vars ret).load 0 o 8)) = v.take 8 := by
  rw [← List.take_append_drop 8 v] at h
  exact bytes_load (bytesAt_append_left h) (by simp [hl]) (by decide)

/-- A 16-byte value's high 8 bytes, as loaded. -/
theorem load_hi {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    {v : List UInt8} (h : BytesAt m.dmem (r.off o) v) (hl : v.length = 16) :
    (List.range 8).map (byteOf ((r.env m vars ret).load 0 (o + 8) 8)) = v.drop 8 := by
  rw [← List.take_append_drop 8 v] at h
  have h2 := bytesAt_append_right h
  rw [List.length_take, Nat.min_eq_left (by omega), Run.off_add] at h2
  exact bytes_load h2 (by simp [hl]) (by decide)

/-- **A 16-byte value** written as two 8-byte halves. -/
theorem write_16 {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m vars ret) S m') {o : Nat} (ho : o + 16 ≤ frameRegion) {a : List UInt8}
    (ha : a.length = 16) {v₀ v₁ : Sym}
    (h₀ : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v₀, i))
    (h₁ : ∀ i < 8, findWrite 0 (o + 8 + i) S.mem = some (v₁, i))
    (e₀ : (List.range 8).map (byteOf (v₀.eval (r.env m vars ret))) = a.take 8)
    (e₁ : (List.range 8).map (byteOf (v₁.eval (r.env m vars ret))) = a.drop 8) :
    BytesAt m'.dmem (r.off o) a := by
  rw [← List.take_append_drop 8 a]
  exact bytesAt_cat (by simp [ha]) (write_eval hm (by omega) h₀ rfl e₀)
    (write_eval hm (by omega) h₁ rfl e₁)

omit [Labels] in
theorem regIs_toNat {m : MachineData} {x : Reg64} {n : Nat} (h : reg m x = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) : (reg m x).toNat = n := by
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The pc after a conditional branch the block's condition decides. -/
theorem pc_cond {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    {b : Bool} (h : PcOk env (.cond c l) next st) (hc : c.eval env = b) :
    st.pc = if b then Labels.label l else next := by
  rw [← hc]; exact h

omit [Labels] in
theorem allOf_append {α : Type} {P : α → Prop} : ∀ {l₁ l₂ : List α}, AllOf P l₁ → AllOf P l₂ →
    AllOf P (l₁ ++ l₂)
  | [], _, _, h => h
  | _ :: _, _, ⟨h, h₁⟩, h₂ => ⟨h, allOf_append h₁ h₂⟩

omit [Labels] in
theorem regIs_of_saved {x : Reg64} (hx : calleeSaved x = true) {m m' : MachineData}
    {v : BitVec 64} (h : Run.RegIs m x v) (hS : Saved m m') : Run.RegIs m' x v := by
  unfold Run.RegIs reg; rw [hS.1 x hx]; exact h

end

/-! ## What the region keeps -/

section
variable (r : Run)

/-- **The inputs and the layer loop's spills the region reads**: the tree's word (`88`), the
height (`160`), the next layer and its offset (`200`, `208`), the key's leaf (`216`), the index
(`552`). -/
@[expose] def Keep (l : Nat) (m : MachineData) : Prop :=
  r.Inputs m ∧ BytesAt m.dmem (r.off 88) (be64 (r.key l).tree) ∧
    r.WordAt m 168 (heightOf l).toUInt64 ∧ r.WordAt m 192 (l + 1).toUInt64 ∧
    r.WordAt m 200 (4656 + 1028 * (l + 1)).toUInt64 ∧ r.WordAt m 208 (r.key l).leaf.toUInt64 ∧
    r.WordAt m 552 r.idx

/-- **Every state of the region**: the layer, the frame, `Keep`, RBP hasher B. -/
@[expose] def Base [Labels] (l : Nat) (m : MachineData) : Prop :=
  l < 3 ∧ r.Frame m ∧ Keep r l m ∧ Run.RegIs m .rbp (r.off 560) ∧
    Run.RegIs m .r14 (Labels.label "memcpy").toBitVec

end

/-- No write of a block reaches the bytes `Keep` holds. -/
@[expose] def keepW (S : SState) : Bool :=
  Run.noWriteIn S 88 8 && Run.noWriteIn S 112 32 && Run.noWriteIn S 168 8 &&
    Run.noWriteIn S 192 24 && Run.noWriteIn S 552 8 && Run.noWriteIn S 12780 7740

section
variable {r : Run} [Labels]

omit [Labels] in
theorem length_pkBytes' : r.pkB.length = 32 := r.hpk

omit [Labels] in
theorem length_sigMem' : (sigMem r.sig).length = 7740 := SigMemBytes.length_sigMem r.sigB r.hsig

/-- **`Keep` after a block** that writes none of its bytes. -/
theorem Keep.of_match (hpre : r.Pre) {l : Nat} {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hK : Keep r l m) (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hk : keepW S = true) : Keep r l m' := by
  simp only [keepW, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨h88, h112⟩, h160⟩, h200⟩, h568⟩, h20540⟩ := hk
  obtain ⟨⟨hpk, hsig⟩, hT, hH, hN, hO, hL, hI⟩ := hK
  have hw : ∀ v : UInt64, (wordBytes v).length = 8 := length_wordBytes
  have k := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn S o bs.length = true) ↦
    r.bytesAt_kept hpre hm hwf ho h hn
  have n200 : ∀ o, 192 ≤ o → o + 8 ≤ 216 → Run.noWriteIn S o 8 = true := fun o h1 h2 ↦ by
    simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h200 ⊢
    intro w hw'
    rcases h200 w hw' with ⟨h0, h | h⟩ | h
    · exact Or.inl ⟨h0, Or.inl (by omega)⟩
    · exact Or.inl ⟨h0, Or.inr (by omega)⟩
    · exact Or.inr h
  refine ⟨⟨k (by rw [length_pkBytes']; decide) hpk (by rw [length_pkBytes']; exact h112),
    k (by rw [length_sigMem']; decide) hsig (by rw [length_sigMem']; exact h20540)⟩,
    k (by simp [be64]) hT (by simp only [be64, List.length_cons, List.length_nil]; exact h88),
    k (by rw [hw]; decide) hH (by rw [hw]; exact h160),
    k (by rw [hw]; decide) hN (by rw [hw]; exact n200 192 (by decide) (by decide)),
    k (by rw [hw]; decide) hO (by rw [hw]; exact n200 200 (by decide) (by decide)),
    k (by rw [hw]; decide) hL (by rw [hw]; exact n200 208 (by decide) (by decide)),
    k (by rw [hw]; decide) hI (by rw [hw]; exact h568)⟩

/-- **`Keep` after a call** that changed the frame's bytes `a .. a + n` between the spills and the
parsed signature. -/
theorem Keep.of_call (hpre : r.Pre) {l : Nat} {m m' : MachineData} (hc : r.AtCall m) {a n N : Nat}
    (ha : 560 ≤ a) (han : a + n ≤ 12780) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (hK : Keep r l m) : Keep r l m' := by
  obtain ⟨⟨hpk, hsig⟩, hT, hH, hN', hO, hL, hI⟩ := hK
  have hw : ∀ v : UInt64, (wordBytes v).length = 8 := length_wordBytes
  have k := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (hd : o + bs.length ≤ a ∨ a + n ≤ o) (h : BytesAt m.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc (by omega) hN hout ho hd h
  refine ⟨⟨k (by rw [length_pkBytes']; decide) (by rw [length_pkBytes']; omega) hpk,
    k (by rw [length_sigMem']; decide) (by omega) hsig⟩,
    k (by simp [be64]) (by simp [be64]; omega) hT,
    k (by rw [hw]; decide) (by rw [hw]; omega) hH, k (by rw [hw]; decide) (by rw [hw]; omega) hN',
    k (by rw [hw]; decide) (by rw [hw]; omega) hO, k (by rw [hw]; decide) (by rw [hw]; omega) hL,
    k (by rw [hw]; decide) (by rw [hw]; omega) hI⟩

/-- **`Base` after a block** that keeps RSP and RBP and writes neither the saved registers nor
`Keep`'s bytes. -/
theorem Base.of_match (hpre : r.Pre) {l : Nat} {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hB : Base r l m) (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 0))
    (hw : Run.frameWrites S = true) (hk : keepW S = true) (hbp : S.reg .rbp = some (.ptr 0 560))
    (h14 : S.reg .r14 = some (.label "memcpy") := by rfl) :
    Base r l m' :=
  ⟨hB.1, Run.Frame.of_match r hpre hB.2.1 hm hwf hsp hw, hB.2.2.1.of_match hpre hm hwf hk,
    (hm.regs _ _ hbp).trans (eval_ptr 560), hm.regs .r14 _ h14⟩

/-- **At a call after a block** from a state of the region. -/
theorem Base.atCall (hpre : r.Pre) {l : Nat} {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hB : Base r l m) (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 (-8)))
    (hw : Run.frameWrites S = true) : r.AtCall m' :=
  Run.AtCall.of_match r hpre hB.2.1 hm hwf hsp hw

/-- **`Base` after a call** from a block's end (`AtCall`, `Keep` and RBP there). -/
theorem Base.of_call (hpre : r.Pre) {l : Nat} {m m' : MachineData} (hl : l < 3) (hc : r.AtCall m)
    (hK : Keep r l m) (hbp : Run.RegIs m .rbp (r.off 560))
    (h14 : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec) (hS : Saved m m')
    (hsp : rspOf m' = rspOf m + 8#64) {a n N : Nat} (ha : 560 ≤ a) (han : a + n ≤ 12780)
    (hN : N ≤ finalizeStack) (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) :
    Base r l m' :=
  ⟨hl, r.frame_of_call hpre hc hS hsp (by omega) hN hout, hK.of_call hpre hc ha han hN hout,
    regIs_of_saved rfl hbp hS, regIs_of_saved rfl h14 hS⟩

end

/-! ## Places and labels -/

section
variable [Host] {k : Nat}

theorem placed_infix {b : List Directive} {j : Nat} (hp : Placed code k) (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

theorem pc_after {j j' : Nat} {ds : List Directive} (h : j + ds.length = j') :
    Host.addrOf (k + j + ds.length) = Host.addrOf (k + j') := by
  rw [Nat.add_assoc, h]

theorem hb151 (hp : Placed code k) : b142.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b142Offset) :=
  placed_infix hp b142_in_code (List.cons_ne_nil _ _)
theorem hb152 (hp : Placed code k) : b143.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b143Offset) :=
  placed_infix hp b143_in_code (List.cons_ne_nil _ _)
theorem hb153 (hp : Placed code k) : b144.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b144Offset) :=
  placed_infix hp b144_in_code (List.cons_ne_nil _ _)
theorem hb154 (hp : Placed code k) : b145.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b145Offset) :=
  placed_infix hp b145_in_code (List.cons_ne_nil _ _)
theorem hb155 (hp : Placed code k) : b146.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b146Offset) :=
  placed_infix hp b146_in_code (List.cons_ne_nil _ _)
theorem hb156 (hp : Placed code k) : b147.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b147Offset) :=
  placed_infix hp b147_in_code (List.cons_ne_nil _ _)
theorem hb157 (hp : Placed code k) : b148.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b148Offset) :=
  placed_infix hp b148_in_code (List.cons_ne_nil _ _)
theorem hb158 (hp : Placed code k) : b149.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b149Offset) :=
  placed_infix hp b149_in_code (List.cons_ne_nil _ _)
theorem hb159 (hp : Placed code k) : b150.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b150Offset) :=
  placed_infix hp b150_in_code (List.cons_ne_nil _ _)
theorem hb160 (hp : Placed code k) : b151.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b151Offset) :=
  placed_infix hp b151_in_code (List.cons_ne_nil _ _)
theorem hb161 (hp : Placed code k) : b152.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset) :=
  placed_infix hp b152_in_code (List.cons_ne_nil _ _)
theorem hb162 (hp : Placed code k) : b153.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b153Offset) :=
  placed_infix hp b153_in_code (List.cons_ne_nil _ _)
theorem hb165 (hp : Placed code k) : b156.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b156Offset) :=
  placed_infix hp b156_in_code (List.cons_ne_nil _ _)
theorem hb166 (hp : Placed code k) : b157.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b157Offset) :=
  placed_infix hp b157_in_code (List.cons_ne_nil _ _)
theorem hb167 (hp : Placed code k) : b158.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b158Offset) :=
  placed_infix hp b158_in_code (List.cons_ne_nil _ _)
theorem hb168 (hp : Placed code k) : b159.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b159Offset) :=
  placed_infix hp b159_in_code (List.cons_ne_nil _ _)
theorem hb169 (hp : Placed code k) : b160.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b160Offset) :=
  placed_infix hp b160_in_code (List.cons_ne_nil _ _)
theorem hb170 (hp : Placed code k) : b161.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b161Offset) :=
  placed_infix hp b161_in_code (List.cons_ne_nil _ _)
theorem hb173 (hp : Placed code k) : b164.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b164Offset) :=
  placed_infix hp b164_in_code (List.cons_ne_nil _ _)
theorem hb174 (hp : Placed code k) : b165.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b165Offset) :=
  placed_infix hp b165_in_code (List.cons_ne_nil _ _)
theorem hb175 (hp : Placed code k) : b166.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b166Offset) :=
  placed_infix hp b166_in_code (List.cons_ne_nil _ _)
theorem hb176 (hp : Placed code k) : b167.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b167Offset) :=
  placed_infix hp b167_in_code (List.cons_ne_nil _ _)
theorem hb177 (hp : Placed code k) : b168.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b168Offset) :=
  placed_infix hp b168_in_code (List.cons_ne_nil _ _)
theorem hb178 (hp : Placed code k) : b169.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b169Offset) :=
  placed_infix hp b169_in_code (List.cons_ne_nil _ _)
theorem hb179 (hp : Placed code k) : b170.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b170Offset) :=
  placed_infix hp b170_in_code (List.cons_ne_nil _ _)
theorem hb182 (hp : Placed code k) : b173.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b173Offset) :=
  placed_infix hp b173_in_code (List.cons_ne_nil _ _)
theorem hb183 (hp : Placed code k) : b174.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b174Offset) :=
  placed_infix hp b174_in_code (List.cons_ne_nil _ _)
theorem hb184 (hp : Placed code k) : b175.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b175Offset) :=
  placed_infix hp b175_in_code (List.cons_ne_nil _ _)
theorem hb185 (hp : Placed code k) : b176.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b176Offset) :=
  placed_infix hp b176_in_code (List.cons_ne_nil _ _)
theorem hb186 (hp : Placed code k) : b177.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b177Offset) :=
  placed_infix hp b177_in_code (List.cons_ne_nil _ _)
theorem hb187 (hp : Placed code k) : b178.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b178Offset) :=
  placed_infix hp b178_in_code (List.cons_ne_nil _ _)
theorem hb188 (hp : Placed code k) : b179.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b179Offset) :=
  placed_infix hp b179_in_code (List.cons_ne_nil _ _)
theorem hb190 (hp : Placed code k) : b181.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b181Offset) :=
  placed_infix hp b181_in_code (List.cons_ne_nil _ _)
theorem hb191 (hp : Placed code k) : b182.IsInfixAt Host.prog (k + NativeRustcX64.Sphincs.SphincsVerify.b182Offset) :=
  placed_infix hp b182_in_code (List.cons_ne_nil _ _)

theorem lbl_65 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_57 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_57_at
theorem lbl_67 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_59 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b156Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_59_at
theorem lbl_68 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_60 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b158Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_60_at
theorem lbl_72 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_64 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b157Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_64_at
theorem lbl_73 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_65 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b164Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_65_at
theorem lbl_74 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_66 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b167Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_66_at
theorem lbl_78 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_70 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b166Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_70_at
theorem lbl_79 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_71 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b173Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_71_at
theorem lbl_82 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_74 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b181Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_74_at
theorem lbl_38 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_30 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b95Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_30_at
theorem lbl_85 (hp : Placed code k) : Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_77 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b187Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_77_at

end

end

end NativeRustcX64.SphincsVerifyProof.Tree
