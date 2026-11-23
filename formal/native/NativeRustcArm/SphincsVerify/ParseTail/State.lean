module

public import NativeRustcArm.SphincsVerify.ParseTail.Steps
public import NativeRustcArm.SphincsVerify.ParseTail.Exec
public import NativeRustcArm.SphincsVerify.SigMem

/-!
# The parse's tail: its states

The raw signature's parts (`wotsRaw`, `pathRaw`, the counters' loads `ctr`), the facts the tail
keeps throughout (`baseL`, from `AtParse16`: `facts_entry`), and the registers' values a block
leaves (`reg_ptr`, `reg_lit`, `reg_load`, `reg_same`, `reg_un`).
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Layer `l`'s raw chain values. -/
def wotsRaw (r : Run) (l : Nat) : List UInt8 := slice (sigBytes r.w) (sigLayerOff l + 4) 1024

/-- Layer `l`'s raw path. -/
def pathRaw (r : Run) (l : Nat) : List UInt8 :=
  slice (sigBytes r.w) (sigLayerOff l + 1028) (16 * layerHeights.getD l 0)

/-- Layer `l`'s counter as `ldr w` loads its raw (big-endian) bytes. -/
def ctr (r : Run) (l : Nat) : BitVec 64 :=
  BitVec.ofInt 64 (Int.ofBytes (slice (sigBytes r.w) (sigLayerOff l) 4))

/-- What the tail keeps throughout: the message, the raw signature, the key, the openings, the
randomizer. -/
def baseL (r : Run) : List (Nat × Nat × List UInt8) :=
  [(432, 32, r.msg), (468, 7740, sigBytes r.w), (8208, 32, pkBytes r.w),
    (16400, 4224, (r.sig.fors.map openingMem).flatten), (27808, 16, r.sig.randomizer)]

/-- The registers the tail keeps throughout: X19 the key, X20 the raw signature (until `b40`). -/
def K0 (r : Run) : List (XReg × BitVec 64) := [(.X19, r.off 8208), (.X20, r.off 468)]

end

/-- The side conditions of a step (`noW`, `disj`, `keptK`, `savedK` on the fact lists): stated on
the lists' offsets, lengths and registers only (`noW_eq`, ...), the lists unfolded, then decided
by the kernel on the block's literal summary. -/
macro "facts_side" : tactic => `(tactic| (
  simp only [noW_eq, disj_eq, keptK_eq, savedK_eq, shape, regsOf, baseL, K0, List.map_cons,
    List.map_nil, List.map_append, List.cons_append, List.nil_append] <;> decide +kernel))

public section

variable (r : Run)

theorem length_msg : r.msg.length = 32 := by
  simp [Run.msg, messageBytes, Native.Keccak.Proof.length_wordsBytes]

theorem length_pk : (pkBytes r.w).length = 32 := by
  simp [pkBytes, Native.Keccak.Proof.length_wordsBytes]

/-- **The tail's entry as facts.** -/
theorem facts_entry {m : MachineData} (h : r.AtParse16 m) :
    Facts r m (baseL r) [(.X19, r.off 8208), (.X20, r.off 468)] := by
  obtain ⟨hF, hmsg, hraw, hpk, hfors, hR, h19, h20⟩ := h
  refine ⟨hF, ?_, ⟨h19, h20, trivial⟩⟩
  simp only [BytesL, baseL, AllOf]
  exact ⟨⟨length_msg r, hmsg⟩, ⟨length_sigBytes r.w, hraw⟩, ⟨length_pk r, hpk⟩,
    ⟨r.length_forsMem, hfors⟩, ⟨r.length_randomizer, hR⟩, trivial⟩

/-- The raw signature's bytes `k .. k + n`. -/
theorem raw_at {m : MachineData} {L : List (Nat × Nat × List UInt8)} {K : List (XReg × BitVec 64)}
    (h : Facts r m L K) (hm : (468, 7740, sigBytes r.w) ∈ L) {k n : Nat} (hkn : k + n ≤ 7740) :
    BytesAt m.dmem (r.off (468 + k)) (slice (sigBytes r.w) k n) := by
  have := Parse.bytesAt_sub (h.2.1.mem hm).2 (k := k) (n := n) (by rw [length_sigBytes]; exact hkn)
  rwa [Parse.off_add] at this

theorem mem_raw {L : List (Nat × Nat × List UInt8)} (h : (468, 7740, sigBytes r.w) ∈ L)
    (a : Nat × Nat × List UInt8) : (468, 7740, sigBytes r.w) ∈ a :: L := List.mem_cons_of_mem _ h

theorem raw_baseL : (468, 7740, sigBytes r.w) ∈ baseL r := by simp [baseL]

theorem length_pathRaw {l : Nat} (hl : l < 3) :
    (pathRaw r l).length = 16 * layerHeights.getD l 0 :=
  length_slice (by have := sigLayerOff_le hl; rw [length_sigBytes]; omega)

/-- **Layer `l`'s raw path** in the frame's environment, at `468 + sigLayerOff l + 1028`. -/
theorem pathRaw_env {m : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) (hm : (468, 7740, sigBytes r.w) ∈ L)
    {l : Nat} (hl : l < 3) (vars : Nat → BitVec 64) :
    BytesAt (r.env m vars).mem0 ((r.env m vars).base 0 +
      BitVec.ofNat 64 (468 + sigLayerOff l + 1028)) (pathRaw r l) := by
  have := raw_at r h hm (k := sigLayerOff l + 1028) (n := 16 * layerHeights.getD l 0)
    (sigLayerOff_le hl)
  rw [← Nat.add_assoc] at this
  exact this

/-- **Layer `l`'s raw path copied** by a block to the frame's `o`. -/
theorem path_copy [NativeRustcArm.Host] {m m' : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) (hm : (468, 7740, sigBytes r.w) ∈ L)
    {S : SState} (hS : Match (r.env m) S m') {l o : Nat} (hl : l < 3)
    (ho : o + 16 * layerHeights.getD l 0 ≤ 29376)
    (hc : Parse.copies S.mem 0 o 0 (468 + sigLayerOff l + 1028) (16 * layerHeights.getD l 0) = true) :
    BytesAt m'.dmem (r.off o) (pathRaw r l) :=
  Parse.copy hS (r := 0) (B := r.base) (sz := 29376) rfl ho hc (length_pathRaw r hl)
    (pathRaw_env r h hm hl _)

/-- Layer `l`'s raw path copied by a block to the frame's `o`, as a fact. -/
theorem pathL [NativeRustcArm.Host] {m m' : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) (hm : (468, 7740, sigBytes r.w) ∈ L)
    {S : SState} (hS : Match (r.env m) S m') {l o n : Nat} (hl : l < 3)
    (hn : 16 * layerHeights.getD l 0 = n) (ho : o + n ≤ 29376)
    (hc : Parse.copies S.mem 0 o 0 (468 + sigLayerOff l + 1028) n = true) :
    BytesL r m'.dmem [(o, n, pathRaw r l)] := by
  subst hn
  exact ⟨⟨length_pathRaw r hl, path_copy r h hm hS hl ho hc⟩, trivial⟩

/-- Known bytes copied by a block to the frame's `o`, as a fact. -/
theorem copyL [NativeRustcArm.Host] {m m' : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) {o' n : Nat} {bs : List UInt8}
    (hm : (o', n, bs) ∈ L) {S : SState} (hS : Match (r.env m) S m') {o : Nat}
    (ho : o + n ≤ 29376) (hc : Parse.copies S.mem 0 o 0 o' n = true) :
    BytesL r m'.dmem [(o, n, bs)] :=
  ⟨⟨(h.2.1.mem hm).1, Parse.copy hS (r := 0) (B := r.base) (sz := 29376) rfl ho hc
    (h.2.1.mem hm).1 (h.2.1.mem hm).2⟩, trivial⟩

/-- A block's 8-byte store of the frame's address `a` at `o`, as a fact. -/
theorem storeL [NativeRustcArm.Host] {m m' : MachineData} {S : SState} (hS : Match (r.env m) S m')
    {o a : Nat} (ho : o + 8 ≤ 29376)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.ptr 0 a, i)) :
    BytesL r m'.dmem [(o, 8, wordBytes (r.addr a))] := by
  have := hS.bytesAt_write (r := 0) (o := o) (n := 8) (b := r.base) (sz := 29376) rfl ho hw
  rw [bytes_word, ptr_eval] at this
  exact ⟨⟨NativeRustc.length_wordBytes _, this⟩, trivial⟩

/-- A block's 4-byte store of a register holding `rev` of `v` at `o`, as a fact: `v`'s low word
big-endian. -/
theorem store4L [NativeRustcArm.Host] {m m' : MachineData} {S : SState} (hS : Match (r.env m) S m')
    {x : XReg} {v : BitVec 64} (hx : (m.regs.getXReg x).toBitVec = UnOp.apply .rev .W32 v)
    {o : Nat} (ho : o + 4 ≤ 29376) (hw : ∀ i < 4, findWrite 0 (o + i) S.mem = some (.reg x, i)) :
    BytesL r m'.dmem [(o, 4, be32 (UInt32.ofNat v.toNat))] := by
  have := hS.bytesAt_write (r := 0) (o := o) (n := 4) (b := r.base) (sz := 29376) rfl ho hw
  have he : (Sym.reg x).eval (r.env m) = UnOp.apply .rev .W32 v := hx
  rw [he, bytes_rev32] at this
  exact ⟨⟨by simp [be32], this⟩, trivial⟩

/-- Bytes then bytes, at frame offsets. -/
theorem bytesAt_cat {d : DataMem} {o n : Nat} {xs ys : List UInt8} (hx : BytesAt d (r.off o) xs)
    (hl : xs.length = n) (hy : BytesAt d (r.off (o + n)) ys) : BytesAt d (r.off o) (xs ++ ys) :=
  bytesAt_append hx (by rw [hl, Parse.off_add]; exact hy)

variable [NativeRustcArm.Host] {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}

theorem reg_ptr (hm : Match (r.env m vars) S m') {x : XReg} {a : Nat}
    (h : S.reg x = some (.ptr 0 (a : Int))) : (m'.regs.getXReg x).toBitVec = r.off a :=
  (hm.regs x _ h).trans (ptr_eval r m vars a)

theorem reg_lit (hm : Match (r.env m vars) S m') {x : XReg} {n : Nat}
    (h : S.reg x = some (.lit n)) : (m'.regs.getXReg x).toBitVec = BitVec.ofNat 64 n :=
  hm.regs x _ h

theorem reg_same (hm : Match (r.env m vars) S m') {x y : XReg} (h : S.reg x = some (.reg y)) :
    (m'.regs.getXReg x).toBitVec = (m.regs.getXReg y).toBitVec :=
  hm.regs x _ h

theorem reg_un (hm : Match (r.env m vars) S m') {x y : XReg} {op : UnOp} {w : RegWidth}
    (h : S.reg x = some (.un op w (.reg y))) :
    (m'.regs.getXReg x).toBitVec = op.apply w (m.regs.getXReg y).toBitVec :=
  hm.regs x _ h

theorem reg_load (hm : Match (r.env m vars) S m') {x : XReg} {o k : Nat}
    (h : S.reg x = some (.load 0 o k)) {bs : List UInt8} (hl : bs.length = k)
    (hb : BytesAt m.dmem (r.off o) bs) :
    (m'.regs.getXReg x).toBitVec = BitVec.ofInt 64 (Int.ofBytes bs) :=
  (hm.regs x _ h).trans (Env.load_of_bytesAt hl hb)

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
