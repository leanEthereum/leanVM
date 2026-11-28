module

public import NativeRustcX64.SphincsVerify.Chains.Steps

/-!
# The chains' loop on x86-64: blocks off the frame's regions

`b107` and `b108` index the frame by the chain: their symbolic states have the indexed bytes as
regions of their own, region 0 a prefix of the frame. What such a block changes
(`sameOutside_region`, `written_three`), keeps (`reg_same`, `KeepRest.of_change`,
`Frame.of_change'`); the frame's addresses (`off_add_ofInt`, `shl4`); the chain's word and digit
(`bytes_chainWord`, `zext8`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

public section

theorem off_add_ofInt {r : Run} (a : Nat) {c : Int} {b : Nat} (h : (a : Int) + c = b) :
    r.off a + BitVec.ofInt 64 c = r.off b := by
  unfold Run.off
  have ha : BitVec.ofNat 64 a = BitVec.ofInt 64 (a : Int) := by simp
  have hb : BitVec.ofNat 64 b = BitVec.ofInt 64 (b : Int) := by simp
  rw [BitVec.add_assoc, ha, hb, ← BitVec.ofInt_add, h]

theorem off_zero' (r : Run) : r.off 0 = r.base := by simp [Run.off]

theorem shl4 {i : Nat} (hi : i < 2 ^ 59) :
    BinOp.apply .shl .W64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * i) := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := by decide
  simp only [BinOp.apply, low_W64, ext_W64, hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  congr 1
  omega

/-- The 32-bit `i << 24` stored is `i` big-endian. -/
theorem bytes_chainWord {i : Nat} (hi : i < 64) :
    (List.range 4).map (byteOf (BinOp.apply .shl .W32 (BitVec.ofNat 64 i) (BitVec.ofNat 64 24))) =
      be32 i.toUInt32 := by
  interval_cases i <;> decide

/-- A byte zero-extended. -/
theorem zext8 {n : Nat} (hn : n < 256) :
    UnOp.apply (.zext .W8) .W32 (BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h8 : Width.W8.bits = 8 := rfl
  have h32 : Width.W32.bits = 32 := rfl
  simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h8, h32]
  omega

variable [Labels] {r : Run}

/-- **A block writing only region `k`** changes only its bytes. -/
theorem sameOutside_region {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    (hwf : env.WF) {k : Nat} {a : BitVec 64} {n : Nat} (hk : env.regions[k]? = some (a, n))
    (hall : S.mem.all (fun w ↦ w.r == k && decide (w.off + w.n ≤ n)) = true) :
    SameOutside env.mem0 m'.dmem (InRange a n) := by
  refine SameOutside.mono (hm.sameOutside hwf) fun p ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ ?_
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
  obtain ⟨hr, hn⟩ := hall w hw
  rw [hr, hk] at hb
  cases hb
  have := hwf.noWrap k a n hk
  rw [Sym.inRange_iff this]
  omega

/-- **A block writing region 0 (the frame from its base) at `a .. a + n`, `a' .. a' + n'` and
`a'' .. a'' + n''`** changes only those bytes. -/
theorem written_three {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    (hwf : env.WF) (hpre : r.Pre) {n0 : Nat} (h0 : env.regions[0]? = some (r.base, n0))
    {a n a' n' a'' n'' : Nat} (ha : a + n ≤ 21624) (ha' : a' + n' ≤ 21624)
    (ha'' : a'' + n'' ≤ 21624)
    (hall : S.mem.all (fun w ↦ w.r == 0 && ((decide (a ≤ w.off) && decide (w.off + w.n ≤ a + n)) ||
      (decide (a' ≤ w.off) && decide (w.off + w.n ≤ a' + n')) ||
      (decide (a'' ≤ w.off) && decide (w.off + w.n ≤ a'' + n'')))) = true) :
    SameOutside env.mem0 m'.dmem (fun p ↦ InRange (r.off a) n p ∨ InRange (r.off a') n' p ∨
      InRange (r.off a'') n'' p) := by
  have hb := r.base_toNat hpre
  refine SameOutside.mono (hm.sameOutside hwf) fun p ⟨w, hw, b, sz, hbw, h1, h2⟩ ↦ ?_
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hall
  obtain ⟨hr, hn⟩ := hall w hw
  rw [hr, h0] at hbw
  cases hbw
  have ho := r.off_toNat hpre (a := a) (by omega)
  have ho' := r.off_toNat hpre (a := a') (by omega)
  have ho'' := r.off_toNat hpre (a := a'') (by omega)
  rcases hn with (⟨g1, g2⟩ | ⟨g1, g2⟩) | ⟨g1, g2⟩
  · left
    rw [Sym.inRange_iff (by rw [ho]; omega), ho]
    omega
  · right; left
    rw [Sym.inRange_iff (by rw [ho']; omega), ho']
    omega
  · right; right
    rw [Sym.inRange_iff (by rw [ho'']; omega), ho'']
    omega

/-- A register a block keeps, in the environment of the state it starts from. -/
theorem reg_same {m m' : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m regions vars ret) S m') {y : Reg64} (h : S.reg y = some (.reg y)) :
    m'.regs.get64 y = m.regs.get64 y :=
  hm.regs y _ h

omit [Labels] in
/-- **A change of the frame's bytes** where `R` says keeps the kept bytes and registers, where `R`
misses them. -/
theorem KeepRest.of_change {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {m m' : MachineData} (hK : KeepRest r l x E m)
    {R : BitVec 64 → Prop} (hout : SameOutside m.dmem m'.dmem R)
    (hR : ∀ o, o < 21624 → (o < 72 ∨ (88 ≤ o ∧ o < 176) ∨ (184 ≤ o ∧ o < 192) ∨
      (192 ≤ o ∧ o < 560) ∨ (3048 ≤ o ∧ o < 3112) ∨ (12780 ≤ o ∧ o < 20520 + E.length)) →
      ¬R (r.off o))
    (h13 : m'.regs.get64 .r13 = m.regs.get64 .r13) :
    KeepRest r l x E m' := by
  obtain ⟨⟨i1, i2⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩, g13, hxa, hEa⟩ := hK
  have hkb : ∀ {o : Nat} {bs : List UInt8}, (o + bs.length ≤ 72 ∨
      (88 ≤ o ∧ o + bs.length ≤ 176) ∨ (184 ≤ o ∧ o + bs.length ≤ 192) ∨
      (192 ≤ o ∧ o + bs.length ≤ 560) ∨ (3048 ≤ o ∧ o + bs.length ≤ 3112) ∨
      (12780 ≤ o ∧ o + bs.length ≤ 20520 + E.length)) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs := fun {o} {bs} ho h ↦
    bytesAt_of_sameOutside h hout fun i hi hp ↦ by
      rw [Run.off_add] at hp
      exact hR (o + i) (by omega) (by omega) hp
  have hreg : ∀ {y : Reg64} {v : BitVec 64}, m'.regs.get64 y = m.regs.get64 y →
      Run.RegIs m y v → Run.RegIs m' y v := fun he h ↦ by
    unfold Run.RegIs reg at *
    rw [he]
    exact h
  refine ⟨⟨hkb ?_ i1, hkb ?_ i2⟩, ⟨hkb ?_ s1, hkb ?_ s2, hkb ?_ s3, hkb ?_ s4, hkb ?_ s5, hkb ?_ s6,
    hkb ?_ s7, hkb ?_ s8, hkb ?_ s9, hkb ?_ s10⟩, hreg h13 g13, hkb ?_ hxa,
    hkb ?_ hEa⟩ <;>
    (try simp only [length_pkBytes, length_sigMemR, NativeRustc.length_wordBytes, length_be32,
      length_be64, hx]) <;> omega

end

end NativeRustcX64.SphincsVerifyProof.Chains
