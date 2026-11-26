module

public import NativeRustcArm.SphincsVerify.Chains.Steps

/-!
# The chains' loop: blocks off the frame's region

`b104` and `b105` index the frame by the chain: their symbolic states have the indexed bytes as
regions of their own. What such a block changes (`sameOutside_region`, `sameOutside_regions2`),
keeps (`reg_same`, `Keep.of_change`, `Keep.of_change2`, `Keep.of_same`), copies (`copy16_gen`);
the frame's addresses (`off_add_ofInt`, `shl4`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

public section

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

/-- **A block writing only region `k1` or offsets `o2 .. o2 + n2` of region `k2`** changes only
those bytes. -/
theorem sameOutside_regions2 {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    (hwf : env.WF) {k1 k2 : Nat} {a1 a2 : BitVec 64} {n1 n2 o2 s2 : Nat}
    (hk1 : env.regions[k1]? = some (a1, n1)) (hk2 : env.regions[k2]? = some (a2, s2))
    (ho2 : o2 + n2 ≤ s2)
    (hall : S.mem.all (fun w ↦ (w.r == k1 && decide (w.off + w.n ≤ n1)) ||
      (w.r == k2 && decide (o2 ≤ w.off && w.off + w.n ≤ o2 + n2))) = true) :
    SameOutside env.mem0 m'.dmem (fun p ↦ InRange a1 n1 p ∨ InRange (a2 + BitVec.ofNat 64 o2) n2 p) := by
  refine SameOutside.mono (hm.sameOutside hwf) fun p ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ ?_
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hall
  rcases hall w hw with ⟨hr, hn⟩ | ⟨hr, hlo, hhi⟩
  · rw [hr, hk1] at hb
    cases hb
    have := hwf.noWrap k1 a1 n1 hk1
    exact Or.inl (by rw [Sym.inRange_iff this]; omega)
  · rw [hr, hk2] at hb
    cases hb
    have hnw := hwf.noWrap k2 a2 s2 hk2
    have hto : (a2 + BitVec.ofNat 64 o2).toNat = a2.toNat + o2 :=
      Sym.toNat_add_ofNat a2 o2 (by omega)
    exact Or.inr (by rw [Sym.inRange_iff (by omega), hto]; omega)

/-- A register a block keeps, in the environment of the state it starts from. -/
theorem reg_same {m m' : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (Env.ofMachine m regions vars) S m')
    {y : XReg} (h : S.reg y = some (.reg y)) : m'.regs.getXReg y = m.regs.getXReg y :=
  UInt64.toBitVec_inj.mp (hm.regs y _ h)

/-- **16 bytes copied** between two regions by two 8-byte loads and stores. -/
theorem copy16_gen {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    {k : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[k]? = some (b, sz)) {o : Nat}
    (ho : o + 16 ≤ sz) {k' o' : Nat} (hw1 : covers S.mem k o 8 (.load k' o' 8) = true)
    (hw2 : covers S.mem k (o + 8) 8 (.load k' (o' + 8) 8) = true) {bs : List UInt8}
    (hlen : bs.length = 16) (h : BytesAt env.mem0 (env.base k' + BitVec.ofNat 64 o') bs) :
    BytesAt m'.dmem (b + BitVec.ofNat 64 o) bs := by
  rw [← List.take_append_drop 8 bs]
  have h1 := bytesAt_write_load hm hb (by omega) hw1 (bs := bs.take 8) (by simp [hlen])
    (by decide) (by simpa using BytesAt.slice h 0 8)
  have h2 := bytesAt_write_load hm hb (by omega) hw2 (bs := bs.drop 8) (by simp [hlen])
    (by decide) (by
      have := BytesAt.slice h 8 8
      rwa [addr_add_add, List.take_of_length_le (by simp [hlen])] at this)
  refine BytesAt.append h1 ?_
  rw [List.length_take, Nat.min_eq_left (by omega), addr_add_add]
  exact h2

omit [Labels] in
/-- The frame's byte `a` moved by `c`. -/
theorem off_add_ofInt (a : Nat) {c : Int} {b : Nat} (h : (a : Int) + c = b) :
    r.off a + BitVec.ofInt 64 c = r.off b := by
  unfold Run.off
  have ha : BitVec.ofNat 64 a = BitVec.ofInt 64 (a : Int) := by simp
  have hb : BitVec.ofNat 64 b = BitVec.ofInt 64 (b : Int) := by simp
  rw [BitVec.add_assoc, ha, hb, ← BitVec.ofInt_add, h]

omit [Labels] in
theorem shl4 {i : Nat} (hi : i < 2 ^ 59) :
    BitVec.ofNat 64 i <<< 4 = BitVec.ofNat 64 (16 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  congr 1
  omega

/-- **A change of the frame's bytes `a .. a + n`** keeps what the chains keep, where they miss
the kept bytes (scratch, or past the ends so far). -/
theorem Keep.of_change (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {m m' : MachineData} (hK : Keep r l x E m) {a n : Nat}
    (ha : a + n ≤ 21520)
    (hd : (8224 ≤ a ∧ a + n ≤ 15936) ∨ (16000 ≤ a ∧ a + n ≤ 20464) ∨ 20464 + E.length ≤ a)
    (hsp : m'.regs.SP.toBitVec = r.base) (h29 : Run.RegIs m' .X29 (r.off 21520))
    (h19 : m'.regs.getXReg .X19 = m.regs.getXReg .X19)
    (h21 : m'.regs.getXReg .X21 = m.regs.getXReg .X21)
    (h25 : m'.regs.getXReg .X25 = m.regs.getXReg .X25)
    (h27 : m'.regs.getXReg .X27 = m.regs.getXReg .X27)
    (hout : SameOutside m.dmem m'.dmem (InRange (r.off a) n)) (hk : Kept m.dmem m'.dmem) :
    Keep r l x E m' := by
  obtain ⟨hF, ⟨i1, i2, i3⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, g19, g21, g25, g27, hxa,
    hEa⟩ := hK
  have hkb : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 8224 ∨
      (15936 ≤ o ∧ o + bs.length ≤ 16000) ∨ (20464 ≤ o ∧ o + bs.length ≤ 20464 + E.length) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    bytesAt_of_sameOutside h hout fun i hi hp ↦ by
      rw [r.off_add] at hp
      exact r.not_inRange_off hpre (by omega) (by omega) (by omega) hp
  have hreg : ∀ {y : XReg} {v : BitVec 64}, m'.regs.getXReg y = m.regs.getXReg y →
      Run.RegIs m y v → Run.RegIs m' y v := fun he h ↦ by
    unfold Run.RegIs at *
    rw [he]
    exact h
  refine ⟨hF.of_block hsp h29 hout (fun _ hp ↦ r.inRange_off hpre ha hp) hk,
    ⟨hkb ?_ i1, hkb ?_ i2, hkb ?_ i3⟩, ⟨hkb ?_ s1, hkb ?_ s2, hkb ?_ s3, hkb ?_ s4, hkb ?_ s5,
      hkb ?_ s6, hkb ?_ s7, hkb ?_ s8, hkb ?_ s9, hkb ?_ s10, hkb ?_ s11⟩, hreg h19 g19,
    hreg h21 g21, hreg h25 g25, hreg h27 g27, hkb ?_ hxa, hkb ?_ hEa⟩ <;>
    (try simp only [r.hpk, r.length_sigMem, NativeRustc.length_wordBytes, length_be32,
      length_be64, hx]) <;> omega

/-- **A change of the cell `8224 .. 8240` and spill `416 .. 424`** keeps what the chains keep. -/
theorem Keep.of_change_b105 (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {m m' : MachineData} (hK : Keep r l x E m)
    (hsp : m'.regs.SP.toBitVec = r.base) (h29 : Run.RegIs m' .X29 (r.off 21520))
    (h19 : m'.regs.getXReg .X19 = m.regs.getXReg .X19)
    (h21 : m'.regs.getXReg .X21 = m.regs.getXReg .X21)
    (h25 : m'.regs.getXReg .X25 = m.regs.getXReg .X25)
    (h27 : m'.regs.getXReg .X27 = m.regs.getXReg .X27)
    (hout : SameOutside m.dmem m'.dmem (fun p ↦ InRange (r.off 8224) 16 p ∨ InRange (r.off 416) 8 p))
    (hk : Kept m.dmem m'.dmem) : Keep r l x E m' := by
  obtain ⟨hF, ⟨i1, i2, i3⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, g19, g21, g25, g27, hxa,
    hEa⟩ := hK
  have hkb : ∀ {o : Nat} {bs : List UInt8},
      ((o + bs.length ≤ 416) ∨ (424 ≤ o ∧ o + bs.length ≤ 8224) ∨
        (15936 ≤ o ∧ o + bs.length ≤ 16000) ∨ (20464 ≤ o ∧ o + bs.length ≤ 20464 + E.length)) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    bytesAt_of_sameOutside h hout fun i hi hp ↦ by
      rw [r.off_add] at hp
      rcases hp with hp | hp
      · exact r.not_inRange_off hpre (by decide) (by omega) (by omega) hp
      · exact r.not_inRange_off hpre (by decide) (by omega) (by omega) hp
  have hreg : ∀ {y : XReg} {v : BitVec 64}, m'.regs.getXReg y = m.regs.getXReg y →
      Run.RegIs m y v → Run.RegIs m' y v := fun he h ↦ by
    unfold Run.RegIs at *
    rw [he]
    exact h
  refine ⟨hF.of_block hsp h29 hout (fun _ hp ↦ by
      rcases hp with hp | hp
      · exact r.inRange_off hpre (by decide) hp
      · exact r.inRange_off hpre (by decide) hp) hk,
    ⟨hkb ?_ i1, hkb ?_ i2, hkb ?_ i3⟩, ⟨hkb ?_ s1, hkb ?_ s2, hkb ?_ s3, hkb ?_ s4, hkb ?_ s5,
      hkb ?_ s6, hkb ?_ s7, hkb ?_ s8, hkb ?_ s9, hkb ?_ s10, hkb ?_ s11⟩, hreg h19 g19,
    hreg h21 g21, hreg h25 g25, hreg h27 g27, hkb ?_ hxa, hkb ?_ hEa⟩ <;>
    (try simp only [r.hpk, r.length_sigMem, NativeRustc.length_wordBytes, length_be32,
      length_be64, hx]) <;> omega

omit [Labels] in
/-- **A block without writes, SP or the kept registers** keeps what the chains keep. -/
theorem Keep.of_same {l : Nat} {x E : List UInt8} {m m' : MachineData} (hK : Keep r l x E m)
    (hd : m'.dmem = m.dmem) (hsp : m'.regs.SP = m.regs.SP)
    (h19 : m'.regs.getXReg .X19 = m.regs.getXReg .X19)
    (h21 : m'.regs.getXReg .X21 = m.regs.getXReg .X21)
    (h25 : m'.regs.getXReg .X25 = m.regs.getXReg .X25)
    (h27 : m'.regs.getXReg .X27 = m.regs.getXReg .X27)
    (h29 : m'.regs.getXReg .X29 = m.regs.getXReg .X29) : Keep r l x E m' := by
  have hb : ∀ {o : Nat} {bs : List UInt8}, BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun h ↦ by rw [hd]; exact h
  have hreg : ∀ {y : XReg} {v : BitVec 64}, m'.regs.getXReg y = m.regs.getXReg y →
      Run.RegIs m y v → Run.RegIs m' y v := fun he h ↦ by
    unfold Run.RegIs at *
    rw [he]
    exact h
  obtain ⟨hF, ⟨i1, i2, i3⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, g19, g21, g25, g27, hxa,
    hEa⟩ := hK
  refine ⟨hF.of_block (by rw [hsp]; exact hF.1) (by rw [h29]; exact hF.2.1)
      (R := fun _ ↦ False) (fun p _ ↦ by rw [hd]) (fun _ h ↦ h.elim) (fun p h ↦ by rw [hd]; exact h),
    ⟨hb i1, hb i2, hb i3⟩, ⟨hb s1, hb s2, hb s3, hb s4, hb s5, hb s6, hb s7, hb s8, hb s9, hb s10,
      hb s11⟩, hreg h19 g19, hreg h21 g21, hreg h25 g25, hreg h27 g27, hb hxa, hb hEa⟩

end

end NativeRustcArm.SphincsVerifyProof.Chains
