module

public import NativeRustcArm.SphincsVerify.Parse.Prologue
public import NativeRustcArm.SphincsVerify.Rev

/-!
# A turn of the words' copy loops

The state the words' blocks share (`AtWords`, from `b3` to `b11`), kept by a block that writes
only frame bytes from `468` on and keeps X19 .. X25 (`keepsRegs`); a loop turn run from region 0
the 32 destination bytes in the frame and region 1 the 4 source words (`copy_turn`: the words'
bytes, the frame's invariant, nothing else changed); the bytes of a stored `REV` of a loaded word
(`bytesAt_rev`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

theorem add_ofNat_zero (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := by simp

/-- The registers `AtWords` speaks of. -/
abbrev wordRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X29]

/-- `S` keeps `S₀`'s SP and the registers `rs`, which `S₀` knows. -/
@[expose] def keepsRegs (rs : List XReg) (S₀ S : SState) : Bool :=
  S.sp == S₀.sp && rs.all fun x => (S₀.reg x).isSome && S.reg x == S₀.reg x

/-- The writes are in region 0, between `lo` and `hi`. -/
@[expose] def writesIn (S : SState) (lo hi : Nat) : Bool :=
  S.mem.all fun w => w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)

section
variable [Labels]

/-- What a block keeps of `AtWords`' registers and SP. -/
theorem keepsRegs_regs {env : Env} {rs : List XReg} {S₀ S : SState} {m m' : MachineData}
    (hm : Match env S₀ m) (hm' : Match env S m') (h : keepsRegs rs S₀ S = true) :
    m'.regs.SP = m.regs.SP ∧ ∀ x ∈ rs, m'.regs.getXReg x = m.regs.getXReg x := by
  simp only [keepsRegs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨Match.sp_eq hm hm' h.1, fun x hx => ?_⟩
  obtain ⟨hs, he⟩ := h.2 x hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Match.reg_eq hm hm' hv (he.trans hv)

end

/-- **A counted loop**: from turn `j < N` in `P j`, each turn reaches the exit `Q` or turn
`j + 1 < N`. -/
theorem count_loop {σ : Type} {tr : σ → (σ → Prop) → Prop} {Q : σ → Prop} {P : Nat → σ → Prop}
    (N : Nat) (step : ∀ j s, j < N → P j s → Eventually tr (fun s' => Q s' ∨ (j + 1 < N ∧ P (j + 1) s')) s) :
    ∀ {j s}, j < N → P j s → Eventually tr Q s := by
  intro j s hj h
  refine loop (fun n s => ∃ j, j < N ∧ n = N - j ∧ P j s) (fun n s ⟨j, hj, hn, h⟩ => ?_)
    ⟨j, hj, rfl, h⟩
  refine eventually_weaken _ _ _ _ (fun s' h' => ?_) (step j s hj h)
  rcases h' with hq | ⟨hj', hp⟩
  · exact Or.inl hq
  · exact Or.inr ⟨N - (j + 1), by omega, j + 1, hj', rfl, hp⟩

variable (r : Run) [Labels]

omit [Labels] in
/-- An address a negative constant below another. -/
theorem alias_neg {A B : BitVec 64} (k : Nat) (h : A + BitVec.ofNat 64 k = B) :
    A = B + BitVec.ofInt 64 (-(k : Int)) := by
  subst h
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.add_assoc]
  simp

omit [Labels] in
/-- An address a constant above another. -/
theorem alias_pos {A B : BitVec 64} (k : Nat) (h : A = B + BitVec.ofNat 64 k) :
    A = B + BitVec.ofInt 64 (k : Int) := by
  rw [BitVec.ofInt_natCast]
  exact h

/-- Linear arithmetic of addresses: the frame's and the input's, with constants (`BitVec.ofNat`). -/
macro "bv_lin" : tactic => `(tactic| (
  try simp only [Run.off, Run.input]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  try simp only [show MemWidth.W64.bits = 64 from rfl]
  omega))

/-- **`AtWords` after a block** of an environment with region 0 at the frame's byte `d`, which
writes only its bytes `lo .. hi` (`468 ≤ d + lo`, below the saved registers) and keeps X19 .. X25. -/
theorem atWords_of_block (hpre : r.Pre) {m m' : MachineData} (hA : AtWords r m)
    {regions : List (BitVec 64 × Nat)} {d n lo hi : Nat} (hb : regions[0]? = some (r.off d, n))
    (hn : hi ≤ n) (hlo : lo ≤ hi) (hd : 468 ≤ d + lo) (hhi : d + hi ≤ 29280) {S' : SState}
    {S₀ : SState} (hm : Match (Env.ofMachine m regions) S₀ m)
    (hm' : Match (Env.ofMachine m regions) S' m')
    (hwf : (Env.ofMachine m regions).WF) (hk : keepsRegs wordRegs S₀ S' = true)
    (hw : writesIn S' lo hi = true) :
    AtWords r m' ∧ SameOutside m.dmem m'.dmem (InRange (r.off (d + lo)) (hi - lo)) := by
  obtain ⟨hF, hmsg, h19, h20, h21, h22, h23, h24, h25⟩ := hA
  have hout := sameOutside_hull hm' hwf hb (lo := lo) (hi := hi) hn hw
  rw [off_add] at hout
  obtain ⟨hsp, hreg'⟩ := keepsRegs_regs hm hm' hk
  have hreg : ∀ x ∈ wordRegs, (m'.regs.getXReg x).toBitVec = (m.regs.getXReg x).toBitVec :=
    fun x hx => by rw [hreg' x hx]
  have hF' : r.Frame m' := hF.of_block (by rw [hsp]; exact hF.1)
    ((hreg .X29 (by simp)).trans hF.2.1) hout (fun _ h => r.inRange_off hpre (by omega) h)
    (hm'.kept hwf)
  refine ⟨⟨hF', keep r hpre hmsg hout (length_wb r.w 4 4) (by left; omega) (by decide) (by omega),
    (hreg .X19 (by simp)).trans h19, (hreg .X20 (by simp)).trans h20,
    (hreg .X21 (by simp)).trans h21, (hreg .X22 (by simp)).trans h22,
    (hreg .X23 (by simp)).trans h23, (hreg .X24 (by simp)).trans h24,
    (hreg .X25 (by simp)).trans h25⟩, hout⟩

/-- **A loop turn**: from region 0 the frame's 32 bytes at `d` and region 1 the input words
`s .. s + 4`, a block that copies the words there (`copies`) and keeps X19 .. X25: the words'
bytes at `d`, `AtWords`, nothing else changed. -/
theorem copy_turn (hpre : r.Pre) {m m' : MachineData} (hA : AtWords r m) {d s : Nat}
    (hd : 468 ≤ d) (hd' : d + 32 ≤ 29280) (hs : s + 4 ≤ 977) {S₀ S' : SState}
    (hm : Match (Env.ofMachine m [(r.off d, 32), (r.input + BitVec.ofNat 64 (8 * s), 32)]) S₀ m)
    (hm' : Match (Env.ofMachine m [(r.off d, 32), (r.input + BitVec.ofNat 64 (8 * s), 32)]) S' m')
    (hk : keepsRegs wordRegs S₀ S' = true) (hw : writesIn S' 0 32 = true)
    (hc : copies S'.mem 0 0 1 0 32 = true) :
    (Env.ofMachine m [(r.off d, 32), (r.input + BitVec.ofNat 64 (8 * s), 32)]).WF ∧
    AtWords r m' ∧ BytesAt m'.dmem (r.off d) (wb r.w s 4) ∧
      SameOutside m.dmem m'.dmem (InRange (r.off d) 32) := by
  have hF := hA.1
  have hwf := wf_frame_input r hpre hF.2.2.2.1 hF.2.2.2.2 (a := d) (n := 32) (s := s) (k := 32)
    (by omega) (by omega) (by decide) (fun _ => 0)
  obtain ⟨hA', hout⟩ := atWords_of_block r hpre hA rfl le_rfl (by decide) hd hd' hm hm' hwf hk hw
  refine ⟨hwf, hA', ?_, hout⟩
  have h := copy hm' (r := 0) (o := 0) (r' := 1) (o' := 0) (n := 32) (B := r.off d) (sz := 32) rfl
    (by decide) hc (length_wb r.w s 4) (by
      show BytesAt m.dmem (r.input + BitVec.ofNat 64 (8 * s) + BitVec.ofNat 64 0) _
      rw [add_ofNat_zero]
      exact bytesAt_wb r hpre hF.2.2.2.1 (by omega))
  rwa [add_ofNat_zero] at h

/-- Bytes `i` of `o .. o + 4` in region `r` hold byte `i` of a `REV` of the 4 bytes at `o'` of
region `r'`. -/
@[expose] def revs (ws : List Write) (r o r' o' : Nat) : Bool :=
  (List.range 4).all fun i => findWrite r (o + i) ws == some (.un .rev .W32 (.load r' o' 4), i)

omit [Labels] in
theorem load4_word {env : Env} {r' o' : Nat} {x : UInt64}
    (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') (wordBytes x)) :
    UInt32.ofNat (env.load r' o' 4).toNat = x.toUInt32 := by
  have h4 : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') ((wordBytes x).take 4) :=
    fun i hi => by
      rw [List.getElem_take]
      exact h i (by simp at hi; rw [length_wordBytes]; omega)
  rw [Env.load_of_bytesAt (by simp [length_wordBytes]) h4, ofBytes_eq_leNat,
    Native.XmssVerifier.wordBytes_eq_bytes, Native.XmssVerifier.bytes,
    ← List.map_take, List.take_range, show min 4 8 = 4 from rfl, ← Native.XmssVerifier.bytes,
    leNat_bytes, BitVec.toNat_ofNat]
  apply UInt32.toNat.inj
  have := x.toNat_lt
  simp only [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]
  omega

omit [Labels] in
theorem getElem_be32_rev (v : BitVec 64) {i : Nat} (hi : i < 4) :
    byteOf (UnOp.apply .rev .W32 v) i = (be32 (UInt32.ofNat v.toNat))[i]'(by simp [be32]; omega) := by
  have h := bytes_rev32 v
  have h' := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at h'
  rw [List.getElem?_eq_getElem (by simp [be32]; omega)] at h'
  exact Option.some.inj h'

/-- **A stored `REV` of a loaded word**: the big-endian bytes of its `u32`. -/
theorem bytesAt_rev {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o r' o' : Nat} {B : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (B, sz))
    (hle : o + 4 ≤ sz) (hc : revs S.mem r o r' o' = true) {x : UInt64}
    (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') (wordBytes x)) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) (be32 x.toUInt32) := by
  intro i hi
  have hi4 : i < 4 := by simpa [be32] using hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr hi4)
  rw [beq_iff_eq] at hc
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  rw [hc]
  simp only [Option.some.injEq]
  rw [show Sym.eval env (.un .rev .W32 (.load r' o' 4)) = UnOp.apply .rev .W32 (env.load r' o' 4)
    from rfl, getElem_be32_rev _ hi4]
  simp only [load4_word h]

end

end NativeRustcArm.SphincsVerifyProof.Parse
