module

public import NativeRustcVmX64.Transcript.Frame

/-!
# A function's body with stack arguments (x86-64)

`verify_keccak` and `keccak_phase` push the six callee-saved registers, keep RSP at an offset of a
frame below the entry's RSP, and read their stack arguments above the return address: region 0 of
a block's environment (`fenv`) is the `F` bytes below the entry's RSP and `Z - F` bytes from there
(the return address and the stack arguments). `Body m0 F Z slots W o d`: RSP at offset `o` of the
region, the slots holding the entry's registers, the region's bytes from `F` the entry's, every
mapped byte kept, memory as at the entry outside `W`. `Geo` the region's geometry: it does not
wrap, is mapped, its slots between `L` and `F`, every callee-saved register in a slot, its bytes
below `F` in `W`.

The prologue makes a body (`Body.prologue`), a block writing below `L` or in `W` outside the
region's top keeps it (`Body.block`), so does a callee changing bytes only there (`Body.call`); the
epilogue restores the registers (`Body.epilogue`) and returns to the entry's return address
(`Body.load_ret`).
-/

namespace NativeRustcVmX64.KeccakGkr.Fn

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript

@[expose] public section

/-- A block's environment: region 0 the `Z` bytes from `F` below the entry's RSP, then `rest`. -/
abbrev fenv (m0 d : MachineData) (F Z : Nat) (rest : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) : Env :=
  Env.ofMachine d ((stackBelow m0 F, Z) :: rest) vars ret

/-- **A function's body**, RSP at offset `o` of its region. -/
structure Body (m0 : MachineData) (F Z : Nat) (slots : Slots) (W : BitVec 64 → Prop) (o : Nat)
    (d : MachineData) : Prop where
  sp : rspOf d = off (stackBelow m0 F) o
  slot : ∀ p ∈ slots,
    NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) p.1) (UInt64.ofBitVec (reg m0 p.2))
  top : ∀ j, F ≤ j → j < Z →
    d.dmem.get? (off (stackBelow m0 F) j) = m0.dmem.get? (off (stackBelow m0 F) j)
  kept : Kept m0.dmem d.dmem
  same : NativeRustcVm.SameOutside m0.dmem d.dmem W

/-- **The region's geometry.** -/
structure Geo (m0 : MachineData) (F Z L : Nat) (slots : Slots) (W : BitVec 64 → Prop) : Prop where
  hF : F ≤ (rspOf m0).toNat
  hZ : (rspOf m0).toNat - F + Z ≤ 2 ^ 64
  FZ : F + 8 ≤ Z
  LF : L ≤ F
  map : NativeRustcVm.Mapped m0.dmem (stackBelow m0 F) Z
  sl : ∀ p ∈ slots, L ≤ p.1 ∧ p.1 + 8 ≤ F
  cs : ∀ r, calleeSaved r = true → ∃ p ∈ slots, p.2 = r
  low : ∀ j < F, W (off (stackBelow m0 F) j)

/-- A byte of memory is in the region's top part (from `L`). -/
abbrev Top (m0 : MachineData) (F Z L : Nat) (q : BitVec 64) : Prop :=
  (stackBelow m0 F).toNat + L ≤ q.toNat ∧ q.toNat < (stackBelow m0 F).toNat + Z

end

public section

variable {m0 d d' : MachineData} {F Z L : Nat} {slots : Slots} {W : BitVec 64 → Prop} {o : Nat}

theorem Geo.base (g : Geo m0 F Z L slots W) : (stackBelow m0 F).toNat = (rspOf m0).toNat - F :=
  stackBelow_toNat g.hF

theorem Geo.off (g : Geo m0 F Z L slots W) {j : Nat} (hj : j < Z) :
    (off (stackBelow m0 F) j).toNat = (stackBelow m0 F).toNat + j :=
  toNat_off (by rw [g.base]; have := g.hZ; omega)

theorem Geo.noWrap (g : Geo m0 F Z L slots W) : NativeRustcVm.NoWrap (stackBelow m0 F) Z := by
  unfold NativeRustcVm.NoWrap; rw [g.base]; exact g.hZ

theorem eval_ptr0' [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (o : Nat) : (Sym.ptr 0 (o : Int)).eval (fenv m0 d F Z rest vars ret) =
      off (stackBelow m0 F) o := by
  show (fenv m0 d F Z rest vars ret).base 0 + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]
  rfl

/-- The region alone is a well-formed environment. -/
theorem fenv_wf0 (g : Geo m0 F Z L slots W) (hk : Kept m0.dmem d.dmem) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : (fenv m0 d F Z [] vars ret).WF :=
  Env.wf_of ⟨⟨Mapped.keeps g.map hk, g.noWrap⟩, trivial⟩ (List.pairwise_singleton _ _)

/-- The region and one more, apart. -/
theorem fenv_wf1 (g : Geo m0 F Z L slots W) (hk : Kept m0.dmem d.dmem) {vars : Nat → BitVec 64}
    {ret : BitVec 64} {b : BitVec 64} {n : Nat} (hm : NativeRustcVm.Mapped d.dmem b n)
    (hn : b.toNat + n ≤ 2 ^ 64)
    (hs : (stackBelow m0 F).toNat + Z ≤ b.toNat ∨ b.toNat + n ≤ (stackBelow m0 F).toNat) :
    (fenv m0 d F Z [(b, n)] vars ret).WF :=
  Env.wf_of ⟨⟨Mapped.keeps g.map hk, g.noWrap⟩, ⟨hm, hn⟩, trivial⟩ (List.pairwise_pair.mpr hs)

/-- **Writes of region 0 below `n`**: bytes of the region's first `n`. -/
theorem written_lt [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {n : Nat}
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ n) {q : BitVec 64}
    (hq : Written (fenv m0 d F Z rest vars ret) S q) :
    (stackBelow m0 F).toNat ≤ q.toNat ∧ q.toNat < (stackBelow m0 F).toNat + n := by
  obtain ⟨w, hwm, b, sz, hb, h1, h2⟩ := hq
  obtain ⟨hr, hle⟩ := hw w hwm
  rw [hr] at hb
  cases hb
  omega

/-- **Writes below `L`** of region 0: in `W`, outside the region's top. -/
theorem written_low [Labels] (g : Geo m0 F Z L slots W) {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (fenv m0 d F Z rest vars ret).WF) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L) :
    ∀ q, Written (fenv m0 d F Z rest vars ret) S q → W q ∧ ¬ Top m0 F Z L q := by
  intro q hq
  obtain ⟨w, hwm, b, sz, hb, j, h1, h2, rfl⟩ := written_off hwf hq
  obtain ⟨hr, hle⟩ := hw w hwm
  rw [hr] at hb
  cases hb
  have := g.LF
  have := g.FZ
  refine ⟨g.low j (by omega), fun ⟨h3, _⟩ ↦ ?_⟩
  rw [g.off (by omega)] at h3
  omega

/-- **A block** keeps the body. -/
theorem Body.block [Labels] (g : Geo m0 F Z L slots W) (hb : Body m0 F Z slots W o d)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (fenv m0 d F Z rest vars ret).WF) (hm : Match (fenv m0 d F Z rest vars ret) S d')
    {o' : Nat} (hsp : S.reg .rsp = some (.ptr 0 (o' : Int)))
    (hW : ∀ q, Written (fenv m0 d F Z rest vars ret) S q → W q ∧ ¬ Top m0 F Z L q) :
    Body m0 F Z slots W o' d' := by
  have keep : ∀ j, L ≤ j → j < Z →
      d'.dmem.get? (off (stackBelow m0 F) j) = d.dmem.get? (off (stackBelow m0 F) j) :=
    fun j h1 h2 ↦ hm.get?_mem0 hwf fun hw ↦ (hW _ hw).2 (by unfold Top; rw [g.off (by omega)]; omega)
  refine ⟨?_, fun p hp ↦ ?_, fun j h1 h2 ↦ ?_, kept_trans hb.kept (hm.kept hwf), fun q hq ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0']
  · refine bytesAt_congr (hb.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    have := g.sl p hp
    have := g.FZ
    rw [off_add]
    exact keep _ (by omega) (by omega)
  · rw [keep j (by have := g.LF; omega) h2]
    exact hb.top j h1 h2
  · exact (hm.get?_mem0 hwf fun hw ↦ hq (hW q hw).1).trans (hb.same q hq)

/-- **A call** keeps the body where the callee changes bytes in `W` outside the region's top. -/
theorem Body.call (g : Geo m0 F Z L slots W) (hb : Body m0 F Z slots W o d) (hsv : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R) (hR : ∀ q, R q → W q ∧ ¬ Top m0 F Z L q) :
    Body m0 F Z slots W (o + 8) d' := by
  have keep : ∀ j, L ≤ j → j < Z →
      d'.dmem.get? (off (stackBelow m0 F) j) = d.dmem.get? (off (stackBelow m0 F) j) :=
    fun j h1 h2 ↦ hso _ fun hr ↦ (hR _ hr).2 (by unfold Top; rw [g.off (by omega)]; omega)
  refine ⟨?_, fun p hp ↦ ?_, fun j h1 h2 ↦ ?_, kept_trans hb.kept hsv.2, fun q hq ↦ ?_⟩
  · rw [hrsp, hb.sp, off_add]
  · refine bytesAt_congr (hb.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    have := g.sl p hp
    have := g.FZ
    rw [off_add]
    exact keep _ (by omega) (by omega)
  · rw [keep j (by have := g.LF; omega) h2]
    exact hb.top j h1 h2
  · exact (hso q fun hr ↦ hq (hR q hr).1).trans (hb.same q hq)

/-- **The prologue** makes a body: the slots written, every write below `F`. -/
theorem Body.prologue [Labels] (g : Geo m0 F Z L slots W) {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (fenv m0 m0 F Z rest vars ret).WF) (hm : Match (fenv m0 m0 F Z rest vars ret) S d')
    (hsp : S.reg .rsp = some (.ptr 0 (o : Int)))
    (hsl : ∀ p ∈ slots, ∀ t < 8, findWrite 0 (p.1 + t) S.mem = some (.reg p.2, t))
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Body m0 F Z slots W o d' := by
  have hW : ∀ q, Written (fenv m0 m0 F Z rest vars ret) S q →
      W q ∧ q.toNat < (stackBelow m0 F).toNat + F := by
    intro q hq
    obtain ⟨w, hwm, b, sz, hb, j, h1, h2, rfl⟩ := written_off hwf hq
    obtain ⟨hr, hle⟩ := hw w hwm
    rw [hr] at hb
    cases hb
    have := g.FZ
    exact ⟨g.low j (by omega), by rw [g.off (by omega)]; omega⟩
  refine ⟨?_, fun p hp ↦ ?_, fun j h1 h2 ↦ ?_, hm.kept hwf, fun q hq ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0']
  · have := g.sl p hp
    have := g.FZ
    have h := wordAt_write hm (r := 0) (b := stackBelow m0 F) (sz := Z) rfl (by omega) (hsl p hp)
    rw [Sym.eval, Env.ofMachine_regs] at h
    exact h
  · refine hm.get?_mem0 hwf fun hw ↦ ?_
    have := (hW _ hw).2
    rw [g.off (by omega)] at this
    omega
  · exact hm.get?_mem0 hwf fun hw ↦ hq (hW q hw).1

/-- A body with fewer changes allowed is one with more. -/
theorem Body.weaken (hb : Body m0 F Z slots W o d) {W' : BitVec 64 → Prop} (hW : ∀ q, W q → W' q) :
    Body m0 F Z slots W' o d :=
  ⟨hb.sp, hb.slot, hb.top, hb.kept, NativeRustcVm.SameOutside.mono hb.same hW⟩

theorem Geo.weaken (g : Geo m0 F Z L slots W) {W' : BitVec 64 → Prop} (hW : ∀ q, W q → W' q) :
    Geo m0 F Z L slots W' :=
  ⟨g.hF, g.hZ, g.FZ, g.LF, g.map, g.sl, g.cs, fun j hj ↦ hW _ (g.low j hj)⟩

/-- The return address, loaded from the region. -/
theorem Body.load_ret (g : Geo m0 F Z L slots W) (hb : Body m0 F Z slots W o d)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} :
    Int64.ofBitVec ((fenv m0 d F Z rest vars ret).load 0 F 8) = retOf m0 := by
  have hget : ∀ j < 8, m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      some ((m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)).getD 0) := fun j hj ↦ by
    have := g.map (F + j) (by have := g.FZ; omega)
    rw [show stackBelow m0 F + BitVec.ofNat 64 (F + j) = off (stackBelow m0 F) (F + j) from rfl,
      frame_add] at this
    revert this
    cases m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) <;> simp
  rw [retOf, loadInt_of_get? _ _ 8 _ hget, Option.getD_some]
  unfold Env.load
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [show (fenv m0 d F Z rest vars ret).base 0 = stackBelow m0 F from rfl, Env.ofMachine_mem0,
    show stackBelow m0 F + BitVec.ofNat 64 (F + j) = off (stackBelow m0 F) (F + j) from rfl,
    hb.top (F + j) (by omega) (by have := g.FZ; omega), frame_add]

/-- **The epilogue** restores the registers from their slots: `Saved`, RSP 8 above the entry's. -/
theorem Body.epilogue [Labels] (g : Geo m0 F Z L slots W) (hb : Body m0 F Z slots W o d)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (fenv m0 d F Z rest vars ret).WF) (hm : Match (fenv m0 d F Z rest vars ret) S d')
    (hld : ∀ p ∈ slots, S.reg p.2 = some (.load 0 p.1 8))
    (hsp : S.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int))) :
    Saved m0 d' ∧ rspOf d' = rspOf m0 + 8#64 := by
  refine ⟨⟨fun r hr ↦ ?_, kept_trans hb.kept (hm.kept hwf)⟩, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := g.cs r hr
    have := hm.regs p.2 _ (hld p hp)
    rw [Sym.eval, load_ofMachine (o := p.1) rfl (hb.slot p hp)] at this
    exact this
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0', frame_add]

end

end NativeRustcVmX64.KeccakGkr.Fn
