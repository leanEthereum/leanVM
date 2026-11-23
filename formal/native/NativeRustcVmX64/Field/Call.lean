module

public import NativeRustcVmX64.Field.Leaf

/-!
# Functions with pushes and calls (x86-64)

The field functions that call others (`kinv::sq`, `kinv`, `kpow`, `EW::sq_iter`) push the
callee-saved registers they use (`used`) and call with RSP 8 bytes below their pushes: their `F`
bytes below the entry's RSP are the pushes (offsets `8` to `F`) above the return-address slot of
their calls (offsets `0` to `8`), all within the `N` bytes of stack they use with their callees'
(`Geo`). From the entry state `m0` and the state `m1` after the prologue, every state between the
prologue and the epilogue keeps (`Fr`): RSP at offset `o` of the frame (`8`, or `0` at a call),
the other callee-saved registers, the pushes as `m1` left them, every byte outside the `N` bytes
below the entry's RSP, every mapped byte. The prologue (`prologue`) establishes it and stores the
pushed registers (`Slots`); a block whose writes stay in the call's slot (`block`) and a callee's
contract (`call`) keep it; the epilogue (`epilogue`, `epilogue_ret`) restores the registers and
RSP.
-/

namespace NativeRustcVmX64.Field

open NativeRustcX64 NativeRustcX64.Sym

@[expose] public section

/-- The geometry: the entry's RSP leaves `N` bytes, the frame their top `F`, at least its call
slot. -/
structure Geo (m0 : MachineData) (F N : Nat) : Prop where
  ok : StackOk m0 N
  le : F ≤ N
  f8 : 8 ≤ F

/-- **Between prologue and epilogue**, RSP at offset `o` of the frame. -/
structure Fr (m0 m1 : MachineData) (F N o : Nat) (used : List Reg64) (m : MachineData) : Prop where
  sp : rspOf m = stackBelow m0 F + BitVec.ofNat 64 o
  regs : ∀ r, calleeSaved r = true → r ∉ used → m.regs.get64 r = m0.regs.get64 r
  frame : ∀ i, 8 ≤ i → i < F → m.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 i) =
    m1.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 i)
  same : SameOutside m0.dmem m.dmem (InRange (stackBelow m0 N) N)
  kept : Kept m0.dmem m.dmem

/-- The prologue's pushes: register `r` of the entry at `off` in the frame. -/
def Slots (m0 m1 : MachineData) (F : Nat) (slots : List (Reg64 × Nat)) : Prop :=
  ∀ p ∈ slots, 8 ≤ p.2 ∧ p.2 + 8 ≤ F ∧
    BytesAt m1.dmem (stackBelow m0 F + BitVec.ofNat 64 p.2)
      ((List.range 8).map (byteOf (m0.regs.get64 p.1)))

/-- A block's summary keeps the callee-saved registers outside `used`. -/
def keepsExcept (used : List Reg64) (S : SState) : Bool :=
  allRegs.all fun r ↦ !calleeSaved r || used.any (decide <| · = r) || S.reg r == some (.reg r)

/-- An epilogue's summary restores the registers of `slots` from their slots, and keeps the other
callee-saved registers, outside `used`. -/
def restores (slots : List (Reg64 × Nat)) (used : List Reg64) (S : SState) : Bool :=
  slots.all (fun p ↦ S.reg p.1 == some (.load 0 p.2 8)) &&
    allRegs.all fun r ↦ !calleeSaved r || slots.any (decide <| ·.1 = r) ||
      (!used.any (decide <| · = r) && S.reg r == some (.reg r))

end

public section

variable {m0 m1 m : MachineData} {F N : Nat} {used : List Reg64}

theorem keepsExcept_reg {S : SState} (h : keepsExcept used S = true) {r : Reg64}
    (hr : calleeSaved r = true) (hu : r ∉ used) : S.reg r = some (.reg r) := by
  have := List.all_eq_true.mp h r (mem_allRegs r)
  simp only [hr, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h | h
  · obtain ⟨u, hu', he⟩ := List.any_eq_true.mp h
    rw [decide_eq_true_eq] at he
    exact absurd (he ▸ hu') hu
  · exact h

theorem ofInt_ofBytes_byteOf' (x : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map (byteOf x))) = x := by
  have := ofBytes_byteOf x 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [this, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem Geo.sp (g : Geo m0 F N) : N ≤ (rspOf m0).toNat := g.ok.1

theorem Geo.top (g : Geo m0 F N) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := g.ok.2.1

theorem Geo.base (g : Geo m0 F N) : (stackBelow m0 F).toNat = (rspOf m0).toNat - F :=
  stackBelow_toNat' (by have := g.sp; have := g.le; omega)

theorem Geo.below (g : Geo m0 F N) : (stackBelow m0 N).toNat = (rspOf m0).toNat - N :=
  stackBelow_toNat' g.sp

/-- An address of the `N + 8` bytes from `N` below the entry's RSP is mapped. -/
theorem Geo.mapped (g : Geo m0 F N) {p : BitVec 64} (h1 : (rspOf m0).toNat - N ≤ p.toNat)
    (h2 : p.toNat < (rspOf m0).toNat + 8) : (m0.dmem.get? p).isSome := by
  have hs := g.sp
  have hb := g.below
  have := g.ok.2.2 (p.toNat - ((rspOf m0).toNat - N)) (by omega)
  have hlt := p.isLt
  have he : stackBelow m0 N + BitVec.ofNat 64 (p.toNat - ((rspOf m0).toNat - N)) = p :=
    BitVec.eq_of_toNat_eq (by rw [toNat_add_ofNat _ _ (by omega), hb]; omega)
  rwa [show rspOf m0 - BitVec.ofNat 64 N = stackBelow m0 N from rfl, he] at this

theorem Geo.okF (g : Geo m0 F N) : StackOk m0 F := by
  refine ⟨by have := g.sp; have := g.le; omega, g.top, fun i hi ↦ g.mapped ?_ ?_⟩ <;>
    rw [show rspOf m0 - BitVec.ofNat 64 F = stackBelow m0 F from rfl,
      toNat_add_ofNat _ _ (by rw [g.base]; have := g.top; have := g.sp; have := g.le; omega),
      g.base] <;> have := g.sp <;> have := g.le <;> omega

theorem Geo.wf [Labels] (g : Geo m0 F N) (hk : Kept m0.dmem m.dmem) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : (frameEnv m0 m F vars ret).WF :=
  frame_wf g.okF hk

/-- An address a write of the frame's first `n` bytes covers. -/
theorem written_frame [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    {n : Nat} (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ n) {a : BitVec 64}
    (h : Written (frameEnv m0 m F vars ret) S a) :
    (stackBelow m0 F).toNat ≤ a.toNat ∧ a.toNat < (stackBelow m0 F).toNat + n := by
  obtain ⟨w, hwm, b, sz, hbs, h1, h2⟩ := h
  obtain ⟨hr, hn⟩ := hw w hwm
  rw [hr] at hbs
  cases hbs
  omega

/-- The frame's base plus `i` as a number. -/
theorem Geo.addr (g : Geo m0 F N) {i : Nat} (hi : i < F + 8) :
    (stackBelow m0 F + BitVec.ofNat 64 i).toNat = (rspOf m0).toNat - F + i := by
  rw [toNat_add_ofNat _ _ (by rw [g.base]; have := g.top; have := g.sp; have := g.le; omega), g.base]

theorem inRange_N (g : Geo m0 F N) {p : BitVec 64} :
    InRange (stackBelow m0 N) N p ↔ (rspOf m0).toNat - N ≤ p.toNat ∧ p.toNat < (rspOf m0).toNat := by
  rw [inRange_iff (by rw [g.below]; have := g.top; have := g.sp; omega), g.below]
  have := g.sp
  constructor <;> intro h <;> omega

theorem Fr.sp_toNat (g : Geo m0 F N) {o : Nat} (h : Fr m0 m1 F N o used m) (ho : o < F + 8) :
    (rspOf m).toNat = (rspOf m0).toNat - F + o := by
  rw [h.sp, g.addr ho]

/-- **A callee's stack**: `S` bytes below RSP at a call. -/
theorem Fr.stackOk (g : Geo m0 F N) (h : Fr m0 m1 F N 0 used m) {S : Nat} (hS : F + S ≤ N) :
    StackOk m S := by
  have hsp := h.sp_toNat g (by omega)
  have := g.sp
  have := g.top
  have hb : (stackBelow m S).toNat = (rspOf m0).toNat - F - S := by
    rw [stackBelow_toNat' (by omega), hsp]
    omega
  refine ⟨by omega, by omega, fun i hi ↦ h.kept _ (g.mapped ?_ ?_)⟩ <;>
    rw [show rspOf m - BitVec.ofNat 64 S = stackBelow m S from rfl,
      toNat_add_ofNat _ _ (by omega), hb] <;> omega

/-- **After a callee** using `S` bytes below RSP at the call. -/
theorem Fr.call (g : Geo m0 F N) (h : Fr m0 m1 F N 0 used m) {S : Nat} (hS : F + S ≤ N)
    {m' : MachineData} (hrsp : rspOf m' = rspOf m + 8#64) (hsv : Saved m m')
    (hso : SameOutside m.dmem m'.dmem (InRange (stackBelow m S) S)) :
    Fr m0 m1 F N 8 used m' := by
  have hsp := h.sp_toNat g (by omega)
  have := g.sp
  have := g.top
  have hcb : (stackBelow m S).toNat = (rspOf m0).toNat - F - S := by
    rw [stackBelow_toNat' (by omega), hsp]
    omega
  have hin : ∀ p : BitVec 64, InRange (stackBelow m S) S p →
      (rspOf m0).toNat - F - S ≤ p.toNat ∧ p.toNat < (rspOf m0).toNat - F := fun p hp ↦ by
    rw [inRange_iff (by rw [hcb]; omega), hcb] at hp
    omega
  refine ⟨?_, fun r hr hu ↦ ?_, fun i hi1 hi2 ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ hsv.2 p (h.kept p hp)⟩
  · rw [hrsp, h.sp, BitVec.add_zero]
  · rw [hsv.1 r hr, h.regs r hr hu]
  · rw [hso _ fun hp ↦ ?_, h.frame i hi1 hi2]
    have := hin _ hp
    rw [g.addr (by omega)] at this
    omega
  · rw [hso p fun hp' ↦ hp ?_, h.same p hp]
    have := hin p hp'
    rw [inRange_N g]
    omega

/-- Less stack below RSP. -/
theorem StackOk.mono {n : Nat} (h : StackOk m N) (hle : n ≤ N) : StackOk m n := by
  obtain ⟨hN, htop, hmap⟩ := h
  refine ⟨by omega, htop, fun i hi ↦ ?_⟩
  have := hmap (N - n + i) (by omega)
  have hlt := (rspOf m).isLt
  have bN : (stackBelow m N).toNat = (rspOf m).toNat - N := stackBelow_toNat' hN
  have bn : (stackBelow m n).toNat = (rspOf m).toNat - n := stackBelow_toNat' (by omega)
  have e1 := toNat_add_ofNat (stackBelow m N) (N - n + i) (by omega)
  have e2 := toNat_add_ofNat (stackBelow m n) i (by omega)
  have he : stackBelow m N + BitVec.ofNat 64 (N - n + i) = stackBelow m n + BitVec.ofNat 64 i :=
    BitVec.eq_of_toNat_eq (by rw [e1, e2, bN, bn]; omega)
  exact he ▸ this

/-- The stack below RSP, in a state with the same RSP keeping the mapped bytes. -/
theorem StackOk.transfer {m' : MachineData} {n : Nat} (h : StackOk m n)
    (hrsp : rspOf m' = rspOf m) (hk : Kept m.dmem m'.dmem) : StackOk m' n := by
  obtain ⟨h1, h2, hmap⟩ := h
  exact ⟨hrsp ▸ h1, hrsp ▸ h2, fun i hi ↦ by rw [hrsp]; exact hk _ (hmap i hi)⟩

/-- The return address `ret` reads, in a state with the same RSP and the same 8 bytes there. -/
theorem retOf_eq {m' : MachineData} (hrsp : rspOf m' = rspOf m)
    (hmem : ∀ j < 8, m'.dmem.get? (rspOf m + BitVec.ofNat 64 j) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 j)) : retOf m' = retOf m := by
  unfold retOf
  rw [hrsp, loadInt_congr hmem]

/-- The entry's return address is outside the `N` bytes below its RSP. -/
theorem Geo.ret_same (g : Geo m0 F N) (hso : SameOutside m0.dmem m.dmem (InRange (stackBelow m0 N) N)) :
    ∀ j < 8, m.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) := fun j hj ↦ hso _ fun hin ↦ by
  rw [inRange_N g, toNat_add_ofNat _ _ (by have := g.top; omega)] at hin
  omega

/-- RSP at the frame's offset `F` is the entry's. -/
theorem frame_top [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (Sym.ptr 0 ((F : Nat) : Int)).eval (frameEnv m0 m F vars ret) = rspOf m0 := by
  show stackBelow m0 F + BitVec.ofInt 64 ((F + 0 : Nat) : Int) = _
  rw [frame_rsp, BitVec.add_zero]

variable [Host]

/-- **The prologue**: the entry block from `frameS F`, writing in the frame, the pushed
registers at their slots, RSP left at offset `o`. -/
theorem prologue (g : Geo m0 F N) {vars : Nat → BitVec 64} {ds : List Directive} {k : Nat}
    {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog k)
    (hrun : exec ds (frameS F) = some (S', x)) {o : Nat}
    (hsp : S'.reg .rsp = some (.ptr 0 (o : Int))) (hkeep : keepsExcept used S' = true)
    (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) {slots : List (Reg64 × Nat)}
    (hslots : ∀ p ∈ slots, 8 ≤ p.2 ∧ p.2 + 8 ≤ F ∧
      ∀ i < 8, findWrite 0 (p.2 + i) S'.mem = some (.reg p.1, i))
    {R : MachineState → Prop}
    (cont : ∀ st, Match (frameEnv m0 m0 F vars (Host.addrOf (k + ds.length)).toBitVec) S'
        st.data →
      PcOk (frameEnv m0 m0 F vars (Host.addrOf (k + ds.length)).toBitVec) x
        (Host.addrOf (k + ds.length)) st →
      Fr m0 st.data F N o used st.data → Slots m0 st.data F slots →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf k⟩ := by
  have hwf := g.wf (m := m0) (fun _ h ↦ h) (vars := vars)
    (ret := (Host.addrOf (k + ds.length)).toBitVec)
  refine exec_then hk hrun hwf (fun _ _ ↦ rfl) match_frame fun st hm' hpc ↦ cont st hm' hpc ?_ ?_
  · refine ⟨?_, fun r hr hu ↦ ?_, fun _ _ _ ↦ rfl, fun p hp ↦ ?_, hm'.kept hwf⟩
    · show st.data.regs.get64 .rsp = _
      rw [hm'.regs .rsp _ hsp]
      show stackBelow m0 F + BitVec.ofInt 64 (o : Int) = _
      rw [BitVec.ofInt_natCast]
    · exact (hm'.regs r _ (keepsExcept_reg hkeep hr hu)).trans rfl
    · refine hm'.get?_mem0 hwf fun hW ↦ hp ?_
      have := written_frame hw hW
      rw [g.base] at this
      rw [inRange_N g]
      have := g.le
      have := g.sp
      omega
  · intro p hp
    obtain ⟨h8, hle, hf⟩ := hslots p hp
    exact ⟨h8, hle, hm'.bytesAt_write (r := 0) (sz := F + 8) rfl (by omega) hf⟩

omit [Host] in
/-- The frame's environment describes a state between prologue and epilogue at `midS F`. -/
theorem match_mid [Labels] (hF : Fr m0 m1 F N 8 used m) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : Match (frameEnv m0 m F vars ret) (midS F) m :=
  match_ofMachine ⟨rfl, trivial⟩
    ⟨show rspOf m = stackBelow m0 F + BitVec.ofInt 64 ((8 : Nat) : Int) by
      rw [BitVec.ofInt_natCast, hF.sp], trivial⟩ trivial trivial trivial

/-- **A block** between prologue and epilogue, from `midS F`, writing in the call's slot only,
keeping the callee-saved registers outside `used`, RSP left at offset `o`. -/
theorem block (g : Geo m0 F N) (hF : Fr m0 m1 F N 8 used m) {vars : Nat → BitVec 64}
    {ds : List Directive} {k : Nat} {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog k)
    (hrun : exec ds (midS F) = some (S', x)) {o : Nat}
    (hsp : S'.reg .rsp = some (.ptr 0 (o : Int))) (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 8)
    (hkeep : keepsExcept used S' = true) {R : MachineState → Prop}
    (cont : ∀ st, Match (frameEnv m0 m F vars (Host.addrOf (k + ds.length)).toBitVec) S'
        st.data →
      PcOk (frameEnv m0 m F vars (Host.addrOf (k + ds.length)).toBitVec) x
        (Host.addrOf (k + ds.length)) st →
      Fr m0 m1 F N o used st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have hwf := g.wf hF.kept (vars := vars) (ret := (Host.addrOf (k + ds.length)).toBitVec)
  have hsp8 := hF.sp_toNat g (o := 8) (by have := g.f8; omega)
  refine exec_then hk hrun hwf (fun _ _ ↦ rfl) (match_mid hF) fun st hm' hpc ↦
    cont st hm' hpc ⟨?_, fun r hr hu ↦ ?_, fun i hi1 hi2 ↦ ?_, fun p hp ↦ ?_, ?_⟩
  · show st.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    show stackBelow m0 F + BitVec.ofInt 64 (o : Int) = _
    rw [BitVec.ofInt_natCast]
  · exact (hm'.regs r _ (keepsExcept_reg hkeep hr hu)).trans (hF.regs r hr hu)
  · rw [hm'.get?_mem0 hwf fun hW ↦ ?_]
    · exact hF.frame i hi1 hi2
    · have := written_frame hw hW
      rw [g.addr (by omega), g.base] at this
      have := g.le
      have := g.sp
      omega
  · rw [hm'.get?_mem0 hwf fun hW ↦ hp ?_]
    · exact hF.same p hp
    · have := written_frame hw hW
      rw [g.base] at this
      rw [inRange_N g]
      have := g.f8
      have := g.le
      have := g.sp
      omega
  · exact fun p hp ↦ hm'.kept hwf p (hF.kept p hp)

/-- **A call** at offset `0`, to a callee using `S` bytes of stack below RSP. -/
theorem call {env : Env} {l : Label} {next : Int64} {st : MachineState} (g : Geo m0 F N)
    (hF : Fr m0 m1 F N 0 used st.data) (hpc : PcOk env (.call l) next st) {S : Nat}
    (hS : F + S ≤ N) {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) (hP : StackOk st.data S → P st.data)
    (hQ : ∀ m m', Q m m' → SameOutside m.dmem m'.dmem (InRange (stackBelow m S) S) ∧ Saved m m')
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → Q st.data st'.data → Fr m0 m1 F N 8 used st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  call_then hpc hspec (hP (hF.stackOk g hS)) fun st' hpc' hrsp hq ↦
    cont st' hpc' hq (hF.call g hS hrsp (hQ _ _ hq).2 (hQ _ _ hq).1)

omit [Host] in
/-- A pushed register's slot holds it. -/
theorem load_slot [Labels] (hF : Fr m0 m1 F N 8 used m) {slots : List (Reg64 × Nat)}
    (hsl : Slots m0 m1 F slots) {vars : Nat → BitVec 64} {ret : BitVec 64} {p : Reg64 × Nat}
    (hp : p ∈ slots) : (frameEnv m0 m F vars ret).load 0 p.2 8 = m0.regs.get64 p.1 := by
  obtain ⟨h8, hle, hbs⟩ := hsl p hp
  rw [Env.load_of_bytesAt (bs := (List.range 8).map (byteOf (m0.regs.get64 p.1))) (by simp) ?_,
    ofInt_ofBytes_byteOf']
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [frame_base, Env.ofMachine_mem0, addr_add, hF.frame _ (by omega) (by omega), ← addr_add]
  exact hbs i (by simp [hi])

/-- **The epilogue**, from `midS F`, restoring the pushed registers, writing nothing. -/
theorem epilogue (g : Geo m0 F N) (hF : Fr m0 m1 F N 8 used m) {slots : List (Reg64 × Nat)}
    (hsl : Slots m0 m1 F slots) {vars : Nat → BitVec 64} {ds : List Directive} {k : Nat}
    {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog k)
    (hrun : exec ds (midS F) = some (S', x)) (hres : restores slots used S' = true)
    (hmem : S'.mem = []) :
    Eventually (step1 Host.exe) (fun st ↦
      Match (frameEnv m0 m F vars (Host.addrOf (k + ds.length)).toBitVec) S' st.data ∧
      PcOk (frameEnv m0 m F vars (Host.addrOf (k + ds.length)).toBitVec) x
        (Host.addrOf (k + ds.length)) st ∧
      SameOutside m0.dmem st.data.dmem (InRange (stackBelow m0 N) N) ∧ Saved m0 st.data)
      ⟨m, Host.addrOf k⟩ := by
  have hwf := g.wf hF.kept (vars := vars) (ret := (Host.addrOf (k + ds.length)).toBitVec)
  simp only [restores, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hres
  obtain ⟨hsl', hcs⟩ := hres
  refine exec_then hk hrun hwf (fun _ _ ↦ rfl) (match_mid hF) fun st hm' hpc ↦
    .done _ ⟨hm', hpc, fun p hp ↦ ?_, fun r hr ↦ ?_, fun p hp ↦ ?_⟩
  · rw [hm'.get?_mem0 hwf fun ⟨w, hw, _⟩ ↦ by rw [hmem] at hw; cases hw]
    exact hF.same p hp
  · have := hcs r (mem_allRegs r)
    simp only [hr, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true, beq_iff_eq,
      Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq] at this
    rcases this with ⟨p, hp, he⟩ | ⟨hu, hS⟩
    · rw [← he, hm'.regs p.1 _ (hsl' p hp)]
      exact load_slot hF hsl hp
    · rw [hm'.regs r _ hS]
      exact hF.regs r hr fun hu' ↦ hu r hu' rfl
  · rw [hm'.get?_mem0 hwf fun ⟨w, hw, _⟩ ↦ by rw [hmem] at hw; cases hw]
    exact hF.kept p hp

/-- **The epilogue, ending in `ret`**: back at the entry's return address, RSP 8 above. -/
theorem epilogue_ret (g : Geo m0 F N) (hF : Fr m0 m1 F N 8 used m) {slots : List (Reg64 × Nat)}
    (hsl : Slots m0 m1 F slots) {vars : Nat → BitVec 64} {ds : List Directive} {k : Nat}
    {S' : SState} (hk : ds.IsInfixAt Host.prog k)
    (hrun : exec ds (midS F) = some (S', .ret (.load 0 F 8))) (hres : restores slots used S' = true)
    (hmem : S'.mem = []) (hsp : S'.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int))) :
    Eventually (step1 Host.exe) (fun st ↦
      Match (frameEnv m0 m F vars (Host.addrOf (k + ds.length)).toBitVec) S' st.data ∧
      st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
      SameOutside m0.dmem st.data.dmem (InRange (stackBelow m0 N) N) ∧ Saved m0 st.data)
      ⟨m, Host.addrOf k⟩ :=
  Eventually.mono (epilogue g hF hsl hk hrun hres hmem) fun st ⟨hm', hpc, hso, hsv⟩ ↦
    ⟨hm', by
      simp only [PcOk] at hpc
      rw [hpc]
      exact load_ret g.okF (g.ret_same hF.same), by
      show st.data.regs.get64 .rsp = _
      rw [hm'.regs .rsp _ hsp]
      exact frame_rsp F 8, hso, hsv⟩

/-- **A block ending in `ret`**, from `frameS F`, in a state `m` with the entry's RSP and return
address, writing nothing and keeping the callee-saved registers. -/
theorem ret_blk (h : StackOk m0 F) (hrsp : rspOf m = rspOf m0) (hk : Kept m0.dmem m.dmem)
    (hret : ∀ j < 8, m.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j))
    {vars : Nat → BitVec 64} {ds : List Directive} {k : Nat} {S' : SState}
    (hds : ds.IsInfixAt Host.prog k) (hrun : exec ds (frameS F) = some (S', .ret (.load 0 F 8)))
    (hsp : S'.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int))) (hkeep : keeps (frameS F) S' = true)
    (hmem : S'.mem = []) :
    Eventually (step1 Host.exe) (fun st ↦ Match (frameEnv m0 m F vars) S' st.data ∧
      st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ st.data.dmem = m.dmem ∧
      Saved m st.data) ⟨m, Host.addrOf k⟩ := by
  have hwf := frame_wf (vars := vars) (ret := 0) h hk
  have hm : Match (frameEnv m0 m F vars) (frameS F) m :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show rspOf m = stackBelow m0 F + BitVec.ofInt 64 (F : Int) by
          rw [hrsp, show ((F : Nat) : Int) = ((F + 0 : Nat) : Int) from rfl, frame_rsp F 0,
            BitVec.add_zero], trivial⟩ trivial trivial trivial
  refine exec_then hds hrun hwf nofun hm fun st hm' hpc ↦ .done _ ⟨hm', ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact load_ret h hret
  · show st.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact frame_rsp F 8
  · exact hm'.dmem_eq hwf hmem
  · exact Match.saved hm hm' hwf rfl hkeep

end

end NativeRustcVmX64.Field
