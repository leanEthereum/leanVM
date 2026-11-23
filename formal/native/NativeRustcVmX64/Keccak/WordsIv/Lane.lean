module

public import NativeRustcVmX64.Keccak.WordsIv.Inv
public import NativeRustcVmX64.Keccak.WordsIv.Blocks
public import NativeRustcVmX64.Code.Vm.IvWord.Names

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): one lane of a block

Lane `j` of the block whose first word index `B` is in `x` goes one of two ways on whether `B + j`
is below the count (`LaneAt`, `WordsHash.LaneG` with the closure's words `wv`): its call block
calls `iv_word` on the index in RDX (`call_step`, `ValAt`: the word in RAX) and its XOR block XORs
RAX into lane `j` (`xorV_step`); its zero block leaves lane `j` (`zero_step`). Both end with RDX
the next index and the branch on it (`WordsHash.lane_block`). The registers between the lanes:
R13 the count, R12 the bytecode, R15 its word count, `x` the index `B` (`RL`), RDX the lane's
index (`RD`). `lane2_step`: a lane either way, `laneF_step`: a lane of a whole block (its words
are below the count).
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt load_of_wordAt)
open NativeRustcVmX64.WordsHash (frame Ctx Lanes pre RegsAt LaneG keepsRegs ctx_step lanes_keep
  lane_block lane_two eval_posCmp regsAt_keep regsAt_cons regsAt_saved rsp_eval frame_wf xor64
  add64)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- The registers of the body: R13 the count, R12 the bytecode, R15 its word count, `x` the
block's first word index `B`, then `Rr`. -/
def RL (m0 : MachineData) (x : Reg64) (B : Nat) (Rr : List (Reg64 × BitVec 64)) :
    List (Reg64 × BitVec 64) :=
  (.r13, m0.regs.get64 .rsi) :: (.r12, bc m0) :: (.r15, m0.regs.get64 .r8) ::
    (x, BitVec.ofNat 64 B) :: Rr

/-- `RL`, RDX the index `B + j` first. -/
def RD (m0 : MachineData) (x : Reg64) (B : Nat) (Rr : List (Reg64 × BitVec 64)) (j : Nat) :
    List (Reg64 × BitVec 64) :=
  (.rdx, BitVec.ofNat 64 (B + j)) :: RL m0 x B Rr

variable [Host]

/-- **Lane `j`'s word in RAX**, at `s`, the registers `R`. -/
def ValAt (m0 : MachineData) (k : Nat) (R : List (Reg64 × BitVec 64)) (A : KeccakState)
    (B j s : Nat) (st : MachineState) : Prop :=
  Ctx m0 (slotsI m0) R 8 st.data ∧ Lanes m0 st.data.dmem (pre A (wv m0) B j) ∧
    st.data.regs.get64 .rax = (wv m0 (B + j)).toBitVec ∧ st.pc = Host.addrOf (k + s)

/-- **Before lane `j`** (`LaneG` with the closure's words and count). -/
abbrev LaneAt (m0 : MachineData) (k : Nat) (R : List (Reg64 × BitVec 64)) (A : KeccakState)
    (B j sL sZ : Nat) : MachineState → Prop :=
  LaneG m0 k (slotsI m0) R (wv m0) (cnt m0) A B j sL sZ

end

public section

variable [Host]

/-- A label of a block. -/
theorem label_at {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) {l : Label} {b' : List Directive} (h : b = .label l :: b') :
    Labels.label l = Host.addrOf (k + j) := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

/-- The frame's environment, and `startMain` matching it. -/
theorem main_env {m0 m : MachineData} (hstk : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    {L : List (Nat × BitVec 64)} {R : List (Reg64 × BitVec 64)} (hc : Ctx m0 L R 8 m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (Env.ofMachine m [(frame m0, 296)] vars ret).WF ∧
      Match (Env.ofMachine m [(frame m0, 296)] vars ret) startMain m :=
  ⟨frame_wf hstk hc.kept,
    match_ofMachine ⟨rfl, trivial⟩ ⟨rsp_eval hc.rsp rfl, trivial⟩ trivial trivial trivial⟩

/-- **A call block**: `iv_word` of the index `i` in the register `r`, R12 the bytecode, R15 its
word count; the word in RAX, the callee-saved registers `R'` kept. -/
theorem call_step (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} {m0 m : MachineData} (g : Geo m0)
    {R R' : List (Reg64 × BitVec 64)} (hc : Ctx m0 (slotsI m0) R 8 m) {f : Nat → UInt64}
    (hl : Lanes m0 m.dmem f) {blk : List Directive} {s : Nat} {S : SState}
    (hk : blk.IsInfixAt Host.prog (k + s))
    (hx : exec blk startMain = some (S, .call NativeRustcVmX64.Vm.IvWord.entryLabel))
    (hmem : S.mem = [⟨0, 0, 8, .retAddr⟩]) (hrsp : S.reg .rsp = some (.ptr 0 0))
    (hrdi : S.reg .rdi = some (.reg .r12)) (hrsi : S.reg .rsi = some (.reg .r15))
    {r : Reg64} (hrdx : S.reg .rdx = some (.reg r))
    (h12 : m.regs.get64 .r12 = bc m0) (h15 : m.regs.get64 .r15 = m0.regs.get64 .r8)
    {i : Nat} (hr : m.regs.get64 r = BitVec.ofNat 64 i) (hi : i < cnt m0)
    (hR' : RegsAt m R') {names : List Reg64} (hn : R'.map Prod.fst = names)
    (hkeep : keepsRegs S names = true) (hcs : names.all calleeSaved = true)
    {sN : Nat} (hsN : s + blk.length = sN) :
    Eventually (step1 Host.exe) (fun st => Ctx m0 (slotsI m0) R' 8 st.data ∧
      Lanes m0 st.data.dmem f ∧ st.data.regs.get64 .rax = (wv m0 i).toBitVec ∧
      st.pc = Host.addrOf (k + sN)) ⟨m, Host.addrOf (k + s)⟩ := by
  subst hsN
  let env := Env.ofMachine m [(frame m0, 296)] (fun _ => 0)
    (Host.addrOf (k + s + blk.length)).toBitVec
  have hwf : env.WF := frame_wf g.stk hc.kept
  have hm : Match env startMain m :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨rsp_eval hc.rsp rfl, trivial⟩ trivial trivial trivial
  refine exec_then hk hx hwf (fun _ _ => rfl) hm fun st1 hm1 hpc1 => ?_
  have hc1 : Ctx m0 (slotsI m0) R' 0 st1.data :=
    ctx_step g.stk (slotsI_low m0) hc hm1 hwf rfl hrsp (by rw [hmem]; rfl)
      (regsAt_keep hm1 hR' hn hkeep)
  have hl1 : Lanes m0 st1.data.dmem f := lanes_keep hm1 rfl (fun w hw _ => by
    rw [hmem, List.mem_singleton] at hw
    subst hw
    decide) hl
  have hrdi1 : st1.data.regs.get64 .rdi = bc m0 := (hm1.regs .rdi _ hrdi).trans h12
  have hrsi1 : st1.data.regs.get64 .rsi = m0.regs.get64 .r8 := (hm1.regs .rsi _ hrsi).trans h15
  have hrdx1 : st1.data.regs.get64 .rdx = BitVec.ofNat 64 i := (hm1.regs .rdx _ hrdx).trans hr
  refine call_iv hiv g hc1 hrdi1 hrsi1 hrdx1 hi hpc1
    fun st2 hpc2 hrsp2 hd2 hsv2 hax2 => .done _ ⟨?_, by rw [hd2]; exact hl1, hax2, ?_⟩
  · refine ⟨?_, regsAt_saved hc1.regs hsv2.1 hn hcs, by rw [hd2]; exact hc1.slots,
      by rw [hd2]; exact hc1.saved, by rw [hd2]; exact hc1.same, by rw [hd2]; exact hc1.kept⟩
    rw [hrsp2, hc1.rsp, BitVec.add_assoc]
    rfl
  · rw [hpc2, Nat.add_assoc]

/-- **An XOR block**: RAX into lane `j`, the registers `R'`, the branch `c` on index
`B + j + 1`. -/
theorem xorV_step {k : Nat} {m0 : MachineData} (g : Geo m0) {R R' : List (Reg64 × BitVec 64)}
    {A : KeccakState} {B j s : Nat} (hj : j < 25) {st : MachineState}
    (h : ValAt m0 k R A B j s st) {blk : List Directive} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startMain = some (S, xx))
    (hmem : S.mem = [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.reg .rax)⟩])
    (hrsp : S.reg .rsp = some (.ptr 0 8))
    (hR : ∀ m m', RegsAt m R → Match (Env.ofMachine m [(frame m0, 296)]) S m' → RegsAt m' R')
    {c : SBool} {lbl : Label} (hexit : xx = .cond c lbl) {pos : Bool}
    (hev : ∀ m, RegsAt m R →
      c.eval (Env.ofMachine m [(frame m0, 296)]) = (pos == decide (B + (j + 1) < cnt m0)))
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k R' A B (j + 1) sL sZ) st := by
  obtain ⟨hc, hl, hax, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hax hpc
  subst hpc
  obtain ⟨hwf, hm0⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  refine lane_block g.stk (slotsI_low m0) hj hc hl rfl hwf hm0 hk hx hmem ?_ hrsp
    (fun m' hm => hR m m' hc.regs hm) hexit (hev m hc.regs) hlab hnext
  simp only [Sym.eval, xor64, Env.ofMachine_regs, hax]
  rw [load_of_wordAt (r := 0) (hl j hj)]
  simp [pre]

/-- **A zero block**: lane `j` kept (its word zero), the registers `R'`, the branch `c` on index
`B + j + 1`. -/
theorem zero_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {R R' : List (Reg64 × BitVec 64)}
    {A : KeccakState} {B j s : Nat} (hj : j < 25) (hz : cnt m0 ≤ B + j)
    (hc : Ctx m0 (slotsI m0) R 8 m) (hl : Lanes m0 m.dmem (pre A (wv m0) B j))
    {blk : List Directive} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startMain = some (S, xx))
    (hmem : S.mem = [⟨0, 40 + 8 * j, 8, .load 0 (40 + 8 * j) 8⟩])
    (hrsp : S.reg .rsp = some (.ptr 0 8))
    (hR : ∀ m', Match (Env.ofMachine m [(frame m0, 296)]) S m' → RegsAt m' R')
    {c : SBool} {lbl : Label} (hexit : xx = .cond c lbl) {pos : Bool}
    (hev : c.eval (Env.ofMachine m [(frame m0, 296)]) = (pos == decide (B + (j + 1) < cnt m0)))
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k R' A B (j + 1) sL sZ) ⟨m, Host.addrOf (k + s)⟩ := by
  obtain ⟨hwf, hm0⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  refine lane_block g.stk (slotsI_low m0) hj hc hl rfl hwf hm0 hk hx hmem ?_ hrsp hR hexit hev
    hlab hnext
  simp only [Sym.eval]
  rw [load_of_wordAt (r := 0) (hl j hj), wv_of_ge hz]
  simp [pre]

/-- The next index, `x + (j + 1)`. -/
theorem rdx_next {env : Env} {x : Reg64} {B j : Nat} (hx : env.regs x = BitVec.ofNat 64 B) :
    (Sym.bin .add .W64 (.reg x) (.lit (j + 1))).eval env = BitVec.ofNat 64 (B + (j + 1)) := by
  simp only [Sym.eval, add64, hx, BitVec.ofNat_add_ofNat]

/-- The registers after an XOR or zero block: RDX the next index, `RL` kept. -/
theorem regs_next {m0 m m' : MachineData} {x : Reg64} {B j : Nat} {Rr : List (Reg64 × BitVec 64)}
    {S : SState} (hm : Match (Env.ofMachine m [(frame m0, 296)]) S m')
    (hRL : RegsAt m (RL m0 x B Rr)) (hrdx : S.reg .rdx = some (.bin .add .W64 (.reg x) (.lit (j + 1))))
    {names : List Reg64} (hn : (RL m0 x B Rr).map Prod.fst = names)
    (hkeep : keepsRegs S names = true) : RegsAt m' (RD m0 x B Rr (j + 1)) :=
  regsAt_cons ((hm.regs .rdx _ hrdx).trans (rdx_next hRL.2.2.2.1)) (regsAt_keep hm hRL hn hkeep)

/-- The branch on index `B + j + 1`, `x` the index `B`. -/
theorem ev_next {m0 m : MachineData} (g : Geo m0) {x : Reg64} {B j : Nat}
    {Rr : List (Reg64 × BitVec 64)} (hRL : RegsAt m (RL m0 x B Rr)) (hB : B + (j + 1) < 2 ^ 32)
    (pos : Bool) :
    (if pos then cmpI x (j + 1) else .not (cmpI x (j + 1))).eval
      (Env.ofMachine m [(frame m0, 296)]) = (pos == decide (B + (j + 1) < cnt m0)) :=
  eval_posCmp (cmpI_eval g hRL.2.2.2.1 hRL.1 hB) pos

/-- **A lane, either way**: from its call block and XOR block if index `B + j` is below the
count, else from its zero block; RDX (`r`, from `R`) the index before, `RD … (j + 1)` after. -/
theorem lane2_step (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} {m0 : MachineData} (g : Geo m0) {x : Reg64}
    {B j : Nat} {Rr R : List (Reg64 × BitVec 64)} {A : KeccakState} (hj : j < 25)
    (hB : B + (j + 1) < 2 ^ 32) (hsub : ∀ m, RegsAt m R → RegsAt m (RL m0 x B Rr))
    {r : Reg64} (hrR : ∀ m, RegsAt m R → m.regs.get64 r = BitVec.ofNat 64 (B + j))
    {names : List Reg64} (hn : (RL m0 x B Rr).map Prod.fst = names)
    (hcs : names.all calleeSaved = true)
    {sL sZ sV sL' sZ' : Nat}
    {blkC : List Directive} {SC : SState} (hkC : blkC.IsInfixAt Host.prog (k + sL))
    (hxC : exec blkC startMain = some (SC, .call NativeRustcVmX64.Vm.IvWord.entryLabel))
    (hmemC : SC.mem = [⟨0, 0, 8, .retAddr⟩]) (hrspC : SC.reg .rsp = some (.ptr 0 0))
    (hrdiC : SC.reg .rdi = some (.reg .r12)) (hrsiC : SC.reg .rsi = some (.reg .r15))
    (hrdxC : SC.reg .rdx = some (.reg r)) (hkeepC : keepsRegs SC names = true)
    (hsV : sL + blkC.length = sV)
    {blkX : List Directive} {SX : SState} {xX : Exit} (hkX : blkX.IsInfixAt Host.prog (k + sV))
    (hxX : exec blkX startMain = some (SX, xX))
    (hmemX : SX.mem =
      [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.reg .rax)⟩])
    (hrspX : SX.reg .rsp = some (.ptr 0 8))
    (hrdxX : SX.reg .rdx = some (.bin .add .W64 (.reg x) (.lit (j + 1))))
    (hkeepX : keepsRegs SX names = true) {posX : Bool} {lblX : Label}
    (hexitX : xX = .cond (if posX then cmpI x (j + 1) else .not (cmpI x (j + 1))) lblX)
    (hlabX : Labels.label lblX = Host.addrOf (k + if posX then sL' else sZ'))
    (hnextX : sV + blkX.length = if posX then sZ' else sL')
    {blkZ : List Directive} {SZ : SState} {xZ : Exit} (hkZ : blkZ.IsInfixAt Host.prog (k + sZ))
    (hxZ : exec blkZ startMain = some (SZ, xZ))
    (hmemZ : SZ.mem = [⟨0, 40 + 8 * j, 8, .load 0 (40 + 8 * j) 8⟩])
    (hrspZ : SZ.reg .rsp = some (.ptr 0 8))
    (hrdxZ : SZ.reg .rdx = some (.bin .add .W64 (.reg x) (.lit (j + 1))))
    (hkeepZ : keepsRegs SZ names = true) {posZ : Bool} {lblZ : Label}
    (hexitZ : xZ = .cond (if posZ then cmpI x (j + 1) else .not (cmpI x (j + 1))) lblZ)
    (hlabZ : Labels.label lblZ = Host.addrOf (k + if posZ then sL' else sZ'))
    (hnextZ : sZ + blkZ.length = if posZ then sZ' else sL')
    {st : MachineState} (h : LaneAt m0 k R A B j sL sZ st) :
    Eventually (step1 Host.exe) (LaneAt m0 k (RD m0 x B Rr (j + 1)) A B (j + 1) sL' sZ') st := by
  refine lane_two (fun m hc hl hin => ?_) (fun m hc hl hz => ?_) h
  · have hRL := hsub m hc.regs
    refine Eventually.bind (call_step hiv g hc hl hkC hxC hmemC hrspC hrdiC hrsiC hrdxC hRL.2.1
      hRL.2.2.1 (hrR m hc.regs) hin hRL hn hkeepC hcs hsV) fun st h => ?_
    exact xorV_step g hj h hkX hxX hmemX hrspX
      (fun _ _ hR hm => regs_next hm hR hrdxX hn hkeepX) hexitX
      (fun _ hR => ev_next g hR hB posX) hlabX hnextX
  · have hRL := hsub m hc.regs
    exact zero_step g hj hz hc hl hkZ hxZ hmemZ hrspZ
      (fun _ hm => regs_next hm hRL hrdxZ hn hkeepZ) hexitZ (ev_next g hRL hB posZ) hlabZ hnextZ

/-- **A lane of a whole block**: index `B + j` is below the count, the call block and the XOR
block. -/
theorem laneF_step (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} {m0 : MachineData} (g : Geo m0) {x : Reg64}
    {B j : Nat} {Rr R : List (Reg64 × BitVec 64)} {A : KeccakState} (hj : j < 25)
    (hin : B + j < cnt m0) (hB : B + (j + 1) < 2 ^ 32)
    (hsub : ∀ m, RegsAt m R → RegsAt m (RL m0 x B Rr))
    {r : Reg64} (hrR : ∀ m, RegsAt m R → m.regs.get64 r = BitVec.ofNat 64 (B + j))
    {names : List Reg64} (hn : (RL m0 x B Rr).map Prod.fst = names)
    (hcs : names.all calleeSaved = true)
    {sL sZ sV sL' sZ' : Nat}
    {blkC : List Directive} {SC : SState} (hkC : blkC.IsInfixAt Host.prog (k + sL))
    (hxC : exec blkC startMain = some (SC, .call NativeRustcVmX64.Vm.IvWord.entryLabel))
    (hmemC : SC.mem = [⟨0, 0, 8, .retAddr⟩]) (hrspC : SC.reg .rsp = some (.ptr 0 0))
    (hrdiC : SC.reg .rdi = some (.reg .r12)) (hrsiC : SC.reg .rsi = some (.reg .r15))
    (hrdxC : SC.reg .rdx = some (.reg r)) (hkeepC : keepsRegs SC names = true)
    (hsV : sL + blkC.length = sV)
    {blkX : List Directive} {SX : SState} {xX : Exit} (hkX : blkX.IsInfixAt Host.prog (k + sV))
    (hxX : exec blkX startMain = some (SX, xX))
    (hmemX : SX.mem =
      [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.reg .rax)⟩])
    (hrspX : SX.reg .rsp = some (.ptr 0 8))
    (hrdxX : SX.reg .rdx = some (.bin .add .W64 (.reg x) (.lit (j + 1))))
    (hkeepX : keepsRegs SX names = true) {posX : Bool} {lblX : Label}
    (hexitX : xX = .cond (if posX then cmpI x (j + 1) else .not (cmpI x (j + 1))) lblX)
    (hlabX : Labels.label lblX = Host.addrOf (k + if posX then sL' else sZ'))
    (hnextX : sV + blkX.length = if posX then sZ' else sL')
    {st : MachineState} (h : LaneAt m0 k R A B j sL sZ st) :
    Eventually (step1 Host.exe) (LaneAt m0 k (RD m0 x B Rr (j + 1)) A B (j + 1) sL' sZ') st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  simp only [hin, ↓reduceIte] at hpc
  subst hpc
  have hRL := hsub m hc.regs
  refine Eventually.bind (call_step hiv g hc hl hkC hxC hmemC hrspC hrdiC hrsiC hrdxC hRL.2.1
    hRL.2.2.1 (hrR m hc.regs) hin hRL hn hkeepC hcs hsV) fun st h => ?_
  exact xorV_step g hj h hkX hxX hmemX hrspX
    (fun _ _ hR hm => regs_next hm hR hrdxX hn hkeepX) hexitX
    (fun _ hR => ev_next g hR hB posX) hlabX hnextX

end

end NativeRustcVmX64.WordsIv
