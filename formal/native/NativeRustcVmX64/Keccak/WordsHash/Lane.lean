module

public import NativeRustcVmX64.Keccak.WordsHash.Inv

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): one lane of a block

Lane `j < 16` of the block whose first word `B` is in `x` goes one of two ways on whether word
`B + j` is in the slice (`LaneAt`): `laneL_step`, the word loaded from the slice (region 1, the
words from `B`) and XORed into lane `j`; `laneZ_step`, lane `j` XORed with zero. Both are
`lane_core`: a block that writes lane `j` then branches on word `B + j + 1`. Where the word is
loaded into a register in one block and XORed in another (`ValAt`): `regL_step`, `regZ_step` and
`xorReg_step`.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt load_of_wordAt)

public section

variable [Host]

/-- The frame's environment, and `startMain` matching it. -/
theorem main_env {m0 m : MachineData} (hstk : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    {L : List (Nat × BitVec 64)} {R : List (Reg64 × BitVec 64)} (hc : Ctx m0 L R 8 m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (Env.ofMachine m [(frame m0, 296)] vars ret).WF ∧
      Match (Env.ofMachine m [(frame m0, 296)] vars ret) startMain m :=
  ⟨frame_wf hstk hc.kept,
    match_ofMachine ⟨rfl, trivial⟩ ⟨rsp_eval hc.rsp rfl, trivial⟩ trivial trivial trivial⟩

/-- The environment of a loaded lane, region 1 the `sz` bytes from word `B` of the slice, and
`startL x sz` matching it. -/
theorem load_env {m0 m : MachineData} (g : Geo m0) {x : Reg64} {R : List (Reg64 × BitVec 64)}
    {B sz : Nat} (hc : HCtx m0 ((x, BitVec.ofNat 64 B) :: R) 8 m) (hsz : 0 < sz)
    (hszn : 8 * B + sz ≤ 8 * nW m0) (h8 : sz % 8 = 0) :
    (Env.ofMachine m [(frame m0, 296), (ws m0 + BitVec.ofNat 64 (8 * B), sz)]).WF ∧
      Match (Env.ofMachine m [(frame m0, 296), (ws m0 + BitVec.ofNat 64 (8 * B), sz)])
        (startL x sz) m := by
  obtain ⟨hreg, hap⟩ := slice_region g hc.kept (i0 := B) (c := sz / 8) (by omega) (by omega)
  rw [show 8 * (sz / 8) = sz by omega] at hreg hap
  refine ⟨Env.wf_of ⟨⟨frame_mapped g.stk hc.kept, frame_noWrap g.stk⟩, hreg, trivial⟩
    (List.pairwise_pair.mpr hap), match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨rsp_eval hc.rsp rfl, trivial⟩ trivial trivial ⟨?_, trivial⟩⟩
  beta_reduce
  rw [addrW_eval hc.regs.2.1 hc.regs.2.2.1]
  simp only [Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.getD_some]
  exact (BitVec.add_zero _).symm

/-- **A block that writes lane `j`** and branches on word `B + j + 1`. -/
theorem lane_core {k : Nat} {m0 m : MachineData} (g : Geo m0) {x : Reg64}
    {R R' : List (Reg64 × BitVec 64)} {A : KeccakState} {B j : Nat} (hj : j < 16)
    (hB : B ≤ nW m0) (hc : HCtx m0 ((x, BitVec.ofNat 64 B) :: R) 8 m)
    (hl : Lanes m0 m.dmem (pre A (word m0) B j))
    {rs : List (BitVec 64 × Nat)} (hb : rs[0]? = some (frame m0, 296))
    (hwf : (Env.ofMachine m rs).WF) {S0 : SState} (hm0 : Match (Env.ofMachine m rs) S0 m)
    {blk : List Directive} {s : Nat} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk S0 = some (S, xx))
    {v : Sym} (hmem : S.mem = [⟨0, 40 + 8 * j, 8, v⟩])
    (hv : v.eval (Env.ofMachine m rs) = (Keccak.lane A j ^^^ word m0 (B + j)).toBitVec)
    (hrsp : S.reg .rsp = some (.ptr 0 8))
    (hR : ∀ m', Match (Env.ofMachine m rs) S m' → RegsAt m'
      ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: (x, BitVec.ofNat 64 B) :: R'))
    {pos : Bool} {lbl : Label}
    (hexit : xx = .cond (if pos then cmpB x (j + 1) else .not (cmpB x (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k x R' A B (j + 1) sL sZ) ⟨m, Host.addrOf (k + s)⟩ := by
  rw [hexit] at hx
  exact lane_block g.stk (slotsH_low m0) (by omega) hc hl hb hwf hm0 hk hx hmem hv hrsp hR rfl
    (eval_posCmp (cmpB_eval g hc.regs.2.2.1 hc.regs.1 hB (by omega)) pos) hlab hnext

/-- **A lane in the slice**: word `B + j` loaded (region 1) and XORed into lane `j`. -/
theorem laneL_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {x : Reg64}
    {R : List (Reg64 × BitVec 64)} {A : KeccakState} {B j sz : Nat} (hj : j < 16)
    (hin : B + j < nW m0) (hsz : 8 * j + 8 ≤ sz) (hszn : 8 * B + sz ≤ 8 * nW m0)
    (h8 : sz % 8 = 0) (hc : HCtx m0 ((x, BitVec.ofNat 64 B) :: R) 8 m)
    (hl : Lanes m0 m.dmem (pre A (word m0) B j))
    {blk : List Directive} {s : Nat} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk (startL x sz) = some (S, xx))
    (hmem : S.mem =
      [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.load 1 (8 * j) 8)⟩])
    (hrsp : S.reg .rsp = some (.ptr 0 8)) {names : List Reg64}
    (hn : ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: (x, BitVec.ofNat 64 B) :: R).map
      Prod.fst = names) (hkeep : keepsRegs S names = true)
    {pos : Bool} {lbl : Label}
    (hexit : xx = .cond (if pos then cmpB x (j + 1) else .not (cmpB x (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k x R A B (j + 1) sL sZ) ⟨m, Host.addrOf (k + s)⟩ := by
  obtain ⟨hwf, hm0⟩ := load_env g hc (by omega) hszn h8
  refine lane_core g hj (by omega) hc hl rfl hwf hm0 hk hx hmem ?_ hrsp
    (fun m' hm => regsAt_keep hm hc.regs hn hkeep) hexit hlab hnext
  have hw : (Env.ofMachine m [(frame m0, 296), (ws m0 + BitVec.ofNat 64 (8 * B), sz)]).load 1
      (8 * j) 8 = (word m0 (B + j)).toBitVec :=
    load_word (r := 1) rfl hin fun t ht => slice_same g hc.same (by omega)
  simp only [Sym.eval, xor64, hw]
  rw [load_of_wordAt (r := 0) (hl j (by omega))]
  simp [pre]

/-- **A lane past the slice**: lane `j` XORed with zero. -/
theorem laneZ_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {x : Reg64}
    {R : List (Reg64 × BitVec 64)} {A : KeccakState} {B j : Nat} (hj : j < 16)
    (hB : B ≤ nW m0) (hz : nW m0 ≤ B + j) (hc : HCtx m0 ((x, BitVec.ofNat 64 B) :: R) 8 m)
    (hl : Lanes m0 m.dmem (pre A (word m0) B j))
    {blk : List Directive} {s : Nat} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startMain = some (S, xx))
    (hmem : S.mem = [⟨0, 40 + 8 * j, 8, .load 0 (40 + 8 * j) 8⟩])
    (hrsp : S.reg .rsp = some (.ptr 0 8)) {names : List Reg64}
    (hn : ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: (x, BitVec.ofNat 64 B) :: R).map
      Prod.fst = names) (hkeep : keepsRegs S names = true)
    {pos : Bool} {lbl : Label}
    (hexit : xx = .cond (if pos then cmpB x (j + 1) else .not (cmpB x (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k x R A B (j + 1) sL sZ) ⟨m, Host.addrOf (k + s)⟩ := by
  obtain ⟨hwf, hm0⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  refine lane_core g hj hB hc hl rfl hwf hm0 hk hx hmem ?_ hrsp
    (fun m' hm => regsAt_keep hm hc.regs hn hkeep) hexit hlab hnext
  simp only [Sym.eval]
  rw [load_of_wordAt (r := 0) (hl j (by omega)), word_ge hz]
  simp [pre]

/-- **A lane's word XORed from the register `t`.** -/
theorem xorReg_step {k : Nat} {m0 : MachineData} (g : Geo m0) {x t : Reg64}
    {R R' : List (Reg64 × BitVec 64)} {A : KeccakState} {B j : Nat} (hj : j < 16)
    (hB : B ≤ nW m0) {s : Nat} {st : MachineState}
    (h : ValAt m0 k ((x, BitVec.ofNat 64 B) :: R) A B j t s st)
    {blk : List Directive} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startMain = some (S, xx))
    (hmem : S.mem = [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.reg t)⟩])
    (hrsp : S.reg .rsp = some (.ptr 0 8))
    (hR : ∀ m', Match (Env.ofMachine st.data [(frame m0, 296)]) S m' → RegsAt m'
      ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: (x, BitVec.ofNat 64 B) :: R'))
    {pos : Bool} {lbl : Label}
    (hexit : xx = .cond (if pos then cmpB x (j + 1) else .not (cmpB x (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k x R' A B (j + 1) sL sZ) st := by
  obtain ⟨hc, hl, ht, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl ht hpc hR
  subst hpc
  obtain ⟨hwf, hm0⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  refine lane_core g hj hB hc hl rfl hwf hm0 hk hx hmem ?_ hrsp hR hexit hlab hnext
  simp only [Sym.eval, xor64, Env.ofMachine_regs, ht]
  rw [load_of_wordAt (r := 0) (hl j (by omega))]
  simp [pre]

/-- How a block that loads a lane's word ends: falling or jumping to `sN`. -/
@[expose] def ExitTo (k s n : Nat) (x : Exit) (sN : Nat) : Prop :=
  (x = .fall ∧ s + n = sN) ∨ ∃ l, x = .jump l ∧ Labels.label l = Host.addrOf (k + sN)

theorem exitTo_pc {env : Env} {k s n sN : Nat} {x : Exit} (h : ExitTo k s n x sN)
    {st : MachineState} (hpc : PcOk env x (Host.addrOf (k + s + n)) st) :
    st.pc = Host.addrOf (k + sN) := by
  rcases h with ⟨rfl, h⟩ | ⟨l, rfl, h⟩
  · simp only [PcOk] at hpc
    rw [hpc, Nat.add_assoc, h]
  · simp only [PcOk] at hpc
    rw [hpc, h]

/-- **A lane's word in the slice, loaded into `t`.** -/
theorem regL_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {x t : Reg64}
    {R R' : List (Reg64 × BitVec 64)} {A : KeccakState} {B j sz : Nat}
    (hin : B + j < nW m0) (hsz : 8 * j + 8 ≤ sz) (hszn : 8 * B + sz ≤ 8 * nW m0)
    (h8 : sz % 8 = 0) (hc : HCtx m0 ((x, BitVec.ofNat 64 B) :: R) 8 m)
    (hl : Lanes m0 m.dmem (pre A (word m0) B j))
    {blk : List Directive} {s : Nat} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk (startL x sz) = some (S, xx))
    (hmem : S.mem = []) (hrsp : S.reg .rsp = some (.ptr 0 8))
    (ht : S.reg t = some (.load 1 (8 * j) 8))
    (hR : ∀ m', Match (Env.ofMachine m [(frame m0, 296), (ws m0 + BitVec.ofNat 64 (8 * B), sz)])
      S m' → RegsAt m' ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: R'))
    {sN : Nat} (hexit : ExitTo k s blk.length xx sN) :
    Eventually (step1 Host.exe) (ValAt m0 k R' A B j t sN) ⟨m, Host.addrOf (k + s)⟩ := by
  obtain ⟨hwf, hm0⟩ := load_env g hc (by omega) hszn h8
  refine exec_then hk hx hwf (fun l h => by rcases hexit with ⟨rfl, -⟩ | ⟨_, rfl, -⟩ <;> cases h)
    hm0 fun st hm hpc => .done _ ⟨?_, ?_, ?_, exitTo_pc hexit hpc⟩
  · exact ctx_step g.stk (slotsH_low m0) hc hm hwf rfl hrsp (by rw [hmem]; rfl) (hR _ hm)
  · exact lanes_keep hm rfl (by rw [hmem]; nofun) hl
  · rw [hm.regs t _ ht]
    exact load_word (r := 1) rfl hin fun t ht => slice_same g hc.same (by omega)

/-- **A lane's word past the slice, zero in `t`.** -/
theorem regZ_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {x t : Reg64}
    {R R' : List (Reg64 × BitVec 64)} {A : KeccakState} {B j : Nat}
    (hz : nW m0 ≤ B + j) (hc : HCtx m0 ((x, BitVec.ofNat 64 B) :: R) 8 m)
    (hl : Lanes m0 m.dmem (pre A (word m0) B j))
    {blk : List Directive} {s : Nat} {S : SState} {xx : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startMain = some (S, xx))
    (hmem : S.mem = []) (hrsp : S.reg .rsp = some (.ptr 0 8))
    (ht : S.reg t = some (.lit 0))
    (hR : ∀ m', Match (Env.ofMachine m [(frame m0, 296)]) S m' →
      RegsAt m' ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: R'))
    {sN : Nat} (hexit : ExitTo k s blk.length xx sN) :
    Eventually (step1 Host.exe) (ValAt m0 k R' A B j t sN) ⟨m, Host.addrOf (k + s)⟩ := by
  obtain ⟨hwf, hm0⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  refine exec_then hk hx hwf (fun l h => by rcases hexit with ⟨rfl, -⟩ | ⟨_, rfl, -⟩ <;> cases h)
    hm0 fun st hm hpc => .done _ ⟨?_, ?_, ?_, exitTo_pc hexit hpc⟩
  · exact ctx_step g.stk (slotsH_low m0) hc hm hwf rfl hrsp (by rw [hmem]; rfl) (hR _ hm)
  · exact lanes_keep hm rfl (by rw [hmem]; nofun) hl
  · rw [hm.regs t _ ht, word_ge hz]
    rfl

/-- **A lane of a block, either way**: lane `j` from its loaded block (`laneL_step`) if word
`B + j` is in the slice, else from its zero block (`laneZ_step`). -/
theorem lane2_step {k : Nat} {m0 : MachineData} (g : Geo m0) {x : Reg64}
    {R : List (Reg64 × BitVec 64)} {A : KeccakState} {B j sz : Nat} (hj : j < 16)
    (hB : B ≤ nW m0) (hsz : 8 * j + 8 ≤ sz) (hszn : B + j < nW m0 → 8 * B + sz ≤ 8 * nW m0)
    (h8 : sz % 8 = 0) {names : List Reg64}
    (hn : ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: (x, BitVec.ofNat 64 B) :: R).map
      Prod.fst = names)
    {sL sZ sL' sZ' : Nat}
    {blkL : List Directive} {SL : SState} {xL : Exit}
    (hkL : blkL.IsInfixAt Host.prog (k + sL)) (hxL : exec blkL (startL x sz) = some (SL, xL))
    (hmemL : SL.mem =
      [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.load 1 (8 * j) 8)⟩])
    (hrspL : SL.reg .rsp = some (.ptr 0 8)) (hkeepL : keepsRegs SL names = true)
    {posL : Bool} {lblL : Label}
    (hexitL : xL = .cond (if posL then cmpB x (j + 1) else .not (cmpB x (j + 1))) lblL)
    (hlabL : Labels.label lblL = Host.addrOf (k + if posL then sL' else sZ'))
    (hnextL : sL + blkL.length = if posL then sZ' else sL')
    {blkZ : List Directive} {SZ : SState} {xZ : Exit}
    (hkZ : blkZ.IsInfixAt Host.prog (k + sZ)) (hxZ : exec blkZ startMain = some (SZ, xZ))
    (hmemZ : SZ.mem = [⟨0, 40 + 8 * j, 8, .load 0 (40 + 8 * j) 8⟩])
    (hrspZ : SZ.reg .rsp = some (.ptr 0 8)) (hkeepZ : keepsRegs SZ names = true)
    {posZ : Bool} {lblZ : Label}
    (hexitZ : xZ = .cond (if posZ then cmpB x (j + 1) else .not (cmpB x (j + 1))) lblZ)
    (hlabZ : Labels.label lblZ = Host.addrOf (k + if posZ then sL' else sZ'))
    (hnextZ : sZ + blkZ.length = if posZ then sZ' else sL')
    {st : MachineState} (h : LaneAt m0 k x R A B j sL sZ st) :
    Eventually (step1 Host.exe) (LaneAt m0 k x R A B (j + 1) sL' sZ') st := by
  refine lane_two (fun m hc hl hin => ?_) (fun m hc hl hz => ?_) h
  · exact laneL_step g hj hin hsz (hszn hin) h8 hc hl hkL hxL hmemL hrspL hn hkeepL hexitL hlabL
      hnextL
  · exact laneZ_step g hj hB hz hc hl hkZ hxZ hmemZ hrspZ hn hkeepZ hexitZ hlabZ hnextZ

/-- **A lane's word into the register `t`, either way**: loaded (`regL_step`) if word `B + j` is
in the slice, else zero (`regZ_step`); the registers `R'` of `R` the blocks keep. -/
theorem val2_step {k : Nat} {m0 : MachineData} (g : Geo m0) {x t : Reg64}
    {R R' : List (Reg64 × BitVec 64)} {A : KeccakState} {B j sz : Nat}
    (hsz : 8 * j + 8 ≤ sz) (hszn : B + j < nW m0 → 8 * B + sz ≤ 8 * nW m0) (h8 : sz % 8 = 0)
    (hsub : ∀ m, RegsAt m ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) ::
      (x, BitVec.ofNat 64 B) :: R) → RegsAt m ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: R'))
    {names : List Reg64}
    (hn : ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: R').map Prod.fst = names)
    {sL sZ sN : Nat}
    {blkL : List Directive} {SL : SState} {xL : Exit}
    (hkL : blkL.IsInfixAt Host.prog (k + sL)) (hxL : exec blkL (startL x sz) = some (SL, xL))
    (hmemL : SL.mem = []) (hrspL : SL.reg .rsp = some (.ptr 0 8))
    (htL : SL.reg t = some (.load 1 (8 * j) 8)) (hkeepL : keepsRegs SL names = true)
    (hexitL : ExitTo k sL blkL.length xL sN)
    {blkZ : List Directive} {SZ : SState} {xZ : Exit}
    (hkZ : blkZ.IsInfixAt Host.prog (k + sZ)) (hxZ : exec blkZ startMain = some (SZ, xZ))
    (hmemZ : SZ.mem = []) (hrspZ : SZ.reg .rsp = some (.ptr 0 8))
    (htZ : SZ.reg t = some (.lit 0)) (hkeepZ : keepsRegs SZ names = true)
    (hexitZ : ExitTo k sZ blkZ.length xZ sN)
    {st : MachineState} (h : LaneAt m0 k x R A B j sL sZ st) :
    Eventually (step1 Host.exe) (ValAt m0 k R' A B j t sN) st := by
  refine lane_two (fun m hc hl hin => ?_) (fun m hc hl hz => ?_) h
  · exact regL_step g hin hsz (hszn hin) h8 hc hl hkL hxL hmemL hrspL htL
      (fun _ hm => regsAt_keep hm (hsub m hc.regs) hn hkeepL) hexitL
  · exact regZ_step g hz hc hl hkZ hxZ hmemZ hrspZ htZ
      (fun _ hm => regsAt_keep hm (hsub m hc.regs) hn hkeepZ) hexitZ

end

end NativeRustcVmX64.WordsHash
