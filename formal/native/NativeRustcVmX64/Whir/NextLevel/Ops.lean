module

public import NativeRustcVmX64.Whir.NextLevel.Zero
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names

/-!
# `next_level`: the query weights and the openings (x86-64)

From the zeroing loop's end (`b18`, `H17`): the query count saturated (RBP), the queries' address
(R13), the zeroed scratch copied over the query weights (`memcpy(sp + 4448, sp + 760, 3680)`),
the count stored at `4440` and `powers(λ, n)` at `4448` (`b19`), the queries' address stored at
`120` and the openings read into the `Option<Rows>` at `760` (`b20`, `query_openings`), its tag
tested (`b21`, `None` to `NativeRustcVmX64.Vm.NextLevel.label_13`): `ops`, to `b22` with `H22`.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel
open NativeRustcVm.Sumcheck (RowsAt OptRowsAt openingsWords)
open NativeVm (phaseBase phaseWords)

@[expose] public section

/-- The callee-saved registers from `b18` on: the index (RBX), `μ` (R12), the `TState` (R14), the
level's fold (R15), the query count (RBP), the queries' address (R13). -/
structure RK (level : Whir.Level) (m0 : MachineData) (n : Nat) (d : MachineData) : Prop where
  rbx : reg d .rbx = reg m0 .rsi
  r12 : reg d .r12 = reg m0 .r9
  r14 : reg d .r14 = tA m0
  r15 : (reg d .r15).toNat = level.fold
  rbp : reg d .rbp = BitVec.ofNat 64 n
  r13 : reg d .r13 = pA m0 + BitVec.ofNat 64 61360

/-- At `b22`: the openings `rows` read (the `Rows` at `760`, the openings at `op`), the query
weights at `4448` (their count at `4440`), the queries' address at `120`, the `TState` at its
state `s9`. -/
structure H22 [Labels] (a : DecArea) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (xs ood : Array EW) (v lam : EW)
    (qs : Array UInt64) (rows : Array (Array UInt64)) (op : BitVec 64) (s9 : TState)
    (d : MachineData) : Prop where
  K : K level w rounds m0 72 d
  rk : RK level m0 qs.size d
  ff : FF m0 xs ood v lam d.dmem
  size : xs.size = level.fold
  osize : ood.size = (reg m0 .r9).toNat
  qsz : qs.size ≤ queryCap
  qbuf : NativeRustcVm.BufWordsAt d.dmem (qA m0) queryCap qs.toList
  w120 : NativeRustcVm.WordAt d.dmem (loc m0 120) (.ofBitVec (pA m0 + BitVec.ofNat 64 61360))
  w4440 : NativeRustcVm.WordAt d.dmem (loc m0 4440) qs.size.toUInt64
  pw : NativeRustcVm.EWsAt d.dmem (loc m0 4448) (powers lam qs.size).toList
  rows : RowsAt d.dmem (loc m0 760) op rows
  opIn : WhirIn m0 op (8 * openingsWords) nextLevelStack
  ts : TStateAt d.dmem (tA m0) a s9
  opBounds : a.words.toNat ≤ op.toNat ∧
    op.toNat + 8 * openingsWords ≤ a.words.toNat + 8 * a.len

end

public section

theorem RK.saved {level : Whir.Level} {m0 d d' : MachineData} {n : Nat} (h : RK level m0 n d)
    (hs : ∀ r, calleeSaved r = true → reg d' r = reg d r) : RK level m0 n d' :=
  ⟨(hs .rbx rfl).trans h.rbx, (hs .r12 rfl).trans h.r12, (hs .r14 rfl).trans h.r14,
    by rw [hs .r15 rfl]; exact h.r15, (hs .rbp rfl).trans h.rbp, (hs .r13 rfl).trans h.r13⟩

theorem RK.six {level : Whir.Level} {m0 d d' : MachineData} {n : Nat} (h : RK level m0 n d)
    (hs : ∀ r ∈ six, reg d' r = reg d r) : RK level m0 n d' :=
  h.saved fun r hr ↦ hs r (cs_six hr)

theorem powers_size' (b : EW) (n : Nat) : (powers b n).size = n := by
  unfold powers
  suffices ∀ (l : List Nat) (acc : Array EW × EW),
      (l.foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) acc).1.size =
        acc.1.size + l.length by
    rw [this]; simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp; omega

/-- `queryOpenings` that returned: its phase existed. -/
theorem qo_lt {i : Nat} {qs : Array UInt64} {s s' : TState} {rows : Array (Array UInt64)}
    (h : (queryOpenings i qs).run s = some (rows, s')) : s.phase < s.openings.size := by
  rw [NativeVm.Equiv.queryOpenings_run] at h
  split at h
  · rename_i r ph _ hph
    exact (Array.getElem?_eq_some_iff.mp hph).1
  · cases h

theorem ult_ofNat {n c : Nat} (hn : n < c) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 c) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem vN_eval [Labels] (env : Env) {n : Nat} (h : env.regs .rax = BitVec.ofNat 64 n)
    (hn : n < 231) : vN.eval env = BitVec.ofNat 64 n := by
  simp only [vN, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]

theorem vQ_eval [Labels] (env : Env) {n : Nat} (h : env.regs .rax = BitVec.ofNat 64 n)
    (hn : n < 231) {p : BitVec 64} (hl : env.load 0 8184 8 = p) :
    vQ.eval env = p + BitVec.ofNat 64 61360 := by
  simp only [vQ, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h, hl,
    ult_ofNat hn (by decide), Bool.not_true, Bool.false_eq_true, ite_false]

theorem cRows_eval [Labels] (env : Env) {x : BitVec 64} (hl : env.load 0 760 8 = x) :
    cRows.eval env = (x == BitVec.ofNat 64 0) := by
  simp only [cRows, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl]

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

/-- Frame ranges apart. -/
theorem Ctx.apart_ll (c : Ctx a s level w rounds m0) {o n o' n' : Nat} (ho : o < 8192)
    (ho' : o' < 8192) (hd : o + n ≤ o' ∨ o' + n' ≤ o) :
    NativeRustcVm.Apart (loc m0 o) n (loc m0 o') n' := by
  unfold NativeRustcVm.Apart
  rw [c.loc_toNat (by omega), c.loc_toNat (by omega)]
  omega

/-- The decoded area as an input. -/
theorem Ctx.decIn (c : Ctx a s level w rounds m0) :
    WhirIn m0 a.words (8 * a.len) nextLevelStack :=
  ⟨c.ts.footprint.2.1, c.wt.2.2.2.1.2.1⟩

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The query weights and the openings**: `b18` to `b21`, to `b22` with `H22`. -/
theorem ops (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hpw : Spec (Labels.label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hqo : ∀ a s Q, Spec (Labels.label NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    {xs ood : Array EW} {v lam : EW} {qs : Array UInt64} {s8 : TState} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b18Offset))
    (hH : H17 a level w rounds m0 xs ood v lam qs s8 st.data)
    (hrun : runN level w rounds m0 s =
      tail8 (reg m0 .rsi).toNat (reg m0 .r9).toNat w rounds xs ood v qs lam s8) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s level w rounds m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b22Offset) ∧ ∃ rows op s9, runN level w rounds m0 s =
        some (glueLevel w lam (reg m0 .r9).toNat ood v qs (powers lam qs.size)
          (batchedOf (reg m0 .rsi).toNat (reg m0 .r9).toNat rounds xs qs rows
            (powers lam qs.size)), s9) ∧
        H22 a level w rounds m0 xs ood v lam qs rows op s9 st'.data)) st := by
  have g := c.geo
  have hK := hH.K
  have hxs : xs.size ≤ 6 := by rw [hH.size]; exact c.fold
  have hos : ood.size ≤ 30 := by rw [hH.osize]; exact c.mu
  have hqn : qs.size ≤ 230 := by have := hH.qbuf.1; rwa [Array.length_toList] at this
  have hqa := c.qA_toNat
  -- `b18`: the count, the queries' address, `memcpy(sp + 4448, sp + 760, 3680)`
  have hwfCopy := c.got_wf hK.fr
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b19Offset)).toBitVec)
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) exit_b18 hwfCopy
    (fun _ _ => rfl) hpc (c.m_copy hK.fr) fun st1 hm1 hpc1 => ?_
  obtain ⟨hfr1, hs1⟩ := c.blk hK.fr hwfCopy hm1 ok_b18.1
    (hi := 8128) le_rfl (by decide +kernel)
  have h80 := Ctx.bytes_blk hwfCopy hm1 (writesIn_of_mid ok_b18.1) ok_b18.2.1
    (by simp [NativeRustcVm.length_wordBytes])
    (by intro p hp; simp only [List.mem_singleton] at hp; subst p; left; decide) hK.w80
  have hK1 := c.K_frame hK hfr1 (by omega) hs1 h80
  have hz1 := keepZ_blk hwfCopy hm1 (writesIn_of_mid ok_b18.1) ok_b18.2.1 (by decide)
  obtain ⟨-, -, hrdi1, hrsi1, hrdx1, hrbp1, hr131, hkr1⟩ := ok_b18
  let env1 := argEnv m0 st.data 8176 8 [(gotAddr "memcpy", 8)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b19Offset)).toBitVec
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b18 copyS).reg r = some v →
      reg st1.data r = v.eval env1 := fun h ↦ hm1.regs _ _ h
  have hrax : env1.regs .rax = BitVec.ofNat 64 qs.size := hH.rax
  have h8184 : env1.load 0 8184 8 = pA m0 :=
    load_ofMachine (r := 0) (o := 8184) rfl (c.arg_keep hK.fr.same)
  have hdi1 : reg st1.data .rdi = loc m0 4448 := (e1 hrdi1).trans (eval_ptr0A 4448)
  have hsi1 : reg st1.data .rsi = loc m0 760 := (e1 hrsi1).trans (eval_ptr0A 760)
  have hdx1 : (reg st1.data .rdx).toNat = 3680 := by rw [e1 hrdx1]; rfl
  have hRK1 : RK level m0 qs.size st1.data :=
    ⟨(e1 (hkr1 .rbx (by simp))).trans hH.rbx, (e1 (hkr1 .r12 (by simp))).trans hH.r12,
      (e1 (hkr1 .r14 (by simp))).trans hH.r14, by rw [e1 (hkr1 .r15 (by simp))]; exact hH.r15,
      (e1 hrbp1).trans (vN_eval env1 hrax (by omega)),
      (e1 hr131).trans (vQ_eval env1 hrax (by omega) h8184)⟩
  have hts1 := c.ts_frame (hi := 8128) (by omega) (hm1.kept hwfCopy) hs1 hH.ts
  have hqb1 := c.qbuf_frame (hi := 8128) (by omega) hs1 hH.qbuf
  have hat1 := c.at_call (o := 64) (by omega) hK1.fr
  have hle1 : 8176 - 64 + 0 ≤ nextLevelStack := by decide
  have hpre1 : MemcpyPre st1.data := by
    have l1 := c.inLoc (o := 64) (by omega) hK1.fr hle1 (j := 4448) (n := 3680) (by omega)
      (by omega)
    have l2 := c.inLoc (o := 64) (by omega) hK1.fr hle1 (j := 760) (n := 3680) (by omega)
      (by omega)
    simp only [MemcpyPre, hdi1, hsi1, hdx1]
    refine ⟨(c.sctx (F := 8176 - 64) (by decide)).stackOk hat1 hle1, l1.1.1, l2.1.1, l1.1.2,
      l2.1.2, c.apart_ll (by omega) (by omega) (by omega), ?_⟩
    rw [hK1.fr.frame.sp]
    exact c.apart_ll (by omega) (by omega) (by omega)
  refine call_then hpc1 hmc hpre1 fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨-, -, hch2, hsv2⟩ := hq
  rw [hdi1, hdx1] at hch2
  have hch2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 4448) 3680 q ∨
        NativeRustcVm.InRange (stackBelow st1.data 0) 0 q) :=
    NativeRustcVm.SameOutside.mono hch2 fun q hq ↦ Or.inl hq
  obtain ⟨hK2, hkeep2⟩ := c.K_call hK1 hle1 hsv2 hrsp2 (lo := 4448) (n := 3680) (by omega)
    (by omega) (fun q hq ↦ Or.inr (Or.inl hq)) hch2'
  have hz2 : KeepZ m0 st1.data.dmem st2.data.dmem :=
    keepZ_call (o := 64) hkeep2 (by omega) (by decide)
  have hRK2 := hRK1.saved hsv2.1
  have hts2 := c.ts_call (o := 64) (by omega) hK1.fr hle1 hsv2
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch2' hts1
  have hqb2 := c.qbuf_call (o := 64) (by omega) hK1.fr hle1 hch2' (lo := 4448) (n := 3680)
    (by omega) (fun q hq ↦ Or.inr (Or.inl hq)) hqb1
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b19Offset) := hpc2
  -- `b19`: the count stored, `powers(λ, sp + 4448, n)`
  have hff2 : FF m0 xs ood v lam st2.data.dmem :=
    hH.ff.keep (KeepZ.trans (KeepZ.trans hz1 hz2) (KeepZ.of_eq rfl)) hxs hos
  refine blk_stepZ c b19_in_code (by simp [b19]) hp exit_b19 ok_b19.1 ok_b19.2.1 (by decide)
    (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl <;> omega) hK2 hpc2'
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b20Offset)).toBitVec) (fun _ _ ↦ rfl) fun st3 hm3 hpc3 hK3 hs3 hz3 ↦ ?_
  obtain ⟨hmid3, hW3, hw4440, hrdi3, hrsi3, hrdx3, hrcx3, hkr3⟩ := ok_b19
  let env3 := argEnv m0 st2.data 8176 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b20Offset)).toBitVec
  have e3 : ∀ {r : Reg64} {v : Sym}, (after b19 retS).reg r = some v →
      reg st3.data r = v.eval env3 := fun h ↦ hm3.regs _ _ h
  have hRK3 := hRK2.six fun r hr ↦ e3 (hkr3 r hr)
  have hdi3 : reg st3.data .rdi = lam.c0.toBitVec :=
    (e3 hrdi3).trans (load_ofMachine (r := 0) (o := 96) rfl hff2.l0)
  have hsi3 : reg st3.data .rsi = lam.c1.toBitVec :=
    (e3 hrsi3).trans (load_ofMachine (r := 0) (o := 88) rfl hff2.l1)
  have hdx3 : reg st3.data .rdx = loc m0 4448 := (e3 hrdx3).trans (eval_ptr0A 4448)
  have hcx3 : (reg st3.data .rcx).toNat = qs.size := by
    rw [e3 hrcx3]
    show (reg st2.data .rbp).toNat = _
    rw [hRK2.rbp, BitVec.toNat_ofNat]
    omega
  have h4440 : NativeRustcVm.WordAt st3.data.dmem (loc m0 4440) qs.size.toUInt64 :=
    wordAt_written hm3 (r := 0) (o := 4440) rfl (by omega) hw4440 hRK2.rbp
  have hts3 := c.ts_frame (hi := 8128) (by omega) (hm3.kept (c.wf0 hK2.fr.frame.kept)) hs3 hts2
  have hqb3 := c.qbuf_frame (hi := 8128) (by omega) hs3 hqb2
  have hat3 := c.at_call (o := 64) (by omega) hK3.fr
  have hle3 : 8176 - 64 + powersStack ≤ nextLevelStack := by decide
  have hpre3 : PowersPre st3.data := by
    refine ⟨(c.sctx (F := 8176 - 64) (by decide)).stackOk hat3 hle3, ?_⟩
    rw [hdx3]
    exact c.sliceLoc (o := 64) (by omega) hK3.fr hle3 (by omega) (by rw [hcx3]; omega)
  refine call_then hpc3 hpw hpre3 fun st4 hpc4 hrsp4 hq ↦ ?_
  obtain ⟨hpow, hch4, hsv4⟩ := hq
  have hew : ewArg (reg st3.data .rdi) (reg st3.data .rsi) = lam :=
    (congrArg₂ ewArg hdi3 hsi3).trans rfl
  rw [hew, hdx3, hcx3] at hpow
  rw [hdx3, hcx3] at hch4
  have hch4' : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 4448) (16 * qs.size) q ∨
        NativeRustcVm.InRange (stackBelow st3.data powersStack) powersStack q) := hch4
  obtain ⟨hK4, hkeep4⟩ := c.K_call hK3 hle3 hsv4 hrsp4 (lo := 4448) (n := 16 * qs.size)
    (by omega) (by omega) (fun q hq ↦ Or.inr (Or.inl hq)) hch4'
  have hz4 : KeepZ m0 st3.data.dmem st4.data.dmem :=
    keepZ_call (o := 64) hkeep4 (by omega) (by unfold Gap; omega)
  have hRK4 := hRK3.saved hsv4.1
  have hts4 := c.ts_call (o := 64) (by omega) hK3.fr hle3 hsv4
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch4' hts3
  have hqb4 := c.qbuf_call (o := 64) (by omega) hK3.fr hle3 hch4' (lo := 4448)
    (n := 16 * qs.size) (by omega) (fun q hq ↦ Or.inr (Or.inl hq)) hqb3
  have h4440' := bytes_call hkeep4 (j := 4440) (by omega)
    (by simp [NativeRustcVm.length_wordBytes]) (Or.inl (by simp [NativeRustcVm.length_wordBytes]))
    h4440
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b20Offset) := hpc4
  -- `b20`: the queries' address stored, `query_openings(sp + 760, t, index, queries, n)`
  refine blk_stepZ c b20_in_code (by simp [b20]) hp exit_b20 ok_b20.1 ok_b20.2.1 (by decide)
    (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl <;> omega) hK4 hpc4'
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b21Offset)).toBitVec) (fun _ _ ↦ rfl) fun st5 hm5 hpc5 hK5 hs5 hz5 ↦ ?_
  obtain ⟨hmid5, hW5, hw120, hrdi5, hrsi5, hrdx5, hrcx5, hr85, hkr5⟩ := ok_b20
  let env5 := argEnv m0 st4.data 8176 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b21Offset)).toBitVec
  have e5 : ∀ {r : Reg64} {v : Sym}, (after b20 retS).reg r = some v →
      reg st5.data r = v.eval env5 := fun h ↦ hm5.regs _ _ h
  have hRK5 := hRK4.six fun r hr ↦ e5 (hkr5 r hr)
  have ho5 : reg st5.data .rdi = loc m0 760 := (e5 hrdi5).trans (eval_ptr0A 760)
  have ht5 : reg st5.data .rsi = tA m0 := (e5 hrsi5).trans hRK4.r14
  have hi5 : reg st5.data .rdx = reg m0 .rsi := (e5 hrdx5).trans hRK4.rbx
  have hq5 : reg st5.data .rcx = pA m0 + BitVec.ofNat 64 61360 := (e5 hrcx5).trans hRK4.r13
  have hn5 : (reg st5.data .r8).toNat = qs.size := by
    rw [e5 hr85]
    show (reg st4.data .rbp).toNat = _
    rw [hRK4.rbp, BitVec.toNat_ofNat]
    omega
  have h120 : NativeRustcVm.WordAt st5.data.dmem (loc m0 120)
      (.ofBitVec (pA m0 + BitVec.ofNat 64 61360)) :=
    wordAt_written hm5 (r := 0) (o := 120) rfl (by omega) hw120 hRK4.r13
  have hblk5 : ∀ {jj : Nat} {bs : List UInt8}, jj + bs.length ≤ 8192 →
      (∀ p ∈ [((64 : Nat), (72 : Nat)), (120, 128)], p.2 ≤ jj ∨ jj + bs.length ≤ p.1) →
      NativeRustcVm.BytesAt st4.data.dmem (loc m0 jj) bs →
      NativeRustcVm.BytesAt st5.data.dmem (loc m0 jj) bs :=
    fun h1 h2 h3 ↦ Ctx.bytes_blk (c.wf0 hK4.fr.frame.kept) hm5 (writesIn_of_mid hmid5) hW5 h1 h2 h3
  have hpwL : ((powers lam qs.size).toList.flatMap NativeRustcVm.ewBytes).length =
      16 * qs.size := by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']
  have hpow5 := hblk5 (jj := 4448) (by rw [hpwL]; omega)
    (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl <;> omega) hpow
  have h4440'' := hblk5 (jj := 4440) (by simp [NativeRustcVm.length_wordBytes])
    (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl <;> simp) h4440'
  have hts5 := c.ts_frame (hi := 8128) (by omega) (hm5.kept (c.wf0 hK4.fr.frame.kept)) hs5 hts4
  have hqb5 := c.qbuf_frame (hi := 8128) (by omega) hs5 hqb4
  have hat5 := c.at_call (o := 64) (by omega) hK5.fr
  have hle5 : 8176 - 64 + queryOpeningsStack ≤ nextLevelStack := by decide
  have hwt5 := c.whirT hat5 hK5.fr.same hle5
  have hpos := c.whirOut hat5 hle5 (WL.whirOut_sub c.pout (o := 61360) (k := 8 * qs.size)
    (by unfold whirBytes; omega))
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hpre5 : QueryOpeningsPre a s8 qs st5.data := by
    simp only [QueryOpeningsPre, ho5, ht5, hq5, hn5]
    refine ⟨hwt5.1, hwt5.2.1, hts5, hwt5.2.2.2.1, trivial, ?_, hpos.1.2.1, hpos.1.2.2.2.2.1,
      hpos.1.2.2.2.1, c.outLoc (o := 64) (by omega) hK5.fr hle5 (by omega) (by omega), ?_, ?_⟩
    · rw [← e8]; exact hqb5.2.2
    · refine (show NativeRustcVm.Apart (loc m0 760) 32 (pA m0 + BitVec.ofNat 64 61360)
        (8 * qs.size) from ?_)
      unfold NativeRustcVm.Apart
      rw [c.loc_toNat (by omega), NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
      have := g.pS; have := g.hN
      omega
    · apply c.got_call hK5.fr (by omega) hle5 (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ (pA m0 + BitVec.ofNat 64 61360).toNat
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
        · change (pA m0 + BitVec.ofNat 64 61360).toNat + _ ≤ (pA m0).toNat + 63200
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_rc
  refine call_then hpc5 (hqo a s8 qs) hpre5 fun st6 hpc6 hrsp6 hq ↦ ?_
  obtain ⟨hrw, hnext, hch6, hsv6⟩ := hq
  rw [ho5, hi5] at hrw
  rw [ht5, hi5] at hnext
  rw [ho5, ht5] at hch6
  have hch6' : NativeRustcVm.SameOutside st5.data.dmem st6.data.dmem (fun q ↦
      (NativeRustcVm.InRange (loc m0 760) 32 q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st5.data queryOpeningsStack) queryOpeningsStack q) :=
    NativeRustcVm.SameOutside.mono hch6 fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
  obtain ⟨hK6, hkeep6⟩ := c.K_call hK5 hle5 hsv6 hrsp6 (lo := 760) (n := 32) (by omega)
    (by omega) (fun q hq ↦ hq.elim (fun h ↦ Or.inr (Or.inl h)) Or.inl) hch6'
  have hz6 : KeepZ m0 st5.data.dmem st6.data.dmem :=
    keepZ_call (o := 64) hkeep6 (by omega) (by decide)
  have hRK6 := hRK5.saved hsv6.1
  have hqb6 := c.qbuf_call (o := 64) (by omega) hK5.fr hle5 hch6' (lo := 760) (n := 32)
    (by omega) (fun q hq ↦ hq.elim (fun h ↦ Or.inr (Or.inl h)) Or.inl) hqb5
  have hkb6 : ∀ {jj : Nat} {bs : List UInt8}, 72 ≤ jj → jj + bs.length ≤ 8192 →
      (jj + bs.length ≤ 760 ∨ 792 ≤ jj) →
      NativeRustcVm.BytesAt st5.data.dmem (loc m0 jj) bs →
      NativeRustcVm.BytesAt st6.data.dmem (loc m0 jj) bs :=
    fun h1 h2 h3 h4 ↦ bytes_call hkeep6 h1 h2 h3 h4
  have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b21Offset) := hpc6
  -- `b21`: the openings' tag
  refine Eventually.bind (cond_spec hp c b21_in_code (by simp [b21]) exit_b21 ok_b21 hK6 hpc6')
    fun st7 ⟨hr7, hd7, hpc7⟩ ↦ ?_
  have hK7 := hK6.congr hr7 hd7
  have hrun9 : runN level w rounds m0 s = ((queryOpenings (reg m0 .rsi).toNat qs).run s8).bind
      fun p9 ↦ some (glueLevel w lam (reg m0 .r9).toNat ood v qs (powers lam qs.size)
        (batchedOf (reg m0 .rsi).toNat (reg m0 .r9).toNat rounds xs qs p9.1
          (powers lam qs.size)), p9.2) := by
    rw [hrun]; rfl
  rcases hr : (queryOpenings (reg m0 .rsi).toNat qs).run s8 with _ | ⟨rows, s9⟩
  · rw [hr] at hrw
    have h0 : NativeRustcVm.WordAt st6.data.dmem (loc m0 760) 0 := hrw
    rw [cRows_eval _ (load_ofMachine (r := 0) (o := 760) rfl h0)] at hpc7
    exact Eventually.mono (none13 hp c hK7.fr (hpc7.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_13_at))
      (by rw [hrun9, hr]; rfl)) fun _ h ↦ Or.inl h
  rw [hr] at hrw
  have hrows : RowsAt st6.data.dmem (loc m0 760)
      (off (a.word (phaseBase a.l s8.phase)) 24) rows := hrw
  obtain ⟨hp0, -, ww, -, hhdr, -⟩ := hrows
  have hl0 := load_ofMachine (r := 0) (o := 760) (rs := [(stackBelow m0 8176, 8176 + 8 + 8)])
    (vs := fun _ ↦ 0) (ret := 0) rfl (NativeRustcVm.wordsAt_cons_iff.mp hhdr).1
  rw [cRows_eval _ hl0] at hpc7
  have hne : ((UInt64.ofBitVec (off (a.word (phaseBase a.l s8.phase)) 24)).toBitVec ==
      BitVec.ofNat 64 0) = false := by
    rw [beq_eq_false_iff_ne]
    exact hp0
  rw [hne] at hpc7
  simp only [Bool.false_eq_true, ite_false] at hpc7
  have hpc7' : st7.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b22Offset) := hpc7
  have hlt := qo_lt hr
  have hpb : phaseBase a.l s8.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts5.decoded.phases_le))
      hts5.decoded.len
  have hpwd : phaseWords = 3 + openingsWords := rfl
  have hop := WL.whirIn_sub c.decIn (o := 8 * phaseBase a.l s8.phase + 24)
    (k := 8 * openingsWords) (by omega)
  rw [← show off (a.word (phaseBase a.l s8.phase)) 24 =
    a.words + BitVec.ofNat 64 (8 * phaseBase a.l s8.phase + 24) from off_off _ _ _] at hop
  have hk7 : ∀ r ∈ six, reg st7.data r = reg st6.data r := fun r _ ↦ hr7 r
  have hq7 : NativeRustcVm.BufWordsAt st7.data.dmem (qA m0) queryCap qs.toList := by
    rw [hd7]; exact hqb6
  have h120' : NativeRustcVm.WordAt st7.data.dmem (loc m0 120)
      (.ofBitVec (pA m0 + BitVec.ofNat 64 61360)) := by
    rw [hd7]
    exact hkb6 (by omega) (by simp [NativeRustcVm.length_wordBytes])
      (Or.inl (by simp [NativeRustcVm.length_wordBytes])) h120
  have h4440''' : NativeRustcVm.WordAt st7.data.dmem (loc m0 4440) qs.size.toUInt64 := by
    rw [hd7]
    exact hkb6 (by omega) (by simp [NativeRustcVm.length_wordBytes]) (Or.inr (by omega)) h4440''
  have hpow7 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 4448) (powers lam qs.size).toList := by
    rw [hd7]
    exact hkb6 (by omega) (by rw [hpwL]; omega) (Or.inr (by omega)) hpow5
  have hrw7 : RowsAt st7.data.dmem (loc m0 760) (off (a.word (phaseBase a.l s8.phase)) 24) rows := by
    rw [hd7]; exact hrw
  have hts7 : TStateAt st7.data.dmem (tA m0) a s9 := by
    rw [hd7]; exact hnext _ _ hr
  have hff7 : FF m0 xs ood v lam st7.data.dmem :=
    hff2.keep (hz3.trans (hz4.trans (hz5.trans (hz6.trans (KeepZ.of_eq hd7))))) hxs hos
  exact .done _ (Or.inr ⟨hpc7', rows, _, s9, by rw [hrun9, hr]; rfl,
    ⟨hK7, hRK6.six hk7, hff7, hH.size, hH.osize, hqn, hq7, h120', h4440''', hpow7, hrw7, hop,
      hts7, by
        have hopenings : 0 < openingsWords := by decide
        rw [show off (a.word (phaseBase a.l s8.phase)) 24 =
          a.words + BitVec.ofNat 64 (8 * phaseBase a.l s8.phase + 24) from off_off _ _ _,
          NativeRustcVm.toNat_add_ofNat (by have := g.aW; omega)]
        constructor <;> omega⟩⟩)

end

end NativeRustcVmX64.Whir.Levels.NL
