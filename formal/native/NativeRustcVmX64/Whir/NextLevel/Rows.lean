module

public import NativeRustcVmX64.Whir.NextLevel.Ops
public import NativeRustcVmX64.Whir.NextLevel.Exec2
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names

/-!
# `next_level`: the rows batched (x86-64)

From `b22` (`H22`): the rows' header copied to `144`, the closure at `760` (`&μ`, the high part,
`&batched` at `104`, zeroed, the query weights), the rounds' count and the closure's address
pushed, `each_row(index, queries, &rows, μ, rounds, &closure)` (`b22`), its `bool` tested (`b23`):
`rows`, to `b24` with `H24`.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel
open NativeRustcVm.Sumcheck (RowsAt openingsWords)

@[expose] public section

/-- At `b24`: the batched value `bt` at `104`, the queries' address (RBX), the query weights'
address (R13) and count (RBP, R14). -/
structure H24 [Labels] (a : DecArea) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (xs ood : Array EW) (v lam : EW)
    (qs : Array UInt64) (bt : EW) (s9 : TState) (d : MachineData) : Prop where
  K : K level w rounds m0 72 d
  rbx : reg d .rbx = pA m0 + BitVec.ofNat 64 61360
  rbp : reg d .rbp = BitVec.ofNat 64 qs.size
  r13 : reg d .r13 = loc m0 4448
  r14 : reg d .r14 = BitVec.ofNat 64 qs.size
  ff : FF m0 xs ood v lam d.dmem
  size : xs.size = level.fold
  osize : ood.size = (reg m0 .r9).toNat
  qsz : qs.size ≤ queryCap
  qbuf : NativeRustcVm.BufWordsAt d.dmem (qA m0) queryCap qs.toList
  pw : NativeRustcVm.EWsAt d.dmem (loc m0 4448) (powers lam qs.size).toList
  bt : NativeRustcVm.EWAt d.dmem (loc m0 104) bt
  ts : TStateAt d.dmem (tA m0) a s9

end

public section

theorem roundsOf_succ (d : Mem 64) (p : BitVec 64) (n : Nat) :
    roundsOf d p (n + 1) =
      ⟨NativeRustcVm.ewOf d p, NativeRustcVm.ewOf d (p + BitVec.ofNat 64 16)⟩ ::
      roundsOf d (p + BitVec.ofNat 64 32) n := by
  unfold roundsOf
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ ↦ ?_⟩
  simp only [Function.comp, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 4 <;> omega

/-- The rounds read back. -/
theorem roundsOf_of_roundsAt {d : Mem 64} {p : BitVec 64} {rs : List FoldRoundW}
    (h : RoundsAt d p rs) : roundsOf d p rs.length = rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih =>
    unfold RoundsAt at h
    rw [show roundEWs (r :: rs) = r.alpha :: r.beta :: roundEWs rs from rfl, ewsAt_cons,
      ewsAt_cons, off_off] at h
    obtain ⟨ha, hb, hr⟩ := h
    rw [List.length_cons, roundsOf_succ, NativeRustcVm.ewOf_of_ewAt ha,
      show p + BitVec.ofNat 64 16 = off p 16 from rfl, NativeRustcVm.ewOf_of_ewAt hb,
      show p + BitVec.ofNat 64 32 = off p (16 + 16) from rfl, ih hr]

section
open LeanVM.Protocol.Compile

/-- **The rows moved**: their header copied to `r'`, their openings kept. -/
theorem rowsAt_move {d d' : Mem 64} {r r' p : BitVec 64} {rows : Array (Array UInt64)}
    (h : RowsAt d r p rows)
    (hh : ∀ w0 w1 w2 w3 : UInt64, NativeRustcVm.WordsAt d r [w0, w1, w2, w3] →
      NativeRustcVm.WordsAt d' r' [w0, w1, w2, w3])
    (ho : NativeRustcVm.Layout.Same d d' p (8 * openingsWords)) : RowsAt d' r' p rows := by
  obtain ⟨hp0, hsz, w, hw, hhdr, hrow⟩ := h
  refine ⟨hp0, hsz, w, hw, hh _ _ _ _ hhdr,
    fun j hj ↦ ⟨(hrow j hj).1, bytesAt_congr (hrow j hj).2 fun i hi ↦ ?_⟩⟩
  rw [off, NativeRustcVm.addr_add_add]
  refine ho _ ?_
  rw [NativeRustcVm.length_wordsBytes, Array.length_toList, (hrow j hj).1] at hi
  have e1 : wireMaxQueries = 256 := rfl
  have e2 : wireMaxLeafWords = 64 := rfl
  have e3 : NativeVm.openingWords = 193 := rfl
  have e4 : openingsWords = 49408 := rfl
  simp only [e1, e2, e3, e4] at hsz hw hj hi ⊢
  omega

end

theorem loc_add (m0 : MachineData) (o i : Nat) :
    loc m0 o + BitVec.ofNat 64 i = loc m0 (o + i) :=
  off_add _ _ _

/-- A stack argument from a frame's word. -/
theorem stackArg_loc {m0 d : MachineData} {o : Nat} (hsp : rspOf d = loc m0 o) (i : Nat)
    {u : UInt64} (hw : NativeRustcVm.WordAt d.dmem (loc m0 (o + (8 + 8 * i))) u) :
    stackArg d i = u.toBitVec := by
  show (NativeRustcVm.wordOf d.dmem (rspOf d + BitVec.ofNat 64 (8 + 8 * i))).toBitVec = _
  rw [hsp, off_add, NativeRustcVm.wordOf_of_wordAt hw]

/-- The closure's word `i`. -/
theorem nextEnv_loc {m0 d : MachineData} (h1 : stackArg d 1 = loc m0 760) (i : Nat) {u : UInt64}
    (hw : NativeRustcVm.WordAt d.dmem (loc m0 (760 + 8 * i)) u) : nextEnv d i = u.toBitVec := by
  unfold nextEnv
  rw [h1, off_add, NativeRustcVm.wordOf_of_wordAt hw]

theorem vRc_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 61152 8 = BitVec.ofNat 64 n)
    (hn : n < 7) : vRc.eval env = BitVec.ofNat 64 n := by
  simp only [vRc, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]

theorem vRp_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 61152 8 = BitVec.ofNat 64 n)
    (hn : n < 7) {p : BitVec 64} (hl : env.load 0 8184 8 = p) :
    vRp.eval env = p + BitVec.ofNat 64 61160 := by
  simp only [vRp, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h, hl,
    ult_ofNat hn (by decide), Bool.not_true, Bool.false_eq_true, ite_false]

theorem vWp_eval [Labels] (env : Env) {n : Nat} (h : env.load 0 4440 8 = BitVec.ofNat 64 n)
    (hn : n < 231) : vWp.eval env = (Sym.ptr 0 4448).eval env := by
  simp only [vWp, SBool.eval, CmpOp.apply, low_W64, ult_ofNat hn (by decide), Bool.not_true,
    Bool.false_eq_true, ite_false, Sym.eval, h]

theorem vWn_eval [Labels] (env : Env) {n : Nat} (h : env.load 0 4440 8 = BitVec.ofNat 64 n)
    (hn : n < 231) : vWn.eval env = BitVec.ofNat 64 n := by
  simp only [vWn, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem reg_retS {r : Reg64} (h : r ≠ .rsp) : retS.reg r = some (.reg r) := by
  cases r <;> first | exact absurd rfl h | rfl

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

/-- The state `w` as an input. -/
theorem Ctx.pIn (c : Ctx a s level w rounds m0) : WhirIn m0 (pA m0) whirBytes nextLevelStack :=
  ⟨⟨c.pout.1.1, c.pout.1.2.1⟩, c.pout.1.2.2.2.2.1⟩

/-- A frame range apart from bytes of the state. -/
theorem Ctx.apart_lp (c : Ctx a s level w rounds m0) {o k j n : Nat} (hok : o + k ≤ 8192)
    (hk : 0 < k) (hj : j + n ≤ 63200) (hj' : j < 63200) :
    NativeRustcVm.Apart (loc m0 o) k (pA m0 + BitVec.ofNat 64 j) n := by
  have g := c.geo
  unfold NativeRustcVm.Apart
  rw [c.loc_toNat (by omega), NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
  have := g.pS; have := g.hN
  omega

/-- A frame range apart from what is apart from the entry's stack. -/
theorem Ctx.apart_lx (c : Ctx a s level w rounds m0) {x : BitVec 64} {n o k : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 nextLevelStack) (nextLevelStack + 8))
    (hok : o + k ≤ 8184) (hk : 0 < k) : NativeRustcVm.Apart (loc m0 o) k x n := by
  have g := c.geo
  unfold NativeRustcVm.Apart at hx ⊢
  rw [c.stk_toNat, stack_eq] at hx
  rw [c.loc_toNat (by omega)]
  have := g.hN
  omega

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The rows batched**: `b22`, `each_row`, `b23`, to `b24` with `H24`. -/
theorem rows (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (her : ∀ rows op, Spec (Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.entryLabel) (EachRowNextPre rows op)
      (EachRowNextPost rows))
    {xs ood : Array EW} {v lam : EW} {qs : Array UInt64} {rws : Array (Array UInt64)}
    {op : BitVec 64} {s9 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b22Offset))
    (hH : H22 a level w rounds m0 xs ood v lam qs rws op s9 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s level w rounds m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b24Offset) ∧
        H24 a level w rounds m0 xs ood v lam qs (batchedOf (reg m0 .rsi).toNat (reg m0 .r9).toNat
          rounds xs qs rws (powers lam qs.size)) s9 st'.data)) st := by
  have g := c.geo
  have hK := hH.K
  have hxs : xs.size ≤ 6 := by rw [hH.size]; exact c.fold
  have hos : ood.size ≤ 30 := by rw [hH.osize]; exact c.mu
  have hqn : qs.size ≤ 230 := hH.qsz
  have hmu := c.mu
  have hqa := c.qA_toNat
  have hbr := hK.wa.2
  have hrl : rounds.size ≤ 6 := by have := hbr.1; rwa [Array.length_toList] at this
  -- `b22`
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b23Offset)).toBitVec
  have hwf : (argEnv m0 st.data 8176 8 [(pA m0, 63200)] (fun _ ↦ 0) ret).WF :=
    c.wf1 hK.fr.frame.kept (show NativeRustcVm.Mapped st.data.dmem (pA m0) 63200 from
      Mapped.keeps c.pout.1.1 hK.fr.frame.kept) g.pW
      (g.pS.imp_left fun h ↦ Nat.le_trans h (Nat.sub_le_sub_left (by decide) _))
  have h8184 : (argEnv m0 st.data 8176 8 [(pA m0, 63200)] (fun _ ↦ 0) ret).load 0 8184 8 =
      pA m0 := load_ofMachine (r := 0) (o := 8184) rfl (c.arg_keep hK.fr.same)
  have hm : Match (argEnv m0 st.data 8176 8 [(pA m0, 63200)] (fun _ ↦ 0) ret) rowsS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hK.fr.frame, trivial⟩ trivial trivial
      ⟨h8184.trans (eval_ptr rfl).symm, trivial⟩
  refine exec_at (infix_of b22_in_code (by simp [b22]) hp) exit_b22 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, h56, h64, h760, h768, h776, h784, h792, h800, h104, h112, h144, h152, h160,
    h168, hrdi1, hrsi1, hrdx1, hrcx1, hr81, hr91, hrbx1, hr131, hr141, hkr1⟩ := ok_b22
  let env := argEnv m0 st.data 8176 8 [(pA m0, 63200)] (fun _ ↦ 0) ret
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b22 rowsS).reg r = some v →
      reg st1.data r = v.eval env := fun h ↦ hm1.regs _ _ h
  obtain ⟨hf1, hs1⟩ := c.blk hK.fr hwf hm1 hmid1 (hi := 808) (by omega)
    (fun w hw ↦ ⟨(hW1 w hw).1, by
      obtain ⟨-, p, hp, -, h2⟩ := hW1 w hw
      simp at hp; rcases hp with rfl | rfl | rfl | rfl <;> exact h2.trans (by decide)⟩)
  have hK1 : K level w rounds m0 48 st1.data :=
    c.K_frame hK hf1 (by omega) hs1 (Ctx.bytes_blk hwf hm1 (writesIn_of_mid hmid1) hW1
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) hK.w80)
  have hz1 : KeepZ m0 st.data.dmem st1.data.dmem :=
    keepZ_blk hwf hm1 (writesIn_of_mid hmid1) hW1 (by decide)
  have hsp1 : rspOf st1.data = loc m0 48 := hf1.frame.sp
  -- the loads
  have hl4440 : env.load 0 4440 8 = BitVec.ofNat 64 qs.size :=
    load_ofMachine (r := 0) (o := 4440) rfl hH.w4440
  have hl61152 : env.load 1 61152 8 = BitVec.ofNat 64 rounds.size := by
    have := load_ofMachine (r := 1) (o := 61152) (rs := [(stackBelow m0 8176, 8176 + 8 + 8),
      (pA m0, 63200)]) (vs := fun _ ↦ 0) (ret := ret) (m := st.data) rfl hbr.2.1
    rw [this, Array.length_toList]
    rfl
  -- the registers
  have hdi1 : reg st1.data .rdi = reg m0 .rsi := (e1 hrdi1).trans hH.rk.rbx
  have hsi1 : reg st1.data .rsi = pA m0 + BitVec.ofNat 64 61360 :=
    (e1 hrsi1).trans (load_ofMachine (r := 0) (o := 120) rfl hH.w120)
  have hdx1 : reg st1.data .rdx = BitVec.ofNat 64 qs.size := (e1 hrdx1).trans hH.rk.rbp
  have hcx1 : reg st1.data .rcx = loc m0 144 := (e1 hrcx1).trans (eval_ptr0A 144)
  have h81 : reg st1.data .r8 = reg m0 .r9 := (e1 hr81).trans hH.rk.r12
  have h91 : reg st1.data .r9 = pA m0 + BitVec.ofNat 64 61160 :=
    (e1 hr91).trans (vRp_eval env hl61152 (by omega) h8184)
  have hbx1 : reg st1.data .rbx = pA m0 + BitVec.ofNat 64 61360 :=
    (e1 hrbx1).trans (load_ofMachine (r := 0) (o := 120) rfl hH.w120)
  have h131 : reg st1.data .r13 = loc m0 4448 :=
    (e1 hr131).trans ((vWp_eval env hl4440 (by omega)).trans (eval_ptr0A 4448))
  have h141 : reg st1.data .r14 = BitVec.ofNat 64 qs.size :=
    (e1 hr141).trans (vWn_eval env hl4440 (by omega))
  have hbp1 : reg st1.data .rbp = BitVec.ofNat 64 qs.size :=
    (e1 (hkr1 .rbp (by simp))).trans hH.rk.rbp
  have hdxn : (reg st1.data .rdx).toNat = qs.size := by
    rw [hdx1, BitVec.toNat_ofNat]; omega
  -- the words the block wrote
  have w56 : NativeRustcVm.WordAt st1.data.dmem (loc m0 56) rounds.size.toUInt64 :=
    wordAt_written hm1 (r := 0) (o := 56) rfl (by omega) h56 (vRc_eval env hl61152 (by omega))
  have w64 : NativeRustcVm.WordAt st1.data.dmem (loc m0 64) (.ofBitVec (loc m0 760)) :=
    wordAt_written hm1 (r := 0) (o := 64) rfl (by omega) h64 (eval_ptr0A 760)
  have w760 : NativeRustcVm.WordAt st1.data.dmem (loc m0 760) (.ofBitVec (loc m0 80)) :=
    wordAt_written hm1 (r := 0) (o := 760) rfl (by omega) h760 (eval_ptr0A 80)
  have w768 : NativeRustcVm.WordAt st1.data.dmem (loc m0 768) (.ofBitVec (loc m0 176)) :=
    wordAt_written hm1 (r := 0) (o := 768) rfl (by omega) h768 (eval_ptr0A 176)
  have w776 : NativeRustcVm.WordAt st1.data.dmem (loc m0 776) (.ofBitVec (reg st.data .r15)) :=
    wordAt_written hm1 (r := 0) (o := 776) rfl (by omega) h776 rfl
  have w784 : NativeRustcVm.WordAt st1.data.dmem (loc m0 784) (.ofBitVec (loc m0 104)) :=
    wordAt_written hm1 (r := 0) (o := 784) rfl (by omega) h784 (eval_ptr0A 104)
  have w792 : NativeRustcVm.WordAt st1.data.dmem (loc m0 792) (.ofBitVec (loc m0 4448)) :=
    wordAt_written hm1 (r := 0) (o := 792) rfl (by omega) h792
      ((vWp_eval env hl4440 (by omega)).trans (eval_ptr0A 4448))
  have w800 : NativeRustcVm.WordAt st1.data.dmem (loc m0 800) qs.size.toUInt64 :=
    wordAt_written hm1 (r := 0) (o := 800) rfl (by omega) h800 (vWn_eval env hl4440 (by omega))
  have w104 : NativeRustcVm.WordAt st1.data.dmem (loc m0 104) 0 :=
    wordAt_written hm1 (r := 0) (o := 104) rfl (by omega) h104 rfl
  have w112 : NativeRustcVm.WordAt st1.data.dmem (loc m0 112) 0 :=
    wordAt_written hm1 (r := 0) (o := 112) rfl (by omega) h112 rfl
  -- the stack arguments and the closure
  have a0 : stackArg st1.data 0 = BitVec.ofNat 64 rounds.size := stackArg_loc hsp1 0 w56
  have a1 : stackArg st1.data 1 = loc m0 760 := stackArg_loc hsp1 1 w64
  have n0 : nextEnv st1.data 0 = loc m0 80 := nextEnv_loc a1 0 w760
  have n1 : nextEnv st1.data 1 = loc m0 176 := nextEnv_loc a1 1 w768
  have n2 : (nextEnv st1.data 2).toNat = level.fold := by
    rw [nextEnv_loc a1 2 w776]; exact hH.rk.r15
  have n3 : nextEnv st1.data 3 = loc m0 104 := nextEnv_loc a1 3 w784
  have n4 : nextEnv st1.data 4 = loc m0 4448 := nextEnv_loc a1 4 w792
  have n5 : nextEnv st1.data 5 = BitVec.ofNat 64 qs.size := nextEnv_loc a1 5 w800
  have n5n : (nextEnv st1.data 5).toNat = qs.size := by rw [n5, BitVec.toNat_ofNat]; omega
  have a0n : (stackArg st1.data 0).toNat = rounds.size := by rw [a0, BitVec.toNat_ofNat]; omega
  -- the rows moved to `144`
  have hcopy : ∀ w0 w1 w2 w3 : UInt64,
      NativeRustcVm.WordsAt st.data.dmem (loc m0 760) [w0, w1, w2, w3] →
      NativeRustcVm.WordsAt st1.data.dmem (loc m0 144) [w0, w1, w2, w3] := by
    intro w0 w1 w2 w3 hw
    obtain ⟨h0, hw⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    obtain ⟨h1, hw⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    obtain ⟨h2, hw⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    obtain ⟨h3, -⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    simp only [loc_add] at h1 h2 h3
    have v0 := wordAt_written hm1 (r := 0) (o := 144) rfl (by omega) h144
      (load_ofMachine (r := 0) (o := 760) rfl h0)
    have v1 := wordAt_written hm1 (r := 0) (o := 152) rfl (by omega) h152
      (load_ofMachine (r := 0) (o := 768) rfl h1)
    have v2 := wordAt_written hm1 (r := 0) (o := 160) rfl (by omega) h160
      (load_ofMachine (r := 0) (o := 776) rfl h2)
    have v3 := wordAt_written hm1 (r := 0) (o := 168) rfl (by omega) h168
      (load_ofMachine (r := 0) (o := 784) rfl h3)
    refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨v0, ?_⟩
    rw [loc_add]
    refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨v1, ?_⟩
    rw [loc_add]
    refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨v2, ?_⟩
    rw [loc_add]
    exact NativeRustcVm.wordsAt_cons_iff.mpr ⟨v3, NativeRustcVm.wordsAt_nil _ _⟩
  have hopn := hH.opIn
  have hsop : NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem op (8 * openingsWords) := by
    refine NativeRustcVm.Layout.Same.of_sameOutside hs1 fun j hj hq ↦ ?_
    have hx : (op + BitVec.ofNat 64 j).toNat = op.toNat + j :=
      NativeRustcVm.toNat_add_ofNat (by
        have h := hopn.1.2
        have h' : op.toNat + 8 * openingsWords ≤ 2 ^ 64 := h
        omega)
    have h2 : op.toNat + 8 * openingsWords ≤ (stackBelow m0 nextLevelStack).toNat ∨
        (stackBelow m0 nextLevelStack).toNat + (nextLevelStack + 8) ≤ op.toNat := hopn.2
    rw [c.stk_toNat, stack_eq] at h2
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [c.fa_toNat]; have := g.hA; have := g.hN; omega),
      c.fa_toNat, hx] at hq
    have := g.hN
    omega
  have hrw1 : RowsAt st1.data.dmem (loc m0 144) op rws := rowsAt_move hH.rows hcopy hsop
  -- what the block kept
  have hff1 : FF m0 xs ood v lam st1.data.dmem := hH.ff.keep hz1 hxs hos
  have hpwL : ((powers lam qs.size).toList.flatMap NativeRustcVm.ewBytes).length =
      16 * qs.size := by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']
  have hpw1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 4448) (powers lam qs.size).toList :=
    Ctx.bytes_blk hwf hm1 (writesIn_of_mid hmid1) hW1 (by rw [hpwL]; omega)
      (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl | rfl | rfl <;> omega) hH.pw
  have hts1 := c.ts_frame (hi := 808) (by omega) (hm1.kept hwf) hs1 hH.ts
  have hqb1 := c.qbuf_frame (hi := 808) (by omega) hs1 hH.qbuf
  have hwa1 := hK1.wa
  have hqs1 : NativeRustcVm.WordsAt st1.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList := by
    have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
      show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
      rw [BitVec.add_assoc]
      rfl
    rw [← e8]; exact hqb1.2.2
  -- `each_row`
  have hat1 := c.at_call (o := 48) (by omega) hf1
  have hle : 8176 - 48 + eachRowNextStack ≤ nextLevelStack := by decide
  have hpIn := c.pIn
  have hposIn := WL.whirIn_sub hpIn (o := 61360) (k := 8 * qs.size) (by unfold whirBytes; omega)
  have hrdIn := WL.whirIn_sub hpIn (o := 61160) (k := roundBytes * rounds.size)
    (by unfold whirBytes roundBytes; omega)
  have hpre : EachRowNextPre rws op st1.data := by
    refine ⟨⟨(c.sctx (F := 8176 - 48) (by decide)).stackOk hat1 hle, ⟨fun i hi ↦ ?_, ?_⟩, ?_,
      ?_, c.whirIn hat1 hle hopn, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsp1, show loc m0 48 + 8#64 + BitVec.ofNat 64 i = loc m0 (56 + i) by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, loc_add, loc_add]]
      exact (c.region_ok hf1.frame.kept).1 _ (by omega)
    · rw [hsp1, c.loc_toNat (by omega)]; have := g.hA; omega
    · rw [hcx1]; exact hrw1
    · rw [hcx1]; exact c.inLoc (o := 48) (by omega) hf1 hle (by omega) (by omega)
    · rw [hsi1, hdxn]; exact c.whirIn hat1 hle hposIn
    · rw [h81]; exact hmu
    · rw [a0n]; exact hrl
    · rw [h91, a0n]; exact c.whirIn hat1 hle hrdIn
    · rw [a1]; exact c.inLoc (o := 48) (by omega) hf1 hle (by omega) (by omega)
    · rw [n0]; exact c.inLoc (o := 48) (by omega) hf1 hle (by omega) (by omega)
    · rw [n0, h81]; exact NativeRustcVm.wordOf_of_wordAt hK1.w80
    · rw [n2]; have := c.fold; unfold roundCap at this; unfold laneCap; omega
    · rw [n1]
      exact c.sliceLoc (o := 48) (by omega) hf1 hle (by omega)
        (by rw [n2]; have := c.fold; unfold roundCap at this; omega)
    · rw [n4]
      exact c.sliceLoc (o := 48) (by omega) hf1 hle (by omega) (by rw [n5n]; omega)
    · rw [n3]; exact c.inLoc (o := 48) (by omega) hf1 hle (by omega) (by omega)
    · rw [n3]
      exact ewAt_iff.mpr ⟨w104, by rw [off_off]; exact w112⟩
    · rw [n3, hsp1, show loc m0 48 + 8#64 = loc m0 56 by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, loc_add]]
      exact c.apart_ll (by omega) (by omega) (by omega)
    · rw [n3, a1]; exact c.apart_ll (by omega) (by omega) (by omega)
    · rw [n3, n0]; exact c.apart_ll (by omega) (by omega) (by omega)
    · rw [n3, hcx1]; exact c.apart_ll (by omega) (by omega) (by omega)
    · rw [n3]; exact c.apart_lx hopn.2 (by omega) (by omega)
    · rw [n3, hsi1, hdxn]; exact c.apart_lp (by omega) (by omega) (by omega) (by omega)
    · rw [n3, h91, a0n]; exact c.apart_lp (by omega) (by omega) (by unfold roundBytes; omega) (by omega)
    · rw [n3, n1, n2]
      exact c.apart_ll (by omega) (by omega) (by omega)
    · rw [n3, n4, n5n]
      exact c.apart_ll (by omega) (by omega) (by omega)
    · have hargs : rspOf st1.data + 8#64 = loc m0 56 := by
        rw [hsp1, show loc m0 48 + 8#64 = loc m0 56 by
          rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, loc_add]]
      rw [hcx1, hsi1, hdxn, h91, a0n, a1, n0, n1, n2, n3, n4, n5n, hargs]
      apply c.got_call hf1 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      have hfold := c.fold
      change level.fold ≤ 6 at hfold
      rcases har with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact c.got_loc (by omega) (by omega)
      · exact ⟨(a.words, 8 * a.len), by simp, hH.opBounds⟩
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ (pA m0 + BitVec.ofNat 64 61360).toNat
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
        · change (pA m0 + BitVec.ofNat 64 61360).toNat + 8 * qs.size ≤ (pA m0).toNat + 63200
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ (pA m0 + BitVec.ofNat 64 61160).toNat
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
        · change (pA m0 + BitVec.ofNat 64 61160).toNat + 32 * rounds.size ≤ (pA m0).toNat + 63200
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_loc (by omega) (by omega)
  refine call_then hpc1 (her rws op) hpre fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hok, hbt, hch2, hsv2⟩ := hq
  have hch2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 104) 16 q ∨
        NativeRustcVm.InRange (stackBelow st1.data eachRowNextStack) eachRowNextStack q) :=
    NativeRustcVm.SameOutside.mono hch2 fun q hq ↦ by
      rcases hq with hq | hq
      · left; rw [one_iff, n3] at hq; exact hq
      · exact Or.inr hq
  obtain ⟨hK2, hkeep2⟩ := c.K_callO (o := 48) (by omega) hK1 hle hsv2 hrsp2 (lo := 104) (n := 16)
    (by omega) (by omega) (fun q hq ↦ Or.inr (Or.inl hq)) hch2'
  have hz2 : KeepZ m0 st1.data.dmem st2.data.dmem :=
    keepZ_call (o := 48) hkeep2 (by omega) (by decide)
  have hts2 := c.ts_call (o := 48) (by omega) hf1 hle hsv2
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch2' hts1
  have hqb2 := c.qbuf_call (o := 48) (by omega) hf1 hle hch2' (lo := 104) (n := 16) (by omega)
    (fun q hq ↦ Or.inr (Or.inl hq)) hqb1
  have hpw2 := bytes_call hkeep2 (j := 4448) (by omega) (by rw [hpwL]; omega)
    (Or.inr (by omega)) hpw1
  -- the batched value
  have eR : (eachRowArgs st1.data).2 = rounds := by
    show (roundsOf st1.data.dmem (reg st1.data .r9) (stackArg st1.data 0).toNat).toArray = _
    have e61160 : pA m0 + BitVec.ofNat 64 61160 = off (off (pA m0) roundsOff) 8 := by
      show _ = pA m0 + BitVec.ofNat 64 61152 + BitVec.ofNat 64 8
      rw [BitVec.add_assoc]
      rfl
    rw [h91, a0n, e61160, ← Array.length_toList, roundsOf_of_roundsAt hwa1.2.2.2,
      Array.toArray_toList]
  have eQ : (eachRowArgs st1.data).1 = qs := by
    show (NativeRustcVm.wordsOf st1.data.dmem (reg st1.data .rsi) (reg st1.data .rdx).toNat).toArray
      = _
    rw [hsi1, hdxn, ← Array.length_toList, NativeRustcVm.wordsOf_of_wordsAt hqs1,
      Array.toArray_toList]
  have eX : slice st1.data (nextEnv st1.data 1) (nextEnv st1.data 2) = xs := by
    show (NativeRustcVm.ewsOf st1.data.dmem (nextEnv st1.data 1) (nextEnv st1.data 2).toNat).toArray
      = _
    have := NativeRustcVm.ewsOf_of_ewsAt hff1.fv.high
    rw [Array.length_toList, hH.size] at this
    rw [n1, n2, this, Array.toArray_toList]
  have eP : slice st1.data (nextEnv st1.data 4) (nextEnv st1.data 5) = powers lam qs.size := by
    show (NativeRustcVm.ewsOf st1.data.dmem (nextEnv st1.data 4) (nextEnv st1.data 5).toNat).toArray
      = _
    have := NativeRustcVm.ewsOf_of_ewsAt hpw1
    rw [Array.length_toList, powers_size'] at this
    rw [n4, n5n, this, Array.toArray_toList]
  rw [n3, hdi1, h81, eR, eQ, eX, eP] at hbt
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b23Offset) := hpc2
  -- `b23`: `each_row`'s `bool`
  have hwf3 := c.wf0 hK2.fr.frame.kept (ret := 0)
  have hm3 : Match (argEnv m0 st2.data 8176 8 []) s56S st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK2.fr.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b23_in_code (by simp [b23]) hp) exit_b23 hwf3 nofun hpc2' hm3
    fun st3 hm3' hpc3 ↦ ?_
  obtain ⟨hmem3, hregs3⟩ := ok_b23
  have hd3 : st3.data.dmem = st2.data.dmem := hm3'.dmem_eq hwf3 hmem3
  have hr3 : ∀ r, r ≠ .rsp → reg st3.data r = reg st2.data r := fun r hr ↦
    hm3'.regs r (.reg r) (by
      show ((after b23 s56S).regs[r.idx]?).getD none = some (.reg r)
      rw [hregs3]; exact reg_retS hr)
  have hK3 : K level w rounds m0 72 st3.data :=
    ⟨⟨Frame.of_blockA hK2.fr.frame hwf3 hm3' mid_b23 slots_le, by rw [Sm, hd3]; exact hK2.fr.same⟩,
      by rw [hd3]; exact hK2.w80, by rw [hd3]; exact hK2.lv, by rw [hd3]; exact hK2.wa⟩
  simp only [PcOk, cAl_eval] at hpc3
  have hal : ((argEnv m0 st2.data 8176 8 [] (fun _ ↦ 0) 0).regs .rax).toNat % 256 = 1 := hok
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b24Offset) := by rw [hpc3, hal]; rfl
  have hcs : ∀ r, calleeSaved r = true → reg st3.data r = reg st1.data r := fun r hr ↦
    (hr3 r (by rintro rfl; cases hr)).trans (hsv2.1 r hr)
  exact .done _ (Or.inr ⟨hpc3', hK3, (hcs .rbx rfl).trans hbx1, (hcs .rbp rfl).trans hbp1,
    (hcs .r13 rfl).trans h131, (hcs .r14 rfl).trans h141,
    by rw [hd3]; exact hff1.keep hz2 hxs hos, hH.size, hH.osize, hqn,
    by rw [hd3]; exact hqb2, by rw [hd3]; exact hpw2, by rw [hd3]; exact hbt,
    by rw [hd3]; exact hts2⟩)

end

end NativeRustcVmX64.Whir.Levels.NL
