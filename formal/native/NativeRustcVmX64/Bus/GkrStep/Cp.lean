module

public import NativeRustcVmX64.Bus.GkrStep.Tl

/-!
# `gkr_step`'s copy of the sumcheck's challenges (x86-64)

From `AtCp` (`NativeRustcVmX64.Vm.GkrStep.label_13`, `b31`): the sumcheck's challenges `xs` (at `352` of the frame) copied
after `y` in the new point, in pairs (`b36`, `b37`) and the odd last one (`b33`/`b38`, `b39`); then
`Some` (`b40`) and the exit (`cp_spec`).
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

public section

/-! ## Arithmetic -/

theorem and_odd_all : ∀ n < 64, CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) = decide (n % 2 = 0) := by
  decide +kernel

theorem and62_all : ∀ n < 64, BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 n))
    (BitVec.ofNat 64 62) = BitVec.ofNat 64 (2 * (n / 2)) := by
  decide +kernel

theorem shl4_all : ∀ n < 64, BinOp.apply .shl .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 4) =
    BitVec.ofNat 64 (16 * n) := by
  decide +kernel

theorem bv_of {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : n < 2 ^ 64) :
    x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, h])

theorem addW (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem ofInt0 : BitVec.ofInt 64 0 = 0#64 := by decide

theorem eq64' (x : BitVec 64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 v) = decide (x.toNat = v) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]

theorem addNeg (x : BitVec 64) (c : Nat) :
    x = x + BitVec.ofNat 64 c + BitVec.ofInt 64 (-(c : Int)) := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast, ← BitVec.sub_eq_add_neg, BitVec.add_sub_cancel]

theorem offE {b : BitVec 64} {o o' : Nat} (e : o = o') : off b o = off b o' := by rw [e]

theorem addr_eq (x : BitVec 64) (a b : Nat) : BitVec.ofNat 64 a + off x b = off x (b + a) := by
  simp only [off]
  rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `movb $1, %bpl`: BPL is `1`. -/
theorem bpl_one (x : BitVec 64) :
    (BinOp.apply .merge .W8 x (BitVec.ofNat 64 1)).toNat % 256 = 1 := by
  have : low .W8 (x.replaceLow (low .W8 (BitVec.ofNat 64 1))) = low .W8 (BitVec.ofNat 64 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi8 : i < 8 := hi
    simp only [low, BitVec.replaceLow, BitVec.getLsbD_setWidth]
    change (decide (i < 8) && (decide (i < 64) &&
      ((x.drop 8) ++ low .W8 (BitVec.ofNat 64 1)).getLsbD i)) = _
    rw [BitVec.getLsbD_append]
    simp [hi8, show i < 64 by omega]
  have h2 := congrArg BitVec.toNat this
  rw [toNat_low] at h2
  exact h2.trans (by decide)

/-! ## Words -/

theorem wRe {d : Mem 64} {b : BitVec 64} {w : UInt64} {o1 o2 o3 o4 : Nat}
    (h : NativeRustcVm.WordAt d (off (off b o1) o2) w) (e : o1 + o2 = o3 + o4) :
    NativeRustcVm.WordAt d (off (off b o3) o4) w := by
  rw [off_off] at h ⊢
  rw [← e]
  exact h

theorem wRe0 {d : Mem 64} {b : BitVec 64} {w : UInt64} {o1 o2 o : Nat}
    (h : NativeRustcVm.WordAt d (off (off b o1) o2) w) (e : o1 + o2 = o) :
    NativeRustcVm.WordAt d (off b o) w := by
  rw [off_off, e] at h
  exact h

theorem srcAt {d : Mem 64} {b : BitVec 64} {xs : Array EW} (h : NativeRustcVm.EWsAt d b xs.toList)
    {j : Nat} (hj : j < xs.size) :
    NativeRustcVm.WordAt d (off b (16 * j)) xs[j].c0 ∧
      NativeRustcVm.WordAt d (off b (16 * j + 8)) xs[j].c1 := by
  have e := NativeRustcVm.Transcript.ewsAt_iff.mp h j (by rwa [Array.length_toList])
  rw [NativeRustcVm.Transcript.ewAt_iff, off_off, Array.getElem_toList] at e
  exact e

/-! ## The copy's state -/

/-- **The copy's state**: the first `c` of the challenges copied after the `step` coordinates. -/
structure CpS [Labels] (a : DecArea) (m0 : MachineData) (xs : Array EW) (s' : TState)
    (d0 : MachineData) (c : Nat) (d : MachineData) : Prop where
  fr : FR m0 40 d
  r13 : (reg d .r13).toNat = xs.size
  fk : FK m0 d0 d
  pk : PK m0 d0 d (56 + 16 * (reg m0 .rsi).toNat)
  ts : TStateAt d.dmem (reg m0 .rdi) a s'
  cp : ∀ j (hj : j < xs.size), j < c →
    NativeRustcVm.EWAt d.dmem (off (reg m0 .rcx) (56 + 16 * (reg m0 .rsi).toNat + 16 * j)) xs[j]

/-- **The pairs' loop's state** after `i` rounds. -/
structure LInv [Labels] (a : DecArea) (m0 : MachineData) (xs : Array EW) (s' : TState)
    (d0 : MachineData) (i : Nat) (d : MachineData) : Prop where
  cs : CpS a m0 xs s' d0 (2 * i) d
  rax : reg d .rax = BitVec.ofNat 64 (2 * i)
  rdx : reg d .rdx = BitVec.ofNat 64 (56 + 32 * i)
  rcx : reg d .rcx = BitVec.ofNat 64 (2 * (xs.size / 2))
  r14 : reg d .r14 = off (reg m0 .rcx) (16 * (reg m0 .rsi).toNat)
  rbx : reg d .rbx = BitVec.ofNat 64 (16 * (reg m0 .rsi).toNat)

end

public section

variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}
  {xs : Array EW} {s' : TState} {d0 : MachineData}

theorem CpS.eq {c : Nat} {d d' : MachineData} (cs : CpS a m0 xs s' d0 c d) (fr : FR m0 40 d')
    (hd : d'.dmem = d.dmem) (h13 : reg d' .r13 = reg d .r13) : CpS a m0 xs s' d0 c d' :=
  ⟨fr, by rw [h13]; exact cs.r13, ⟨fun h1 h2 hb ↦ by rw [hd]; exact cs.fk.keep h1 h2 hb⟩,
    ⟨fun h1 hb ↦ by rw [hd]; exact cs.pk.keep h1 hb⟩, by rw [hd]; exact cs.ts,
    fun j hj hc ↦ by rw [hd]; exact cs.cp j hj hc⟩

theorem nums (h : GkrStepPre a s0 g0 m0) :
    (reg m0 .rcx).toNat + 1064 ≤ 2 ^ 64 ∧ (fb m0).toNat + 1416 ≤ 2 ^ 64 ∧
      ((reg m0 .rcx).toNat + 1064 ≤ (fb m0).toNat ∨
        (fb m0).toNat + 1416 ≤ (reg m0 .rcx).toNat) := by
  have cx := ctxF h 1408 N_ge
  have ha := apart_frame (pre_gk h).2.2.2.2.1 cx.spN N_ge
  have hw := cx.noWrap_frame
  have hgb : gkrStateBytes = 1064 := rfl
  unfold NativeRustcVm.Apart at ha
  unfold NativeRustcVm.NoWrap at hw
  rw [hgb] at ha
  exact ⟨(pre_gk h).2.1, hw, ha⟩

/-- **Memory changed in `n` bytes of the `GkrStateW` at `lo`** keeps the frame. -/
theorem FR.localP (h : GkrStepPre a s0 g0 m0) {o : Nat} {d d' : MachineData} (fr : FR m0 o d)
    (hrsp : rspOf d' = rspOf d) (hcs : ∀ r, calleeSaved r = true → reg d' r = reg d r)
    (hk : Kept d.dmem d'.dmem) {lo n : Nat} (hle : lo + n ≤ 1064)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (NativeRustcVm.InRange (off (reg m0 .rcx) lo) n)) :
    FR m0 o d' := by
  have hnot : ∀ j, j < 1416 →
      ¬ NativeRustcVm.InRange (off (reg m0 .rcx) lo) n (off (fb m0) j) :=
    fun j hj hq ↦ fb_not_outs h hj (Or.inr (pSub h hle hq))
  refine ⟨⟨hrsp.trans fr.frame.sp, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans fr.frame.kept hk,
    fun r hr hsl ↦ (hcs r hr).trans (fr.frame.regs r hr hsl)⟩,
    NativeRustcVm.SameOutside.mono (fr.same.trans hs) fun q hq ↦ hq.elim id
      fun hq ↦ Or.inr (Or.inr (pSub h hle hq))⟩
  · refine bytesAt_congr (fr.frame.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    have := slots_hi p hp
    rw [off_add]
    exact hs _ (hnot _ (by omega))
  · rw [hs _ (hnot _ (by omega))]
    exact fr.frame.ret j hj

theorem fkP (h : GkrStepPre a s0 g0 m0) {d d' : MachineData} {lo n : Nat} (hle : lo + n ≤ 1064)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (NativeRustcVm.InRange (off (reg m0 .rcx) lo) n)) : FK m0 d d' :=
  ⟨fun {o} {_} _ hob hb ↦ NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ by
    rw [off_add] at hq
    exact fb_not_outs h (by omega) (Or.inr (pSub h hle hq))⟩

theorem pkP (h : GkrStepPre a s0 g0 m0) {d d' : MachineData} {lo n : Nat} (hle : lo + n ≤ 1064)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (NativeRustcVm.InRange (off (reg m0 .rcx) lo) n)) {B : Nat} (hB : B ≤ lo) :
    PK m0 d d' B :=
  ⟨fun hob hb ↦ pKeep h hs hle (fun q hq ↦ .inr (.inr hq)) (by omega) (.inl (by omega)) hb⟩

theorem ewKeep (h : GkrStepPre a s0 g0 m0) {d d' : Mem 64} {lo n : Nat} (hle : lo + n ≤ 1064)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off (reg m0 .rcx) lo) n))
    {o : Nat} {x : EW} (ho : o + 16 ≤ lo ∨ lo + n ≤ o) (ho' : o + 16 ≤ 1064)
    (hb : NativeRustcVm.EWAt d (off (reg m0 .rcx) o) x) :
    NativeRustcVm.EWAt d' (off (reg m0 .rcx) o) x :=
  pKeep h hs hle (fun q hq ↦ .inr (.inr hq)) (by rw [NativeRustcVm.length_ewBytes]; omega)
    (by rw [NativeRustcVm.length_ewBytes]; omega) hb

end

public section

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}
  {xs : Array EW} {s' : TState} {d0 : MachineData} {k : Nat}

/-- **The exit with `Some`** (`b40`), all the challenges copied. -/
theorem fin_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {y vs : Array EW}
    (at0 : AtCp a s0 g0 m0 xs y vs s' d0) {d : MachineData}
    (cs : CpS a m0 xs s' d0 xs.size d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b40Offset)⟩ := by
  have lE : ∀ xs : List EW, (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
    NativeRustcVm.length_ewsBytes
  have hcap := at0.size
  have hysz := at0.ysz
  unfold busPointCap at hcap
  have hwf := wf0 h cs.fr.frame.kept 0
  obtain ⟨hmid, hmem, hbp⟩ := ok_b40
  refine exec_then (infix_of b40_in_code (by simp [b40]) hp) exit_b40 hwf nofun (match_head cs.fr 0)
    fun st hm hpc ↦ ?_
  obtain ⟨fr', hd⟩ := FR.block_nil h cs.fr hwf hm hmid hmem
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_18_at)) (exit_spec hp h fr' ?_ ?_)
  · rw [at0.run, rv hm hbp]
    exact bpl_one _
  · intro g' s'' hr
    rw [at0.run] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [hd]
    refine ⟨cs.ts, at0.vsz, ?_, ?_, ?_, ?_⟩
    · have hv0 : NativeRustcVm.EWsAt d0.dmem (off (reg m0 .rcx) 0) vs.toList := by
        rw [off_zero]; exact at0.vals
      have := cs.pk.keep (by rw [lE, Array.length_toList, at0.vsz]; omega) hv0
      rwa [off_zero] at this
    · simp only [Array.toList_append, List.length_append, Array.length_toList]
      unfold busPointCap
      omega
    · simp only [Array.toList_append, List.length_append, Array.length_toList]
      exact cs.pk.keep (by rw [NativeRustcVm.length_wordBytes]; omega) at0.len
    · rw [Array.toList_append, show off (reg m0 .rcx) 48 + 8#64 = off (reg m0 .rcx) 56 from
        off_add _ 48 8, NativeRustcVm.ewsAt_append_iff]
      refine ⟨cs.pk.keep (by rw [lE, Array.length_toList]; omega) at0.ys, ?_⟩
      rw [off_add, Array.length_toList, hysz]
      refine NativeRustcVm.Transcript.ewsAt_iff.mpr fun j hj ↦ ?_
      rw [Array.length_toList] at hj
      rw [off_off, Array.getElem_toList]
      exact cs.cp j hj hj

/-- **The odd last challenge** (`b39`), then the exit. -/
theorem cp_last (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {y vs : Array EW}
    (at0 : AtCp a s0 g0 m0 xs y vs s' d0) (hn1 : 1 ≤ xs.size) {d : MachineData}
    (cs : CpS a m0 xs s' d0 (xs.size - 1) d) (hax : reg d .rax = BitVec.ofNat 64 (xs.size - 1))
    (hbx : reg d .rbx = BitVec.ofNat 64 (16 * (reg m0 .rsi).toNat)) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b39Offset)⟩ := by
  obtain ⟨hpw, hfw, hap⟩ := nums h
  have hcap := at0.size
  unfold busPointCap at hcap
  have hst := pre_step h
  have lE : ∀ xs : List EW, (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
    NativeRustcVm.length_ewsBytes
  set st := (reg m0 .rsi).toNat with hstd
  set n := xs.size with hn
  set p := reg m0 .rcx with hpd
  have hsp : reg d .rsp = off (fb m0) 40 := cs.fr.frame.sp
  have hmp := (ctxF h 1408 N_ge).mapped_frame cs.fr.frame.kept
  have hmq : NativeRustcVm.Mapped d.dmem p 1064 := Mapped.keeps (pre_gk h).1 cs.fr.frame.kept
  have pa0 : NativeRustcVm.WordAt d.dmem (off (off (fb m0) 96) 0) (UInt64.ofBitVec (off p 56)) := by
    rw [off_zero]
    exact cs.fk.keep (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega) at0.pa
  have hx := cs.fk.keep (by omega) (by rw [lE, Array.length_toList]; omega) at0.hxs
  have sx := srcAt hx (j := n - 1) (by omega)
  set R : List (BitVec 64 × Nat) := [(off (fb m0) 96, 8), (off (fb m0) (352 + 16 * (n - 1)), 16),
    (off p (56 + 16 * st + 16 * (n - 1)), 16)] with hR
  have hwf : (Env.ofMachine d R).WF := by
    refine Env.wf_of ⟨⟨mapped_off hmp (by omega), ?_⟩, ⟨mapped_off hmp (by omega), ?_⟩,
      ⟨mapped_off hmq (by omega), ?_⟩, trivial⟩ (List.pairwise_cons.mpr ⟨fun e he ↦ ?_,
        List.pairwise_pair.mpr ?_⟩)
    · show (off (fb m0) 96).toNat + 8 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega
    · show (off (fb m0) (352 + 16 * (n - 1))).toNat + 16 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega
    · show (off p (56 + 16 * st + 16 * (n - 1))).toNat + 16 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show NativeRustcVm.Apart (off (fb m0) 96) 8 (off (fb m0) (352 + 16 * (n - 1))) 16
        unfold NativeRustcVm.Apart
        rw [toNat_off (by omega), toNat_off (by omega)]; omega
      · show NativeRustcVm.Apart (off (fb m0) 96) 8 (off p (56 + 16 * st + 16 * (n - 1))) 16
        unfold NativeRustcVm.Apart
        rw [toNat_off (by omega), toNat_off (by omega)]; omega
    · show NativeRustcVm.Apart (off (fb m0) (352 + 16 * (n - 1))) 16
        (off p (56 + 16 * st + 16 * (n - 1))) 16
      unfold NativeRustcVm.Apart
      rw [toNat_off (by omega), toNat_off (by omega)]; omega
  have hld0 : (Env.ofMachine d R).load 0 0 8 = off p 56 :=
    load_ofMachine (rs := R) (r := 0) (o := 0) rfl pa0
  have hm : Match (Env.ofMachine d R) tS d := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ trivial trivial trivial ⟨?_, ?_, ?_, trivial⟩
    · show reg d .rsp = off (fb m0) 96 + BitVec.ofInt 64 (-56)
      have := addNeg (off (fb m0) 40) 56
      rw [off_add] at this
      rw [hsp]
      exact this
    · show BinOp.apply .add .W64 (reg d .rsp) (BinOp.apply .shl .W64 (reg d .rax)
        (BitVec.ofNat 64 4)) = off (fb m0) (352 + 16 * (n - 1)) + BitVec.ofInt 64 (-312)
      rw [hax, shl4_all _ (by omega), addW, hsp, off_add]
      have := addNeg (off (fb m0) (40 + 16 * (n - 1))) 312
      rw [off_add, offE (show 40 + 16 * (n - 1) + 312 = 352 + 16 * (n - 1) by omega)] at this
      exact this
    · show BinOp.apply .add .W64 (BinOp.apply .add .W64 (reg d .rbx)
        ((Env.ofMachine d R).load 0 0 8)) (BinOp.apply .shl .W64 (reg d .rax) (BitVec.ofNat 64 4)) =
          off p (56 + 16 * st + 16 * (n - 1)) + BitVec.ofInt 64 0
      rw [hbx, hld0, hax, shl4_all _ (by omega), addW, addW, ofInt0, BitVec.add_zero, addr_eq,
        off_add]
  refine exec_then (infix_of b39_in_code (by simp [b39]) hp) exit_b39 hwf nofun hm
    fun st' hm' hpc ↦ ?_
  obtain ⟨hw, w0, w8, hk⟩ := ok_b39
  have hs : NativeRustcVm.SameOutside d.dmem st'.data.dmem
      (NativeRustcVm.InRange (off p (56 + 16 * st + 16 * (n - 1))) 16) :=
    sameOutside_region hwf hm' (r := 2) rfl fun w hw' ↦ ⟨(hw w hw').1, Nat.zero_le _, (hw w hw').2⟩
  have hkr : ∀ r ∈ (.rsp :: cs6 : List Reg64), reg st'.data r = reg d r := fun r hr ↦ kr hm' hk hr
  have W0 := wordAt_eq hm' (r := 2) (sz := 16) rfl (by omega) w0 (w := xs[n - 1].c0) (by
    show (Env.ofMachine d R).load 1 0 8 = _
    exact load_ofMachine (rs := R) (r := 1) (o := 0) rfl (wRe sx.1 (by omega)))
  have W8 := wordAt_eq hm' (r := 2) (sz := 16) rfl (by omega) w8 (w := xs[n - 1].c1) (by
    show (Env.ofMachine d R).load 1 8 8 = _
    exact load_ofMachine (rs := R) (r := 1) (o := 8) rfl (wRe sx.2 (by omega)))
  have hkp : Kept d.dmem st'.data.dmem := hm'.kept hwf
  have cs' : CpS a m0 xs s' d0 n st'.data := by
    refine ⟨FR.localP h cs.fr (hkr .rsp (by simp)) (fun r hr ↦ hkr r (by
        cases r <;> simp_all [calleeSaved])) hkp (by omega) hs,
      by rw [hkr .r13 (by simp)]; exact cs.r13, cs.fk.trans (fkP h (by omega) hs),
      ⟨fun hob hb ↦ (pkP h (by omega) hs (B := 56 + 16 * st) (by omega)).keep hob
        (cs.pk.keep hob hb)⟩,
      tsKeep h hkp hs (fun q hq ↦ .inr (pSub h (by omega) hq)) cs.ts, fun j hj hjc ↦ ?_⟩
    rcases (show j < n - 1 ∨ j = n - 1 by omega) with hj' | rfl
    · exact ewKeep h (by omega) hs (.inl (by omega)) (by omega) (cs.cp j hj hj')
    · exact NativeRustcVm.Transcript.ewAt_iff.mpr ⟨wRe0 W0 (by omega), wRe W8 (by omega)⟩
  simp only [PcOk] at hpc
  exact at_pc (hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b39_next)) (fin_spec hp h at0 cs')

/-- **A round of the pairs' loop** (`b37`). -/
theorem cp_step (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {y vs : Array EW}
    (at0 : AtCp a s0 g0 m0 xs y vs s' d0) {i : Nat} (hi : 2 * i + 2 ≤ 2 * (xs.size / 2))
    {d : MachineData} (inv : LInv a m0 xs s' d0 i d) :
    Eventually (step1 Host.exe) (fun st ↦ (2 * (i + 1) = 2 * (xs.size / 2) ∧
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b38Offset) ∧ LInv a m0 xs s' d0 (i + 1) st.data) ∨
      (2 * (i + 1) < 2 * (xs.size / 2) ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b37Offset) ∧
        LInv a m0 xs s' d0 (i + 1) st.data)) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b37Offset)⟩ := by
  obtain ⟨hpw, hfw, hap⟩ := nums h
  have hcap := at0.size
  unfold busPointCap at hcap
  have hst := pre_step h
  have lE : ∀ xs : List EW, (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
    NativeRustcVm.length_ewsBytes
  set st := (reg m0 .rsi).toNat with hstd
  set n := xs.size with hn
  set p := reg m0 .rcx with hpd
  have hsp : reg d .rsp = off (fb m0) 40 := inv.cs.fr.frame.sp
  have hmp := (ctxF h 1408 N_ge).mapped_frame inv.cs.fr.frame.kept
  have hmq : NativeRustcVm.Mapped d.dmem p 1064 := Mapped.keeps (pre_gk h).1 inv.cs.fr.frame.kept
  have hx := inv.cs.fk.keep (by omega) (by rw [lE, Array.length_toList]; omega) at0.hxs
  have sa := srcAt hx (j := 2 * i) (by omega)
  have sb := srcAt hx (j := 2 * i + 1) (by omega)
  set R : List (BitVec 64 × Nat) := [(off p (56 + 16 * st + 32 * i), 32),
    (off (fb m0) (352 + 32 * i), 32)] with hR
  have hwf : (Env.ofMachine d R).WF := by
    refine Env.wf_of ⟨⟨mapped_off hmq (by omega), ?_⟩, ⟨mapped_off hmp (by omega), ?_⟩, trivial⟩
      (List.pairwise_pair.mpr ?_)
    · show (off p (56 + 16 * st + 32 * i)).toNat + 32 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega
    · show (off (fb m0) (352 + 32 * i)).toNat + 32 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega
    · show NativeRustcVm.Apart (off p (56 + 16 * st + 32 * i)) 32 (off (fb m0) (352 + 32 * i)) 32
      unfold NativeRustcVm.Apart
      rw [toNat_off (by omega), toNat_off (by omega)]; omega
  have hm : Match (Env.ofMachine d R) cS d := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial ⟨?_, ?_, trivial⟩
    · show BinOp.apply .add .W64 (reg d .r14) (reg d .rdx) =
        off p (56 + 16 * st + 32 * i) + BitVec.ofInt 64 0
      rw [addW, inv.r14, inv.rdx, off_add, ofInt0, BitVec.add_zero]
      exact offE (by omega)
    · show BinOp.apply .add .W64 (reg d .rsp) (reg d .rdx) =
        off (fb m0) (352 + 32 * i) + BitVec.ofInt 64 (-256)
      rw [addW, hsp, inv.rdx, off_add]
      have := addNeg (off (fb m0) (40 + (56 + 32 * i))) 256
      rw [off_add, offE (show 40 + (56 + 32 * i) + 256 = 352 + 32 * i by omega)] at this
      exact this
  refine exec_then (infix_of b37_in_code (by simp [b37]) hp) exit_b37 hwf nofun hm
    fun st' hm' hpc ↦ ?_
  obtain ⟨hw, w0, w8, w16, w24, hax, hdx, hk⟩ := ok_b37
  have hs : NativeRustcVm.SameOutside d.dmem st'.data.dmem
      (NativeRustcVm.InRange (off p (56 + 16 * st + 32 * i)) 32) :=
    sameOutside_region hwf hm' (r := 0) rfl fun w hw' ↦ ⟨(hw w hw').1, Nat.zero_le _, (hw w hw').2⟩
  have hkr : ∀ r ∈ (.rsp :: .rcx :: cs6 : List Reg64), reg st'.data r = reg d r :=
    fun r hr ↦ kr hm' hk hr
  have W0 := wordAt_eq hm' (r := 0) (o := 0) (sz := 32) rfl (by omega) w0 (w := xs[2 * i].c0) (by
    show (Env.ofMachine d R).load 1 0 8 = _
    exact load_ofMachine (rs := R) (r := 1) (o := 0) rfl (wRe sa.1 (by omega)))
  have W8 := wordAt_eq hm' (r := 0) (o := 8) (sz := 32) rfl (by omega) w8 (w := xs[2 * i].c1) (by
    show (Env.ofMachine d R).load 1 8 8 = _
    exact load_ofMachine (rs := R) (r := 1) (o := 8) rfl (wRe sa.2 (by omega)))
  have W16 := wordAt_eq hm' (r := 0) (o := 16) (sz := 32) rfl (by omega) w16
    (w := xs[2 * i + 1].c0) (by
    show (Env.ofMachine d R).load 1 16 8 = _
    exact load_ofMachine (rs := R) (r := 1) (o := 16) rfl (wRe sb.1 (by omega)))
  have W24 := wordAt_eq hm' (r := 0) (o := 24) (sz := 32) rfl (by omega) w24
    (w := xs[2 * i + 1].c1) (by
    show (Env.ofMachine d R).load 1 24 8 = _
    exact load_ofMachine (rs := R) (r := 1) (o := 24) rfl (wRe sb.2 (by omega)))
  have hkp : Kept d.dmem st'.data.dmem := hm'.kept hwf
  have cs' : CpS a m0 xs s' d0 (2 * (i + 1)) st'.data := by
    refine ⟨FR.localP h inv.cs.fr (hkr .rsp (by simp)) (fun r hr ↦ hkr r (by
        cases r <;> simp_all [calleeSaved])) hkp (by omega) hs,
      by rw [hkr .r13 (by simp)]; exact inv.cs.r13, inv.cs.fk.trans (fkP h (by omega) hs),
      ⟨fun hob hb ↦ (pkP h (by omega) hs (B := 56 + 16 * st) (by omega)).keep hob
        (inv.cs.pk.keep hob hb)⟩,
      tsKeep h hkp hs (fun q hq ↦ .inr (pSub h (by omega) hq)) inv.cs.ts, fun j hj hjc ↦ ?_⟩
    rcases (show j < 2 * i ∨ j = 2 * i ∨ j = 2 * i + 1 by omega) with hj' | rfl | rfl
    · exact ewKeep h (by omega) hs (.inl (by omega)) (by omega) (inv.cs.cp j hj hj')
    · exact NativeRustcVm.Transcript.ewAt_iff.mpr ⟨wRe0 W0 (by omega), wRe W8 (by omega)⟩
    · exact NativeRustcVm.Transcript.ewAt_iff.mpr ⟨wRe0 W16 (by omega), wRe W24 (by omega)⟩
  have inv' : LInv a m0 xs s' d0 (i + 1) st'.data := by
    refine ⟨cs', ?_, ?_, (hkr .rcx (by simp)).trans inv.rcx, (hkr .r14 (by simp)).trans inv.r14,
      (hkr .rbx (by simp)).trans inv.rbx⟩
    · rw [rv hm' hax]
      show BinOp.apply .add .W64 (BitVec.ofNat 64 2) (reg d .rax) = _
      rw [inv.rax]
      exact add_word _ _ (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
    · rw [rv hm' hdx]
      show BinOp.apply .add .W64 (BitVec.ofNat 64 32) (reg d .rdx) = _
      rw [inv.rdx]
      exact add_word _ _ (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
  have hc : SBool.eval (Env.ofMachine d R)
      (SBool.cmp .eq .W64 (.reg .rcx) (.bin .add .W64 (.lit 2) (.reg .rax))).not =
        !decide (2 * (n / 2) = 2 * i + 2) := by
    show (!CmpOp.apply .eq .W64 (reg d .rcx) (BinOp.apply .add .W64 (BitVec.ofNat 64 2)
      (reg d .rax))) = _
    rw [inv.rcx, inv.rax, add_word (BitVec.ofNat 64 2) (BitVec.ofNat 64 (2 * i)) (n := 2 * i + 2)
      (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega), eq64' _ _ (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [PcOk, hc] at hpc
  by_cases he : 2 * (n / 2) = 2 * i + 2
  · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    exact .done _ (.inl ⟨by omega, hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b37_next), inv'⟩)
  · simp only [he, decide_false, Bool.not_false, ↓reduceIte] at hpc
    exact .done _ (.inr ⟨by omega, hpc.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_20_at), inv'⟩)

/-- **The pairs' loop** from its first round. -/
theorem cp_loop (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {y vs : Array EW}
    (at0 : AtCp a s0 g0 m0 xs y vs s' d0) (hn2 : 2 ≤ xs.size) {d : MachineData}
    (inv : LInv a m0 xs s' d0 0 d) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b38Offset) ∧
      LInv a m0 xs s' d0 (xs.size / 2) st.data) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b37Offset)⟩ := by
  refine loop (I := fun m st ↦ ∃ i, m = xs.size / 2 - i ∧ 2 * i + 2 ≤ 2 * (xs.size / 2) ∧
    st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b37Offset) ∧ LInv a m0 xs s' d0 i st.data)
    (fun m st ⟨i, hm, hi, hpc, hinv⟩ ↦ at_pc hpc (Eventually.mono (cp_step hp h at0 hi hinv)
      fun st' hs ↦ ?_)) ⟨0, rfl, by omega, rfl, inv⟩
  rcases hs with ⟨he, hpc', hinv'⟩ | ⟨hlt, hpc', hinv'⟩
  · have e : i + 1 = xs.size / 2 := by omega
    rw [e] at hinv'
    exact .inl ⟨hpc', hinv'⟩
  · exact .inr ⟨xs.size / 2 - (i + 1), by omega, i + 1, rfl, by omega, hpc', hinv'⟩

/-- **The copy** (`b31` to `b40`), from `AtCp`. -/
theorem cp_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {y vs : Array EW}
    {d : MachineData} (at0 : AtCp a s0 g0 m0 xs y vs s' d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b31Offset)⟩ := by
  have hcap := at0.size
  unfold busPointCap at hcap
  have hst := pre_step h
  set st := (reg m0 .rsi).toNat with hstd
  set n := xs.size with hn
  have c0 : CpS a m0 xs s' d 0 d :=
    ⟨at0.fr, at0.r13, ⟨fun _ _ hb ↦ hb⟩, ⟨fun _ hb ↦ hb⟩, at0.ts, fun _ _ hj ↦ absurd hj (by omega)⟩
  have e13 : reg d .r13 = BitVec.ofNat 64 n := bv_of at0.r13 (by omega)
  -- `b31`: no challenges?
  have hwf1 := wf0 h at0.fr.frame.kept 0
  obtain ⟨hmid1, hmem1, hk1⟩ := ok_b31
  refine exec_then (infix_of b31_in_code (by simp [b31]) hp) exit_b31 hwf1 nofun
    (match_head at0.fr 0) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨fr1, hd1⟩ := FR.block_nil h at0.fr hwf1 hm1 hmid1 hmem1
  have c1 := c0.eq fr1 hd1 (kr hm1 hk1 (by simp))
  have hc1 : SBool.eval (frameEnv m0 d 1408 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W64 (.bin .and .W64 (.reg .r13) (.reg .r13)) (.lit 0)) = decide (n = 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg d .r13) (reg d .r13))
      (BitVec.ofNat 64 0) = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [eq64' _ _ (by omega), at0.r13]
  simp only [PcOk, hc1] at hpc1
  by_cases hn0 : n = 0
  · simp only [hn0, decide_true, ↓reduceIte] at hpc1
    exact at_pc (hpc1.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_23_at)) (fin_spec hp h at0
      ⟨c1.fr, c1.r13, c1.fk, c1.pk, c1.ts, fun _ _ hj ↦ absurd hj (by omega)⟩)
  simp only [hn0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b32`: `16 step`; one challenge?
  have hwf2 := wf0 h fr1.frame.kept 0
  obtain ⟨hmid2, hmem2, hbx2, hk2⟩ := ok_b32
  refine exec_at (infix_of b32_in_code (by simp [b32]) hp) exit_b32 hwf2 nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b31_next)) (match_head fr1 0) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨fr2, hd2⟩ := FR.block_nil h fr1 hwf2 hm2 hmid2 hmem2
  have c2 := c1.eq fr2 hd2 (kr hm2 hk2 (by simp))
  have ebx2 : reg st2.data .rbx = BitVec.ofNat 64 (16 * st) := by
    rw [rv hm2 hbx2]
    show BinOp.apply .shl .W64 (reg st1.data .rbx) (BitVec.ofNat 64 4) = _
    rw [kr hm1 hk1 (by simp), at0.rbx, bv_of (x := reg m0 .rsi) rfl (by omega),
      shl4_all _ (by omega)]
  have e13' : reg st1.data .r13 = BitVec.ofNat 64 n := (kr hm1 hk1 (by simp)).trans e13
  have hc2 : SBool.eval (frameEnv m0 st1.data 1408 [] (fun _ ↦ 0) 0)
      (SBool.cmp .eq .W64 (.reg .r13) (.lit 1)).not = !decide (n = 1) := by
    show (!CmpOp.apply .eq .W64 (reg st1.data .r13) (BitVec.ofNat 64 1)) = _
    rw [eq64' _ _ (by omega), e13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [PcOk, hc2] at hpc2
  by_cases hn1 : n = 1
  · -- `b33`: the one challenge.
    simp only [hn1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    have hwf3 := wf0 h fr2.frame.kept 0
    obtain ⟨hmid3, hmem3, hax3, hk3⟩ := ok_b33
    refine exec_at (infix_of b33_in_code (by simp [b33]) hp) exit_b33 hwf3 nofun
      (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b32_next)) (match_head fr2 0)
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨fr3, hd3⟩ := FR.block_nil h fr2 hwf3 hm3 hmid3 hmem3
    simp only [PcOk] at hpc3
    exact at_pc (hpc3.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_22_at)) (cp_last hp h at0 (by omega)
      (by rw [← hn, hn1]; exact c2.eq fr3 hd3 (kr hm3 hk3 (by simp)))
      (by rw [rv hm3 hax3, ← hn, hn1]; rfl) ((kr hm3 hk3 (by simp)).trans ebx2))
  simp only [hn1, decide_false, Bool.not_false, ↓reduceIte] at hpc2
  -- `b36`: the pairs' loop's start.
  have hwf4 := wf0 h fr2.frame.kept 0
  obtain ⟨hmid4, hmem4, hcx4, h144, hdx4, hax4, hk4⟩ := ok_b36
  refine exec_at (infix_of b36_in_code (by simp [b36]) hp) exit_b36 hwf4 nofun
    (hpc2.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_19_at)) (match_head fr2 0) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨fr4, hd4⟩ := FR.block_nil h fr2 hwf4 hm4 hmid4 hmem4
  have e13'' : reg st2.data .r13 = BitVec.ofNat 64 n := (kr hm2 hk2 (by simp)).trans e13'
  have inv0 : LInv a m0 xs s' d 0 st4.data := by
    refine ⟨c2.eq fr4 hd4 (kr hm4 hk4 (by simp)), by rw [rv hm4 hax4]; rfl,
      by rw [rv hm4 hdx4]; rfl, ?_, ?_, (kr hm4 hk4 (by simp)).trans ebx2⟩
    · rw [rv hm4 hcx4]
      show BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (reg st2.data .r13)) (BitVec.ofNat 64 62) = _
      rw [e13'', and62_all _ (by omega)]
    · rw [rv hm4 h144]
      show BinOp.apply .add .W64 (reg st2.data .rbx) (reg st2.data .r14) = _
      rw [ebx2, kr hm2 hk2 (by simp), kr hm1 hk1 (by simp), at0.r14, addW, BitVec.add_comm]
  simp only [PcOk] at hpc4
  refine at_pc (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b36_next))
    (Eventually.bind (cp_loop hp h at0 (by omega) inv0) fun st5 ⟨hpc5, inv5⟩ ↦ ?_)
  -- `b38`: an odd last challenge?
  have hwf6 := wf0 h inv5.cs.fr.frame.kept 0
  obtain ⟨hmid6, hmem6, hk6⟩ := ok_b38
  refine exec_at (infix_of b38_in_code (by simp [b38]) hp) exit_b38 hwf6 nofun hpc5
    (match_head inv5.cs.fr 0) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨fr6, hd6⟩ := FR.block_nil h inv5.cs.fr hwf6 hm6 hmid6 hmem6
  have c6 := inv5.cs.eq fr6 hd6 (kr hm6 hk6 (by simp))
  have hc6 : SBool.eval (frameEnv m0 st5.data 1408 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W8 (.bin .and .W8 (.reg .r13) (.lit 1)) (.lit 0)) = decide (n % 2 = 0) := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st5.data .r13) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = _
    rw [bv_of inv5.cs.r13 (by omega), and_odd_all _ (by omega)]
  simp only [PcOk, hc6] at hpc6
  by_cases ho : n % 2 = 0
  · simp only [ho, decide_true, ↓reduceIte] at hpc6
    exact at_pc (hpc6.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_23_at)) (fin_spec hp h at0
      ⟨c6.fr, c6.r13, c6.fk, c6.pk, c6.ts, fun j hj _ ↦ c6.cp j hj (by omega)⟩)
  · simp only [ho, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc6
    exact at_pc (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b38_next)) (cp_last hp h at0 (by omega)
      ⟨c6.fr, c6.r13, c6.fk, c6.pk, c6.ts, fun j hj hj' ↦ c6.cp j hj (by omega)⟩
      ((kr hm6 hk6 (by simp)).trans (inv5.rax.trans (by congr 1; omega)))
      ((kr hm6 hk6 (by simp)).trans inv5.rbx))

end

end NativeRustcVmX64.Bus.GkrStep
