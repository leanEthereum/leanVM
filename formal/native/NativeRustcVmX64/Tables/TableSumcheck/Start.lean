module

public import NativeRustcVmX64.Tables.TableSumcheck.State
public import NativeRustcVmX64.Tables.TableTerms.Entry
public import NativeRustcVmX64.Code.Vm.TableSumcheck.Names

/-!
# `table_sumcheck`: the entry and the exits (x86-64)

`b0` pushes RBP to RBX, keeps the arguments in callee-saved registers and computes the heights'
maximum `n` in R13 (at most `30`, so it goes on): `start`. `b15` (`NativeRustcVmX64.Vm.TableSumcheck.label_12`) restores
the registers and returns AL (`exit15`); `b14` (`NativeRustcVmX64.Vm.TableSumcheck.label_11`) clears it first
(`exit_fail`: the model's run fails).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableSumcheck
open NativeRustcVmX64.Tables.TableTerms (at_pc addr_eq)
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The heights' maximum: the sumcheck's rounds. -/
def nR (heights : Array Nat) : Nat := heights.foldl max 0

/-- **After the prologue**: the arguments in callee-saved registers, `n` in R13, the `TState`. -/
structure St0 [Labels] (a : DecArea) (s : TState) (heights : Array Nat) (m0 d : MachineData) :
    Prop where
  r13 : reg d .r13 = BitVec.ofNat 64 (nR heights)
  rbp : reg d .rbp = cpA m0
  r14 : reg d .r14 = bA m0
  rbx : reg d .rbx = hA m0
  r10 : reg d .r10 = tA m0
  r8 : reg d .r8 = fpA m0
  r9 : reg d .r9 = reg m0 .r9
  ts : TStateAt d.dmem (tA m0) a s

end

public section

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n :=
  NativeRustcVm.toNat_ofNat_of_lt h

theorem eval_gt [Labels] {env : Env} (x y : Sym) :
    (gt x y).eval env = decide ((y.eval env).toNat < (x.eval env).toNat) := by
  unfold gt
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.ult]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne,
    ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have : (x.eval env).toNat ≠ (y.eval env).toNat := fun he ↦ h2 (BitVec.eq_of_toNat_eq he)
    omega
  · intro h
    exact ⟨by omega, fun he ↦ by rw [he] at h; omega⟩

theorem eval_mx [Labels] {env : Env} {a b : Sym} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (ha : a.eval env = BitVec.ofNat 64 x) (hb : b.eval env = BitVec.ofNat 64 y) :
    (mx a b).eval env = BitVec.ofNat 64 (max x y) := by
  unfold mx
  show (if (gt b a).eval env then b.eval env else a.eval env) = _
  rw [eval_gt, ha, hb, toNat_ofNat_lt hx, toNat_ofNat_lt hy]
  by_cases hxy : x < y
  · simp [hxy, Nat.max_eq_right (Nat.le_of_lt hxy)]
  · simp [hxy, Nat.max_eq_left (by omega : y ≤ x)]

theorem foldl_max_lt (H : Array Nat) (h : H.size = 6) (hle : ∀ x ∈ H, x ≤ 30) :
    H.foldl max 0 < 2 ^ 64 := by
  have := foldl_max_le H h hle; omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableSumcheck.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.TableSumcheck.entry_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableSumcheck.label_5 = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.TableSumcheck.label_5_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableSumcheck.label_6 = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b7Offset) :=
  hp.label NativeRustcVmX64.Vm.TableSumcheck.label_6_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableSumcheck.label_8 = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b9Offset) :=
  hp.label NativeRustcVmX64.Vm.TableSumcheck.label_8_at
theorem lbl_9 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableSumcheck.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b10Offset) :=
  hp.label NativeRustcVmX64.Vm.TableSumcheck.label_9_at
theorem lbl_11 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableSumcheck.label_11 = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b14Offset) :=
  hp.label NativeRustcVmX64.Vm.TableSumcheck.label_11_at
theorem lbl_12 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableSumcheck.label_12 = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b15Offset) :=
  hp.label NativeRustcVmX64.Vm.TableSumcheck.label_12_at

/-- **The epilogue** (`b15`): the registers restored, `ret`, AL kept. -/
theorem exit15 (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0) {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) 40 d)
    (hpost : ∀ d' : MachineData, d'.dmem = d.dmem → reg d' .rax = reg d .rax →
      OkAl d' (res s heights bus m0).isSome ∧
      (∀ x s', res s heights bus m0 = some (x, s') → TableEvalsAt d'.dmem (ev m0) x) ∧
      NextAt d'.dmem (tA m0) a (res s heights bus m0)) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b15Offset)⟩ := by
  obtain ⟨hepi, hmem, hrax⟩ := ok_b15
  refine Bd.done' (st := ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b15Offset)⟩) hb (Pre.stack h)
    (by unfold N tableSumcheckStack; omega) (infix_of b15_in_code (by simp [b15]) hp) exit_b15 rfl
    (match_body hb ⟨rfl, trivial⟩ trivial) hepi hmem fun st' hm' hpc hrsp hsv hd ↦ ?_
  obtain ⟨p1, p2, p3⟩ := hpost st'.data hd (hm'.regs .rax _ hrax)
  refine ⟨hpc, hrsp, p1, p2, p3, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hb.same fun q hq ↦ hq.elim
    (fun h ↦ h.elim .inl (.inr ∘ .inl)) (fun h ↦ .inr (.inr h))

omit [Host] in
theorem okWord_false_toNat : (okWord false).toNat = 0 := rfl

/-- **A failed run** (`b14`): AL `0`. -/
theorem exit_fail (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0) {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) 40 d) (hr : res s heights bus m0 = none) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b14Offset)⟩ := by
  have hwf : (E m0 d [] 0).WF := wf_nil h hb.fr.kept
  have hm : Match (E m0 d [] 0) sF d := match_body hb ⟨rfl, trivial⟩ trivial
  refine exec_then (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf nofun hm
    fun st hm1 hpc ↦ ?_
  obtain ⟨mid, mem, rax⟩ := ok_b14
  have hd : st.data.dmem = d.dmem := hm1.dmem_eq hwf mem
  have hb1 := (blockB h hb hwf hm1 mid (by rw [WrOk, mem]; rfl)).1
  have hrax : reg st.data .rax = 0 := hm1.regs .rax _ rax
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b14_next)))
    (exit15 hp h hb1 fun d' _ hra ↦ ⟨?_, fun x s' h' ↦ (by rw [hr] at h'; cases h'),
      fun x s' h' ↦ (by rw [hr] at h'; cases h')⟩)
  unfold OkAl boolRet
  rw [hra, hrax, hr]
  rfl

/-- The heights' words, loaded from region `1`. -/
theorem ld_h (h : TableSumcheckPre a s heights bus m0) {i : Nat} (hi : i < 6) {ret : BitVec 64} :
    (hS i).eval (E m0 m0 [(hA m0, 48)] ret) = BitVec.ofNat 64 (heights[i]'(by
      rw [(Pre.hts h).1]; exact hi)) := by
  have hH := Pre.hts h
  have hsz : heights.size = 6 := hH.1
  have hw := hH.2.2
  rw [wordsAt_iff] at hw
  have hl : i < (heights.toList.map Nat.toUInt64).length := by simp [hsz]; exact hi
  have := hw i hl
  simp only [List.getElem_map, Array.getElem_toList] at this
  show (E m0 m0 [(hA m0, 48)] ret).load 1 (8 * i) 8 = _
  rw [NativeRustcVmX64.Tables.TableTerms.load_eq_wordOf]
  show (wordOf m0.dmem (hA m0 + BitVec.ofNat 64 (8 * i))).toBitVec = _
  rw [NativeRustcVm.wordOf_of_wordAt this]
  have hle := hH.2.1 _ (Array.getElem_mem (show i < heights.size by omega))
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega), toNat_ofNat_lt (by omega)]

/-- **The prologue** (`b0`): to the sumcheck's call. -/
theorem start (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0)
    {R : MachineState → Prop}
    (cont : ∀ d, Bd m0 736 N slots (outs m0) 40 d → St0 a s heights m0 d →
      Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b1Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b0Offset)⟩ := by
  have hH := Pre.hts h
  have hsz : heights.size = 6 := hH.1
  have hwf : (E m0 m0 [(hA m0, 48)] 0).WF :=
    wf_one h (fun _ h ↦ h) (Pre.hs h).1.1 (Pre.hs h).1.2 (frame_ap h (Pre.hs h).2.1)
  have hm : Match (E m0 m0 [(hA m0, 48)] 0) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
      ⟨by show reg m0 .rsi = hA m0 + BitVec.ofInt 64 0; rw [ofInt_zero64, BitVec.add_zero], trivial⟩
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hpro, hW, r13, rbp, r14, rbx, r10, r8, r9⟩ := ok_b0
  have hin := writesIn_of_pro hpro
  have hbr := belowRet_of_pro hpro
  have hfr : Frame m0 736 slots 40 st.data :=
    Frame.of_prologue Frame.entry hwf hm' hpro (fun p hp ↦ (slots_le p hp).2) slots_cs
  have hs0 := same_block hwf hm' hin hbr hW (X := fun _ ↦ False) (fun _ h ↦ nomatch h)
  have hs : NativeRustcVm.SameOutside m0.dmem st.data.dmem
      (fun q ↦ outs m0 q ∨ NativeRustcVm.InRange (stackBelow m0 N) N q) :=
    NativeRustcVm.SameOutside.mono hs0 fun q hq ↦ hq.elim (fun h' ↦ .inr (fr_stack h h')) False.elim
  have hle := fun x hx ↦ hH.2.1 x hx
  have hn : (R13.eval (E m0 m0 [(hA m0, 48)] 0)) = BitVec.ofNat 64 (nR heights) := by
    have l : ∀ i (hi : i < 6), (hS i).eval (E m0 m0 [(hA m0, 48)] 0) =
        BitVec.ofNat 64 (heights[i]'(by omega)) := fun i hi ↦ ld_h h hi
    have b : ∀ i (hi : i < 6), heights[i]'(by omega) < 2 ^ 64 := fun i hi ↦ by
      have := hle _ (Array.getElem_mem (show i < heights.size by omega)); omega
    have b0 := b 0 (by omega); have b1 := b 1 (by omega); have b2 := b 2 (by omega)
    have b3 := b 3 (by omega); have b4 := b 4 (by omega); have b5 := b 5 (by omega)
    unfold nR R13
    rw [foldl_max6 heights hsz]
    refine eval_mx (by omega) b5 ?_ (l 5 (by omega))
    refine eval_mx (by omega) b4 ?_ (l 4 (by omega))
    refine eval_mx (by omega) b3 ?_ (l 3 (by omega))
    refine eval_mx (by omega) b2 ?_ (l 2 (by omega))
    exact eval_mx b0 b1 (l 0 (by omega)) (l 1 (by omega))
  have hn30 := foldl_max_le heights hsz hle
  have hc : (gt R13 (.lit 30)).eval (E m0 m0 [(hA m0, 48)] 0) = false := by
    rw [eval_gt, hn]
    simp only [Sym.eval, toNat_ofNat_lt (show 30 < 2 ^ 64 by omega),
      toNat_ofNat_lt (show nR heights < 2 ^ 64 by unfold nR; omega)]
    simp only [decide_eq_false_iff_not, Nat.not_lt]
    exact hn30
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc
  have rg : ∀ {r : Reg64} {v : Sym}, (after b0 entryS).reg r = some v →
      reg st.data r = v.eval (E m0 m0 [(hA m0, 48)] 0) := fun hv ↦ hm'.regs _ _ hv
  refine at_pc (hpc.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b0_next))) (cont st.data ⟨hfr, hs⟩
    ⟨(rg r13).trans hn, rg rbp, rg r14, rg rbx, rg r10, rg r8, rg r9, ?_⟩)
  exact (Pre.ts h).frame (hm'.kept hwf) (fun q hq ↦ (ctx h).stack_not_t
    (hq.elim (fr_stack h) False.elim)) hs0

end

end NativeRustcVmX64.Tables.TableSumcheck
