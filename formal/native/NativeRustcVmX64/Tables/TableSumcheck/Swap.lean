module

public import NativeRustcVmX64.Tables.TableSumcheck.Plain
public import NativeRustcVmX64.Tables.TableSumcheck.Loc

/-!
# `table_sumcheck`: the challenges' swaps (x86-64)

The challenges are reversed in place: `b7` (`NativeRustcVmX64.Vm.TableSumcheck.label_6`) swaps two pairs, the challenges
`2t`, `2t + 1` with `n - 1 - 2t`, `n - 2 - 2t` (`iter`, `loop`), `b9` (`NativeRustcVmX64.Vm.TableSumcheck.label_8`) one
more pair (`one`). `Kp`: what the swaps keep (the body, the words saved at `56` to `88`, the claim
at `600`, the `TState`, `n`, the heights); `Ch m0 L j`: the challenges after `j` swaps (`rv`).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableSumcheck
open NativeRustcVmX64.Tables.TableTerms (at_pc addr_eq)

@[expose] public section

/-- The challenges after `j` swaps. -/
def Ch (m0 : MachineData) (L : List EW) (j : Nat) (d : MachineData) : Prop :=
  ∀ i (_ : i < L.length), NativeRustcVm.EWAt d.dmem (off (fb m0) (112 + 16 * i)) (rv L j i)

/-- **What the swaps keep.** -/
structure Kp [Labels] (a : DecArea) (s1 : TState) (heights : Array Nat) (m0 : MachineData) (c : EW)
    (d : MachineData) : Prop where
  bd : Bd m0 736 N slots (outs m0) 40 d
  w56 : NativeRustcVm.WordAt d.dmem (off (fb m0) 56) (.ofBitVec (cpA m0))
  w64 : NativeRustcVm.WordAt d.dmem (off (fb m0) 64) (.ofBitVec (fpA m0))
  w72 : NativeRustcVm.WordAt d.dmem (off (fb m0) 72) (.ofBitVec (bA m0))
  w80 : NativeRustcVm.WordAt d.dmem (off (fb m0) 80) (.ofBitVec (tA m0))
  cl : NativeRustcVm.EWAt d.dmem (off (fb m0) 600) c
  ts : TStateAt d.dmem (tA m0) a s1
  r13 : reg d .r13 = BitVec.ofNat 64 (nR heights)
  rbx : reg d .rbx = hA m0

/-- The two pairs `b7` swaps: the challenges `2t`, `2t + 1`, `n - 1 - 2t`, `n - 2 - 2t`. -/
def swL (n t : Nat) : List (Nat × Nat) :=
  [(112 + 32 * t, 32), (112 + 16 * (n - 1 - 2 * t), 16), (112 + 16 * (n - 2 - 2 * t), 16)]

/-- The pair `b9` swaps: the challenges `c`, `n - 1 - c`. -/
def oneL (n c : Nat) : List (Nat × Nat) := [(112 + 16 * c, 16), (112 + 16 * (n - 1 - c), 16)]

/-- The loop's registers at its iteration `t` of `T`. -/
structure LR (m0 : MachineData) (n t T : Nat) (d : MachineData) : Prop where
  rcx : reg d .rcx = BitVec.ofNat 64 (2 * t)
  r15 : reg d .r15 = off (fb m0) (112 + 32 * t)
  rsi : reg d .rsi + BitVec.ofNat 64 (32 * t) = off (fb m0) (96 + 16 * n)
  rax : reg d .rax = off (fb m0) (112 + 16 * n)
  rdi : reg d .rdi = BitVec.ofNat 64 1152921504606846974
  rdx : reg d .rdx = BitVec.ofNat 64 (2 * T)

end

/-! ## Words -/

public section

theorem f_shr : ∀ n < 31, BinOp.apply .shr .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 1) =
    BitVec.ofNat 64 (n / 2) := by decide +kernel

theorem f_and : ∀ x < 16, BinOp.apply .and .W32 (BitVec.ofNat 64 x) (BitVec.ofNat 64 14) =
    BitVec.ofNat 64 (2 * (x / 2)) := by decide +kernel

theorem f_test : ∀ n < 31, CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 2)) (BitVec.ofNat 64 0) = decide (n / 2 % 2 = 0) := by decide +kernel

theorem f_xor : ∀ t < 8, BinOp.apply .shl .W64 (BinOp.apply .xor .W64 (BitVec.ofNat 64 (2 * t))
    (BitVec.ofNat 64 1152921504606846974)) (BitVec.ofNat 64 4) + BitVec.ofNat 64 (32 + 32 * t) = 0 := by
  decide +kernel

theorem f_not : ∀ c < 16, BinOp.apply .shl .W64 (UnOp.apply .not .W64 (BitVec.ofNat 64 c))
    (BitVec.ofNat 64 4) + BitVec.ofNat 64 (16 * c + 16) = 0 := by decide +kernel

theorem f_m72 : BitVec.ofInt 64 (-72) = BitVec.ofNat 64 18446744073709551544 := by decide

theorem add_apply (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by simp [BinOp.apply]

theorem eq_apply {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    CmpOp.apply .eq .W64 (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x = y) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rwa [toNat_ofNat_lt hx, toNat_ofNat_lt hy] at this
  · rintro rfl; rfl

theorem shl4 (n : Nat) : BinOp.apply .shl .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 4) =
    BitVec.ofNat 64 (16 * n) := by
  have e : BinOp.apply .shl .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 4) =
      BitVec.ofNat 64 n <<< 4 := by
    simp only [BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
    congr 1
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem off_congr {b : BitVec 64} {i j : Nat} (h : i = j) : off b i = off b j := by rw [h]

theorem ew_congr {d : Mem 64} {b : BitVec 64} {i j : Nat} {x : EW} (h : i = j)
    (hx : NativeRustcVm.EWAt d (off b i) x) : NativeRustcVm.EWAt d (off b j) x := h ▸ hx

/-! ## The swaps -/

theorem rv_one {L : List EW} {j : Nat} (hj : 2 * j + 2 ≤ L.length) :
    rv L (j + 1) j = rv L j (L.length - 1 - j) ∧ rv L (j + 1) (L.length - 1 - j) = rv L j j ∧
    ∀ i, i ≠ j → i ≠ L.length - 1 - j → rv L (j + 1) i = rv L j i := by
  refine ⟨?_, ?_, fun i h1 h2 ↦ ?_⟩
  · rw [rv_succ L hj]; simp
  · rw [rv_succ L hj]; simp [show L.length - 1 - j ≠ j by omega]
  · rw [rv_succ L hj]; simp [h1, h2]

theorem rv_two {L : List EW} {j : Nat} (hj : 2 * j + 4 ≤ L.length) :
    rv L (j + 2) j = rv L j (L.length - 1 - j) ∧ rv L (j + 2) (L.length - 1 - j) = rv L j j ∧
    rv L (j + 2) (j + 1) = rv L j (L.length - 2 - j) ∧
    rv L (j + 2) (L.length - 2 - j) = rv L j (j + 1) ∧
    ∀ i, i ≠ j → i ≠ L.length - 1 - j → i ≠ j + 1 → i ≠ L.length - 2 - j →
      rv L (j + 2) i = rv L j i := by
  obtain ⟨a0, b0, c0⟩ := rv_one (L := L) (j := j) (by omega)
  obtain ⟨a1, b1, c1⟩ := rv_one (L := L) (j := j + 1) (by omega)
  have e : L.length - 1 - (j + 1) = L.length - 2 - j := by omega
  rw [e] at a1 b1
  rw [show j + 2 = j + 1 + 1 from rfl]
  refine ⟨?_, ?_, ?_, ?_, fun i h1 h2 h3 h4 ↦ ?_⟩
  · rw [c1 j (by omega) (by omega), a0]
  · rw [c1 _ (by omega) (by omega), b0]
  · rw [a1, c0 _ (by omega) (by omega)]
  · rw [b1, c0 _ (by omega) (by omega)]
  · rw [c1 i h3 (by omega), c0 i h1 h2]

variable [Labels] {a : DecArea} {s s1 : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {c : EW}

omit [Labels] in
theorem LE_base {d : MachineData} {L : List (Nat × Nat)} {r : Nat} {p : Nat × Nat}
    (hp : L[r]? = some p) : (LE m0 d L).base r = off (fb m0) p.1 :=
  Env.base_ofMachine _ _ _ _ (locs_get' hp)

omit [Labels] in
/-- An element no part holds, kept. -/
theorem ew_keep {d d' : MachineData} {L : List (Nat × Nat)} {Sy : SState} [Labels]
    (hwf : (LE m0 d L).WF) (hm : Match (LE m0 d L) Sy d') (hin : InLocs L Sy)
    (hL : ∀ p ∈ L, p.1 + p.2 ≤ 744) {lo : Nat} (hlo : lo + 16 ≤ 744)
    (hmiss : ∀ p ∈ L, lo + 16 ≤ p.1 ∨ p.1 + p.2 ≤ lo) {x : EW}
    (hx : NativeRustcVm.EWAt d.dmem (off (fb m0) lo) x) :
    NativeRustcVm.EWAt d'.dmem (off (fb m0) lo) x :=
  bytes_keep hwf hm hin hL (bs := NativeRustcVm.ewBytes x)
    (by rw [NativeRustcVm.length_ewBytes]; exact hlo)
    (fun p hp ↦ by rw [NativeRustcVm.length_ewBytes]; exact hmiss p hp) hx

omit [Labels] in
/-- A word no part holds, kept. -/
theorem word_keep {d d' : MachineData} {L : List (Nat × Nat)} {Sy : SState} [Labels]
    (hwf : (LE m0 d L).WF) (hm : Match (LE m0 d L) Sy d') (hin : InLocs L Sy)
    (hL : ∀ p ∈ L, p.1 + p.2 ≤ 744) {lo : Nat} (hlo : lo + 8 ≤ 744)
    (hmiss : ∀ p ∈ L, lo + 8 ≤ p.1 ∨ p.1 + p.2 ≤ lo) {w : UInt64}
    (hx : NativeRustcVm.WordAt d.dmem (off (fb m0) lo) w) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) lo) w :=
  bytes_keep hwf hm hin hL (bs := NativeRustcVm.wordBytes w)
    (by rw [NativeRustcVm.length_wordBytes]; exact hlo)
    (fun p hp ↦ by rw [NativeRustcVm.length_wordBytes]; exact hmiss p hp) hx

/-- **A block over parts of the challenges** keeps `Kp`. -/
theorem Kp.loc (h : TableSumcheckPre a s heights bus m0) {d d' : MachineData}
    (H : Kp a s1 heights m0 c d) {L : List (Nat × Nat)} {Sy : SState} (hwf : (LE m0 d L).WF)
    (hm : Match (LE m0 d L) Sy d') (hin : InLocs L Sy)
    (hL : ∀ p ∈ L, 112 ≤ p.1 ∧ p.1 + p.2 ≤ 592) (hsp : Sy.reg .rsp = some (.reg .rsp))
    (h13 : reg d' .r13 = reg d .r13) (hbx : reg d' .rbx = reg d .rbx) :
    Kp a s1 heights m0 c d' := by
  have hL' : ∀ p ∈ L, p.1 + p.2 ≤ 744 := fun p hp ↦ by have := hL p hp; omega
  obtain ⟨hb, hso⟩ := Bd.loc h H.bd hwf hm hin (fun p hp ↦ by have := hL p hp; omega) hsp
  have kw : ∀ {lo : Nat} {w : UInt64}, lo + 8 ≤ 112 ∨ 592 ≤ lo → lo + 8 ≤ 744 →
      NativeRustcVm.WordAt d.dmem (off (fb m0) lo) w →
      NativeRustcVm.WordAt d'.dmem (off (fb m0) lo) w := fun h1 h2 hw ↦
    word_keep hwf hm hin hL' h2 (fun p hp ↦ by have := hL p hp; omega) hw
  refine ⟨hb, kw (by omega) (by omega) H.w56, kw (by omega) (by omega) H.w64,
    kw (by omega) (by omega) H.w72, kw (by omega) (by omega) H.w80,
    ew_keep hwf hm hin hL' (by omega) (fun p hp ↦ by have := hL p hp; omega) H.cl,
    H.ts.frame (hm.kept hwf) (fun q hq ↦ (ctx h).stack_not_t (fr_stack h hq)) hso,
    h13.trans H.r13, hbx.trans H.rbx⟩

/-- **A body block writing nothing** keeps `Kp` and memory. -/
theorem Kp.nil (h : TableSumcheckPre a s heights bus m0) {d d' : MachineData}
    (H : Kp a s1 heights m0 c d) {Sy : SState} (hwf : (E m0 d [] 0).WF)
    (hm : Match (E m0 d [] 0) Sy d') (hmid : MidOk 736 40 slots Sy = true) (hmem : Sy.mem = [])
    (hk : Keeps Sy csR = true) : Kp a s1 heights m0 c d' ∧ d'.dmem = d.dmem := by
  have hd : d'.dmem = d.dmem := hm.dmem_eq hwf hmem
  have hb := (blockB h H.bd hwf hm hmid (by rw [WrOk, hmem]; rfl)).1
  refine ⟨⟨hb, ?_, ?_, ?_, ?_, ?_, ?_, (keeps_reg hm hk (by simp)).trans H.r13,
    (keeps_reg hm hk (by simp)).trans H.rbx⟩, hd⟩ <;> rw [hd]
  exacts [H.w56, H.w64, H.w72, H.w80, H.cl, H.ts]

omit [Labels] in
theorem Ch.nil {L : List EW} {j : Nat} {d d' : MachineData} (hc : Ch m0 L j d)
    (hd : d'.dmem = d.dmem) : Ch m0 L j d' := fun i hi ↦ by rw [hd]; exact hc i hi

end

public section

variable [Host] {k : Nat} {a : DecArea} {s s1 : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {c : EW}

/-- **One iteration of the loop** (`b7`): the pairs `2t`, `n - 1 - 2t` and `2t + 1`,
`n - 2 - 2t` swapped. -/
theorem iter (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0) {L : List EW}
    (hL : L.length = nR heights) {T t : Nat} (htT : t < T) (hT : 4 * T ≤ nR heights)
    {d : MachineData} (H : Kp a s1 heights m0 c d) (hc : Ch m0 L (2 * t) d)
    (hr : LR m0 (nR heights) t T d)
    (cont : ∀ d' pc, Kp a s1 heights m0 c d' → Ch m0 L (2 * t + 2) d' →
      LR m0 (nR heights) (t + 1) T d' → (T = t + 1 → pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b8Offset)) →
      (T ≠ t + 1 → pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b7Offset)) →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d', pc⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b7Offset)⟩ := by
  have hH := Pre.hts h
  have hn30 : nR heights ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  generalize hn : nR heights = n at hL hT hr cont hn30
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hmem : ∀ p ∈ swL n t, p = (112 + 32 * t, 32) ∨ p = (112 + 16 * (n - 1 - 2 * t), 16) ∨
      p = (112 + 16 * (n - 2 - 2 * t), 16) := fun p hp ↦ by
    simpa only [swL, List.mem_cons, List.not_mem_nil, or_false] using hp
  have hLb : ∀ p ∈ swL n t, 112 ≤ p.1 ∧ p.1 + p.2 ≤ 592 := fun p hp ↦ by
    rcases hmem p hp with rfl | rfl | rfl <;> dsimp only <;> omega
  have hL' : ∀ p ∈ swL n t, p.1 + p.2 ≤ 744 := fun p hp ↦ by have := hLb p hp; omega
  have hwf : (LE m0 d (swL n t)).WF :=
    loc_wf h H.bd.fr.kept (fun p hp ↦ by have := hLb p hp; omega) (by
      simp only [swL, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
        implies_true]
      omega)
  have b0 : (LE m0 d (swL n t)).base 0 = off (fb m0) (112 + 32 * t) :=
    LE_base (p := (112 + 32 * t, 32)) rfl
  have b1 : (LE m0 d (swL n t)).base 1 = off (fb m0) (112 + 16 * (n - 1 - 2 * t)) :=
    LE_base (p := (112 + 16 * (n - 1 - 2 * t), 16)) rfl
  have b2 : (LE m0 d (swL n t)).base 2 = off (fb m0) (112 + 16 * (n - 2 - 2 * t)) :=
    LE_base (p := (112 + 16 * (n - 2 - 2 * t), 16)) rfl
  have hm : Match (LE m0 d (swL n t)) swapS d := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ trivial trivial trivial ⟨?_, ?_, ?_, trivial⟩
    · show reg d .r15 = _
      rw [b0, ofInt_zero64, BitVec.add_zero]; exact hr.r15
    · show reg d .rsi = _
      rw [b1, ofInt_zero64, BitVec.add_zero]
      have := hr.rsi
      unfold off at this ⊢
      bv_omega
    · show BinOp.apply .add .W64 (reg d .rax) (BinOp.apply .shl .W64
        (BinOp.apply .xor .W64 (reg d .rcx) (reg d .rdi)) (BitVec.ofNat 64 4)) = _
      rw [b2, ofInt_zero64, BitVec.add_zero, hr.rax, hr.rcx, hr.rdi, add_apply]
      have := f_xor t (by omega)
      generalize BinOp.apply .shl .W64 (BinOp.apply .xor .W64 (BitVec.ofNat 64 (2 * t))
        (BitVec.ofNat 64 1152921504606846974)) (BitVec.ofNat 64 4) = X at this ⊢
      unfold off
      bv_omega
  refine exec_then (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf nofun hm
    fun st hm7 hpc7 ↦ ?_
  obtain ⟨hin7, w0, w8, v0, v8, w16, w24, u0, u8, rcx7, r15_7, rsi7, rsp7, rax7, rdx7, rdi7, k7⟩ :=
    ok_b7
  have hin : InLocs (swL n t) (after b7 swapS) := fun w hw ↦ by
    rcases hin7 w hw with ⟨hr', hl⟩ | ⟨hr', hl⟩ | ⟨hr', hl⟩ <;> exact ⟨_, by rw [hr']; rfl, hl⟩
  have rg : ∀ {r : Reg64} {v : Sym}, (after b7 swapS).reg r = some v →
      reg st.data r = v.eval (LE m0 d (swL n t)) := fun hv ↦ hm7.regs _ _ hv
  have H' : Kp a s1 heights m0 c st.data :=
    Kp.loc h H hwf hm7 hin hLb rsp7 (keeps_reg hm7 k7 (by simp)) (keeps_reg hm7 k7 (by simp))
  -- The challenges.
  have e0 := hc (2 * t) (by omega)
  have e1 := hc (2 * t + 1) (by omega)
  have e2 := hc (n - 1 - 2 * t) (by omega)
  have e3 := hc (n - 2 - 2 * t) (by omega)
  have l0 := ew_ld (d := d) (L := swL n t) (r := 0) (p := (112 + 32 * t, 32)) rfl (o := 0)
    (ew_congr (by dsimp only; omega) e0)
  have l16 := ew_ld (d := d) (L := swL n t) (r := 0) (p := (112 + 32 * t, 32)) rfl (o := 16)
    (ew_congr (by dsimp only; omega) e1)
  have l1 := ew_ld (d := d) (L := swL n t) (r := 1) (p := (112 + 16 * (n - 1 - 2 * t), 16)) rfl
    (o := 0) (ew_congr (by dsimp only; omega) e2)
  have l2 := ew_ld (d := d) (L := swL n t) (r := 2) (p := (112 + 16 * (n - 2 - 2 * t), 16)) rfl
    (o := 0) (ew_congr (by dsimp only; omega) e3)
  have n0 := ew_written hm7 (r := 0) (p := (112 + 32 * t, 32)) rfl (o := 0) (by dsimp only; omega)
    w0 w8 l1.1 l1.2
  have n16 := ew_written hm7 (r := 0) (p := (112 + 32 * t, 32)) rfl (o := 16)
    (by dsimp only; omega) w16 w24 l2.1 l2.2
  have n1 := ew_written hm7 (r := 1) (p := (112 + 16 * (n - 1 - 2 * t), 16)) rfl (o := 0)
    (by dsimp only; omega) v0 v8 l0.1 l0.2
  have n2 := ew_written hm7 (r := 2) (p := (112 + 16 * (n - 2 - 2 * t), 16)) rfl (o := 0)
    (by dsimp only; omega) u0 u8 l16.1 l16.2
  obtain ⟨r0, r1, r2, r3, r4⟩ := rv_two (L := L) (j := 2 * t) (by omega)
  rw [hL] at r0 r1 r2 r3 r4
  have hc' : Ch m0 L (2 * t + 2) st.data := fun i hi ↦ by
    rw [hL] at hi
    by_cases i0 : i = 2 * t
    · subst i0; rw [r0]; exact ew_congr (by dsimp only; omega) n0
    by_cases i1 : i = n - 1 - 2 * t
    · subst i1; rw [r1]; exact ew_congr (by dsimp only; omega) n1
    by_cases i2 : i = 2 * t + 1
    · subst i2; rw [r2]; exact ew_congr (by dsimp only; omega) n16
    by_cases i3 : i = n - 2 - 2 * t
    · subst i3; rw [r3]; exact ew_congr (by dsimp only; omega) n2
    rw [r4 i i0 i1 i2 i3]
    exact ew_keep hwf hm7 hin hL' (by omega) (fun p hp ↦ by
      rcases hmem p hp with rfl | rfl | rfl <;> dsimp only <;> omega) (hc i (by omega))
  -- The registers.
  have hr' : LR m0 n (t + 1) T st.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rg rcx7]
      show BinOp.apply .add .W64 (BitVec.ofNat 64 2) (reg d .rcx) = _
      rw [add_apply, hr.rcx, BitVec.add_comm, ← BitVec.ofNat_add]
      exact congrArg _ (by omega)
    · rw [rg r15_7]
      show BinOp.apply .add .W64 (BitVec.ofNat 64 32) (reg d .r15) = _
      rw [add_apply, hr.r15, BitVec.add_comm, off_add]
      exact off_congr (by omega)
    · rw [rg rsi7]
      show BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551584) (reg d .rsi) + _ = _
      rw [add_apply]
      have := hr.rsi
      unfold off at this ⊢
      bv_omega
    · rw [rg rax7]; exact hr.rax
    · rw [rg rdi7]; exact hr.rdi
    · rw [rg rdx7]; exact hr.rdx
  simp only [PcOk] at hpc7
  have hcnd : (SBool.not (.cmp .eq .W64 (.reg .rdx) (.bin .add .W64 (.lit 2) (.reg .rcx)))).eval
      (LE m0 d (swL n t)) = !decide (T = t + 1) := by
    show (!CmpOp.apply .eq .W64 (reg d .rdx) (BinOp.apply .add .W64 (BitVec.ofNat 64 2)
      (reg d .rcx))) = _
    rw [hr.rdx, hr.rcx, add_apply, ← BitVec.ofNat_add, eq_apply (by omega) (by omega)]
    by_cases e : T = t + 1
    · rw [decide_eq_true e, decide_eq_true (by omega)]
    · rw [decide_eq_false e, decide_eq_false (by omega)]
  rw [hcnd] at hpc7
  refine at_pc rfl (cont st.data st.pc H' hc' hr' (fun e ↦ ?_) (fun e ↦ ?_))
  · rw [decide_eq_true e] at hpc7
    exact hpc7.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b7_next))
  · rw [decide_eq_false e] at hpc7
    exact hpc7.trans (lbl_6 hp)

/-- **The loop**, from its iteration `t`: `2T` swaps. -/
theorem loop (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0) {L : List EW}
    (hL : L.length = nR heights) {T : Nat} (hT : 4 * T ≤ nR heights)
    (cont : ∀ d', Kp a s1 heights m0 c d' → Ch m0 L (2 * T) d' →
      LR m0 (nR heights) T T d' →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b8Offset)⟩) :
    ∀ u t, t + 1 + u = T → ∀ d, Kp a s1 heights m0 c d → Ch m0 L (2 * t) d →
      LR m0 (nR heights) t T d →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b7Offset)⟩ := by
  intro u
  induction u with
  | zero =>
    intro t e d H hc hr
    refine iter hp h hL (by omega) hT H hc hr fun d' pc H' hc' hr' p1 _ ↦ ?_
    rw [p1 (by omega)]
    have e' : t + 1 = T := by omega
    subst e'
    exact cont d' H' (by rwa [show 2 * (t + 1) = 2 * t + 2 by omega]) hr'
  | succ u ih =>
    intro t e d H hc hr
    refine iter hp h hL (by omega) hT H hc hr fun d' pc H' hc' hr' _ p2 ↦ ?_
    rw [p2 (by omega)]
    exact ih (t + 1) (by omega) d' H' (by rwa [show 2 * (t + 1) = 2 * t + 2 by omega]) hr'

/-- **The last swap** (`b9`): the pair `c`, `n - 1 - c`. -/
theorem one (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0) {L : List EW}
    (hL : L.length = nR heights) {j : Nat} (hj : 2 * j + 2 ≤ nR heights) {d : MachineData}
    (H : Kp a s1 heights m0 c d) (hc : Ch m0 L j d) (hrcx : reg d .rcx = BitVec.ofNat 64 j)
    (hrax : reg d .rax = off (fb m0) (112 + 16 * nR heights))
    (cont : ∀ d', Kp a s1 heights m0 c d' → Ch m0 L (j + 1) d' →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b10Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b9Offset)⟩ := by
  have hH := Pre.hts h
  have hn30 : nR heights ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  generalize hn : nR heights = n at hL hj hrax hn30
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hmem : ∀ p ∈ oneL n j, p = (112 + 16 * j, 16) ∨ p = (112 + 16 * (n - 1 - j), 16) :=
    fun p hp ↦ by simpa only [oneL, List.mem_cons, List.not_mem_nil, or_false] using hp
  have hLb : ∀ p ∈ oneL n j, 112 ≤ p.1 ∧ p.1 + p.2 ≤ 592 := fun p hp ↦ by
    rcases hmem p hp with rfl | rfl <;> dsimp only <;> omega
  have hL' : ∀ p ∈ oneL n j, p.1 + p.2 ≤ 744 := fun p hp ↦ by have := hLb p hp; omega
  have hwf : (LE m0 d (oneL n j)).WF :=
    loc_wf h H.bd.fr.kept (fun p hp ↦ by have := hLb p hp; omega) (by
      simp only [oneL, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
        implies_true]
      omega)
  have b0 : (LE m0 d (oneL n j)).base 0 = off (fb m0) (112 + 16 * j) :=
    LE_base (p := (112 + 16 * j, 16)) rfl
  have b1 : (LE m0 d (oneL n j)).base 1 = off (fb m0) (112 + 16 * (n - 1 - j)) :=
    LE_base (p := (112 + 16 * (n - 1 - j), 16)) rfl
  have hm : Match (LE m0 d (oneL n j)) oneS d := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial ⟨?_, ?_, trivial⟩
    · show BinOp.apply .add .W64 (reg d .rsp) (BinOp.apply .shl .W64 (reg d .rcx)
        (BitVec.ofNat 64 4)) = _
      rw [b0, hrcx, shl4, add_apply, f_m72]
      have := H.bd.fr.sp
      change reg d .rsp = _ at this
      rw [this, off_add (stackBelow m0 736) 40 (16 * j),
        show 112 + 16 * j = 40 + 16 * j + 72 by omega, ← off_add (fb m0) (40 + 16 * j) 72,
        BitVec.add_assoc,
        show BitVec.ofNat 64 72 + BitVec.ofNat 64 18446744073709551544 = 0#64 by decide,
        BitVec.add_zero]
    · show BinOp.apply .add .W64 (reg d .rax) (BinOp.apply .shl .W64
        (UnOp.apply .not .W64 (reg d .rcx)) (BitVec.ofNat 64 4)) = _
      rw [b1, ofInt_zero64, BitVec.add_zero, hrax, hrcx, add_apply]
      have := f_not j (by omega)
      generalize BinOp.apply .shl .W64 (UnOp.apply .not .W64 (BitVec.ofNat 64 j))
        (BitVec.ofNat 64 4) = X at this ⊢
      unfold off
      bv_omega
  refine exec_then (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf nofun hm
    fun st hm9 hpc9 ↦ ?_
  obtain ⟨hin9, w0, w8, v0, v8, rsp9, k9⟩ := ok_b9
  have hin : InLocs (oneL n j) (after b9 oneS) := fun w hw ↦ by
    rcases hin9 w hw with ⟨hr', hl⟩ | ⟨hr', hl⟩ <;> exact ⟨_, by rw [hr']; rfl, hl⟩
  have H' : Kp a s1 heights m0 c st.data :=
    Kp.loc h H hwf hm9 hin hLb rsp9 (keeps_reg hm9 k9 (by simp)) (keeps_reg hm9 k9 (by simp))
  have e0 := hc j (by omega)
  have e1 := hc (n - 1 - j) (by omega)
  have l0 := ew_ld (d := d) (L := oneL n j) (r := 0) (p := (112 + 16 * j, 16)) rfl (o := 0)
    (ew_congr (by dsimp only; omega) e0)
  have l1 := ew_ld (d := d) (L := oneL n j) (r := 1) (p := (112 + 16 * (n - 1 - j), 16)) rfl
    (o := 0) (ew_congr (by dsimp only; omega) e1)
  have n0 := ew_written hm9 (r := 0) (p := (112 + 16 * j, 16)) rfl (o := 0) (by dsimp only; omega)
    w0 w8 l1.1 l1.2
  have n1 := ew_written hm9 (r := 1) (p := (112 + 16 * (n - 1 - j), 16)) rfl (o := 0)
    (by dsimp only; omega) v0 v8 l0.1 l0.2
  obtain ⟨r0, r1, r2⟩ := rv_one (L := L) (j := j) (by omega)
  rw [hL] at r0 r1 r2
  have hc' : Ch m0 L (j + 1) st.data := fun i hi ↦ by
    rw [hL] at hi
    by_cases i0 : i = j
    · subst i0; rw [r0]; exact ew_congr (by dsimp only; omega) n0
    by_cases i1 : i = n - 1 - j
    · subst i1; rw [r1]; exact ew_congr (by dsimp only; omega) n1
    rw [r2 i i0 i1]
    exact ew_keep hwf hm9 hin hL' (by omega) (fun p hp ↦ by
      rcases hmem p hp with rfl | rfl <;> dsimp only <;> omega) (hc i (by omega))
  simp only [PcOk] at hpc9
  exact at_pc (hpc9.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b9_next))) (cont st.data H' hc')

end

end NativeRustcVmX64.Tables.TableSumcheck
