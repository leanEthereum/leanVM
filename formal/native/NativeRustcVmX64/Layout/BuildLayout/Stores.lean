module

public import NativeRustcVmX64.Layout.BuildLayout.Checks
public import NativeRustcVmX64.Code.Vm.BitLength.Names

/-!
# `build_layout` on x86-64: the sizes, rows and heights (`b9` to `b14`)

Region 1 is the layout's first `120` bytes (R13). `b9` stores the log-sizes and keeps row counts
`3` to `5` and the bytecode's log-size in the frame (`frW`); `b9` to `b14` each call `bit_length`
on a row count less one (saturating) for a height, and `b10` to `b14` store the previous row count
and height. `SL m0 d n`: the first `n` words of `wsK` stored.
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BuildLayout NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

/-- The words `b9` to `b15` store, for the entry `m0`. -/
abbrev wsK0 (m0 : MachineData) : List (Nat × UInt64) :=
  wsK (lmN m0) (bitLength (nN m0) - 5) (rowsOf m0)

/-- The frame's words `b9` stores. -/
abbrev frW (m0 : MachineData) : List (Nat × UInt64) :=
  [(16, rowW m0 3), (24, rowW m0 4), (32, rowW m0 5), (40, (bitLength (nN m0) - 5).toUInt64)]

/-- A block's environment: the frame, the layout's first `120` bytes. -/
abbrev envL (m0 d : MachineData) (ret : BitVec 64) : Env :=
  frameEnv m0 d 1360 [(ll m0, 120)] (fun _ ↦ 0) ret

section
variable [Labels]

/-- **Storing**: the first `n` words stored, the frame's words kept. -/
structure SL (m0 d : MachineData) (n : Nat) : Prop where
  b : B m0 8 d
  r13 : reg d .r13 = ll m0
  rbx : reg d .rbx = reg m0 .rsi
  ws : Ws d.dmem (ll m0) ((wsK0 m0).take n)
  fr : Ws d.dmem (fb m0) (frW m0)
  pow2 : Pow2 (nN m0)
  chk : Chk m0

end

end

public section

variable {m0 : MachineData} {bc : Array UInt64}

theorem wsK_le {lm lb : Nat} {rows : Array Nat} : ∀ p ∈ wsK lm lb rows, p.1 + 8 ≤ 120 := by
  simp

theorem frW_le : ∀ p ∈ frW m0, p.1 + 8 ≤ 1368 := by simp
theorem frW_ge : ∀ p ∈ frW m0, 16 ≤ p.1 := by simp

theorem Ws.nil {d : Mem 64} {b : BitVec 64} : Ws d b [] := nofun

theorem Ws.take2 {d : Mem 64} {b : BitVec 64} {l : List (Nat × UInt64)} {n : Nat}
    {a c : Nat × UInt64} (h : Ws d b (l.take n)) (ha : l[n]? = some a) (hc : l[n + 1]? = some c)
    (hwa : WordAt d (off b a.1) a.2) (hwc : WordAt d (off b c.1) c.2) : Ws d b (l.take (n + 2)) := by
  intro p hp
  rw [show n + 2 = (n + 1) + 1 from rfl, List.take_add_one, List.take_add_one, ha, hc] at hp
  simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hp
  rcases hp with (hp | rfl) | rfl
  · exact h p hp
  · exact hwa
  · exact hwc

theorem row_toNat {t : Nat} (ht : t < 6) : ((rowsOf m0).getD t 0).toUInt64.toNat = (rowW m0 t).toNat := by
  rw [rows_getD m0 ht]; exact toNat_toUInt64 (UInt64.toNat_lt _)

theorem hgt_toNat {t : Nat} (ht : t < 6) :
    (hgt (rowsOf m0) t).toNat = bitLength ((rowW m0 t).toNat - 1) := by
  show (bitLength ((rowsOf m0).getD t 0 - 1)).toUInt64.toNat = _
  rw [rows_getD m0 ht]
  exact toNat_toUInt64 (by
    have := bitLength_le (k := 64) (n := (rowW m0 t).toNat - 1) (by have := UInt64.toNat_lt (rowW m0 t); omega)
    omega)

section
variable [Labels]

theorem Facts.lay0 (hF : Facts bc m0) :
    NativeRustcVm.Mapped m0.dmem (ll m0) 120 ∧ NativeRustcVm.NoWrap (ll m0) 120 :=
  ⟨fun i hi ↦ hF.lr.1 i (by rw [layoutBytes_eq]; omega),
    by have := hF.lnw; unfold NativeRustcVm.NoWrap; omega⟩

theorem wfL (hF : Facts bc m0) {o : Nat} {d : MachineData} (hb : B m0 o d) {ret : BitVec 64} :
    (envL m0 d ret).WF :=
  fr_wf1 hb hF.stack (by decide) hF.lay0.1 hF.lay0.2 (hF.lay_apart (by decide))

theorem matchL {d : MachineData} {ret : BitVec 64} (hb : B m0 8 d) (h13 : reg d .r13 = ll m0) :
    Match (envL m0 d ret) layS d :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, by
    show reg d .r13 = ll m0 + BitVec.ofInt 64 0
    rw [ofInt_zero64, BitVec.add_zero, h13], trivial⟩ trivial trivial trivial

omit [Labels] in
theorem restL : ∀ x ∈ [(ll m0, 120)], ∀ q, NativeRustcVm.InRange x.1 x.2 q →
    R m0 q ∨ NativeRustcVm.InRange (stackBelow m0 7824) 7824 q := by
  intro x hx q hq
  rw [List.mem_singleton] at hx
  subst hx
  exact .inl (inRange_mono' hq (show 120 ≤ layoutBytes by decide))

omit [Labels] in
theorem writesIn_of {Sy : SState} {o : Nat} (h : MidOk 1360 o slots Sy = true) : writesIn Sy = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.2

/-- The register `ptr 1 0` is the layout. -/
theorem r13_of {d d' : MachineData} {ret : BitVec 64} {Sy : SState} (hm : Match (envL m0 d ret) Sy d')
    (h : Sy.reg .r13 = some (.ptr 1 0)) : reg d' .r13 = ll m0 :=
  (hm.regs .r13 _ h).trans (by show _ + BitVec.ofInt 64 0 = _; rw [ofInt_zero64, BitVec.add_zero]; rfl)

omit [Labels] in
/-- A frame word, loaded. -/
theorem load_fr {d : MachineData} {ret : BitVec 64} {o : Nat} {v : UInt64}
    (h : WordAt d.dmem (off (fb m0) o) v) : (envL m0 d ret).load 0 o 8 = v.toBitVec := by
  rw [Arrays.load8_eq]
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h)

end

variable [Host] {k : Nat}

/-- **A store-and-height block** (`b10` to `b14`): two words stored, `bit_length` called. -/
theorem stepL (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) (hF : Facts bc m0)
    {ds : List Directive} {kk n o1 o2 : Nat} {Sy1 : SState} {v1 : Sym} {u1 u2 : UInt64}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds layS = some (Sy1, .call NativeRustcVmX64.Vm.BitLength.entryLabel))
    (hok : MidOk 1360 0 slots Sy1 = true) (h0 : ∀ w ∈ Sy1.mem, w.r = 0 → w.off + w.n ≤ 8)
    (hmiss : Misses 1 (((wsK0 m0).take n).map (·.1)) Sy1 = true)
    (hw1 : W1 Sy1 o1 v1) (hw2 : W1 Sy1 o2 (.reg .rax)) (h13 : Sy1.reg .r13 = some (.ptr 1 0))
    (hbx : Sy1.reg .rbx = some (.reg .rbx))
    (hn1 : (wsK0 m0)[n]? = some (o1, u1)) (hn2 : (wsK0 m0)[n + 1]? = some (o2, u2))
    {st : MachineState} (hpc : st.pc = Host.addrOf kk) (hs : SL m0 st.data n)
    (hv1 : (v1.eval (envL m0 st.data (Host.addrOf (kk + ds.length)).toBitVec)).toNat = u1.toNat)
    (hv2 : (reg st.data .rax).toNat = u2.toNat) {Q : MachineState → Prop}
    (cont : ∀ st1 st' : MachineState,
      Match (envL m0 st.data (Host.addrOf (kk + ds.length)).toBitVec) Sy1 st1.data →
      st'.pc = Host.addrOf (kk + ds.length) → SL m0 st'.data (n + 2) →
      (∀ r, calleeSaved r = true → reg st'.data r = reg st1.data r) →
      (reg st'.data .rax).toNat = bitLength (reg st1.data .rdi).toNat →
      Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hb := hs.b
  have hwf := wfL (ret := (Host.addrOf (kk + ds.length)).toBitVec) hF hb
  refine exec_at hk hx hwf (fun _ _ ↦ rfl) hpc (matchL hb hs.r13) fun st1 hm1 hpc1 ↦ ?_
  have hb1 : B m0 0 st1.data := hb.of_block hF.stack (by decide) hwf hm1 hok slots_le restL
  have hin := writesIn_of hok
  have hl1 : o1 + 8 ≤ 120 := wsK_le _ (List.mem_of_getElem? hn1)
  have hl2 : o2 + 8 ≤ 120 := wsK_le _ (List.mem_of_getElem? hn2)
  have hws1 : Ws st1.data.dmem (ll m0) ((wsK0 m0).take (n + 2)) :=
    Ws.take2 (Ws.keep hwf hm1 hin (r := 1) rfl
      (fun p hp ↦ wsK_le p (List.mem_of_mem_take hp)) (misses_of hmiss rfl) hs.ws) hn1 hn2
      (w_write hm1 (r := 1) rfl hl1 hw1 hv1) (w_write hm1 (r := 1) rfl hl2 hw2 (by exact hv2))
  have hfr1 : Ws st1.data.dmem (fb m0) (frW m0) :=
    Ws.keep hwf hm1 hin (r := 0) rfl frW_le (below_of (fun w hw hr ↦ by
      have := h0 w hw hr; omega) frW_ge) hs.fr
  refine callBL hbl hF hpc1 hb1 fun st' hpc' hb' hd' hsv' hax' ↦
    cont st1 st' hm1 hpc' ⟨hb', ?_, ?_, hws1.of_eq hd', hfr1.of_eq hd', hs.pow2, hs.chk⟩ hsv' hax'
  · rw [hsv' .r13 rfl]; exact r13_of hm1 h13
  · rw [hsv' .rbx rfl, show reg st1.data .rbx = _ from hm1.regs .rbx _ hbx]; exact hs.rbx

/-- The state after a height's `bit_length`: `t` the table. -/
abbrev Ht (m0 d : MachineData) (n t : Nat) : Prop :=
  SL m0 d n ∧ (reg d .rax).toNat = bitLength ((rowW m0 t).toNat - 1)

/-- **`b9`**: the log-sizes stored, rows `3` to `5` kept in the frame, `bit_length(r0 - 1)`. -/
theorem s9 (hp : Placed code k) (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hF : Facts bc m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b9Offset)) (h9 : St9 m0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b10Offset) ∧ Ht m0 s.data 2 0 ∧
      reg s.data .r12 = (rowW m0 0).toBitVec ∧ reg s.data .rbp = (rowW m0 1).toBitVec ∧
      reg s.data .r15 = (rowW m0 2).toBitVec) st := by
  have hb := h9.b
  have hwf := wfL (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b9Offset + b9.length)).toBitVec) hF hb
  obtain ⟨hok, h0, w0, w8, w16, w24, w32, w40, hdi, h13, hK⟩ := ok_b9
  refine exec_at (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b9 hwf (fun _ _ ↦ rfl) hpc
    (matchL hb h9.r13) fun st1 hm1 hpc1 ↦ ?_
  have hb1 : B m0 0 st1.data := hb.of_block hF.stack (by decide) hwf hm1 hok slots_le restL
  have hlm : lmN m0 < 2 ^ 64 := (reg m0 .rsi).isLt
  have hlb : bitLength (nN m0) - 5 < 2 ^ 64 := by have := h9.chk.2.2.2.2; omega
  have hws1 : Ws st1.data.dmem (ll m0) ((wsK0 m0).take 2) :=
    Ws.take2 (n := 0) Ws.nil rfl rfl
      (w_write hm1 (r := 1) rfl (by decide) w0 (by
        show (reg st.data .rbx).toNat = _; rw [h9.rbx, toNat_toUInt64 hlm]))
      (w_write hm1 (r := 1) rfl (by decide) w8 (by
        show (reg st.data .rax).toNat = _; rw [h9.rax, toNat_toUInt64 hlb]))
  have hfr1 : Ws st1.data.dmem (fb m0) (frW m0) := by
    refine Ws.cons ?_ (Ws.cons ?_ (Ws.cons ?_ (Ws.cons ?_ Ws.nil)))
    · exact w_write hm1 (r := 0) rfl (by decide) w16 (by show (reg st.data .r8).toNat = _; rw [h9.r8]; rfl)
    · exact w_write hm1 (r := 0) rfl (by decide) w24 (by show (reg st.data .rdi).toNat = _; rw [h9.rdi]; rfl)
    · exact w_write hm1 (r := 0) rfl (by decide) w32 (by show (reg st.data .rsi).toNat = _; rw [h9.rsi]; rfl)
    · exact w_write hm1 (r := 0) rfl (by decide) w40 (by
        show (reg st.data .rax).toNat = _; rw [h9.rax, toNat_toUInt64 hlb])
  have hz : ((Sym.lit 0).eval (envL m0 st.data (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b9Offset + b9.length)).toBitVec)).toNat = 0 :=
    lit_eval _ (by decide)
  have hrdi : (reg st1.data .rdi).toNat = (rowW m0 0).toNat - 1 := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi, sat_eval _ _ _ hz]
    show (reg st.data .r12).toNat - 1 = _
    rw [h9.r12]; rfl
  have k1 := fun r (hr : r ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15]) ↦ kreg hm1 hK hr
  refine callBL hbl hF hpc1 hb1 fun st' hpc' hb' hd' hsv' hax' ↦ .done _ ⟨hpc'.trans rfl,
    ⟨⟨hb', ?_, ?_, hws1.of_eq hd', hfr1.of_eq hd', h9.pow2, h9.chk⟩, by rw [hax', hrdi]⟩, ?_, ?_, ?_⟩
  · rw [hsv' .r13 rfl]; exact r13_of hm1 h13
  · rw [hsv' .rbx rfl, k1 .rbx (by simp)]; exact h9.rbx
  · rw [hsv' .r12 rfl, k1 .r12 (by simp)]; exact h9.r12
  · rw [hsv' .rbp rfl, k1 .rbp (by simp)]; exact h9.rbp
  · rw [hsv' .r15 rfl, k1 .r15 (by simp)]; exact h9.r15

/-- **`b10`**: row `0` and its height stored, `bit_length(r1 - 1)`. -/
theorem s10 (hp : Placed code k) (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hF : Facts bc m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b10Offset))
    (hs : Ht m0 st.data 2 0) (h12 : reg st.data .r12 = (rowW m0 0).toBitVec)
    (hbp : reg st.data .rbp = (rowW m0 1).toBitVec) (h15 : reg st.data .r15 = (rowW m0 2).toBitVec) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b11Offset) ∧ Ht m0 s.data 4 1 ∧
      reg s.data .rbp = (rowW m0 1).toBitVec ∧ reg s.data .r15 = (rowW m0 2).toBitVec) st := by
  obtain ⟨hok, h0, hmiss, w1, w2, hdi, h13, hK⟩ := ok_b10
  refine stepL hbl hF (n := 2) (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b10 hok h0
    hmiss w1 w2 h13 (keeps_reg_some hK (by simp)) rfl rfl hpc hs.1
    (by show (reg st.data .r12).toNat = _; rw [h12, row_toNat (by decide)]; rfl)
    (by rw [hs.2, hgt_toNat (by decide)]) fun st1 st' hm1 hpc' hs' hsv' hax' ↦ ?_
  have k1 := fun r (hr : r ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15]) ↦ kreg hm1 hK hr
  have hz : ((Sym.lit 0).eval (envL m0 st.data (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b10Offset + b10.length)).toBitVec)).toNat = 0 :=
    lit_eval _ (by decide)
  refine .done _ ⟨hpc'.trans rfl, ⟨hs', ?_⟩, ?_, ?_⟩
  · rw [hax', show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi, sat_eval _ _ _ hz]
    show bitLength ((reg st.data .rbp).toNat - 1) = _
    rw [hbp]; rfl
  · rw [hsv' .rbp rfl, k1 .rbp (by simp)]; exact hbp
  · rw [hsv' .r15 rfl, k1 .r15 (by simp)]; exact h15

/-- **`b11`**: row `1` and its height stored, `bit_length(r2 - 1)`. -/
theorem s11 (hp : Placed code k) (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hF : Facts bc m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b11Offset))
    (hs : Ht m0 st.data 4 1) (hbp : reg st.data .rbp = (rowW m0 1).toBitVec)
    (h15 : reg st.data .r15 = (rowW m0 2).toBitVec) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b12Offset) ∧ Ht m0 s.data 6 2 ∧
      reg s.data .r15 = (rowW m0 2).toBitVec ∧ reg s.data .r12 = 0#64) st := by
  obtain ⟨hok, h0, hmiss, w1, w2, hdi, h12, h13, hK⟩ := ok_b11
  refine stepL hbl hF (n := 4) (b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b11 hok h0
    hmiss w1 w2 h13 (keeps_reg_some hK (by simp)) rfl rfl hpc hs.1
    (by show (reg st.data .rbp).toNat = _; rw [hbp, row_toNat (by decide)]; rfl)
    (by rw [hs.2, hgt_toNat (by decide)]) fun st1 st' hm1 hpc' hs' hsv' hax' ↦ ?_
  have k1 := fun r (hr : r ∈ [Reg64.rbx, .rbp, .r14, .r15]) ↦ kreg hm1 hK hr
  have hz : ((Sym.lit 0).eval (envL m0 st.data (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b11Offset + b11.length)).toBitVec)).toNat = 0 :=
    lit_eval _ (by decide)
  refine .done _ ⟨hpc'.trans rfl, ⟨hs', ?_⟩, ?_, ?_⟩
  · rw [hax', show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi, sat_eval _ _ _ hz]
    show bitLength ((reg st.data .r15).toNat - 1) = _
    rw [h15]; rfl
  · rw [hsv' .r15 rfl, k1 .r15 (by simp)]; exact h15
  · rw [hsv' .r12 rfl, show reg st1.data .r12 = _ from hm1.regs .r12 _ h12]; rfl

/-- **`b12` to `b14`**: row `t - 1` (R15) and its height stored, row `t` loaded from the frame,
`bit_length(r_t - 1)`. -/
theorem sF (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) (hF : Facts bc m0)
    {ds : List Directive} {kk n o1 o2 fo t : Nat} {Sy1 : SState} {u1 u2 : UInt64}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds layS = some (Sy1, .call NativeRustcVmX64.Vm.BitLength.entryLabel))
    (hok : MidOk 1360 0 slots Sy1 = true) (h0 : ∀ w ∈ Sy1.mem, w.r = 0 → w.off + w.n ≤ 8)
    (hmiss : Misses 1 (((wsK0 m0).take n).map (·.1)) Sy1 = true)
    (hw1 : W1 Sy1 o1 (.reg .r15)) (hw2 : W1 Sy1 o2 (.reg .rax))
    (hdi : Sy1.reg .rdi = some (sat (.load 0 fo 8) (.reg .r12)))
    (h15' : Sy1.reg .r15 = some (.load 0 fo 8)) (h13 : Sy1.reg .r13 = some (.ptr 1 0))
    (hbx : Sy1.reg .rbx = some (.reg .rbx))
    (hn1 : (wsK0 m0)[n]? = some (o1, u1)) (hn2 : (wsK0 m0)[n + 1]? = some (o2, u2))
    (hfo : (fo, rowW m0 t) ∈ frW m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf kk) (hs : SL m0 st.data n)
    (hv1 : (reg st.data .r15).toNat = u1.toNat) (hv2 : (reg st.data .rax).toNat = u2.toNat)
    (h12 : reg st.data .r12 = 0#64) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (kk + ds.length) ∧ Ht m0 s.data (n + 2) t ∧
      reg s.data .r15 = (rowW m0 t).toBitVec ∧
      (∀ r, calleeSaved r = true → ∀ v, Sy1.reg r = some v →
        reg s.data r = v.eval (envL m0 st.data (Host.addrOf (kk + ds.length)).toBitVec))) st := by
  refine stepL hbl hF hk hx hok h0 hmiss hw1 hw2 h13 hbx hn1 hn2 hpc hs (by exact hv1) hv2
    fun st1 st' hm1 hpc' hs' hsv' hax' ↦ ?_
  have hl : (envL m0 st.data (Host.addrOf (kk + ds.length)).toBitVec).load 0 fo 8 =
      (rowW m0 t).toBitVec := load_fr (hs.fr.get hfo)
  have hz : ((Sym.reg .r12).eval (envL m0 st.data (Host.addrOf (kk + ds.length)).toBitVec)).toNat = 0 := by
    show (reg st.data .r12).toNat = 0; rw [h12]; rfl
  refine .done _ ⟨hpc', ⟨hs', ?_⟩, ?_, fun r hr v h ↦ ?_⟩
  · rw [hax', show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi, sat_eval _ _ _ hz]
    show bitLength (((envL m0 st.data _).load 0 fo 8).toNat - 1) = _
    rw [hl]; rfl
  · rw [hsv' .r15 rfl, show reg st1.data .r15 = _ from hm1.regs .r15 _ h15']; exact hl
  · rw [hsv' r hr]; exact hm1.regs r _ h

/-- **`b12`**. -/
theorem s12 (hp : Placed code k) (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hF : Facts bc m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b12Offset))
    (hs : Ht m0 st.data 6 2) (h15 : reg st.data .r15 = (rowW m0 2).toBitVec)
    (h12 : reg st.data .r12 = 0#64) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b13Offset) ∧ Ht m0 s.data 8 3 ∧
      reg s.data .r15 = (rowW m0 3).toBitVec ∧ reg s.data .r12 = 0#64) st := by
  obtain ⟨hok, h0, hmiss, w1, w2, hdi, h15', h12', h13, hK⟩ := ok_b12
  refine (sF hbl hF (n := 6) (t := 3) (b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b12 hok
    h0 hmiss w1 w2 hdi h15' h13 (keeps_reg_some hK (by simp)) rfl rfl (by simp) hpc hs.1
    (by rw [h15, row_toNat (by decide)]; rfl) (by rw [hs.2, hgt_toNat (by decide)]) h12).mono
    fun s ⟨h1, h2, h3, h4⟩ ↦ ⟨h1.trans rfl, h2, h3, (h4 .r12 rfl _ h12').trans rfl⟩

/-- **`b13`**. -/
theorem s13 (hp : Placed code k) (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hF : Facts bc m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b13Offset))
    (hs : Ht m0 st.data 8 3) (h15 : reg st.data .r15 = (rowW m0 3).toBitVec)
    (h12 : reg st.data .r12 = 0#64) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b14Offset) ∧ Ht m0 s.data 10 4 ∧
      reg s.data .r15 = (rowW m0 4).toBitVec ∧ reg s.data .r12 = 0#64) st := by
  obtain ⟨hok, h0, hmiss, w1, w2, hdi, h15', h13, hK⟩ := ok_b13
  refine (sF hbl hF (n := 8) (t := 4) (b13_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b13 hok
    h0 hmiss w1 w2 hdi h15' h13 (keeps_reg_some hK (by simp)) rfl rfl (by simp) hpc hs.1
    (by rw [h15, row_toNat (by decide)]; rfl) (by rw [hs.2, hgt_toNat (by decide)]) h12).mono
    fun s ⟨h1, h2, h3, h4⟩ ↦ ⟨h1.trans rfl, h2, h3,
      (h4 .r12 rfl _ (keeps_reg_some hK (by simp))).trans h12⟩

/-- **`b14`**. -/
theorem s14 (hp : Placed code k) (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hF : Facts bc m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b14Offset))
    (hs : Ht m0 st.data 10 4) (h15 : reg st.data .r15 = (rowW m0 4).toBitVec)
    (h12 : reg st.data .r12 = 0#64) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b15Offset) ∧ Ht m0 s.data 12 5 ∧
      reg s.data .r15 = (rowW m0 5).toBitVec) st := by
  obtain ⟨hok, h0, hmiss, w1, w2, hdi, h15', h13, hK⟩ := ok_b14
  refine (sF hbl hF (n := 10) (t := 5) (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b14 hok
    h0 hmiss w1 w2 hdi h15' h13 (keeps_reg_some hK (by simp)) rfl rfl (by simp) hpc hs.1
    (by rw [h15, row_toNat (by decide)]; rfl) (by rw [hs.2, hgt_toNat (by decide)]) h12).mono
    fun s ⟨h1, h2, h3, _⟩ ↦ ⟨h1.trans rfl, h2, h3⟩

/-- **`b9` to `b14`**. -/
theorem stores (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) (hF : Facts bc m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b9Offset)) (h9 : St9 m0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b15Offset) ∧ Ht m0 s.data 12 5 ∧
      reg s.data .r15 = (rowW m0 5).toBitVec) st :=
  (s9 hp hbl hF hpc h9).bind fun _ ⟨h1, h2, h3, h4, h5⟩ ↦
    (s10 hp hbl hF h1 h2 h3 h4 h5).bind fun _ ⟨h1, h2, h3, h4⟩ ↦
      (s11 hp hbl hF h1 h2 h3 h4).bind fun _ ⟨h1, h2, h3, h4⟩ ↦
        (s12 hp hbl hF h1 h2 h3 h4).bind fun _ ⟨h1, h2, h3, h4⟩ ↦
          (s13 hp hbl hF h1 h2 h3 h4).bind fun _ ⟨h1, h2, h3, h4⟩ ↦
            s14 hp hbl hF h1 h2 h3 h4

end

end NativeRustcVmX64.Layout.BuildLayout
