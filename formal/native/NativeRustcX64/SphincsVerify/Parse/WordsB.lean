module

public import NativeRustcX64.SphincsVerify.Parse.WordsA

/-!
# The parse, part 3: the layers' words and counters (`b4 .. b8`, x86-64)

A layer's word loop (`b4`, `b6`, `b8`: `rax_loop`) copies `4 N` words from `s0` to the frame
right after the raw signature's prefix `P` (EAX from `8 s0 + 1048`, 32 bytes a turn); a counter
block (`b5`, `b7`: `counter_block`) stores the next layer's counter word big-endian after it.
From `WS P1` at `b4` the raw signature is complete at `b9` (`words_spec`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

public section

variable (r : Run) [Host]

/-- **A turn of a layer's word loop**. -/
theorem rax_turn (hp : Placed code r.k) (hpre : r.Pre) {ds : List Directive} {jd jn : Nat}
    (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn) {lab : Label}
    (hlab : Labels.label lab = r.pc jd) (s0 L N : Nat) {S' : SState}
    (hx : exec ds (turnS .rax 32 24 (-((11404 + L - (8 * s0 + 1048) : Nat) : Int))) =
      some (S', .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 32) (.reg .rax))
        (.lit (8 * s0 + 1048 + 32 * N)))) lab))
    (hrax : S'.reg .rax = some (.bin .add .W64 (.lit 32) (.reg .rax)))
    (hc : copies S'.mem 1 0 0 0 (8 * 4) = true) (hwr : writesIn S' 1 0 (8 * 4) = true)
    (hk : keepsRegs wsRegs (turnS .rax 32 24 (-((11404 + L - (8 * s0 + 1048) : Nat) : Int))) S' =
      true)
    (hL0 : 8 * s0 + 1048 ≤ 11404 + L) (hs : s0 + 4 * N ≤ 977) (hd : 11404 + L + 32 * N ≤ 29352)
    {P : List UInt8} (hL : P.length = L) {j : Nat} (hj : j < N) {m : MachineData}
    (h : WS r (P ++ wb r.w s0 (4 * j)) m ∧
      Run.RegIs m .rax (BitVec.ofNat 64 (8 * s0 + 1048 + 32 * j))) :
    Eventually (step1 Host.exe) (fun st ↦
      (st.pc = r.pc jn ∧ WS r (P ++ wb r.w s0 (4 * N)) st.data) ∨
      (j + 1 < N ∧ st.pc = r.pc jd ∧ WS r (P ++ wb r.w s0 (4 * (j + 1))) st.data ∧
        Run.RegIs st.data .rax (BitVec.ofNat 64 (8 * s0 + 1048 + 32 * (j + 1)))))
      ⟨m, r.pc jd⟩ := by
  obtain ⟨hw, hax⟩ := h
  have hk' : ds.IsInfixAt Host.prog (r.k + jd) := hb.trans hp.1 (by rintro rfl; cases hx)
  have hwf := wf_in_frame r hpre hw.1.2.2.2 hw.1.2.2.1 (s := s0 + 4 * j) (k := 8 * 4)
    (a := 11404 + L + 32 * j) (n := 8 * 4) (by omega) (by decide) (by omega) (fun _ ↦ 0) 0
  have hbx : reg m .rbx = ctx r := hw.2.2.2.1
  have hax' : reg m .rax = BitVec.ofNat 64 (8 * s0 + 1048 + 32 * j) := hax
  have hm : Match (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * (s0 + 4 * j)), 8 * 4),
      (r.off (11404 + L + 32 * j), 8 * 4)] (fun _ ↦ 0) 0)
      (turnS .rax 32 24 (-((11404 + L - (8 * s0 + 1048) : Nat) : Int))) m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs]
        show reg m .rbx + reg m .rax = r.input + BitVec.ofNat 64 (8 * (s0 + 4 * j)) +
          BitVec.ofInt 64 ((24 : Nat) : Int)
        rw [hbx, hax']
        refine alias_pos 24 ?_
        bv_lin, by
        sym_simp
        simp only [Env.ofMachine_regs]
        show reg m .rsp + reg m .rax = r.off (11404 + L + 32 * j) +
          BitVec.ofInt 64 (-((11404 + L - (8 * s0 + 1048) : Nat) : Int))
        rw [show reg m .rsp = r.base from hw.1.1, hax']
        refine alias_neg _ ?_
        bv_lin, trivial⟩
  refine exec_then hk' hx hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  obtain ⟨hF', hnew, hout, hbx', hkey'⟩ := copy_turn r hpre hw (s := s0 + 4 * j) (q := 4)
    (d := 11404 + L + 32 * j) (by omega) (by omega) hm hm' hwf hc hwr hk
  have hraw : BytesAt st.data.dmem (r.off 11404) (P ++ wb r.w s0 (4 * (j + 1))) := by
    rw [show 4 * (j + 1) = 4 * j + 4 by omega, wb_add, ← List.append_assoc]
    refine BytesAt.append (fact_keep r hpre hw.2.2.1 hout
      (by rw [List.length_append, hL, length_wb]) (by left; omega) (by omega) (by omega)) ?_
    rw [List.length_append, hL, length_wb, off_add,
      show 11404 + (L + 8 * (4 * j)) = 11404 + L + 32 * j by omega]
    exact hnew
  have hmsg := fact_keep r hpre hw.2.1 hout (length_msg r) (by left; omega) (by decide) (by omega)
  have hv : Sym.eval (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * (s0 + 4 * j)), 8 * 4),
      (r.off (11404 + L + 32 * j), 8 * 4)] (fun _ ↦ 0) 0) (.bin .add .W64 (.lit 32) (.reg .rax)) =
      BitVec.ofNat 64 (8 * s0 + 1048 + 32 * (j + 1)) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    show BitVec.ofNat 64 32 + reg m .rax = _
    rw [hax']
    bv_lin
  have hax'' : Run.RegIs st.data .rax (BitVec.ofNat 64 (8 * s0 + 1048 + 32 * (j + 1))) :=
    (hm'.regs .rax _ hrax).trans hv
  obtain ⟨hne, heq⟩ := pc_cond hpc hv (by omega) (by omega)
  by_cases hj1 : j + 1 < N
  · rw [hlab] at hne
    exact .done _ (Or.inr ⟨hj1, hne (by omega), ⟨hF', hmsg, hraw, hbx', hkey'⟩, hax''⟩)
  · obtain rfl : N = j + 1 := by omega
    exact .done _ (Or.inl ⟨pc_next r (heq rfl) hjn, ⟨hF', hmsg, hraw, hbx', hkey'⟩⟩)

/-- **A layer's word loop**. -/
theorem rax_loop (hp : Placed code r.k) (hpre : r.Pre) {ds : List Directive} {jd jn : Nat}
    (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn) {lab : Label}
    (hlab : Labels.label lab = r.pc jd) (s0 L N : Nat) {S' : SState}
    (hx : exec ds (turnS .rax 32 24 (-((11404 + L - (8 * s0 + 1048) : Nat) : Int))) =
      some (S', .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 32) (.reg .rax))
        (.lit (8 * s0 + 1048 + 32 * N)))) lab))
    (hrax : S'.reg .rax = some (.bin .add .W64 (.lit 32) (.reg .rax)))
    (hc : copies S'.mem 1 0 0 0 (8 * 4) = true) (hwr : writesIn S' 1 0 (8 * 4) = true)
    (hk : keepsRegs wsRegs (turnS .rax 32 24 (-((11404 + L - (8 * s0 + 1048) : Nat) : Int))) S' =
      true)
    (hL0 : 8 * s0 + 1048 ≤ 11404 + L) (hs : s0 + 4 * N ≤ 977) (hd : 11404 + L + 32 * N ≤ 29352)
    (hN : 0 < N) {P : List UInt8} (hL : P.length = L) {m : MachineData}
    (h : WS r P m ∧ Run.RegIs m .rax (BitVec.ofNat 64 (8 * s0 + 1048))) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc jn ∧ WS r (P ++ wb r.w s0 (4 * N)) st.data)
      ⟨m, r.pc jd⟩ :=
  count_loop (σ := MachineState) (P := fun j st ↦ st.pc = r.pc jd ∧
      WS r (P ++ wb r.w s0 (4 * j)) st.data ∧
      Run.RegIs st.data .rax (BitVec.ofNat 64 (8 * s0 + 1048 + 32 * j))) N
    (fun j st hj ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      exact rax_turn r hp hpre hb hjn hlab s0 L N hx hrax hc hwr hk hL0 hs hd hL hj h)
    (j := 0) (s := ⟨m, r.pc jd⟩) hN
    ⟨rfl, by simpa [wb, Native.Keccak.wordsBytes] using h.1, h.2⟩

/-- **A counter block**: the input word `k`'s low 4 bytes big-endian after the prefix `P`, EAX
`a`. -/
theorem counter_block (hp : Placed code r.k) (hpre : r.Pre) {ds : List Directive} {jd jn : Nat}
    (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn) {S' : SState}
    (hx : exec ds ctxS = some (S', .fall)) (k L a : Nat) (hk : k < 977) (ho : 11404 + L + 4 ≤ 29352)
    (hsp : S'.reg .rsp = some (.ptr 0 0)) (hfw : Run.frameWrites S' = true)
    (hwr : writesIn S' 0 (11404 + L) (11404 + L + 4) = true)
    (hl : holdsLow S'.mem 0 (11404 + L) (.un .trunc .W32 (.un .bswap .W32 (.load 2 (8 * k) 4))) =
      true)
    (hkr : keepsRegs wsRegs ctxS S' = true) (hrax : S'.reg .rax = some (.lit a))
    {P : List UInt8} (hL : P.length = L) {m : MachineData} (h : WS r P m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc jn ∧
      WS r (P ++ be32 (r.w k).toUInt32) st.data ∧ Run.RegIs st.data .rax (BitVec.ofNat 64 a))
      ⟨m, r.pc jd⟩ := by
  have hk' : ds.IsInfixAt Host.prog (r.k + jd) := hb.trans hp.1 (by
    rintro rfl
    cases hx
    simp [holdsLow, findWrite, ctxS, fS3, init] at hl
    exact absurd (hl 0) (by decide))
  have hwf := wf3 r hpre h.1.2.2.2 h.1.2.2.1 (fun _ ↦ 0) 0
  have hm := ctxS_match r h.1 h.2.2.2.1 (fun _ ↦ 0) 0
  refine exec_then hk' hx hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  obtain ⟨hF', hc, hout⟩ := low4_counter r hpre h (k := k) (o := 11404 + L) hk ho hm' hwf hsp hfw
    hwr hl
  have hreg := keepsRegs_regs hm hm' hkr
  obtain ⟨hbx, hkey⟩ := wsRegs_keep hreg h
  refine .done _ ⟨pc_next r hpc hjn, ⟨hF', ?_, ?_, hbx, hkey⟩, (hm'.regs .rax _ hrax).trans rfl⟩
  · exact fact_keep r hpre h.2.1 hout (length_msg r) (by left; omega) (by decide) (by omega)
  · refine BytesAt.append (fact_keep r hpre h.2.2.1 hout hL (by left; omega) (by omega)
      (by omega)) ?_
    rw [hL, off_add]
    exact hc

end

end NativeRustcX64.SphincsVerifyProof.Parse
