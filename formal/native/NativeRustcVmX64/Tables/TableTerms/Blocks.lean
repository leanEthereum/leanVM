module

public import NativeRustcVmX64.Tables.TableTerms.Lemmas

/-!
# `table_terms`: the blocks' environments (x86-64)

A block's environment `E m0 d rest ret`: region `0` the frame and the return address, then `rest`.
The regions of table `i` (its `TABLES` entry, its evaluations' entry, its forms, its weight, its
height, the stack arguments, `out`), each mapped, not wrapping, apart from the frame and each other
(`wf_*`); the start states' `Match` (`match_body`); the frame's words a block keeps (`missR`,
`keepR`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck

@[expose] public section

/-- A block's environment: the frame, then `rest`. -/
abbrev E (m0 d : MachineData) (rest : List (BitVec 64 × Nat)) (ret : BitVec 64) : Env :=
  frameEnv m0 d 272 rest (fun _ ↦ 0) ret

end

public section

theorem missR_spec {Sy : SState} {lo hi : Nat} (h : missR Sy lo hi = true) :
    ∀ w ∈ Sy.mem, w.r = 0 → w.off + w.n ≤ lo ∨ hi ≤ w.off := by
  intro w hw hr
  have := List.all_eq_true.mp h w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

theorem pairwise4 {α : Type} {R : α → α → Prop} {w x y z : α} (h1 : R w x) (h2 : R w y)
    (h3 : R w z) (h4 : R x y) (h5 : R x z) (h6 : R y z) : [w, x, y, z].Pairwise R :=
  .cons (fun b hb ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> assumption) (pairwise3 h4 h5 h6)

theorem apart_sub {x b : BitVec 64} {n nb o k : Nat} (hnw : NativeRustcVm.NoWrap x n)
    (hA : NativeRustcVm.Apart x n b nb) (hk : o + k ≤ n) :
    NativeRustcVm.Apart (x + BitVec.ofNat 64 o) k b nb := by
  have h1 : x.toNat + n ≤ 2 ^ 64 := hnw
  have h2 : x.toNat + n ≤ b.toNat ∨ b.toNat + nb ≤ x.toNat := hA
  have e := NativeRustcVm.toNat_add_ofNat_le (a := x) (i := o) (by omega)
  show (x + BitVec.ofNat 64 o).toNat + k ≤ b.toNat ∨ b.toNat + nb ≤ (x + BitVec.ofNat 64 o).toNat
  omega

theorem rin_sub {m : MachineData} {x : BitVec 64} {n N o k : Nat} {ws : List NativeRustcVm.Region}
    (h : ReadIn m x n N ws) (hk : o + k ≤ n) : ReadIn m (x + BitVec.ofNat 64 o) k N ws := by
  obtain ⟨⟨hm, hnw⟩, hst, hws⟩ := h
  have ap : ∀ {b : BitVec 64} {nb : Nat}, NativeRustcVm.Apart x n b nb →
      NativeRustcVm.Apart (x + BitVec.ofNat 64 o) k b nb := fun hA ↦ apart_sub hnw hA hk
  exact ⟨⟨NativeRustcVm.Mapped.sub hm hk, NativeRustcVm.NoWrap.sub hnw hk⟩, ap hst,
    fun w hw ↦ ap (hws w hw)⟩


variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- A region apart from the stack is apart from the frame. -/
theorem frame_ap (h : TableTermsPre a s heights forms m0) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8)) :
    NativeRustcVm.Apart (stackBelow m0 272) (272 + 8) x n :=
  Apart.symm' (apart_frame hx (spN h) (by rw [N_eq]; omega))

/-- The stack arguments are apart from the frame. -/
theorem frame_args (h : TableTermsPre a s heights forms m0) :
    NativeRustcVm.Apart (stackBelow m0 272) (272 + 8) (argA m0) 32 := by
  unfold NativeRustcVm.Apart
  rw [argA_toNat h, fb_toNat h]
  have := spN h
  rw [N_eq] at this
  omega

theorem stack_ap_args (h : TableTermsPre a s heights forms m0) :
    NativeRustcVm.Apart (argA m0) 32 (stackBelow m0 N) (N + 8) := by
  unfold NativeRustcVm.Apart
  rw [argA_toNat h, stk h]
  have := spN h
  omega

omit [Labels] in
/-- A region from an input, as `frame_wf'` takes it. -/
theorem rest_of_rin {x : BitVec 64} {n : Nat} (hr : ReadIn m0 x n N (wsL m0)) :
    NativeRustcVm.Mapped m0.dmem x n ∧ NativeRustcVm.NoWrap x n := hr.1

theorem args_ok (h : TableTermsPre a s heights forms m0) :
    NativeRustcVm.Mapped m0.dmem (argA m0) 32 ∧ NativeRustcVm.NoWrap (argA m0) 32 :=
  ⟨(Pre.args h).1, args_noWrap h⟩

/-! ## The regions of table `i` -/

/-- `TABLES`, as an input. -/
theorem tables_ok (h : TableTermsPre a s heights forms m0) :
    NativeRustcVm.Mapped m0.dmem T 240 ∧ NativeRustcVm.NoWrap T 240 ∧
      NativeRustcVm.Apart T 240 (stackBelow m0 N) (N + 8) := by
  have hb := RodataAt.bytesAt (Pre.tables h) .tables
  have hnw := RodataAt.noWrap (Pre.tables h) .tables
  have hap := RodataAt.apart (Pre.tables h) .tables
  rw [tables_length] at hnw hap
  exact ⟨fun i hi ↦ hb.mapped i (by rw [tables_length]; exact hi), hnw, hap⟩

theorem tab_ok (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    NativeRustcVm.Mapped m0.dmem (T + BitVec.ofNat 64 (40 * i)) 40 ∧
      NativeRustcVm.NoWrap (T + BitVec.ofNat 64 (40 * i)) 40 ∧
      NativeRustcVm.Apart (T + BitVec.ofNat 64 (40 * i)) 40 (stackBelow m0 N) (N + 8) := by
  obtain ⟨hm, hnw, hap⟩ := tables_ok h
  exact ⟨NativeRustcVm.Mapped.sub hm (by omega), NativeRustcVm.NoWrap.sub hnw (by omega),
    apart_sub hnw hap (by omega)⟩

theorem wf_tab (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] ret).WF := by
  obtain ⟨hm, hnw, hap⟩ := tab_ok h hi
  refine frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (frame_ap h hap))
  rw [List.mem_singleton] at hx; subst hx; exact ⟨hm, hnw⟩

theorem wf_ev (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} : (E m0 d [(evi m0 i, 1968)] ret).WF := by
  have e := evi_out h hi
  refine frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (frame_ap h e.2.2.2.2.1))
  rw [List.mem_singleton] at hx; subst hx; exact ⟨e.1, e.2.1⟩

theorem form_rin (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    ReadIn m0 (fA m0 + BitVec.ofNat 64 (17784 * i)) 17784 N (wsL m0) :=
  rin_sub (Pre.fs h) (by
    show 17784 * i + 17784 ≤ formBufBytes * (3 * nTables)
    unfold formBufBytes termBytes formCap nTables; omega)

theorem wf_form (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (E m0 d [(fA m0 + BitVec.ofNat 64 (17784 * i), 17784)] ret).WF := by
  have e := form_rin h hi
  refine frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (frame_ap h e.2.1))
  rw [List.mem_singleton] at hx; subst hx; exact e.1

theorem w_rin (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    ReadIn m0 (wA m0 + BitVec.ofNat 64 (16 * i)) 16 N (wsL m0) :=
  rin_sub (Pre.ws h) (by omega)

theorem wf_w (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (E m0 d [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ret).WF := by
  have e := w_rin h hi
  refine frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (fun x hx ↦ ?_)
    (pairwise3 (frame_args h) (frame_ap h e.2.1) (Apart.symm' (in_args e)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact args_ok h
  · exact e.1

theorem h_rin (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    ReadIn m0 (hA m0 + BitVec.ofNat 64 (8 * i)) 8 N (wsL m0) :=
  rin_sub (Pre.hs h) (by omega)

theorem wf_pt (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (E m0 d [(argA m0, 32), (evi m0 i, 8), (hA m0 + BitVec.ofNat 64 (8 * i), 8)] ret).WF := by
  have e := evi_out h hi
  have eh := h_rin h hi
  have hev8 : NativeRustcVm.NoWrap (evi m0 i) 8 := NativeRustcVm.NoWrap.mono e.2.1 (by omega)
  have hevst : NativeRustcVm.Apart (evi m0 i) 8 (stackBelow m0 N) (N + 8) :=
    NativeRustcVm.Apart.mono e.2.2.2.2.1 le_rfl (by omega) le_rfl le_rfl
  have hevarg : NativeRustcVm.Apart (evi m0 i) 8 (argA m0) 32 :=
    apart_sub (ev_noWrap h) (Pre.ev_arg h)
      (by unfold tableEvalsBytes nTables tableEvalBytes; omega)
  have hevh : NativeRustcVm.Apart (evi m0 i) 8 (hA m0 + BitVec.ofNat 64 (8 * i)) 8 :=
    apart_sub (ev_noWrap h) (Apart.symm' (eh.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp [wsL])))
      (by unfold tableEvalsBytes nTables tableEvalBytes; omega)
  refine frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (fun x hx ↦ ?_)
    (pairwise4 (frame_args h) (frame_ap h hevst) (frame_ap h eh.2.1) (Apart.symm' hevarg)
      (Apart.symm' (in_args eh)) hevh)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact args_ok h
  · exact ⟨fun j hj ↦ e.1 j (by omega), hev8⟩
  · exact eh.1

theorem wf_out (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} : (E m0 d [(oA m0, 24)] ret).WF := by
  have e := Pre.out h
  refine frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (frame_ap h e.2.2.2.2.1))
  rw [List.mem_singleton] at hx; subst hx; exact ⟨e.1, e.2.1⟩

theorem wf_args (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} : (E m0 d [(argA m0, 32)] ret).WF := by
  refine frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (frame_args h))
  rw [List.mem_singleton] at hx; subst hx; exact args_ok h

theorem wf_nil (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} : (E m0 d [] ret).WF :=
  frame_wf' (Pre.stack h) (by rw [N_eq]; omega) hk (by simp) (List.pairwise_singleton _ _)

/-! ## Start states -/

omit [Labels] in
theorem regionsOk2 {b x : BitVec 64} {n : Nat} : RegionsOk [280, n] [(b, 272 + 8), (x, n)] :=
  ⟨rfl, rfl, trivial⟩

/-- **A body block's start**: RSP at the frame's offset `8`, the aliases. -/
theorem match_body {d : MachineData} {R : BitVec 64 → Prop}
    (hb : Bd m0 272 N slots R 8 d) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {sizes : List Nat} {aliases : List (Sym × Nat × Int)}
    (hr : RegionsOk sizes ((stackBelow m0 272, 272 + 8) :: rest))
    (hal : AllOf (fun p ↦ p.1.eval (E m0 d rest ret) =
      (E m0 d rest ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Match (E m0 d rest ret) (init sizes [(.rsp, .ptr 0 8)] [] [] aliases) d :=
  match_ofMachine hr ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial hal

/-- **A frame word a block kept**, its writes in region `0` missing it. -/
theorem keepR {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hwf : (E m0 d rest ret).WF) (hm : Match (E m0 d rest ret) Sy d')
    (hin : writesIn Sy = true) {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ 280)
    (hmiss : missR Sy o (o + bs.length) = true)
    (h : NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fb m0) o) bs :=
  keep_frame hwf hm hin hle (missR_spec hmiss) h

theorem keepW' {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hwf : (E m0 d rest ret).WF) (hm : Match (E m0 d rest ret) Sy d')
    (hin : writesIn Sy = true) {o : Nat} {w : UInt64} (hle : o + 8 ≤ 280)
    (hmiss : missR Sy o (o + 8) = true)
    (h : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o) w :=
  keepR hwf hm hin (bs := NativeRustcVm.wordBytes w) hle hmiss h

/-- A frame word a block wrote. -/
theorem wroteW {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hm : Match (E m0 d rest ret) Sy d') {o : Nat} (hle : o + 8 ≤ 280) {v : Sym}
    (hw : WordW 0 o v Sy) {w : UInt64} (hv : v.eval (E m0 d rest ret) = w.toBitVec) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o) w :=
  wordAt_written hm (r := 0) rfl hle hw hv

/-- A frame word loaded. -/
theorem ld0 {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    (Sym.load 0 o 8).eval (E m0 d rest ret) = w.toBitVec :=
  load0 h

theorem eval_reg {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} (r : Reg64) :
    (Sym.reg r).eval (E m0 d rest ret) = reg d r := rfl

end

end NativeRustcVmX64.Tables.TableTerms
