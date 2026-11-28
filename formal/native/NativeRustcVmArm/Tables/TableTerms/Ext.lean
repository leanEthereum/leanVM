module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Tables.TableTerms.Forms

/-!
# `table_terms`: table `i`'s point

`b10` empties entry `i`'s point, advances the height's address and calls `Buf::extend` with the
point's first `min height |point|` elements (it fits: `|point| ≤ 30`); `b11` goes on (`ext_step`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf BufEWAt)
open NativeRustcVmArm.Bus (after)

@[expose] public section

/-- The frame's words after table `i`'s point: the next height's address. -/
def Lt (m0 : MachineData) (i : Nat) (f sm : EW) : List (Nat × BitVec 64) :=
  [(96, wp m0 + BitVec.ofNat 64 (8 + 16 * i)), (80, f.c1.toBitVec), (88, f.c0.toBitVec),
    (64, sm.c1.toBitVec), (72, sm.c0.toBitVec), (104, rg m0 .X6 + BitVec.ofNat 64 (8 * (i + 1)))]

/-- Table `i`'s point. -/
abbrev pti (heights : Array Nat) (m0 : MachineData) (i : Nat) : Array EW :=
  (ptw m0).extract 0 (heights.getD i 0)

/-- The frame and two regions. -/
abbrev E2 (m0 m : MachineData) (b : BitVec 64) (n : Nat) (c : BitVec 64) (p : Nat) : Env :=
  Env.ofMachine m [(base m0 288, 288), (b, n), (c, p)]

end

public section

theorem Lt_le {m0 : MachineData} {i : Nat} {f sm : EW} {p : Nat × BitVec 64}
    (hp : p ∈ Lt m0 i f sm) : p.1 + 8 ≤ 112 := by
  simp only [Lt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rin_mono {m : MachineData} {x : BitVec 64} {n N k : Nat} {ws : List NativeRustcVm.Region}
    (h : ReadIn m x n N ws) (hk : k ≤ n) : ReadIn m x k N ws :=
  ⟨⟨NativeRustcVm.Mapped.mono h.1.1 hk, NativeRustcVm.NoWrap.mono h.1.2 hk⟩,
    by have := h.2.1; unfold OffStack Apart at this ⊢; omega,
    fun w hw ↦ by have := h.2.2 w hw; unfold Apart at this ⊢; omega⟩

/-- **Where a block wrote**: the first `n0` bytes of region 0 or the first `n1` of region 1. -/
theorem written_two {env : Env} {S : SState} {b0 b1 : BitVec 64} {s0 s1 n0 n1 : Nat}
    (h0 : env.regions[0]? = some (b0, s0)) (h1 : env.regions[1]? = some (b1, s1))
    (hn0 : NoWrap b0 n0) (hn1 : NoWrap b1 n1)
    (hS : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ n0) ∨ (w.r = 1 ∧ w.off + w.n ≤ n1))
    {q : BitVec 64} (h : Written env S q) : InRange b0 n0 q ∨ InRange b1 n1 q := by
  obtain ⟨w, hw, b, sz, hb, hlo, hhi⟩ := h
  unfold NoWrap at hn0 hn1
  rcases hS w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr, h0] at hb
    cases hb
    exact .inl ((NativeRustcVm.inRange_iff hn0).mpr ⟨by omega, by omega⟩)
  · rw [hr, h1] at hb
    cases hb
    exact .inr ((NativeRustcVm.inRange_iff hn1).mpr ⟨by omega, by omega⟩)

theorem ext_le : 288 + bufExtendStack ≤ N := by rw [N_eq]; decide

/-- A word of region 2 the block's environment loads. -/
theorem ld2 [Labels] (m0 m : MachineData) (b c : BitVec 64) (n p o : Nat) :
    (Sym.load 2 o 8).eval (E2 m0 m b n c p) = (wordOf m.dmem (c + BitVec.ofNat 64 o)).toBitVec := by
  show Env.load _ 2 o 8 = _
  rw [load_eq_wordOf]
  rfl

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- The frame and two regions at `x`, `y` (offsets `ox`, `oy`). -/
theorem match2 (hS : StackOk m0 N) {m : MachineData} (hsp : m.regs.SP.toBitVec = base m0 288)
    {b c : BitVec 64} {n p : Nat} {x y : Sym} {ox oy : Int}
    (hx : x.eval (E2 m0 m b n c p) = b + BitVec.ofInt 64 ox)
    (hy : y.eval (E2 m0 m b n c p) = c + BitVec.ofInt 64 oy) :
    Match (E2 m0 m b n c p)
      (init [(288, true), (n, false), (p, false)] (.ptr 0 0) [] [] [] [(x, (1, ox)), (y, (2, oy))])
      m :=
  match_ofMachine (sregions := [(288, true), (n, false), (p, false)])
    (regions := [(base m0 288, 288), (b, n), (c, p)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hS (by decide) rfl, rfl, nofun, rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    trivial trivial trivial ⟨hx, hy, trivial⟩

omit [Labels] in
/-- The frame and two regions apart from the stack and each other. -/
theorem wf2 (hS : StackOk m0 N) {m : MachineData} (hk : Kept m0.dmem m.dmem) {b c : BitVec 64}
    {n p : Nat} (hb : Readable m0 b n) (hc : Readable m0 c p) (hbs : OffStack m0 b n N)
    (hcs : OffStack m0 c p N) (hbc : Apart b n c p) : (E2 m0 m b n c p).WF := by
  have hN := hS.2.1
  have hbs' := hbs
  have hcs' := hcs
  unfold OffStack Apart at hbs' hcs'
  have hN' : N = 960 := N_eq
  have h1 := base_toNat (m0 := m0) (F := 288) (by omega)
  have h2 : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  refine Env.wf_of ⟨⟨fun i hi ↦ hk _ ((Bus.frame_mapped hS (by decide)).1 i hi),
    (Bus.frame_mapped hS (by decide)).2⟩, ⟨fun i hi ↦ hk _ (hb.1 i hi), hb.2⟩,
    ⟨fun i hi ↦ hk _ (hc.1 i hi), hc.2⟩, trivial⟩ ?_
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    unfold Apart
    constructor <;> omega
  · simp only [List.mem_singleton, forall_eq]
    exact hbc

/-- Table `i`'s height in a state of the frame. -/
theorem height_word (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) {i : Nat} (hi : i < 6) :
    (wordOf m.dmem (rg m0 .X6 + BitVec.ofNat 64 (8 * i))).toNat = heights.getD i 0 := by
  have hH := Pre.hts h
  have hi' : i < heights.size := by rw [hH.1]; exact hi
  have hl : i < (heights.toList.map Nat.toUInt64).length := by simp [hi']
  have hw := NativeRustcVm.Layout.WordAt.of_same (hH.2.2.getElem hl)
    (readIn_same h hfr (h_rin h hi)) (Nat.le_refl _)
  show (wordOf m.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 (8 * i))).toNat = _
  rw [NativeRustcVm.wordOf_of_wordAt hw, List.getElem_map, Array.getElem_toList,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
  have := hH.2.1 heights[i] (Array.getElem_mem hi')
  exact toNat_toUInt64 (by omega)

/-- Entry `i` across a change of the stack only. -/
theorem pt_keep (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d d' : Mem 64}
    {W : BitVec 64 → Prop} (hs : SameOutside d d' W)
    (hW : ∀ q, W q → InRange (stackBelow m0 N) N q) {l : List EW}
    (hb : BufEWAt d (evi m0 i) 30 l) : BufEWAt d' (evi m0 i) 30 l :=
  NativeRustcVm.Layout.BufEWAt.of_same hb (n := 1968)
    (Same.of_sameOutside hs fun j hj hq ↦ NativeRustcVm.Apart.not_inRange_add
      (evi_out h hi).2.2.2.2.1 (evi_noWrap h hi) (Bus.stack_noWrap (Pre.stack h)) hj (hW _ hq))
    (by omega)

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **Table `i`'s point** (`b10`, `Buf::extend`, `b11`). -/
theorem ext_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {R : MachineState → Prop} {i : Nat} (hi : i < 6) {o : Array (Array EW × Array EW)}
    {xs : Array EW} {s' : TState} {m : MachineData} (H : It a m0 i o xs s' m) {f sm fd : EW}
    (hw : FW m0 m (Lb m0 i f sm)) (x19 : rg m .X19 = wp m0 + BitVec.ofNat 64 (8 + 16 * i))
    (x28 : m.regs.X28 = (wt m0 i).c0) (x23 : m.regs.X23 = (wt m0 i).c1)
    (x22 : (m.regs.X22).toNat = (tb i).nConstraints) (hfd : ewRet m = fd)
    (cont : ∀ m', It a m0 i o xs s' m' → FW m0 m' (Lt m0 i f sm) →
      rg m' .X19 = wp m0 + BitVec.ofNat 64 (8 + 16 * i) → m'.regs.X28 = (wt m0 i).c0 →
      m'.regs.X23 = (wt m0 i).c1 → (m'.regs.X22).toNat = (tb i).nConstraints →
      m'.regs.X24 = fd.c0 → m'.regs.X25 = fd.c1 →
      BufEWAt m'.dmem (evi m0 i) 30 (pti heights m0 i).toList →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b12Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b10Offset)⟩ := by
  have hS := Pre.stack h
  have hN := spN h
  have eo := evi_out h hi
  have hr := h_rin h hi
  have hec : Apart (evi m0 i) 1968 (rg m0 .X6 + BitVec.ofNat 64 (8 * i)) 8 :=
    (apart_sub (o := 1968 * i) (k := 1968)
      (hr.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp [wsL])).symm (ev_noWrap h)
      (by show 1968 * i + 1968 ≤ tableEvalsBytes
          unfold tableEvalsBytes nTables tableEvalBytes; omega) : _)
  have hwf : (E2 m0 m (evi m0 i) 1968 (rg m0 .X6 + BitVec.ofNat 64 (8 * i)) 8).WF :=
    wf2 hS H.fr.kept ⟨eo.1, eo.2.1⟩ hr.1 eo.2.2.2.2.1 hr.2.1 hec
  have f104 : fw m0 m 104 = rg m0 .X6 + BitVec.ofNat 64 (8 * i) := hw (104, _) (by simp [Lb, lws])
  have hm : Match (E2 m0 m (evi m0 i) 1968 (rg m0 .X6 + BitVec.ofNat 64 (8 * i)) 8) ptS m :=
    match2 hS H.fr.sp (by show rg m .X27 = _; rw [H.x27]; exact (BitVec.add_zero _).symm)
      (by rw [ld0, f104]; exact (BitVec.add_zero _).symm)
  refine exec_then (hb10 hp) run_b10 hwf hm fun st hma0 hpc ↦ ?_
  have hma : Match (E2 m0 m (evi m0 i) 1968 (rg m0 .X6 + BitVec.ofNat 64 (8 * i)) 8)
      (after b10 ptS) st.data := by rw [Bus.after_eq run_b10]; exact hma0
  obtain ⟨sp10, wok10, fok10, l104, l10, k10, r0, r1, r2, r24, r25⟩ := ok_b10
  have hfr10 := fr_block (szs := [288, 1968, 8]) H.fr hN hm hma hwf (sp10.trans rfl) rfl
    (hout_mid fun _ hj ↦ evi_outs h hi hj) wok10
  have hsplit : ∀ w ∈ (after b10 ptS).mem, (w.r = 0 ∧ w.off + w.n ≤ 288) ∨
      (w.r = 1 ∧ w.off + w.n ≤ 8) := by
    rw [Bus.after_eq run_b10]; decide
  have k10r : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X26, .X27, .X28, .X29],
      st.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ rk hma (keeps_get k10 hr)
  have It10 : It a m0 i o xs s' st.data :=
    It.step h hi H hfr10 (hma.kept hwf) (hma.sameOutside hwf)
      (fun q hq ↦ (written_two rfl rfl (base_noWrap (by rw [N_eq] at hN; omega))
        (NativeRustcVm.NoWrap.mono (evi_noWrap h hi) (by omega)) hsplit hq).elim
        (fun hq ↦ .inl (Bus.frame_inRange hN (by decide) hq))
        fun hq ↦ .inr (NativeRustcVm.InRange.mono hq
          (NativeRustcVm.NoWrap.mono (evi_noWrap h hi) (by omega))
          (NativeRustcVm.NoWrap.mono (evi_noWrap h hi) (by omega)) le_rfl (by omega)))
      (FW.block hma hwf (L := cws m0) (fun p hp ↦ mem_of_all (by simp [cws]) hp) fok10 H.cw)
      fun r hr ↦ k10r r (by revert r hr; simp)
  have hw' : FW m0 m [(96, wp m0 + BitVec.ofNat 64 (8 + 16 * i)), (80, f.c1.toBitVec),
      (88, f.c0.toBitVec), (64, sm.c1.toBitVec), (72, sm.c0.toBitVec)] := fun p hp ↦ hw p (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [Lb, lws])
  have fw10' := FW.block hma hwf (fun p hp ↦ mem_of_all (by simp) hp) fok10 hw'
  have fw10 : FW m0 st.data (Lt m0 i f sm) := by
    intro p hp
    simp only [Lt, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fw10' _ (by simp)
    · exact fw10' _ (by simp)
    · exact fw10' _ (by simp)
    · exact fw10' _ (by simp)
    · exact fw10' _ (by simp)
    · show fw m0 st.data 104 = _
      rw [fw_write hma hwf (by omega), l104, eval_add_lit, ld0, f104, NativeRustcVm.addr_add_add,
        show 8 * i + 8 = 8 * (i + 1) by ring]
  -- The point's count is `0`.
  have hw0 : (wordOf st.data.dmem (evi m0 i)).toNat = 0 := by
    have := wordAt_of_load hma hwf (r := 1) (o := 0) rfl (by omega) l10
    rw [NativeRustcVm.addr_add_zero] at this
    rw [NativeRustcVm.wordOf_of_wordAt this]
    rfl
  -- The arguments.
  have e0 : st.data.regs.X0.toBitVec = evi m0 i := by
    show rg st.data .X0 = _
    rw [rv hma r0]; exact H.x27
  have e1 : st.data.regs.X1 = m0.regs.X4 := by
    apply UInt64.toBitVec_inj.mp
    show rg st.data .X1 = _
    rw [rv hma r1, ld0, H.cw (40, rg m0 .X4) (by simp [cws])]; rfl
  have hx5 := Pre.x5 h
  have e2 : st.data.regs.X2.toNat = min (heights.getD i 0) m0.regs.X5.toNat := by
    show (rg st.data .X2).toNat = _
    have hh : (wordOf m.dmem (rg m0 .X6 + BitVec.ofNat 64 (8 * i))).toBitVec.toNat =
        heights.getD i 0 := height_word h H.fr hi
    have l2 : (Sym.load 2 0 8).eval
        (E2 m0 m (evi m0 i) 1968 (rg m0 .X6 + BitVec.ofNat 64 (8 * i)) 8) =
        (wordOf m.dmem (rg m0 .X6 + BitVec.ofNat 64 (8 * i))).toBitVec := by
      rw [ld2, NativeRustcVm.addr_add_zero]
    have l48 : (Sym.load 0 48 8).eval
        (E2 m0 m (evi m0 i) 1968 (rg m0 .X6 + BitVec.ofNat 64 (8 * i)) 8) = m0.regs.X5.toBitVec :=
      by rw [ld0, H.cw (48, rg m0 .X5) (by simp [cws])]; rfl
    have h5 : m0.regs.X5.toBitVec.toNat = m0.regs.X5.toNat := rfl
    rw [rv hma r2, eval_min, l2, l48]
    split <;> omega
  have hmin : min (heights.getD i 0) m0.regs.X5.toNat ≤ 30 := by
    unfold tablePointCap at hx5; omega
  have pr := rin_mono (Pre.pt h) (k := 16 * min (heights.getD i 0) m0.regs.X5.toNat) (by omega)
  have hle := ext_le
  have hpre : BufEWExtendPre 30 st.data := by
    simp only [BufEWExtendPre]
    rw [e0, e1, e2, hw0]
    refine ⟨by omega, Bus.Fr.readable hfr10 ⟨NativeRustcVm.Mapped.mono eo.1 (by omega),
      NativeRustcVm.NoWrap.mono eo.2.1 (by omega)⟩, Bus.Fr.readable hfr10 pr.1, ?_⟩
    exact (apart_sub (o := 1968 * i) (k := 488)
      (pr.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp)).symm (ev_noWrap h)
      (by show 1968 * i + 488 ≤ tableEvalsBytes
          unfold tableEvalsBytes nTables tableEvalBytes; omega) : _)
  have hin : ∀ q, InRange (evi m0 i) (8 + 16 * 30) q → outs m0 q := fun q hq ↦
    .inr (.inr (evi_in h hi (NativeRustcVm.InRange.mono hq
      (NativeRustcVm.NoWrap.mono (evi_noWrap h hi) (by omega)) (evi_noWrap h hi) le_rfl
      (by omega))))
  have hpc' : st.pc = Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b11Offset) :=
    ⟨hpc.1, hpc.2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b10_next]))⟩
  have hch : ∀ m', BufEWExtendPost 30 st.data m' → SameOutside st.data.dmem m'.dmem
      (fun q ↦ InRange (stackBelow st.data bufExtendStack) bufExtendStack q ∨
        InRange (evi m0 i) (8 + 16 * 30) q) := fun m' hq ↦ by
    have := hq.2.1
    unfold Changes at this
    rw [e0] at this
    exact NativeRustcVm.SameOutside.mono this fun q hq ↦ hq.elim .inr .inl
  refine Bus.Gkr.Fr.callSpec hfr10 hN hle (fun _ h ↦ nomatch h) slots_le (outs_frame h) hext
    hpc' hpre (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hch m' hq) fun q hq ↦
      hq.elim .inl fun hq ↦ .inr (hin q hq), hq.2.2⟩) fun m5 hfr5 hq5 hcs5 ↦ ?_
  have hs5 := hch m5 hq5
  have hfit : (wordOf st.data.dmem st.data.regs.X0.toBitVec).toNat + st.data.regs.X2.toNat ≤ 30 :=
    by rw [e0, hw0, e2]; omega
  have hq5' := hq5.1
  split at hq5'
  rotate_left
  · exact absurd hfit ‹_›
  obtain ⟨hx0, hbuf⟩ := hq5'
  have hpt : (NativeRustcVm.bufEWOf st.data.dmem st.data.regs.X0.toBitVec ++
      (slice st.data st.data.regs.X1 st.data.regs.X2).toList) = (pti heights m0 i).toList := by
    rw [NativeRustcVm.bufEWOf, e0, hw0, e1]
    unfold slice
    rw [e2, ewsOf_in h hfr10 pr, ewsOf_take,
      show ewsOf st.data.dmem (evi m0 i + 8#64) 0 = [] from rfl]
    show _ = ((ptw m0).extract 0 (heights.getD i 0)).toList
    rw [Array.toList_extract]
    simp [ptw, slice]
  rw [hpt, e0] at hbuf
  have It5 : It a m0 i o xs s' m5 :=
    It.call h hi It10 hfr5 hle hs5
      (fun q hq ↦ .inr (NativeRustcVm.InRange.mono hq
        (NativeRustcVm.NoWrap.mono (evi_noWrap h hi) (by omega))
        (NativeRustcVm.NoWrap.mono (evi_noWrap h hi) (by omega)) le_rfl (by omega)))
      (fun p hp j hj hq ↦ outs_frame_add h (j := p.1 + j)
        (by have := cl_le (i := 0) (List.mem_append_left (lws m0 0) hp); omega) (hin _ hq))
      hq5.2.2
  have fw5 : FW m0 m5 (Lt m0 i f sm) :=
    FW.out h hfr10 hle (fun p hp ↦ by have := Lt_le hp; omega)
      (NativeRustcVm.SameOutside.mono hs5 fun q hq ↦ hq.elim .inl fun hq ↦ .inr (hin q hq)) fw10
  -- `b11`: `Some`.
  refine Bus.Gkr.Fr.runBlock hS (by rw [N_eq]; omega) rfl hfr5 (hb11 hp) run_b11 rfl rfl
    (by decide) (by decide) fun st6 hfr6 hd6 hm6 hpc6 ↦ ?_
  have hm6' : Match (E0 m0 m5) (after b11 sF) st6.data := by rw [Bus.after_eq run_b11]; exact hm6
  obtain ⟨-, -, k11⟩ := ok_b11
  have hc : SBool.eval (E0 m0 m5) (.not (.bit .W32 (.reg .X0) 0)) = false := by
    show (!(low .W32 (m5.regs.getXReg .X0).toBitVec).getLsbD 0) = false
    rw [show m5.regs.getXReg .X0 = m5.regs.X0 from rfl, hx0,
      show (1 : UInt64) = okWord true from rfl, Bus.Gkr.okWord_bit]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc6
  have kr : ∀ r ∈ cs, st6.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦ by
    rw [rk hm6' (keeps_get k11 hr), hcs5 r (cs_saved r hr)]
  have G : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X26, .X27, .X28, .X29],
      st6.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    rw [kr r (by revert r hr; simp [cs]), k10r r hr]
  refine Bus.Gkr.at_pc (hpc6.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b11_next])))
    (cont st6.data ?_ (FW.of_dmem hd6 fw5) ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hd6]; exact hbuf))
  · exact It.step h hi It5 hfr6 (by rw [hd6]; exact fun _ h ↦ h)
      (NativeRustcVm.SameOutside.of_eq hd6 (fun _ ↦ False)) (fun _ h ↦ h.elim)
      (FW.of_dmem hd6 It5.cw) fun r hr ↦ rk hm6' (keeps_get k11 (by revert r hr; simp [cs]))
  · unfold rg; rw [G .X19 (by simp)]; exact x19
  · show st6.data.regs.getXReg .X28 = _; rw [G .X28 (by simp)]; exact x28
  · show st6.data.regs.getXReg .X23 = _; rw [G .X23 (by simp)]; exact x23
  · show (st6.data.regs.getXReg .X22).toNat = _; rw [G .X22 (by simp)]; exact x22
  · show st6.data.regs.getXReg .X24 = _
    rw [kr .X24 (by simp [cs])]
    apply UInt64.toBitVec_inj.mp
    rw [show (st.data.regs.getXReg .X24).toBitVec = rg st.data .X24 from rfl, rv hma r24, ← hfd]
    rfl
  · show st6.data.regs.getXReg .X25 = _
    rw [kr .X25 (by simp [cs])]
    apply UInt64.toBitVec_inj.mp
    rw [show (st.data.regs.getXReg .X25).toBitVec = rg st.data .X25 from rfl, rv hma r25, ← hfd]
    rfl

end

end NativeRustcVmArm.Tables.TableTerms
