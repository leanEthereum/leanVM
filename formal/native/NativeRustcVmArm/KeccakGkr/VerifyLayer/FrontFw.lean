module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontPro

/-!
# `verify_layer`'s front: the frame's contents across blocks and calls

Words and ranges of the frame kept by a block whose writes miss them (`fw_blk`, `same_blk`), by a
call writing below the frame, a range of the frame and memory outside it (`fw_call`,
`same_call`); a frame range as a slice (`slice_loc`), as readable data apart from a callee's
stack (`readable_loc`, `offStack_loc`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm.Layout (Same)
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)

@[expose] public section

/-- The writes of a block miss the frame's words at `offs` and the `n` bytes at `o`. -/
def MissW (mem : List Write) (offs : List Nat) (o n : Nat) : Bool :=
  mem.all fun w ↦ w.r == 0 && w.off + w.n ≤ 1936 &&
    offs.all (fun p ↦ w.off + w.n ≤ p || p + 8 ≤ w.off) && (w.off + w.n ≤ o || o + n ≤ w.off)

end

public section

variable {m0 : MachineData}

theorem same_word {d d' : DataMem} {b : BitVec 64} {o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) v)
    (hs : Same d d' (b + BitVec.ofNat 64 o) 8) :
    NativeRustcVm.WordAt d' (b + BitVec.ofNat 64 o) v :=
  NativeRustcVm.Layout.WordAt.of_same h hs (Nat.le_refl _)

/-- **Bytes of the frame a call keeps**: outside the range `[o, o + n)` it writes, the other
bytes it writes below the frame or outside it. -/
theorem same_call (g : Geo m0) {d d' : DataMem} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {o n : Nat} (hR : ∀ q, R q → Bel m0 q ∨ InRange (loc m0 o) n q ∨
      ¬InRange (base m0 2032) 2032 q) (hon : o + n ≤ 2032) {o' n' : Nat} (hon' : o' + n' ≤ 2032)
    (hd : o' + n' ≤ o ∨ o + n ≤ o') : Same d d' (loc m0 o') n' := by
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN
  have hb3 : (base m0 3648).toNat = m0.regs.SP.toNat - 3648 := base_toNat (by omega)
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ ?_
  rw [NativeRustcVm.addr_add_add] at hq
  have e := g.fa (o := o' + j) (by omega)
  rcases hR _ hq with hq | hq | hq
  · unfold Bel at hq
    rw [Sym.inRange_iff (by rw [hb3]; omega), hb3, e] at hq
    omega
  · rw [Sym.inRange_iff (by rw [g.fa (by omega)]; omega), g.fa (by omega), e] at hq
    omega
  · exact hq (NativeRustcVm.inRange_add (by omega) (by omega))

/-- **The frame's words a call keeps.** -/
theorem fw_call (g : Geo m0) {d d' : DataMem} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {o n : Nat} (hR : ∀ q, R q → Bel m0 q ∨ InRange (loc m0 o) n q ∨
      ¬InRange (base m0 2032) 2032 q) (hon : o + n ≤ 2032) {ws : List (Nat × UInt64)}
    (hws : ∀ p ∈ ws, p.1 + 8 ≤ 2032 ∧ (p.1 + 8 ≤ o ∨ o + n ≤ p.1))
    (h : Bus.FrameWords d (base m0 2032) ws) : Bus.FrameWords d' (base m0 2032) ws :=
  fun p hp ↦ same_word (h p hp) (same_call g hs hR hon (hws p hp).1 (hws p hp).2)

/-- A word of the frame not among a block's writes. -/
theorem same_blk [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 2032, 2032) :: rs)).WF) {o' n' : Nat}
    (hon' : o' + n' ≤ 2032) (hw : S.mem.all (fun w ↦ w.r == 0 &&
      (w.off + w.n ≤ o' || o' + n' ≤ w.off)) = true) :
    Same m.dmem m'.dmem (loc m0 o') n' := by
  refine fun j hj ↦ hm.get?_mem0 hwf fun ⟨w, hwm, b, sz, hb, h1, h2⟩ ↦ ?_
  have h' := List.all_eq_true.mp hw w hwm
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at h'
  obtain ⟨hr, hd⟩ := h'
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have hnw := hwf.noWrap 0 _ _ rfl
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at h1 h2
  omega

/-- **The frame's words a block keeps.** -/
theorem fw_blk [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 2032, 2032) :: rs)).WF) {ws : List (Nat × UInt64)}
    (offs : List Nat) (hoffs : ws.map Prod.fst = offs)
    (hchk : (offs.all fun p ↦ p + 8 ≤ 2032 && S.mem.all (fun w ↦ w.r == 0 &&
      (w.off + w.n ≤ p || p + 8 ≤ w.off))) = true)
    (h : Bus.FrameWords m.dmem (base m0 2032) ws) : Bus.FrameWords m'.dmem (base m0 2032) ws := by
  intro p hp
  have hp' : p.1 ∈ offs := hoffs ▸ List.mem_map_of_mem hp
  have hc := List.all_eq_true.mp hchk p.1 hp'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact same_word (h p hp) (same_blk hm hwf hc.1 hc.2)

/-- A range of the frame as a slice. -/
theorem slice_loc {m : MachineData} {o : Nat} {xs : List EW}
    (h : NativeRustcVm.EWsAt m.dmem (loc m0 o) xs) {a n : UInt64} (ha : a.toBitVec = loc m0 o)
    (hn : n.toNat = xs.length) : (slice m a n).toList = xs := by
  unfold slice
  rw [ha, hn, List.toList_toArray]
  exact NativeRustcVm.ewsOf_of_ewsAt h

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW}

/-- A range of the frame is readable in the front. -/
theorem readable_loc (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) {o n : Nat}
    (hon : o + n ≤ 2032) : Readable m (loc m0 o) n := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0
  exact ⟨fun i hi ↦ by
      rw [NativeRustcVm.addr_add_add]
      exact hb.kept _ (frame_mapped (pre_stack h) N_ge _ (by omega)),
    by unfold NoWrap; rw [g.fa (by omega)]; omega⟩

/-- A range of the frame is apart from a callee's stack. -/
theorem offStack_loc (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) {o n N' : Nat}
    (hon : o + n ≤ 2032) (hN : N' ≤ 1616) : OffStack m (loc m0 o) n N' := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0
  have hst := g.stk hb.sp hN
  unfold OffStack Apart
  rw [hst, g.fa (by omega)]
  omega

/-- A range of the scratch is readable in the front. -/
theorem readable_scr (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) {o n : Nat}
    (ho : o < 205824) (hon : o + n ≤ 205824) : Readable m (sA m0 + BitVec.ofNat 64 o) n := by
  have g := geo_of h
  have pg := pgeo_of h
  have := g.hs
  exact ⟨mapped_sub hb.kept pg.sm hon, by unfold NoWrap; rw [g.sa ho]; omega⟩

/-- A range of the scratch is apart from a callee's stack. -/
theorem offStack_scr (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) {o n N' : Nat}
    (ho : o < 205824) (hon : o + n ≤ 205824) (hN : N' ≤ 1616) :
    OffStack m (sA m0 + BitVec.ofNat 64 o) n N' := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0; have := g.hs; have := g.hss
  have hst := g.stk hb.sp hN
  unfold OffStack Apart
  rw [hst, g.sa ho]
  omega

/-- A range of the claim is readable in the front. -/
theorem readable_cl (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) {o n : Nat}
    (ho : o < 768) (hon : o + n ≤ 768) : Readable m (cA m0 + BitVec.ofNat 64 o) n := by
  have g := geo_of h
  have pg := pgeo_of h
  have := g.hc
  exact ⟨mapped_sub hb.kept pg.cm hon, by unfold NoWrap; rw [g.ca ho]; omega⟩

/-- A range of the claim is apart from a callee's stack. -/
theorem offStack_cl (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) {o n N' : Nat}
    (ho : o < 768) (hon : o + n ≤ 768) (hN : N' ≤ 1616) :
    OffStack m (cA m0 + BitVec.ofNat 64 o) n N' := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0; have := g.hc; have := g.hcs
  have hst := g.stk hb.sp hN
  unfold OffStack Apart
  rw [hst, g.ca ho]
  omega

end

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
