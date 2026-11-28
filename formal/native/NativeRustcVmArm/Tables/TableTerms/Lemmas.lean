module

public import NativeRustcVmArm.Tables.TableTerms.State

/-!
# `table_terms`: what every step uses

The entry's context (`ctx`); the outputs apart from the frame and the round constants; the
blocks' writes (`wok`, `writeOk_of`) and the frame's words a block keeps (`fok`, `FW.block`),
writes (`fw_write`) or a callee keeps (`FW.call`); the `TState` and the finished entries across
the changes of the iteration over table `i` (`Ch`: the stack, entry `i`, `out`; `ts_keep`,
`ev_keep`); the inputs as at the entry (`readIn_same`, `tables_same`, `tword`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout
open NativeRustcVmArm.Sumcheck (Ctx At)
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The writes a block may make: in the frame below byte `288` apart from the slots, or within a
region `r > 0` of the outputs (`outR`), of size `szs[r]`. -/
def wok (S : SState) (szs : List Nat) (outR : List Bool) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 288) &&
      slots.all fun p ↦ decide (w.off + w.n ≤ p.1) || decide (p.1 + 8 ≤ w.off)) ||
    (w.r != 0 && decide (w.off + w.n ≤ szs.getD w.r 0) && outR.getD w.r false)

/-- Offsets of the frame whose words a block leaves alone. -/
def fok (S : SState) (os : List Nat) : Bool :=
  os.all fun o ↦ decide (o + 8 ≤ 288) && loadSym S.mem 0 o 8 == .load 0 o 8

/-- What the iteration over table `i` changes but the `TState`: the stack, entry `i`, `out`. -/
def Ch (m0 : MachineData) (i : Nat) (q : BitVec 64) : Prop :=
  InRange (stackBelow m0 N) N q ∨ InRange (evi m0 i) 1968 q ∨ InRange m0.regs.X0.toBitVec 24 q

end

public section

theorem N_eq : N = 960 := rfl
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 288 := by decide

/-- **A block's writes** as `Fr.ofBlockW` takes them. -/
theorem writeOk_of {env : Env} {S : SState} {szs : List Nat} {outR : List Bool}
    {outs : BitVec 64 → Prop} (hsz : env.regions.map Prod.snd = szs)
    (hout : ∀ r b sz, outR.getD r false = true → env.regions[r]? = some (b, sz) →
      ∀ i < sz, outs (b + BitVec.ofNat 64 i))
    (h : wok S szs outR = true) : ∀ w ∈ S.mem, WriteOk env 288 slots outs w := by
  intro w hw
  have := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    ne_eq, List.all_eq_true] at this
  rcases this with ⟨⟨hr, hle⟩, hs⟩ | ⟨⟨hr, hle⟩, ho⟩
  · exact .inl ⟨hr, hle, fun p hp ↦ by simpa using hs p hp⟩
  · refine .inr ⟨hr, fun b sz hb ↦ ⟨?_, hout w.r b sz ho hb⟩⟩
    have : szs[w.r]? = some sz := by rw [← hsz, List.getElem?_map, hb]; rfl
    rw [List.getD_eq_getElem?_getD, this, Option.getD_some] at hle
    exact hle

section
variable [Labels] {m0 : MachineData}

/-- **A word of the frame a block left alone.** -/
theorem FW.block {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {L : List (Nat × BitVec 64)} (hm : Match (Env.ofMachine m ((base m0 288, 288) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 288, 288) :: rs)).WF) {os : List Nat}
    (hL : ∀ p ∈ L, p.1 ∈ os) (hos : fok S os = true) (h : FW m0 m L) : FW m0 m' L := by
  intro p hp
  have := List.all_eq_true.mp hos p.1 (hL p hp)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  rw [← h p hp]
  unfold fw
  rw [match_wordOf_keep hm hwf (r := 0) rfl this.1 this.2]
  rfl

/-- **A word of the frame a block wrote**: its symbolic value. -/
theorem fw_write {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 288, 288) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 288, 288) :: rs)).WF) {o : Nat} (hle : o + 8 ≤ 288) :
    fw m0 m' o = (loadSym S.mem 0 o 8).eval (Env.ofMachine m ((base m0 288, 288) :: rs)) :=
  match_wordOf hm hwf (r := 0) rfl hle

omit [Labels] in
/-- A byte of the frame is not a callee's. -/
theorem frame_not_callee {m : MachineData} {N' j : Nat}
    (hsp : m.regs.SP.toBitVec = base m0 288) (hN : 288 + N' ≤ m0.regs.SP.toNat) (hj : j < 288) :
    ¬InRange (stackBelow m N') N' (base m0 288 + BitVec.ofNat 64 j) := by
  intro hq
  have hsb := stackBelow_eq hsp (N' := N') hN
  have hnw : NoWrap (base m0 (288 + N')) N' := by
    unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
  have hF := base_noWrap (m0 := m0) (F := 288) (by omega)
  unfold NoWrap at hF
  rw [hsb, Sym.inRange_iff hnw, base_toNat (by omega),
    NativeRustcVm.toNat_add_ofNat (by omega), base_toNat (by omega)] at hq
  omega

omit [Labels] in
/-- **The frame's words across a call** writing its stack below the frame and `X`. -/
theorem FW.call {m m' : MachineData} {N' : Nat} {X : BitVec 64 → Prop}
    {L : List (Nat × BitVec 64)} (hsp : m.regs.SP.toBitVec = base m0 288)
    (hN : 288 + N' ≤ m0.regs.SP.toNat)
    (hs : SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ X q))
    (hle : ∀ p ∈ L, p.1 + 8 ≤ 288)
    (hX : ∀ p ∈ L, ∀ i < 8, ¬X (base m0 288 + BitVec.ofNat 64 (p.1 + i)))
    (h : FW m0 m L) : FW m0 m' L := by
  intro p hp
  rw [← h p hp]
  have hb : ∀ i < 8, m'.dmem.get? (base m0 288 + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) =
      m.dmem.get? (base m0 288 + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) := by
    intro i hi
    refine hs _ fun hq ↦ ?_
    rw [NativeRustcVm.addr_add_add] at hq
    rcases hq with hq | hq
    · exact frame_not_callee hsp hN (by have := hle p hp; omega) hq
    · exact hX p hp i hi hq
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr hb)

variable {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}

/-- The entry's context. -/
theorem ctx (h : TableTermsPre a s heights forms m0) : Ctx m0 m0.regs.X1.toBitVec a N 288 :=
  Bus.Gkr.ctx_of (Pre.stack h) (Pre.rc h) (Pre.ts h) (Pre.tok h) (by rw [N_eq]; omega) rfl

theorem spN (h : TableTermsPre a s heights forms m0) : N ≤ m0.regs.SP.toNat := (Pre.stack h).2.1

/-- The outputs are apart from the round constants. -/
theorem outs_rc (h : TableTermsPre a s heights forms m0) :
    ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun _ hq ↦
  hq.elim (Bus.Gkr.out_not_rc (ctx h) (Pre.out h)) fun hq ↦
    hq.elim (ctx h).not_rc_tstate (Bus.Gkr.out_not_rc (ctx h) (Pre.evs h))

/-- The outputs are apart from the frame. -/
theorem outs_frame (h : TableTermsPre a s heights forms m0) :
    ∀ q, outs m0 q → ¬InRange (base m0 288) 288 q := fun _ hq ↦
  hq.elim (Bus.Gkr.out_not_frame (ctx h) (Pre.out h)) fun hq ↦
    hq.elim (Bus.Gkr.tstate_not_frame (ctx h)) (Bus.Gkr.out_not_frame (ctx h) (Pre.evs h))

/-- No output is a byte of the frame. -/
theorem outs_frame_add (h : TableTermsPre a s heights forms m0) {j : Nat} (hj : j < 288) :
    ¬outs m0 (base m0 288 + BitVec.ofNat 64 j) := fun ho ↦
  outs_frame h _ ho (NativeRustcVm.inRange_add hj (by norm_num))

theorem ev_noWrap (h : TableTermsPre a s heights forms m0) : NoWrap (ev m0) tableEvalsBytes :=
  (Pre.evs h).2.1

theorem evi_noWrap (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    NoWrap (evi m0 i) 1968 :=
  NativeRustcVm.NoWrap.sub (ev_noWrap h) (by unfold tableEvalsBytes nTables tableEvalBytes; omega)

/-- Entry `i` is in the entries. -/
theorem evi_in (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {q : BitVec 64}
    (hq : InRange (evi m0 i) 1968 q) : InRange (ev m0) tableEvalsBytes q :=
  NativeRustcVm.InRange.of_sub hq (ev_noWrap h)
    (by unfold tableEvalsBytes nTables tableEvalBytes; omega)

/-- Entry `i` is outputs. -/
theorem evi_outs (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {j : Nat}
    (hj : j < 1968) : outs m0 (evi m0 i + BitVec.ofNat 64 j) :=
  .inr (.inr (evi_in h hi (NativeRustcVm.inRange_add hj (by norm_num))))

omit [Labels] in
/-- `out` is outputs. -/
theorem out_outs {j : Nat} (hj : j < 24) : outs m0 (m0.regs.X0.toBitVec + BitVec.ofNat 64 j) :=
  .inl (NativeRustcVm.inRange_add hj (by norm_num))

/-- Two entries are apart. -/
theorem evi_apart (h : TableTermsPre a s heights forms m0) {i j : Nat} (hi : i < 6) (hj : j < 6)
    (hne : i ≠ j) : Apart (evi m0 i) 1968 (evi m0 j) 1968 :=
  NativeRustcVm.apart_of_le (ev_noWrap h)
    (by unfold tableEvalsBytes nTables tableEvalBytes; omega)
    (by unfold tableEvalsBytes nTables tableEvalBytes; omega) (by omega)

/-- A change of the iteration is neither the `TState`'s nor its decoded area's. -/
theorem ch_not_ts (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {q : BitVec 64}
    (hq : Ch m0 i q) :
    ¬InRange m0.regs.X1.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have c := ctx h
  rcases hq with hq | hq | hq
  · have hnw : NoWrap (stackBelow m0 N) N := Bus.stack_noWrap (Pre.stack h)
    exact ⟨NativeRustcVm.Apart.not_inRange c.tok.1.symm hnw c.fp.1.2 hq,
      NativeRustcVm.Apart.not_inRange c.tok.2.1.symm hnw c.fp.2.1.2 hq⟩
  · exact out_not_ts (Pre.ts h) (Pre.evs h) _ (evi_in h hi hq)
  · exact out_not_ts (Pre.ts h) (Pre.out h) _ hq

/-- **The `TState`** across changes of the iteration. -/
theorem ts_keep (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d d' : Mem 64}
    {W : BitVec 64 → Prop} (hk : Kept d d') (hs : SameOutside d d' W)
    (hW : ∀ q, W q → Ch m0 i q) {si : TState} (hts : TStateAt d m0.regs.X1.toBitVec a si) :
    TStateAt d' m0.regs.X1.toBitVec a si :=
  hts.frame hk (fun q hq ↦ ch_not_ts h hi (hW q hq)) hs

omit [Labels] in
/-- An entry's point and evaluations over bytes that stayed the same. -/
theorem TableEvalAt.of_same {d d' : Mem 64} {p : BitVec 64} {x : Array EW × Array EW}
    (hx : TableEvalAt d p x) (hs : Same d d' p 1968) : TableEvalAt d' p x :=
  ⟨BufEWAt.of_same hx.1 hs (by decide),
    BufEWAt.of_same hx.2 (hs.sub (o := valuesOff) (k := 1480) (by decide)) (by decide)⟩

/-- **A finished entry** across changes of a later iteration and of the `TState`. -/
theorem ev_keep (h : TableTermsPre a s heights forms m0) {i j : Nat} (hi : i < 6) (hji : j < i)
    {d d' : Mem 64} {W : BitVec 64 → Prop} (hs : SameOutside d d' W)
    (hW : ∀ q, W q → Ch m0 i q ∨ InRange m0.regs.X1.toBitVec tstateBytes q)
    {x : Array EW × Array EW} (hx : TableEvalAt d (evi m0 j) x) : TableEvalAt d' (evi m0 j) x := by
  refine TableEvalAt.of_same hx (Same.of_sameOutside hs fun k hk hq ↦ ?_)
  have hnj := evi_noWrap h (show j < 6 by omega)
  have hin : InRange (ev m0) tableEvalsBytes (evi m0 j + BitVec.ofNat 64 k) :=
    evi_in h (by omega) (NativeRustcVm.inRange_add hk (by norm_num))
  rcases hW _ hq with (hq | hq | hq) | hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.evs h).2.2.2.2.1 (ev_noWrap h)
      (Bus.stack_noWrap (Pre.stack h)) hin hq
  · exact NativeRustcVm.Apart.not_inRange_add (evi_apart h (by omega) hi (by omega)) hnj
      (evi_noWrap h hi) hk hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.out_ev h).symm (ev_noWrap h) (Pre.out h).2.1 hin hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.evs h).2.2.1 (ev_noWrap h)
      (Pre.ts h).footprint.1.2 hin hq

/-- **An input** in a state of the frame: its bytes the entry's. -/
theorem readIn_same (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) {x : BitVec 64} {n : Nat}
    (hr : ReadIn m0 x n N
      [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩]) :
    Same m0.dmem m.dmem x n :=
  same_in hfr (Pre.stack h) hr.1.2 hr.2.1 fun j hj ho ↦ by
    rcases ho with ho | ho | ho
    · exact Bus.not_inRange_of_apart (hr.2.2 ⟨m0.regs.X0.toBitVec, 24⟩ (by simp)) hr.1.2
        (Pre.out h).2.1 hj ho
    · exact Bus.not_inRange_of_apart (hr.2.2 ⟨m0.regs.X1.toBitVec, tstateBytes⟩ (by simp)) hr.1.2
        (Pre.ts h).footprint.1.2 hj ho
    · exact Bus.not_inRange_of_apart (hr.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp)) hr.1.2
        (ev_noWrap h) hj ho

omit [Labels] in
theorem tables_length : (NativeRustcVm.Data.Item.bytes .tables).length = 240 := by
  rw [tables_bytes, NativeRustcVm.Transcript.length_flatMap_wordBytes, tablesWords_length]

/-- **`TABLES`** in a state of the frame: its bytes the entry's. -/
theorem tables_same (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) : Same m0.dmem m.dmem T 240 := by
  obtain ⟨-, hnw, hap⟩ := Pre.tables h .tables
  rw [tables_length] at hnw hap
  refine same_in hfr (Pre.stack h) hnw hap fun j hj ho ↦ ?_
  have hT : InRange T 240 (T + BitVec.ofNat 64 j) := NativeRustcVm.inRange_add hj (by norm_num)
  have ht := tables_length
  rcases ho with ho | ho | ho
  · have := Pre.ro h .tables
    rw [ht] at this
    exact NativeRustcVm.Apart.not_inRange this (Pre.out h).2.1 hnw ho hT
  · have := Pre.rt h .tables
    rw [ht] at this
    exact NativeRustcVm.Apart.not_inRange this (Pre.ts h).footprint.1.2 hnw ho hT
  · have := Pre.re h .tables
    rw [ht] at this
    exact NativeRustcVm.Apart.not_inRange this (ev_noWrap h) hnw ho hT

/-- **A word of `TABLES`** in a state of the frame. -/
theorem tword (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) {j : Nat} (hj : j < 30) :
    wordOf m.dmem (T + BitVec.ofNat 64 (8 * j)) = tablesWords.getD j 0 := by
  have hb := (Pre.tables h .tables).1
  rw [tables_bytes] at hb
  have hw : NativeRustcVm.WordsAt m.dmem T tablesWords :=
    WordsAt.of_same hb (tables_same h hfr) (by rw [tablesWords_length])
  have hj' : j < tablesWords.length := by rw [tablesWords_length]; exact hj
  rw [NativeRustcVm.wordOf_of_wordAt (hw.getElem hj'), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj', Option.getD_some]

end

end

end NativeRustcVmArm.Tables.TableTerms
