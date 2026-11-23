module

public import NativeRustcVmX64.Tables.TableTerms.State
public import NativeRustcVmX64.Tables.TableTerms.Run
public import NativeRustcVm.Tables.Same

/-!
# `table_terms`: what every step uses (x86-64)

The entry's context (`ctx`); the outputs apart from the stack, the frame, the round constants, the
arguments and the inputs (`not_*`); the inputs and `TABLES` as at the entry in a body
(`same_in`, `args_same`, `tables_same`, `tword`); the frame's words across blocks and calls
(`FW.block`, `FW.call`); the iteration's outputs across the changes after `read_scalars`
(`It.step`); words an environment loads (`load_eq_wordOf`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeRustcVm (wordOf ewsOf)

public section

theorem N_eq : N = 976 := by decide

theorem slots_le : ∀ p ∈ slots, 224 ≤ p.1 ∧ p.1 + 8 ≤ 272 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem ofBytes_eq_leNat : ∀ bs : List UInt8, Nat.ofBytes bs = NativeRustcVm.leNat bs
  | [] => rfl
  | b :: bs => by
    show Nat.ofBytes bs * 256 + b.toNat = b.toNat + 256 * NativeRustcVm.leNat bs
    rw [ofBytes_eq_leNat bs]
    omega

/-- **An environment's load of eight bytes** is the word `wordOf` reads there. -/
theorem load_eq_wordOf (env : Env) (r o : Nat) :
    env.load r o 8 = (wordOf env.mem0 (env.base r + BitVec.ofNat 64 o)).toBitVec := by
  unfold Env.load NativeRustcVm.wordOf NativeRustcVm.bytesFrom
  rw [ofBytes_natCast, BitVec.ofInt_natCast, ofBytes_eq_leNat]
  show BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  congr 2
  apply List.map_congr_left
  intro i _
  rw [addr_add]

/-- A word an environment loads where the word is known. -/
theorem load_of_wordAt' {env : Env} {r o : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) :
    env.load r o 8 = w.toBitVec := by
  rw [load_eq_wordOf, NativeRustcVm.wordOf_of_wordAt h]

/-- The frame's word `o` is loaded from region `0` of a frame environment. -/
theorem load0 {m0 d : MachineData} {F : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) o) w) :
    (frameEnv m0 d F rest vars ret).load 0 o 8 = w.toBitVec :=
  load_of_wordAt' (r := 0) h

theorem toBitVec_ofBitVec' (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x := rfl

/-- The frame's words left alone by a block. -/
theorem FW.block [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d 272 rest vars ret).WF) (hm : Match (frameEnv m0 d 272 rest vars ret) S d')
    (hin : writesIn S = true) {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, p.1 + 8 ≤ 280)
    (hmiss : missO S (L.map Prod.fst) = true) (h : FW m0 d L) : FW m0 d' L := by
  intro p hp
  refine keepW hwf hm hin (hL p hp) (fun w hw hr ↦ ?_) (h p hp)
  have := List.all_eq_true.mp (List.all_eq_true.mp hmiss p.1 (List.mem_map_of_mem hp)) w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

/-- `missO` of fewer words. -/
theorem missO_sub {S : SState} {os os' : List Nat} (h : missO S os = true)
    (hs : ∀ o ∈ os', o ∈ os) : missO S os' = true :=
  List.all_eq_true.mpr fun o ho ↦ List.all_eq_true.mp h o (hs o ho)

/-- The frame's words of a body kept by a call at offset `0` changing `Ro` and its stack. -/
theorem FW.call {m0 d d' : MachineData} {R : BitVec 64 → Prop} (hb : Bd m0 272 N slots R 0 d)
    (hst : StackOk m0 N) {n' : Nat} (hn : 272 + n' ≤ N) {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d n') n' q))
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280)
    (hRo : ∀ p ∈ L, ∀ i < 8, ¬ Ro (off (fb m0) (p.1 + i))) (h : FW m0 d L) : FW m0 d' L :=
  fun p hp ↦ keepW_call hb hst (by rw [N_eq]; omega) (by omega) (by omega) hso (hL p hp).1
    (hL p hp).2 (hRo p hp) (h p hp)

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- The entry's context. -/
theorem ctx (h : TableTermsPre a s heights forms m0) : Ctx m0 (tA m0) a N 272 :=
  ⟨Pre.stack h, Pre.rc h, Pre.tok h, (Pre.ts h).footprint, by rw [N_eq]; omega⟩

theorem spN (h : TableTermsPre a s heights forms m0) : N ≤ (rspOf m0).toNat := (Pre.stack h).1

theorem sp8 (h : TableTermsPre a s heights forms m0) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 :=
  (Pre.stack h).2.1

theorem stack_noWrap (h : TableTermsPre a s heights forms m0) :
    NativeRustcVm.NoWrap (stackBelow m0 N) (N + 8) :=
  noWrap_stackBelow (Pre.stack h)

theorem stk (h : TableTermsPre a s heights forms m0) :
    (stackBelow m0 N).toNat = (rspOf m0).toNat - N := stackBelow_toNat (spN h)

theorem fb_toNat (h : TableTermsPre a s heights forms m0) :
    (fb m0).toNat = (rspOf m0).toNat - 272 := stackBelow_toNat (by have := spN h; rw [N_eq] at this; omega)

theorem argA_toNat (h : TableTermsPre a s heights forms m0) :
    (argA m0).toNat = (rspOf m0).toNat + 8 := by
  have := (Pre.args h).2
  exact NativeRustcVm.toNat_add_ofNat (by omega)

theorem args_noWrap (h : TableTermsPre a s heights forms m0) : NativeRustcVm.NoWrap (argA m0) 32 := by
  have := (Pre.args h).2
  unfold NativeRustcVm.NoWrap
  rw [argA_toNat h]
  omega

theorem ev_noWrap (h : TableTermsPre a s heights forms m0) :
    NativeRustcVm.NoWrap (ev m0) tableEvalsBytes := (Pre.evs h).2.1

theorem evi_noWrap (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    NativeRustcVm.NoWrap (evi m0 i) 1968 :=
  NativeRustcVm.NoWrap.sub (ev_noWrap h) (by unfold tableEvalsBytes nTables tableEvalBytes; omega)

/-- Entry `i` is in the entries. -/
theorem evi_in (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (evi m0 i) 1968 q) : NativeRustcVm.InRange (ev m0) tableEvalsBytes q :=
  NativeRustcVm.InRange.of_sub hq (ev_noWrap h)
    (by unfold tableEvalsBytes nTables tableEvalBytes; omega)

/-- Two entries are apart. -/
theorem evi_apart (h : TableTermsPre a s heights forms m0) {i j : Nat} (hi : i < 6) (hj : j < 6)
    (hne : i ≠ j) : NativeRustcVm.Apart (evi m0 i) 1968 (evi m0 j) 1968 :=
  NativeRustcVm.apart_of_le (ev_noWrap h)
    (by unfold tableEvalsBytes nTables tableEvalBytes; omega)
    (by unfold tableEvalsBytes nTables tableEvalBytes; omega) (by omega)

/-- Entry `i` as an output. -/
theorem evi_out (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    OutOk m0 (tA m0) a (evi m0 i) 1968 N := by
  have e := Pre.evs h
  have hk : 1968 * i + 1968 ≤ tableEvalsBytes := by
    unfold tableEvalsBytes nTables tableEvalBytes; omega
  have hnw : NativeRustcVm.NoWrap (ev m0) tableEvalsBytes := e.2.1
  have sub : ∀ {b : BitVec 64} {nb : Nat}, NativeRustcVm.Apart (ev m0) tableEvalsBytes b nb →
      NativeRustcVm.Apart (evi m0 i) 1968 b nb := fun hA ↦ by
    have := NativeRustcVm.toNat_add_ofNat_le (a := ev m0) (i := 1968 * i)
      (by unfold NativeRustcVm.NoWrap at hnw; omega)
    unfold NativeRustcVm.NoWrap at hnw
    unfold NativeRustcVm.Apart at hA ⊢
    unfold evi
    omega
  exact ⟨NativeRustcVm.Mapped.sub e.1 hk, NativeRustcVm.NoWrap.sub hnw hk, sub e.2.2.1,
    sub e.2.2.2.1, sub e.2.2.2.2.1, sub e.2.2.2.2.2⟩

/-! ## The outputs apart -/

theorem not_stack_of_apart {x : BitVec 64} {n : Nat} (h : TableTermsPre a s heights forms m0)
    (hx : NativeRustcVm.NoWrap x n)
    (hA : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8)) {q : BitVec 64}
    (hq : NativeRustcVm.InRange x n q) : ¬ NativeRustcVm.InRange (stackBelow m0 N) (N + 8) q :=
  NativeRustcVm.Apart.not_inRange hA hx (stack_noWrap h) hq

/-- An output is not a byte of the stack or the return address. -/
theorem outs_not_stack (h : TableTermsPre a s heights forms m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange (stackBelow m0 N) (N + 8) q := by
  rcases hq with hq | hq | hq
  · exact not_stack_of_apart h (Pre.out h).2.1 (Pre.out h).2.2.2.2.1 hq
  · exact not_stack_of_apart h (Pre.ts h).footprint.1.2 (Pre.tok h).1 hq
  · exact not_stack_of_apart h (ev_noWrap h) (Pre.evs h).2.2.2.2.1 hq

theorem outs_not_stackN (h : TableTermsPre a s heights forms m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange (stackBelow m0 N) N q :=
  fun h' ↦ outs_not_stack h hq (inRange_mono h' (by omega))

/-- An output is not a byte of the frame. -/
theorem outs_not_frame (h : TableTermsPre a s heights forms m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange (fb m0) 280 q := by
  intro hf
  apply outs_not_stack h hq
  have hnw := stack_noWrap h
  have e := stk h
  have ef := fb_toNat h
  have h1 := spN h; have h2 := sp8 h
  have hN : N = 976 := N_eq
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [ef]; omega), ef] at hf
  rw [inRange_iff' hnw, e]
  omega

/-- An output is not a round constant. -/
theorem outs_not_rc (h : TableTermsPre a s heights forms m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange rcAddr 192 q := by
  have c := ctx h
  rcases hq with hq | hq | hq
  · exact c.out_not_rc (Pre.out h) hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (Pre.evs h) hq

/-- An output is not an argument word. -/
theorem outs_not_args (h : TableTermsPre a s heights forms m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange (argA m0) 32 q := by
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.out_arg h) (Pre.out h).2.1 (args_noWrap h) hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.t_arg h) (Pre.ts h).footprint.1.2 (args_noWrap h) hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.ev_arg h) (ev_noWrap h) (args_noWrap h) hq

/-- An output is not a byte of an input. -/
theorem outs_not_in (h : TableTermsPre a s heights forms m0) {x : BitVec 64} {n : Nat}
    (hr : ReadIn m0 x n N (wsL m0)) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange x n q := by
  intro hx
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange (hr.2.2 ⟨oA m0, 24⟩ (by simp [wsL])) hr.1.2
      (Pre.out h).2.1 hx hq
  · exact NativeRustcVm.Apart.not_inRange (hr.2.2 ⟨tA m0, tstateBytes⟩ (by simp [wsL])) hr.1.2
      (Pre.ts h).footprint.1.2 hx hq
  · exact NativeRustcVm.Apart.not_inRange (hr.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp [wsL]))
      hr.1.2 (ev_noWrap h) hx hq

omit [Labels] in
/-- An input is apart from the stack arguments. -/
theorem in_args {x : BitVec 64} {n : Nat} (hr : ReadIn m0 x n N (wsL m0)) :
    NativeRustcVm.Apart x n (argA m0) 32 :=
  hr.2.2 ⟨argA m0, 32⟩ (by simp [wsL])

/-- An output is not a byte of the read-only data. -/
theorem outs_not_rodata (h : TableTermsPre a s heights forms m0) {q : BitVec 64} (hq : outs m0 q)
    (t : NativeRustcVm.Data.Item) : ¬ NativeRustcVm.InRange (rodataAddr t) t.bytes.length q := by
  have hT := RodataAt.noWrap (Pre.tables h) t
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.ro h t) (Pre.out h).2.1 hT hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.rt h t) (Pre.ts h).footprint.1.2 hT hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.re h t) (ev_noWrap h) hT hq

/-! ## Inputs in a body -/

/-- **An input** in a body: its bytes the entry's. -/
theorem same_in (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.NoWrap x n) (hst : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8))
    (hout : ∀ q, outs m0 q → ¬ NativeRustcVm.InRange x n q) : Same m0.dmem d.dmem x n :=
  Same.of_sameOutside hb.same fun j hj hq ↦ by
    have hin : NativeRustcVm.InRange x n (x + BitVec.ofNat 64 j) :=
      NativeRustcVm.inRange_add hj (by unfold NativeRustcVm.NoWrap at hx; omega)
    rcases hq with hq | hq
    · exact hout _ hq hin
    · exact NativeRustcVm.Apart.not_inRange hst hx (stack_noWrap h) hin (inRange_mono hq (by omega))

theorem same_readIn (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {x : BitVec 64} {n : Nat}
    (hr : ReadIn m0 x n N (wsL m0)) : Same m0.dmem d.dmem x n :=
  same_in h hb hr.1.2 hr.2.1 fun _ hq ↦ outs_not_in h hr hq

/-- **The stack arguments** in a body. -/
theorem args_same (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) : Same m0.dmem d.dmem (argA m0) 32 := by
  refine same_in h hb (args_noWrap h) ?_ fun _ hq ↦ outs_not_args h hq
  unfold NativeRustcVm.Apart
  rw [argA_toNat h, stk h]
  have := spN h
  omega

omit [Labels] in
theorem tables_length : (NativeRustcVm.Data.Item.bytes .tables).length = 240 := by
  rw [tables_bytes, NativeRustcVm.Transcript.length_flatMap_wordBytes, tablesWords_length]

/-- **`TABLES`** in a body. -/
theorem tables_same (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) : Same m0.dmem d.dmem T 240 := by
  have hnw := RodataAt.noWrap (Pre.tables h) .tables
  have hap := RodataAt.apart (Pre.tables h) .tables
  rw [tables_length] at hnw hap
  exact same_in h hb hnw hap fun q hq ↦ by
    have := outs_not_rodata h hq .tables
    rwa [tables_length] at this

/-- **A word of `TABLES`** in a body. -/
theorem tword (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {j : Nat} (hj : j < 30) :
    wordOf d.dmem (T + BitVec.ofNat 64 (8 * j)) = tablesWords.getD j 0 := by
  have hb' := RodataAt.bytesAt (Pre.tables h) .tables
  rw [tables_bytes] at hb'
  have hw : NativeRustcVm.WordsAt d.dmem T tablesWords :=
    WordsAt.of_same hb' (tables_same h hb) (by rw [tablesWords_length])
  have hj' : j < tablesWords.length := by rw [tablesWords_length]; exact hj
  rw [NativeRustcVm.wordOf_of_wordAt (hw.getElem hj'), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj', Option.getD_some]

/-- **Word `o` of table `i`'s entry** in a body. -/
theorem tw_get (h : TableTermsPre a s heights forms m0) {k : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) k d) {i o : Nat} (hi : i < 6) (ho : o < 5) :
    wordOf d.dmem (T + BitVec.ofNat 64 (40 * i) + BitVec.ofNat 64 (8 * o)) =
      tablesWords.getD (5 * i + o) 0 := by
  rw [NativeRustcVm.addr_add_add, show 40 * i + 8 * o = 8 * (5 * i + o) by omega]
  exact tword h hb (by omega)

/-- **Stack argument `j`** in a body. -/
theorem arg_word (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {j : Nat} (hj : j < 4) :
    (wordOf d.dmem (argA m0 + BitVec.ofNat 64 (8 * j))).toBitVec = stackArg m0 j := by
  have hs := (args_same h hb).sub (o := 8 * j) (k := 8) (by omega)
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ hs i hi]
  unfold stackArg argA
  rw [NativeRustcVm.addr_add_add (rspOf m0) 8 (8 * j)]

end

end

end NativeRustcVmX64.Tables.TableTerms
