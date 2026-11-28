module

public import NativeRustcVmX64.Tables.TableTerms.Exit

/-!
# `table_terms`: what the iteration over table `i` keeps (x86-64)

A body at a call (`Bd.at0`: `Sumcheck.At` for its callee's contract), a call changing outputs and
its stack (`call_bd`); the iteration's outputs across a change of the stack and entry `i`'s first
`488` bytes (`It.step`); an entry over bytes that stayed the same (`TableEvalAt.of_same'`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeRustcVm (wordOf ewsOf)

public section

/-- An entry's point and evaluations over bytes that stayed the same. -/
theorem TableEvalAt.of_same' {d d' : Mem 64} {p : BitVec 64} {x : Array EW × Array EW}
    (hx : TableEvalAt d p x) (hs : Same d d' p 1968) : TableEvalAt d' p x :=
  ⟨BufEWAt.of_same hx.1 hs (by decide),
    BufEWAt.of_same hx.2 (hs.sub (o := valuesOff) (k := 1480) (by decide)) (by decide)⟩

variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- The frame below its return address is in the stack. -/
theorem fr_stack (h : TableTermsPre a s heights forms m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 272) 272 q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  inRange_frame_stack (Pre.stack h).2.1 (Pre.stack h).1 (by rw [N_eq]; omega) hq

/-- **At a call** from the body. -/
theorem Bd.at0 (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) : At m0 272 d :=
  ⟨by rw [hb.rsp_at (by omega)], hb.fr.kept, fun i hi ↦ hb.same _ fun hq ↦ by
    have hin : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
      inRange_off_self hi (by omega)
    rcases hq with hq | hq
    · exact outs_not_rc h hq hin
    · exact (ctx h).not_rc_stack hq hin⟩

/-- **A call from the body** changing outputs and its stack. -/
theorem call_bd (h : TableTermsPre a s heights forms m0) {d d' : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    (hRo : ∀ q, Ro q → outs m0 q) : Bd m0 272 N slots (outs m0) 8 d' :=
  hb.call_apart_at (Pre.stack h) (by rw [N_eq]; omega) (Nat.zero_le _) hs hrsp
    (by simpa using hle) hso (fun q hq ↦ .inl (hRo q hq))
    (fun q hq hf ↦ outs_not_frame h (hRo q hq) hf)
    (fun p hp ↦ ⟨Nat.zero_le _, (slots_le p hp).2⟩)

/-- The callee's stack is in the function's. -/
theorem callee_stack (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  (hb.callee_in (Pre.stack h) (Nat.zero_le _) (by simpa using hle) hq).1

/-- A byte from entry `i`'s byte `488` is not one of its first `488`. -/
theorem not_e488 (h : TableTermsPre a s heights forms m0) {i j : Nat} (hi : i < 6)
    (hj : j < 1480) :
    ¬ NativeRustcVm.InRange (evi m0 i) 488 (evi m0 i + BitVec.ofNat 64 488 + BitVec.ofNat 64 j) := by
  rw [NativeRustcVm.addr_add_add]
  have := NativeRustcVm.not_inRange_sub (a := evi m0 i) (o := 0) (m := 488) (evi_noWrap h hi)
    (by omega) (show 488 + j < 1968 by omega) (.inr (by omega))
  rwa [NativeRustcVm.addr_add_zero] at this

/-- **The finished entries** across a change of the stack, entry `i` and the `TState`. -/
theorem evs_keep (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d d' : Mem 64}
    {W : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' W)
    (hW : ∀ q, W q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange (evi m0 i) 1968 q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q)
    {o : Array (Array EW × Array EW)} (ho : o.size ≤ i)
    (hx : ∀ j (hj : j < o.size), TableEvalAt d (evi m0 j) o[j]) :
    ∀ j (hj : j < o.size), TableEvalAt d' (evi m0 j) o[j] := by
  intro j hj
  refine TableEvalAt.of_same' (hx j hj) (Same.of_sameOutside hs fun l hl hq ↦ ?_)
  have hj6 : j < 6 := by omega
  have hin : NativeRustcVm.InRange (evi m0 j) 1968 (evi m0 j + BitVec.ofNat 64 l) :=
    NativeRustcVm.inRange_add hl (by norm_num)
  have hev := evi_in h hj6 hin
  rcases hW _ hq with hq | hq | hq
  · exact outs_not_stackN h (.inr (.inr hev)) hq
  · exact NativeRustcVm.Apart.not_inRange (evi_apart h hj6 hi (by omega)) (evi_noWrap h hj6)
      (evi_noWrap h hi) hin hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.evs h).2.2.1 (ev_noWrap h)
      (Pre.ts h).footprint.1.2 hev hq

/-- The `TState` across a change of the stack and entry `i`. -/
theorem ts_keep (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d d' : Mem 64}
    {W : BitVec 64 → Prop} (hk : Kept d d') (hs : NativeRustcVm.SameOutside d d' W)
    (hW : ∀ q, W q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange (evi m0 i) 1968 q) {s' : TState}
    (hts : TStateAt d (tA m0) a s') : TStateAt d' (tA m0) a s' :=
  hts.frame hk (fun q hq ↦ (hW q hq).elim (ctx h).stack_not_t
    fun hq ↦ (ctx h).out_not_t (evi_out h hi) hq) hs

/-- **Across a change** of the stack and entry `i`'s first `488` bytes. -/
theorem It.step (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6)
    {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState} {d d' : MachineData}
    (H : It a m0 i o xs s' d) (hk : Kept d.dmem d'.dmem) {W : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem W)
    (hW : ∀ q, W q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange (evi m0 i) 488 q) : It a m0 i o xs s' d' := by
  have hW' : ∀ q, W q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange (evi m0 i) 1968 q := fun q hq ↦ (hW q hq).imp_right fun h' ↦
    inRange_mono h' (by omega)
  refine ⟨ts_keep h hi hk hs hW' H.ts, ?_, evs_keep h hi hs (fun q hq ↦ (hW' q hq).imp_right .inl)
    (by rw [H.osz]) H.evs, H.osz⟩
  refine BufEWAt.of_same H.vals (n := 1480) (Same.of_sameOutside hs fun j hj hq ↦ ?_) (by omega)
  rcases hW _ hq with hq | hq
  · have hin : NativeRustcVm.InRange (evi m0 i) 1968
        (evi m0 i + BitVec.ofNat 64 488 + BitVec.ofNat 64 j) := by
      rw [NativeRustcVm.addr_add_add]
      exact NativeRustcVm.inRange_add (by omega) (by norm_num)
    exact outs_not_stackN h (.inr (.inr (evi_in h hi hin))) hq
  · exact not_e488 h hi hj hq

end

end NativeRustcVmX64.Tables.TableTerms
