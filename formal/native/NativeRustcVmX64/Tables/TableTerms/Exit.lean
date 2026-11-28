module

public import NativeRustcVmX64.Tables.TableTerms.Entry
public import NativeRustcVmX64.Tables.TableTerms.Run

/-!
# `table_terms`: the exits (x86-64)

`b16` (`NativeRustcVmX64.Vm.TableTerms.label_7`) restores the registers and returns (`exit16`). `b15` (`NativeRustcVmX64.Vm.TableTerms.label_6`)
writes `None` at `out` (`exit_none`: the model's run fails). `b14` writes `Some` of the running
sum at `out` (`exit_some`: after the sixth table).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **The epilogue** (`b16`): the registers restored, `ret`; the memory the block's. -/
theorem exit16 (hp : Placed code k) (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 8 d)
    (hpost : ∀ d' : MachineData, d'.dmem = d.dmem →
      OptEWAt d'.dmem (oA m0) ((R heights forms m0 s).map (·.1.1)) ∧
      (∀ x s', R heights forms m0 s = some (x, s') → TableEvalsAt d'.dmem (ev m0) x.2) ∧
      NextAt d'.dmem (tA m0) a (R heights forms m0 s)) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b16Offset)⟩ := by
  obtain ⟨hepi, hmem⟩ := ok_b16
  refine Bd.done (st := ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b16Offset)⟩) hb (Pre.stack h) (by rw [N_eq]; omega)
    (infix_of b16_in_code (by simp [b16]) hp) exit_b16 rfl
    (match_body hb ⟨rfl, trivial⟩ trivial) hepi hmem fun st' hpc hrsp hsv hd ↦ ?_
  obtain ⟨p1, p2, p3⟩ := hpost st'.data hd
  refine ⟨hpc, hrsp, p1, p2, p3, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hb.same fun q hq ↦ hq.elim
    (fun h ↦ h.elim .inl fun h ↦ h.elim (.inr ∘ .inl) (.inr ∘ .inr ∘ .inl))
    (fun h ↦ .inr (.inr (.inr h)))

/-- `out` as region 1 of a block's environment. -/
theorem out_env (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 8 d) (hw : FW m0 d (cws m0)) :
    (E m0 d [(oA m0, 24)] 0).WF ∧ Match (E m0 d [(oA m0, 24)] 0) outS d := by
  refine ⟨wf_out h hb.fr.kept, match_body hb ⟨rfl, rfl, trivial⟩ ⟨?_, trivial⟩⟩
  show (Sym.load 0 8 8).eval (E m0 d [(oA m0, 24)] 0) = oA m0 + BitVec.ofInt 64 0
  rw [ld0 (hw (8, .ofBitVec (oA m0)) (by simp [cws]))]
  show oA m0 = oA m0 + BitVec.ofInt 64 0
  rw [ofInt_zero64, BitVec.add_zero]

/-- The memory after a block writing only `out`. -/
theorem out_same {d d' : MachineData} {Sy : SState}
    (hm : Match (E m0 d [(oA m0, 24)] 0) Sy d') (hwf : (E m0 d [(oA m0, 24)] 0).WF)
    (hmid : MidOk 272 8 slots Sy = true) (hW : WrOk Sy [1] = true) :
    NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 272) 272 q ∨
        NativeRustcVm.InRange (oA m0) 24 q) :=
  same_block hwf hm (writesIn_of_mid hmid) (belowRet_of_mid hmid) hW fun r hr x hx q hq ↦ by
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    exact hq

/-- A change of the frame or `out` keeps the `TState` and the entries. -/
theorem out_keep (h : TableTermsPre a s heights forms m0) {d d' : Mem 64}
    (hs : NativeRustcVm.SameOutside d d'
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 272) 272 q ∨
        NativeRustcVm.InRange (oA m0) 24 q)) (hk : Kept d d') :
    (∀ {s' : TState}, TStateAt d (tA m0) a s' → TStateAt d' (tA m0) a s') ∧
      Same d d' (ev m0) tableEvalsBytes := by
  have c := ctx h
  have hFst : ∀ q, NativeRustcVm.InRange (stackBelow m0 272) 272 q →
      NativeRustcVm.InRange (stackBelow m0 N) N q :=
    fun q hq ↦ inRange_frame_stack (Pre.stack h).2.1 (Pre.stack h).1 (by rw [N_eq]; omega) hq
  refine ⟨fun hts ↦ hts.frame hk (fun q hq ↦ hq.elim (fun hq ↦ c.stack_not_t (hFst q hq))
    (fun hq ↦ c.out_not_t (Pre.out h) hq)) hs, Same.of_sameOutside hs fun j hj hq ↦ ?_⟩
  have hin := NativeRustcVm.inRange_add (a := ev m0) hj
    (by have := ev_noWrap h; unfold NativeRustcVm.NoWrap at this; omega)
  rcases hq with hq | hq
  · exact outs_not_stackN h (.inr (.inr hin)) (hFst _ hq)
  · exact NativeRustcVm.Apart.not_inRange (Pre.out_ev h) (Pre.out h).2.1 (ev_noWrap h) hq hin

/-- **A failed run** (`b15`): `None` at `out`. -/
theorem exit_none (hp : Placed code k) (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 8 d) (hw : FW m0 d (cws m0))
    (hr : R heights forms m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b15Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := out_env h hb hw
  refine exec_then (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf nofun hm
    fun st hm1 hpc ↦ ?_
  obtain ⟨-, hmid, hW, -, w0⟩ := ok_b15
  have hb1 := Bd.step hb (Pre.stack h) (by rw [N_eq]; omega) hwf hm1 hmid
    (fun p hp ↦ (slots_le p hp).2) hW fun r hr x hx q hq ↦ by
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact .inl hq
  have hw0 : NativeRustcVm.WordAt st.data.dmem (oA m0) 0 := by
    have := wordAt_written hm1 (r := 1) (o := 0) rfl (by omega) w0 (w := 0) rfl
    rwa [off_zero] at this
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b15_next)))
    (exit16 hp h hb1 fun d' hd ↦ ⟨?_, fun x s' h' ↦ (by rw [hr] at h'; cases h'),
      fun x s' h' ↦ (by rw [hr] at h'; cases h')⟩)
  rw [hr, hd]
  exact hw0

/-- **After the sixth table** (`b14`): `Some` of the running sum at `out`. -/
theorem exit_some (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6) {acc : Acc} {si : TState} {d : MachineData}
    (H : Head a s heights forms m0 6 acc si d) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b14Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := out_env h H.bd H.fw
  refine exec_then (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf nofun hm
    fun st hm1 hpc ↦ ?_
  obtain ⟨-, hmid, hW, -, l0, l8, l16⟩ := ok_b14
  have hb1 := Bd.step H.bd (Pre.stack h) (by rw [N_eq]; omega) hwf hm1 hmid
    (fun p hp ↦ (slots_le p hp).2) hW fun r hr x hx q hq ↦ by
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact .inl hq
  obtain ⟨kts, kev⟩ := out_keep h (out_same hm1 hwf hmid hW) (hm1.kept hwf)
  have hrun : R heights forms m0 s = some ((acc.2.1, acc.2.2), si) := by
    rw [R_eq hh hf, H.run]; rfl
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (lbl_7 hp)) (exit16 hp h hb1 fun d' hd ↦ ?_)
  rw [hrun, hd]
  refine ⟨⟨?_, ?_⟩, fun x s' h' ↦ ?_, fun x s' h' ↦ ?_⟩
  · have := wordAt_written hm1 (r := 1) (o := 0) rfl (by omega) l0 (w := 1) rfl
    rwa [off_zero] at this
  · rw [ewAt_iff, off_off]
    exact ⟨wordAt_written hm1 (r := 1) (o := 8) rfl (by omega) l8 H.rdx,
      wordAt_written hm1 (r := 1) (o := 16) rfl (by omega) l16 H.rcx⟩
  · cases h'
    refine ⟨by rw [H.osz]; rfl, fun j hj ↦ ?_⟩
    have hj6 : j < 6 := by rw [H.osz] at hj; exact hj
    have hs := kev.sub (o := 1968 * j) (k := 1968)
      (by unfold tableEvalsBytes nTables tableEvalBytes; omega)
    have he := H.evs j hj
    exact ⟨BufEWAt.of_same he.1 hs (by decide),
      BufEWAt.of_same he.2 (hs.sub (o := valuesOff) (k := 1480) (by decide)) (by decide)⟩
  · cases h'
    exact kts H.ts

end

end NativeRustcVmX64.Tables.TableTerms
