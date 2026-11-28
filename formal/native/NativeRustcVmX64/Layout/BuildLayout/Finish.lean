module

public import NativeRustcVmX64.Layout.BuildLayout.Kappas
public import NativeRustcVmX64.Code.Vm.PlacementsOf.Names

/-!
# `build_layout` on x86-64: `placements_of`, the stack's log-size, the return

`b16` calls `placements_of` on the frame's `kappas` and the layout's placements (offset `120`);
`b17` checks it returned `Some`; `b18` stores the stack's log-size; `b20` returns `1`. The words
stored and the placements make the model's layout (`layoutWAt_of`).
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BuildLayout NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

public section

variable {m0 : MachineData} {bc : Array UInt64}

theorem not_inRange_off {b : BitVec 64} {N j : Nat} (hj : N ≤ j) (hj' : j < 2 ^ 64) :
    ¬ NativeRustcVm.InRange b N (off b j) := by
  unfold NativeRustcVm.InRange
  rw [show off b j - b = BitVec.ofNat 64 j by simp [off], BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj']
  omega

/-- A word kept where memory changed elsewhere. -/
theorem wordAt_keep {d d' : Mem 64} {a : BitVec 64} {w : UInt64} {Rc : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' Rc) {o n : Nat} (ho : o + 8 ≤ n)
    (hR : ∀ i < n, ¬ Rc (off a i)) (h : WordAt d (off a o) w) : WordAt d' (off a o) w :=
  bytesAt_congr h fun j hj ↦ by
    have hj8 : j < 8 := by simpa [NativeRustcVm.length_wordBytes] using hj
    rw [show off a o + BitVec.ofNat 64 j = off a (o + j) from off_off a o j]
    exact hs _ (hR _ (by omega))

/-- Words kept where memory changed elsewhere. -/
theorem wordsAt_keep {d d' : Mem 64} {a : BitVec 64} {ws : List UInt64} {Rc : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' Rc) (hR : ∀ o < 8 * ws.length, ¬ Rc (off a o))
    (h : WordsAt d a ws) : WordsAt d' a ws :=
  NativeRustcVm.wordsAt_iff.mpr fun i hi ↦
    wordAt_keep (o := 8 * i) hs (by omega) hR (NativeRustcVm.wordsAt_iff.mp h i hi)

/-- A placement kept where memory changed elsewhere. -/
theorem PlacementWAt.keep {d d' : Mem 64} {a : BitVec 64} {p : Option Placement}
    {Rc : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' Rc)
    (hR : ∀ i < 24, ¬ Rc (off a i)) (h : PlacementWAt d a p) : PlacementWAt d' a p := by
  cases p with
  | none =>
    show WordAt d' a 0
    have := wordAt_keep (o := 0) hs (by decide) hR (by rw [off_zero]; exact h)
    rwa [off_zero] at this
  | some q =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    have h0' := wordAt_keep (o := 0) hs (by decide) hR (by rw [off_zero]; exact h0)
    rw [off_zero] at h0'
    exact ⟨h0', h1, h2, wordAt_keep hs (by decide) hR h3, wordAt_keep hs (by decide) hR h4⟩

theorem rng6 {A : Nat} (hA : 7824 ≤ A) : A - 7824 + (6464 + 8) ≤ A - 1312 := by omega
theorem rng7 {A L : Nat} (hLA : L + 3912 ≤ A - 7824 ∨ A + 8 ≤ L) (hA : 7824 ≤ A) :
    L + 120 + 3792 ≤ A - 7824 ∨ A - 7824 + (6464 + 8) ≤ L + 120 := by omega
theorem rng8 {A L : Nat} (hLA : L + 3912 ≤ A - 7824 ∨ A + 8 ≤ L) (hA : 7824 ≤ A) :
    A - 1312 + 1264 ≤ L + 120 ∨ L + 120 + 3792 ≤ A - 1312 := by omega

section
variable [Labels]

/-- The frame's bytes: not in a callee's stack nor the layout. -/
theorem Facts.frame_not (hF : Facts bc m0) {d : MachineData} (hb : B m0 0 d) {n' : Nat}
    (hn' : 1360 + n' ≤ 7824) {n o : Nat} (hon : o + n ≤ 3912) {j : Nat} (hj : j < 1368) :
    ¬ (NativeRustcVm.InRange (off (ll m0) o) n (off (fb m0) j) ∨
      NativeRustcVm.InRange (stackBelow d n') n' (off (fb m0) j)) := by
  have hin := fb_in (F := 1360) hF.stack (by decide) (j := j) (by omega)
  rintro (h | h)
  · exact hF.R_frame (hF.lay_R hon h) hin
  · exact (hb.callee hF.stack hn' h).2 hin

/-- The layout's bytes: not in a callee's stack. -/
theorem Facts.lay_not_callee (hF : Facts bc m0) {d : MachineData} (hb : B m0 0 d) {n' : Nat}
    (hn' : 1360 + n' ≤ 7824) {j : Nat} (hj : j < 3912) :
    ¬ NativeRustcVm.InRange (stackBelow d n') n' (off (ll m0) j) := fun h ↦
  not_inRange_of_apart hF.lo hF.lr.2 (noWrap_stackBelow hF.stack)
    (inRange_off_self (by rw [layoutBytes_eq]; exact hj) (by rw [layoutBytes_eq]; decide))
    (inRange_mono' (hb.callee hF.stack hn' h).1 (by omega))

end

variable [Host] {k : Nat}

/-- **`b16` to `b20`: `placements_of`, the stack's log-size, the return.** -/
theorem finish (hp : Placed code k)
    (hpl : Spec (Labels.label NativeRustcVmX64.Vm.PlacementsOf.entryLabel) PlacementsOfPre PlacementsOfPost) (hF : Facts bc m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b16Offset)) (hs : SK m0 st.data) :
    Eventually (step1 Host.exe) (Post bc m0) st := by
  obtain ⟨hA, hA1, hA2, hL, hLA⟩ := hF.num
  have hc := hs.chk
  have hrs := rowsOf_size m0
  have hr := rows_le hc
  have hlm30 : lmN m0 ≤ 30 := hc.2.2.1
  have hlb30 : bitLength (nN m0) - 5 ≤ 30 := hc.2.2.2.2
  have hres := model_some hF.size hs.pow2 hc
  -- `b16`
  obtain ⟨hok, h0, hsi, hdi, hK16⟩ := ok_b16
  have hwf0 := fr_wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b16Offset + b16.length)).toBitVec)
    hs.b hF.stack (by decide)
  refine run0 (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b16Offset + b16.length)).toBitVec) hF
    (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b16 (fun _ _ ↦ rfl) hpc hs.b hok
    fun st1 hm1 hpc1 hb1 ↦ ?_
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (fb m0) 8) := sameOutside_low hwf0 hm1 rfl (by decide) h0
  have hdi1 : reg st1.data .rdi = off (fb m0) 48 := (hm1.regs .rdi _ hdi).trans hs.r12
  have hsi1 : reg st1.data .rsi = off (ll m0) 120 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hsi]
    show BinOp.apply .add .W64 (reg st.data .r13) (BitVec.ofNat 64 120) = _
    simp only [BinOp.apply, low_W64, ext_W64, hs.r13]
  have k1 := fun r (hr : r ∈ cs) ↦ kreg hm1 hK16 hr
  have hfr8 : ∀ {j : Nat}, 8 ≤ j → j < 1368 → ¬ NativeRustcVm.InRange (fb m0) 8 (off (fb m0) j) :=
    fun h1 h2 ↦ not_inRange_off h1 (by omega)
  have hkap1 : WordsAt st1.data.dmem (off (fb m0) 48)
      (natWords (columnKappas (lmN m0) (bitLength (nN m0) - 5) (heightsF (rowsOf m0)))) :=
    wordsAt_keep hs1 (fun o ho ↦ by
      rw [off_off]
      have : (natWords (columnKappas (lmN m0) (bitLength (nN m0) - 5)
        (heightsF (rowsOf m0)))).length = 158 := by simp [natWords, columnKappas_size']
      exact hfr8 (by omega) (by omega)) hs.kap
  have hn : natsOf st1.data (reg st1.data .rdi) columnCountW =
      columnKappas (lmN m0) (bitLength (nN m0) - 5) (heightsF (rowsOf m0)) := by
    rw [hdi1]
    exact natsOf_of_words hkap1 (fun x hx ↦ by have := cols_lt hrs hlm30 hlb30 hr x hx; omega)
      (by rw [columnKappas_size']; rfl)
  have hsp1 := hb1.rsp0
  have hcs : stackBelow st1.data 6464 = stackBelow m0 7824 :=
    stackBelow_callee hsp1 (by show 1360 + 6464 ≤ _; omega)
  have hsb := hF.sb_toNat
  have hk48 : (off (fb m0) 48).toNat = (rspOf m0).toNat - 1312 := by
    rw [hF.off_toNat (by decide)]; omega
  have hl120 : (off (ll m0) 120).toNat = (ll m0).toNat + 120 := toNat_off (by omega)
  have hfm : NativeRustcVm.Mapped st1.data.dmem (fb m0) 1368 :=
    Mapped.keeps (frame_mapped hF.stack (by decide)) hb1.fr.kept
  have hlm : NativeRustcVm.Mapped st1.data.dmem (ll m0) 3912 :=
    Mapped.keeps hF.lr.1 hb1.fr.kept
  have hpre : PlacementsOfPre st1.data := by
    refine ⟨hb1.stackOk hF.stack (by decide), fun t ↦ ⟨?_, hF.rod.noWrap t, ?_⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · refine (hF.rod.bytesAt t).of_sameOutside hb1.same fun i hi hq ↦ hq.elim (fun h ↦ ?_) fun h ↦ ?_
      · exact (hF.lrod t).symm.not_inRange_add (hF.rod.noWrap t) hF.lr.2 hi h
      · exact (hF.rod.apart t).not_inRange_add (hF.rod.noWrap t) (noWrap_stackBelow hF.stack) hi
          (inRange_mono' h (by omega))
    · show NativeRustcVm.Apart _ _ (stackBelow st1.data 6464) (6464 + 8)
      rw [hcs]
      have := hF.rod.apart t
      unfold NativeRustcVm.Apart at this ⊢
      omega
    · rw [hdi1]
      exact ⟨mapped_off hfm (by decide),
        (show (off (fb m0) 48).toNat + 1264 ≤ 2 ^ 64 by rw [hk48]; omega)⟩
    · rw [hdi1]
      show _ + _ ≤ (stackBelow st1.data 6464).toNat ∨ (stackBelow st1.data 6464).toNat + (6464 + 8) ≤ _
      rw [hcs]
      exact (show (off (fb m0) 48).toNat + 1264 ≤ (stackBelow m0 7824).toNat ∨
        (stackBelow m0 7824).toNat + (6464 + 8) ≤ (off (fb m0) 48).toNat by
        rw [hk48, hsb]; exact .inr (rng6 hA1))
    · rw [hsi1]
      exact ⟨mapped_off hlm (by decide),
        (show (off (ll m0) 120).toNat + 3792 ≤ 2 ^ 64 by rw [hl120]; omega)⟩
    · rw [hsi1]
      show _ + _ ≤ (stackBelow st1.data 6464).toNat ∨ (stackBelow st1.data 6464).toNat + (6464 + 8) ≤ _
      rw [hcs]
      exact (show (off (ll m0) 120).toNat + 3792 ≤ (stackBelow m0 7824).toNat ∨
        (stackBelow m0 7824).toNat + (6464 + 8) ≤ (off (ll m0) 120).toNat by
        rw [hl120, hsb]; exact rng7 hLA hA1)
    · rw [hsi1]
      intro t
      have := hF.lrod t
      unfold NativeRustcVm.Apart at this ⊢
      rw [hl120]
      rw [layoutBytes_eq] at this
      show _ + 3792 ≤ _ ∨ _
      omega
    · rw [hdi1, hsi1]
      exact (show (off (fb m0) 48).toNat + 1264 ≤ (off (ll m0) 120).toNat ∨
        (off (ll m0) 120).toNat + 3792 ≤ (off (fb m0) 48).toNat by
        rw [hk48, hl120]; exact rng8 hLA hA1)
    · rw [hn]; exact cols_lt hrs hlm30 hlb30 hr
    · have hgbytes := got_keep hF.got hF.stack (writes := [(ll m0, layoutBytes)])
        (by simp) (by simpa using (noWrap_iff.mp hF.lr.2))
        (hb1.same.mono (by intro q h; simpa [R, SS_eq] using h))
      apply got_callee hF.got hgbytes hb1.rsp0 hF.stack.1 (by decide)
      intro l hl a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [hdi1]
        exact got_apart_frame hF.got hF.stack hl (by decide) (by dsimp only; decide)
      · rw [hsi1]
        exact Transcript.Apart.sub ((hF.got.1 l hl).2.2.2 (ll m0, layoutBytes) (by simp))
          (by dsimp only; rw [hl120]; omega)
          (by change (off (ll m0) 120).toNat + 3792 ≤ (ll m0).toNat + 3912
              rw [hl120])
  refine call_then hpc1 hpl hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨h0', h1, hsz, hpw, hch, hsv⟩ := hpost
  rw [hn] at h1 hsz hpw
  rw [hsi1] at hch hpw
  rw [show placementsOfStack = 6464 from rfl] at hch
  have hb2 : B m0 8 st2.data := hb1.call hsv hrsp2 hch
    (fun q hq ↦ hq.elim (fun h ↦ .inl (hF.lay_R (o := 120) (by decide) h))
      fun h ↦ .inr (hb1.callee hF.stack (by decide) h).1)
    (fun p hp i hi ↦ hF.frame_not hb1 (by decide) (by decide)
      (by have := slots_le p hp; omega))
    (fun j hj ↦ hF.frame_not hb1 (by decide) (by decide) (by omega))
  have hW2 : Ws st2.data.dmem (ll m0) (wsK0 m0) := by
    refine (hs.ws.same hs1 fun p hp i hi h ↦ ?_).same hch fun p hp i hi h ↦ ?_
    · have := wsK_le p hp
      have hin := inRange_off_self (b := ll m0) (j := p.1 + i) (N := 3912) (by omega) (by decide)
      exact hF.R_frame (by rw [R, layoutBytes_eq]; exact hin) (inRange_mono' h (by decide))
    · have := wsK_le p hp
      rcases h with h | h
      · exact absurd ((inRange_off_iff (by omega) (by decide)).mp h) (by omega)
      · exact hF.lay_not_callee hb1 (by decide) (by omega) h
  -- `b17`
  obtain ⟨ok17, mem17, hK17⟩ := ok_b17
  refine step0 hF (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b17 nofun (hpc2.trans rfl)
    hb2 ok17 mem17 fun st3 hm3 hpc3 hb3 hd3 ↦ ?_
  have k3 := fun r (hr : r ∈ Reg64.rax :: .rdx :: cs) ↦ kreg hm3 hK17 hr
  have hcond : (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not.eval
      (frameEnv m0 st2.data 1360 [] (fun _ ↦ 0) 0) = false := by
    show (!(SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).eval _) = false
    rw [eq_eval, lit_eval _ (by decide)]
    show (!decide ((reg st2.data .rax).toNat = 1)) = false
    rw [h0']; rfl
  simp only [PcOk, hcond, Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `b18`
  have h133 : reg st3.data .r13 = ll m0 := by
    exact (k3 .r13 (by simp [cs])).trans ((hsv.1 .r13 rfl).trans ((k1 .r13 (by simp [cs])).trans hs.r13))
  have hwf := wfL (ret := 0) hF hb3
  obtain ⟨ok18, hr18, miss18, w18, hK18⟩ := ok_b18
  refine exec_at (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b18 hwf nofun
    (hpc3.trans rfl) (matchL hb3 h133) fun st4 hm4 hpc4 ↦ ?_
  have hb4 : B m0 8 st4.data := hb3.of_block hF.stack (by decide) hwf hm4 ok18 slots_le restL
  have hs4 : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem
      (NativeRustcVm.InRange (ll m0) 120) := fun q hq ↦ hm4.get?_mem0 hwf fun hW ↦ by
    obtain ⟨w, hw, b, sz, hb, hin⟩ := written_in hwf hm4 (writesIn_of ok18) hW
    rw [hr18 w hw] at hb
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact hq hin
  have hsl : (reg st3.data .rdx).toNat = (layoutF bc (lmN m0) (bitLength (nN m0) - 5)
      (rowsOf m0)).stackLog := by
    rw [k3 .rdx (by simp)]; exact h1
  have hW4 : Ws st4.data.dmem (ll m0) (wsK0 m0) :=
    Ws.keep hwf hm4 (writesIn_of ok18) (r := 1) rfl wsK_le (misses_of miss18 rfl)
      (hW2.of_eq hd3)
  have hS16 : WordAt st4.data.dmem (off (ll m0) 16)
      (layoutF bc (lmN m0) (bitLength (nN m0) - 5) (rowsOf m0)).stackLog.toUInt64 :=
    w_write hm4 (r := 1) rfl (by decide) w18 (by
      show (reg st3.data .rdx).toNat = _
      rw [hsl, toNat_toUInt64 (by rw [← hsl]; exact BitVec.isLt _)])
  have hax4 : reg st4.data .rax = 1#64 := by
    rw [kreg hm4 hK18 (by simp), k3 .rax (by simp)]; exact h0'
  simp only [PcOk] at hpc4
  -- the epilogue
  refine Eventually.mono (epi (b := true) hp hF (hpc4.trans (hp.label NativeRustcVmX64.Vm.BuildLayout.label_18_at)) hb4
    (by rw [hax4]; rfl)) fun s ⟨hs1', hs2', hs3', hs4', hs5', hs6'⟩ ↦
      ⟨hs1', hs2', ?_, fun L hL ↦ ?_, hs4', hs5'⟩
  · show OkAl s.data (buildLayout bc (lmN m0) (rowsOf m0)).isSome
    rw [hres]; exact hs3'
  · change buildLayout bc (lmN m0) (rowsOf m0) = some L at hL
    rw [hres] at hL
    cases hL
    rw [hs6']
    refine layoutWAt_of hrs hlm30 hlb30 hr hW4 (by rw [← hsl]; exact BitVec.isLt _) hS16
      fun c hc ↦ ?_
    have hc' : c < 158 := lt_of_lt_of_eq hc hsz
    have h2 : PlacementWAt st2.data.dmem (off (ll m0) (120 + placementBytes * c))
        (layoutF bc (lmN m0) (bitLength (nN m0) - 5) (rowsOf m0)).placements[c] := by
      have := hpw c hc
      rwa [off_off] at this
    rw [← hd3] at h2
    refine PlacementWAt.keep hs4 (fun i hi ↦ ?_) h2
    rw [off_off]
    exact not_inRange_off (by omega)
      (by rw [show placementBytes = 24 from rfl]; omega)

end

end NativeRustcVmX64.Layout.BuildLayout
