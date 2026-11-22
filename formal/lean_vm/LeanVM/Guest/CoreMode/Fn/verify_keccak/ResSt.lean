/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.ResSt

  `verify_keccak`'s cursor in the proof stream (`VkQ`), carried down from `verify_sub`'s front.
-/

module

public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.TermQ
public import LeanVM.Guest.Child.Reads
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# `verify_keccak`'s cursor

`VkQ J`: at an instance of `verify_keccak`, its cursor is `stream·g^p`, its table's log-height `τ`
(`tau_g = g^τ`, `9 ≤ τ ≤ 28`), and `p + vkNeed τ ≤ 8192`: room for the word before its first layer,
its twelve layers, each reading `84 + 2(τ - 3)` words, and the words after them.

`runsTo_reads`: a run of a program of `n` reads (`Child.Reads`) from a carried sponge reads at most
`n` words (`Child.run_reads`) and leaves a carried sponge. `vkQ_all`: at every honest instance of
`verify_keccak`, by `Res.insts_down`: its only caller is `verify_sub` (`Res.termCallers_all`), whose
only call of it is at `vkArgsV` (`vs_vk_sites`), whose front (`B1.VerifySub.vs_front`) puts the
cursor at `stream·g^(13 + |xsG| + |xsT|)`, the bus's GKR walk and the tables' segment run from carried
sponges (`front_carried`), so their words are at most their reads (`reads_gkrPhase`,
`reads_tablesSeg`), and the sum fits (`vk_room`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The words `verify_keccak` reads at a table of log-height `τ`: one, twelve layers of
`84 + 2(τ - 3)`, then the outputs' and the inputs' `97`. -/
def vkNeed (τ : ℕ) : ℕ := 1 + 12 * (84 + 2 * (τ - 3)) + 97

/-- **`verify_keccak`'s cursor in its stream**: `cursor = stream·g^p`, `tau_g = g^τ`, `9 ≤ τ ≤ 28`,
and room for its reads. -/
def VkQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node "verify_keccak" σ bufs kids →
    ∃ p τ, σ (.n (val% «verify_keccak» "cursor@1")) = σ (.n (val% «verify_keccak» "stream")) * gen ^ p ∧ σ (.n (val% «verify_keccak» "tau_g")) = gen ^ τ ∧ 9 ≤ τ ∧ τ ≤ 28 ∧ p + vkNeed τ ≤ 8192

/-- `verify_keccak`'s call arguments in `verify_sub`. -/
def vkArgsV : List V := [val% «verify_sub» "fs0@4", val% «verify_sub» "fs1@4", val% «verify_sub» "fs2@4", val% «verify_sub» "fs3@4", val% «verify_sub» "fs4@4", val% «verify_sub» "cursor@3", val% «verify_sub» "tau_keccak_g", val% «verify_sub» "chi", val% «verify_sub» "fs0@5~8", val% «verify_sub» "z_vals", val% «verify_sub» "slices", val% «verify_sub» "fs0@5~10", val% «verify_sub» "stream"].map .n

/-- The words of the bus after its GKR walk: the memory's two, the two finals, the bytecode's share. -/
def busRestReads : ℕ := 4 + (1 + busBits * Child.roundReads 3 + 1)

end

public section

/-! ## Reads of runs -/

/-- **A run reads at most its program's reads**, from a carried sponge, and leaves one carried. -/
theorem runsTo_reads {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α} {n : ℕ}
    {Q : α → Prop} (hR : Child.Reads p n Q) (h : RunsTo p s xs a s') {sp : Sponge} (hc : s.Carries sp) :
    xs.length ≤ n ∧ ∃ sp', s'.Carries sp' := by
  obtain ⟨sp', hc', hrun⟩ := h sp hc [] [] []
  obtain ⟨ys, hys, hl⟩ := Child.run_reads keccak256 keccakF1600 hR hrun
  simp only [List.append_nil] at hys
  rw [hys]
  exact ⟨hl, sp', hc'⟩

theorem carries_of_runsTo {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') {sp : Sponge} (hc : s.Carries sp) : ∃ sp', s'.Carries sp' := by
  obtain ⟨sp', hc', -⟩ := h sp hc [] [] []
  exact ⟨sp', hc'⟩

theorem carries_absorbAll (xs : List E) (t : ℕ) : ∀ {s : Fs} {sp : Sponge}, s.Carries sp →
    ∃ sp', (s.absorbAll xs t).Carries sp' := by
  induction xs with
  | nil => intro s sp h; exact ⟨sp, h⟩
  | cons x xs ih => intro s sp h; exact ih (carries_absorb h x t)

/-- The bus's GKR walk and its count root's check: the walk's reads. -/
theorem reads_gkrPhase (d : ℕ) :
    Child.Reads (Tables.gkrPhase d) (2 + Child.gkrReads d 0) fun _ ↦ True := by
  unfold Tables.gkrPhase
  exact Child.Reads.seq (Child.reads_verifyGkrGrandProducts d)
    (fun _ _ ↦ Child.Reads.seq (Child.Reads.require (n := 0) _) (fun _ _ ↦ trivial) (Nat.zero_le _)) le_rfl

/-- The bus after its GKR walk. -/
theorem reads_busRest (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, Child.Reads (ev w p v) 0 fun _ ↦ True) (layout : Layout) (weights : List E)
    (beta : E) (point treeValues : List E) :
    Child.Reads (Tables.busRest ev layout weights beta point treeValues) busRestReads fun _ ↦ True := by
  unfold Tables.busRest
  refine Child.Reads.seq (Child.Reads.readN 2) (fun _ _ ↦ Child.Reads.seq Child.Reads.readE (fun _ _ ↦
    Child.Reads.seq Child.Reads.readE (fun _ _ ↦
      Child.Reads.seq (Child.reads_bytecodeShare _ _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_
  · obtain ⟨share, bytecodePoint, value⟩ := r
    exact Child.Reads.seq (hev _ _ _) (fun _ _ ↦ trivial) (Nat.zero_le _)
  all_goals unfold busRestReads; omega

/-- The table phase on heights of at most `30`. -/
theorem reads_tablePhase' (layout : Layout) (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 30) (bus : BusResult) :
    Child.Reads (tablePhaseClaims layout bus) Child.tableReads fun _ ↦ True := by
  unfold tablePhaseClaims
  exact Child.Reads.seq (Child.Reads.grindP _) (fun _ _ ↦
    Child.Reads.seq Child.Reads.sampleE (fun _ _ ↦ Child.Reads.seq
      (Child.reads_tableSumcheck _ _ _ _ _ _ hh) (fun _ _ ↦ trivial) (by unfold Child.tableReads; omega))
      (by unfold Child.tableReads; omega))
    (by unfold Child.tableReads; omega)

/-- **The tables' segment**: the bus after its GKR walk, the table phase, the public input's
binding. -/
theorem reads_tablesSeg (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, Child.Reads (ev w p v) 0 fun _ ↦ True) (layout : Layout)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 30) (publicInput : Digest) (weights : List E) (beta : E)
    (point treeValues : List E) :
    Child.Reads (Tables.tablesSeg ev layout publicInput weights beta point treeValues)
      (busRestReads + Child.tableReads) fun _ ↦ True := by
  unfold Tables.tablesSeg
  refine Child.Reads.seq (reads_busRest ev hev layout weights beta point treeValues) (fun bus _ ↦
    Child.Reads.seq (reads_tablePhase' layout hh bus) (fun _ _ ↦
      Child.Reads.seq ((Child.reads_publicInputPhase layout publicInput).mono le_rfl fun _ _ ↦ trivial)
        (fun _ _ ↦ trivial) (Nat.zero_le _)) (by omega)) (by omega)

/-- **The room**: the front's words, the bus's GKR walk over fewer than `34` levels, the tables'
segment and `verify_keccak`'s layers at `τ ≤ 28` fit the stream. -/
theorem vk_room {d g t τ : ℕ} (hd : d < 34) (hg : g ≤ 2 + Child.gkrReads d 0)
    (ht : t ≤ busRestReads + Child.tableReads) (hτ : τ ≤ 28) : 13 + g + t + vkNeed τ ≤ 8192 := by
  have h1 := Child.gkrReads_le d (by omega)
  have h2 : vkNeed τ ≤ vkNeed 28 := by unfold vkNeed; omega
  have h3 : 13 + (2 + Child.gkrReadsBound) + (busRestReads + Child.tableReads) + vkNeed 28 ≤ 8192 := by
    decide
  omega

/-! ## Down from `verify_sub` -/

/-- **`verify_sub` calls `verify_keccak` only at `vkArgsV`.** -/
theorem vs_vk_sites :
    Res.sitesB (fun f args _ ↦ f != "verify_keccak" || args == vkArgsV) VerifySub.vsT = true := by
  decide +kernel

theorem vk_params : (fn% «verify_keccak»).params = (List.range 13).map V.n := rfl

/-- A parameter's word, from a callee's parameters `v_0 .. v_(n-1)` matched to a call's arguments. -/
theorem params_get {σ σ' : Val} {n : ℕ} {as : List V} (h : ((List.range n).map V.n).map σ = as.map σ')
    {k : ℕ} (hk : k < n) {a : V} (ha : as[k]? = some a) : σ (.n k) = σ' a := by
  have := congrArg (·[k]?) h
  simpa [List.getElem?_map, List.getElem?_range hk, ha] using this

/-- **The front's sponges are carried**, from the seed's permutation: the bus's GKR walk starts from
one, and so does the tables' segment. -/
theorem front_carried {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VerifySub.VsFront bytecode C rd σ) :
    ∃ sp, (⟨[σ (.n (val% «verify_sub» "nxt[8]@19")), σ (.n (val% «verify_sub» "nxt[9]@19")), σ (.n (val% «verify_sub» "nxt[10]@19")), σ (.n (val% «verify_sub» "nxt[11]@19")), σ (.n (val% «verify_sub» "nxt[12]@19"))], []⟩ : Fs).Carries sp := by
  have h0 : (⟨[σ (.n (val% «verify_sub» "sp[8]")), σ (.n (val% «verify_sub» "sp[9]")), σ (.n (val% «verify_sub» "sp[10]")), σ (.n (val% «verify_sub» "sp[11]")), σ (.n (val% «verify_sub» "sp[12]"))], []⟩ : Fs).Carries
      ⟨keccakF1600 (seedInput F.seed F.pi), [], none⟩ := ⟨F.hcap0.symm, rfl, rfl⟩
  obtain ⟨sp1, h1⟩ := carries_absorbAll (VerifySub.vsWords σ) dsObserve h0
  rw [F.habs1] at h1
  have h2 := carries_absorb (carries_absorb h1 (σ (.n (val% «verify_sub» "x@9"))) dsObserve) (σ (.n (val% «verify_sub» "x@10"))) dsObserve
  rw [F.habs2] at h2
  obtain ⟨sp3, h3⟩ := carries_of_runsTo F.hO h2
  exact carries_of_runsTo F.hB h3

variable {r : Ref}

/-- **`verify_keccak`'s cursor passes down from `verify_sub`.** -/
theorem vkQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) VkQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = "verify_keccak" := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the caller is `verify_sub`
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI)) hw c hc)
    (name% «verify_keccak», name% «verify_sub») (by decide)
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «verify_keccak» := Option.some.inj (hfI.symm.trans VerifySub.find_vk)
      exact absurd hl (by decide +kernel)
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans VerifySub.find_vs)
  obtain rfl : fn = fn% «verify_keccak» := Option.some.inj (hfn.symm.trans VerifySub.find_vk)
  -- its call of `verify_keccak`
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_sub»).body = true by
    rw [VerifySub.vs_body]; exact vs_vk_sites) hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
  rw [hs, vk_params] at hpar
  have e5 := params_get hpar (k := 5) (by decide) rfl
  have e6 := params_get hpar (k := 6) (by decide) rfl
  have e12 := params_get hpar (k := 12) (by decide) rfl
  -- its front
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hQ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «verify_sub», 4, .tab) (by decide) rfl
    (.n 4) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨hexp, hwin⟩ := hQ
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  -- the words before the cursor
  obtain ⟨sp, hsp⟩ := front_carried F
  obtain ⟨hlG, sp', hsp'⟩ := runsTo_reads (reads_gkrPhase _) F.hG hsp
  have hhl : ∀ h ∈ (Tables.layoutOf (List.replicate (2 ^ 23) 0) F.logMem F.rowsN).tableLogHeights,
      h ≤ 30 := by
    rw [VerifySub.layoutOf_heights]
    intro h hh'
    have := F.hh31 h hh'
    omega
  obtain ⟨hlT, -⟩ := runsTo_reads (reads_tablesSeg _ (fun w p v ↦ Child.reads_claimedBytecodeValue _ w p v)
    _ hhl _ _ _ _ _) F.hT hsp'
  have hτ9 := VerifySub.tau_ge F.hrowsL
  have hτ24 := VerifySub.tau_le_of_kappasBelow (VerifySub.tableHeights_length _ F.hrowsL) F.hKB
  refine ⟨13 + F.xsG.length + F.xsT.length, (Tables.tableHeightsOf F.rowsN).getD 5 0, ?_, ?_, hτ9,
    by omega, ?_⟩
  · rw [e5, e12, F.h578, F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]
  · rw [e6, F.h583]
  · have := vk_room F.hdep34 hlG hlT (show (Tables.tableHeightsOf F.rowsN).getD 5 0 ≤ 28 by omega)
    omega

/-- **`verify_keccak`'s cursor at every honest instance.** -/
theorem vkQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VkQ J := by
  refine insts_all hr (vkQ_step hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
