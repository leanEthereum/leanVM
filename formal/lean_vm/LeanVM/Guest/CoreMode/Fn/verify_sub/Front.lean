/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Front

  `verify_sub`'s front as its callees see it: the words its runs read from the proof stream, and its
  sponges carried, for the cursors it hands `verify_tables` and `verify_keccak`.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundOf
public import LeanVM.Guest.Child.Reads
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.CoreMode.Fam.ResF
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# `verify_sub`'s front, read

`runsTo_reads`: a run of a program of `n` reads (`Child.Reads`) from a carried sponge reads at most
`n` words (`Child.run_reads`) and leaves a carried sponge. The front (`B1.VerifySub.vs_front`) runs
the bus's GKR walk and the tables' segment from carried sponges (`front_carried`), so their words are
at most their reads (`reads_gkrPhase`, `reads_tablesSeg`), and with `verify_keccak`'s (`vkNeed`) they
fit the stream (`vk_room`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The words `verify_keccak` reads at a table of log-height `τ`: one, twelve layers of
`84 + 2(τ - 3)`, then the outputs' and the inputs' `97`. -/
def vkNeed (τ : ℕ) : ℕ := 1 + 12 * (84 + 2 * (τ - 3)) + 97

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

end

end LeanVM.Guest.EndExec
