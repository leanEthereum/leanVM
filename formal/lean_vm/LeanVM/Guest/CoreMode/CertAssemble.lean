module

public import LeanVM.Guest.CoreMode.CertDefs
public import LeanVM.Guest.EndExec
public import LeanVM.Guest.SoundFacts
import all Statement.Data.Bytecode

/-!
# `ModeCerts` from each certificate's facts

`modeCerts_of`: the certificates `Ks` are closed (`EndExec.ModeCerts`) for `main`'s `Km` and the
guest's program `guestE0` once each contributes its facts (`CertSt`, `FnLink`, `SigsIn`), no entry
repeats (`nodupB`), and `main` is among them, never returning, with no termination fact.
`mainOk_guest`: `main`'s certificate starts as the prologue leaves it, the prologue's `SET`s writing
the jump table's slots in order (`slots_guest`, from the jump table's check `JumpTable.jtOk`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.EndExec
open LeanVM.Prover.Exec (maxCells)

@[expose] public section

/-- The guest's program as every certificate's environment has it, but the signatures. -/
noncomputable def guestE0 : Env :=
  ⟨Data.powTree, Data.jtTrie, Data.mainCells, Data.mainCells + Data.f0.instructionCount, .nil, 2 ^ 19 - 1⟩

theorem jt_guest : ∀ d e, Data.jtTrie.get d = some e → e < 2 ^ 62 := jt_lt_of (by decide +kernel)

/-- **The certificates closed**, from each one's facts. -/
theorem modeCerts_of {Ks : List Cert} {Km : Cert} (hst : ∀ K ∈ Ks, CertSt K) (hfn : ∀ K ∈ Ks, FnLink K)
    (hsig : ∀ K ∈ Ks, SigsIn Ks K) (hu : nodupB (Ks.map (·.F.entry)) 0 = true) (hm : Km ∈ Ks)
    (hmF : Km.F.main = true) (hmR : Km.code.all (fun i ↦ !isRet i) = true) (hmT : Km.F.sig.term = []) :
    ModeCerts Ks Km guestE0 where
  fn K hK := by
    obtain ⟨⟨f, hf, hc, he⟩, hs⟩ := hfn K hK
    exact ⟨f, hf, hc, he, hs⟩
  ne K hK := (staticB_spec (hst K hK).b).2.1
  uniq := uniq_of_nodupB hu
  sigs K hK t G hG := hsig K hK (t, G) (Trie.mem_entries hG)
  env K hK := by
    obtain ⟨-, -, -, h1, h2, h3, -⟩ := staticB_spec (hst K hK).b
    exact ⟨(hst K hK).pows, (hst K hK).jt, h1, h2, h3⟩
  pows := PowTree.ok_of_okW Checked.powTree_ok
  jt := jt_guest
  halt := by show (2 ^ 19 - 1 : ℕ) = _; rw [guest_logSize]
  main := hm
  mainF := hmF
  mainRet := not_ret_of hmR
  mainTerm := hmT
  termFr K hK := (staticB_spec (hst K hK).b).2.2.2.2.2.2

/-- No certificate's entry is `__jump_tables`'s. -/
theorem entry_ne_zero {Ks : List Cert} (hst : ∀ K ∈ Ks, CertSt K) : ∀ K ∈ Ks, K.F.entry ≠ 0 :=
  fun K hK ↦ Nat.pos_iff_ne_zero.1 (staticB_spec (hst K hK).b).2.2.1

/-! ## `main` -/

/-- Every slot of `__jump_tables` is a key of the jump table. -/
theorem jt_full : (List.range proLen).all (fun i ↦ (Data.jtTrie.get (Data.mainCells + i)).isSome) = true := by
  decide +kernel

/-- **The prologue's `SET`s write the jump table's slots in order**, each its target's power. -/
theorem slots_guest : ∀ i < proLen, ∃ k0 k1, Data.f0.instructionAt i = .set (Data.mainCells + i) k0 k1 ∧
    ∀ e, Data.jtTrie.get (Data.mainCells + i) = some e → OffsetInstruction.immediateWord k0 k1 = ofK (g ^ e) := by
  intro i hi
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp jt_full i (List.mem_range.mpr hi))
  have he := JumpTable.allEntries_get JumpTable.jtOk ht
  rw [Nat.one_mul, Nat.add_zero] at he
  unfold JumpTable.entryOk at he
  rw [Bool.and_eq_true, Nat.add_sub_cancel_left] at he
  obtain ⟨-, he⟩ := he
  split at he
  · rename_i o k0 k1 hins
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨ho, hk1⟩, hf⟩ := he
    subst ho hk1
    refine ⟨k0, 0, hins, fun e he' ↦ ?_⟩
    rw [ht, Option.some.injEq] at he'
    subst he'
    exact imm_of_ofBits (PowTree.find_ok (PowTree.ok_of_okW Checked.powTree_ok) hf)
  · exact absurd he Bool.false_ne_true

/-- `main`'s signature entered at its header alone. -/
def mainSigB (G : Sig) : Bool :=
  G.entry.all (· < 2) && G.self.isNone && G.pre.isEmpty && G.preR.isEmpty && G.preP.isEmpty

/-- **`main`'s certificate starts as the prologue leaves it**: entered past the prologue at its
header alone. -/
theorem mainOk_guest {Km : Cert} (hsig : mainSigB Km.F.sig = true) (hent : Km.F.entry = proLen) :
    MainOk Km guestE0 := by
  simp only [mainSigB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at hsig
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hsig
  exact ⟨hent, rfl, by show Data.mainCells + proLen ≤ maxCells; unfold maxCells; decide +kernel, slots_guest,
    h1, h2, h3, h4, h5⟩

end

end LeanVM.Guest.Mode
