module

public import LeanVM.Guest.CoreMode.CertDefs
public import LeanVM.Guest.EndExecParts
import all LeanVM.Guest.Data.Functions

/-!
# `ModeCerts` from each certificate's facts

`modeCerts_of`: the certificates `Ks` are closed (`EndExec.ModeCerts`) for `main`'s `Km` and the
guest's program `guestE0` once each contributes its facts (`CertSt`, `FnSpec`, `FnLink`,
`SigsIn`), no entry repeats (`nodupB`), and `main` is among them, never returning, with no
termination fact. `mainOk_guest`: `main`'s certificate starts as the prologue leaves it.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.EndExec

@[expose] public section

/-- The guest's program as every certificate's environment has it, but the signatures. -/
noncomputable def guestE0 : Env := ⟨Data.powTree, Data.jtTrie, CoreMode.jtLo, CoreMode.jtHi, .nil, CoreMode.haltPc⟩

theorem jt_guest : ∀ d e, Data.jtTrie.get d = some e → e < 2 ^ 62 := jt_lt_of (by decide +kernel)

/-- **The certificates closed**, from each one's facts. -/
theorem modeCerts_of {Ks : List Cert} {Km : Cert} {tab : List CoreMode.HcEnt} {T : List CoreMode.CFun}
    (hT : ∀ Cf ∈ T, CoreMode.CfOk Cf) (hst : ∀ K ∈ Ks, CertSt K) (hw : ∀ K ∈ Ks, FnSpec tab T K)
    (hfn : ∀ K ∈ Ks, FnLink K) (hsig : ∀ K ∈ Ks, SigsIn Ks K) (hu : nodupB (Ks.map (·.F.entry)) 0 = true)
    (hm : Km ∈ Ks) (hmF : Km.F.main = true) (hmR : Km.code.all (fun i ↦ !isRet i) = true)
    (hmT : Km.F.sig.term = []) (hmc : CoreMode.hcNone tab Km.F.entry = true) : ModeCerts Ks Km guestE0 where
  fn K hK := by
    obtain ⟨⟨f, hf, hc, he⟩, hs⟩ := hfn K hK
    exact ⟨f, hf, hc, he, hs⟩
  spec := ⟨tab, T, hT, hw, hmc⟩
  ne K hK := (staticB_spec (hst K hK).b).2.1
  uniq := uniq_of_nodupB hu
  sigs K hK t G hG := hsig K hK (t, G) (Trie.mem_entries hG)
  env K hK := by
    obtain ⟨-, -, -, h1, h2, h3, -⟩ := staticB_spec (hst K hK).b
    exact ⟨(hst K hK).pows, (hst K hK).jt, h1, h2, h3⟩
  pows := PowTree.ok_of_okW Checked.powTree_ok
  jt := jt_guest
  halt := by show CoreMode.haltPc = _; rw [guest_logSize]; decide
  main := hm
  mainF := hmF
  mainRet := not_ret_of hmR
  mainTerm := hmT
  termFr K hK := (staticB_spec (hst K hK).b).2.2.2.2.2.2

/-- No certificate's entry is `__jump_tables`'s (`entryNode_X`). -/
theorem entry_ne_zero {Ks : List Cert} (hst : ∀ K ∈ Ks, CertSt K) : ∀ K ∈ Ks, K.F.entry ≠ 0 :=
  fun K hK ↦ Nat.pos_iff_ne_zero.1 (staticB_spec (hst K hK).b).2.2.1

/-- **`main`'s certificate starts as the prologue leaves it.** -/
theorem mainOk_guest {Km : Cert} (hsig : Km.F.sig = Fn.«main».csig) (hent : Km.F.entry = Data.f0.instructionCount) :
    MainOk Km guestE0 :=
  mainOk_of hsig hent rfl rfl rfl rfl

end

end LeanVM.Guest.Mode
