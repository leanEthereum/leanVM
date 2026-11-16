module

public import LeanVM.Guest.Mode.CertDefs
public import LeanVM.Guest.EndExecParts

/-!
# `ModeCerts` from each certificate's facts

`modeCerts_of`: the certificates `Ks` are closed (`EndExec.ModeCerts`) for `main`'s `Km` and the
guest's program `guestE0` once each contributes its facts (`CertSt`, `CertWalk`, `FnLink`,
`SigsIn`), no entry repeats (`nodupB`), and `main` is among them, never returning, with no
termination fact. `mainOk_guest`: `main`'s certificate starts as the prologue leaves it.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.EndExec

@[expose] public section

/-- The guest's program as every certificate's environment has it, but the signatures. -/
noncomputable def guestE0 : Env := ⟨Data.powTree, Data.jtTrie, 430, jtEnd, .nil, 524287⟩

theorem jt_guest : ∀ d e, Data.jtTrie.get d = some e → e < 2 ^ 62 := jt_lt_of (by decide +kernel)

theorem staticB_spec {K : Cert} (h : staticB K = true) :
    K.F.len = K.code.length ∧ 0 < K.code.length ∧ 0 < K.F.entry ∧ K.E.jtLo = 430 ∧ K.E.jtHi = jtEnd ∧
      K.E.halt = 524287 ∧ tailRetB K = true ∧ loopRngB K.F.sig = true ∧ termFr K.F.sig = true := by
  simpa only [staticB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h

theorem tailRet_of {K : Cert} (h : tailRetB K = true) :
    ∀ G, K.E.sigs.get K.F.entry = some G → RetEmpty G := fun G hG ↦ by
  unfold tailRetB at h
  rw [hG] at h
  simpa only [retEmptyB, Bool.and_eq_true, List.isEmpty_iff, RetEmpty, and_assoc] using h

theorem loopRng_of {G : Sig} (h : loopRngB G = true) :
    ∀ r ∈ G.postL ++ G.postLP.map (·.1), (r.lo, r.hi) ∈ G.term := fun r hr ↦
  of_decide_eq_true (List.all_eq_true.1 h r hr)

/-- **The certificates closed**, from each one's facts. -/
theorem modeCerts_of {Ks : List Cert} {Km : Cert} (hst : ∀ K ∈ Ks, CertSt K) (hw : ∀ K ∈ Ks, CertWalk K)
    (hfn : ∀ K ∈ Ks, FnLink K) (hsig : ∀ K ∈ Ks, SigsIn Ks K) (hu : nodupB (Ks.map (·.F.entry)) 0 = true)
    (hm : Km ∈ Ks) (hmF : Km.F.main = true) (hmR : Km.code.all (fun i ↦ !isRet i) = true)
    (hmT : Km.F.sig.term = []) : ModeCerts Ks Km guestE0 where
  fn K hK := by
    obtain ⟨⟨f, hf, hc, he⟩, hs⟩ := hfn K hK
    exact ⟨f, hf, hc, he, (hw K hK).1, (staticB_spec (hst K hK).b).1, hs, (hw K hK).2⟩
  ne K hK := (staticB_spec (hst K hK).b).2.1
  uniq := uniq_of_nodupB hu
  sigs K hK t G hG := hsig K hK (t, G) (Trie.mem_entries hG)
  env K hK := by
    obtain ⟨-, -, -, h1, h2, h3, -⟩ := staticB_spec (hst K hK).b
    exact ⟨(hst K hK).pows, (hst K hK).jt, h1, h2, h3⟩
  pows := PowTree.ok_of_okW Checked.powTree_ok
  jt := jt_guest
  halt := by show 524287 = _; rw [guest_logSize]; rfl
  main := hm
  mainF := hmF
  mainRet := not_ret_of hmR
  mainTerm := hmT
  tailRet K hK := tailRet_of (staticB_spec (hst K hK).b).2.2.2.2.2.2.1
  loopRng K hK := loopRng_of (staticB_spec (hst K hK).b).2.2.2.2.2.2.2.1
  endOk K hK _ _ h := preAt_end_cur (hw K hK).1 le_rfl h
  termFr K hK := (staticB_spec (hst K hK).b).2.2.2.2.2.2.2.2

/-- No certificate's entry is `__jump_tables`'s (`entryNode_X`). -/
theorem entry_ne_zero {Ks : List Cert} (hst : ∀ K ∈ Ks, CertSt K) : ∀ K ∈ Ks, K.F.entry ≠ 0 :=
  fun K hK ↦ Nat.pos_iff_ne_zero.1 (staticB_spec (hst K hK).b).2.2.1

/-- **`main`'s certificate starts as the prologue leaves it.** -/
theorem mainOk_guest {Km : Cert} (hsig : Km.F.sig = Fn.«main».modeSig) (hent : Km.F.entry = Data.f0.instructionCount) :
    MainOk Km guestE0 :=
  mainOk_of hsig hent rfl rfl rfl rfl

end

end LeanVM.Guest.Mode
