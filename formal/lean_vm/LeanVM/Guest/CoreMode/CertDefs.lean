module

public import LeanVM.Guest.ExecDecodable
public import LeanVM.Guest.Mode.HintsData
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.CoreMode.GlueG

/-!
# What each certificate contributes

The certificates are assembled pack by pack (`CoreMode/Gen/<pack>/Cert.lean`, `scripts/core-mode/certs.py`)
into `ModeCerts` (`CoreMode/Assemble.lean`). Each certificate contributes facts of its own: `CertSt`,
decided by the kernel or by `rfl` (its length, its program, a loop's tail call and runs, its termination
facts' cells); `fnSpec_core`, its frame interface (`FnSpec`) from the core route's; `FnLink`, its code a function of the
guest's table; `SigsIn`, each callee signature its environment holds a certificate's (as a list, `Trie.entries`,
`CoreMode/Contracts.lean`), and `nodupB` decides that a list of entries has no duplicate, as a bit set.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-! ## Per certificate -/

/-- The certificate's facts the kernel decides: its length, a code, an entry past `__jump_tables`'s, the guest's jump table and
halting pc, its termination facts' cells. -/
noncomputable def staticB (K : Cert) : Bool :=
  K.F.len == K.code.length && 0 < K.code.length && 0 < K.F.entry && K.E.jtLo == CoreMode.jtLo &&
    K.E.jtHi == CoreMode.jtHi && K.E.halt == CoreMode.haltPc && termFr K.F.sig

/-- **A certificate's static facts**: `staticB`, and the guest's powers and jump table. -/
structure CertSt (K : Cert) : Prop where
  b : staticB K = true
  pows : K.E.pows = Data.powTree
  jt : K.E.jt = Data.jtTrie

/-- **A certificate's code is a guest function's**, its operands small. -/
def FnLink (K : Cert) : Prop :=
  (∃ f ∈ Data.functions, K.code = f.code ∧ K.F.entry = f.entryPc) ∧ K.code.all offSmall = true

theorem staticB_spec {K : Cert} (h : staticB K = true) :
    K.F.len = K.code.length ∧ 0 < K.code.length ∧ 0 < K.F.entry ∧ K.E.jtLo = CoreMode.jtLo ∧ K.E.jtHi = CoreMode.jtHi ∧
      K.E.halt = CoreMode.haltPc ∧ termFr K.F.sig = true := by
  simpa only [staticB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h

/-- **A function on the core route meets its frame interface**: its core data among `T` at its entry, its
interface, and the heap contracts' table agreeing with it. -/
theorem fnSpec_core {tab : List CoreMode.HcEnt} {T : List CoreMode.CFun} {K : Cert} {Cf : CoreMode.CFun}
    (hT : Cf ∈ T) (he : Cf.frame.entry = K.F.entry) (hs : FnSpecC K Cf)
    (hb : CoreMode.ctB tab K Cf = true := by decide +kernel) : FnSpec tab T K :=
  ⟨Cf, hT, he, hs, hb⟩

/-- A callee's signature at entry `p.1` is `p.2`, a certificate's among `Ks`, not `main`'s. -/
def SigIn (Ks : List Cert) (p : ℕ × Sig) : Prop :=
  ∃ K' ∈ Ks, K'.F.entry = p.1 ∧ K'.F.sig = p.2 ∧ K'.F.main = false

/-- Every callee signature of `K`'s environment is a certificate's among `Ks`. -/
def SigsIn (Ks : List Cert) (K : Cert) : Prop := ∀ p ∈ K.E.sigs.entries, SigIn Ks p

/-- A list's facts, element by element. -/
theorem fa_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (h : P a) (t : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x :=
  List.forall_mem_cons.2 ⟨h, t⟩

theorem fa_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := fun _ h ↦ absurd h List.not_mem_nil

/-- **A function's code from the table**: function `j` is `c`, and the certificate's code and entry
are its. -/
theorem fnLink_of {K : Cert} {c f : CompiledFunction} (hf : f ∈ Data.functions) (hc : f = c)
    (hcode : K.code = c.code) (hentry : K.F.entry = c.entryPc) : FnLink K := by
  subst hc
  refine ⟨⟨f, hf, hcode, hentry⟩, ?_⟩
  have := List.all_eq_true.1 functions_offSmall f hf
  rw [hcode, CompiledFunction.code, List.all_eq_true]
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
  exact List.all_eq_true.1 (List.all_eq_true.1 this l hl) x hx

/-! ## No duplicate entry -/

/-- No element of the list twice, nor in the bit set `s`. -/
def nodupB : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, s => !s.testBit a && nodupB l (s ||| 2 ^ a)

theorem nodupB_sound : ∀ {l : List ℕ} {s : ℕ}, nodupB l s = true → l.Nodup ∧ ∀ a ∈ l, s.testBit a = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h ↦ absurd h List.not_mem_nil⟩
  | a :: l, s, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨ha, ih⟩ := nodupB_sound h.2
    have hb : ∀ b ∈ l, b ≠ a ∧ s.testBit b = false := fun b hb ↦ by
      have := ih b hb
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
      refine ⟨fun e ↦ ?_, this.1⟩
      subst e
      rw [Nat.testBit_two_pow_self] at this
      exact absurd this.2 (by decide)
    refine ⟨List.nodup_cons.2 ⟨fun hm ↦ (hb a hm).1 rfl, ha⟩, fun b hb' ↦ ?_⟩
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact h.1
    · exact (hb b hb').2

/-- **Entries tell certificates apart** when no entry repeats. -/
theorem uniq_of_nodupB {Ks : List Cert} (h : nodupB (Ks.map (·.F.entry)) 0 = true) :
    ∀ K ∈ Ks, ∀ K' ∈ Ks, K.F.entry = K'.F.entry → K = K' :=
  fun _ hK _ hK' he ↦ List.inj_on_of_nodup_map (nodupB_sound h).1 hK hK' he

/-! ## `main` -/

/-- An instruction is a return, `JUMP` to the header's return cell. -/
def isRet : OffsetInstruction → Bool
  | .jump _ 0 1 => true
  | _ => false

theorem not_ret_of {code : List OffsetInstruction} (h : code.all (fun ins ↦ !isRet ins) = true) :
    ∀ (i c : ℕ), code[i]? ≠ some (OffsetInstruction.jump c 0 1) := fun i c hi ↦ by
  have := List.all_eq_true.1 h _ (List.mem_of_getElem? hi)
  simp [isRet] at this

/-- The jump table's targets are below `2^62`. -/
theorem jt_lt_of {t : Trie ℕ} (h : t.entries.all (fun p ↦ decide (p.2 < 2 ^ 62)) = true) :
    ∀ d e, t.get d = some e → e < 2 ^ 62 := fun _ _ he ↦ by
  simpa using List.all_eq_true.1 h _ (Trie.mem_entries he)

end

end LeanVM.Guest.Mode
