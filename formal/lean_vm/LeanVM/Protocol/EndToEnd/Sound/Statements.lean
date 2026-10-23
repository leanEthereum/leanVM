/-
  LeanVM.Protocol.EndToEnd.Sound.Statements

  Knowledge soundness of the leanVM verifier against an adversary that chooses the statement:
  the program and the public input, together with the proof, after querying the random oracle.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Theorem

/-!
# Soundness for adversarially chosen statements

The deployed verifier seeds its Fiat-Shamir chain with the statement: the bytecode's hash, then
the IV around it, then the public input (`leanVmSeed`), and runs `leanVmProgram bytecode
publicInput` from that seed. The random-oracle theorem (`romSound`) takes a family of seedings
(`Seeds`), one per statement, and a single verifier program with one doom certificate; the
family's seeds put the program at the statement's root history.

* **The program of every statement** (`anyProgram`): read the bytecode's length and words and
  the public input's four lanes, as scalars, then run the leanVM verifier program of that
  bytecode and public input. The root of a statement is its history of reads (`stmtHistory`),
  at which `anyProgram` is the statement's verifier program (`after_stmtHistory`). The reads
  are never absorbed: they only index the statement in the program.
* **The seedings** (`leanVmSeeds`): the statement's seeding and root. The last seeding input,
  computed through answers without collisions, names the statement, because the bytecode words
  name the program (`bytecodeWords_injective`) and the digest names the public input
  (`publicDigest_injective`).
* **The certificate** (`anyCert`): past a statement's root, the doom of `leanVmCert` of that
  statement on the rest of the history. Roots are prefix-free (`stmt_eq_of_prefix`), so the
  history names the statement and every obligation is `leanVmCert`'s.

`leanVm_knowledge` and `leanVm_execution` state knowledge soundness for an adversary of `QA`
queries that outputs a statement and a proof: with `N = QA + 13213`, the verifier accepts while
the extractor finds no witness of the adversary's statement with probability at most
`N · (2^-128 + 5N / 2^256)`.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicDigest publicDigest_injective)
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## Histories of reads -/

/-- A history of reads: the program's node at it, if any, is reached through read nodes. -/
theorem reachable_of_after_reads {P : Prog Bool} :
    ∀ (l : List E) {p : Prog Bool}, P.after (l.map Ev.read) = some p →
      P.Reachable (l.map Ev.read) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intros; exact Prog.Reachable.nil
  | append_singleton l e ih =>
    intro p hp
    rw [List.map_append, List.map_singleton, Prog.after_append] at hp
    rcases hq : P.after (l.map Ev.read) with _ | q
    · rw [hq] at hp; cases hp
    · rw [hq, Option.bind_some] at hp
      cases q with
      | read k =>
        rw [List.map_append, List.map_singleton]
        exact Prog.Reachable.read e (ih hq) hq
      | _ => simp [Prog.after] at hp

theorem commits_map_read (l : List E) : commits (l.map Ev.read) = [] := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [commits] using ih

/-! ## Transport past a prefix without commitments -/

section Transport

variable {P p : Prog Bool} {h₀ : List Ev}

theorem answer_append (hc : commits h₀ = []) (h : List Ev) (i : ℕ) (ps : List ℕ) :
    answer (h₀ ++ h) i ps = answer h i ps := by
  simp [answer, Compile.commits_append, hc]

/-- A reachable history past a prefix without commitments is a reachable history of the node
at the prefix. -/
theorem reachable_drop (ha : P.after h₀ = some p) (hc : commits h₀ = []) :
    ∀ {h : List Ev}, P.Reachable h → ∀ h', h = h₀ ++ h' → p.Reachable h' := by
  intro h hr
  induction hr with
  | nil =>
    intro h' he
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he.symm
    exact Prog.Reachable.nil
  | @read h k x hr hk ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact Prog.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine Prog.Reachable.read (k := k) x (ih h'' rfl) ?_
      rwa [Prog.after_append, ha, Option.bind_some] at hk
  | @sample h k c hr hk ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact Prog.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine Prog.Reachable.sample (k := k) c (ih h'' rfl) ?_
      rwa [Prog.after_append, ha, Option.bind_some] at hk
  | @grind h b k hr hk ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact Prog.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine Prog.Reachable.grind (k := k) (ih h'' rfl) ?_
      rwa [Prog.after_append, ha, Option.bind_some] at hk
  | @commit h ht w k word hr hk hw ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact Prog.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine Prog.Reachable.commit (k := k) word (ih h'' rfl) ?_ hw
      rwa [Prog.after_append, ha, Option.bind_some] at hk
  | @query h i ps k rows hr hk hans ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact Prog.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine Prog.Reachable.query (i := i) (ps := ps) (k := k) (ih h'' rfl) ?_ ?_
      · rwa [Prog.after_append, ha, Option.bind_some] at hk
      · rwa [answer_append hc] at hans

theorem after_drop (ha : P.after h₀ = some p) (h' : List Ev) :
    P.after (h₀ ++ h') = p.after h' := by
  rw [Prog.after_append, ha, Option.bind_some]

/-- Escape probabilities past a prefix without commitments, for doom predicates that agree
past it. -/
theorem esc_drop (hc : commits h₀ = []) {D D' : List Ev → Prop}
    (hD : ∀ h', D (h₀ ++ h') ↔ D' h') :
    ∀ (h' : List Ev) (q : Prog Bool), esc D (h₀ ++ h') q = esc D' h' q
  | h', .sample k => by
    rw [esc_sample, esc_sample]
    congr 1
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [List.append_assoc]
    exact esc_drop hc hD _ _
  | h', .query i ps k => by
    rw [esc_query, esc_query, answer_append hc]
    split
    · rw [List.append_assoc]; exact esc_drop hc hD _ _
    · rfl
  | h', .ret true => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]
  | h', .ret false => rfl
  | h', .fail => rfl
  | h', .read k => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]
  | h', .grind b k => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]
  | h', .commit ht w k => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]

/-- A boundary history ending in one more event. -/
theorem boundary_append_of {h h' : List Ev} {e : Ev} (hb : Boundary (h ++ [e])) :
    Boundary (h' ++ [e]) := by
  cases e with
  | read x => exact boundary_append_read _ _
  | grind b => exact boundary_append_grind _ _
  | commit ht w W => exact boundary_append_commit _ _ _ _
  | sample c => exact absurd hb (not_boundary_append_sample _ _)
  | query rows => exact absurd hb (not_boundary_append_query _ _)

/-- A boundary past a prefix is a boundary of the rest. -/
theorem boundary_drop {h' : List Ev} (hb : Boundary (h₀ ++ h')) : Boundary h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · trivial
  · rw [List.concat_eq_append] at hb ⊢
    rw [← List.append_assoc] at hb
    exact boundary_append_of hb

end Transport

/-! ## The statements and their program -/

/-- A statement: a program and a public input. -/
abbrev Statement : Type := Program × PublicInput

/-- A word as a scalar: its first limb. -/
def wordE (k : K) : E := E.ofLimbs k 0 0

/-- The value of a word, as a natural number. -/
def kNat (k : K) : ℕ := k.toBitVec.toNat

/-- Read `n` words, one per scalar's first limb, then continue with them. -/
def readWords : ℕ → (List K → Prog Bool) → Prog Bool
  | 0, k => k []
  | n + 1, k => .read fun e ↦ readWords n fun ws ↦ k (e.limb 0 :: ws)

/-- **The verifier program of every statement**: the bytecode's length and words and the
public input's four lanes, read as scalars, then the leanVM verifier program of that bytecode and
public input. -/
def anyProgram : Prog Bool :=
  .read fun n ↦ readWords (kNat (n.limb 0)) fun ws ↦ readWords 4 fun ls ↦
    leanVmProgram ws (publicDigest ⟨fun i ↦ ls.getD i 0⟩)

/-- The scalars of a statement: the bytecode's length and words, and the public input's lanes. -/
def stmtScalars (x : Statement) : List E :=
  wordE (K.ofBits (bytecodeWords x.1).length) ::
    ((bytecodeWords x.1).map wordE ++ (List.ofFn x.2.lanes).map wordE)

/-- **The root of a statement**: the history of its reads. -/
def stmtHistory (x : Statement) : List Ev := (stmtScalars x).map Ev.read

theorem limb_wordE (k : K) : (wordE k).limb 0 = k := by simp [wordE]

theorem after_readWords (k : List K → Prog Bool) :
    ∀ (ws : List K) (rest : List Ev),
      (readWords ws.length k).after ((ws.map wordE).map Ev.read ++ rest) = (k ws).after rest
  | [], rest => rfl
  | w :: ws, rest => by
    simp only [List.length_cons, readWords, List.map_cons, List.cons_append, Prog.after]
    rw [limb_wordE]
    exact after_readWords (fun ws' ↦ k (w :: ws')) ws rest

theorem after_readWords' (k : List K → Prog Bool) {n : ℕ} (ws : List K) (hn : ws.length = n)
    (rest : List Ev) :
    (readWords n k).after ((ws.map wordE).map Ev.read ++ rest) = (k ws).after rest := by
  subst hn
  exact after_readWords k ws rest

theorem kNat_ofBits {n : ℕ} (hn : n < 2 ^ 64) : kNat (K.ofBits n) = n := by
  change (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem length_bytecodeWords_lt (prog : Program) : (bytecodeWords prog).length < 2 ^ 64 := by
  rw [length_bytecodeWords]
  have := prog.logSize_le
  unfold maxLogBytecode at this
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- **The root of a statement leads to the statement's verifier program.** -/
theorem after_stmtHistory (x : Statement) :
    anyProgram.after (stmtHistory x) =
      some (leanVmProgram (bytecodeWords x.1) (publicDigest x.2)) := by
  simp only [stmtHistory, stmtScalars, List.map_cons, anyProgram, Prog.after, limb_wordE,
    kNat_ofBits (length_bytecodeWords_lt x.1), List.map_append]
  rw [after_readWords]
  rw [← List.append_nil ((List.map Ev.read (List.map wordE (List.ofFn x.2.lanes)))),
    after_readWords' _ _ List.length_ofFn]
  have hpi : (⟨fun i ↦ (List.ofFn x.2.lanes).getD i 0⟩ : PublicInput) = x.2 := by
    obtain ⟨lanes⟩ := x.2
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hpi]
  rfl

theorem nodeAt_stmtHistory (x : Statement) :
    nodeAt anyProgram (stmtHistory x) = leanVmProgram (bytecodeWords x.1) (publicDigest x.2) := by
  simp [nodeAt, after_stmtHistory]

theorem boundary_map_read {l : List E} (hl : l ≠ []) : Boundary (l.map Ev.read) := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', e, rfl⟩
  · exact absurd rfl hl
  · rw [List.concat_eq_append, List.map_append, List.map_singleton]
    exact boundary_append_read _ _

theorem grindBits_map_read (l : List E) : grindBits (l.map Ev.read) = 0 := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', e, rfl⟩
  · rfl
  · rw [List.concat_eq_append, List.map_append, List.map_singleton]
    exact grindBits_append_read _ _

theorem commits_stmtHistory (x : Statement) : commits (stmtHistory x) = [] :=
  commits_map_read _

/-- A statement's root is a root of `anyProgram`. -/
theorem rootOk_stmtHistory (x : Statement) : RootOk anyProgram (stmtHistory x) := by
  have ha := after_stmtHistory x
  exact ⟨reachable_of_after_reads _ ha, boundary_map_read (by simp [stmtScalars]),
    grindBits_map_read _, commits_map_read _, by simp [ha]⟩

theorem wordE_injective : Function.Injective wordE := fun a b h ↦ by
  rw [← limb_wordE a, ← limb_wordE b, h]

theorem ofBits_injective {n m : ℕ} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (h : K.ofBits n = K.ofBits m) : n = m := by
  rw [← kNat_ofBits hn, ← kNat_ofBits hm, h]

theorem length_stmtHistory (x : Statement) :
    (stmtHistory x).length = (bytecodeWords x.1).length + 5 := by
  simp [stmtHistory, stmtScalars]

/-- **Roots are prefix-free**: two roots on one history are one statement's. -/
theorem stmt_eq_of_prefix {x x' : Statement} {h : List Ev} (hx : stmtHistory x <+: h)
    (hx' : stmtHistory x' <+: h) : x = x' := by
  -- The first read gives the bytecode's length, so the roots have one length.
  have hhead : ∀ {y y' : Statement}, stmtHistory y <+: stmtHistory y' →
      (bytecodeWords y.1).length = (bytecodeWords y'.1).length := by
    intro y y' hp
    have h0 := hp.getElem (i := 0) (by simp [length_stmtHistory])
    simp only [stmtHistory, stmtScalars, List.map_cons, List.getElem_cons_zero,
      Ev.read.injEq] at h0
    exact ofBits_injective (length_bytecodeWords_lt _) (length_bytecodeWords_lt _)
      (wordE_injective h0)
  have heq : stmtHistory x = stmtHistory x' := by
    rcases List.prefix_or_prefix_of_prefix hx hx' with hp | hp
    · exact hp.eq_of_length (by rw [length_stmtHistory, length_stmtHistory, hhead hp])
    · exact (hp.eq_of_length (by rw [length_stmtHistory, length_stmtHistory, hhead hp])).symm
  have hs : stmtScalars x = stmtScalars x' :=
    List.map_injective_iff.mpr (fun a b h ↦ Ev.read.inj h) heq
  simp only [stmtScalars, List.cons.injEq] at hs
  obtain ⟨hl, hs⟩ := hs
  have hlen : (bytecodeWords x.1).length = (bytecodeWords x'.1).length :=
    ofBits_injective (length_bytecodeWords_lt _) (length_bytecodeWords_lt _) (wordE_injective hl)
  obtain ⟨hw, hp⟩ := List.append_inj hs (by simp [hlen])
  have hw' := List.map_injective_iff.mpr wordE_injective hw
  have hp' := List.map_injective_iff.mpr wordE_injective hp
  obtain ⟨prog, input⟩ := x
  obtain ⟨prog', input'⟩ := x'
  have h1 := bytecodeWords_injective hw'
  have h2 : input = input' := by
    obtain ⟨l⟩ := input
    obtain ⟨l'⟩ := input'
    congr 1
    exact List.ofFn_injective hp'
  exact Prod.ext h1 h2

/-! ## The seedings -/

theorem leanVmSeed_steps (bytecode : List K) (pd : Digest) :
    (leanVmSeed bytecode pd).steps = [(ivPrefix, []), ([], digestBytes pd)] := rfl

theorem length_ivPrefix : ivPrefix.length = 46 := rfl

/-- The last pending input of the leanVM seeding: the IV's digest and the public input. -/
theorem pend_leanVmSeed {H : Bytes → Option Digest} {bytecode : List K} {pd : Digest}
    {t : Bytes} (h : pend H (leanVmSeed bytecode pd) = some (t, true)) :
    ∃ d₀ d₁, H (bytecode.flatMap kBytes) = some d₀ ∧ H (ivPrefix ++ digestBytes d₀) = some d₁ ∧
      t = digestBytes d₁ ++ digestBytes pd := by
  simp only [pend, leanVmSeed] at h
  split at h
  · simp at h
  · rename_i d₀ hd₀
    simp only [goPend, Seed.input, List.append_nil, List.nil_append] at h
    split at h
    · simp at h
    · rename_i d₁ hd₁
      split at h
      · simp only [List.isEmpty_nil, Option.some.injEq, Prod.mk.injEq, and_true] at h
        exact ⟨d₀, d₁, hd₀, hd₁, h.symm⟩
      · simp at h

theorem length_flatMap_kBytes (ws : List K) : (ws.flatMap kBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, kBytes_length, ih]; ring

/-- **The seedings of the statements.** -/
def leanVmSeeds : Seeds Statement where
  seed x := leanVmSeed (bytecodeWords x.1) (publicDigest x.2)
  root := stmtHistory
  steps := [(ivPrefix, [])]
  steps_mem x a ha := by
    rw [leanVmSeed_steps] at ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact Or.inl List.mem_cons_self
    · exact Or.inr rfl
  last x := ⟨digestBytes (publicDigest x.2), digestBytes_length _, rfl⟩
  first_len x := by
    show ((bytecodeWords x.1).flatMap kBytes).length ≠ 64
    rw [length_flatMap_kBytes, length_bytecodeWords, pow_add]
    have : 1 ≤ 2 ^ x.1.logSize := Nat.one_le_two_pow
    omega
  mid_len x a ha d := by
    rw [leanVmSeed_steps] at ha
    simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.mem_singleton] at ha
    subst ha
    simp [Seed.input, length_ivPrefix, digestBytes_length]
  inj H hH x x' t hx hx' := by
    obtain ⟨d₀, d₁, h₀, h₁, ht⟩ := pend_leanVmSeed hx
    obtain ⟨d₀', d₁', h₀', h₁', ht'⟩ := pend_leanVmSeed hx'
    rw [ht] at ht'
    obtain ⟨e₁, e₂⟩ := List.append_inj ht' (by rw [digestBytes_length, digestBytes_length])
    have hpd := publicDigest_injective (digestBytes_injective e₂)
    rw [digestBytes_injective e₁] at h₁
    have hd₀ : d₀ = d₀' := digestBytes_injective
      (List.append_cancel_left (hH _ _ _ h₁ h₁'))
    rw [hd₀] at h₀
    have hb := hH _ _ _ h₀ h₀'
    have hl : (bytecodeWords x.1).length = (bytecodeWords x'.1).length := by
      have := congrArg List.length hb
      rw [length_flatMap_kBytes, length_flatMap_kBytes] at this
      omega
    have hw := bytecodeWords_injective (flatMap_kBytes_inj hl hb)
    exact Prod.ext hw hpd

/-! ## The certificate -/

/-- **Doom for every statement**: past a statement's root, its certificate's doom on the rest. -/
def anyD (h : List Ev) : Prop :=
  ∃ x, stmtHistory x <+: h ∧ (leanVmCert x.1 x.2).D (h.drop (stmtHistory x).length)

open Classical in
/-- The escape bound for every statement: its certificate's past its root, `0` elsewhere. -/
noncomputable def anyε (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ x, stmtHistory x <+: h then
    (leanVmCert hx.choose.1 hx.choose.2).ε (h.drop (stmtHistory hx.choose).length)
  else 0

theorem anyD_iff (x : Statement) (h' : List Ev) :
    anyD (stmtHistory x ++ h') ↔ (leanVmCert x.1 x.2).D h' := by
  constructor
  · rintro ⟨x', hx', hD⟩
    obtain rfl := stmt_eq_of_prefix hx' (List.prefix_append _ _)
    simpa using hD
  · intro hD
    exact ⟨x, List.prefix_append _ _, by simpa using hD⟩

theorem anyε_eq (x : Statement) (h' : List Ev) :
    anyε (stmtHistory x ++ h') = (leanVmCert x.1 x.2).ε h' := by
  unfold anyε
  split
  · rename_i hx
    rw [stmt_eq_of_prefix hx.choose_spec (List.prefix_append _ _)]
    simp
  · rename_i hx
    exact absurd ⟨x, List.prefix_append _ _⟩ hx

/-- A doomed history is past a root. -/
theorem anyD_split {h : List Ev} (hD : anyD h) :
    ∃ x h', h = stmtHistory x ++ h' ∧ (leanVmCert x.1 x.2).D h' := by
  obtain ⟨x, ⟨h', rfl⟩, hD⟩ := hD
  exact ⟨x, h', rfl, by simpa using hD⟩

/-- **The certificate of every statement.** -/
noncomputable def anyCert : Cert anyProgram where
  D := anyD
  ε := anyε
  read := by
    intro h k e hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split hD
    have hax := after_stmtHistory x
    rw [List.append_assoc, anyD_iff]
    exact (leanVmCert x.1 x.2).read e
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  grind := by
    intro h b k hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split hD
    have hax := after_stmtHistory x
    rw [List.append_assoc, anyD_iff]
    exact (leanVmCert x.1 x.2).grind
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  commit := by
    intro h ht w k word hr ha hw hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split hD
    have hax := after_stmtHistory x
    rw [List.append_assoc, anyD_iff]
    exact (leanVmCert x.1 x.2).commit word
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hw hDx
  group := by
    intro h p hr hb ha hp hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split hD
    have hax := after_stmtHistory x
    rw [esc_drop (h₀ := stmtHistory x) (commits_stmtHistory x) (anyD_iff x), anyε_eq]
    exact (leanVmCert x.1 x.2).group (reachable_drop hax (commits_stmtHistory x) hr h' rfl)
      (boundary_drop hb) (by rwa [after_drop hax] at ha) hp hDx
  final := by
    intro h hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split hD
    have hax := after_stmtHistory x
    exact (leanVmCert x.1 x.2).final (reachable_drop hax (commits_stmtHistory x) hr h' rfl)
      (by rwa [after_drop hax] at ha) hDx

theorem grindBits_stmt (x : Statement) (h' : List Ev) :
    grindBits (stmtHistory x ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil]; exact grindBits_map_read _
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `2^-128`. -/
theorem anyCert_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * anyCert.ε h ≤ εLean := by
  by_cases hx : ∃ x, stmtHistory x <+: h
  · obtain ⟨x, h', rfl⟩ : ∃ x h', h = stmtHistory x ++ h' := by
      obtain ⟨x, h', he⟩ := hx
      exact ⟨x, h', he.symm⟩
    show _ * anyε _ ≤ _
    rw [anyε_eq, grindBits_stmt]
    exact leanVmCert_bound x.1 x.2 h'
  · show _ * anyε _ ≤ _
    simp only [anyε, hx, ↓reduceDIte, mul_zero, zero_le]

/-! ## The verifier of every statement -/

/-- The verifier of the statement and proof `z` is the compiled leanVM verifier. -/
theorem verifierFam_leanVm (z : Statement × Proof) :
    verifierFam leanVmSeeds anyProgram z =
      verifierComp (leanVmSeed (bytecodeWords z.1.1) (publicDigest z.1.2))
        (leanVmProgram (bytecodeWords z.1.1) (publicDigest z.1.2)) z.2 := by
  simp only [verifierFam, leanVmSeeds, nodeAt_stmtHistory]

theorem isTotalQueryBound_leanVmFam (z : Statement × Proof) :
    IsTotalQueryBound (verifierFam leanVmSeeds anyProgram z) leanVmQueryBound := by
  rw [verifierFam_leanVm]
  exact isTotalQueryBound_leanVm _ _ _

/-! ## From a statement's doom to doom for every statement -/

/-- A compiled run from a longer history extends the same history. -/
theorem xrun_append_hist (H : Bytes → Option Digest) {α : Type} :
    ∀ (p : Prog α) (s : St) (h₀ h : List Ev),
      xrun H p s (h₀ ++ h) = (xrun H p s h).map fun r ↦ (r.1, r.2.1, h₀ ++ r.2.2)
  | .ret a, s, h₀, h => rfl
  | .fail, s, h₀, h => rfl
  | .read k, s, h₀, h => by
    simp only [xrun]
    split
    · rfl
    · rcases absorbBlock H s.cv _ with _ | cv
      · rfl
      · simp only [Option.bind_some, List.append_assoc]
        exact xrun_append_hist H _ _ h₀ _
  | .sample k, s, h₀, h => by
    simp only [xrun]
    rcases absorbBlock H s.cv _ with _ | cv
    · rfl
    · simp only [Option.bind_some, List.append_assoc]
      exact xrun_append_hist H _ _ h₀ _
  | .grind bits k, s, h₀, h => by
    simp only [xrun]
    split
    · rfl
    · rcases absorbBlock H s.cv _ with _ | base
      · rfl
      · simp only [Option.bind_some]
        rcases absorbBlock H base _ with _ | d
        · rfl
        · simp only [Option.bind_some]
          rcases absorbBlock H s.cv _ with _ | cv
          · rfl
          · simp only [Option.bind_some]
            split
            · rw [List.append_assoc]; exact xrun_append_hist H _ _ h₀ _
            · rfl
  | .commit height width k, s, h₀, h => by
    simp only [xrun]
    split
    · rcases absorbBlock H s.cv _ with _ | cv0
      · rfl
      · simp only [Option.bind_some]
        rcases absorbBlock H cv0 _ with _ | cv1
        · rfl
        · simp only [Option.bind_some]
          split
          · rw [List.append_assoc]; exact xrun_append_hist H _ _ h₀ _
          · rfl
    · rfl
  | .query i ps k, s, h₀, h => by
    simp only [xrun]
    split
    · rfl
    · split
      · rw [List.append_assoc]; exact xrun_append_hist H _ _ h₀ _
      · rfl

/-- The extracted history of a run from a statement's root is the root followed by the
extracted history from the empty history. -/
theorem extractedFrom_eq (H : Bytes → Option Digest) (σ : Seed) (p : Prog Bool) (h₀ : List Ev)
    (π : Proof) (hv : Rom.verify H σ p π = some true) :
    extractedFrom H σ p h₀ π = h₀ ++ extractedHistory H σ p π := by
  obtain ⟨seed, s, hseed, hx⟩ := xrun_of_verify hv
  have hx' := xrun_append_hist H p ⟨seed, π.stream, π.openings, []⟩ h₀ []
  rw [List.append_nil, hx, Option.map_some] at hx'
  simp only [extractedFrom, hseed, hx']

/-- **A statement's doom is doom for every statement.** -/
theorem doomed_of_doomedRun {x : Statement} {π : Proof} {c : HashSpec.QueryCache}
    (hv : Rom.verify (fun y ↦ c y) (leanVmSeed (bytecodeWords x.1) (publicDigest x.2))
      (leanVmProgram (bytecodeWords x.1) (publicDigest x.2)) π = some true)
    (hd : DoomedRun (leanVmCert x.1 x.2) (leanVmSeed (bytecodeWords x.1) (publicDigest x.2)) π
      c) :
    Doomed anyCert leanVmSeeds (x, π) c := by
  obtain ⟨h₀, hh₀, hb, hD⟩ := hd
  refine ⟨stmtHistory x ++ h₀, ?_,
    by show (stmtHistory x).length ≤ _; rw [List.length_append]; omega, ?_,
    (anyD_iff x h₀).mpr hD⟩
  · change stmtHistory x ++ h₀ <+: extractedFrom (fun y ↦ c y)
      (leanVmSeed (bytecodeWords x.1) (publicDigest x.2)) (nodeAt anyProgram (stmtHistory x))
      (stmtHistory x) π
    rw [nodeAt_stmtHistory, extractedFrom_eq _ _ _ _ _ hv]
    exact (List.prefix_append_right_inj _).mpr hh₀
  · rcases List.eq_nil_or_concat h₀ with rfl | ⟨h'', e, rfl⟩
    · rw [List.append_nil]; exact (rootOk_stmtHistory x).2.1
    · rw [List.concat_eq_append] at hb ⊢
      rw [← List.append_assoc]
      exact boundary_append_of hb

/-! ## Knowledge soundness for chosen statements -/

/-- **Knowledge soundness for adversarially chosen statements.** An adversary of `QA` queries
that outputs a statement and a proof makes the deployed verifier, with BLAKE2s a random oracle,
accept while `extractStack` does not extract admissible sizes `s` and a stack satisfying
`M3Holds (leanIsaInstance blake2sFlockSpec prog s) input` for the adversary's statement with
probability at most `(QA + 13213) · (2^-128 + failBound leanVmSeeds (QA + 13213))`. -/
theorem leanVm_knowledge (A : OracleComp HashSpec (Statement × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam leanVmSeeds anyProgram)}[z.1.2 = true ∧
      ¬ Extracted z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2] ≤
      ((QA + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + failBound leanVmSeeds (QA + 13213)) := by
  have h := romSound_of_imp anyProgram anyCert leanVmSeeds (fun x ↦ rootOk_stmtHistory x) εLean
    anyCert_bound A QA hA leanVmQueryBound isTotalQueryBound_leanVmFam
    (fun z c ↦ ¬ Extracted z.1.1 z.1.2 c z.2)
    (fun z c hv hb ↦ by
      simp only [leanVmSeeds, nodeAt_stmtHistory] at hv
      exact doomed_of_doomedRun hv (doomed_of_not_extracted z.1.1 z.1.2 hv hb))
  rwa [leanVmQueryBound_eq] at h

/-- **The extracted witness represents a valid execution, for chosen statements.** An adversary
of `QA` queries that outputs a statement and a proof makes the deployed verifier accept, for a
program with well-formed bytecode, while `extractStack` does not extract sizes `s` and a stack
`q` whose witness represents a valid execution of the adversary's program on its public input,
with probability at most `(QA + 13213) · (2^-128 + failBound leanVmSeeds (QA + 13213))`. -/
theorem leanVm_execution (A : OracleComp HashSpec (Statement × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam leanVmSeeds anyProgram)}[z.1.2 = true ∧
      SentinelSafe z.1.1.1.1 ∧
      ¬ ∃ (s : Sizes) (q : Column (leanIsaμ z.1.1.1.1 s)),
        extractStack z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 =
          some (⟨s, q⟩ : Σ s : Sizes, Column (leanIsaμ z.1.1.1.1 s)) ∧
        ∃ t, AssignmentRepresents (witnessOf F₀ z.1.1.1.1 s q) t ∧
          ValidExecution z.1.1.1.1 z.1.1.1.2 t] ≤
      ((QA + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + failBound leanVmSeeds (QA + 13213)) := by
  have h := romSound_of_imp anyProgram anyCert leanVmSeeds (fun x ↦ rootOk_stmtHistory x) εLean
    anyCert_bound A QA hA leanVmQueryBound isTotalQueryBound_leanVmFam
    (fun z c ↦ SentinelSafe z.1.1 ∧ ¬ ∃ (s : Sizes) (q : Column (leanIsaμ z.1.1 s)),
        extractStack z.1.1 z.1.2 c z.2 = some ⟨s, q⟩ ∧
        ∃ t, AssignmentRepresents (witnessOf F₀ z.1.1 s q) t ∧ ValidExecution z.1.1 z.1.2 t)
    (fun z c hv hb ↦ by
      simp only [leanVmSeeds, nodeAt_stmtHistory] at hv
      exact doomed_of_doomedRun hv (doomed_of_not_extracted z.1.1 z.1.2 hv
        fun ⟨s, q, hx, hs, hM⟩ ↦ hb.2 ⟨s, q, hx, execution_of_extracted F₀ hb.1 hs hM⟩))
  rwa [leanVmQueryBound_eq] at h

/-! ## The numbers -/

/-- `2^-k` as `2^(n - k) / 2^n`. -/
theorem inv_pow_eq_div (k n : ℕ) (h : k ≤ n) :
    (2 : ℝ≥0∞)⁻¹ ^ k = ((2 ^ (n - k) : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ENNReal.div_eq_inv_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, pow_add, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- **The numeric bound**: for an adversary of at most `2^64` queries, the bound of the
knowledge statement is at most `2^-63`. -/
theorem leanVm_bound_le {QA : ℕ} (hQ : QA ≤ 2 ^ 64) :
    ((QA + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + failBound leanVmSeeds (QA + 13213)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  set N := QA + 13213 with hN
  have hfail : failBound leanVmSeeds N = ((5 * N : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
    rw [failBound, Nat.cast_pow, Nat.cast_ofNat]
    rfl
  rw [hfail, inv_pow_eq_div 128 256 (by norm_num), ENNReal.div_add_div_same, ← mul_div_assoc,
    ← Nat.cast_add, ← Nat.cast_mul, inv_pow_eq_div 63 256 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  have hN' : N ≤ 2 ^ 64 + 13213 := by omega
  rw [show 256 - 128 = 128 from rfl, show 256 - 63 = 193 from rfl]
  calc N * (2 ^ 128 + 5 * N) ≤ (2 ^ 64 + 13213) * (2 ^ 128 + 5 * (2 ^ 64 + 13213)) :=
        Nat.mul_le_mul hN' (Nat.add_le_add_left (Nat.mul_le_mul_left 5 hN') _)
    _ ≤ 2 ^ 193 := by norm_num

end
end LeanVM.Protocol.EndToEnd.Sound
