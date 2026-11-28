/-
  LeanVM.Protocol.Relation.Statements

  The statements an adversary chooses: one verifier program reading the statement first, its
  roots prefix-free.
-/

module

public import LeanVM.Protocol.Relation.Doomed
public import LeanVM.Protocol.Compile.Drop
public import LeanVM.Protocol.Verifier.PackedPos
public import LeanVM.Arithmetization.Bytecode
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Verifier.Grinds
public import LeanVM.Protocol.Compile.Rom.Sound
import LeanVM.Protocol.Relation.Link.Steps
import LeanVM.Protocol.Relation.Link.Valid

/-!
# Statements chosen by the adversary

The random-oracle theorem takes one program and one certificate; the adversary chooses the
statement. **The program of every statement** (`anyProgram`) reads the bytecode's length and words
and the public input's four lanes as scalars, never absorbed, then runs the leanVM verifier
program of that statement; a statement's root is its history of reads (`stmtHistory`), at which
`anyProgram` is the statement's verifier program (`after_stmtHistory`, `rootOk_stmtHistory`).
Roots are prefix-free (`stmt_eq_of_prefix`), since the bytecode names the program
(`bytecodeWords_injective`) and the digest the public input (`publicDigest_injective`). From tag
`formal-bus-archive`, `EndToEnd/Sound/Statements.lean`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Arithmetization LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Whir.Params

@[expose] public section

/-- **The bytecode names the program.** -/
theorem bytecodeWords_injective : Function.Injective bytecodeWords := by
  intro p p' h
  have hl := congrArg List.length h
  rw [length_bytecodeWords, length_bytecodeWords] at hl
  have hs : p.logSize = p'.logSize := Nat.pow_right_injective (le_refl 2) (by simp only; omega)
  obtain ⟨n, hn, code⟩ := p
  obtain ⟨n', hn', code'⟩ := p'
  simp only at hs
  subst hs
  have hcode : code = code' := by
    funext i
    apply entry_injective
    refine Vector.ext fun j hj ↦ ?_
    have h1 := congrArg (fun l ↦ l.getD ((j + 3) * 2 ^ n + i) 0) h
    rw [bytecodeWords_getD ⟨n, hn, code⟩ (by omega) i.isLt,
      bytecodeWords_getD ⟨n, hn', code'⟩ (by omega) i.isLt] at h1
    rw [encodeSlots_getElem _ _ (show j + 3 < 16 by omega),
      encodeSlots_getElem _ _ (show j + 3 < 16 by omega)] at h1
    simpa [show 3 ≤ j + 3 ∧ j + 3 < 16 by omega] using h1
  subst hcode
  rfl

/-- **The digest names the public input.** -/
theorem publicDigest_injective : Function.Injective publicInputDigest := by
  intro a b h
  have hl : ∀ i : Fin 4, a.lanes i = b.lanes i := by
    intro i
    have hw : (publicInputDigest a)[i.val] = (publicInputDigest b)[i.val] := by rw [h]
    rw [← K.ofLane_lane (a.lanes i), ← K.ofLane_lane (b.lanes i)]
    fin_cases i <;> simp_all [publicInputDigest]
  cases a; cases b
  simp only [PublicInput.mk.injEq]
  exact funext hl

/-- A history of reads: the program's node at it, if any, is reached through read nodes. -/
theorem reachable_of_after_reads {P : VerifierProgram Bool} :
    ∀ (l : List E) {p : VerifierProgram Bool}, P.after (l.map Ev.read) = some p →
      P.Reachable (l.map Ev.read) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intros; exact VerifierProgram.Reachable.nil
  | append_singleton l e ih =>
    intro p hp
    rw [List.map_append, List.map_singleton, VerifierProgram.after_append] at hp
    rcases hq : P.after (l.map Ev.read) with _ | q
    · rw [hq] at hp; cases hp
    · rw [hq, Option.bind_some] at hp
      cases q with
      | read k =>
        rw [List.map_append, List.map_singleton]
        exact VerifierProgram.Reachable.read e (ih hq) hq
      | _ => simp [VerifierProgram.after] at hp

/-- A statement: a program and a public input. -/
abbrev Statement : Type := LeanIsaProgram × PublicInput

/-- A word as a scalar: its first limb. -/
def wordE (k : K) : E := E.ofLimbs k 0

/-- The value of a word, as a natural number. -/
def kNat (k : K) : ℕ := k.toBitVec.toNat

/-- Read `n` words, one per scalar's first limb, then continue with them. -/
def readWords : ℕ → (List K → VerifierProgram Bool) → VerifierProgram Bool
  | 0, k => k []
  | n + 1, k => .read fun e ↦ readWords n fun ws ↦ k (e.limb 0 :: ws)

/-- **The verifier program of every statement**: the bytecode's length and words and the
public input's four lanes, read as scalars, then the leanVM verifier program of that bytecode and
public input. -/
def anyProgram : VerifierProgram Bool :=
  .read fun n ↦ readWords (kNat (n.limb 0)) fun ws ↦ readWords 4 fun ls ↦
    leanVmVerifierProgram ws (publicInputDigest ⟨fun i ↦ ls.getD i 0⟩)

/-- The scalars of a statement: the bytecode's length and words, and the public input's lanes. -/
def stmtScalars (x : Statement) : List E :=
  wordE (K.ofBits (bytecodeWords x.1).length) ::
    ((bytecodeWords x.1).map wordE ++ (List.ofFn x.2.lanes).map wordE)

/-- **The root of a statement**: the history of its reads. -/
def stmtHistory (x : Statement) : List Ev := (stmtScalars x).map Ev.read

theorem limb_wordE (k : K) : (wordE k).limb 0 = k := by simp [wordE]

theorem after_readWords (k : List K → VerifierProgram Bool) :
    ∀ (ws : List K) (rest : List Ev),
      (readWords ws.length k).after ((ws.map wordE).map Ev.read ++ rest) = (k ws).after rest
  | [], rest => rfl
  | w :: ws, rest => by
    simp only [List.length_cons, readWords, List.map_cons, List.cons_append, VerifierProgram.after]
    rw [limb_wordE]
    exact after_readWords (fun ws' ↦ k (w :: ws')) ws rest

theorem after_readWords' (k : List K → VerifierProgram Bool) {n : ℕ} (ws : List K) (hn :
    ws.length = n)
    (rest : List Ev) :
    (readWords n k).after ((ws.map wordE).map Ev.read ++ rest) = (k ws).after rest := by
  subst hn
  exact after_readWords k ws rest

theorem kNat_ofBits {n : ℕ} (hn : n < 2 ^ 64) : kNat (K.ofBits n) = n := by
  change (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem length_bytecodeWords_lt (prog : LeanIsaProgram) : (bytecodeWords prog).length < 2 ^ 64 := by
  rw [length_bytecodeWords]
  have := prog.logSize_le
  unfold Parameters.maxLogBytecode at this
  calc 16 * 2 ^ prog.logSize ≤ 16 * 2 ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
    _ < 2 ^ 64 := by norm_num

/-- **The root of a statement leads to the statement's verifier program.** -/
theorem after_stmtHistory (x : Statement) :
    anyProgram.after (stmtHistory x) =
      some (leanVmVerifierProgram (bytecodeWords x.1) (publicInputDigest x.2)) := by
  simp only [stmtHistory, stmtScalars, List.map_cons, anyProgram, VerifierProgram.after, limb_wordE,
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
    nodeAt anyProgram (stmtHistory x) = leanVmVerifierProgram (bytecodeWords x.1) (publicInputDigest
        x.2) := by
  simp [nodeAt, after_stmtHistory]

theorem commits_stmtHistory (x : Statement) : commits (stmtHistory x) = [] :=
  commits_map_read _

/-- A statement's root is a root of `anyProgram`. -/
theorem rootOk_stmtHistory (x : Statement) : RootOk anyProgram (stmtHistory x) := by
  have ha := after_stmtHistory x
  exact ⟨reachable_of_after_reads _ ha, boundary_map_read (by simp [stmtScalars]),
    grindBits_map_read _, commits_map_read _, by simp [ha], by
      rw [nodeAt_stmtHistory]; exact packedPos_leanVmVerifierProgram _ _⟩

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

theorem length_flatMap_kBytes (ws : List K) : (ws.flatMap K.toBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h8 : (K.toBytes w).length = 8 := rfl
    simp only [List.flatMap_cons, List.length_append, h8, ih, List.length_cons]; ring

/-- The public digest of a seeding's permutation input: its lanes `4 … 7`. -/
def pdOf (t : KeccakState) : Digest :=
  #v[Keccak.lane t 4, Keccak.lane t 5, Keccak.lane t 6, Keccak.lane t 7]

theorem pdOf_seedInput (iv pd : Digest) : pdOf (seedInput iv pd) = pd := by
  ext i hi
  simp only [pdOf]
  interval_cases i <;> simp [seedInput, lane_ofFn]

/-- The leanVM seeding has one hash step, the IV's. -/
theorem length_leanVmSeed_hs (bytecode : List K) (pd : Digest) :
    (leanVmSeed bytecode pd).hs.length = 1 := rfl

/-- **The seedings of the statements**: the statement's seeding (the IV, the hash of the version
tag and the bytecode, then the permutation of the IV and the public digest) and root. The IV is
the permutation input's first four lanes. -/
def leanVmSeeds : Seeds Statement where
  seed x := leanVmSeed (bytecodeWords x.1) (publicInputDigest x.2)
  root := stmtHistory
  offs := []
  refs x ds hds i hi := by
    rw [length_leanVmSeed_hs] at hds
    have hd0 : ds.getD 0 default = ds[0] := by simp [List.getD_eq_getElem?_getD, hds]
    rw [hds] at hi
    interval_cases i
    left
    show laneDigest (seedInput (ds.getD 0 default) (publicInputDigest x.2)) = ds[0]
    rw [laneDigest_seedInput, hd0]
  cap0 x ds := capOf_seedInput _ _
  inj H hH x x' ds ds' ha ha' he := by
    have hl : ds.length = 1 := ha.1
    have hl' : ds'.length = 1 := ha'.1
    have hiv : ds.getD 0 default = ds'.getD 0 default := by
      have := congrArg laneDigest he
      simpa [leanVmSeed, laneDigest_seedInput] using this
    have hpd : publicInputDigest x.2 = publicInputDigest x'.2 := by
      have := congrArg pdOf he
      simpa [leanVmSeed, pdOf_seedInput] using this
    obtain ⟨f0, hf0, hH0⟩ := ha.2 0 (by omega)
    obtain ⟨f0', hf0', hH0'⟩ := ha'.2 0 (by omega)
    simp only [leanVmSeed, List.getElem?_cons_zero, Option.some.injEq] at hf0 hf0'
    subst hf0 hf0'
    have e0 : ds[0] = ds'[0] := by
      simpa [List.getD_eq_getElem?_getD, hl, hl'] using hiv
    rw [e0] at hH0
    have hb := List.append_cancel_left (hH _ _ _ hH0 hH0')
    have hlen : (bytecodeWords x.1).length = (bytecodeWords x'.1).length := by
      have := congrArg List.length hb
      rw [length_flatMap_kBytes, length_flatMap_kBytes] at this
      omega
    have hw := bytecodeWords_injective (flatMap_kBytes_inj hlen hb)
    exact Prod.ext hw (publicDigest_injective hpd)

/-! ## The certificate of every statement -/

variable (O : OpeningIface) (LI : LinkIface) (KI : KeccakIface)

/-- The certificate of a statement: `leanVmCert` at its bytecode and public input. -/
noncomputable def stmtCert (x : Statement) :
    CertG (leanVmVerifierProgram (bytecodeWords x.1) (publicInputDigest x.2))
      (GoodRun O LI (bytecodeWords x.1) x.2) :=
  leanVmCert O LI KI (bytecodeWords x.1) x.2 (ringFactsOf_holds x.2 _)

/-- A good run of a statement's verifier. -/
def stmtG (x : Statement) (h : List Ev) : Prop := GoodRun O LI (bytecodeWords x.1) x.2 h

/-- **Doom for every statement**: past a statement's root, its certificate's doom on the rest. -/
def anyD (h : List Ev) : Prop :=
  ∃ x, stmtHistory x <+: h ∧ (stmtCert O LI KI x).D (h.drop (stmtHistory x).length)

open Classical in
/-- The escape bound for every statement: its certificate's past its root, `0` elsewhere. -/
noncomputable def anyε (h : List Ev) : ENNReal :=
  if hx : ∃ x, stmtHistory x <+: h then
    (stmtCert O LI KI hx.choose).ε (h.drop (stmtHistory hx.choose).length)
  else 0

theorem anyD_iff (x : Statement) (h' : List Ev) :
    anyD O LI KI (stmtHistory x ++ h') ↔ (stmtCert O LI KI x).D h' := by
  constructor
  · rintro ⟨x', hx', hD⟩
    obtain rfl := stmt_eq_of_prefix hx' (List.prefix_append _ _)
    simpa using hD
  · intro hD
    exact ⟨x, List.prefix_append _ _, by simpa using hD⟩

theorem anyε_eq (x : Statement) (h' : List Ev) :
    anyε O LI KI (stmtHistory x ++ h') = (stmtCert O LI KI x).ε h' := by
  unfold anyε
  split
  · rename_i hx
    rw [stmt_eq_of_prefix hx.choose_spec (List.prefix_append _ _)]
    simp
  · rename_i hx
    exact absurd ⟨x, List.prefix_append _ _⟩ hx

/-- A doomed history is past a root. -/
theorem anyD_split {h : List Ev} (hD : anyD O LI KI h) :
    ∃ x h', h = stmtHistory x ++ h' ∧ (stmtCert O LI KI x).D h' := by
  obtain ⟨x, ⟨h', rfl⟩, hD⟩ := hD
  exact ⟨x, h', rfl, by simpa using hD⟩

/-- **A good run of some statement**: past a statement's root, a good run of its verifier. -/
def anyG (h : List Ev) : Prop :=
  ∃ x h', h = stmtHistory x ++ h' ∧ stmtG O LI x h'

/-- **The certificate of every statement.** -/
noncomputable def anyCert : CertG anyProgram (anyG O LI) where
  D := anyD O LI KI
  ε := anyε O LI KI
  read := by
    intro h k e hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split O LI KI hD
    have hax := after_stmtHistory x
    rw [List.append_assoc, anyD_iff]
    exact (stmtCert O LI KI x).read e
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  readPacked := by
    intro h n k xs hr ha hn hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split O LI KI hD
    have hax := after_stmtHistory x
    rw [List.append_assoc, anyD_iff]
    exact (stmtCert O LI KI x).readPacked xs
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hn hDx
  grind := by
    intro h b k hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split O LI KI hD
    have hax := after_stmtHistory x
    rw [List.append_assoc, anyD_iff]
    exact (stmtCert O LI KI x).grind
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  commit := by
    intro h ht w k word hr ha hw hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split O LI KI hD
    have hax := after_stmtHistory x
    rw [List.append_assoc, anyD_iff]
    exact (stmtCert O LI KI x).commit word
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hw hDx
  group := by
    intro h p hr hb ha hp hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split O LI KI hD
    have hax := after_stmtHistory x
    rw [esc_drop (h₀ := stmtHistory x) (commits_stmtHistory x) (anyD_iff O LI KI x), anyε_eq]
    exact (stmtCert O LI KI x).group (reachable_drop hax (commits_stmtHistory x) hr h' rfl)
      (boundary_drop hb) (by rwa [after_drop hax] at ha) hp hDx
  final := by
    intro h hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyD_split O LI KI hD
    have hax := after_stmtHistory x
    exact ⟨x, h', rfl, (stmtCert O LI KI x).final
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx⟩

theorem grindBits_stmt (x : Statement) (h' : List Ev) :
    grindBits (stmtHistory x ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil]; exact grindBits_map_read _
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- A statement's certificate's bound at the random-oracle theorem's discount. -/
theorem stmtCert_bound (x : Statement) (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ min (grindBits h) 64 * (stmtCert O LI KI x).ε h ≤ εmsg := by
  by_cases hr : (leanVmVerifierProgram (bytecodeWords x.1) (publicInputDigest x.2)).Reachable h
  · rw [min_eq_left (grindBits_le_of_reachable _ _ hr)]
    exact leanVmCert_bound O LI KI _ _ _ h
  · change (2 : ENNReal)⁻¹ ^ min (grindBits h) 64 * Spec.certε _ h ≤ εmsg
    simp only [Spec.certε, hr, false_and, ↓reduceIte, mul_zero, zero_le]

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `2^-125`. -/
theorem anyCert_bound (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ min (grindBits h) 64 * (anyCert O LI KI).ε h ≤ εmsg := by
  by_cases hx : ∃ x, stmtHistory x <+: h
  · obtain ⟨x, h', rfl⟩ : ∃ x h', h = stmtHistory x ++ h' := by
      obtain ⟨x, h', he⟩ := hx
      exact ⟨x, h', he.symm⟩
    show _ * anyε O LI KI _ ≤ _
    rw [anyε_eq, grindBits_stmt]
    exact stmtCert_bound O LI KI x h'
  · show _ * anyε O LI KI _ ≤ _
    simp only [anyε, hx, ↓reduceDIte, mul_zero, zero_le]

/-! ## The verifier of every statement -/

/-- The verifier of the statement and proof `z` is the compiled leanVM verifier. -/
theorem verifierFam_leanVm (z : Statement × Proof) :
    verifierFam leanVmSeeds anyProgram z =
      verifierComp (leanVmSeed (bytecodeWords z.1.1) (publicInputDigest z.1.2))
        (leanVmVerifierProgram (bytecodeWords z.1.1) (publicInputDigest z.1.2)) z.2 := by
  simp only [verifierFam, leanVmSeeds, nodeAt_stmtHistory]

theorem isTotalQueryBound_leanVmFam (z : Statement × Proof) :
    OracleComp.IsTotalQueryBound (verifierFam leanVmSeeds anyProgram z) leanVmQueryBound := by
  rw [verifierFam_leanVm]
  exact isTotalQueryBound_leanVm _ _ _

/-! ## From a statement's doom to doom for every statement -/

/-- A compiled run from a longer history extends the same history. -/
theorem xrun_append_hist (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)
    {α : Type} : ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h₀ h : List Ev),
      xrun H F p s (h₀ ++ h) = (xrun H F p s h).map fun r ↦ (r.1, r.2.1, h₀ ++ r.2.2)
  | .ret a, s, h₀, h => rfl
  | .fail, s, h₀, h => rfl
  | .read k, s, h₀, h => by
    simp only [xrun]
    split
    · rcases absorb (m := Option) F s.sponge _ _ with _ | sp
      · rfl
      · simp only [Option.bind_some, List.append_assoc]
        exact xrun_append_hist H F _ _ h₀ _
    · rfl
  | .sample k, s, h₀, h => by
    simp only [xrun]
    rcases squeeze (m := Option) F s.sponge with _ | r
    · rfl
    · simp only [Option.bind_some, List.append_assoc]
      exact xrun_append_hist H F _ _ h₀ _
  | .readPacked n k, s, h₀, h => by
    simp only [xrun]
    split
    · rcases observePacked (m := Option) F s.sponge (s.stream.take n) with _ | sp
      · rfl
      · simp only [Option.bind_some, List.append_assoc]
        exact xrun_append_hist H F _ _ h₀ _
    · rfl
  | .samplePacked n k, s, h₀, h => by
    simp only [xrun]
    rcases samplesPacked (m := Option) F s.sponge n with _ | r
    · rfl
    · simp only [Option.bind_some, List.append_assoc]
      exact xrun_append_hist H F _ _ h₀ _
  | .grind bits k, s, h₀, h => by
    simp only [xrun]
    split
    · rcases absorbNonce (m := Option) F s.sponge _ with _ | r
      · rfl
      · simp only [Option.bind_some]
        split
        · rw [List.append_assoc]; exact xrun_append_hist H F _ _ h₀ _
        · rfl
    · rfl
  | .commit height width k, s, h₀, h => by
    simp only [xrun]
    split
    · rcases absorb (m := Option) F s.sponge _ _ with _ | sp0
      · rfl
      · simp only [Option.bind_some]
        rcases absorb (m := Option) F sp0 _ _ with _ | sp1
        · rfl
        · simp only [Option.bind_some]
          rw [List.append_assoc]; exact xrun_append_hist H F _ _ h₀ _
    · rfl
  | .query i ps k, s, h₀, h => by
    simp only [xrun]
    split
    · split
      · rw [List.append_assoc]; exact xrun_append_hist H F _ _ h₀ _
      · rfl
    · rfl

/-- The extracted history of a run from a statement's root is the root followed by the
extracted history from the empty history. -/
theorem extractedFrom_eq (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)
    (σ : Seed) (p : VerifierProgram Bool) (h₀ : List Ev) (π : Proof)
    (hv : Rom.verify H F σ p π = some true) :
    extractedFrom H F σ p h₀ π = h₀ ++ extractedHistory H F σ p π := by
  obtain ⟨seed, s, hseed, hx⟩ := xrun_of_verify hv
  have hx' := xrun_append_hist H F p ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ h₀ []
  rw [List.append_nil, hx, Option.map_some] at hx'
  simp only [extractedFrom, hseed, hx']

/-- **A statement's doom is doom for every statement.** -/
theorem doomed_of_doomedRun {x : Statement} {π : Proof} {c : KeccakCalls.QueryCache}
    (hv : Rom.verify (fun y ↦ c (.inl y)) (fun t ↦ c (.inr t))
      (leanVmSeed (bytecodeWords x.1) (publicInputDigest x.2))
      (leanVmVerifierProgram (bytecodeWords x.1) (publicInputDigest x.2)) π = some true)
    (hd : DoomedRun (stmtCert O LI KI x) (leanVmSeed (bytecodeWords x.1) (publicInputDigest x.2))
      π c) :
    Doomed (anyCert O LI KI) leanVmSeeds (x, π) c := by
  obtain ⟨h₀, hh₀, hb, hD⟩ := hd
  refine ⟨stmtHistory x ++ h₀, ?_,
    by show (stmtHistory x).length ≤ _; rw [List.length_append]; omega, ?_,
    (anyD_iff O LI KI x h₀).mpr hD⟩
  · change stmtHistory x ++ h₀ <+: extractedFrom (fun y ↦ c (.inl y)) (fun t ↦ c (.inr t))
      (leanVmSeed (bytecodeWords x.1) (publicInputDigest x.2)) (nodeAt anyProgram (stmtHistory x))
      (stmtHistory x) π
    rw [nodeAt_stmtHistory, extractedFrom_eq _ _ _ _ _ _ hv]
    exact (List.prefix_append_right_inj _).mpr hh₀
  · rcases List.eq_nil_or_concat h₀ with rfl | ⟨h'', e, rfl⟩
    · rw [List.append_nil]; exact (rootOk_stmtHistory x).2.1
    · rw [List.concat_eq_append] at hb ⊢
      rw [← List.append_assoc]
      exact boundary_append_of hb

/-- **A statement's run that is not good is not good for every statement.** -/
theorem not_anyG_of {x : Statement} {π : Proof} {c : KeccakCalls.QueryCache}
    (hv : Rom.verify (fun y ↦ c (.inl y)) (fun t ↦ c (.inr t))
      (leanVmSeed (bytecodeWords x.1) (publicInputDigest x.2))
      (leanVmVerifierProgram (bytecodeWords x.1) (publicInputDigest x.2)) π = some true)
    (hg : ¬ stmtG O LI x (extractedHistory (fun y ↦ c (.inl y)) (fun t ↦ c (.inr t))
      (leanVmSeed (bytecodeWords x.1) (publicInputDigest x.2))
      (leanVmVerifierProgram (bytecodeWords x.1) (publicInputDigest x.2)) π)) :
    ¬ anyG O LI (extractedFrom (fun y ↦ c (.inl y)) (fun t ↦ c (.inr t))
      (leanVmSeed (bytecodeWords x.1) (publicInputDigest x.2)) (nodeAt anyProgram (stmtHistory x))
      (stmtHistory x) π) := by
  rintro ⟨x', h', he, hG⟩
  rw [nodeAt_stmtHistory, extractedFrom_eq _ _ _ _ _ _ hv] at he
  obtain rfl := stmt_eq_of_prefix ⟨_, he.symm⟩ (List.prefix_append _ _)
  rw [List.append_cancel_left he] at hg
  exact hg hG

end

end LeanVM.Protocol.Relation
