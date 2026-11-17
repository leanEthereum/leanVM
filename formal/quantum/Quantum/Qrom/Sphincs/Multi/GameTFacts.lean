module

public import Quantum.Qrom.Sphincs.Multi.GameTFactsPre

@[expose] public section

/-!
# The classification facts of leanSPHINCS's multi-user challenge prefix in the QROM

The `n`-user analog of `Quantum.Qrom.Sphincs.GameTFactsPre`. On every branch of the challenge
prefix at the event side's digest policies (`prefixQSN (strPolN n)`), in the decompressed basis,
the register satisfies, per user `i`, the hypotheses of `win_imp_badQN` against user `i`'s run's
table `runTab (userOf θ i) (labU L i)` (`L` the register's label) and the view's hash.

* **The invariant** (`InvQSN log T`): no empty cell, each user's stream bookkeeping on its part of
  the label, and for every family of tables compatible with the label (`CompatSN`): each user's
  transcript's signatures are its table's, its memory records its requests' selections and only
  selections, its memo holds the view's selections of requested keys (`MemoOkSN`), and every
  hardwired cell is a signed digest cell or a published position's cell of some user.
* **One signature** (`invQSN_step`, `htQ₂SN_signInv`): user `j`'s signature with the memo keeps
  the invariant, the transcript grown by the request and the memo by its answer.
* **The prefix** (`htQ_logSignsSN`, `htQ₂SN_prefixS`): the adversary's memo transform moves the
  invariant along all users' transcript, each user within its signing budget.
* **The facts** (`PreFactsQSN`, `preFactsQSN_of`, `prefixFactsQSN`): per user, the transcript's
  signatures and records, under distinct `PK.seed`s the hardwired chain steps and FORS leaves known
  (`HwKnown`) and the hardwired call-0 `H_msg` cells with the user's `PK.seed` signed digests
  (`HwDigestsP`), and every signed view covered by the user's `starCover (streamOf ·)`.
-/

open Matrix IPFunctor
open scoped Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos ValPos Known layerDisclosed forsDisclosed Covered)
open Quantum.Xmss.Hybrid (restrictTo)
open Quantum.Xmss.Assembly (recHwSpec realizeT revealThen RevealVals runtimeR NoBot initU
  noBot_init querySupportedOn_conj_compressReg querySupportedOn_inter realizeT_substitute)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muLogSigns muLogAfter withMuSignLog MuSignLog
  cmdCharge signChargeAt)

attribute [local irreducible] sphincsRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MuPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n Message (Option Signature))

/-! ## Transcripts -/

section log

variable (log : MuSignLog n Message (Option Signature)) (j : Fin n) (r : Message)
  (b : Option Signature)

theorem userS_append (i : Fin n) :
    MuSignLog.user (log ++ [⟨(j, r), b⟩]) i =
      MuSignLog.user log i ++ if j = i then [⟨r, b⟩] else [] :=
  SufCma.Multi.MuSignLog.user_append_singleton log j r b i

theorem userS_append_self :
    MuSignLog.user (log ++ [⟨(j, r), b⟩]) j = MuSignLog.user log j ++ [⟨r, b⟩] := by
  rw [userS_append, ite_eq_left rfl]

theorem userS_append_of_ne {i : Fin n} (h : j ≠ i) :
    MuSignLog.user (log ++ [⟨(j, r), b⟩]) i = MuSignLog.user log i := by
  rw [userS_append, ite_eq_right h, List.append_nil]

variable {log j r b}

theorem mem_userS_append_left {i : Fin n} {q : (_ : Message) × Option Signature}
    (hq : q ∈ MuSignLog.user log i) : q ∈ MuSignLog.user (log ++ [⟨(j, r), b⟩]) i := by
  rw [userS_append]
  exact List.mem_append_left _ hq

variable (log j r b) in
theorem mem_userS_append_self :
    (⟨r, b⟩ : (_ : Message) × Option Signature) ∈ MuSignLog.user (log ++ [⟨(j, r), b⟩]) j := by
  rw [userS_append_self]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem mem_userS_append {i : Fin n} {q : (_ : Message) × Option Signature}
    (hq : q ∈ MuSignLog.user (log ++ [⟨(j, r), b⟩]) i) :
    q ∈ MuSignLog.user log i ∨ (j = i ∧ q = ⟨r, b⟩) := by
  rw [userS_append] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact .inl hq
  · split_ifs at hq with hji
    · exact .inr ⟨hji, List.mem_singleton.mp hq⟩
    · exact absurd hq List.not_mem_nil

end log

/-! ## The memory after a signature with the memo -/

section grind3N

variable (P : HashDomain → PairOut) (seed : PublicParameter)

theorem grindO_of_ne {K K' : Key} (m : Digest) (h : K' ≠ K) (o : Option SelS) (mem : SelMem) :
    grindO P seed K m o mem K' = mem K' := by
  cases o with
  | some _ => rfl
  | none => exact grindMemS_of_ne P seed K m h _ _ _

theorem grindO_of_ne_none (K : Key) (m : Digest) {K' : Key} (o : Option SelS) {mem : SelMem}
    (hm : mem K' ≠ none) : grindO P seed K m o mem K' = mem K' := by
  cases o with
  | some _ => rfl
  | none => exact grindMemS_of_ne_none P seed K m _ _ mem hm

variable (θ : TVals) (idx : Index) (h : KeyMemo)

theorem grind3N_of_ne_none {mem : SelMem} {K : Key} (hm : mem K ≠ none) :
    grind3N θ P idx h mem K = mem K := by
  unfold grind3N
  have h1 := grindO_of_ne_none P (tabOf θ).publicSeed (keyOf 0 idx)
    ((tabOf θ).layerMessage idx 0) (h (keyOf 0 idx)) hm
  have h2 := (grindO_of_ne_none P (tabOf θ).publicSeed (keyOf 1 idx)
    ((tabOf θ).layerMessage idx 1) (h (keyOf 1 idx)) (by rw [h1]; exact hm)).trans h1
  rw [grindO_of_ne_none _ _ _ _ _ (by rw [h2]; exact hm), h2]

theorem grind3N_of_ne {mem : SelMem} {K : Key} (hK : ∀ l, K ≠ keyOf l idx) :
    grind3N θ P idx h mem K = mem K := by
  unfold grind3N
  rw [grindO_of_ne _ _ _ (hK 2), grindO_of_ne _ _ _ (hK 1), grindO_of_ne _ _ _ (hK 0)]

theorem grind3N_hit0 {mem : SelMem} (hh : h (keyOf 0 idx) ≠ none) :
    grind3N θ P idx h mem (keyOf 0 idx) = mem (keyOf 0 idx) := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hh
  unfold grind3N
  rw [grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (0 : Layer) ≠ 2)),
    grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (0 : Layer) ≠ 1)), ho, grindO_some]

theorem grind3N_hit1 {mem : SelMem} (hh : h (keyOf 1 idx) ≠ none) :
    grind3N θ P idx h mem (keyOf 1 idx) = mem (keyOf 1 idx) := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hh
  unfold grind3N
  rw [grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (1 : Layer) ≠ 2)), ho, grindO_some,
    grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (1 : Layer) ≠ 0))]

theorem grind3N_hit2 {mem : SelMem} (hh : h (keyOf 2 idx) ≠ none) :
    grind3N θ P idx h mem (keyOf 2 idx) = mem (keyOf 2 idx) := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hh
  unfold grind3N
  rw [ho, grindO_some, grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (2 : Layer) ≠ 1)),
    grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (2 : Layer) ≠ 0))]

/-- **A memoized key's memory is kept.** -/
theorem grind3N_of_hit {mem : SelMem} (l : Layer) (hh : h (keyOf l idx) ≠ none) :
    grind3N θ P idx h mem (keyOf l idx) = mem (keyOf l idx) := by
  fin_cases l
  · exact grind3N_hit0 P θ idx h hh
  · exact grind3N_hit1 P θ idx h hh
  · exact grind3N_hit2 P θ idx h hh

theorem grind3N_key0 {mem : SelMem} (hm : mem (keyOf 0 idx) = none)
    (hh : h (keyOf 0 idx) = none) :
    grind3N θ P idx h mem (keyOf 0 idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx 0).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) 0 idx) := by
  unfold grind3N
  rw [grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (0 : Layer) ≠ 2)),
    grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (0 : Layer) ≠ 1)), hh, grindO_none,
    grindMemS_self _ _ _ _ _ _ _ hm]
  rfl

theorem grind3N_key1 {mem : SelMem} (hm : mem (keyOf 1 idx) = none)
    (hh : h (keyOf 1 idx) = none) :
    grind3N θ P idx h mem (keyOf 1 idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx 1).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) 1 idx) := by
  unfold grind3N
  rw [grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (1 : Layer) ≠ 2)), hh, grindO_none,
    grindMemS_self _ _ _ _ _ _ _
      ((grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (1 : Layer) ≠ 0)) _ _).trans hm)]
  rfl

theorem grind3N_key2 {mem : SelMem} (hm : mem (keyOf 2 idx) = none)
    (hh : h (keyOf 2 idx) = none) :
    grind3N θ P idx h mem (keyOf 2 idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx 2).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) 2 idx) := by
  unfold grind3N
  rw [hh, grindO_none, grindMemS_self _ _ _ _ _ _ _
    (((grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (2 : Layer) ≠ 1)) _ _).trans
      (grindO_of_ne _ _ _ (keyOf_ne_layer idx (by decide : (2 : Layer) ≠ 0)) _ _)).trans hm)]
  rfl

/-- **A search records its selection** at an unselected key missing from the memo. -/
theorem grind3N_key {mem : SelMem} (l : Layer) (hm : mem (keyOf l idx) = none)
    (hh : h (keyOf l idx) = none) :
    grind3N θ P idx h mem (keyOf l idx) = ((tabOf θ).layerSelect (fun z ↦ (P z).1) idx l).map
      (recOfS (tabOf θ) (fun z ↦ (P z).1) l idx) := by
  fin_cases l
  · exact grind3N_key0 P θ idx h hm hh
  · exact grind3N_key1 P θ idx h hm hh
  · exact grind3N_key2 P θ idx h hm hh

end grind3N

theorem layerSels_eq (g : Layer → SelS) : layerSels (g 0) (g 1) (g 2) = g := by
  funext l
  fin_cases l <;> rfl

/-! ## The invariant of the challenge prefix at the event side's policies -/

section inv

/-- **User `i`'s memo holds the view's selections of requested keys.** -/
def MemoOkSN (w : QTable) (H : HashDomain → HashOutput) (log : SLogS) (h : KeyMemo) : Prop :=
  ∀ K o, h K = some o → ∃ q ∈ log, ∃ l, K = keyOf l (w.index q.1) ∧
    o = w.layerSelect H (w.index q.1) l

/-- **A family of tables compatible with the label `L`**, user by user. -/
def CompatSN (θ : TValsN n) (L : Finset (TPosN n)) (W : Fin n → QTable) : Prop :=
  ∀ i, CompatS (userOf θ i) (labU L i) (W i)

/-- **The facts of a register** against the tables `W` and the hash `H`: per user, the
transcript's signatures are the table's, the memory records every request's selections and only
selections, the memo holds the view's selections of requested keys; every hardwired cell is a
signed message's digest cell with its pair or a published position's cell, of some user. -/
def FactsSN (S0 : Fin n → MasterSeed) (W : Fin n → QTable) (H : HashDomain → HashOutput)
    (log : MuSignLog n Message (Option Signature)) (T : SelMemoS n)
    (s : RRegSN n (SelMemN n)) : Prop :=
  (∀ i, ∀ q ∈ log.user i, q.2 = (W i).signature H q.1) ∧
    (∀ i, ∀ q ∈ log.user i, Records (W i) H (s.2.2.2 i) q.1) ∧
    (∀ i, MemOkS (W i) H (s.2.2.2 i)) ∧ (∀ i, MemoOkSN (W i) H (log.user i) (T i)) ∧
    ∀ z ω, s.2.1.1 z = some ω → ∃ i,
      (∃ q ∈ log.user i, z = cellOf (S0 i) (digPos q.1) (W i) ∧ ω = W i (digPos q.1)) ∨
        ∃ q ∈ log.user i, ∃ p, PubBy (W i) H q.1 p ∧ z = cellOf (S0 i) p (W i)

/-- **The invariant along the challenge prefix** with all users' transcript `log` and the memo
`T`: no empty cell, each user's stream bookkeeping, and the facts against every family of tables
compatible with the label, with the hash of the register's view. -/
def InvQSN (θ : TValsN n) (log : MuSignLog n Message (Option Signature)) (T : SelMemoS n) :
    Set (RRegSN n (SelMemN n)) :=
  {s | NoBot s ∧ (∀ i, StrOk (labU s.2.2.1 i) (log.user i)) ∧
    ∀ W, CompatSN θ s.2.2.1 W → FactsSN (seedsOf θ) W (hHSN s) log T s}

set_option maxHeartbeats 400000 in
/-- **One signature of user `j` keeps the invariant**, from its effect on the decompressed
register: the request and its answer appended, the answer's selections memoized. -/
theorem invQSN_step {θ : TValsN n} {log : MuSignLog n Message (Option Signature)}
    {T : SelMemoS n} {j : Fin n} {msg : Message} {s s' : RRegSN n (SelMemN n)}
    {a : Option Signature × MemoAns} (hs : s ∈ InvQSN θ log T)
    (he : SignEffN θ j msg (T j) s a s') :
    s' ∈ InvQSN θ (log ++ [⟨(j, msg), a.1⟩]) (T.put j a.2) := by
  obtain ⟨-, hok, hF⟩ := hs
  obtain ⟨hnb, henc, hsub, hnew, hstr, hmem, g₀, g₁, g₂, hg0, hg1, hg2, ha, hW⟩ := he
  have hlabU : ∀ i, i ≠ j → labU s'.2.2.1 i = labU s.2.2.1 i := fun i hi ↦ by
    ext t
    rw [mem_labU, mem_labU]
    refine ⟨fun ht ↦ ?_, fun ht ↦ hsub ht⟩
    rcases hnew _ ht with h | ⟨h, -⟩
    · exact h
    · exact absurd h hi
  have hsubj : labU s.2.2.1 j ⊆ labU s'.2.2.1 j := fun t ht ↦ mem_labU.2 (hsub (mem_labU.1 ht))
  have hnewj : ∀ t ∈ labU s'.2.2.1 j,
      t ∈ labU s.2.2.1 j ∨ t.IsVal ∨ t ∈ strNeed (labU s.2.2.1 j) msg := fun t ht ↦ by
    rcases hnew _ (mem_labU.1 ht) with h | ⟨-, h⟩
    · exact .inl (mem_labU.2 h)
    · exact .inr h
  have hstrj : strNeed (labU s.2.2.1 j) msg ⊆ labU s'.2.2.1 j :=
    fun t ht ↦ mem_labU.2 (hstr (mk_mem_atU j ht))
  have hok' : ∀ i, StrOk (labU s'.2.2.1 i) (MuSignLog.user (log ++ [⟨(j, msg), a.1⟩]) i) := by
    intro i
    by_cases hij : i = j
    · subst i
      rw [userS_append_self]
      exact strOk_step hnewj (hok j) hsubj hstrj
    · rw [userS_append_of_ne _ _ _ _ (Ne.symm hij), hlabU i hij]
      exact hok i
  have hmj : s'.2.2.2 j = grind3N (userOf θ j) (hvwSN s)
      (idxS (userOf θ j) (labU s.2.2.1 j) msg) (T j) (s.2.2.2 j) := by
    rw [hmem, Function.update_self]
  have hmi : ∀ i, i ≠ j → s'.2.2.2 i = s.2.2.2 i := fun i hi ↦ by
    rw [hmem, Function.update_of_ne hi]
  refine ⟨hnb, hok', fun W hW' ↦ ?_⟩
  have hWo : CompatSN θ s.2.2.1 W := fun i ↦ by
    by_cases hij : i = j
    · subst i
      exact compatS_anti (hW' j) (hok' j) hsubj
    · rw [← hlabU i hij]
      exact hW' i
  obtain ⟨hlog, hrec, hmok, hmemo, hhw⟩ := hF W hWo
  have hea : ∀ i, EncAgree (W i).publicSeed (hHSN s) (hHSN s') := fun i l τ e m c ↦
    congrArg Prod.fst (henc _ l τ e m c).symm
  have hwj := hW' j
  have hdig : W j (digPos msg) = dgS (userOf θ j) (labU s.2.2.1 j) msg := by
    obtain ⟨hm, hp⟩ := pairAt_markC_step (θ := userOf θ j) (hok' j) hstrj
    exact (hwj.2 msg hm).trans hp
  have hidx : (W j).index msg = idxS (userOf θ j) (labU s.2.2.1 j) msg :=
    congrArg (fun y ↦ digestIndex (digestOfPair y)) hdig
  have hlv : (W j).leaves msg = lvS (userOf θ j) (labU s.2.2.1 j) msg :=
    congrArg (fun y ↦ digestForsLeaves (digestOfPair y)) hdig
  have hselT : ∀ l, (W j).layerSelect (hHSN s) ((W j).index msg) l =
      (tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) l :=
    fun l ↦ by rw [hidx]; exact hwj.1.layerSelect _ _ _
  have key : ∀ (l : Layer) (g : SelS),
      g = (T j (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
        ((tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) l) →
      g = (W j).layerSelect (hHSN s) ((W j).index msg) l := fun l g hg ↦ by
    rw [hselT]
    rcases hT : T j (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j) msg)) with _ | o
    · rw [hT, Option.getD_none] at hg
      exact hg
    · rw [hT, Option.getD_some] at hg
      obtain ⟨q, -, l', hK, ho⟩ := hmemo j _ o hT
      obtain rfl : l = l' := congrArg Prod.fst hK
      rw [hg, ho, layerSelect_congr hK.symm]
      exact hwj.1.layerSelect _ _ _
  have h0 := key 0 g₀ hg0
  have h1 := key 1 g₁ hg1
  have h2 := key 2 g₂ hg2
  rw [← hidx] at hmj
  have hsigN : a.1 = (W j).signature (hHSN s) msg := by
    rw [ha, signature_eq_sigOf3, hwj.1.randomizer, hwj.1.forsOpening, hwj.1.layerSig,
      hwj.1.layerSig, hwj.1.layerSig, layerSig_eq_mapOpen, layerSig_eq_mapOpen,
      layerSig_eq_mapOpen, ← hwj.1.layerSelect, ← hwj.1.layerSelect, ← hwj.1.layerSelect,
      ← h0, ← h1, ← h2, hidx, hlv]
  have hrecN : Records (W j) (hHSN s) (s'.2.2.2 j) msg := by
    intro l sel hls
    rw [hmj]
    have e1 : (tabOf (userOf θ j)).layerSelect (hHSN s) ((W j).index msg) l = some sel :=
      (hwj.1.layerSelect _ _ _).symm.trans hls
    rcases hh : T j (keyOf l ((W j).index msg)) with _ | o
    · rcases hk : s.2.2.2 j (keyOf l ((W j).index msg)) with _ | c
      · rw [grind3N_key _ _ _ _ l hk hh]
        exact (congrArg (Option.map _) e1).trans
          (congrArg some (recOfS_offDig hwj.1 (hHSN s) l ((W j).index msg) sel).symm)
      · obtain ⟨l', idx', sel', hK, hs', rfl⟩ := hmok j _ c hk
        obtain rfl : l' = l := congrArg Prod.fst hK
        rw [layerSelect_congr hK, hls] at hs'
        obtain rfl := Option.some.inj hs'
        rw [grind3N_of_ne_none _ _ _ _ (by rw [hk]; exact Option.some_ne_none _), hk]
        exact congrArg some (recOfS_key hK sel)
    · obtain ⟨q, hq, l', hK, -⟩ := hmemo j _ o hh
      obtain rfl : l = l' := congrArg Prod.fst hK
      rw [grind3N_of_hit _ _ _ _ l (by rw [hh]; exact Option.some_ne_none _), hK]
      exact (hrec j q hq l sel ((layerSelect_congr hK.symm).trans hls)).trans
        (congrArg some (recOfS_key hK.symm sel))
  have hmokN : MemOkS (W j) (hHSN s) (s'.2.2.2 j) := by
    intro K c hc
    rw [hmj] at hc
    by_cases hK0 : s.2.2.2 j K = none
    · by_cases hK : ∃ l, K = keyOf l ((W j).index msg)
      · obtain ⟨l, rfl⟩ := hK
        rcases hh : T j (keyOf l ((W j).index msg)) with _ | o
        · rw [grind3N_key _ _ _ _ l hK0 hh] at hc
          obtain ⟨sel, hsel, rfl⟩ := Option.map_eq_some_iff.1 hc
          exact ⟨l, (W j).index msg, sel, rfl, (hwj.1.layerSelect _ _ _).trans hsel,
            (recOfS_offDig hwj.1 (hHSN s) l ((W j).index msg) sel).symm⟩
        · rw [grind3N_of_hit _ _ _ _ l (by rw [hh]; exact Option.some_ne_none _), hK0] at hc
          cases hc
      · rw [grind3N_of_ne _ _ _ _ (fun l h ↦ hK ⟨l, h⟩), hK0] at hc
        cases hc
    · rw [grind3N_of_ne_none _ _ _ _ hK0] at hc
      exact hmok j K c hc
  refine ⟨fun i q hq ↦ ?_, fun i q hq ↦ ?_, fun i ↦ ?_, fun i K o ho ↦ ?_, fun z ω hz ↦ ?_⟩
  · rcases mem_userS_append hq with hq | ⟨rfl, rfl⟩
    · rw [hlog i q hq, signature_congrH (hea i)]
    · exact hsigN.trans (signature_congrH (hea _) msg)
  · refine records_congrH (hea i) ?_
    rcases mem_userS_append hq with hq | ⟨rfl, rfl⟩
    · by_cases hij : i = j
      · subst i
        intro l sel hls
        have h0 := hrec j q hq l sel hls
        rw [hmj, grind3N_of_ne_none _ _ _ _ (by rw [h0]; exact Option.some_ne_none _), h0]
      · rw [hmi i hij]
        exact hrec i q hq
    · exact hrecN
  · refine memOkS_congrH (hea i) ?_
    by_cases hij : i = j
    · subst i
      exact hmokN
    · rw [hmi i hij]
      exact hmok i
  · by_cases hit : i = j ∧ K = keyOf K.1 a.2.1
    · obtain ⟨hij, hK⟩ := hit
      subst i
      rw [hK, SelMemoS.put_self] at ho
      obtain rfl := Option.some.inj ho
      refine ⟨⟨msg, a.1⟩, mem_userS_append_self _ _ _ _, K.1, ?_, ?_⟩
      · rw [hidx]
        exact hK.trans (congrArg (keyOf K.1) (by rw [ha]))
      · have hl : ∀ l, a.2.2 l = (W j).layerSelect (hHSN s) ((W j).index msg) l := fun l ↦ by
          rw [ha]
          show layerSels g₀ g₁ g₂ l = _
          rw [h0, h1, h2]
          exact congrFun (layerSels_eq fun l ↦ (W j).layerSelect (hHSN s) ((W j).index msg) l) l
        rw [hl, (hea j).layerSelect]
    · rw [SelMemoS.put_of_ne _ hit] at ho
      obtain ⟨q, hq, l, hK, ho'⟩ := hmemo i K o ho
      exact ⟨q, mem_userS_append_left hq, l, hK, ho'.trans ((hea i).layerSelect _ _)⟩
  · rcases hW z ω hz with h | ⟨rfl, rfl⟩ | ⟨sel₀, sel₁, sel₂, e0, e1, e2, p, hp, rfl⟩
    · obtain ⟨i, hi⟩ := hhw z ω h
      refine ⟨i, ?_⟩
      rcases hi with ⟨q, hq, e1, e2⟩ | ⟨q, hq, p, hp, e1⟩
      · exact .inl ⟨q, mem_userS_append_left hq, e1, e2⟩
      · exact .inr ⟨q, mem_userS_append_left hq, p, pubBy_congrH (hea i) hp, e1⟩
    · exact ⟨j, .inl ⟨⟨msg, a.1⟩, mem_userS_append_self _ _ _ _,
        (hwj.1.cellOf (seedsOf θ j) (digPos msg)).symm, hdig.symm⟩⟩
    · have hpub : PubBy (W j) (hHSN s) msg p := by
        refine ⟨sel₀, sel₁, sel₂, by rw [← h0, e0], by rw [← h1, e1], by rw [← h2, e2], ?_⟩
        rw [hidx, hlv]
        exact hp
      exact ⟨j, .inr ⟨⟨msg, a.1⟩, mem_userS_append_self _ _ _ _, p, pubBy_congrH (hea j) hpub,
        (hwj.1.cellOf (seedsOf θ j) p).symm⟩⟩

variable {m₀ : Finset (TPosN n) × SelMemN n}

variable (θ : TValsN n) in
/-- **User `j`'s signature at the event side's policy keeps the invariant `InvQSN`.** -/
theorem htQ₂SN_signInv (B : QReg) (j : Fin n) (msg : Message)
    (log : MuSignLog n Message (Option Signature)) (T : SelMemoS n) :
    HTQ₂SN m₀ (realizeT θ (signTN (SelMemN n) cwUpdN (strPolN n) j B msg (T j)))
      (InvQSN θ log T) fun a ↦ InvQSN θ (log ++ [⟨(j, msg), a.1⟩]) (T.put j a.2) :=
  (htQ₂SN_signS θ j B msg (T j) _ fun _ hs ↦ hs.1).mono subset_rfl fun _ ↦ by
    rintro s' ⟨s, hs, he⟩
    exact invQSN_step hs he

end inv

/-! ## The challenge prefix -/

section prefixRun

variable {m₀ : Finset (TPosN n) × SelMemN n}

/-- **The adversary's memo transform with all users' transcript**, each user `i` within its
signing budget: from a transcript of user `i`'s length at most `K` less `i`'s remaining budget
`k i`, sponge-only steps keep `Inv log T`, a signing request of user `j` moves it to the extended
transcript and memo. -/
theorem htQ_logSignsSN (θ : TValsN n) (K : ℕ)
    (Inv : MuSignLog n Message (Option Signature) → SelMemoS n → Set (RRegSN n (SelMemN n)))
    (hsign : ∀ (B : QReg) (j : Fin n) (msg : Message)
      (log : MuSignLog n Message (Option Signature)) (T : SelMemoS n),
      HTQ₂SN m₀ (realizeT θ (signTN (SelMemN n) cwUpdN (strPolN n) j B msg (T j)))
        (Inv log T) fun a ↦ Inv (log ++ [⟨(j, msg), a.1⟩]) (T.put j a.2))
    {Ω Y : QReg → Type} (leaf : ∀ u, Ω u → MuSignLog n Message (Option Signature) → Y u)
    (Q : (Σ u, Y u) → Set (RRegSN n (SelMemN n)))
    (hleaf : ∀ u y log T, (∀ i, (log.user i).length ≤ K) → Inv log T ⊆ Q ⟨u, leaf u y log⟩)
    {A : QReg} (x : IFreeM (MuPS n) Ω A) (k : Fin n → ℕ)
    (hx : ∀ i, IFreeM.IsChargeBound x (cmdCharge (signChargeAt i)) (k i))
    (log : MuSignLog n Message (Option Signature)) (T : SelMemoS n)
    (hk : ∀ i, (log.user i).length + k i ≤ K) :
    HTQSN m₀ ((memoFromS T (muLogSigns leaf x log)).substitute fun A c ↦
      realizeT θ (challengeTN (SelMemN n) cwUpdN (strPolN n) A c)) (Inv log T) Q := by
  induction x using IFreeM.inductionOn generalizing k log T with
  | pure u y => exact htQSN_pure (leaf u y log) (hleaf u y log T fun i ↦ by have := hk i; omega)
  | liftBind s c next ih =>
    have hc := fun i ↦ (IFreeM.isChargeBound_liftBind_iff _ _ _).1 (hx i)
    rcases c with o | ⟨_ | ⟨j, r⟩, E, ℓ⟩
    · refine HTQSN.bind (x := realizeT θ (challengeTN (SelMemN n) cwUpdN (strPolN n) s
        (QuantumComp.Cmd.prim o))) (Q := fun _ ↦ Inv log T)
        (htQSN_sponge m₀ θ _ (Inv log T)) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b k (fun i ↦ (hc i).2 b) log T hk
    · refine HTQSN.bind (x := realizeT θ (challengeTN (SelMemN n) cwUpdN (strPolN n) s
        (QuantumComp.Cmd.query MuPort.hash E ℓ))) (Q := fun _ ↦ Inv log T)
        (htQSN_sponge m₀ θ _ (Inv log T)) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b k (fun i ↦ (hc i).2 b) log T hk
    · refine HTQSN.bind (x := realizeT θ (challengeTN (SelMemN n) cwUpdN (strPolN n) s
        (QuantumComp.Cmd.query (MuPort.sign j (r, T j)) E ℓ)))
        (Q := fun p ↦ Inv (log ++ [⟨(j, r), p.2.1.down.1⟩]) (T.put j p.2.1.down.2))
        ?_ fun u ans ↦ ?_
      · have hs : HTQ₂SN m₀ (realizeT θ (signAtSN j (r, T j) E ℓ fun B ↦
            signTN (SelMemN n) cwUpdN (strPolN n) j B r (T j)))
            (Inv log T) fun a ↦ Inv (log ++ [⟨(j, r), a.1⟩]) (T.put j a.2) :=
          htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_act _ _) fun _ ↦ hsign _ j r log T
        exact htQSN_realizeT_bind m₀ θ (htQSN_of_htQ₂SN hs) fun _ l ↦ htQSN_pure _ subset_rfl
      · obtain ⟨b, hb⟩ := ans
        subst hb
        refine ih (ULift.up b.down.1) _ (fun i ↦ (hc i).2 _) _ _ fun i ↦ ?_
        have h1 := (hc i).1
        have h2 := hk i
        have hci : cmdCharge (signChargeAt i) s (QuantumComp.Cmd.query (L := LocalSig.instruments)
            (MuPort.sign j r) E ℓ) = if j = i then 1 else 0 :=
          rfl
        rw [hci] at h1 ⊢
        have hlen : ∀ c', (MuSignLog.user (log ++ [⟨(j, r), c'⟩]) i).length ≤
            (MuSignLog.user log i).length + (if j = i then 1 else 0) := fun c' ↦ by
          rw [userS_append]
          split_ifs <;> simp
        refine (Nat.add_le_add_right (hlen _) _).trans ?_
        split_ifs at h1 ⊢ <;> omega

/-- The revealed public keys are the users' template public keys. -/
theorem pksT_restrictTo_pkRevealN (θ : TValsN n) :
    pksT (restrictTo pkRevealN θ) = fun i ↦ (tabOf (userOf θ i)).publicKey := by
  funext i
  have hm := tabRN_restrictTo_congr (T := pkRevealN) (i := i) (U := pkReveal)
    (fun _ hs ↦ Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩) θ
  exact congrArg₂ Sphincs.PublicKey.mk
    (publicSeed_tabOf_congr (hm _ (Finset.mem_insert_self _ _)))
    (root_tabOf_congr (hm _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))

/-- **The challenge prefix**: all users' public keys revealed, then the adversary's memo
transform, each user within the signing budget `K`, moving `Inv log T` along all users'
transcript; it returns the users' template public keys and a transcript of at most `K` requests
per user. -/
theorem htQ₂SN_prefixS (θ : TValsN n) (A : MuAdversaryS n) (K : ℕ)
    (hA : ∀ pks i, IFreeM.IsChargeBound (A pks) (cmdCharge (signChargeAt i)) K)
    (Inv : MuSignLog n Message (Option Signature) → SelMemoS n → Set (RRegSN n (SelMemN n)))
    (hsign : ∀ (B : QReg) (j : Fin n) (msg : Message)
      (log : MuSignLog n Message (Option Signature)) (T : SelMemoS n),
      HTQ₂SN m₀ (realizeT θ (signTN (SelMemN n) cwUpdN (strPolN n) j B msg (T j)))
        (Inv log T) fun a ↦ Inv (log ++ [⟨(j, msg), a.1⟩]) (T.put j a.2))
    (P₀ : Set (RRegSN n (SelMemN n)))
    (hroot : ∀ s ∈ P₀, (s.1, s.2.1, (s.2.2.1 ∪ pkRevealN, s.2.2.2)) ∈ Inv [] fun _ _ ↦ none) :
    HTQ₂SN m₀ (realizeT θ (prefixTN (SelMemN n) cwUpdN (strPolN n) A)) P₀
      (fun pre ↦ {s | (∃ T, s ∈ Inv pre.2.2 T) ∧ (∀ i, (pre.2.2.user i).length ≤ K) ∧
        pre.1 = fun i ↦ (tabOf (userOf θ i)).publicKey}) := by
  unfold prefixTN
  refine htQ₂SN_revealThen m₀ θ _ _ P₀ _ fun mem ↦ ?_
  refine htQ₂SN_realizeT_bind m₀ θ (Q := fun run : MuRunS n ↦
    {s | (∃ T, s ∈ Inv run.2 T) ∧ ∀ i, (run.2.user i).length ≤ K}) ?_
    fun run ↦ htQ₂SN_pure _ fun s hs ↦ ⟨hs.1, hs.2, pksT_restrictTo_pkRevealN θ⟩
  refine htQ₂SN_of_htQSN (HTQSN.mono (P := Inv [] fun _ _ ↦ none) ?_ ?_ fun _ ↦ subset_rfl)
  · have e := realizeT_substitute (good := goodQN) (M := SelMemN n) θ
      (challengeTN (SelMemN n) cwUpdN (strPolN n))
      (memoFromS (fun _ _ ↦ none) (withMuSignLog (A (pksT (restrictTo pkRevealN θ)))))
    refine (congrArg (fun y ↦ HTQSN m₀ y (Inv [] fun _ _ ↦ none)
      fun p ↦ {s | (∃ T, s ∈ Inv p.2.2.2 T) ∧ ∀ i, (p.2.2.2.user i).length ≤ K}) e).mpr ?_
    exact htQ_logSignsSN θ K Inv hsign _
      (fun q : (Σ u, QuantumComp₂.Leaf (QReg.of Unit)
        ((Fin n × Forgery) × MuSignLog n Message (Option Signature)) u) ↦
          {s | (∃ T, s ∈ Inv q.2.2.2 T) ∧ ∀ i, (q.2.2.2.user i).length ≤ K})
      (fun _ _ _ T hl _ hs ↦ ⟨⟨T, hs⟩, hl⟩) _ (fun _ ↦ K) (hA _) [] _ fun i ↦ by simp
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hroot s₀ hs₀

/-- **The initial operator in the decompressed basis**: no empty cell, no hardwired cell, memory
`m₀`. -/
theorem init_decQSN (m₀ : Finset (TPosN n) × SelMemN n) :
    QuerySupportedOn (fun p : Unit × RRegSN n (SelMemN n) ↦ p.2)
      {s | NoBot s ∧ s.2 = (hwEmpty PairOut HashDomain, m₀)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut HashDomain (Finset (TPosN n) × SelMemN n)) (initU m₀)) := by
  have h0 : QuerySupportedOn (fun p : Unit × RRegSN n (SelMemN n) ↦ p.2)
      {s | s.2 = (hwEmpty PairOut HashDomain, m₀)} (initU m₀) := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty PairOut HashDomain, m₀) : RRegSN n (SelMemN n))).matrix) m m' ≠ 0
      at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨congrArg Prod.snd he.1.symm, congrArg Prod.snd he.2.symm⟩
    · exact absurd rfl h
  exact querySupportedOn_inter (noBot_init m₀ (A := Unit) (SubState.basis ()).matrix)
    (querySupportedOn_conj_compressReg (P := fun b ↦ b = (hwEmpty PairOut HashDomain, m₀)) h0)

/-- **The invariant after the public keys' reveal**, from no empty cell, no hardwired cell, an
empty label and no selection. -/
theorem invQSN_init (θ : TValsN n) (hm₀ : m₀ = m0SN) {s : RRegSN n (SelMemN n)}
    (hs : NoBot s ∧ s.2 = (hwEmpty PairOut HashDomain, m₀)) :
    (s.1, s.2.1, (s.2.2.1 ∪ pkRevealN, s.2.2.2)) ∈ InvQSN θ [] fun _ _ ↦ none := by
  obtain ⟨hnb, hs2⟩ := hs
  subst hm₀
  have hW : s.2.1 = hwEmpty PairOut HashDomain := congrArg Prod.fst hs2
  have hL : s.2.2.1 = ∅ := congrArg (·.2.1) hs2
  have hM : s.2.2.2 = fun _ _ ↦ none := congrArg (·.2.2) hs2
  refine ⟨noBot_of_fst_eqSN rfl hnb, fun i ↦ ?_, fun W _ ↦ ⟨fun _ q hq ↦ ?_, fun _ q hq ↦ ?_,
    fun i K c hc ↦ ?_, fun i K o ho ↦ ?_, fun z ω hz ↦ ?_⟩⟩
  · rw [SufCma.Multi.MuSignLog.user_nil]
    refine strOk_nil fun t ht ↦ ?_
    change t ∈ labU (s.2.2.1 ∪ pkRevealN) i at ht
    rw [hL, Finset.empty_union, mem_labU] at ht
    exact valOnly_pkReveal t (Finset.mem_product.1 ht).2
  · rw [SufCma.Multi.MuSignLog.user_nil] at hq
    exact absurd hq List.not_mem_nil
  · rw [SufCma.Multi.MuSignLog.user_nil] at hq
    exact absurd hq List.not_mem_nil
  · change s.2.2.2 i K = some c at hc
    rw [hM] at hc
    cases hc
  · cases ho
  · change s.2.1.1 z = some ω at hz
    rw [hW] at hz
    exact absurd hz (by simp [hwEmpty, Database.empty])

end prefixRun

/-! ## The facts of the prefix -/

theorem not_isExpandPos_digPos (m : Message) : ¬IsExpandPos (digPos m) := by
  rintro (h | h) <;> cases h

section facts

variable {S0 : Fin n → MasterSeed} {W : Fin n → QTable} {H : HashDomain → HashOutput}
  {log : MuSignLog n Message (Option Signature)} {s : RRegSN n (SelMemN n)}
  (hP : Function.Injective fun i ↦ (W i).publicSeed)
  (hhw : ∀ z ω, s.2.1.1 z = some ω → ∃ i,
    (∃ q ∈ log.user i, z = cellOf (S0 i) (digPos q.1) (W i) ∧ ω = W i (digPos q.1)) ∨
      ∃ q ∈ log.user i, ∃ p, PubBy (W i) H q.1 p ∧ z = cellOf (S0 i) p (W i))
include hP hhw

omit hhw in
/-- Two users' cells of a non-expansion position agree only for the same user. -/
theorem user_eq_of_cellOf_eq {i i' : Fin n} {p p' : Pos} (hp : ¬IsExpandPos p)
    (hp' : ¬IsExpandPos p') (h : cellOf (S0 i) p (W i) = cellOf (S0 i') p' (W i')) : i' = i := by
  have h1 := prefixS_cellOf (S0 i) (W i) hp
  rw [h, prefixS_cellOf (S0 i') (W i') hp'] at h1
  exact hP (Option.some.inj h1)

-- The linter's `whnf` of the disclosure memberships runs the counter search.
set_option linter.constructorNameAsVariable false in
/-- **Every hardwired chain step and FORS leaf of user `i` has a known input**, under distinct
`PK.seed`s. -/
theorem hwKnown_ofSN (i : Fin n) :
    HwKnown (S0 i) (W i) H (projU i (s.1, s.2.1, s.2.2.2)) ((log.user i).map Sigma.fst) := by
  have hD : ∀ q ∈ log.user i,
      (W i).disclosedBy H q.1 ⊆ (W i).disclosures H ((log.user i).map Sigma.fst) := fun q hq ↦ by
    unfold QTable.disclosures
    exact Set.subset_union_of_subset_right (Set.subset_iUnion₂
      (s := fun m (_ : m ∈ (log.user i).map Sigma.fst) ↦ (W i).disclosedBy H m) q.1
      (List.mem_map_of_mem hq)) _
  refine ⟨fun l τ e c step hp hz ↦ ?_, fun idx κ t hz ↦ ?_⟩
  · obtain ⟨ω, hω⟩ := Option.isSome_iff_exists.1 hz
    have hne : ¬IsExpandPos ⟨RawPos.chain l τ e c step, hp⟩ := by
      rintro (h | h) <;> cases h
    obtain ⟨i', hi'⟩ := hhw _ ω hω
    rcases hi' with ⟨q, -, e1, -⟩ | ⟨q, hq, p, hpb, e1⟩
    · have h := congrArg Subtype.val (pos_eq_of_cellOf_eq e1)
      cases h
    · obtain rfl := pos_eq_of_cellOf_eq e1
      obtain rfl := user_eq_of_cellOf_eq hP hne hne e1
      obtain ⟨sel₀, sel₁, sel₂, h0, h1, h2, hc⟩ := hpb
      have hd := hD q hq
      rw [disclosedBy_of_select h0 h1 h2] at hd
      rcases hc with hc | hc | hc | hc
      · rcases mem_forsPos_cases hc with ⟨_, h⟩ | ⟨_, _, _, h, -⟩ | h <;> cases h
      · exact known_of_layerPos (fun _ hx ↦ hd (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_right _ hx)))) hp hc
      · exact known_of_layerPos (fun _ hx ↦ hd (Set.mem_union_left _ (Set.mem_union_right _ hx)))
          hp hc
      · exact known_of_layerPos (fun _ hx ↦ hd (Set.mem_union_right _ hx)) hp hc
  · obtain ⟨ω, hω⟩ := Option.isSome_iff_exists.1 hz
    have hne : ¬IsExpandPos ⟨RawPos.forsLeaf idx κ t, trivial⟩ := by
      rintro (h | h) <;> cases h
    obtain ⟨i', hi'⟩ := hhw _ ω hω
    rcases hi' with ⟨q, -, e1, -⟩ | ⟨q, hq, p, hpb, e1⟩
    · have h := congrArg Subtype.val (pos_eq_of_cellOf_eq e1)
      cases h
    · obtain rfl := pos_eq_of_cellOf_eq e1
      obtain rfl := user_eq_of_cellOf_eq hP hne hne e1
      obtain ⟨sel₀, sel₁, sel₂, h0, h1, h2, hc⟩ := hpb
      have hd := hD q hq
      rw [disclosedBy_of_select h0 h1 h2] at hd
      rcases hc with hc | hc | hc | hc
      · rcases mem_forsPos_cases hc with ⟨_, h⟩ | ⟨_, _, _, h, -⟩ | h
        · obtain ⟨rfl, rfl, rfl⟩ := RawPos.forsLeaf.inj h
          exact Known.disclosed _ (hd (Set.mem_union_left _ (Set.mem_union_left _
            (Set.mem_union_left _ ⟨_, Or.inl rfl⟩))))
        · cases h
        · cases h
      all_goals
        rcases mem_layerPos_cases hc with ⟨_, _, -, h⟩ | h | ⟨_, _, h, -⟩ <;> cases h

/-- **The hardwired call-0 `H_msg` cells with user `i`'s `PK.seed` are user `i`'s signed
digests**, under distinct `PK.seed`s. -/
theorem hwDigestsP_ofSN (i : Fin n) :
    HwDigestsP (S0 i) (W i) (projU i (s.1, s.2.1, s.2.2.2)) ((log.user i).map Sigma.fst) := by
  intro x ω hx hpre hz
  obtain ⟨i', hi'⟩ := hhw x ω hz
  rcases hi' with ⟨q, hq, rfl, e2⟩ | ⟨q, hq, p, hp, rfl⟩
  · rw [prefixS_cellOf (S0 i') (W i') (not_isExpandPos_digPos q.1)] at hpre
    obtain rfl := hP (Option.some.inj hpre)
    exact ⟨q.1, List.mem_map_of_mem hq, rfl, e2⟩
  · refine absurd hx (hmsgCall_cellOf_ne_zero (S0 i') (W i') fun m hm ↦ ?_)
    have h := isStruct_of_pubBy hp
    rw [hm] at h
    exact h

end facts

/-- **The facts of a prefix outcome `pre`** on a register `s`, per user `i` (`win_imp_badQN`'s
hypotheses on the projected register `(s.1, s.2.1, s.2.2.2)`, against user `i`'s run's table
`runTab (userOf θ i) (labU s.2.2.1 i)`, the hash `hHSN s` of the register's view, and the
stream's disclosures `starCover (streamOf (userOf θ i))`): the public keys are the template's, no
empty cell, user `i`'s transcript's signatures are the table's, user `i`'s memory records every
request's selections, under distinct `PK.seed`s every hardwired chain step and FORS leaf of `i` has
a known input and every hardwired call-0 `H_msg` cell with `i`'s `PK.seed` is `i`'s signed digest,
and every signed view of `i` is covered. -/
def PreFactsQSN (θ : TValsN n) (pre : (Fin n → PublicKey) × MuRunS n)
    (s : RRegSN n (SelMemN n)) : Prop :=
  (∀ i, pre.1 i = (tabOf (userOf θ i)).publicKey) ∧ NoBot s ∧ ∀ i,
    (∀ q ∈ pre.2.2.user i, q.2 = (runTab (userOf θ i) (labU s.2.2.1 i)).signature (hHSN s) q.1) ∧
    (∀ q ∈ pre.2.2.user i,
      Records (runTab (userOf θ i) (labU s.2.2.1 i)) (hHSN s) (s.2.2.2 i) q.1) ∧
    (PDistinct (tabOfN θ) →
      HwKnown (seedsOf θ i) (runTab (userOf θ i) (labU s.2.2.1 i)) (hHSN s)
        (projU i (s.1, s.2.1, s.2.2.2)) ((pre.2.2.user i).map Sigma.fst) ∧
      HwDigestsP (seedsOf θ i) (runTab (userOf θ i) (labU s.2.2.1 i))
        (projU i (s.1, s.2.1, s.2.2.2)) ((pre.2.2.user i).map Sigma.fst)) ∧
    ∀ q ∈ pre.2.2.user i, Covered (starCover (streamOf (userOf θ i)))
      (pairView (runTab (userOf θ i) (labU s.2.2.1 i) (digPos q.1)))

/-- **The facts from the invariant**, each user within the signing budget. -/
theorem preFactsQSN_of {θ : TValsN n} {pre : (Fin n → PublicKey) × MuRunS n}
    {s : RRegSN n (SelMemN n)} {T : SelMemoS n} (hs : s ∈ InvQSN θ pre.2.2 T)
    (hlen : ∀ i, (pre.2.2.user i).length ≤ signatureLimit)
    (hpk : pre.1 = fun i ↦ (tabOf (userOf θ i)).publicKey) : PreFactsQSN θ pre s := by
  obtain ⟨hnb, hok, hF⟩ := hs
  obtain ⟨hlog, hrec, -, -, hhw⟩ := hF (fun i ↦ runTab (userOf θ i) (labU s.2.2.1 i))
    fun i ↦ compatS_runTab _ _
  refine ⟨fun i ↦ congrFun hpk i, hnb, fun i ↦ ⟨hlog i, hrec i, fun hP ↦ ?_, fun q hq ↦ ?_⟩⟩
  · have hP' : Function.Injective fun i ↦ (runTab (userOf θ i) (labU s.2.2.1 i)).publicSeed :=
      fun a b hab ↦ hP ((runTab_offDig (userOf θ a) (labU s.2.2.1 a)).publicSeed.symm.trans
        (hab.trans (runTab_offDig (userOf θ b) (labU s.2.2.1 b)).publicSeed))
    exact ⟨hwKnown_ofSN hP' hhw i, hwDigestsP_ofSN hP' hhw i⟩
  · rcases (hok i).2.2.2 q hq with ⟨j, hj⟩ | ⟨-, hlt⟩
    · rw [runTab_digPos, markC_of_asg (hok i).1 hj]
      exact covered_starCover (streamOf (userOf θ i)) j
    · have := hlen i
      omega

/-- **The classification facts of the canonical prefix**: on every branch `pre` of the challenge
prefix `prefixQSN (strPolN n) A θ`, run against `runtimeR m₀` from an empty label and no
selection by an adversary making at most `signatureLimit` signing requests to each user, in the
decompressed basis, the register is supported where `PreFactsQSN θ pre` holds. -/
theorem prefixFactsQSN (A : MuAdversaryS n)
    (hsignAt : ∀ pks i, IFreeM.IsChargeBound (A pks) (cmdCharge (signChargeAt i)) signatureLimit)
    (m₀ : Finset (TPosN n) × SelMemN n) (hm₀ : m₀ = m0SN) (θ : TValsN n)
    (pre : (Fin n → PublicKey) × MuRunS n) :
    QuerySupportedOn (fun p : Unit × RRegSN n (SelMemN n) ↦ p.2) {s | PreFactsQSN θ pre s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut HashDomain (Finset (TPosN n) × SelMemN n))
        (((runtimeR m₀).run₂ .instruments (prefixQSN (strPolN n) A θ)).branch pre
          (initU m₀))) := by
  rw [Quantum.Xmss.Assembly.conj_branch₂ m₀ (prefixQSN (strPolN n) A θ) pre (initU m₀)]
  have H := htQ₂SN_prefixS (m₀ := m₀) θ A signatureLimit hsignAt (InvQSN θ)
    (fun B j msg log T ↦ htQ₂SN_signInv θ B j msg log T)
    {s | NoBot s ∧ s.2 = (hwEmpty PairOut HashDomain, m₀)} fun _ hs ↦ invQSN_init θ hm₀ hs
  refine (H _ (init_decQSN m₀) pre).mono ?_
  rintro s ⟨⟨T, hinv⟩, hlen, hpk⟩
  exact preFactsQSN_of hinv hlen hpk

end Quantum.Qrom.Sphincs.Multi

end
