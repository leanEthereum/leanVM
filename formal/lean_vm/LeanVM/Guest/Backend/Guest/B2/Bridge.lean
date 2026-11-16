/-
  LeanVM.Guest.Backend.Guest.B2.Bridge

  `B2SoundL` from the back end's correctness, through the certificates' data and no certificate
  check.
-/

module

public import LeanVM.Guest.EndLoc
public import LeanVM.Guest.CertName
public import LeanVM.Guest.Backend.Guest.End
public import LeanVM.Guest.Backend.Guest.B2.Agree
public import LeanVM.Guest.Backend.Guest.B2.DataAll
public import LeanVM.Guest.Backend.Guest.Facts
public import LeanVM.Guest.Backend.Guest.Places
public import LeanVM.Guest.Backend.Guest.B2.Pow
public import LeanVM.Guest.Backend.Guest.B2.Eval.Res

/-!
# B2 from the back end

`B2SoundL` (`Guest/EndLoc.lean`) states B2 as checker K's contracts over `glob`: each function's
`Check.Pre` gives, on a halting run from its entry, its return and `Check.Post` (its body under its
certificate's cells, calls located by `Check.EnteredAt`, its promised bounds), and `main`'s body
holds at frame `1` under its certificate's cells. `b2SoundL_backend` proves it from the back end's
contracts (`contracts`, `guest_main_body`) on the guest's world `guestEnd`, reading only the
certificates' data (`sigOf`, `certOf j`'s cells, `post`, `env`, `nret`; the test `dataOk`), with
one hypothesis beside `GuestCompiles`:

* `LocsAgree`: function `j`'s places (the back end's placement of the guest, `gLocs`) compare with
  its certificate's cells (`Agree.fnOk`, decidable, one test per function).

The residual values `fnOk` admits hold at every frame where the run from the function's entry
halts (`residualFacts`, `B2/Prologue.lean`), and every frame the contracts quantify over is one.

The steps: a frame the back end's located relation enters is one `Check.EnteredAt` enters, and
there the callee's parameters and body carry over from places to cells (`entered_cert`), so the
back end's located relation is below `RLg` (`C_le`); `Check.Pre` gives the back end's `World.Pre`
(`pre_of_cert`); the back end's `World.Post` gives `Check.Post` (`post_cert`).
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend.Obl

@[expose] public section

/-! ## The hypothesis on places -/

/-- **Every function's places compare with its certificate's cells** (`Agree.fnOk`), one test per
function on its placed locations. -/
def LocsAgree : Prop :=
  ∀ j, 1 ≤ j → j < nFns → (agreeWith (gLocs (coreOf j).name) j).fnOk (coreOf j) = true

/-- `LocsAgree` from `locsOkAt` of each entry of the back end's input on its placed locations. -/
theorem locsAgree_of (h : ∀ i < coreProgram.length, locsOkAt i (gLocs (coreOf (i + 1)).name) = true) :
    LocsAgree := by
  intro j h1 h2
  have := h (j - 1) (by have := coreProgram_length_succ; omega)
  rw [locsOkAt_eq, Nat.sub_add_cancel h1] at this
  exact this

/-! ## Places to cells -/

variable {κ : ℕ} {L : MemoryImage κ}

theorem valC_eq {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) (locs : VMap Loc) (fp : K) :
    (agreeWith locs j).valC L fp = Check.frameVal L certByName (coreOf j).name fp := by
  funext v
  simp only [Agree.valC, Agree.cell, agreeWith, Check.frameVal, Check.valG, certByName_coreOf h1 h2]
  rfl

/-- **Function `j`'s parameters and body carry over from places to cells** at a frame where the
run from its entry halts. -/
theorem transport (hagree : LocsAgree) {j k : ℕ} {fp : K} (h1 : 1 ≤ j)
    (h2 : j < nFns) (hs : Safe guestProgram L k ⟨addressOfIndex (fnOf j).entryPc, fp⟩) :
    (coreOf j).params.map (valP L fp (gLocs (coreOf j).name)) =
        (coreOf j).params.map (Check.frameVal L certByName (coreOf j).name fp) ∧
      ∀ (C : CallRel) (rd : Reader) (N : Prop) (kret : List E → Prop),
        Stmt.HoldsList C rd (valP L fp (gLocs (coreOf j).name)) (coreOf j).body N kret →
          Stmt.HoldsList C rd (Check.frameVal L certByName (coreOf j).name fp) (coreOf j).body N kret := by
  have := Agree.fnOk_sound (A := agreeWith (gLocs (coreOf j).name) j) (L := L) (fp := fp)
    (locs := gLocs (coreOf j).name) (fun _ => rfl) (residualFacts L j k fp h1 h2 hs) (hagree j h1 h2)
  rwa [valC_eq h1 h2] at this

/-! ## The executor's tries -/

/-- A read of the key just stored, within the trie's depth. -/
theorem trie_get_set {α : Type} (a : α) : ∀ (d : ℕ) (t : Exec.Trie α) (n : ℕ), n + 1 < 2 ^ d →
    (t.set a d n).get n = some a
  | 0, _, n, h => absurd h (by simp)
  | d + 1, t, n, h => by
      rw [Exec.Trie.set_succ, pow_succ] at *
      by_cases h0 : n = 0
      · rw [ite_eq_left h0, Exec.Trie.get_node, ite_eq_left h0]
      · rw [ite_eq_right h0]
        by_cases h1 : n % 2 = 1
        · rw [ite_eq_left h1, Exec.Trie.get_node, ite_eq_right h0, ite_eq_left h1]
          exact trie_get_set a d _ _ (by omega)
        · rw [ite_eq_right h1, Exec.Trie.get_node, ite_eq_right h0, ite_eq_right h1]
          exact trie_get_set a d _ _ (by omega)

/-! ## Entry environments -/

theorem envOk_cases {env : List (ℕ × Exec.Sym)} {reg : Bool} {na : ℕ} (h : envOk env reg na = true) :
    (env = [] ∧ reg = false) ∨ (env = [(2 + na, .fpg 0)] ∧ reg = true) := by
  unfold envOk at h
  split at h
  · simp_all
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  · exact absurd h (by simp)

theorem fp_mul_one (fp : K) : fp * addressOfIndex 0 = fp := by
  rw [addressOfIndex, pow_zero, mul_one]

theorem ofK_ne_zero_of_inMem {fp : K} (h : InMem κ fp) : ofK fp ≠ 0 := by
  obtain ⟨a, -, rfl⟩ := h
  exact ofK_gpow_ne_zero a

/-- The self pointer gives the certificate's entry environment. -/
theorem envHolds_of {env : List (ℕ × Exec.Sym)} {reg : Bool} {na : ℕ} {fp : K}
    (h : envOk env reg na = true) (hin : InMem κ fp)
    (hself : reg = true → Backend.wd L fp (2 + na) = ofK fp) : Exec.EnvHolds L fp (Exec.envOf env) := by
  rcases envOk_cases h with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
  · exact Exec.EnvHolds.nil
  · show Exec.EnvHolds L fp (Exec.Trie.nil.set (Exec.Sym.fpg 0) Exec.envDepth (2 + na))
    refine Exec.EnvHolds.set Exec.EnvHolds.nil ?_
    rw [show (Exec.Sym.fpg 0).val fp = ofK fp by rw [Exec.Sym.val, fp_mul_one]]
    exact read_of_wd (hself rfl) (ofK_ne_zero_of_inMem hin)

/-- The certificate's entry environment gives the self pointer. -/
theorem self_of_env {env : List (ℕ × Exec.Sym)} {reg : Bool} {na : ℕ} {fp : K}
    (h : envOk env reg na = true) (hna : na < 2 ^ 12) (hE : Exec.EnvHolds L fp (Exec.envOf env)) :
    reg = true → Backend.wd L fp (2 + na) = ofK fp := by
  rcases envOk_cases h with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · intro h; cases h
  · intro _
    have hd : 2 + na + 1 < 2 ^ Exec.envDepth := by
      have : na < 4096 := hna
      rw [show (2 : ℕ) ^ Exec.envDepth = 16384 from rfl]
      omega
    have hg : (Exec.Trie.nil.set (Exec.Sym.fpg 0) Exec.envDepth (2 + na)).get (2 + na) =
        some (.fpg 0) := trie_get_set _ _ _ _ hd
    have hE' : Exec.EnvHolds L fp (Exec.Trie.nil.set (Exec.Sym.fpg 0) Exec.envDepth (2 + na)) := hE
    have := hE' _ _ hg
    rw [Exec.Sym.val, fp_mul_one] at this
    exact wd_of_read this

/-! ## The world -/

variable {fns : List Lowered} {slots : Array KVal}

/-- The guest's world on `L`. -/
local notation "WG" => guestEnd fns slots L

theorem sig_nargs (j : ℕ) : (glob.sig j).nargs = (coreOf j).params.length := rfl

/-- A halting run from `(g^0, 1)` writes the jump table the certificates read. -/
theorem jtHolds_glob {k : ℕ} (hs : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) : Check.JTHolds glob L :=
  JumpTable.jt_of_jumpTables (End.safe_jumpTables hs).1 powTree_ok

/-- **A frame the back end's located relation enters**, on a run from `(g^0, 1)` that halts, is one
`Check.EnteredAt` enters, and there the callee's parameters and body carry over from places to
cells. -/
theorem entered_cert (h : GuestCompiles fns slots) (hagree : LocsAgree)
    {k0 : ℕ} (hs0 : Safe guestProgram L k0 ⟨addressOfIndex 0, 1⟩) {f : String} {fp : K}
    {a r : List E} (hE : (WG).Entered f fp a r) :
    ∃ j, 2 ≤ j ∧ j < nFns ∧ (coreOf j).name = f ∧ Check.EnteredAt glob L f fp a r ∧
      (coreOf j).params.map ((WG).vf f fp) = (coreOf j).params.map (Check.frameVal L certByName f fp) ∧
      ∀ (C : CallRel) (N : Prop) (kret : List E → Prop),
        Stmt.HoldsList C L.read ((WG).vf f fp) (coreOf j).body N kret →
          Stmt.HoldsList C L.read (Check.frameVal L certByName f fp) (coreOf j).body N kret := by
  obtain ⟨hin, hpre, hreach, tf, htf, hname, rfl, rfl⟩ := hE
  obtain ⟨j, h1, h2, rfl⟩ := mem_guestTraced htf
  subst hname
  obtain ⟨hne, -, tf', htf', hn', hreg, hU⟩ := hpre
  obtain rfl := tf_eq L h htf' h1 h2 hn'
  have hj2 : 2 ≤ j := by
    by_contra hc
    obtain rfl : j = 1 := by omega
    exact hne core0_main.1
  obtain ⟨hsig, hnret, henv, -, -, -⟩ := dataOk_spec (dataOk_all h1 h2)
  have hent := ent_eq (L := L) (U := guestU L.read) h h1 h2
  rw [guestProgram_eq h, hent] at hreach
  obtain ⟨k, hk⟩ := safe_of_reach hs0 hreach
  obtain ⟨hpar, hbody⟩ := transport (L := L) hagree h1 h2 hk
  rw [vf_eq]
  refine ⟨j, hj2, h2, rfl, ⟨hin, j, rfl, ?_, hreach, rfl, ?_⟩, hpar, fun C N kret => hbody C L.read N kret⟩
  · obtain ⟨hb, hm, hsm⟩ := cert_of_u (G := glob) rfl hsig hU
    refine ⟨by simp [glob, good]; omega, jtHolds_glob hs0, envHolds_of henv hin ?_, hb, hm, hsm⟩
    intro hr
    exact hreg ((registered_tfOf h h1 h2).mpr hr)
  · show Backend.frameWords L fp (2 + (coreOf j).params.length) (certOf j).nret = _
    rw [show (certOf j).nret = (infoOf j).2.1 from hnret]
    rfl

/-- **The back end's located relation is below the certificates'** on a memory where a run from
`(g^0, 1)` halts. -/
theorem C_le (h : GuestCompiles fns slots) (hagree : LocsAgree) {k0 : ℕ}
    (hs0 : Safe guestProgram L k0 ⟨addressOfIndex 0, 1⟩) : CallRel.Le (WG).C (Located.RLg L) := by
  have hc : (WG).C = coreProgram.RelL L.read (WG).vf (WG).Entered := by
    show (guestWorld fns slots L (guestU L.read)).core.RelL _ _ _ = _
    rw [guestWorld_core]
    rfl
  rw [hc]
  refine relL_le_of fun f fp a r fn hf hA => ?_
  obtain ⟨j, hj2, h2, rfl, hEA, hpar, hbody⟩ := entered_cert h hagree hs0 hA
  obtain rfl : fn = coreOf j := Option.some.inj (hf.symm.trans (coreOf_find (by omega) h2))
  exact ⟨hEA, hpar, hbody⟩

/-! ## Pre and post -/

/-- **`Check.Pre` gives the back end's precondition**, on a run from `(g^0, 1)` that halts. -/
theorem pre_of_cert (h : GuestCompiles fns slots) {k0 : ℕ}
    (hs0 : Safe guestProgram L k0 ⟨addressOfIndex 0, 1⟩) {i : ℕ} {fp : K}
    (hpre : Check.Pre glob L i fp) :
    2 ≤ i ∧ i < nFns ∧ (WG).Pre (coreOf i).name fp := by
  obtain ⟨hgood, -, henvh, hb, hm, hsm⟩ := hpre
  have hi : 2 ≤ i ∧ i < nFns := by simpa [glob, good] using hgood
  obtain ⟨hsig, -, henv, -, -, -⟩ := dataOk_spec (dataOk_all (by omega) hi.2)
  refine ⟨hi.1, hi.2, name_ne_main hi.1 hi.2, ?_, tfOf i, getElem_mem_guestTraced (by omega) hi.2,
    rfl, fun hr => ?_, u_of_cert (G := glob) rfl hsig hb hm hsm⟩
  · have hW := guestWorld_compiled (L := L) (U := guestU L.read) h
    obtain ⟨-, -, hjt, -⟩ := jt_of_run hW (k := k0)
      ⟨by rw [guestProgram_eq h]; exact hs0, Reach.refl _⟩
    exact hjt
  · exact self_of_env henv (fn_names (by omega) hi.2).2 henvh ((registered_tfOf h (by omega) hi.2).mp hr)

theorem frameWords_length_any {fp : K} (o n : ℕ) : (Backend.frameWords L fp o n).length = n := by
  simp [Backend.frameWords]

theorem frameWords_append_getD {fp : K} {na nr i : ℕ} (hi : i < na + nr) :
    (Backend.frameWords L fp 2 na ++ Backend.frameWords L fp (2 + na) nr).getD i 0 =
      Backend.wd L fp (i + 2) := by
  rcases Nat.lt_or_ge i na with h | h
  · rw [List.getD_append _ _ _ _ (by rw [frameWords_length]; exact h), frameWords_getD h]
  · rw [List.getD_append_right _ _ _ _ (by rw [frameWords_length]; exact h), frameWords_length,
      Backend.frameWords, List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1
    omega

/-- The bounds the analysis proves at a return give the certificate's promised bounds. -/
theorem bnd_post {j na nr : ℕ} {fp : K} (hok : postOk (csig j) (guestTab.sig (coreOf j).name) = true)
    (hna : (csig j).nargs = na) (hnr : (csig j).nret = nr)
    (hS : SigPost (guestTab.sig (coreOf j).name)
      (Backend.frameWords L fp 2 na ++ Backend.frameWords L fp (2 + na) nr)) :
    Check.BndHolds L fp (csig j).post := by
  intro p hp
  have := List.all_eq_true.mp hok p hp
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨q, hq, ⟨h1, h2⟩, h3⟩ := this
  rw [hna, hnr] at h3
  have hb := hS q hq (by rw [List.length_append, frameWords_length_any, frameWords_length_any]; omega)
  rw [frameWords_append_getD h3, h1] at hb
  obtain ⟨e, he, hr⟩ := read_of_bnd hb
  exact ⟨e, lt_of_lt_of_le he h2, hr⟩

/-- **The located relation meets the table's postconditions** in the guest's world. -/
theorem sigPost_of (h : GuestCompiles fns slots) (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) {f : String}
    {a r : List E} (hC : (WG).C f a r) : SigPost (guestTab.sig f) (a ++ r) := by
  have hW := guestWorld_compiled (L := L) (U := guestU L.read) h
  have hW' : (WG).core = coreProgram := guestWorld_core
  have hlen : coreProgram.length = 1549 := core_length
  have hxp : ∀ f a r, (WG).core.Rel L.read f a r →
      XPost guestRel L.read (guestTab.sig f) (a ++ r) := by
    intro f a r h p hp _
    by_cases hx : (guestTab.sig f).xpost = []
    · rw [hx] at hp
      exact absurd hp List.not_mem_nil
    obtain ⟨rfl, he⟩ := sig_xpost hx
    rw [he, List.mem_singleton] at hp
    subst hp
    rw [hW'] at h
    exact ⟨fun _ => expPost_B1 _ a r h, fun h1 => absurd h1 (by decide),
      fun h1 => absurd h1 (by decide), fun h1 => absurd h1 (by decide)⟩
  have hP : ∀ fn ∈ (WG).core, (guestTab.sig fn.name).post ≠ [] → chkFn guestTab fn = true := by
    intro fn hfn hpost
    rw [hW'] at hfn
    obtain ⟨j, hj, rfl⟩ := getD_of_mem hfn
    cases hs : guestSkip j with
    | true => exact absurd (sig_post hpost) (skip_post hs)
    | false => exact guest_chk (hlen ▸ hj) hs
  exact (World.post_of_chk hW guestTab_pows (hκ.2.trans maxLogMem_le) rfl hP hxp f a r hC).1

/-- **The back end's postcondition gives `Check.Post`**, on a run from `(g^0, 1)` that halts. -/
theorem post_cert (h : GuestCompiles fns slots) (hagree : LocsAgree)
    (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) {k0 : ℕ} (hs0 : Safe guestProgram L k0 ⟨addressOfIndex 0, 1⟩)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i < nFns) {fp : K} (hpost : (WG).Post (coreOf i).name fp) :
    Check.Post coreProgram glob L certByName (Check.EnteredAt glob L) i fp := by
  obtain ⟨tf, htf, hn, ⟨hpar, hbody⟩, hE⟩ := hpost
  obtain rfl := tf_eq L h htf h1 h2 hn
  obtain ⟨j, hj2, hj, hjn, hEA, hpar', hbody'⟩ := entered_cert h hagree hs0 hE
  obtain rfl := coreOf_name_inj (by omega) hj h1 h2 hjn
  obtain ⟨-, hnret, -, hpo, -, -⟩ := dataOk_spec (dataOk_all h1 h2)
  have hr : (glob.sig j).nret = (infoOf j).2.1 := hnret
  have hC : (WG).C (coreOf j).name (Backend.frameWords L fp 2 (coreOf j).params.length)
      (Backend.frameWords L fp (2 + (coreOf j).params.length) (infoOf j).2.1) := by
    refine (relL_iff _ _ _ _).mpr ⟨coreOf j, fp, ?_, hE, hpar, hbody⟩
    rw [guestWorld_core]
    exact coreOf_find h1 h2
  refine ⟨⟨coreOf j, coreOf_find h1 h2, hpar'.symm.trans hpar, ?_⟩, ?_, ?_⟩
  · show Stmt.HoldsList _ L.read _ (coreOf j).body False
      (fun rs => rs = Backend.frameWords L fp (2 + (coreOf j).params.length) (glob.sig j).nret)
    rw [hr]
    exact holdsList_mono (C_le h hagree hs0) _ id (fun _ h => h) (hbody' _ _ _ hbody)
  · show Check.EnteredAt glob L (coreOf j).name fp (Backend.frameWords L fp 2 (coreOf j).params.length)
      (Backend.frameWords L fp (2 + (coreOf j).params.length) (glob.sig j).nret)
    rw [hr]
    exact hEA
  · exact bnd_post hpo rfl hr (sigPost_of h hκ hC)

/-! ## The end theorem -/

/-- **B2 from the back end**: given that the back end compiles the guest to the statement's
bytecode and that every function's places compare with its certificate's cells, `B2SoundL`
holds, with no certificate check. -/
theorem b2SoundL_backend (h : GuestCompiles fns slots) (hagree : LocsAgree) :
    End.B2SoundL where
  step := by
    intro κ L h16 h32 n _ i fp k _ hpre hsafe
    obtain ⟨k0, hs0⟩ := safe_of_reach_back hsafe.2 hsafe.1
    obtain ⟨hi2, hin, hWpre⟩ := pre_of_cert (L := L) h hs0 hpre
    have hW := guestWorld_compiled (L := L) (U := guestU L.read) h
    have hobl := guest_obligations hW guestTraced_core ⟨h16, h32⟩ rfl
    have hc := contracts hW (lt_of_le_of_lt h32 maxLogMem_lt) hobl (coreOf i).name
    rw [guestProgram_eq h, ent_eq h (by omega) hin] at hc
    obtain ⟨k', hk', r, hr, hpost, hs'⟩ := hc fp k hWpre hsafe
    exact ⟨k', hk', r, hr, post_cert h hagree ⟨h16, h32⟩ hs0 (by omega) hin hpost, hs'⟩
  mainL := by
    intro κ L h16 h32 _ k _ hsafe
    obtain ⟨k0, hs0⟩ := safe_of_reach_back hsafe.2 hsafe.1
    have hm := guest_main_body h κ L h16 h32 k0 hs0
    rw [vf_eq, ← core0_main.1, ← coreOf_one] at hm
    have hT := Agree.fnOk_sound (A := agreeWith (gLocs (coreOf 1).name) 1) (L := L) (fp := 1)
      (locs := gLocs (coreOf 1).name) (fun _ => rfl) (residualFacts L 1 k 1 le_rfl (by decide) hsafe.1)
      (hagree 1 le_rfl (by decide))
    exact holdsList_mono (C_le h hagree hs0) _ id (fun _ h => h) (hT.2 _ _ _ _ hm)

end
end LeanVM.Guest.Backend.B2

/-- info: 'LeanVM.Guest.Backend.B2.b2SoundL_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.B2.b2SoundL_backend
