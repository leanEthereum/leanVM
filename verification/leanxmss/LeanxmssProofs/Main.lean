import LeanxmssProofs.Verify

/-!
# The guest's `main`

`main` (`programs/leanxmss/guest/src/main.rs`) reads from the advice a count, then for each signature a public key, a
leaf index, a message and a signature, verifies it, and commits its claim: the key, the leaf index and the message.

Aeneas has no model of `read` and `commit`, which act on the VM's memory, so `main` is transcribed here by hand
(`mainModel`), line by line, over the advice as a list of words: a read takes the next words and panics past the end
of the advice, a panic is `fail`, and the committed words are the result. It calls the Aeneas translation of
`verify`. The run's public output is the BLAKE2s digest of the committed words' bytes (`output`).

`main_spec` then says: a run succeeds exactly when the advice holds a count and that many entries, each with a leaf
index below `2^32` and a signature the specification's `verify` accepts, and it commits exactly their claims.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Main

open Bytes Statement Proofs

/-- Words `i` and `i + 1` as a digest. -/
def arr2 (ws : List U64) (i : Nat) : Std.Array U64 2#usize :=
  Std.Array.make 2#usize [ws.getD i 0#u64, ws.getD (i + 1) 0#u64]

/-- `read_unchecked::<PublicKey>()`: four words, `repr(C)`, so `merkle_root` then `public_param`. -/
def publicKeyOf (ws : List U64) : leanxmss.PublicKey := { merkle_root := arr2 ws 0, public_param := arr2 ws 2 }

/-- `read::<Message>()`: four words. -/
def messageOf (ws : List U64) : Std.Array U64 4#usize :=
  Std.Array.make 4#usize [ws.getD 0 0#u64, ws.getD 1 0#u64, ws.getD 2 0#u64, ws.getD 3 0#u64]

/-- `read_unchecked::<Signature>()`: 151 words, `repr(C)`, so 42 chain tips, then the randomness, then 32 siblings. -/
def signatureOf (ws : List U64) : leanxmss.Signature :=
  { chain_tips := Std.Array.make 42#usize (List.ofFn fun i : Fin 42 => arr2 ws (2 * i.val)) (by simp)
    randomness := Std.Array.make 3#usize [ws.getD 84 0#u64, ws.getD 85 0#u64, ws.getD 86 0#u64]
    merkle_proof := Std.Array.make 32#usize (List.ofFn fun i : Fin 32 => arr2 ws (87 + 2 * i.val)) (by simp) }

/-- `read`: the `k` words at `pos`, or a panic past the end of the advice. -/
def readWords (advice : List U64) (pos k : Nat) : Result (List U64) :=
  if pos + k ≤ advice.length then ok ((advice.drop pos).take k) else fail .panic

/-- `LeafIndex::try_from(leaf_index)`: the low 32 bits, which are all of it below `2^32`. -/
def leafIndexOf (w : U64) : Std.U32 := ⟨w.bv.setWidth 32⟩

/-- The loop of `main`: `k` signatures left, the next at advice word `pos`, `out` committed so far. -/
def mainLoop (advice : List U64) : Nat → Nat → List U64 → Result (List U64)
  | 0, _, out => ok out
  | k + 1, pos, out => do
    let pkW ← readWords advice pos 4
    let leafW ← readWords advice (pos + 4) 1
    let msgW ← readWords advice (pos + 5) 4
    let sigW ← readWords advice (pos + 9) 151
    let leafIndex := leafW.getD 0 0#u64
    if leafIndex.val < 2 ^ 32 then
      let r ← leanxmss.verify (publicKeyOf pkW) (leafIndexOf leafIndex) (messageOf msgW) (signatureOf sigW)
      match r with
      | .Ok () =>
        -- `commit` of the key's two fields, the leaf index as read (a whole word), and the message.
        mainLoop advice k (pos + 160) (out ++ pkW ++ [leafIndex] ++ msgW)
      | .Err _ => fail .panic
    else fail .panic

/-- `main`: the count, then the loop from advice word 1. -/
def mainModel (advice : List U64) : Result (List U64) := do
  let nW ← readWords advice 0 1
  mainLoop advice (nW.getD 0 0#u64).val 1 []

/-- The run's public output: the BLAKE2s digest of the committed words' bytes (`sdk/src/io.rs`). -/
def output (committed : List U64) : Std.Array U64 4#usize := blake2s (ofWords committed)

/-! ## What the advice holds -/

/-- One signature as `main` reads it. -/
structure Entry where
  pk : leanxmss.PublicKey
  leafIndex : U64
  message : Std.Array U64 4#usize
  signature : leanxmss.Signature

/-- The entry 160 advice words hold, read as `main` reads them: 4 words of key, 1 of leaf index, 4 of message, 151
of signature. -/
def Entry.ofWords (ws : List U64) : Entry :=
  { pk := publicKeyOf (ws.take 4)
    leafIndex := (ws.drop 4).getD 0 0#u64
    message := messageOf ((ws.drop 5).take 4)
    signature := signatureOf ((ws.drop 9).take 151) }

/-- An entry's 160 advice words: `Entry.ofWords` inverts it (`ofWords_words`). -/
def Entry.words (e : Entry) : List U64 :=
  e.pk.merkle_root.val ++ e.pk.public_param.val ++ [e.leafIndex] ++ e.message.val ++
    e.signature.chain_tips.val.flatMap (·.val) ++ e.signature.randomness.val ++
    e.signature.merkle_proof.val.flatMap (·.val)

/-- An entry's claim, the words `main` commits for it: the key's two fields, the leaf index and the message. -/
def Entry.claim (e : Entry) : List U64 :=
  e.pk.merkle_root.val ++ e.pk.public_param.val ++ [e.leafIndex] ++ e.message.val

/-- The entry is a valid signature under the specification: its leaf index is below `2^32` and the specification's
`verify` accepts it. -/
def Entry.valid (e : Entry) : Prop :=
  e.leafIndex.val < 2 ^ 32 ∧
    EthCryptographySpecs.Xmss.verify (Statement.publicKey e.pk) (Statement.message e.message)
      (Statement.signature e.signature) (UInt32.ofNat e.leafIndex.val) = true

/-- The count the advice starts with. -/
def count (advice : List U64) : Nat := (advice.getD 0 0#u64).val

/-- The `n` entries after the count. -/
def entries (advice : List U64) (n : Nat) : List Entry :=
  List.ofFn fun j : Fin n => Entry.ofWords ((advice.drop (1 + 160 * j.val)).take 160)

/-! ## Proofs -/

theorem readWords_ok {advice : List U64} {pos k : Nat} {ws : List U64} :
    readWords advice pos k = ok ws ↔ pos + k ≤ advice.length ∧ ws = (advice.drop pos).take k := by
  unfold readWords
  split <;> simp_all [eq_comm]

theorem list4 (ws : List U64) (h : ws.length = 4) :
    [ws.getD 0 0#u64, ws.getD 1 0#u64, ws.getD 2 0#u64, ws.getD 3 0#u64] = ws := by
  match ws, h with
  | [_, _, _, _], _ => rfl

theorem claim_ofWords (S : List U64) (h : 160 ≤ S.length) :
    (Entry.ofWords S).claim = S.take 4 ++ [(S.drop 4).getD 0 0#u64] ++ (S.drop 5).take 4 := by
  have h4 : (S.take 4).length = 4 := by simp; omega
  have h5 : ((S.drop 5).take 4).length = 4 := by simp; omega
  simp only [Entry.claim, Entry.ofWords, publicKeyOf, messageOf, arr2, Std.Array.make_val]
  rw [list4 _ h5]
  conv => rhs; rw [← list4 _ h4]
  simp

/-- The result of `verify` is `Ok(())` exactly when the specification accepts. -/
theorem specResult_eq_ok_iff (pk : leanxmss.PublicKey) (leaf : Std.U32) (msg : Std.Array U64 4#usize)
    (sig : leanxmss.Signature) :
    specResult pk leaf msg sig = .Ok () ↔
      EthCryptographySpecs.Xmss.verify (publicKey pk) (message msg) (signature sig) (epoch leaf) = true := by
  have := verify_ok_iff pk leaf msg sig
  rw [verify_spec] at this
  rw [← this]
  exact ⟨fun h => h ▸ rfl, fun h => Result.ok_injective h⟩

theorem epoch_leafIndexOf (w : U64) (h : w.val < 2 ^ 32) : epoch (leafIndexOf w) = UInt32.ofNat w.val := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by simpa using h)]
  show (w.bv.setWidth 32).toNat = w.val
  rw [BitVec.toNat_setWidth, UScalar.bv_toNat, Nat.mod_eq_of_lt (by simpa using h)]

/-- The loop: `k` entries from advice word `pos`. -/
theorem mainLoop_ok (advice : List U64) (k : Nat) : ∀ (pos : Nat) (out out' : List U64),
    pos ≤ advice.length → (mainLoop advice k pos out = ok out' ↔
      pos + 160 * k ≤ advice.length ∧
        (∀ j : Fin k, (Entry.ofWords ((advice.drop (pos + 160 * j.val)).take 160)).valid) ∧
        out' = out ++ (List.ofFn fun j : Fin k =>
          (Entry.ofWords ((advice.drop (pos + 160 * j.val)).take 160)).claim).flatten) := by
  induction k with
  | zero => intro pos out out' hpos; simp [mainLoop, eq_comm, hpos]
  | succ k ih =>
    intro pos out out' hpos
    simp only [mainLoop]
    by_cases hlen : pos + 160 ≤ advice.length
    · have r1 : readWords advice pos 4 = ok ((advice.drop pos).take 4) := by simp [readWords]; omega
      have r2 : readWords advice (pos + 4) 1 = ok ((advice.drop (pos + 4)).take 1) := by simp [readWords]; omega
      have r3 : readWords advice (pos + 5) 4 = ok ((advice.drop (pos + 5)).take 4) := by simp [readWords]; omega
      have r4 : readWords advice (pos + 9) 151 = ok ((advice.drop (pos + 9)).take 151) := by simp [readWords]; omega
      simp only [r1, r2, r3, r4, Std.bind_ok]
      -- The four reads are the parts of the entry's 160 words.
      have hS : 160 ≤ ((advice.drop pos).take 160).length := by simp; omega
      have e1 : (advice.drop pos).take 4 = ((advice.drop pos).take 160).take 4 := by simp [List.take_take]
      have e2 : ((advice.drop (pos + 4)).take 1).getD 0 0#u64 = (((advice.drop pos).take 160).drop 4).getD 0 0#u64 := by
        simp [List.drop_take, List.drop_drop, List.getD_eq_getElem?_getD] <;> omega
      have e3 : (advice.drop (pos + 5)).take 4 = (((advice.drop pos).take 160).drop 5).take 4 := by
        simp [List.drop_take, List.drop_drop, List.take_take] <;> omega
      have e4 : (advice.drop (pos + 9)).take 151 = (((advice.drop pos).take 160).drop 9).take 151 := by
        simp [List.drop_take, List.drop_drop, List.take_take] <;> omega
      rw [e1, e2, e3, e4]
      generalize hE : Entry.ofWords ((advice.drop pos).take 160) = E
      have hclaim := claim_ofWords _ hS
      rw [hE] at hclaim
      have hpk : publicKeyOf (((advice.drop pos).take 160).take 4) = E.pk := by rw [← hE]; rfl
      have hleaf : (((advice.drop pos).take 160).drop 4).getD 0 0#u64 = E.leafIndex := by rw [← hE]; rfl
      have hmsg : messageOf ((((advice.drop pos).take 160).drop 5).take 4) = E.message := by rw [← hE]; rfl
      have hsig : signatureOf ((((advice.drop pos).take 160).drop 9).take 151) = E.signature := by rw [← hE]; rfl
      rw [hleaf] at hclaim
      rw [hpk, hleaf, hmsg, hsig, verify_spec]
      simp only [Std.bind_ok]
      rw [List.ofFn_succ, Fin.forall_fin_succ]
      simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, hE, Fin.val_succ, List.flatten_cons]
      have hshift : ∀ j : Nat, pos + 160 * (j + 1) = pos + 160 + 160 * j := fun j => by ring
      simp only [hshift]
      have hvalid : E.valid ↔ E.leafIndex.val < 2 ^ 32 ∧ specResult E.pk (leafIndexOf E.leafIndex) E.message E.signature = .Ok () := by
        unfold Entry.valid
        constructor
        · rintro ⟨hl, hv⟩
          exact ⟨hl, (specResult_eq_ok_iff _ _ _ _).mpr (by rw [epoch_leafIndexOf _ hl]; exact hv)⟩
        · rintro ⟨hl, hv⟩
          exact ⟨hl, by rw [← epoch_leafIndexOf _ hl]; exact (specResult_eq_ok_iff _ _ _ _).mp hv⟩
      rw [hvalid]
      by_cases hl : E.leafIndex.val < 2 ^ 32
      · simp only [hl, if_true, true_and]
        cases hr : specResult E.pk (leafIndexOf E.leafIndex) E.message E.signature with
        | Ok u =>
          cases u
          simp only
          rw [ih (pos + 160) _ _ hlen, hclaim]
          constructor
          · rintro ⟨h1, h2, h3⟩
            exact ⟨by omega, ⟨trivial, h2⟩, by rw [h3]; simp only [List.append_assoc]⟩
          · rintro ⟨h1, ⟨_, h2⟩, h3⟩
            exact ⟨by omega, h2, by rw [h3]; simp only [List.append_assoc]⟩
        | Err e =>
          simp
      · have hl' : ¬ E.leafIndex.val < 4294967296 := hl
        rw [if_neg hl]; simp [hl']
    · -- The advice ends inside the entry: one of the four reads panics.
      have : ¬ (pos + 160 * (k + 1) ≤ advice.length) := by omega
      simp only [this, false_and, iff_false]
      have rd : ∀ p k, readWords advice p k = if p + k ≤ advice.length then ok ((advice.drop p).take k)
          else fail .panic := fun _ _ => rfl
      rw [rd, rd, rd, rd]
      by_cases h1 : pos + 4 ≤ advice.length
      · by_cases h2 : pos + 4 + 1 ≤ advice.length
        · by_cases h3 : pos + 5 + 4 ≤ advice.length
          · have h4 : ¬ (pos + 9 + 151 ≤ advice.length) := by omega
            simp [h1, h2, h3, h4]
          · simp [h1, h2, h3]
        · simp [h1, h2]
      · simp [h1]

/-- A run of `main` succeeds exactly when the advice holds the count and that many entries, all valid; it then
commits their claims, in order. Otherwise it panics: it never runs forever. -/
theorem main_spec (advice out : List U64) :
    mainModel advice = ok out ↔
      1 + 160 * count advice ≤ advice.length ∧ (∀ e ∈ entries advice (count advice), e.valid) ∧
        out = (entries advice (count advice)).flatMap Entry.claim := by
  unfold mainModel
  by_cases h0 : 0 + 1 ≤ advice.length
  · have r0 : readWords advice 0 1 = ok (advice.take 1) := by rw [readWords, if_pos h0, List.drop_zero]
    rw [r0, Std.bind_ok]
    have hc : (advice.take 1).getD 0 0#u64 = advice.getD 0 0#u64 := by
      match advice, h0 with
      | a :: _, _ => simp
    rw [hc, mainLoop_ok advice _ 1 [] out (by omega)]
    simp only [count, entries, List.forall_mem_ofFn_iff, List.nil_append, List.flatMap_def, List.map_ofFn]
    rfl
  · have r0 : readWords advice 0 1 = fail .panic := by rw [readWords, if_neg h0]
    rw [r0]
    simp only [Std.bind_fail]
    simp
    omega

/-- `main` never runs forever: it commits or it panics. -/
theorem mainLoop_terminates (advice : List U64) (k : Nat) : ∀ (pos : Nat) (out : List U64),
    (∃ o, mainLoop advice k pos out = ok o) ∨ mainLoop advice k pos out = fail .panic := by
  induction k with
  | zero => intro pos out; exact .inl ⟨out, rfl⟩
  | succ k ih =>
    intro pos out
    have rd : ∀ p k, readWords advice p k = if p + k ≤ advice.length then ok ((advice.drop p).take k)
        else fail .panic := fun _ _ => rfl
    simp only [mainLoop, rd]
    split_ifs <;> simp only [Std.bind_ok, Std.bind_fail, verify_spec, or_true]
    split_ifs
    · generalize specResult _ _ _ _ = r
      cases r with
      | Ok u => cases u; exact ih _ _
      | Err e => exact .inr rfl
    · exact .inr rfl

theorem main_terminates (advice : List U64) : (∃ out, mainModel advice = ok out) ∨ mainModel advice = fail .panic := by
  unfold mainModel readWords
  split_ifs
  · simp only [Std.bind_ok]; exact mainLoop_terminates _ _ _ _
  · simp
