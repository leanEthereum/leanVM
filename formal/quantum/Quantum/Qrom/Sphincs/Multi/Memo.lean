module

public import Quantum.Cost.Charge
public import Quantum.Qrom.SufCma.MultiOne
public import Quantum.Qrom.Sphincs.Scheme
public import Quantum.Sphincs.HonestTable.Disclosure

@[expose] public section

/-!
# leanSPHINCS's multi-user signing ports with a selection memo, in the QROM

Every leanSPHINCS signature recomputes the counter searches of its three WOTS+C keys
`keyOf l idx` from counter `0`, and each key signs one fixed value. The memo transform
`memoFromS T x` runs the adversary `x` and attaches to each signing request of user `i` user `i`'s
memo `T i` (per key, its search result once computed), reading the request's index and the three
layers' selections from the answer (`MemoAns`) into the memo.

* `SelS`, `KeyMemo`, `SelMemoS n`, `MemoAns`: a search result, one user's memo, all users' memos,
  the memo part of an answer.
* `memoSpecS n`: the adversary's ports with the memo.
* `SelMemoS.put T i a`: memoize the answer `a` of user `i`; `layerSels`: layer selections.
* `memoFromS T x`: the memo transform.
* `memoChargeS α β`: `α` per hash call, `β` per signing request.
* `sphincsValid`, `MuAdversaryS n`: leanSPHINCS's transcript validity (every transcript, as the
  scheme is stateless) and multi-user adversaries.

## Main statements

* `isChargeBound_memoFromS_of_le`: the memo transform keeps a charge bound for a charge on the
  memo ports at most the adversary's charge of the same call.
* `isChargeBound_memoFromS_memoChargeS`: `α` per hash call and `β` per request cost at most
  `α * q + β * total`.
* `sphincs_muQuantumStronglyUnforgeable_one_iff`: with one user, leanSPHINCS's multi-user SUF-CMA
  is the single-user one.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key keyOf)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec MuAdversary cmdCharge hashCharge signCharge
  signChargeAt MuSignLog)

namespace Quantum.Qrom.Sphincs.Multi

attribute [local irreducible] sphincsRom

variable {n : ℕ}

/-! ## The memo and the signing ports with the memo -/

/-- A key's counter-search result (single-user `QTable.select`'s type). -/
abbrev SelS : Type :=
  Option (EncodingCounter × Encoding)

/-- One user's memo: per WOTS+C key, its search result once computed. -/
abbrev KeyMemo : Type :=
  Key → Option SelS

/-- All users' memos. -/
abbrev SelMemoS (n : ℕ) : Type :=
  Fin n → KeyMemo

/-- The memo part of an answer: the request's index and the three layers' selections. -/
abbrev MemoAns : Type :=
  Index × (Layer → SelS)

/-- Signing port `.sign i (M, h)`: message `M` of user `i` with user `i`'s memo `h`; answer the
signature and `MemoAns`. -/
abbrev memoSpecS (n : ℕ) : QuantumOracleSpec.{0, 0} :=
  muAdvSpec n (Message × KeyMemo) (Option Signature × MemoAns)

-- The adversary's commands, as indexed polynomial functors.
set_option quotPrecheck false in
local notation "MuPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n Message (Option Signature))

set_option quotPrecheck false in
local notation "MemoPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpecS n)

/-- Memoize the answer `a` of user `i`: each layer's key of the index, its selection. -/
def SelMemoS.put (T : SelMemoS n) (i : Fin n) (a : MemoAns) : SelMemoS n :=
  Function.update T i fun K ↦ if K = keyOf K.1 a.1 then some (a.2 K.1) else T i K

theorem SelMemoS.put_self (T : SelMemoS n) (i : Fin n) (a : MemoAns) (l : Layer) :
    T.put i a i (keyOf l a.1) = some (a.2 l) := by
  simp only [SelMemoS.put, Function.update_self]
  split_ifs with hK
  · rfl
  · exact absurd rfl hK

theorem SelMemoS.put_of_ne (T : SelMemoS n) {i j : Fin n} {a : MemoAns} {K : Key}
    (h : ¬(j = i ∧ K = keyOf K.1 a.1)) : T.put i a j K = T j K := by
  simp only [SelMemoS.put]
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    split_ifs with hK
    · exact absurd ⟨rfl, hK⟩ h
    · rfl
  · rw [Function.update_of_ne hj]

/-- Layer selections from three values. -/
def layerSels (g₀ g₁ g₂ : SelS) : Layer → SelS :=
  fun l ↦ if l.val = 0 then g₀ else if l.val = 1 then g₁ else g₂

/-- **The memo transform**: the adversary's program with each signing request of user `i`
carrying user `i`'s memo, and the answer's selections memoized. -/
def memoFromS {Y : QReg → Type} : {A : QReg} → SelMemoS n → IFreeM (MuPS n) Y A →
    IFreeM (MemoPS n) Y A
  | _, _, .pure y => .pure y
  | _, T, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ memoFromS T (next b)
  | _, T, .liftBind (.query .hash E ℓ) next =>
      .liftBind (.query .hash E ℓ) fun b ↦ memoFromS T (next b)
  | _, T, .liftBind (.query (.sign i M) E ℓ) next =>
      .liftBind (.query (.sign i (M, T i)) E ℓ) fun b ↦
        memoFromS (T.put i (b.down : Option Signature × MemoAns).2)
          (next (ULift.up (b.down : Option Signature × MemoAns).1))

/-! ## Charges -/

/-- **The memo transform keeps a charge bound** for a charge on the memo ports at most the
adversary's charge of the same call. -/
theorem isChargeBound_memoFromS_of_le {Y : QReg → Type} {c : MuPort n Message → ℕ}
    {c' : MuPort n (Message × KeyMemo) → ℕ} (hh : c' .hash ≤ c .hash)
    (hs : ∀ i r h, c' (.sign i (r, h)) ≤ c (.sign i r)) {A : QReg} (x : IFreeM (MuPS n) Y A)
    (T : SelMemoS n) {m : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge c) m) :
    IFreeM.IsChargeBound (memoFromS T x) (cmdCharge c') m := by
  induction x using IFreeM.inductionOn generalizing T m with
  | pure _ _ => trivial
  | liftBind _ cmd next ih =>
    rcases cmd with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact ⟨hx.1, fun b ↦ ih b T (hx.2 b)⟩
    · exact ⟨hh.trans hx.1, fun b ↦ (ih b T (hx.2 b)).mono (Nat.sub_le_sub_left hh m)⟩
    · exact ⟨(hs i r _).trans hx.1, fun b ↦ (ih _ _ (hx.2 _)).mono
        (Nat.sub_le_sub_left (hs i r _) m)⟩

/-- The memo transform keeps the hash calls. -/
theorem isChargeBound_memoFromS_hash {Y : QReg → Type} {A : QReg} (x : IFreeM (MuPS n) Y A)
    (T : SelMemoS n) {q : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge hashCharge) q) :
    IFreeM.IsChargeBound (memoFromS T x) (cmdCharge hashCharge) q :=
  isChargeBound_memoFromS_of_le le_rfl (fun _ _ _ ↦ le_rfl) x T hx

/-- The memo transform keeps the signing requests. -/
theorem isChargeBound_memoFromS_sign {Y : QReg → Type} {A : QReg} (x : IFreeM (MuPS n) Y A)
    (T : SelMemoS n) {total : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge signCharge) total) :
    IFreeM.IsChargeBound (memoFromS T x) (cmdCharge signCharge) total :=
  isChargeBound_memoFromS_of_le le_rfl (fun _ _ _ ↦ le_rfl) x T hx

/-- The memo transform keeps the signing requests of user `i`. -/
theorem isChargeBound_memoFromS_signAt {Y : QReg → Type} {A : QReg} (x : IFreeM (MuPS n) Y A)
    (T : SelMemoS n) (i : Fin n) {m : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdCharge (signChargeAt i)) m) :
    IFreeM.IsChargeBound (memoFromS T x) (cmdCharge (signChargeAt i)) m :=
  isChargeBound_memoFromS_of_le le_rfl (fun _ _ _ ↦ le_rfl) x T hx

/-- The charge of the adversary's commands with the memo: `α` per hash call, `β` per signing
request. -/
def memoChargeS (α β : ℕ) : MuPort n (Message × KeyMemo) → ℕ
  | .hash => α
  | .sign _ _ => β

/-- **The adversary's charge with the memo**: `α` per hash call and `β` per request cost at most
`α * q + β * total`. -/
theorem isChargeBound_memoFromS_memoChargeS {Y : QReg → Type} {A : QReg}
    (x : IFreeM (MuPS n) Y A) (T : SelMemoS n) {q total : ℕ}
    (hhash : IFreeM.IsChargeBound x (cmdCharge hashCharge) q)
    (hsign : IFreeM.IsChargeBound x (cmdCharge signCharge) total) (α β : ℕ) :
    IFreeM.IsChargeBound (memoFromS T x) (cmdCharge (memoChargeS α β)) (α * q + β * total) := by
  have h1 := (isChargeBound_memoFromS_hash x T hhash).mul α
  have h2 := (isChargeBound_memoFromS_sign x T hsign).mul β
  refine (h1.add h2).mono_charge fun s cmd ↦ ?_
  rcases cmd with o | ⟨_ | ⟨i, r, h⟩, E, ℓ⟩
  · exact Nat.zero_le _
  · simp [cmdCharge, memoChargeS, hashCharge, signCharge]
  · simp [cmdCharge, memoChargeS, hashCharge, signCharge]

/-! ## Validity and one user -/

/-- **leanSPHINCS's transcript validity**: every transcript (the scheme is stateless). -/
def sphincsValid : SufCma.SignLog Message (Option Signature) → Bool :=
  fun _ ↦ true

theorem allValid_sphincsValid (log : MuSignLog n Message (Option Signature)) :
    log.allValid sphincsValid = true :=
  decide_eq_true fun _ ↦ rfl

/-- leanSPHINCS's multi-user adversaries. -/
abbrev MuAdversaryS (n : ℕ) : Type 1 :=
  SufCma.Multi.MuAdversary n PublicKey Message (Option Signature) Forgery

/-- **One user**: leanSPHINCS's multi-user SUF-CMA with one user, per-user and total limits
`limit`, is the single-user one. -/
theorem sphincs_muQuantumStronglyUnforgeable_one_iff {limit : ℕ} {bound : ℕ → ℝ≥0∞} :
    SufCma.Multi.MuQuantumStronglyUnforgeable sphincsRom sphincsValid 1 limit limit bound ↔
      SufCma.QuantumStronglyUnforgeable sphincsRom limit bound :=
  SufCma.Multi.muQuantumStronglyUnforgeable_one_iff sphincsRom sphincsValid fun _ _ _ ↦ rfl

end Quantum.Qrom.Sphincs.Multi

end
