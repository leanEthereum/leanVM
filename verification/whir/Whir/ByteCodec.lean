import Whir.Concrete
import Whir.FiatShamirGame

/-! Little-endian codecs of baseline `fiat_shamir/src/merkle.rs:15-37,47-51,62-67`
at `69f5499304a6957f6780c8998999d783bae13302`. The Merkle file is byte-identical
in conditional #552 (`ff6a275304a3b577118b066ddcff83bfafa5998d`).
These are byte encodings, not assumptions about the hash primitive or a
Fiat–Shamir security claim for either transcript version. -/
namespace Whir.ByteCodec
open Concrete FiatShamirGame

def encodeNat : (n : Nat) → Nat → (Fin n → Byte)
  | 0, _, i => Fin.elim0 i
  | n + 1, x, i => Fin.cases ⟨x % 256, Nat.mod_lt _ (by decide)⟩
      (encodeNat n (x / 256)) i

def decodeNat : (n : Nat) → (Fin n → Byte) → Nat
  | 0, _ => 0
  | n + 1, b => (b 0).val + 256 * decodeNat n (fun i => b i.succ)

theorem decodeNat_lt (n : Nat) (b : Fin n → Byte) : decodeNat n b < 256 ^ n := by
  induction n with
  | zero => simp [decodeNat]
  | succ n ih =>
    have h := ih (fun i => b i.succ)
    have hb := (b 0).isLt
    simp only [decodeNat, pow_succ]
    omega

theorem decodeNat_encodeNat (n x : Nat) (h : x < 256 ^ n) :
    decodeNat n (encodeNat n x) = x := by
  induction n generalizing x with
  | zero => simp only [pow_zero] at h; simp [decodeNat]; omega
  | succ n ih =>
    have hd : x / 256 < 256 ^ n := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa [pow_succ] using h
    simp only [decodeNat, encodeNat, Fin.cases_zero, Fin.cases_succ]
    rw [ih _ hd]
    exact Nat.mod_add_div x 256

theorem encodeNat_decodeNat (n : Nat) (b : Fin n → Byte) :
    encodeNat n (decodeNat n b) = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Fin.ext
      simp [encodeNat, decodeNat, Nat.add_mod, Nat.mod_eq_of_lt (b 0).isLt]
    · simp only [encodeNat, decodeNat, Fin.cases_succ]
      rw [Nat.add_mul_div_left _ _ (by decide)]
      rw [Nat.div_eq_of_lt (b 0).isLt, Nat.zero_add]
      exact congrFun (ih (fun i => b i.succ)) j

/-- Byte `i` is exactly the base-256 little-endian digit, not merely an
arbitrary injective representation of the machine word. -/
theorem encodeNat_byte (n x : Nat) (i : Fin n) :
    (encodeNat n x i).val = (x / 256 ^ i.val) % 256 := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [encodeNat]
    · simp only [encodeNat, Fin.cases_succ, Fin.val_succ]
      rw [ih]
      simp [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

def encodeK (x : K) : Fin 8 → Byte := encodeNat 8 x.toNat
def decodeK (b : Fin 8 → Byte) : K := UInt64.ofNat (decodeNat 8 b)

theorem encodeK_byte (x : K) (i : Fin 8) :
    (encodeK x i).val = (x.toNat / 256 ^ i.val) % 256 :=
  encodeNat_byte 8 x.toNat i

theorem decodeK_encodeK (x : K) : decodeK (encodeK x) = x := by
  unfold decodeK encodeK
  rw [decodeNat_encodeNat]
  · simp
  · exact x.toNat_lt

theorem encodeK_decodeK (b : Fin 8 → Byte) : encodeK (decodeK b) = b := by
  unfold encodeK decodeK
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show decodeNat 8 b < 2 ^ 64 from decodeNat_lt 8 b)]
  exact encodeNat_decodeNat 8 b

theorem encodeK_injective : Function.Injective encodeK :=
  Function.LeftInverse.injective decodeK_encodeK

def encodeE (x : E) : Scalar24 := fun i =>
  if h : i.val < 8 then encodeK x.c0 ⟨i.val, h⟩
  else if h' : i.val < 16 then encodeK x.c1 ⟨i.val - 8, by omega⟩
  else encodeK x.c2 ⟨i.val - 16, by omega⟩

def decodeE (b : Scalar24) : E :=
  ⟨decodeK (fun i => b ⟨i.val, by omega⟩),
   decodeK (fun i => b ⟨i.val + 8, by omega⟩),
   decodeK (fun i => b ⟨i.val + 16, by omega⟩)⟩

theorem decodeE_encodeE (x : E) : decodeE (encodeE x) = x := by
  have h0 : (fun i : Fin 8 => encodeE x ⟨i.val, by omega⟩) = encodeK x.c0 := by
    funext i; simp [encodeE, i.isLt]
  have h1 : (fun i : Fin 8 => encodeE x ⟨i.val + 8, by omega⟩) = encodeK x.c1 := by
    funext i; simp [encodeE, show ¬i.val + 8 < 8 by omega, show i.val + 8 < 16 by omega]
  have h2 : (fun i : Fin 8 => encodeE x ⟨i.val + 16, by omega⟩) = encodeK x.c2 := by
    funext i; simp [encodeE, show ¬i.val + 16 < 8 by omega, show ¬i.val + 16 < 16 by omega]
  simp only [decodeE, h0, h1, h2, decodeK_encodeK]

theorem encodeE_decodeE (b : Scalar24) : encodeE (decodeE b) = b := by
  funext i
  unfold encodeE decodeE
  split <;> try split
  all_goals simp only [encodeK_decodeK]
  all_goals congr 1
  all_goals apply Fin.ext; dsimp; omega

theorem encodeE_injective : Function.Injective encodeE :=
  Function.LeftInverse.injective decodeE_encodeE

def pairBytes (p : Digest32 × Digest32) : Fin 64 → Byte := fun i =>
  if h : i.val < 32 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 32, by omega⟩

theorem pairBytes_injective : Function.Injective pairBytes := by
  intro a b h
  apply Prod.ext
  · funext i
    have := congrFun h ⟨i.val, by omega⟩
    simpa [pairBytes, i.isLt] using this
  · funext i
    have := congrFun h ⟨i.val + 32, by omega⟩
    simpa [pairBytes, show ¬ i.val + 32 < 32 by omega] using this

def hashToScalars (b : Digest32) : E × E :=
  (⟨decodeK (fun i => b ⟨i.val, by omega⟩),
    decodeK (fun i => b ⟨i.val + 8, by omega⟩), 0⟩,
   ⟨decodeK (fun i => b ⟨i.val + 16, by omega⟩),
    decodeK (fun i => b ⟨i.val + 24, by omega⟩), 0⟩)

def scalarHalves (p : E × E) : Digest32 := fun i =>
  if h : i.val < 8 then encodeK p.1.c0 ⟨i.val, h⟩
  else if h' : i.val < 16 then encodeK p.1.c1 ⟨i.val - 8, by omega⟩
  else if h'' : i.val < 24 then encodeK p.2.c0 ⟨i.val - 16, by omega⟩
  else encodeK p.2.c1 ⟨i.val - 24, by omega⟩

def scalarsToHash (p : E × E) : Option Digest32 :=
  if p.1.c2 = 0 ∧ p.2.c2 = 0 then some (scalarHalves p) else none

theorem scalarsToHash_hashToScalars (b : Digest32) :
    scalarsToHash (hashToScalars b) = some b := by
  simp only [scalarsToHash, hashToScalars, and_self, ite_true]
  congr 1
  funext i
  unfold scalarHalves
  split <;> try split <;> try split
  all_goals simp only [encodeK_decodeK]
  all_goals congr 1
  all_goals apply Fin.ext; dsimp; omega

theorem hashToScalars_scalarHalves (p : E × E) :
    hashToScalars (scalarHalves p) =
      (⟨p.1.c0, p.1.c1, 0⟩, ⟨p.2.c0, p.2.c1, 0⟩) := by
  have h0 : (fun i : Fin 8 => scalarHalves p ⟨i.val, by omega⟩) = encodeK p.1.c0 := by
    funext i; simp [scalarHalves, i.isLt]
  have h1 : (fun i : Fin 8 => scalarHalves p ⟨i.val + 8, by omega⟩) = encodeK p.1.c1 := by
    funext i; simp [scalarHalves, show ¬i.val + 8 < 8 by omega, show i.val + 8 < 16 by omega]
  have h2 : (fun i : Fin 8 => scalarHalves p ⟨i.val + 16, by omega⟩) = encodeK p.2.c0 := by
    funext i
    simp [scalarHalves, show ¬i.val + 16 < 8 by omega,
      show ¬i.val + 16 < 16 by omega, show i.val + 16 < 24 by omega]
  have h3 : (fun i : Fin 8 => scalarHalves p ⟨i.val + 24, by omega⟩) = encodeK p.2.c1 := by
    funext i
    simp [scalarHalves, show ¬i.val + 24 < 8 by omega,
      show ¬i.val + 24 < 16 by omega, show ¬i.val + 24 < 24 by omega]
  simp only [hashToScalars, h0, h1, h2, h3, decodeK_encodeK]

theorem hashToScalars_scalarsToHash (p : E × E) (b : Digest32)
    (accepted : scalarsToHash p = some b) : hashToScalars b = p := by
  unfold scalarsToHash at accepted
  split at accepted
  · rename_i h
    cases accepted
    rw [hashToScalars_scalarHalves]
    rcases p with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
    simp only at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  · contradiction

theorem scalarsToHash_noncanonical (p : E × E) (h : p.1.c2 ≠ 0 ∨ p.2.c2 ≠ 0) :
    scalarsToHash p = none := by
  simp only [scalarsToHash]
  split
  · rename_i hp; rcases h with h | h <;> simp_all
  · rfl

/-- Exact leaf preimage: consecutive little-endian K words, without a tag. -/
def wordsBytes (words : List K) : List Byte :=
  words.flatMap (fun x => List.ofFn (encodeK x))

theorem wordsBytes_injective : Function.Injective wordsBytes := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons x xs =>
      have := congrArg List.length h
      simp [wordsBytes] at this
  | cons x xs ih =>
    intro b h
    cases b with
    | nil =>
      have := congrArg List.length h
      simp [wordsBytes] at this
    | cons y ys =>
      have first := congrArg (List.take 8) h
      have rest := congrArg (List.drop 8) h
      have ex : x = y := by
        apply encodeK_injective
        apply List.ofFn_injective
        simpa [wordsBytes, List.take_append] using first
      have er : xs = ys := ih (by simpa [wordsBytes, List.drop_append] using rest)
      exact congrArg₂ List.cons ex er

theorem hashToScalars_injective : Function.Injective hashToScalars := by
  intro a b h
  have := congrArg scalarsToHash h
  simpa [scalarsToHash_hashToScalars] using this

/-- Intermediate WHIR rows (`pcs/src/whir/verify.rs:224-227`) use consecutive
three-word groups, in c0/c1/c2 order, with no lane reversal. These are arbitrary
E elements, not digest halves: a nonzero third word is valid here. -/
def fieldWords (fields : List E) : List K :=
  fields.flatMap (fun x => [x.c0,x.c1,x.c2])

def wordsToFields : List K → Option (List E)
  | [] => some []
  | a :: b :: c :: rest => (wordsToFields rest).map (⟨a,b,c⟩ :: ·)
  | _ => none

theorem wordsToFields_fieldWords (fields : List E) :
    wordsToFields (fieldWords fields) = some fields := by
  induction fields with
  | nil => rfl
  | cons x xs ih =>
    change (wordsToFields (fieldWords xs)).map (x :: ·) = some (x :: xs)
    rw [ih]
    rfl

theorem fieldWords_wordsToFields (words : List K) (fields : List E)
    (decoded : wordsToFields words = some fields) : fieldWords fields = words := by
  induction words using (measure List.length).wf.induction generalizing fields with
  | _ words ih =>
    cases words with
    | nil => simp [wordsToFields] at decoded; subst fields; rfl
    | cons a ws =>
      cases ws with
      | nil => simp [wordsToFields] at decoded
      | cons b ws =>
        cases ws with
        | nil => simp [wordsToFields] at decoded
        | cons c rest =>
          simp only [wordsToFields, Option.map_eq_some_iff] at decoded
          obtain ⟨tail,ht,rfl⟩ := decoded
          have he := ih rest (by change rest.length < (a :: b :: c :: rest).length; simp; omega) tail ht
          change a :: b :: c :: fieldWords tail = a :: b :: c :: rest
          rw [he]

theorem fieldWords_length (fields : List E) : (fieldWords fields).length = 3 * fields.length := by
  induction fields with
  | nil => rfl
  | cons x xs ih => simp [fieldWords] at *; omega

theorem wordsToFields_length (words : List K) (fields : List E)
    (decoded : wordsToFields words = some fields) : words.length = 3 * fields.length := by
  rw [← fieldWords_wordsToFields words fields decoded, fieldWords_length]

theorem wordsToFields_total (words : List K) (width : Nat)
    (shape : words.length = 3 * width) :
    ∃ fields, wordsToFields words = some fields ∧ fields.length = width := by
  induction width generalizing words with
  | zero => simp at shape; subst words; exact ⟨[],rfl,rfl⟩
  | succ width ih =>
    cases words with
    | nil => simp at shape
    | cons a ws =>
      cases ws with
      | nil => simp at shape; omega
      | cons b ws =>
        cases ws with
        | nil => simp at shape; omega
        | cons c rest =>
          obtain ⟨fields,hf,hlen⟩ := ih rest (by simp at shape; omega)
          exact ⟨⟨a,b,c⟩ :: fields, by simp [wordsToFields,hf], by simp [hlen]⟩

theorem fieldWords_injective : Function.Injective fieldWords :=
  fun _ _ h => Option.some.inj ((wordsToFields_fieldWords _).symm.trans
    ((congrArg wordsToFields h).trans (wordsToFields_fieldWords _)))

end Whir.ByteCodec
