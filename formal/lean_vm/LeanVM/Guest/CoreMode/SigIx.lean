/-
  LeanVM.Guest.CoreMode.SigIx

  The callees' signatures of a heap check read by number: each name's key (`strKey`, its bytes as a
  number) compared instead of the name, equal to the lookup by name, faster in the kernel.
-/

module

public import LeanVM.Guest.CoreMode.Defs

/-!
# The callees' signatures, by key

A heap check reads a callee's signature at each call and several times for each arm of a dispatch,
through `fun f ↦ bif f == core.name then hcert.sig else (csigs.lookup f).getD {}` (`heapwin.py`'s
`sigW`): a scan of the callee list comparing strings. The kernel compares two strings byte by byte
through their UTF-8 encodings, a few milliseconds each, so a dispatch over a hundred arms whose
callee list holds a hundred names spends most of its check there. `strKey` reads a string's bytes as
one number (base 256, a leading `1`), which is injective (`strKey_inj`), so the same lookup compares
numbers (`sigK`) once each name's key is known: one key per lookup, the callee list's keys stated
once (`sigK_eq`).
-/

namespace LeanVM.Guest.CoreMode

@[expose] public section

/-- A byte list as a number: base 256 from the last byte, over a leading `1`. -/
def bytesKey (l : List UInt8) : ℕ := l.foldr (fun b h ↦ h * 256 + b.toNat) 1

/-- **A string's key**: its UTF-8 bytes as one number (`bytesKey`). -/
def strKey (s : String) : ℕ := bytesKey s.toByteArray.data.toList

theorem one_le_bytesKey : ∀ l : List UInt8, 1 ≤ bytesKey l
  | [] => Nat.le_refl 1
  | b :: l => by
    have := one_le_bytesKey l
    change 1 ≤ bytesKey l * 256 + b.toNat
    omega

theorem bytesKey_inj : ∀ {l l' : List UInt8}, bytesKey l = bytesKey l' → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by
    have := one_le_bytesKey l'
    change 1 = bytesKey l' * 256 + b.toNat at h
    omega
  | b :: l, [], h => by
    have := one_le_bytesKey l
    change bytesKey l * 256 + b.toNat = 1 at h
    omega
  | b :: l, b' :: l', h => by
    change bytesKey l * 256 + b.toNat = bytesKey l' * 256 + b'.toNat at h
    have hb := b.toNat_lt
    have hb' := b'.toNat_lt
    have h1 : b.toNat = b'.toNat := by omega
    have h2 : bytesKey l = bytesKey l' := by omega
    rw [UInt8.toNat_inj.mp h1, bytesKey_inj h2]

theorem strKey_inj {s t : String} (h : strKey s = strKey t) : s = t :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (bytesKey_inj h)))

private theorem beq_strKey {s t : String} (h : s ≠ t) : Nat.beq (strKey s) (strKey t) = false := by
  cases hb : Nat.beq (strKey s) (strKey t)
  · rfl
  · exact absurd (strKey_inj (Nat.eq_of_beq_eq_true hb)) h

/-- The value of the first entry of `L` whose key (the entry of `K` at its position) is `k`. -/
def lookupK {β : Type} (k : ℕ) : List ℕ → List (String × β) → Option β
  | k' :: K, p :: L => bif Nat.beq k k' then some p.2 else lookupK k K L
  | _, _ => none

theorem lookupK_eq {β : Type} (g : String) :
    ∀ (L : List (String × β)), lookupK (strKey g) (L.map fun p ↦ strKey p.1) L = L.lookup g
  | [] => rfl
  | (n, G) :: L => by
    simp only [List.map_cons, lookupK, List.lookup_cons]
    by_cases h : g = n
    · subst h
      simp [Nat.beq_refl]
    · rw [beq_strKey h, beq_eq_false_iff_ne.mpr h, Bool.cond_false, lookupK_eq g L]

/-- **The callees' signatures by key**: the own signature `sig` at the key `own`, else the first entry of `L`
at the name's key (`K` the keys of `L`'s names), else none. -/
def sigK (own : ℕ) (sig : HSig) (K : List ℕ) (L : List (String × HSig)) (g : String) : HSig :=
  bif Nat.beq (strKey g) own then sig else (lookupK (strKey g) K L).getD {}

/-- **The lookup by name is the lookup by key**, `own` the own name's key and `K` the callees'. -/
theorem sigK_eq {name : String} {sig : HSig} {L : List (String × HSig)} {own : ℕ} {K : List ℕ}
    (hown : strKey name = own) (hK : L.map (fun p ↦ strKey p.1) = K) :
    (fun f ↦ bif f == name then sig else (L.lookup f).getD {}) = sigK own sig K L := by
  funext g
  subst hown hK
  rw [sigK, lookupK_eq]
  by_cases h : g = name
  · subst h
    simp [Nat.beq_refl]
  · rw [beq_eq_false_iff_ne.mpr h, beq_strKey h]

end

end LeanVM.Guest.CoreMode
