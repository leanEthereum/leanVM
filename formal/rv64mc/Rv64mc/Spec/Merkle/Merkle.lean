/-
  Rv64mc.Spec.Merkle.Merkle

  The contracts of `merkle.rs`, each returning a digest through `sret` (`a0`) as `Spec.Hash.KeccakHash` does:

  * `hash_pair(left, right)`: the image passes both as `[u8; 32]` (pointers in `a1`, `a2`); `Model.hashPairRust`.
  * `hash_leaf(image)`: the `K` words as a pointer and a length (`a1`, `a2`); `Model.hashLeafRust`.
  * `MerklePath::root(&self)`: the path at `a1` an opening's (`Spec.Transcript.PathAt`); `MerklePathRust.root`.
-/

import Rv64mc.Spec.Hash.Keccak
import Rv64mc.Spec.Transcript.Repr
import Rv64mc.Model.Merkle

namespace Rv64mc.Spec.Merkle

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Protocol.Compile Rv64mc.Spec.Hash

namespace HashPair

def Pre (env : Env) (l r : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestSlot env m (regs .x2) (regs .x10) ∧ DigestAt m (regs .x11) l ∧ DigestAt m (regs .x12) r ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.Digest.byteSize ∧
    env.Owned m (regs .x2) (regs .x12) Layouts.Digest.byteSize

def Post (l r : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  DigestPost m (regs .x10) m' (Model.hashPairRust l r)

/-- **The contract of `hash_pair`**, function `i` of `p` with `need` bytes of stack, for every two digests. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ l r, Holds env p i need (Pre env l r) (Post l r) fun regs _ => DigestOut (regs .x10)

end HashPair

namespace HashLeaf

def Pre (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestSlot env m (regs .x2) (regs .x10) ∧ SliceArgs WordsAt m (regs .x11) (regs .x12) ws ∧
    env.Live m (regs .x11) (Layouts.K.byteSize * ws.length)

def Post (ws : List Word) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  DigestPost m (regs .x10) m' (Model.hashLeafRust ws)

/-- **The contract of `hash_leaf`**, function `i` of `p` with `need` bytes of stack, for every leaf. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws, Holds env p i need (Pre env ws) (Post ws) fun regs _ => DigestOut (regs .x10)

end HashLeaf

namespace Root

def Pre (env : Env) (o : Opening) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestSlot env m (regs .x2) (regs .x10) ∧ Spec.Transcript.PathAt env m (regs .x11) o ∧
    env.Live m (regs .x11) Layouts.MerklePath.byteSize

def Post (o : Opening) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  DigestPost m (regs .x10) m' (Model.MerklePathRust.ofOpening o).root

/-- **The contract of `MerklePath::root`**, function `i` of `p` with `need` bytes of stack, for every opening. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ o, Holds env p i need (Pre env o) (Post o) fun regs _ => DigestOut (regs .x10)

end Root

end Rv64mc.Spec.Merkle
