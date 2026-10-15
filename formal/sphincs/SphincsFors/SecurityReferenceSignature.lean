import SphincsFors.SecurityReferenceChoice
import SphincsFors.SecuritySignatureWitness

/-! The reference WOTS word and counter chosen by the actual canonical encoding search at each
leaf, defined also for unsigned leaves and exhausted searches. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.SignatureWitness
open Concrete

attribute [local irreducible] messageDigest ftsRecover otsLeaf treeFold
  Seeded.ftsKey Seeded.treeRoot Seeded.treePath chainWalk encode

noncomputable def chosenWord (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : Encoding :=
  ReferenceChoice.word f parameter topLayer rootTree leaf (canonicalFors f parameter seed leaf)

noncomputable def chosenCounter (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : Option Counter :=
  (ReferenceChoice.selection f parameter topLayer rootTree leaf
    (canonicalFors f parameter seed leaf)).map Prod.fst

end SphincsFors.Security.SignatureWitness
