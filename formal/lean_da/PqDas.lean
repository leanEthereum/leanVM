/-
# PqDas

The definitions LeanDA's proofs use of the security framework for erasure code commitments of
Benedikt Wagner (`PqDas/Defs.lean`).

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified (`lean_da/NOTICE`). His vector commitments, his erasure code commitment and its
random-oracle runtime, and his proofs (position binding, committed soundness and its forking bound,
code binding) were removed when LeanDA's end statements stopped naming an argument of knowledge;
his repository has them.
-/
import PqDas.Defs
