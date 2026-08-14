import InverseGalois.Rigidity.Certificate
import InverseGalois.Rigidity.StructureConstant
import InverseGalois.Rigidity.Rigidity
import InverseGalois.Rigidity.Symmetric
import InverseGalois.Rigidity.Braid
import InverseGalois.Rigidity.RET
import InverseGalois.Rigidity.Examples.S3Rigid

/-!
# The rigidity method for the inverse Galois problem

This module collects the rigidity criterion: a cheap, checkable **rigidity certificate**
(rational conjugacy-class data for a centerless finite group) proves that the group is an inverse
Galois group over `ℚ`.  The single analytic ingredient — the Riemann Existence Theorem — is
isolated as one recognizable statement (`inertiaRootData_exists`, `RET.Descent.Tower`, in its
tame-inertia form; `riemann_existence_cover`, `RET.Existence`, in its covers form); everything else
is complete Lean.

* `Rigidity.rigidity_realizable` — the criterion.
* `Rigidity.rigid_card_iff_single_orbit` — soundness: the certificate's cheap cardinality
  condition equals classical rigidity (a single simultaneous-conjugation orbit).
* `Rigidity.permCert`, `Rigidity.sn_isInverseGalois` — the rigid triple of a symmetric group
  (a transposition, an `(n-1)`-cycle and an `n`-cycle) assembled into a certificate, for every
  `n ≥ 3`.
* `Rigidity.braidTuple`, `Rigidity.braidConj_of_rigidityCertificate` — the Hurwitz braid moves on
  generating product-one tuples, and the Nielsen class of a certificate as a single orbit of the
  braid moves together with simultaneous conjugation.
* `Rigidity.S3Example.s3_isInverseGalois` — the `S₃` sanity example firing it end-to-end.
-/
