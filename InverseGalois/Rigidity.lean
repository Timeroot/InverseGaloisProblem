import InverseGalois.Rigidity.Certificate
import InverseGalois.Rigidity.StructureConstant
import InverseGalois.Rigidity.RiemannExistence
import InverseGalois.Rigidity.Rigidity
import InverseGalois.Rigidity.Examples.S3Rigid

/-!
# The rigidity method for the inverse Galois problem

This module collects the rigidity criterion: a cheap, checkable **rigidity certificate**
(rational conjugacy-class data for a centerless finite group) proves that the group is an inverse
Galois group over `ℚ`.  The single analytic ingredient — the Riemann Existence Theorem — is
isolated as a labelled axiom in `InverseGalois.Rigidity.RiemannExistence`; everything else is
axiom-free.

* `Rigidity.rigidity_realizable` — the criterion.
* `Rigidity.rigid_card_iff_single_orbit` — soundness: the certificate's cheap cardinality
  condition equals classical rigidity (a single simultaneous-conjugation orbit).
* `Rigidity.S3Example.s3_isInverseGalois` — the `S₃` sanity example firing it end-to-end.
-/
