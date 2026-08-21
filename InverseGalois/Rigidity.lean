import InverseGalois.Rigidity.Certificate
import InverseGalois.Rigidity.StructureConstant
import InverseGalois.Rigidity.Rigidity
import InverseGalois.Rigidity.Symmetric
import InverseGalois.Rigidity.Braid
import InverseGalois.Rigidity.RET
import InverseGalois.Rigidity.Examples.S3Rigid
import InverseGalois.Rigidity.Examples.PGL27
import InverseGalois.Rigidity.Examples.PGL2F11
import InverseGalois.Rigidity.Examples.PGL2F13
import InverseGalois.Rigidity.Examples.PGL2F17
import InverseGalois.Rigidity.Examples.PGL2F19
import InverseGalois.Rigidity.Examples.Shih

/-!
# The rigidity method for the inverse Galois problem

This module collects the rigidity criterion: a cheap, checkable **rigidity certificate**
(rational conjugacy-class data for a centerless finite group) proves that the group is a *regular*
Galois group over `ℚ(T)`, and hence an inverse Galois group over `ℚ`.  Its analytic ingredient is
the Riemann Existence Theorem, stated in two recognizable forms — `inertiaRootData_exists`
(`RET.Descent.Tower`) in its tame-inertia form and `riemann_existence_cover` (`RET.ExistenceCovers`)
in its covers form — and established in `RET.Completeness` as `geomRET`.

* `Rigidity.RigidityCertificate.isRegularInverseGalois` — the criterion, in its regular form.
* `Rigidity.rigidity_realizable` — the criterion over `ℚ`.
* `Rigidity.rigid_card_iff_single_orbit` — soundness: the certificate's cheap cardinality
  condition equals classical rigidity (a single simultaneous-conjugation orbit).
* `Rigidity.permCert`, `Rigidity.sn_isRegularInverseGalois` — the rigid triple of a symmetric group
  (a transposition, an `(n-1)`-cycle and an `n`-cycle) assembled into a certificate, for every
  `n ≥ 3`.
* `Rigidity.braidTuple`, `Rigidity.braidConj_of_rigidityCertificate` — the Hurwitz braid moves on
  generating product-one tuples, and the Nielsen class of a certificate as a single orbit of the
  braid moves together with simultaneous conjugation.
* `Rigidity.S3Example.s3_isInverseGalois` — the `S₃` sanity example firing it end-to-end.
* `Rigidity.PGL27.isRegularInverseGalois` — the group of Lie type `PGL₂(𝔽₇)`, from the rational
  rigid triple `(2B, 6A, 7A)` on the projective line.
* `Rigidity.PGL2F11.isRegularInverseGalois`, `Rigidity.PGL2F13.isRegularInverseGalois`,
  `Rigidity.PGL2F17.isRegularInverseGalois`, `Rigidity.PGL2F19.isRegularInverseGalois` — the same
  for `PGL₂(𝔽ₚ)` at `p = 11, 13, 17, 19`, each from a rational rigid triple
  `(2, m, p)` on the projective line with `m ∈ {4, 6}`; the certificates are checked by the kernel
  on base-`(p+1)` numerals through `Rigidity.PermCode`.
* `Rigidity.Shih.shihPrime_iff` — the congruence condition on `p` under which one of `2`, `3`, `7`
  is a quadratic non-residue, which is the arithmetic half of Shih's modular construction of
  `PSL₂(𝔽ₚ)`.
-/
