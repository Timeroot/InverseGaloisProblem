/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core
import InverseGalois.Groups
import InverseGalois.Hilbert
import InverseGalois.Rigidity

/-!
# Catalogue of the realized groups

A finite group `G` is *realized over `ℚ`* when `IsInverseGalois G` holds — some finite Galois
extension of `ℚ` has Galois group `G` — and *realized regularly* when `IsRegularInverseGalois G`
holds: some finite Galois extension `L / ℚ(T)` with group `G` has `ℚ` algebraically closed inside
`L`.  The regular statement is the stronger one.  It implies the other by Hilbert irreducibility
(`IsRegularInverseGalois.isInverseGalois`), it is stable under base change, and it is what a
geometric construction actually produces.

Every group family this development realizes is realized *regularly*, with the single exception
recorded at the end.  This module is the index, and it fills in the regular form of the three
abelian realizations whose elementary proofs in `InverseGalois.Core` predate the regular machinery.

## The catalogue

Structural closure properties (`InverseGalois.Rigidity.RET.Statement`, `RegularCriterion`,
`RegularQuotient`, `RegularProduct`):

* `IsRegularInverseGalois.of_mulEquiv` — transport along a group isomorphism.
* `IsRegularInverseGalois.of_subsingleton` — the trivial group.
* `IsRegularInverseGalois.of_surjective`, `IsRegularInverseGalois.quotient` — quotients.
* `Rigidity.RET.IsRegularInverseGalois.prod_of_coprime` — products of coprime order.

Families:

* `Rigidity.RET.IsRegularInverseGalois.of_isCyclic` — every finite cyclic group, by the twisted
  Kummer descent of `RegularCyclic`.
* `Rigidity.RET.IsRegularInverseGalois.of_commGroup` — every finite abelian group.
* `Rigidity.RET.isRegularInverseGalois_perm_fin` — `Sₙ` for every `n`.
* `Rigidity.RET.isRegularInverseGalois_alternatingGroup` — `Aₙ` for every `n`.
* `Rigidity.RET.isRegularInverseGalois_of_isMobius` — every finite subgroup of `PGL₂(ℚ)`, hence
  `DihedralGroup n` for `n ∈ {1, 2, 3, 4, 6}` (`MobiusDihedral`) and the cyclic groups of those
  orders (`MobiusFinite`).
* `Rigidity.RigidityCertificate.isRegularInverseGalois` — every finite group carrying a rigidity
  certificate; `Rigidity.sn_isRegularInverseGalois` is the certificate for `Sₙ`, `n ≥ 3`.

The realizations proved by exhibiting a single polynomial over `ℚ` — `X³ - 2` for `S₃`
(`Groups.S3`), `X⁴ + 8X + 12` for `A₄` (`Groups.A4`), `X⁵ + 20X + 16` for `A₅` (`Groups.A5`),
`ℚ(√2, √3)` for the Klein four group (`Groups.SmallGroups`), and the `Hilbert` specializations —
are all instances of the families above, so each is also realized regularly.

## The exception

`DihedralGroup 5` is realized over `ℚ`, as the Galois group of `X⁵ - 5X + 12`
(`IsInverseGalois.dihedral_five`, `InverseGalois.Groups.D5`), and this is the one group in the
development with no regular realization.  It is not a subgroup of `PGL₂(ℚ)` — that would put
`ζ₅ + ζ₅⁻¹` in `ℚ` — and a rigidity certificate cannot reach it either: rigidity needs rational
classes, whereas the two classes of rotations of order `5`, namely `{r, r⁴}` and `{r², r³}`, are
interchanged by `Gal(ℚ(ζ₅)/ℚ)`.  A rigid triple of `D₅` is rational only over `ℚ(ζ₅ + ζ₅⁻¹) = ℚ(√5)`
and so descends to a regular extension of `ℚ(√5)(T)`.

## Beyond `ℚ`

Irrational classes are not the end of the rigidity method, only of its `ℚ`-form.  If every
cyclotomic twist of the class tuple is again rigid, the branch-cycle argument runs over the
subgroup of the arithmetic fundamental group that fixes the tuple and realizes the group regularly
over the number field that subgroup cuts out:
`Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid`.  The Mathieu groups `M₁₁` and
`M₁₂` are realized that way — their classes of `11`-cycles are interchanged by the exponents prime
to `11` — in the separate `MathieuRigidity` target, which is kept out of this catalogue so that
`InverseGalois` does not depend on the vendored `Mathieu` library.

## Main results

* `Rigidity.RET.isRegularInverseGalois_units_zmod` — `(ZMod n)ˣ`.
* `Rigidity.RET.isRegularInverseGalois_multiplicative_zmod` — the cyclic group `ZMod n`, written
  multiplicatively.
* `Rigidity.RET.isRegularInverseGalois_klein_four` — the Klein four group.
-/

namespace Rigidity.RET

/-- **The unit group of `ZMod n` is a regular Galois group over `ℚ(T)`.**  It is finite abelian,
so the regular abelian realization applies; compare `IsInverseGalois.units_zmod`, which realizes it
over `ℚ` directly inside a cyclotomic field. -/
theorem isRegularInverseGalois_units_zmod (n : ℕ) [NeZero n] :
    IsRegularInverseGalois (ZMod n)ˣ :=
  IsRegularInverseGalois.of_commGroup _

/-- **The cyclic group of order `n`, written multiplicatively, is a regular Galois group over
`ℚ(T)`.** -/
theorem isRegularInverseGalois_multiplicative_zmod (n : ℕ) [NeZero n] :
    IsRegularInverseGalois (Multiplicative (ZMod n)) :=
  IsRegularInverseGalois.of_commGroup _

/-- **The Klein four group is a regular Galois group over `ℚ(T)`.**  Compare
`IsInverseGalois.klein_four`, which realizes it over `ℚ` as `ℚ(√2, √3)`. -/
theorem isRegularInverseGalois_klein_four :
    IsRegularInverseGalois (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  IsRegularInverseGalois.of_commGroup _

end Rigidity.RET
