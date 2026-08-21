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

Every group family this development realizes is realized *regularly*.  This module is the index,
and it fills in the regular form of the three abelian realizations whose elementary proofs in
`InverseGalois.Core` predate the regular machinery.

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
* `Rigidity.RET.isRegularInverseGalois_dihedral_of_odd` — `DihedralGroup n` for every odd `n > 1`,
  by the twisted Kummer descent of `RegularDihedral`; in particular
  `Rigidity.RET.isRegularInverseGalois_dihedral_five` for `DihedralGroup 5`.
* `Rigidity.RigidityCertificate.isRegularInverseGalois` — every finite group carrying a rigidity
  certificate; `Rigidity.sn_isRegularInverseGalois` is the certificate for `Sₙ`, `n ≥ 3`.
* `Rigidity.PGL27.isRegularInverseGalois` — the group of Lie type `PGL₂(𝔽₇)`, of order `336`, from
  the rational rigid triple `(2B, 6A, 7A)` on the projective line `ℙ¹(𝔽₇)`.
* `Rigidity.PGL2F11.isRegularInverseGalois`, `Rigidity.PGL2F13.isRegularInverseGalois`,
  `Rigidity.PGL2F17.isRegularInverseGalois`, `Rigidity.PGL2F19.isRegularInverseGalois` — the same
  for `PGL₂(𝔽ₚ)` at `p = 11, 13, 17, 19`, of orders `1320`, `2184`, `4896` and `6840`.

The realizations proved by exhibiting a single polynomial over `ℚ` — `X³ - 2` for `S₃`
(`Groups.S3`), `X⁴ + 8X + 12` for `A₄` (`Groups.A4`), `X⁵ + 20X + 16` for `A₅` (`Groups.A5`),
`ℚ(√2, √3)` for the Klein four group (`Groups.SmallGroups`), and the `Hilbert` specializations —
are all instances of the families above, so each is also realized regularly.

## The dihedral groups

`DihedralGroup 5` is realized over `ℚ` as the Galois group of `X⁵ - 5X + 12`
(`IsInverseGalois.dihedral_five`, `InverseGalois.Groups.D5`), and it was for a long time the one
group in the development without a regular realization: it is not a subgroup of `PGL₂(ℚ)` — that
would put `ζ₅ + ζ₅⁻¹` in `ℚ` — and no rigidity certificate reaches it either, since rigidity needs
rational classes whereas the two classes of rotations of order `5`, namely `{r, r⁴}` and
`{r², r³}`, are interchanged by `Gal(ℚ(ζ₅)/ℚ)`.  Dèbes and Fried moreover bound below by six the
number of branch points of a regular dihedral cover of the line, whereas the rigidity engine here
works with three.

The construction that reaches it is instead an explicit one, `RET.RegularDihedral`: the twisted
Kummer tower of `RegularCyclic` over `ℚ(ζₙ)(u)`, with the radicand's linear factors indexed by the
`2 φ(n)` points `(-1)^ε ζ^x` rather than the `φ(n)` points `ζ^x`.  Those points are distinct
exactly when `n` is odd, and the substitution `u ↦ -u` permutes them; weighting the point `(ε, x)`
by the representative of `± x⁻¹` makes the substitution send the radicand `g` to `m^n / g`, so it
lifts to an involution `w ↦ m / w` of the Kummer extension inverting the Kummer automorphism.  The
degree-`n` layer is then dihedral of order `2n` over the invariants `ℚ(u²)`, which Artin's theorem
gives degree two inside `ℚ(u)` and Lüroth recognizes as a rational function field.  Six points are
branched — the four fifth roots of unity for `n = 5`, together with `0` and `∞` — as the lower
bound requires.

Odd `n` and the Möbius list `n ∈ {1, 2, 3, 4, 6}` together leave the even `n ≥ 8` open.

## Beyond `ℚ`

Irrational classes are not the end of the rigidity method, only of its `ℚ`-form.  If every
cyclotomic twist of the class tuple is again rigid, the branch-cycle argument runs over the
subgroup of the arithmetic fundamental group that fixes the tuple and realizes the group regularly
over the number field that subgroup cuts out:
`Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid`.  The Mathieu groups `M₁₁`, `M₁₂`
and `M₂₄` are realized that way — the classes of `11`-cycles in the first two, and of `23`-cycles
in the third, are interchanged by the exponents prime to `11`, resp. `23` — in the separate
`MathieuRigidity` and `MathieuRigidityM24` targets, which are kept out of this catalogue so that
`InverseGalois` does not depend on the vendored `Mathieu` library.  No Mathieu group has a
rationally rigid triple, and `M₂₂` and `M₂₃` have no rigid triple at all, so the method stops
there; `Aut(M₂₂) = M₂₂ : 2` does have one, and its certificate lives in the
`MathieuRigidityM22` target.  See `docs/Development/MathieuRigidity.md`.  The same descent applies
to `PSL₂(𝔽₇)` (`Rigidity.PSL27.exists_regular_numberField`), whose rigid triple `(2A, 3A, 7A)` is
irrational for the same reason: the exponents prime to `7` interchange its two classes of elements
of order `7`.

## Groups of Lie type

The same split between a simple group and the group of its algebraic automorphisms governs the
rank-one groups of Lie type.  `PSL₂(𝔽_q)` has very few rational classes — for `q` prime only those
of orders `2`, `3` and `6`, never enough to generate — and its two classes of elements of order `q`
are interchanged by the exponents prime to `q`.  Passing to `PGL₂(𝔽_q)` fuses those two classes and
adds outer rational classes of order `2` and, when the tori allow it, of order `4` or `6`; that is
exactly what a rational rigid triple needs.  `PGL₂(𝔽₇)` is the smallest case where the fibre count
is as sharp as it can be — seven product-one triples, matching the centraliser of a `7`-cycle.

Which primes this reaches is decided by the two cyclic tori, of orders `p - 1` and `p + 1`.  An
element of order `4` in a cyclic torus of order `m` lies outside `PSL₂(𝔽ₚ)` exactly when `4 ∣ m`
and `8 ∤ m`, and one of order `6` exactly when `6 ∣ m` and `12 ∤ m`; a triple
`(2, m, p)` consisting of the outer involution, an outer element of order `m ∈ {4, 6}` and a
`p`-cycle is then rational, generating and — for the primes below — rigid, its product-one fibre
having exactly `p` elements, the order of the centraliser of the `p`-cycle.  Among the primes at
most `37` this succeeds for `5, 7, 11, 13, 17, 19, 29, 31, 37` and fails only for `23`, where
`p - 1 = 22` and `p + 1 = 24` admit neither an outer element of order `4` (as `8 ∣ 24`) nor one of
order `6` (as `12 ∣ 24`).

The certificates for `p = 7, 11, 13, 17, 19` are formalized here; the computations are carried out
by the kernel on base-`(p+1)` numerals encoding permutations of `ℙ¹(𝔽ₚ)`, through
`Rigidity.PermCode`.

The simple group `PSL₂(𝔽ₚ)` itself stays out of reach of rigidity **over `ℚ`**: it is the
index-two subgroup of `PGL₂(𝔽ₚ)` rather than a quotient, so a realization of the overgroup does not
descend to it directly.  What the rigidity data does give is a cover of the line branched over
three rational points whose deck group is `PGL₂(𝔽ₚ)`, and the intermediate field cut out by
`PSL₂(𝔽ₚ)` is then a conic through two of the three branch points, hence a rational function field
(`RET.Descent.Index2`).  The classical route to `PSL₂(𝔽ₚ)` is different again — Shih's modular
construction, whose arithmetic half is `Rigidity.Shih.shihPrime_iff`; see
`docs/Development/Shih.md`.

Over a number field the simple group is nevertheless reachable, by the same orbit-rigidity descent
that realizes the Mathieu groups.  `PSL₂(𝔽₇)`, of order `168`, has the rigid triple `(2A, 3A, 7A)`
— an involution, an element of order `3` and a `7`-cycle — whose product-one fibre has exactly
`7 = |C(z)|` elements.  The triple is not rational, the two classes of elements of order `7` being
interchanged by the exponents prime to `7`, but both members of its cyclotomic orbit are rigid, so
`Rigidity.PSL27.exists_regular_numberField` realizes `PSL₂(𝔽₇)` regularly over `K(T)` for the
number field `K` that the index-two stabilizer cuts out.

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
