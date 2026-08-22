/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core
import InverseGalois.Groups
import InverseGalois.Hilbert
import InverseGalois.Rigidity
import InverseGalois.GeneralLinear

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
* `IsRegularInverseGalois.prod_of_noCommonQuotient` — products of two groups sharing no nontrivial
  quotient, and `IsRegularInverseGalois.prod_of_perfect` for a perfect group times an abelian one.

Families:

* `Rigidity.RET.IsRegularInverseGalois.of_isCyclic` — every finite cyclic group, by the twisted
  Kummer descent of `RegularCyclic`.
* `Rigidity.RET.IsRegularInverseGalois.of_commGroup` — every finite abelian group.
* `isRegularInverseGalois_of_isSemiabelian` — every finite semiabelian group, by the Dentzer–Stoll
  wreath construction (`RET.Wreath`); `IsRegularInverseGalois.wreath` is the closure of the
  catalogue under wreath products by finite abelian groups.
* `InverseGalois.isRegularInverseGalois_of_isZGroup` — every finite group all of whose Sylow
  subgroups are cyclic, and `InverseGalois.isRegularInverseGalois_of_squarefree_card` — every
  finite group of squarefree order (`RET.Wreath.SmallGroups`).
* `Rigidity.RET.isRegularInverseGalois_perm_fin` — `Sₙ` for every `n`.
* `Rigidity.RET.isRegularInverseGalois_alternatingGroup` — `Aₙ` for every `n`.
* `Rigidity.RET.isRegularInverseGalois_of_isMobius` — every finite subgroup of `PGL₂(ℚ)`, hence
  `DihedralGroup n` for `n ∈ {1, 2, 3, 4, 6}` (`MobiusDihedral`) and the cyclic groups of those
  orders (`MobiusFinite`).
* `Rigidity.RET.isRegularInverseGalois_dihedral` — `DihedralGroup n` for every `n ≠ 0`, by the
  twisted Kummer descent of `RegularDihedral`; in particular
  `Rigidity.RET.isRegularInverseGalois_dihedral_five` for `DihedralGroup 5` and
  `Rigidity.RET.isRegularInverseGalois_dihedral_eight` for `DihedralGroup 8`.
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
`2 φ(n)` points `(-1)^ε (ζ^x + 1/4)` rather than the `φ(n)` points `ζ^x`.  The substitution
`u ↦ -u` permutes them; weighting the point `(ε, x)` by the representative of `± x⁻¹` makes the
substitution send the radicand `g` to `m^n / g`, so it lifts to an involution `w ↦ m / w` of the
Kummer extension inverting the Kummer automorphism.  The degree-`n` layer is then dihedral of
order `2n` over the invariants `ℚ(u²)`, which Artin's theorem gives degree two inside `ℚ(u)` and
Lüroth recognizes as a rational function field.  Six points are branched — the four fifth roots of
unity for `n = 5`, together with `0` and `∞` — as the lower bound requires.

The rational shift `1/4` is what makes the construction work in every degree.  The unshifted
points `± ζ^x` are distinct only when `4 ∤ n`: for `4 ∣ n` one has `-ζ^x = ζ^(x + n/2)` with
`x + n/2` again a unit, so the two halves of the index set collide.  Shifting first turns a
collision into the equation `ζ^x + ζ^y = -1/2`, in which the left side is a sum of two roots of
unity — an algebraic integer — and the right side is a rational number that is not one.  Nothing
else in the tower sees the shift: all it asks of the points is that they be distinct, that the
sign flip negate them, and that the cyclotomic character permute them.

Together with the Möbius list, which supplies `n ∈ {1, 2}`, this realizes every finite dihedral
group regularly (`Rigidity.RET.isRegularInverseGalois_dihedral`).

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
to the simple groups `PSL₂(𝔽ₚ)` (`Rigidity.PSL27.exists_regular_numberField`,
`Rigidity.PSL2F11.exists_regular_numberField`, and the `PSL2Large` target for
`p = 13, 17, 19, 23, 29, 31, 37`), whose rigid triple `(2A, 3A, pA)` is irrational for the same
reason: the exponents prime to `p` interchange its two classes of elements of order `p`.

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
that realizes the Mathieu groups, and for every prime rather than for a sporadic list.  `PSL₂(𝔽ₚ)`
has the triple `(2A, 3A, pA)` — an involution, an element of order `3` and a `p`-cycle — whose
product-one fibre has exactly `p = |C(z)|` elements, so it is rigid; it is not rational, the two
classes of elements of order `p` being interchanged by the exponents prime to `p`, but both members
of its cyclotomic orbit are rigid, and that is what the descent needs.  It realizes `PSL₂(𝔽ₚ)`
regularly over `K(T)` for the number field `K` that the index-two stabilizer cuts out, the
quadratic subfield of `ℚ(ζₚ)`.  The certificates are `Rigidity.PSL27.exists_regular_numberField`
and `Rigidity.PSL2F11.exists_regular_numberField` here, and `p = 13, 17, 19, 23, 29, 31, 37` in
the `PSL2Large` target, which raises the elaboration-thread stack.  Note that `p = 23`, the one
prime below `37` out of reach of the rational triples above, is reached this way.

## The general linear groups

`GL n 𝔽q` is never centerless — the scalars are central — so no rigidity certificate can name it.
What can be used is the splitting `GL n 𝔽q ≅ SL n 𝔽q × 𝔽qˣ`, valid exactly when `gcd (n, q - 1) = 1`
(`Matrix.GeneralLinearGroup.mulEquivProdUnits`).  The order of `𝔽qˣ` divides that of `SL n 𝔽q` for
`n ≥ 2`, so the coprime-order product theorem is useless here; the Goursat product theorem is not,
because `SL n 𝔽q` is perfect and `𝔽qˣ` is abelian.  That reduces `GL n 𝔽q` to `SL n 𝔽q`
(`Rigidity.isRegularInverseGalois_generalLinearGroup_of_specialLinearGroup`), and for `q = 2` the
two groups coincide (`Rigidity.isRegularInverseGalois_generalLinearGroup_of_specialLinearGroup_two`).

Two members of the family are realized outright:
`Rigidity.isRegularInverseGalois_generalLinearGroup_one` for `GL₁(𝔽q) ≅ 𝔽qˣ`, which is abelian, and
`Rigidity.isRegularInverseGalois_generalLinearGroup_two_two` for `GL₂(𝔽₂)`, which is the symmetric
group on the three nonzero vectors of `𝔽₂²`.  Beyond those the special linear groups are simple —
`SL n 𝔽₂ = PSL n 𝔽₂` for every `n ≥ 3` — and reaching them needs braid-orbit methods on Hurwitz
spaces rather than rigidity.

## Solvable groups

Shafarevich's theorem — every finite solvable group is a Galois group over `ℚ` — is not in the
catalogue.  Its proof is arithmetic, running through class field theory and the Grunwald–Wang
theorem, and it produces extensions of `ℚ` rather than of `ℚ(T)`: the regular version is open even
for `p`-groups.  What `InverseGalois.Solvable` contributes is the group theory that organizes the
approach — the elementary abelian chief-series induction, the Sylow decomposition of a nilpotent
group, and the presentation of every semidirect product `A ⋊[φ] H` with abelian `A` as a quotient of
the regular wreath product `A ≀ᵣ H`.

That group theory is carried far enough to isolate the arithmetic completely.  Ore's supplement
theorem, `exists_nilpotent_normal_supplement`, exhibits a nontrivial finite solvable group as a
quotient of `N ⋊ U` with `N` nilpotent and `U` a proper — hence smaller — subgroup, and the Sylow
splitting turns a nilpotent kernel into a tower of kernels of prime power order.  The outcome is
`Shafarevich.isSolvable_isInverseGalois_of_splitPrimePowerEP`: Shafarevich's theorem in full
follows from the single statement that a split embedding problem over `ℚ` whose kernel is a finite
`p`-group is solvable.  Nothing of the group theory remains.  The neighbouring case of an
**abelian** kernel is unconditional here — `Shafarevich.splitAbelianEP_regular`, a repackaging of
the wreath product construction — but the two do not meet: filtering a `p`-group kernel leaves a
residual lifting that is no longer split, and that lifting is where class field theory enters.

Dentzer's class of semiabelian groups — the smallest class containing the finite abelian groups and
closed under quotients and under semidirect products by a finite abelian group — *is* in the
catalogue, regularly.  The group theory of `InverseGalois.Solvable` reduces the whole class to the
single statement that wreathing a regularly realizable group by a finite *cyclic* group again gives
one, and `RET.Wreath` proves that statement by the construction of Dentzer and Stoll: a regular
realization of `H` with primitive element `θ` supplies `|H|` coordinates `h(θ) + c` on one curve,
and pulling a regular cyclic realization back along all of them at once produces a compositum whose
Galois group is the full wreath product, because for all but finitely many intercepts `c` the
radicands of the pullbacks are independent modulo `n`-th powers.  So

* `isRegularInverseGalois_of_isSemiabelian` — every finite semiabelian group is a regular Galois
  group over `ℚ(T)`, and
* `IsRegularInverseGalois.wreath` — the catalogue is closed under wreath products by finite abelian
  groups.

The class is generated from the trivial group by iterated semidirect products by finite abelian
groups, with arbitrary actions, together with quotients; so it contains every finite group that can
be written as an iterated split extension of abelian groups, and in particular every finite abelian
group and every quotient of such an iterated product.  It does not contain every finite solvable
group: a solvable group whose chief factors are not complemented need not be semiabelian, and
Shafarevich's theorem remains outside the catalogue.

Recognizing a group as semiabelian is therefore what widens the catalogue, and several criteria do
it.  A normal abelian subgroup of cyclic quotient suffices, with no splitting hypothesis; so does a
normal abelian subgroup with a complement, whether the complement comes from Schur–Zassenhaus, from
a normal abelian Sylow subgroup or from a homomorphic section; so does an abelian subgroup whose
index is the smallest prime factor of the order, which is automatically normal.  The widest of them
is the theorem of Hölder, Burnside and Zassenhaus: a finite group all of whose Sylow subgroups are
cyclic is metacyclic.  Together these give, unconditionally and regularly over `ℚ(T)`,

* `InverseGalois.isRegularInverseGalois_of_isZGroup` — every finite group all of whose Sylow
  subgroups are cyclic, and hence
* `InverseGalois.isRegularInverseGalois_of_squarefree_card` — every finite group of squarefree
  order, and
* the groups of order `p`, `p ^ 2`, `p ^ 3` and `p * q`.

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
