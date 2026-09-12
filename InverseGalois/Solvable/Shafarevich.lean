import InverseGalois.Solvable.Shafarevich.Frattini
import InverseGalois.Solvable.Shafarevich.SemidirectAssoc
import InverseGalois.Solvable.Shafarevich.Reduction
import InverseGalois.Solvable.Shafarevich.Main
import InverseGalois.Solvable.Shafarevich.PrimePower
import InverseGalois.Solvable.Shafarevich.SplitAbelian
import InverseGalois.Solvable.Shafarevich.QuotientChar
import InverseGalois.Solvable.Shafarevich.AbelianKernel
import InverseGalois.Solvable.Shafarevich.MinimalKernel
import InverseGalois.Solvable.Shafarevich.FrattiniKernel
import InverseGalois.Solvable.Shafarevich.ProductAbelian
import InverseGalois.Solvable.Shafarevich.Radicand
import InverseGalois.Solvable.Shafarevich.RadicalTower
import InverseGalois.Solvable.Shafarevich.WreathGalois
import InverseGalois.Solvable.Shafarevich.Ikeda
import InverseGalois.Solvable.Shafarevich.Generic
import InverseGalois.Solvable.Shafarevich.Shrink
import InverseGalois.Solvable.Shafarevich.PCentral
import InverseGalois.Solvable.Shafarevich.ClassTwo
import InverseGalois.Solvable.Shafarevich.PCentralSpan
import InverseGalois.Solvable.Shafarevich.LayerWord
import InverseGalois.Solvable.Shafarevich.ShrinkHom
import InverseGalois.Solvable.Shafarevich.Layer
import InverseGalois.Solvable.Shafarevich.LayerShrink
import InverseGalois.Solvable.Shafarevich.LayerCohomology
import InverseGalois.Solvable.Shafarevich.LayerHomology
import InverseGalois.Solvable.Shafarevich.LayerTensor
import InverseGalois.Solvable.Shafarevich.HomologyOne
import InverseGalois.Solvable.Shafarevich.SemidirectHomology
import InverseGalois.Solvable.Shafarevich.GenericHomology
import InverseGalois.Solvable.Shafarevich.LayerDualTensor
import InverseGalois.Solvable.Shafarevich.GenericCohomology
import InverseGalois.Solvable.Shafarevich.LayerSmooth
import InverseGalois.Solvable.Shafarevich.LayerExtension
import InverseGalois.Solvable.Shafarevich.LayerSplit
import InverseGalois.Solvable.Shafarevich.LayerSection
import InverseGalois.Solvable.Shafarevich.LayerTower
import InverseGalois.Solvable.Shafarevich.LevelSolution
import InverseGalois.Solvable.Shafarevich.LevelObstruction
import InverseGalois.Solvable.Shafarevich.LayerFrattini
import InverseGalois.Solvable.Shafarevich.LevelLift
import InverseGalois.Solvable.Shafarevich.LevelShrink
import InverseGalois.Solvable.Shafarevich.LevelTwist
import InverseGalois.Solvable.Shafarevich.LevelLocal
import InverseGalois.Solvable.Shafarevich.LevelCover
import InverseGalois.Solvable.Shafarevich.LevelCoverOperator
import InverseGalois.Solvable.Shafarevich.HomologyIntegral
import InverseGalois.Solvable.Shafarevich.IntLinHom
import InverseGalois.Solvable.Shafarevich.LinHomTensor
import InverseGalois.Solvable.Shafarevich.LayerDuality
import InverseGalois.Solvable.Shafarevich.LevelRung
import InverseGalois.Solvable.Shafarevich.RamifiedHom
import InverseGalois.Solvable.Shafarevich.RamifiedTransport
import InverseGalois.Solvable.Shafarevich.CyclicTransport
import InverseGalois.Solvable.Shafarevich.InducedCocycle
import InverseGalois.Solvable.Shafarevich.LevelRamification
import InverseGalois.Solvable.Shafarevich.LevelRepair
import InverseGalois.Solvable.Shafarevich.LevelOneCharacter
import InverseGalois.Solvable.Shafarevich.CharacterProduct
import InverseGalois.Solvable.Shafarevich.LayerTensorOne
import InverseGalois.Solvable.Shafarevich.LayerPi
import InverseGalois.Solvable.Shafarevich.LayerKummerShrink
import InverseGalois.Solvable.Shafarevich.LayerLocalOrd
import InverseGalois.Solvable.Shafarevich.LayerShaPlaces
import InverseGalois.Solvable.Shafarevich.LayerShaLevel
import InverseGalois.Solvable.Shafarevich.LayerShaDescent
import InverseGalois.Solvable.Shafarevich.LocalLift
import InverseGalois.Solvable.Shafarevich.RamifiedSplit
import InverseGalois.Solvable.Shafarevich.LevelCyclicRepair
import InverseGalois.Solvable.Shafarevich.CyclicLift
import InverseGalois.Solvable.Shafarevich.LevelFlatTwist
import InverseGalois.Solvable.Shafarevich.LevelFlatKernel
import InverseGalois.Solvable.Shafarevich.LevelFlatOrbit
import InverseGalois.Solvable.Shafarevich.CyclicCorrection
import InverseGalois.Solvable.Shafarevich.LevelConfinedTwist
import InverseGalois.Solvable.Shafarevich.LevelKernelPrescription
import InverseGalois.Solvable.Shafarevich.ElementaryQuotient
import InverseGalois.Solvable.Shafarevich.ElementaryQuotientDecomposition
import InverseGalois.Solvable.Shafarevich.RootsLevel
import InverseGalois.Solvable.Shafarevich.LevelOneArith
import InverseGalois.Solvable.Shafarevich.LevelOneFamily
import InverseGalois.Solvable.Shafarevich.LevelOneTwoPlace
import InverseGalois.Solvable.Shafarevich.LevelOneDecomposition
import InverseGalois.Solvable.Shafarevich.LocalLiftInfinite
import InverseGalois.Solvable.Shafarevich.LevelRungData
import InverseGalois.Solvable.Shafarevich.LevelStepRepair
import InverseGalois.Solvable.Shafarevich.LayerCoord
import InverseGalois.Solvable.Shafarevich.LayerMatrix
import InverseGalois.Solvable.Shafarevich.LayerZeroChar
import InverseGalois.Solvable.Shafarevich.KernelKummer
import InverseGalois.Solvable.Shafarevich.KernelPrimeClass
import InverseGalois.Solvable.Shafarevich.KernelClauses
import InverseGalois.Solvable.Shafarevich.KernelCyclic
import InverseGalois.Solvable.Shafarevich.KernelPrimeCyclic
import InverseGalois.Solvable.Shafarevich.InertiaCyclic
import InverseGalois.Solvable.Shafarevich.LevelFlatRadicand
import InverseGalois.Solvable.Shafarevich.FlatCyclic
import InverseGalois.Solvable.Shafarevich.KummerTensor
import InverseGalois.Solvable.Shafarevich.KernelPlaces
import InverseGalois.Solvable.Shafarevich.FlatPlaces
import InverseGalois.Solvable.Shafarevich.KernelArith
import InverseGalois.Solvable.Shafarevich.KernelStep
import InverseGalois.Solvable.Shafarevich.NamedOrthogonal

/-!
# Shafarevich's theorem

Every finite solvable group is a Galois group over `ℚ`.  The proof separates cleanly into a
group-theoretic reduction and an arithmetic core, and this directory carries out the reduction in
full, leaving the arithmetic core as a single named statement.

The reduction is Ore's.  A nontrivial finite solvable group `G` has a nilpotent normal subgroup
that is not contained in the Frattini subgroup, hence one admitting a *proper* supplement `U`, and
then `G` is a quotient of a semidirect product `N ⋊ U` in which `U` is strictly smaller than `G`.
Induction on the order therefore reduces the whole theorem to *split* embedding problems with
nilpotent kernel, and the Sylow decomposition of a nilpotent group reduces those in turn to split
embedding problems whose kernel has prime power order.

What is left is arithmetic, and it is the part of the theorem that needs class field theory: one
must solve a split embedding problem with `p`-group kernel over `ℚ`.  The neighbouring case of an
**abelian** kernel is already unconditional in this development, by way of the wreath product
construction of `InverseGalois.Solvable.Wreath`, but the two cases do not meet — filtering a
`p`-group kernel leaves a residual lifting that is no longer split.

* `InverseGalois.Solvable.Shafarevich.Frattini` proves Ore's supplement theorem, that a nontrivial
  finite solvable group is the join of a nilpotent normal subgroup and a proper subgroup.
* `InverseGalois.Solvable.Shafarevich.SemidirectAssoc` splits a semidirect product whose kernel is
  a direct product into two stages, `(A × B) ⋊ U ≃* A ⋊ (B ⋊ U)`.
* `InverseGalois.Solvable.Shafarevich.Reduction` states the arithmetic hypothesis and runs Ore's
  induction on the order.
* `InverseGalois.Solvable.Shafarevich.Main` assembles the two into Shafarevich's theorem, in both
  the classical form over `ℚ` and the regular form over `ℚ(T)`.
* `InverseGalois.Solvable.Shafarevich.PrimePower` reduces nilpotent kernels to kernels of prime
  power order.
* `InverseGalois.Solvable.Shafarevich.SplitAbelian` records the unconditional abelian case.
* `InverseGalois.Solvable.Shafarevich.QuotientChar` hands the operators of a group with operators
  down to a quotient by a characteristic subgroup, functorially, which is how a filtration by
  characteristic subgroups becomes a tower of groups with the same operators.
* `InverseGalois.Solvable.Shafarevich.AbelianKernel` peels the centre off a `p`-group kernel one
  layer at a time, reducing the arithmetic hypothesis further to embedding problems whose kernel
  is abelian.
* `InverseGalois.Solvable.Shafarevich.MinimalKernel` continues that filtration through minimal
  normal subgroups, so that the kernel may be taken elementary abelian and minimal.
* `InverseGalois.Solvable.Shafarevich.FrattiniKernel` splits such an embedding problem in two: a
  minimal kernel outside the Frattini subgroup has a complement, so the problem is split with
  abelian kernel, and over `ℚ(T)` that half is already settled; what remains is the case of a
  kernel inside the Frattini subgroup.
* `InverseGalois.Solvable.Shafarevich.ProductAbelian` settles the split embedding problems with
  abelian kernel and trivial action: a realizable group stays realizable after multiplying by an
  arbitrary finite abelian group, by adjoining cyclic subfields of cyclotomic fields ramified at
  pairwise distinct primes.
* `InverseGalois.Solvable.Shafarevich.Radicand` produces, inside a Galois number field, an element
  whose Galois orbit is multiplicatively independent modulo `p`-th powers.
* `InverseGalois.Solvable.Shafarevich.RadicalTower` adjoins a `p`-th root of every member of such
  an orbit and shows the resulting field is Galois over the ground field.
* `InverseGalois.Solvable.Shafarevich.WreathGalois` computes the Galois group of that field: it is
  the regular wreath product of the `p`-th roots of unity by the Galois group of the orbit's field.
* `InverseGalois.Solvable.Shafarevich.Ikeda` deduces Ikeda's theorem, that every split embedding
  problem over `ℚ` with finite abelian kernel is solvable, and so leaves the Frattini-kernel
  embedding problem as the one remaining hypothesis of Shafarevich's theorem.
* `InverseGalois.Solvable.Shafarevich.Generic` builds the relatively free operator group on `n`
  copies of the regular representation of the quotient, and shows that every split embedding
  problem with `p`-group kernel is a quotient of a generic one, so that only the generic kernels
  need to be treated.
* `InverseGalois.Solvable.Shafarevich.Shrink` supplies the counting argument that transports a
  solution found for a generic kernel of very large rank down to the intended rank: a
  Chevalley–Warning count produces a nonzero vector of scalars whose associated combination of
  copies is surjective and annihilates finitely many prescribed obstructions at once.
* `InverseGalois.Solvable.Shafarevich.PCentral` sets up the filtration along which such a solution
  is built: the descending `p`-central series, whose terms are characteristic, whose successive
  quotients are elementary abelian and central, and which a surjection carries onto the
  corresponding series of the image.
* `InverseGalois.Solvable.Shafarevich.ClassTwo` records the commutator calculus that is available
  inside one layer, where the commutators that arise are central: the commutator is bilinear, and
  the `p`-th power of a product differs from the product of the `p`-th powers by a single binomial
  power of the commutator.
* `InverseGalois.Solvable.Shafarevich.PCentralSpan` uses that calculus to generate each layer
  explicitly: starting from a generating set of the group and applying, at each step, either a
  `p`-th power or a commutator with a generator produces a set of words generating the layer.
* `InverseGalois.Solvable.Shafarevich.LayerWord` records those words as syntax rather than only as
  the elements they produce, and reads off the two numbers that the counting argument needs: the
  level of a word, which is the layer it lands in, and its degree, the multiset of generators it
  involves.  Rescaling the generators multiplies the value of a word by the product of the scaling
  exponents over its degree, modulo the next layer, so a word of level `n` is a monomial in those
  exponents of total degree at most `n + 1`.
* `InverseGalois.Solvable.Shafarevich.ShrinkHom` builds the map along which the counting argument
  transports a solution: reading `r * n` letters as `r` blocks of `n`, a vector of exponents sends
  the letter in position `i` of block `k` to the corresponding power of the letter `i`.  The
  resulting homomorphism of free operator groups, and the homomorphism of generic groups it
  induces, are equivariant, and are surjective as soon as one of the exponents is prime to the
  characteristic.
* `InverseGalois.Solvable.Shafarevich.Layer` makes each layer of the filtration into a vector space
  over `ZMod p`, realised as the image of one term in the quotient by the next, functorial in the
  group and spanned by the classes of any family that generates the term modulo the next one.  That
  is the space in which the counting argument is carried out, and the automorphisms of the group
  act on it linearly, so that it is a representation of any group of operators.
* `InverseGalois.Solvable.Shafarevich.LayerShrink` ties the three together: the words of a given
  level span the layer, a shrinking homomorphism turns each of them into a monomial in the
  exponents of degree at most one more than the level, and the Chevalley–Warning count then
  produces a nonzero vector of exponents pushing finitely many prescribed elements of one term into
  the next, whose shrinking homomorphism is surjective because a nonzero vector has a coordinate
  prime to the characteristic.  The layers of the generic groups are linear representations of the
  operator group, and the map between them is equivariant.
* `InverseGalois.Solvable.Shafarevich.LayerCohomology` raises the count from the layer itself to the
  cohomology of the operator group with coefficients in the layer: a class is the class of a
  cocycle, a cocycle on a finite group takes only finitely many values, and a map of coefficients
  annihilating those values annihilates the class.  Finitely many prescribed classes, in any single
  degree, are therefore killed at once by a suitable surjective shrinking homomorphism.
* `InverseGalois.Solvable.Shafarevich.LayerHomology` runs the same argument on cycles instead of
  cocycles, and so obtains the same count for the homology of the operator group with coefficients
  in a layer.  Having both is what makes the whole shrinking procedure work in ordinary
  (co)homology, with no recourse to Tate cohomology in negative degrees.
* `InverseGalois.Solvable.Shafarevich.LayerTensor` runs the count in a tensor product of two layers
  with a fixed module of coefficients: such a product is spanned by the tensors of the classes of
  layer words, a shrinking homomorphism multiplies each of those by the product of the two monomials
  attached to the words, and the degrees add.
* `InverseGalois.Solvable.Shafarevich.HomologyOne` presents the first homology of a group acting
  trivially on coefficients killed by `p`: it is covered by the zeroth layer of the descending
  `p`-central series tensored with the coefficients, compatibly with changing the group and the
  coefficients.  That is the universal coefficient formula in the shape the shrinking argument needs
  it, and it is what turns a homology class into a tensor of layers on which the count operates.
* `InverseGalois.Solvable.Shafarevich.SemidirectHomology` supplies the exactness that the two counts
  are fitted into: for coefficients inflated from the second factor of a semidirect product, a first
  homology class of the product comes from the first factor as soon as it dies in the homology of
  the second.  That is the tail of the homological Hochschild–Serre sequence, with the quotient by
  the kernel of the projection identified with the second factor.
* `InverseGalois.Solvable.Shafarevich.GenericHomology` puts the pieces together: finitely many first
  homology classes of a generic operator group extended by the operator group, with coefficients in
  a layer tensored with a fixed representation, are annihilated all at once by one surjective
  equivariant homomorphism onto the intended rank.  A first shrinking kills the images in the
  homology of the operator group, so the classes come from the generic group itself, where the
  coefficients are trivial and the first homology is the zeroth layer tensored with them; a second
  shrinking kills the chosen preimages there.
* `InverseGalois.Solvable.Shafarevich.LayerDualTensor` says what the count is fed.  What the
  arithmetic produces is not an element of a tensor product but a linear map from the dual of the
  zeroth layer to a layer, and over a field of finite dimension the two are the same thing: a basis
  being named, the map is the sum of the basis vectors against its values on the dual basis, and
  contracting that sum against a functional of the target of a comparison map returns the value of
  the map at the functional pulled back.  So a naming element killed by a comparison map has every
  pulled back value of its map killed, which is the orthogonality the reciprocity residue is asked
  for.
* `InverseGalois.Solvable.Shafarevich.GenericCohomology` frees the count from the group that acts:
  the classes to be killed may be classes of any finite group mapping into the operator group, in
  any single degree and with coefficients in a layer tensored with a fixed representation.  That is
  the form in which the count meets the decomposition subgroups of a finite set of places.
* `InverseGalois.Solvable.Shafarevich.LayerSmooth` runs the same count in the language in which the
  embedding problems are posed, that of cochains on a topological group.  A layer is written
  additively but is the additive copy of a subgroup of a quotient of the group, and the operator
  group acts on that subgroup by automorphisms, so a layer is a multiplicative module and the map
  induced by a homomorphism commuting with the operators is equivariant.  The count then applies
  unchanged, because it only ever looks at the values a cocycle takes: **finitely many second
  cohomology classes of a subgroup of the operator group, with coefficients in a layer, are
  annihilated all at once by one surjective homomorphism onto the intended rank.**
* `InverseGalois.Solvable.Shafarevich.LayerExtension` assembles the group one layer at a time.
  Dividing an operator group by one term of the filtration rather than the next presents the larger
  quotient, with its operators alongside, as an extension of the smaller one by the layer between
  them; a homomorphism commuting with the operators induces a morphism of two such extensions.
  Since the layer is central in the quotient it sits inside, **conjugation in the extension moves it
  only by the operators**, so the class of the extension is a class for the action the count is
  formed with, and killing that class is exactly solving the embedding problem one step further up
  the filtration.
* `InverseGalois.Solvable.Shafarevich.LayerSplit` runs the count against those extension classes.
  The subgroups the count is fed are the ones a place of a number field contributes, and a place
  which is completely decomposed at the level reached contributes a homomorphism of a subgroup of
  the operator group into the group one level up which is a right inverse to the projection.
  Pulling the class of the extension back along such a section, killing the pullbacks all at once
  and transporting the result back along an isomorphism onto the image gives: **after one
  shrinking, the extension one layer gives splits over the image of each of finitely many
  prescribed sections.**
* `InverseGalois.Solvable.Shafarevich.LayerSection` restates that in the currency arithmetic deals
  in.  A place does not hand over a section but a subgroup, its decomposition subgroup at the level
  reached, and the place being completely decomposed there over the field the operators cut out says
  exactly that the projection is injective on that subgroup.  A homomorphism injective on a subgroup
  is an isomorphism of it onto its image, so it has a section over that image whose own image is the
  subgroup one started from; and the image downstairs is settled by the base field and the place
  alone, so it may be prescribed before the count decides how far to shrink.
* `InverseGalois.Solvable.Shafarevich.LayerTower` assembles the filtration into a ladder.  The
  descending `p`-central series of a finite `p`-group starts at the whole group and reaches the
  trivial subgroup, so the semidirect product the generic problem asks for is the top of a finite
  tower whose bottom is the operator group alone.  Both ends being free, what is left is the step
  from one layer to the next, and that step is isolated as a single named statement:
  **`Shafarevich.GenericLayerStepEP` for every prime implies the split embedding problem with a
  kernel of prime power order, and hence Shafarevich's theorem.**
* `InverseGalois.Solvable.Shafarevich.LevelSolution` fixes the order in which that step has
  to be taken.  A step between realizations known only to exist cannot be taken, because the
  subgroups the count has to kill a class on come from the places at which the realization
  already reached is completely decomposed, and a realization known only to exist names no
  places.  So the base realization is fixed once, as a smooth surjection of the Galois group
  of an algebraic closure, and each rung of the ladder carries a smooth surjection projecting
  onto it, trivial along a family of subgroups chosen once from the base realization alone, and
  carrying a property likewise chosen once — in the arithmetic a prescription on the ramification
  of the field it cuts out, which the local solvability of the next step needs and which no rung
  inherits for free.  Both ends of the ladder survive the extra clauses, and the step between them
  becomes a statement whose quantifiers are in the order the arithmetic can meet:
  **`Shafarevich.GenericLevelStepEP` for every prime implies the split embedding problem with
  a kernel of prime power order, and hence Shafarevich's theorem.**
* `InverseGalois.Solvable.Shafarevich.LevelObstruction` spends the two clauses a solution at one
  level carries.  Being trivial on a member of the family wherever the base realization is says the
  projection onto the operator group is injective there, and the image downstairs is settled by the
  base realization alone, so the count may be run before the solution is chosen; running it at the
  number of letters the count asks for, and reading the class of the extension one layer gives
  through the resulting map, leaves **a single solution at the level whose obstruction to the next
  level dies on every member of the family.**  What is left of the step is to make an everywhere
  locally trivial class vanish.
* `InverseGalois.Solvable.Shafarevich.LayerFrattini` disposes of the clause that a solution be
  onto, for every layer but the first.  A layer of the descending `p`-central series is a term of
  that series read in a quotient, and for a finite `p`-group every term past the zeroth lies in the
  Frattini subgroup, which consists of the elements that generate nothing: a subgroup which
  together with it generates the group is already the group.  The operator group carried alongside
  is no obstacle, the layer sitting inside the normal factor, so pulling a supplement back to that
  factor is enough, and **past the first layer a lift over a surjection is a surjection.**
* `InverseGalois.Solvable.Shafarevich.LevelLift` puts those two together and reads off what is
  left.  A solution at one level, taken with enough letters, lifts to the next level, and three of
  the four clauses asked of a solution there come with it: **the lift is smooth, it projects to the
  base realization, and past the first layer it is onto.**  The fourth clause is not free, but its
  failure is confined: along a member of the family, wherever the base realization is trivial, the
  lift lands in the layer.  So the entire remaining content of one rung of the ladder is a
  prescription of restrictions in the layer, in degree one.
* `InverseGalois.Solvable.Shafarevich.LevelShrink` removes the demand that no class be everywhere
  locally trivial, which over a number field is false.  What is true there is that such a class is
  inflated from the finite quotient the base realization cuts out, and that is enough, because the
  shrinking count is insensitive to everything but the order of the group carrying the class, and
  the operator group has an order fixed in advance.  So the count is run a second time, on the
  single class the first run leaves behind: the rank it asks for is settled by the operator group,
  the intended number of letters and the layer alone, so a solution with that many times as many
  letters is produced, its obstruction written as an inflated class, and the class killed.  Pushing
  the solution down carries its obstruction to the image of what was killed.  What the ladder
  consumes is isolated as one condition, that **every everywhere locally trivial class of the layer
  at a number of letters fixed in advance die under a shrinking down to the intended number**;
  inflation is one way of meeting it, and **a solution at one level then lifts to the next.**
* `InverseGalois.Solvable.Shafarevich.LevelTwist` pays that price and closes the rung.  The lifts of
  an embedding problem form a torsor under the one cocycles of the kernel, and along a member of the
  family where the base realization is trivial the discrepancy is a smooth homomorphism into the
  layer; a single global cocycle restricting to the inverses of those homomorphisms cancels them
  all at once, and disturbs neither smoothness, nor the projection, nor surjectivity.  So **a
  solution at one level, past the first, gives a solution at the next**, in exchange for one
  prescription of restrictions of a smooth one cocycle along the family.
* `InverseGalois.Solvable.Shafarevich.LevelLocal` removes that price too, by shrinking a third
  time.  The discrepancy along a member of the family is a homomorphism into the layer, which is
  killed by the prime and commutative, so it factors through the largest elementary abelian quotient
  of that member; when the member has such a quotient finite — which for a decomposition subgroup is
  what local class field theory says — the number of values the discrepancies can take is settled
  before any solution is chosen, and the count then asks for a number of letters settled by that
  number alone.  A shrinking down to the intended number of letters carries all of those values to
  one at once, so **a solution at one level, past the first, gives a solution at the next** with
  nothing asked of the first cohomology beyond restoring the prescribed property, which the
  shrinking is free to destroy.
* `InverseGalois.Solvable.Shafarevich.LevelCover` says where the one surviving condition is to come
  from.  Inflation from the operator group meets it, but inflation is not what a number field
  offers; what a number field offers is duality, under which the everywhere locally trivial classes
  of the second cohomology are the characters of the everywhere locally trivial classes of the first
  cohomology of the Cartier dual, those inject into the first cohomology of a finite level, and the
  characters of the first cohomology of a finite group are its first homology.  So the classes to be
  killed are covered by the first homology of the level with coefficients in the layer twisted by a
  fixed module, and the count already run on that homology asks for a rank settled by the operator
  group, the intended number of letters, the layer and the twist alone.  Granted the covering and
  the naturality of the reading in the coefficients, **a covered class is a shrinkable class.**
* `InverseGalois.Solvable.Shafarevich.LevelCoverOperator` asks for the covering in the shape the
  arithmetic supplies it.  The homology the count is run in is that of the generic operator group
  extended by the operator group, but a number field only ever knows the operator group, which is
  the Galois group of the level the coefficients live over.  The inclusion of the operator group
  into that extension is a section of the projection onto it, and the coefficients are inflated
  along that projection, so a homology class of the operator group pushes into the extension losing
  nothing.  Since the projection is natural in a shrinking, **a covering by the homology of the
  operator group alone is a covering.**
* `InverseGalois.Solvable.Shafarevich.HomologyIntegral` removes the last discrepancy of shape: the
  ladder writes its coefficients over the field with a prime number of elements, while duality over
  a number field writes them over the integers.  The first homology is computed from the action and
  the addition alone, so the cycles and the boundaries in degree one are literally the same subsets
  either way, and the class of a cycle over the smaller ring governs the class of the same cycle
  over the integers for every map of the coefficients at once.  So **a covering by integral homology
  classes is a covering.**
* `InverseGalois.Solvable.Shafarevich.IntLinHom` reads the maps of one representation into another
  over the integers.  A linear map over the field with a prime number of elements is exactly an
  additive map between the underlying groups, so **the maps of two representations read over the
  integers are the integral reading of the maps between them**, and the identification commutes with
  following a map of the target.
* `InverseGalois.Solvable.Shafarevich.LinHomTensor` matches the two descriptions of the
  coefficients.  A linear map out of a finite dimensional space is a sum of a value against a linear
  form, so **the maps of one representation into another are the target tensored with the dual of
  the source**, with the diagonal action answering to the action by conjugation; and following a map
  of the target is, on the tensor product, that map applied to the left factor alone.  The section
  closes with the transport the identification is for: two isomorphic pairs of coefficients joined
  by a commuting square carry the same vanishing in first homology.
* `InverseGalois.Solvable.Shafarevich.LayerDuality` joins the ladder to global duality.  Duality
  produces one class of complete cohomology of the level in degree minus two, in coefficients that
  are the maps of a fixed module into the layer; the ladder consumes one class of first homology, in
  coefficients that are the layer tensored with the dual of that module.  Complete cohomology in
  degree minus two is first homology and the two sets of coefficients are the same, compatibly with
  every shrinking, so the one class produced before any shrinking is chosen is exactly the one class
  the ladder asks for.  Granted the reading of the locally trivial classes as characters and its
  compatibility with a shrinking, **global duality produces the governing class.**
* `InverseGalois.Solvable.Shafarevich.LevelRung` collects what the ladder now asks of the arithmetic
  into a single condition and climbs the whole of it.  A finite family of subgroups, a wider family
  against which local triviality is measured and a property the solutions are to carry are chosen
  once from the base realization; the bottom of the ladder and the first rung are asked for
  outright, the layer there being the Frattini layer, across which a lift carries no guarantee of
  being onto; the property is asked to survive a shrinking; each member of the finite family is
  asked to have a finite elementary quotient; and at every later rung three things are asked, for
  every number of letters — that the step be locally solvable along the members of the wider family
  the finite one does not name, that every everywhere locally trivial class of the layer be killed
  by a shrinking, and that the property be restorable on a lift which already has every other
  clause.  Granted that package, **the step of the ladder holds**, and with it every split embedding
  problem with a kernel of prime power order.
* `InverseGalois.Solvable.Shafarevich.RamifiedHom` states that restriction for a homomorphism to an
  arbitrary group.  Nothing in it mentions the group a homomorphism lands in, and stating it there
  is what lets a solution be assembled in a group convenient for the arithmetic — a group of
  functions on the base group, say, whose Kummer theory is transparent — and only afterwards pushed
  forward to the group the ladder names.  The same file separates out the part of the restriction
  that is about values alone, dropping the clause that asks the local field for roots of unity, and
  shows that **a uniform bound on the order of the values restores that clause**: if every value the
  homomorphism takes where the base realization is trivial is killed by one fixed number, then a
  base realization fixing the roots of unity of the prime times that number turns the restriction
  read off values into the restriction itself.  It then drops total ramification too, and shows that
  **a cyclic local image over a totally ramified one is itself totally ramified**: the generator of
  the local image agrees one layer down with a value on inertia, the two differ by an element the
  prime kills, and an element of prime power order in that position lies in any nontrivial subgroup
  of its own powers.  So splitting and cyclicity are all a construction ever has to arrange.
* `InverseGalois.Solvable.Shafarevich.RamifiedTransport` makes that restriction a finite condition.
  Its three clauses speak only of the decomposition and inertia subgroups of a prime and of the
  values two homomorphisms take on them, and moving a prime by an automorphism conjugates both
  subgroups, so **the clauses move with the prime**: the element bounding the local image is
  replaced by its conjugate, whose order — the only thing the roots of unity rider reads off it — is
  unchanged.  Only finitely many orbits of primes ramify, so **the restriction holds as soon as it
  holds at a family of primes meeting every orbit at which the homomorphism ramifies.**
* `InverseGalois.Solvable.Shafarevich.CyclicTransport` does the same for what is left of the
  restriction once total ramification and the roots of unity are gone.  That a lift ramify over the
  base realization only where the solution below already does or else takes no value at all, and
  that its local image be cyclic where it does, are again clauses about the decomposition and
  inertia subgroups of a prime, so again **they move with the prime**, and **confinement and
  cyclicity are a check at finitely many named primes.**
* `InverseGalois.Solvable.Shafarevich.InducedCocycle` builds the homomorphism such a convenient
  group receives.  Given a homomorphism onto a group, an abelian group and a character of the kernel
  of the homomorphism, a set theoretic section produces a one cocycle with values in the functions
  on the group below, the coordinate at a point being the value of the character at a twisted
  argument there, and hence a homomorphism to the semidirect product lying over the given one.  It
  is onto as soon as the restriction of the cocycle to the kernel is, which is to say as soon as the
  conjugates of the character are jointly onto; and an open normal subgroup on which the
  homomorphism and the character are both trivial lies in its kernel, which is what makes it smooth.
  Summing the translates of the coordinates then carries the functions equivariantly onto any
  abelian group the group below acts on, so the construction reaches the semidirect products an
  embedding problem actually names.  This is Shapiro's lemma in degree one written out, and it is
  what **turns a character of the Galois group of a subfield into a solution over the base field.**
* `InverseGalois.Solvable.Shafarevich.LevelRamification` names the property the package leaves free.
  What the next step needs of a solution is a restriction on where the field it cuts out ramifies
  over the field the base realization cuts out: at a prime where it does ramify, the base
  realization must split completely, the solution must be cyclic there and totally ramified, and the
  local field must already carry the roots of unity the next layer will call for.
  Stated over the primes of the ring of integers of the whole extension the restriction mentions
  only the two subgroups such a prime carries, its decomposition subgroup and its inertia subgroup,
  so no finite level has to be named.  Every clause of it is a statement about the values a solution
  takes, and following a homomorphism can only identify values, so **a shrinking does not destroy
  it**; and at the bottom of the ladder the solution is the base realization itself, which is
  trivial wherever the base realization is, so **the bottom carries it for nothing**.
* `InverseGalois.Solvable.Shafarevich.LevelRepair` cuts the repair the ladder asks of the arithmetic
  down to its arithmetic core.  Of the four clauses of a solution, three survive replacing a lift by
  another lift of the same solution below: such a replacement is again over the base realization,
  because the projection of the layer extension leaves the operator coordinate alone, and it is
  again onto, because past the first layer the layer sits in the Frattini subgroup of the normal
  factor and a lift over a surjection therefore generates.  So **what the arithmetic has to produce
  is only some lift carrying the restriction**, and whether it is onto is not its concern.
* `InverseGalois.Solvable.Shafarevich.LevelOneCharacter` takes the first step of the ladder, the one
  the group theory cannot take on its own.  The layer there is the Frattini layer of the generic
  operator group and it is the whole of the quotient by the first term of the series, so the group
  at the first level is that layer with the operators alongside; a solution there is a smooth
  surjection onto it lying over the base realization, and nothing about the base realization
  produces one.  What produces one is a character of the kernel of the base realization: inducing it
  up and summing the translates of the coordinates gives a homomorphism onto the layer with the
  operators alongside, onto exactly when the conjugates of the character are jointly onto, trivial
  along the family exactly when the character kills the conjugates the family names, and smooth
  because an open normal subgroup the character kills lies in its kernel.  So **the first rung is a
  question about characters**, and it is the question the arithmetic answers.
* `InverseGalois.Solvable.Shafarevich.CharacterProduct` assembles that character coordinate by
  coordinate.  What the arithmetic supplies is a family of additive characters with values in the
  cyclic group of order the exponent, one for each element of the layer, and the character wanted is
  the product of the powers of those elements by the values of the family.  Indexing by the elements
  themselves rather than by a basis makes the generating hypothesis free, so **the product is onto
  together with its conjugates as soon as each coordinate is realised with value one somewhere the
  others vanish**, and **it carries the ramification restriction as soon as, at every prime where it
  ramifies, one coordinate survives on one coset of the decomposition subgroup and nowhere else**.
* `InverseGalois.Solvable.Shafarevich.LayerTensorOne` runs the count in degree one, where the
  coefficients are not a layer but a layer tensored on the left with a finitely generated abelian
  group.  Such a tensor product is infinite, but a spanning family of the left factor writes every
  element of it as a combination of finitely many members against coefficients in the right factor
  alone, so a cocycle on a finite group has finitely many coordinates there.  Reading each
  coordinate in the layer through the map the shrinking induces turns the demand back into finitely
  many scalar equations, and **one first cohomology class with those coefficients is annihilated by
  a surjective shrinking onto the intended rank.**
* `InverseGalois.Solvable.Shafarevich.LayerPi` names the shape twisted Kummer theory asks the
  coefficients to have.  A layer is abelian, killed by the prime and finite, so it is a finite
  vector space over the field with that many elements; a group of that prime order is a one
  dimensional such space; and a basis therefore writes **a layer as a finite power of any group of
  prime order**, in particular of the roots of unity of that order.
* `InverseGalois.Solvable.Shafarevich.LayerKummerShrink` spends the two counts, one after the
  other, on a single everywhere locally trivial class.  Over a finite Galois subextension carrying
  the roots of unity, twisted Kummer theory splits such a class into the obstruction to descending
  it to that subextension, one class of the first cohomology with coefficients the units tensored
  against the homomorphisms of the roots of unity into the layer, and what is left after the
  descent, one class of the second cohomology of a finite group.  Enlarging the alphabet once for
  each of the two and composing the resulting shrinkings gives **one shrinking which annihilates
  the class**, granted the local dictionary that reads the class in the units as an order at each
  place being avoided.
* `InverseGalois.Solvable.Shafarevich.LayerLocalOrd` supplies that dictionary.  The places are the
  primes of the subextension outside a set carried into itself by the Galois group and the reading
  is the vector of orders at them, so the dictionary at a place already says everything; what it
  asks of the coefficients is that the homomorphisms of the roots of unity into the layer be a
  coordinate space over the field with as many elements as the prime, and they are, being a finite
  abelian group killed by the prime.  Since they are produced afresh at each number of letters,
  **the vector of orders is the local dictionary of a layer at every number of letters at once.**
* `InverseGalois.Solvable.Shafarevich.LayerShaPlaces` chooses the set of places and thereby removes
  the last hypothesis.  A finite set of primes stable under the Galois group and meeting every
  ideal class makes the vector of orders onto; its kernel is the group of units for the set, stable
  because the set is and finitely generated because the units of the ring of integers are and the
  orders at the chosen primes span a subgroup of a free abelian group of finite rank.  With the
  dictionary of the previous file that is everything the two counts require, so **every everywhere
  locally trivial class with coefficients in a layer dies under a shrinking**, for any Kummer datum
  over a finite Galois subextension through which the base realization factors.
* `InverseGalois.Solvable.Shafarevich.LayerShaLevel` builds the subextension and the datum rather
  than assuming them.  The base realization is smooth and its target is finite and discrete, so the
  subgroup it kills is open and normal and therefore contains the subgroup fixing a finite Galois
  subextension; the realization factors through the Galois group of that subextension, which is a
  number field because it is finite over one, and the ambient field is its algebraic closure.  The
  datum is the residues modulo the prime read as the roots of unity of the subextension: they come
  from the base, so the whole Galois group fixes them.  Hence **every everywhere locally trivial
  class with coefficients in a layer dies under a shrinking**, over any number field carrying a
  primitive root of unity of the prime order in play.
* `InverseGalois.Solvable.Shafarevich.LayerShaDescent` removes the roots of unity from the base as
  well.  A class over the base is read over the subextension the roots of unity generate, where it
  is still everywhere locally trivial because a decomposition subgroup over the subextension lands
  in one over the base; the shrinking there kills it; killing commutes with the map of the
  coefficients the shrinking induces; and dying over a subextension is dying on the subgroup which
  fixes it, so a class of the prime order dying there is trivial once the index of that subgroup is
  prime to the order — which it is, the degree of the subextension dividing the prime minus one.
  The number of letters is inherited unchanged, the descent changing the base and not the count, so
  **every everywhere locally trivial class with coefficients in a layer dies under a shrinking**,
  over an arbitrary number field.
* `InverseGalois.Solvable.Shafarevich.LocalLift` settles the first of the three things the ladder
  asks at every rung, along the primes where the solution does not ramify.  The decomposition
  subgroup of a prime of the ring of integers of the algebraic closure is generated modulo inertia
  by the Frobenius, in the strong sense that a finite quotient of it which kills inertia is
  generated by one element, so a homomorphism of it into a finite group which kills inertia lifts
  along any surjection onto that group from a finite group; **at a prime where the solution kills
  inertia the step therefore has a local solution**, with nothing asked of the arithmetic.  What is
  left is the other kind of prime, where the solution ramifies and the property it carries makes
  the base realization split completely and the solution cyclic and totally ramified, and that is
  named as a condition in the shape the property supplies, so that **local solvability of the step
  is the ramified case alone** once the finite family names every prime where the base realization
  ramifies.  That case is then stripped of the tower entirely: the values of the solution on the
  decomposition subgroup lie in the powers of one of their own, which lies over the identity of the
  base group because the prime splits completely there, hence has order a power of the prime, and
  any preimage of it one level up has order at most that times the prime, the step being killed by
  the prime.  So **the ramified case asks nothing but the lifting of a cyclic character of
  prime-power order** along a surjection raising that order once, at the decomposition subgroups of
  the primes the base realization splits completely, and with the order bounded by the order of the
  generator of the local image times the prime — which is exactly the bound whose roots of unity
  the restriction asks the local field to carry.  That bound is itself bounded, and uniformly: the
  generic operator group is the free operator group divided by what every homomorphism into the test
  group kills, so **it is killed by the exponent of the test group**, and a value of a solution
  lying over the identity of the base group comes from it, whatever the level and however many
  letters.
* `InverseGalois.Solvable.Shafarevich.RamifiedSplit` reads the restriction at a single prime where
  the solution below splits completely, which is where a repaired lift is allowed to acquire new
  ramification.  The values of the lift on the decomposition subgroup lie over the identity of the
  solution below, so they come from the layer and are killed by the prime, and the base realization
  kills the decomposition subgroup.  What is then left of the restriction is a single clause: that
  the local image be cyclic.  It gives the totally ramified clause because a cyclic image killed by
  the prime has prime order as soon as the prime ramifies at all, so the image of inertia, being a
  nontrivial subgroup of it, is the whole of it; and it gives the roots of unity clause because the
  order of the generator divides the prime, and the base realization is asked to fix the roots of
  unity of order its square.  So **cyclicity is the whole of the restriction at a prime the solution
  below splits completely.**
* `InverseGalois.Solvable.Shafarevich.LevelCyclicRepair` takes the roots of unity out of the repair.
  All but one clause of the restriction is a statement about the values a lift takes on the
  decomposition and inertia subgroups of a prime; the remaining clause is about the field, the local
  field being asked to carry the roots of unity of the prime times the order of the local image, and
  that order is not fixed in advance because it may grow as the ladder is climbed.  It is bounded,
  though, by the exponent of the test group, which depends on neither the level nor the number of
  letters, so **asking the base realization to fix the roots of unity of the prime times that
  exponent discharges the field clause once and for all**.  What is left is a demand about values
  alone: **a lift, trivial along the family, which ramifies over the base realization only where the
  base realization splits completely and is cyclic and totally ramified there**.  Being totally
  ramified is then dropped as well, being a consequence of cyclicity, and what the class field
  theory is left to answer is **a lift whose new ramification is confined to primes the solution
  below splits completely and whose local image there is cyclic**.
* `InverseGalois.Solvable.Shafarevich.CyclicLift` closes that case.  The powers of an element are
  carried onto the powers of any other element whose order divides them, by sending one generator
  to the other; this is well defined because two exponents with the same power of the first element
  differ by a multiple of its order, hence by a multiple of the order of the second.  A cyclic
  character is thereby read inside the units of the algebraic closure, where the roots of unity of
  every order are found, and Hilbert's theorem ninety for a closed subgroup extracts a root of it
  of the complementary order; the transport in the other direction carries that root into the group
  the lift was wanted in, the two transports agreeing at the generators.  The one thing asked is
  that the roots of unity of the order in play be fixed by the decomposition subgroup, that is, that
  the local field at the prime contain them — and that is the last clause of the restriction the
  solutions of the ladder already carry.  So **the step has a local solution at every prime**,
  unconditionally, and no local class field theory is spent on the way.
* `InverseGalois.Solvable.Shafarevich.LevelFlatTwist` flattens a lift before anything sharper is
  asked of it.  A lift may ramify over the base realization at primes where the solution below does
  not, and at such a prime it lands in the layer along the part of inertia the base realization
  kills, so its restriction there is a homomorphism into the layer and a cocycle prescribed to be
  the inverse of it corrects the lift to one unramified there outright.  Only finitely many orbits
  of primes are at stake and one prime of each is named; away from them the cocycle is asked only to
  be unramified, save at primes it brings in itself, where the lift is asked to kill the whole
  decomposition subgroup.  Nothing is demanded of the local image, so this weaker prescription can
  be made over the base field directly and its named primes need not split completely.  So **any
  lift can be corrected to one whose new ramification over the base realization occurs only where
  the solution below already ramifies or else at a prime completely decomposed in the field the
  solution below cuts out**.
* `InverseGalois.Solvable.Shafarevich.LevelFlatKernel` buys that prescription one field up.  Every
  clause it asks for is read along the kernel of the base realization, so it is enough to prescribe
  an equivariant smooth homomorphism there and to extend it back down along a section of the base
  realization.  The extension fails to be a cocycle only by the factor set of the section, a family
  of layer elements indexed by ordered pairs of operators — a number fixed before the number of
  letters is announced — so the number of letters can be announced large enough that one surjective
  shrinking of the operator group annihilates the whole factor set at once.  The prescription
  upstairs may spend a shrinking of its own, and the two compose: the number the factor set is
  killed from is fixed first, the prescription answers at that number, and the shrinking it spends
  comes first.  The section is the identity along the kernel, so the prescribed values, the
  vanishing along the named subgroups and the clause confining the new ramification all transfer
  verbatim.  So **a prescription of an equivariant homomorphism on the kernel of the base
  realization, at every number of letters, buys the flat prescription over the base field**.
* `InverseGalois.Solvable.Shafarevich.LevelFlatOrbit` buys that prescription one named prime at a
  time.  What the prescription upstairs asks of one homomorphism is equivariance for conjugation by
  the whole group, and the arithmetic supplying homomorphisms — a radicand and a root of unity, read
  as a character of the kernel — supplies only the equivariance the radicand has: a radicand in the
  field a decomposition subgroup cuts out is equivariant for that decomposition subgroup and for
  nothing more.  The gap is closed by a trace over the cosets of that subgroup, saturated along the
  base realization; the saturation costs nothing, a homomorphism of the kernel into an abelian group
  not seeing conjugation by the kernel, and it contains the kernel, so its cosets are finitely many.
  Tracing over cosets and not over the whole group is what keeps the prescribed values, a trace over
  the whole group repeating one value as many times as the decomposition subgroup has elements and
  such a power being trivial in an elementary abelian layer.  Several primes are named at once and
  their decomposition subgroups differ, so each is traced separately and the traces are multiplied,
  each factor killing the subgroups belonging to the other named primes so that at a named prime the
  product collapses to its own factor.  So **a prescription made prime by prime, equivariant only
  for the decomposition subgroup of the prime it belongs to, buys the flat prescription one field
  up**.
* `InverseGalois.Solvable.Shafarevich.CyclicCorrection` makes a two generator image cyclic.  The
  decomposition subgroup of a tame prime maps into the step by a pair of generators, one of them
  carrying the whole inertia; writing the other as a layer element times a power of the first puts
  the image inside the products of a power of that layer element with a power of the first
  generator.  The layer element is killed by the prime, so either its image already lies in the
  powers of the first generator, in which case nothing needs correcting, or a Bézout relation makes
  its exponent unique modulo the prime and the exponent is therefore additive.  Taking its inverse
  gives a homomorphism into the layer, trivial at the first generator and factoring through the map
  itself, whose twist lands in the powers of the first generator.  So **a decomposition subgroup
  whose image needs two generators can be corrected by a homomorphism into the layer into one whose
  image is cyclic, generated by the image of the tame generator**.
* `InverseGalois.Solvable.Shafarevich.LevelConfinedTwist` turns the demand about values into a
  demand about one cocycle.  Two lifts of one solution across one layer differ by a one cocycle with
  values in the layer, so the repair is a choice of cocycle; and once the lift has been flattened,
  only finitely many orbits of primes carry any ramification of it at all, one prime of each being
  named, and every one of them is completely decomposed in the field the base realization cuts out
  unless the solution below ramifies there too.  At a named prime where the solution below ramifies
  over the base realization, the base realization kills the whole decomposition subgroup, so that
  subgroup acts trivially on the layer and the local solution of the step differs from the flattened
  lift along it by a homomorphism into the layer; prescribing the cocycle to be that homomorphism
  makes the corrected lift agree with the local solution there, which is cyclic.  At a named prime
  where the solution below does not ramify over the base realization, the flattened lift already
  lands in the layer along the part of inertia the base realization kills, and prescribing the
  cocycle to cancel it there makes the corrected lift unramified outright.  Nowhere else does the
  flattened lift ramify, so any new ramification of the corrected lift is ramification of the
  cocycle, and the cocycle carries its own confinement and cyclicity at the primes it brings in.  So
  **the repair costs exactly one smooth one cocycle, prescribed along finitely many subgroups of
  decomposition subgroups of completely decomposed primes, trivial along the family and ramified
  only where it is allowed to be**.
* `InverseGalois.Solvable.Shafarevich.LevelKernelPrescription` makes that cocycle one field up.  The
  base realization acts on the layer through itself, so through its own kernel it acts trivially,
  and over the field that kernel cuts out a cocycle is nothing but a homomorphism into a finite
  abelian group.  A homomorphism prescribed there is carried back down by averaging it over the
  cosets of the kernel, and the average is a cocycle over the base field for free.  Averaging is
  faithful at the data the prescription names because the primes it names are completely decomposed
  in that field: the representatives of the nontrivial cosets move such a prime, and the
  homomorphism is asked to kill the decomposition subgroups of the primes they move it to, so a
  single term survives the product and, the trivial coset being represented by the identity, that
  term is the value of the homomorphism itself.  The prescribed values and their cyclicity descend
  verbatim, ramification of the average is ramification of the homomorphism somewhere in the same
  orbit, and the finite family, killed at every conjugate, is killed by the average outright.  So
  **the repair costs one smooth homomorphism of the kernel of the base realization into the
  layer**.
* `InverseGalois.Solvable.Shafarevich.ElementaryQuotient` buys the finiteness the ladder asks of
  each member of the finite family.  A subgroup carrying only finitely many smooth characters of
  order dividing the prime has a finite elementary quotient, the product of all of them being a
  homomorphism into a finite group through which every smooth homomorphism into a commutative group
  killed by the prime factors, since such a group is a vector space over the field with that many
  elements and its nonzero vectors are separated by linear functionals.  The finiteness of the
  characters is Kummer theory: on a subgroup fixing the roots of unity of that order, a character
  killed by the prime is a one cocycle for the action on the units, hence the coboundary of a single
  unit whose power is invariant, and that invariant power determines the character up to a root of
  unity, which is invariant as well.  So **finitely many representatives of the power classes of the
  invariants bound the characters**, and the bound survives a subgroup of finite index, a character
  being determined by its restriction together with its values on one representative of each coset
  — which is what lets the counting be done after the base has been enlarged to contain the roots
  of unity.
* `InverseGalois.Solvable.Shafarevich.ElementaryQuotientDecomposition` supplies that finiteness
  for the members the arithmetic actually hands the ladder, the decomposition subgroups of an
  algebraic closure of a number field cut down by the open normal subgroup the base realization
  defines.  The counting is done over a finite Galois level chosen to contain the roots of unity of
  the prime and to fix no more than the open subgroup does: over that level the elements fixed by
  the part of the decomposition subgroup lying above it have finitely many power classes, and that
  part has finite index in the whole, its quotient being carried faithfully into the Galois group of
  the level.  Reading an automorphism over an intermediate field as one over the base is what makes
  the two descriptions of that part agree, the reading being injective with image the subgroup
  fixing the field and moving an ideal of the integers the same way on both sides.  So **a
  decomposition subgroup cut down by an open normal subgroup has a finite elementary quotient**.
* `InverseGalois.Solvable.Shafarevich.RootsLevel` frees the ladder from having to work over a base
  realization whose field is arbitrary.  The group the base realization names may be enlarged: a
  finite Galois level of the realization joined to the field generated by a primitive root of unity
  of any prescribed order is again a finite Galois extension, its Galois group still covers the
  group one started from, and the same kernel with the action pulled back along that covering poses
  a split embedding problem over the larger group whose quotient by the identity on the kernel and
  the covering on the outer factor is the problem one started from.  So **the step of the ladder
  need only be taken over base realizations whose field already contains the roots of unity of a
  prescribed order**, which is what Kummer theory over that field asks for.
* `InverseGalois.Solvable.Shafarevich.LevelOneArith` answers the first rung's question with units.
  A family of units of a finite level, one for each element of the layer, each of which fails to be
  a local power at exactly one place of its own, is a local power at every proper conjugate of its
  two places, and is a local power at both places attached to any other member, becomes the
  character wanted by taking the `ℓ`-th root of each unit and reading the resulting character of the
  automorphisms over the level.  The arithmetic of a unit is the arithmetic of its character: the
  character vanishes on the inertia at a prime where the unit has valuation divisible by the prime,
  and on the whole decomposition subgroup at a prime where the unit is a local power.  So each place
  where a member is not a local power produces one element of the layer and kills every other
  coordinate there, every conjugate the base map moves lands where all the coordinates vanish, and a
  prime where the induced homomorphism ramifies must lie over one of the two places attached to the
  single surviving coordinate.  Hence **a two-place family of units gives the first rung of the
  ladder its character**.
* `InverseGalois.Solvable.Shafarevich.LevelOneFamily` kills that character on the prescribed
  subgroups.  Those subgroups are decomposition subgroups, at a prime above each place of a Galois
  stable set of places of the level and at each archimedean place.  A unit which is a local power at
  a place of the set stays a local power in the completion of any extension, so the whole
  decomposition subgroup at a prime above it fixes every root of the unit, and stability of the set
  carries this to every conjugate.  At an archimedean place an automorphism fixing the place either
  is the identity or composes the embedding with complex conjugation, hence squares to one; such an
  involution multiplies a root of the unit by a root of unity the level already contains, and
  applying it twice forces that root of unity to be a square root of one, which for an odd prime
  exponent leaves only one.  So **a family of units which are local powers along a stable set of
  places gives a character killed on the decomposition subgroups of that set and on the archimedean
  ones**.
* `InverseGalois.Solvable.Shafarevich.LevelOneTwoPlace` supplies the units themselves.  The
  two-place construction of the Poitou-Tate directory produces a family of units over a Galois
  stable finite set of places carrying the ideal classes and the places above the exponent, once an
  auxiliary field is named in which the places outside the set are unramified and the places inside
  it split completely; the level itself serves, since the places the construction spends have
  trivial decomposition group in the level by construction and every prime is unramified in a field
  over itself.  So **a Galois stable finite set of places carrying the ideal classes and the places
  above the exponent gives the first rung of the ladder its character**.
* `InverseGalois.Solvable.Shafarevich.LevelOneDecomposition` names the finite family the ladder is
  climbed along.  A prime of the integers of the whole extension is chosen above each place of the
  stable set, and the stabilisers of those primes are the family: each of them, cut down by the
  kernel of the base realization, has a finite elementary quotient because it is a decomposition
  subgroup, and the character of the previous file dies on all of them because the places it spends
  are places of the set.  Enlarging the set by the finitely many places which ramify in the level
  buys a third property at no cost, that away from the conjugates of the family the base
  realization kills inertia: a prime whose place of the level is outside the set is unramified
  there, so its inertia already fixes the level, and a prime whose place is inside the set is a
  conjugate of a chosen one.  So **a prescribed finite set of places of a level is covered by a
  finite family of primes whose stabilisers carry every condition the first rung asks of the
  family**.
* `InverseGalois.Solvable.Shafarevich.LocalLiftInfinite` closes local solvability at the remaining
  places.  The family the local conditions are read on holds the decomposition subgroups at the
  archimedean places too, and there an automorphism fixing the place is an involution, so the image
  of the decomposition subgroup is killed by two while the layer being added is killed by the odd
  prime the ladder climbs.  The kernel of the surjection therefore has order coprime to the image,
  the preimage of the image splits over that kernel, and a complement maps isomorphically onto the
  image; the inverse of that isomorphism is the lift, and it factors through the same open subgroup
  the solution does, so it is smooth.  So **the step of the ladder is locally solvable along every
  decomposition subgroup, at the finite and at the infinite places together**.
* `InverseGalois.Solvable.Shafarevich.LevelRungData` collects the clauses.  The package the ladder
  consumes asks seven things of the arithmetic, and six of them are now theorems: the bottom of the
  ladder and the stability of the property under a shrinking are free, the property being a
  restriction on ramification over the base realization; the first rung and the finite elementary
  quotients come from the family of primes above a prescribed finite set of places; local
  solvability of the step comes from the third property of that family together with the
  archimedean coprimality; and the shrinking away of the everywhere locally trivial classes is the
  Kummer-theoretic statement proved over an arbitrary number field.  So **a prescribed finite set
  of places of a level is covered by a finite family for which the repair of the property on a lift
  is the only thing the ladder still asks of the arithmetic**.
* `InverseGalois.Solvable.Shafarevich.LevelStepRepair` spends the level.  Over the rationals the
  level the family is built from costs nothing: the kernel of a smooth realization is open and
  normal, so the subfield it fixes is a finite Galois extension whose fixing subgroup is exactly
  that kernel, and it is a number field because the base is.  The roots of unity of order the prime
  lie in it, the restricted step of the ladder having asked the realization to fix those of order
  the square of the prime times the exponent of the kernel, so the family and with it six of the
  seven clauses are available for every base realization at once.  So **for an odd prime the repair
  of the property on a lift is
  the only thing between the arithmetic and the step of the ladder**.  The residual condition is
  named in five forms, each implying the one before it: a repair returning a whole solution, a
  repair returning only a lift, a repair returning a lift whose ramification is described one prime
  at a time, a repair returning a lift whose new ramification is merely confined and cyclic, and —
  no lift at all — **a prescription of one smooth one cocycle with values in the layer**, along
  finitely many subgroups of decomposition subgroups, trivial along the family and ramified only
  where it is allowed to be.
* `InverseGalois.Solvable.Shafarevich.LayerCoord` names coordinates on a layer.  A basis over the
  field with `ℓ` elements having been chosen, an element of a layer is the tuple of its coordinates
  and **a homomorphism into a layer is a tuple of additive characters**; a demand that such a
  homomorphism take given values on a subgroup is therefore a demand on each character separately,
  which is the currency an arithmetic construction deals in.  The generation clauses never needed
  this, a family indexed by the elements of the layer generating it whatever the coordinates are,
  but a prescription of values does.
* `InverseGalois.Solvable.Shafarevich.LayerMatrix` writes a comparison map in those coordinates.
  The coordinates are additive and read a product of powers of the basis off as the exponents, so
  **the coordinates of the image of an element under a map of layers are the combination of its own
  coordinates by the matrix of that map on the basis**.  That matrix is the linear relation the
  reciprocity residues have to satisfy: the classes prescribed downstairs being the images of the
  ones named upstairs, the symbol against them is the corresponding product of powers.
* `InverseGalois.Solvable.Shafarevich.LayerZeroChar` names the characters of the group.  A
  homomorphism to the residues modulo a prime kills the first term of the descending central series,
  so it is read off from a functional on the zeroth layer, and conversely **every character of a
  quotient by a term of that series is named by a functional on the zeroth layer**, additively in
  the functional and naturally in the group: pulling a functional back along a homomorphism names
  the character read through the induced map of quotients.  That naturality is what lets a relation
  established after a shrinking be read at the level the arithmetic named.
* `InverseGalois.Solvable.Shafarevich.KernelKummer` supplies the currency.  The kernel of the base
  realization is the group of automorphisms over the level it cuts out, and over that level Kummer
  theory is available: a unit of the level has an `ℓ`-th root in the algebraic closure and the way
  the automorphisms move that root is an additive character of the kernel.  Read against a family
  of elements of the layer, a family of units of the level therefore assembles into **a
  homomorphism of the kernel into the layer**, and everything the prescription asks of such a
  homomorphism becomes a statement about one unit at a time: it is trivial at an automorphism
  fixing all the roots, hence on the subgroup cutting out the finite level they generate, which is
  what makes it smooth; it is trivial along the decomposition subgroup at a prime where every unit
  of the family is a local power; it is trivial along the inertia subgroup at a prime away from the
  exponent where every unit has order divisible by the exponent; and it takes a prescribed value
  wherever the characters of the units take the coordinates of that value.
* `InverseGalois.Solvable.Shafarevich.KernelPrimeClass` turns the prescription at a named prime into
  the currency itself.  Over the level the base realization cuts out the subgroup carrying a
  prescription is either the whole decomposition subgroup at that prime or the whole inertia
  subgroup there — the part of inertia the base realization kills is all of it once one is over the
  level — so Kummer theory names each coordinate of the prescribed homomorphism by **a class in the
  completion at the place below**, and any family of units of the level carrying those classes
  assembles into a homomorphism restricting to the prescribed one.  Smoothness of the prescription
  is what makes each of those characters trivial on an open subgroup, an open subgroup of a subgroup
  of a Galois group containing the automorphisms of it which fix a finite extension of the base.
* `InverseGalois.Solvable.Shafarevich.KernelClauses` reads the remaining demands the same way.  An
  automorphism lies in the kernel of the base realization exactly when it fixes the level that
  kernel cuts out, so a prime whose place below has trivial decomposition group over the base has
  its whole decomposition group inside that kernel; the place below a conjugate of a prime is the
  conjugate of the place below it, so the demand at the primes the base realization moves the named
  ones to is the demand that the units be local powers at the proper conjugates of the named
  places; and **where the assembled homomorphism is nontrivial on inertia, some unit of the family
  has order not divisible by the exponent at the place below**, since a family all of whose orders
  are divisible by it makes the homomorphism die on inertia away from the exponent, and above the
  exponent the units are local powers anyway.
* `InverseGalois.Solvable.Shafarevich.KernelCyclic` reads the last one.  The confinement clause asks
  that the values along a decomposition subgroup all be powers of a single one, and for a
  homomorphism assembled out of units that is a statement about the family: at a place where every
  unit but one is a local power only one coordinate of the product survives, so **every value is a
  power of the one element of the layer that coordinate reads against**, the residues modulo a
  prime being generated by any nonzero one of them.
* `InverseGalois.Solvable.Shafarevich.KernelPrimeCyclic` sharpens the naming of the classes when the
  prescription has cyclic values.  **The coordinates of a homomorphism with cyclic image are the
  multiples of a single character** of its source — one nonzero coordinate of a generator of the
  image is invertible modulo the prime and divides out — and **the class naming a character names
  all its multiples**, a unit whose class is a power of the named one having that multiple of the
  character, so the classes prescribed at one place all lie on a single line.
* `InverseGalois.Solvable.Shafarevich.InertiaCyclic` shows that a prescription along inertia has
  cyclic values of its own accord.  The inertia subgroup at a prime away from the exponent is
  carried by a single element modulo an open subgroup and modulo raising to a power prime to the
  exponent, so **a smooth homomorphism of it into a group of that exponent has one of its own values
  generating all of them**: what a value differs from the corresponding power of the value at that
  element by is killed both by the prime-to-the-exponent power and by the exponent, hence trivial.
  Read over the level the base realization cuts out, the part of inertia that realization kills is
  the whole inertia subgroup there, so the same holds for it.
* `InverseGalois.Solvable.Shafarevich.LevelFlatRadicand` reads a single unit of the level as such a
  prescription.  The homomorphism assembled out of the powers of one unit against a basis of the
  layer has, at each element of the kernel, that basis product raised to the Kummer character of the
  unit; and at a conjugate of that element by an automorphism carrying the unit to itself up to an
  exponent-th power, the same value raised to the power by which the automorphism raises the roots
  of unity.  **A unit whose order at the place below a prime is prime to the exponent has a Kummer
  character taking a unit value** somewhere on the part of inertia the base realization kills, and
  **every smooth additive character of that part is then a multiple of it**, that part being carried
  by a single element.  A finite family of such homomorphisms is trivial off one open subgroup, the
  roots of the units generating a single finite level.
* `InverseGalois.Solvable.Shafarevich.FlatCyclic` spends that reading on a **single** unit.  A
  prescription at one named prime is a homomorphism of the part of inertia there the base
  realization kills, and that part is carried by a single element, so every coordinate of the
  prescription against a basis of the layer is one and the same multiple of the Kummer character of
  any unit whose order at the place below is prime to the exponent.  The corresponding powers of
  that one unit therefore assemble the prescription, and **the value it is the power of is a single
  product of basis powers**.  Conjugating the argument by an automorphism fixing the unit then
  multiplies the character by the exponent by which that automorphism raises the roots of unity, so
  **the assembled homomorphism is moved by any map of the layer raising that single value to that
  exponent** — the equivariance a prescription made at one prime carries, at the cost of the unit
  being fixed by the decomposition subgroup there and nothing more.
* `InverseGalois.Solvable.Shafarevich.KummerTensor` reads the same assembly with no indexing at all.
  The homomorphism a family of units and a family of coefficients assemble is bilinear in the two
  families and kills the exponent-th powers of a unit, so it depends only on the tensor they define
  and is defined on every tensor of the units of the level with the target.  A conjugation of the
  argument then reads as a **twist** of that tensor — the radicand carried by the automorphism the
  conjugating element induces on the level, the coefficient raised to the power by which that
  element raises the roots of unity — and **the assembled homomorphism is moved by a map of the
  target exactly when the twist of the tensor is the tensor that map carries it to.**  No
  permutation of an index set is exhibited, which is what a tensor invariant for the twist, not
  presented as a sum over orbits, is able to supply.
* `InverseGalois.Solvable.Shafarevich.KernelPlaces` collects those readings into one demand on the
  level and pays the prescription with it.  A basis of the layer having been named, the homomorphism
  asked for is the one assembled out of a family of units indexed by that basis, and each clause of
  the prescription becomes a clause about the local behaviour of the family: the prescribed values
  are classes in the completions at the places below the named primes, the demands at the primes the
  base realization moves them to are triviality of those classes at the proper conjugate places, the
  finite family is avoided by fixing the roots of the units, and the leftover ramification is
  confined by asking that wherever some unit has order not divisible by the exponent the place
  either sits under a named prime or is completely decomposed in a named finite level with a single
  coordinate surviving.  A prime and a named prime with the same place below differ by an
  automorphism of the level, which is what turns the first alternative into being a conjugate of the
  named prime; and the finite level asked for is the one cut out by the kernel of the given lift
  together with the level itself.  **A level carrying such families of units carries the sharp
  prescription**, with no shrinking spent.
* `InverseGalois.Solvable.Shafarevich.FlatPlaces` does the same for the flat prescription, and the
  demand it makes on the level is markedly cheaper.  One unit is asked for at each named place, not
  one class in each coordinate, and the only thing asked of it at its own place is that its order
  there be prime to the exponent; the coordinates of the prescribed homomorphism are then multiples
  of the Kummer character of that one unit, and the powers of it by those multipliers assemble into
  exactly what was prescribed.  Equivariance for the decomposition subgroup is bought by asking the
  automorphisms of the level fixing the place below to fix the unit up to an exponent-th power — the
  whole demand depending on the unit only through its class modulo exponent-th powers — an
  automorphism multiplying the character of such a unit by the power to which it raises the roots of
  unity.
  Because nothing is named but a single unit, and any unit of order prime to the exponent will do,
  **the reciprocity residue the sharp demand leaves behind is absent here**: there is no pairing
  condition, and a level carrying such units carries the flat prescription outright.
* `InverseGalois.Solvable.Shafarevich.KernelArith` buys those families from the arithmetic.  The
  named places are read as a finite set of places and the classes prescribed at them as a family
  indexed by that set, the lines they lie on are spread over the orbits of the named places, and the
  finite level the leftover places are asked to be decomposed in is replaced by its normal closure
  over the base — harmlessly, since a place decomposed in the larger field is decomposed in the
  smaller one, and only finitely many places ramify in it, a place ramifying exactly when the prime
  below it divides the nonzero different.  With that bookkeeping the two-place construction over a
  number field produces the family, and its four conclusions are the four clauses of the demand read
  back through the naming.  What the construction does not carry by itself is the reciprocity
  residue: the product of the power residue symbols of a global unit against the prescribed classes
  vanishes over all the places at once, and away from the named places the prescription contributes
  nothing, so what is left is a pairing condition between the classes named at the named places and
  the units of the level which become exponent-th powers in a finite level.  **A level whose
  prescribed classes pair trivially with those units carries the families of units the prescription
  is made of.**
* `InverseGalois.Solvable.Shafarevich.KernelStep` closes the circle over the rationals.  A base
  realization there cuts out a finite Galois level, the roots of unity of order the prime lie in it
  because the realization fixes those of order its square, and the finite family the local
  conditions are read on names the primes whose places below the families of units are prescribed
  at.  The one thing the level asks of the family beyond its being a family of decomposition
  subgroups is that it cover the primes above the prime, and a place of the level carrying the prime
  carries a prime of the whole extension above it, which the family moves onto one of its members.
  **Every finite Galois level of the rationals containing a primitive root of unity of order the
  prime carrying such families of units buys the sharp prescription, hence the step of the ladder.**
* `InverseGalois.Solvable.Shafarevich.NamedOrthogonal` pays the reciprocity condition and thereby
  removes it.  The number of letters is announced first, by the count in the tensor product of the
  zeroth layer with the layer the values live in: one vector there is annihilated by a surjection
  onto the intended number.  The prescription at that larger number is then answered, at each named
  prime, by local classes on the line of the class of one unit of the level, and the residues of the
  power residue symbol against those classes assemble into a homomorphism of the units of the level
  into the layer — the observation the reciprocity law has to kill.  A functional on the zeroth
  layer names a character of the group of the letters; read through the lift of the base realization
  it becomes a character of the Galois group over the level, and Kummer theory presents that
  character as the character of a unit, so the observation depends on the functional alone and
  linearly, and the naming element of the tensor product turns the whole of it into the single
  vector the count annihilates.  The finite level is the one cutting out the kernel of the lift
  carried across the surjection, and a unit which becomes an exponent-th power there has a Kummer
  character killing that kernel, hence is one of the units the observation was shown to annihilate.
  **The orthogonality of the naming holds for every prime**, so the sharp prescription is
  unconditional and the step of the ladder is bought by the flattening alone.
-/
