import InverseGalois.Solvable.Shafarevich.Frattini
import InverseGalois.Solvable.Shafarevich.SemidirectAssoc
import InverseGalois.Solvable.Shafarevich.Reduction
import InverseGalois.Solvable.Shafarevich.Main
import InverseGalois.Solvable.Shafarevich.PrimePower
import InverseGalois.Solvable.Shafarevich.SplitAbelian
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
-/
