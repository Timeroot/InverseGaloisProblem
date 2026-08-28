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
-/
